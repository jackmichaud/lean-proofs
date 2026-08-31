#!/usr/bin/env node

import { writeFile } from "node:fs/promises";
import { randomBytes } from "node:crypto";
import net from "node:net";

const endpoint = process.env.FRONTIER_CDP ?? "http://127.0.0.1:9222";
const targetUrl = process.env.FRONTIER_URL ?? "http://127.0.0.1:4173/";
const screenshotPath = process.env.FRONTIER_SCREENSHOT ?? "/private/tmp/frontier-mobile-cdp.png";

const target = await fetch(`${endpoint}/json/new?${encodeURIComponent(targetUrl)}`, { method: "PUT" }).then((response) => response.json());
const socket = await connectWebSocket(target.webSocketDebuggerUrl);

let nextId = 1;
const pending = new Map();
const exceptions = [];
socket.onMessage((data) => {
  const message = JSON.parse(data);
  if (message.id && pending.has(message.id)) {
    const { resolve, reject } = pending.get(message.id);
    pending.delete(message.id);
    if (message.error) reject(new Error(message.error.message)); else resolve(message.result);
  }
  if (message.method === "Runtime.exceptionThrown") {
    exceptions.push(message.params.exceptionDetails.text);
  }
});

function connectWebSocket(address) {
  const url = new URL(address);
  return new Promise((resolve, reject) => {
    const connection = net.createConnection(Number(url.port), url.hostname);
    const key = randomBytes(16).toString("base64");
    let buffer = Buffer.alloc(0);
    let connected = false;
    let messageHandler = () => {};
    let fragments = [];
    let fragmentOpcode = 0;

    const api = {
      send(text) {
        const payload = Buffer.from(text);
        const mask = randomBytes(4);
        let header;
        if (payload.length < 126) {
          header = Buffer.from([0x81, 0x80 | payload.length]);
        } else if (payload.length < 65536) {
          header = Buffer.alloc(4);
          header[0] = 0x81;
          header[1] = 0x80 | 126;
          header.writeUInt16BE(payload.length, 2);
        } else {
          header = Buffer.alloc(10);
          header[0] = 0x81;
          header[1] = 0x80 | 127;
          header.writeBigUInt64BE(BigInt(payload.length), 2);
        }
        const masked = Buffer.alloc(payload.length);
        for (let index = 0; index < payload.length; index++) {
          masked[index] = payload[index] ^ mask[index % 4];
        }
        connection.write(Buffer.concat([header, mask, masked]));
      },
      onMessage(handler) { messageHandler = handler; },
      close() { connection.end(Buffer.from([0x88, 0x80, 0, 0, 0, 0])); },
    };

    function parseFrames() {
      while (buffer.length >= 2) {
        const first = buffer[0];
        const second = buffer[1];
        let length = second & 0x7f;
        let offset = 2;
        if (length === 126) {
          if (buffer.length < 4) return;
          length = buffer.readUInt16BE(2);
          offset = 4;
        } else if (length === 127) {
          if (buffer.length < 10) return;
          length = Number(buffer.readBigUInt64BE(2));
          offset = 10;
        }
        if (second & 0x80) offset += 4;
        if (buffer.length < offset + length) return;
        let payload = buffer.subarray(offset, offset + length);
        if (second & 0x80) {
          const mask = buffer.subarray(offset - 4, offset);
          payload = Buffer.from(payload.map((byte, index) => byte ^ mask[index % 4]));
        }
        buffer = buffer.subarray(offset + length);
        const opcode = first & 0x0f;
        if (opcode === 0x8) return connection.end();
        if (opcode === 0x9) continue;
        if (opcode === 0x1 || opcode === 0x2) {
          fragments = [payload];
          fragmentOpcode = opcode;
        } else if (opcode === 0x0) {
          fragments.push(payload);
        }
        if ((first & 0x80) && (fragmentOpcode === 0x1)) {
          messageHandler(Buffer.concat(fragments).toString("utf8"));
          fragments = [];
        }
      }
    }

    connection.on("connect", () => connection.write(
      `GET ${url.pathname} HTTP/1.1\r\n` +
      `Host: ${url.host}\r\n` +
      "Upgrade: websocket\r\n" +
      "Connection: Upgrade\r\n" +
      `Sec-WebSocket-Key: ${key}\r\n` +
      "Sec-WebSocket-Version: 13\r\n\r\n",
    ));
    connection.on("data", (chunk) => {
      buffer = Buffer.concat([buffer, chunk]);
      if (!connected) {
        const boundary = buffer.indexOf("\r\n\r\n");
        if (boundary < 0) return;
        const response = buffer.subarray(0, boundary).toString("utf8");
        if (!response.startsWith("HTTP/1.1 101")) return reject(new Error(response));
        buffer = buffer.subarray(boundary + 4);
        connected = true;
        resolve(api);
      }
      if (connected) parseFrames();
    });
    connection.on("error", reject);
  });
}

function call(method, params = {}) {
  const id = nextId++;
  socket.send(JSON.stringify({ id, method, params }));
  return new Promise((resolve, reject) => pending.set(id, { resolve, reject }));
}

async function evaluate(expression) {
  const result = await call("Runtime.evaluate", { expression, awaitPromise: true, returnByValue: true });
  if (result.exceptionDetails) throw new Error(result.exceptionDetails.text);
  return result.result.value;
}

async function waitFor(expression, timeoutMs = 5000) {
  const start = Date.now();
  while (Date.now() - start < timeoutMs) {
    if (await evaluate(expression)) return;
    await new Promise((resolve) => setTimeout(resolve, 50));
  }
  throw new Error(`Timed out waiting for: ${expression}`);
}

await call("Page.enable");
await call("Runtime.enable");
await call("Emulation.setDeviceMetricsOverride", {
  width: 390,
  height: 844,
  deviceScaleFactor: 1,
  mobile: true,
});
await call("Page.navigate", { url: targetUrl });
await waitFor("document.readyState === 'complete' && document.querySelector('#library-count')?.textContent === '5'");

const dimensions = await evaluate("({ innerWidth, scrollWidth: document.documentElement.scrollWidth, bodyWidth: document.body.scrollWidth })");
if (dimensions.innerWidth !== 390 || dimensions.scrollWidth > 390 || dimensions.bodyWidth > 390) {
  throw new Error(`Mobile overflow: ${JSON.stringify(dimensions)}`);
}

await evaluate("document.querySelector('#new-conjecture-button').click()");
await waitFor("document.querySelector('#conjecture-dialog').open");
await evaluate(`(() => {
  document.querySelector('#conjecture-title').value = 'Twin prime conjecture';
  document.querySelector('#conjecture-topic').value = 'number-theory';
  document.querySelector('#conjecture-informal').value = 'There are infinitely many twin primes.';
  document.querySelector('#conjecture-formal').value = 'True';
  document.querySelector('#conjecture-form').requestSubmit();
})()`);
await waitFor("document.querySelector('#queue-count').textContent === '1'");

await evaluate(`(() => {
  location.hash = 'library';
  const input = document.querySelector('#library-search');
  input.value = 'integer';
  input.dispatchEvent(new Event('input', { bubbles: true }));
})()`);
await waitFor("document.querySelectorAll('#theorem-rows tr').length === 2");

await evaluate("location.hash = 'dependencies'");
await waitFor("document.querySelectorAll('.graph-node').length === 5 && document.querySelectorAll('#graph-lines path').length === 4");

await evaluate("location.hash = 'overview'");
await waitFor("document.querySelector('#overview-view').classList.contains('active')");
const screenshot = await call("Page.captureScreenshot", { format: "png", captureBeyondViewport: false });
await writeFile(screenshotPath, Buffer.from(screenshot.data, "base64"));

if (exceptions.length) throw new Error(`Browser exceptions: ${exceptions.join("; ")}`);

console.log(JSON.stringify({
  dimensions,
  catalogEntries: 5,
  filteredRows: 2,
  graphNodes: 5,
  graphEdges: 4,
  queueItems: 1,
  exceptions: 0,
  screenshotPath,
}, null, 2));

socket.close();
