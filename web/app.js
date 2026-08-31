const state = {
  catalog: null,
  entries: [],
  selectedId: null,
  status: "all",
  topic: "all",
  query: "",
  queue: loadQueue(),
  scaffoldItem: null,
};

const $ = (selector, root = document) => root.querySelector(selector);
const $$ = (selector, root = document) => [...root.querySelectorAll(selector)];

document.addEventListener("DOMContentLoaded", init);

async function init() {
  bindNavigation();
  bindControls();
  renderQueue();
  try {
    const response = await fetch("data/catalog.json", { cache: "no-store" });
    if (!response.ok) throw new Error(`Catalog request failed: ${response.status}`);
    state.catalog = await response.json();
    state.entries = state.catalog.entries;
    state.selectedId = state.entries[0]?.id ?? null;
    renderCatalog();
  } catch (error) {
    $("#kernel-state").classList.add("invalid");
    $("#kernel-state span:last-child").textContent = "Registry unavailable";
    $("#metrics").innerHTML = `<div class="empty-state">${escapeHtml(error.message)}</div>`;
  }
  route();
}

function bindNavigation() {
  window.addEventListener("hashchange", route);
  $("#menu-button").addEventListener("click", () => $("#sidebar").classList.toggle("open"));
  $$(".nav-item").forEach((item) => item.addEventListener("click", () => $("#sidebar").classList.remove("open")));
}

function bindControls() {
  $("#new-conjecture-button").addEventListener("click", () => openConjectureDialog());
  $("#queue-new-button").addEventListener("click", () => openConjectureDialog());
  $("#library-search").addEventListener("input", (event) => {
    state.query = event.target.value.trim().toLowerCase();
    renderLibrary();
  });
  $("#topic-filter").addEventListener("change", (event) => {
    state.topic = event.target.value;
    renderLibrary();
  });
  $("#status-filter").addEventListener("click", (event) => {
    const button = event.target.closest("button");
    if (!button) return;
    state.status = button.dataset.status;
    $$("button", event.currentTarget).forEach((item) => item.classList.toggle("active", item === button));
    renderLibrary();
  });
  $("#conjecture-form").addEventListener("submit", saveConjecture);
  $("#export-queue-button").addEventListener("click", exportQueue);
  $("#close-scaffold-button").addEventListener("click", () => $("#scaffold-dialog").close());
  $("#copy-scaffold-button").addEventListener("click", copyScaffold);
  $("#download-scaffold-button").addEventListener("click", downloadScaffold);
}

function route() {
  const view = (location.hash || "#overview").slice(1).split("/")[0];
  const validView = ["overview", "library", "dependencies", "queue"].includes(view) ? view : "overview";
  $$(".view").forEach((element) => element.classList.toggle("active", element.dataset.view === validView));
  $$(".nav-item").forEach((element) => element.classList.toggle("active", element.dataset.view === validView));
  if (validView === "dependencies") requestAnimationFrame(renderGraph);
}

function renderCatalog() {
  const allValid = state.catalog.summary.valid === state.catalog.summary.total && !state.catalog.summary.globalErrors.length;
  const kernel = $("#kernel-state");
  kernel.classList.add(allValid ? "verified" : "invalid");
  $("#kernel-state span:last-child").textContent = allValid ? "Kernel audit verified" : "Registry audit failed";
  $("#library-count").textContent = state.entries.length;
  const latest = [...state.entries].sort((a, b) => b.updated.localeCompare(a.updated))[0]?.updated;
  $("#updated-label").textContent = latest ? `Updated ${formatDate(latest)}` : "";
  renderTopics();
  renderOverview();
  renderLibrary();
  renderGraph();
}

function renderTopics() {
  const counts = countBy(state.entries, (entry) => entry.topic);
  $("#topic-links").innerHTML = Object.entries(counts).map(([topic, count]) => `
    <button class="topic-link" data-topic="${escapeHtml(topic)}">
      ${escapeHtml(displayTopic(topic))}<span>${count}</span>
    </button>`).join("");
  $$(".topic-link").forEach((button) => button.addEventListener("click", () => {
    state.topic = button.dataset.topic;
    $("#topic-filter").value = state.topic;
    location.hash = "library";
    renderLibrary();
  }));
  const select = $("#topic-filter");
  select.innerHTML = `<option value="all">All topics</option>${Object.keys(counts).map((topic) =>
    `<option value="${escapeHtml(topic)}">${escapeHtml(displayTopic(topic))}</option>`).join("")}`;
}

function renderOverview() {
  const proved = state.entries.filter((entry) => entry.status === "proved").length;
  const unresolved = state.entries.filter((entry) => ["open", "formalizing", "conditional"].includes(entry.status)).length;
  const edgeCount = state.entries.reduce((total, entry) => total + entry.dependencies.length, 0);
  const reused = new Set(state.entries.flatMap((entry) => entry.dependencies)).size;
  const metricData = [
    ["Cataloged artifacts", state.entries.length, `${state.catalog.summary.valid} kernel-audited`],
    ["Proved", proved, `${Math.round((proved / Math.max(state.entries.length, 1)) * 100)}% of registry`],
    ["Open frontier", unresolved + state.queue.length, `${state.queue.length} in research queue`],
    ["Reusable results", reused, `${edgeCount} proof dependencies`],
  ];
  $("#metrics").innerHTML = metricData.map(([label, value, note]) => `
    <div class="metric"><div class="metric-label">${label}</div><div class="metric-value">${value}</div><p class="metric-note">${note}</p></div>`).join("");
  $("#edge-count").textContent = `${edgeCount} checked reuse edges`;

  $("#recent-results").innerHTML = [...state.entries].sort((a, b) => b.updated.localeCompare(a.updated)).slice(0, 5).map((entry) => `
    <article class="result-item" data-entry-id="${entry.id}" tabindex="0">
      <div><span class="result-title">${escapeHtml(entry.title)}</span><span class="result-decl mono">${escapeHtml(entry.statement)}</span></div>
      ${statusBadge(entry.status)}
      <span class="dependency-count">${entry.dependencies.length} ${entry.dependencies.length === 1 ? "dependency" : "dependencies"}</span>
    </article>`).join("");
  $$("[data-entry-id]", $("#recent-results")).forEach((item) => {
    const open = () => selectEntry(item.dataset.entryId);
    item.addEventListener("click", open);
    item.addEventListener("keydown", (event) => { if (event.key === "Enter") open(); });
  });
  renderQueuePreview();
  renderLineage();
}

function renderLineage() {
  const roots = state.entries.filter((entry) => entry.dependencies.length === 0);
  const chain = [];
  const visited = new Set();
  let current = roots[0];
  while (current && !visited.has(current.id)) {
    chain.push(current);
    visited.add(current.id);
    current = state.entries.find((entry) => entry.dependencies.includes(current.id));
  }
  $("#lineage-strip").innerHTML = chain.flatMap((entry, index) => [
    `<button class="lineage-node" data-lineage-id="${entry.id}"><strong>${escapeHtml(entry.title)}</strong><span>${escapeHtml(entry.statement)}</span></button>`,
    index < chain.length - 1 ? `<span class="lineage-arrow" aria-hidden="true">→</span>` : "",
  ]).join("");
  $$("[data-lineage-id]").forEach((button) => button.addEventListener("click", () => selectEntry(button.dataset.lineageId)));
}

function filteredEntries() {
  return state.entries.filter((entry) => {
    if (state.status !== "all" && entry.status !== state.status) return false;
    if (state.topic !== "all" && entry.topic !== state.topic) return false;
    if (!state.query) return true;
    return [entry.id, entry.title, entry.summary, entry.statement, entry.statementType, ...entry.tags]
      .join(" ").toLowerCase().includes(state.query);
  });
}

function renderLibrary() {
  if (!state.catalog) return;
  const entries = filteredEntries();
  $("#library-empty").classList.toggle("hidden", entries.length > 0);
  $("#theorem-rows").innerHTML = entries.map((entry) => `
    <tr data-row-id="${entry.id}" class="${entry.id === state.selectedId ? "selected" : ""}">
      <td><span class="table-title">${escapeHtml(entry.title)}</span><span class="table-decl mono">${escapeHtml(entry.statement)}</span></td>
      <td>${statusBadge(entry.status)}</td>
      <td>${escapeHtml(displayTopic(entry.topic))}</td>
      <td>${entry.dependencies.length}</td>
      <td>${formatDate(entry.updated)}</td>
    </tr>`).join("");
  $$("[data-row-id]").forEach((row) => row.addEventListener("click", () => {
    state.selectedId = row.dataset.rowId;
    renderLibrary();
  }));
  const selected = state.entries.find((entry) => entry.id === state.selectedId) || entries[0];
  renderDetail(selected);
}

function renderDetail(entry) {
  if (!entry) {
    $("#detail-panel").innerHTML = `<div class="empty-state">Select a theorem.</div>`;
    return;
  }
  const dependencies = entry.dependencies.length
    ? entry.dependencies.map((id) => `<button class="dependency-link" data-dependency-id="${id}">${escapeHtml(titleFor(id))} →</button>`).join("")
    : `<span class="subtle">No catalog dependencies</span>`;
  $("#detail-panel").innerHTML = `
    ${statusBadge(entry.status)}
    <h2>${escapeHtml(entry.title)}</h2>
    <p class="detail-summary">${escapeHtml(entry.summary)}</p>
    <div class="detail-section"><span class="detail-label">Lean statement</span><pre class="type-block">${escapeHtml(entry.statementType)}</pre></div>
    <div class="detail-section"><span class="detail-label">Dependencies</span>${dependencies}</div>
    <div class="detail-section"><span class="detail-label">Tags</span><div class="tag-row">${entry.tags.map((tag) => `<span class="tag">${escapeHtml(tag)}</span>`).join("")}</div></div>
    <div class="detail-section">
      <span class="detail-label">Trust audit</span>
      <div class="trust-row"><span>Certificate</span><code>${escapeHtml(entry.certificate || "none")}</code></div>
      <div class="trust-row"><span>Evidence</span><strong>${escapeHtml(entry.evidence || "none")}</strong></div>
      <div class="trust-row"><span>Axioms</span><strong>${entry.axioms.length}</strong></div>
      <div class="tag-row">${entry.axioms.map((axiom) => `<span class="tag">${escapeHtml(axiom)}</span>`).join("") || `<span class="tag">axiom-free</span>`}</div>
    </div>`;
  $$("[data-dependency-id]", $("#detail-panel")).forEach((button) => button.addEventListener("click", () => {
    state.selectedId = button.dataset.dependencyId;
    renderLibrary();
  }));
}

function selectEntry(id) {
  state.selectedId = id;
  location.hash = "library";
  renderLibrary();
}

function renderGraph() {
  if (!state.entries.length) return;
  const stage = $("#graph-stage");
  const width = Math.max(stage.clientWidth || 1000, 900);
  const height = Math.max(stage.clientHeight || 500, 430);
  const depth = new Map();
  const getDepth = (entry, stack = new Set()) => {
    if (depth.has(entry.id)) return depth.get(entry.id);
    if (stack.has(entry.id) || !entry.dependencies.length) return 0;
    const nextStack = new Set(stack).add(entry.id);
    const value = 1 + Math.max(...entry.dependencies.map((id) => getDepth(state.entries.find((item) => item.id === id), nextStack)));
    depth.set(entry.id, value);
    return value;
  };
  state.entries.forEach((entry) => depth.set(entry.id, getDepth(entry)));
  const columns = countBy(state.entries, (entry) => depth.get(entry.id));
  const positions = new Map();
  const maxDepth = Math.max(...depth.values(), 1);
  const seenColumn = {};
  state.entries.forEach((entry) => {
    const level = depth.get(entry.id);
    const index = seenColumn[level] || 0;
    seenColumn[level] = index + 1;
    const count = columns[level];
    positions.set(entry.id, {
      x: 40 + (level / maxDepth) * (width - 280),
      y: ((index + 1) / (count + 1)) * (height - 90),
    });
  });
  $("#graph-nodes").innerHTML = state.entries.map((entry) => {
    const position = positions.get(entry.id);
    return `<button class="graph-node ${entry.id === state.selectedId ? "active" : ""}" data-graph-id="${entry.id}" style="left:${position.x}px;top:${position.y}px"><strong>${escapeHtml(entry.title)}</strong><span>${entry.dependencies.length} dependencies · ${escapeHtml(entry.status)}</span></button>`;
  }).join("");
  $("#graph-lines").setAttribute("viewBox", `0 0 ${width} ${height}`);
  $("#graph-lines").innerHTML = state.entries.flatMap((entry) => entry.dependencies.map((id) => {
    const from = positions.get(id);
    const to = positions.get(entry.id);
    return `<path d="M ${from.x + 190} ${from.y + 38} C ${from.x + 230} ${from.y + 38}, ${to.x - 40} ${to.y + 38}, ${to.x} ${to.y + 38}" fill="none" stroke="#829089" stroke-width="1.5"/>`;
  })).join("");
  $$("[data-graph-id]").forEach((button) => button.addEventListener("click", () => {
    state.selectedId = button.dataset.graphId;
    renderGraph();
  }));
  const selected = state.entries.find((entry) => entry.id === state.selectedId) || state.entries[0];
  $("#graph-selection").innerHTML = `<strong>${escapeHtml(selected.title)}</strong><span class="subtle">${selected.dependencies.length ? `Uses ${selected.dependencies.map(titleFor).join(", ")}` : "Root result with no catalog dependencies"}</span>`;
}

function loadQueue() {
  try { return JSON.parse(localStorage.getItem("frontier-research-queue") || "[]"); }
  catch { return []; }
}

function persistQueue() {
  localStorage.setItem("frontier-research-queue", JSON.stringify(state.queue));
  renderQueue();
  renderQueuePreview();
  if (state.catalog) renderOverview();
}

function renderQueuePreview() {
  const container = $("#queue-preview");
  if (!state.queue.length) {
    container.innerHTML = `<div class="empty-queue"><span>No active conjectures.</span><button class="secondary-button" id="preview-new-button">Add conjecture</button></div>`;
    $("#preview-new-button").addEventListener("click", () => openConjectureDialog());
    return;
  }
  container.innerHTML = state.queue.slice(0, 4).map((item) => `
    <article class="queue-preview-item"><strong>${escapeHtml(item.title)}</strong><div class="queue-preview-meta"><span>${escapeHtml(displayTopic(item.topic))}</span><span>·</span><span>${escapeHtml(item.stage)}</span></div></article>`).join("");
}

function renderQueue() {
  $("#queue-count").textContent = state.queue.length;
  const stages = [
    ["formalizing", "Formalizing"],
    ["investigating", "Investigating"],
    ["ready", "Ready for proof"],
  ];
  $("#queue-board").innerHTML = stages.map(([stage, label]) => {
    const items = state.queue.filter((item) => item.stage === stage);
    return `<section class="queue-column"><div class="queue-column-header"><h2>${label}</h2><span>${items.length}</span></div><div class="queue-items">${items.map(queueCard).join("")}</div></section>`;
  }).join("");
  $$("[data-queue-action]").forEach((button) => button.addEventListener("click", () => handleQueueAction(button)));
}

function queueCard(item) {
  return `<article class="queue-card"><h3>${escapeHtml(item.title)}</h3><p>${escapeHtml(item.informal)}</p><div class="queue-card-footer"><i class="priority priority-${item.priority}"></i><span>${escapeHtml(displayTopic(item.topic))}</span><button class="mini-button" data-queue-action="scaffold" data-id="${item.id}">Lean</button><button class="mini-button" data-queue-action="advance" data-id="${item.id}">Advance</button><button class="mini-button" data-queue-action="edit" data-id="${item.id}">Edit</button></div></article>`;
}

function handleQueueAction(button) {
  const item = state.queue.find((candidate) => candidate.id === button.dataset.id);
  if (!item) return;
  if (button.dataset.queueAction === "edit") openConjectureDialog(item);
  if (button.dataset.queueAction === "scaffold") showScaffold(item);
  if (button.dataset.queueAction === "advance") {
    const stages = ["formalizing", "investigating", "ready"];
    item.stage = stages[(stages.indexOf(item.stage) + 1) % stages.length];
    persistQueue();
  }
}

function openConjectureDialog(item = null) {
  $("#dialog-title").textContent = item ? "Edit conjecture" : "New conjecture";
  $("#conjecture-id").value = item?.id || "";
  $("#conjecture-title").value = item?.title || "";
  $("#conjecture-topic").value = item?.topic || "";
  $("#conjecture-priority").value = item?.priority || "normal";
  $("#conjecture-informal").value = item?.informal || "";
  $("#conjecture-formal").value = item?.formal || "";
  $("#conjecture-dialog").showModal();
  $("#conjecture-title").focus();
}

function saveConjecture(event) {
  event.preventDefault();
  const id = $("#conjecture-id").value;
  const existing = state.queue.find((item) => item.id === id);
  const record = {
    id: id || crypto.randomUUID(),
    title: $("#conjecture-title").value.trim(),
    topic: slugify($("#conjecture-topic").value),
    priority: $("#conjecture-priority").value,
    informal: $("#conjecture-informal").value.trim(),
    formal: $("#conjecture-formal").value.trim(),
    stage: existing?.stage || "formalizing",
    created: existing?.created || new Date().toISOString(),
    updated: new Date().toISOString(),
  };
  if (existing) Object.assign(existing, record); else state.queue.unshift(record);
  $("#conjecture-dialog").close();
  persistQueue();
  showToast(existing ? "Conjecture updated" : "Conjecture added");
}

function scaffoldFor(item) {
  const namespace = pascalCase(item.title);
  const proposition = item.formal || "True -- replace with the formal proposition";
  return `import Mathlib\n\n/-!\n# ${item.title}\n\n${item.informal}\n-/\n\nnamespace Frontier.Research.${namespace}\n\ndef claim : Prop :=\n  ${proposition.replaceAll("\n", "\n  ")}\n\n-- Promote this declaration to the Frontier catalog only after Lean checks it.\ntheorem proof : claim := by\n  sorry\n\nend Frontier.Research.${namespace}\n`;
}

function showScaffold(item) {
  state.scaffoldItem = item;
  $("#scaffold-code").textContent = scaffoldFor(item);
  $("#scaffold-dialog").showModal();
}

async function copyScaffold() {
  await navigator.clipboard.writeText($("#scaffold-code").textContent);
  showToast("Lean scaffold copied");
}

function downloadScaffold() {
  const blob = new Blob([$("#scaffold-code").textContent], { type: "text/plain" });
  downloadBlob(blob, `${pascalCase(state.scaffoldItem.title)}.lean`);
}

function exportQueue() {
  const blob = new Blob([JSON.stringify({ schemaVersion: 1, conjectures: state.queue }, null, 2)], { type: "application/json" });
  downloadBlob(blob, "frontier-research-queue.json");
}

function downloadBlob(blob, filename) {
  const url = URL.createObjectURL(blob);
  const link = document.createElement("a");
  link.href = url;
  link.download = filename;
  link.click();
  URL.revokeObjectURL(url);
}

function statusBadge(status) {
  return `<span class="status-badge status-${escapeHtml(status)}">${escapeHtml(status)}</span>`;
}

function titleFor(id) {
  return state.entries.find((entry) => entry.id === id)?.title || id;
}

function countBy(values, key) {
  return values.reduce((counts, value) => {
    const name = key(value);
    counts[name] = (counts[name] || 0) + 1;
    return counts;
  }, {});
}

function slugify(value) {
  return value.trim().toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/^-|-$/g, "") || "general";
}

function pascalCase(value) {
  const name = value.replace(/[^a-zA-Z0-9]+/g, " ").trim().split(/\s+/).map((word) => word[0]?.toUpperCase() + word.slice(1)).join("");
  return /^\d/.test(name) ? `Claim${name}` : name || "NewClaim";
}

function displayTopic(topic) { return topic.split("-").map((word) => word[0]?.toUpperCase() + word.slice(1)).join(" "); }
function formatDate(date) { return new Intl.DateTimeFormat("en", { month: "short", day: "numeric", year: "numeric" }).format(new Date(`${date}T12:00:00`)); }
function escapeHtml(value) { const node = document.createElement("span"); node.textContent = String(value); return node.innerHTML; }

let toastTimer;
function showToast(message) {
  const toast = $("#toast");
  toast.textContent = message;
  toast.classList.add("show");
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => toast.classList.remove("show"), 1800);
}
