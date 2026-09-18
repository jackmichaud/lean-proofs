// Schema this UI understands. `frontier export` stamps every catalog with its version; a
// mismatch means the page would silently render a stale or partial view of the registry, so
// say so instead.
const SUPPORTED_SCHEMA_VERSION = 2;

// The work journal is a separate, *untrusted* feed: a record of attempts written by
// `frontier work` and `frontier check --work`, versioned independently of the catalog because
// it is mutable data about process rather than audited data about mathematics.
const SUPPORTED_WORK_SCHEMA_VERSION = 1;

// How often to reload the journal while the tab is visible. The point of the journal is to
// follow along with work as it happens, which a page that only reads its data once cannot do.
// Hidden tabs do not poll: a workspace left open overnight should not sit in a request loop.
const WORK_POLL_MS = 4000;

const state = {
  catalog: null,
  entries: [],
  selectedId: null,
  status: "all",
  literature: "all",
  topic: "all",
  query: "",
  queue: loadQueue(),
  scaffoldItem: null,
  work: null,
  workItems: [],
  workError: null,
  // Signature of the last rendered journal, so polling re-renders only on a real change and
  // does not fight with the user's scroll position or focus.
  workSignature: null,
};

const WORK_STAGES = [
  ["exploring", "Exploring", "A goal, no draft yet"],
  ["drafting", "Drafting", "Iterating on a draft"],
  ["blocked", "Blocked", "Stuck, with a reason"],
  ["clean", "Clean", "Lean accepted the draft"],
  ["registered", "Registered", "Promoted to the catalog"],
  ["abandoned", "Abandoned", "Dropped, kept for the record"],
];

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
    // Not assigned to state until it validates. `state.catalog` being set is what every later
    // render treats as "the registry loaded"; a half-accepted catalog left there means the
    // journal poll calls renderOverview a moment later and overwrites the error below with a
    // grid of zeroes, so the one message telling the reader to run `make catalog` appears and
    // then vanishes.
    const catalog = await response.json();
    if (catalog.schemaVersion !== SUPPORTED_SCHEMA_VERSION) {
      throw new Error(`Catalog schema v${catalog.schemaVersion} but this workspace reads v${SUPPORTED_SCHEMA_VERSION}. Run \`make catalog\`.`);
    }
    state.catalog = catalog;
    state.entries = catalog.entries;
    state.selectedId = state.entries[0]?.id ?? null;
    renderCatalog();
  } catch (error) {
    $("#kernel-state").classList.add("invalid");
    $("#kernel-state span:last-child").textContent = "Registry unavailable";
    $("#metrics").innerHTML = `<div class="empty-state">${escapeHtml(error.message)}</div>`;
  }
  await loadWork();
  startWorkPolling();
  route();
}

// The journal is optional: a fresh clone has done no work yet, and a missing file is that
// state rather than an error to report.
async function loadWork() {
  try {
    const response = await fetch("data/work.json", { cache: "no-store" });
    if (response.status === 404) {
      state.work = null;
      state.workItems = [];
      state.workError = null;
      renderWork();
      return;
    }
    if (!response.ok) throw new Error(`Work journal request failed: ${response.status}`);
    const journal = await response.json();
    if (journal.schemaVersion !== SUPPORTED_WORK_SCHEMA_VERSION) {
      throw new Error(`Work journal schema v${journal.schemaVersion} but this workspace reads v${SUPPORTED_WORK_SCHEMA_VERSION}.`);
    }
    state.work = journal;
    state.workItems = journal.items ?? [];
    state.workError = null;
  } catch (error) {
    state.work = null;
    state.workItems = [];
    state.workError = error.message;
  }
  renderWork();
}

function startWorkPolling() {
  const tick = async () => {
    if (document.hidden) return;
    await loadWork();
  };
  setInterval(tick, WORK_POLL_MS);
  // Reload immediately on returning to the tab, rather than waiting out the interval.
  document.addEventListener("visibilitychange", () => { if (!document.hidden) tick(); });
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
  $("#literature-filter").addEventListener("change", (event) => {
    state.literature = event.target.value;
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
  $("#copy-commands-button").addEventListener("click", copyCommands);
  $("#download-scaffold-button").addEventListener("click", downloadScaffold);
}

function route() {
  const view = (location.hash || "#overview").slice(1).split("/")[0];
  const validView = ["overview", "library", "dependencies", "work", "queue"].includes(view) ? view : "overview";
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
  $("#schema-label").textContent = `Catalog schema v${state.catalog.schemaVersion}`;
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
  // The two reasons an entry is unresolved here are completely different, and collapsing them
  // is what makes a registry misleading. A known theorem we have not typed in is formalization
  // backlog; a claim mathematics has not settled is the actual research frontier.
  const unformalized = state.entries.filter((entry) =>
    ["open", "formalizing"].includes(entry.status) && entry.literature !== "unresolved");
  const researchFrontier = state.entries.filter((entry) =>
    !isClosedStatus(entry.status) && entry.literature === "unresolved");
  const edgeCount = state.entries.reduce((total, entry) => total + entry.dependencies.length, 0);
  const reused = new Set(state.entries.flatMap((entry) => entry.dependencies)).size;
  // Each metric counts one kind of thing. The catalog is kernel-audited, the journal is a
  // record of attempts, and the local notes are typed into a browser; summing any two of them
  // is the category collapse the status/literature split exists to prevent, and it would
  // report a typed-in conjecture as part of the verified frontier.
  const active = state.workItems.filter((item) => ["exploring", "drafting", "blocked"].includes(item.stage)).length;
  const metricData = [
    ["Cataloged artifacts", state.entries.length, `${state.catalog.summary.valid} kernel-audited`],
    ["Proved here", proved, `${Math.round((proved / Math.max(state.entries.length, 1)) * 100)}% of registry`],
    ["Research frontier", researchFrontier.length, `unresolved in the literature · ${state.queue.length} local notes`],
    ["Formalization backlog", unformalized.length, "known results, not yet checked here"],
    ["Work in progress", active, `${state.workItems.length} journal items · untrusted`],
    ["Reusable results", reused, `${edgeCount} proof dependencies`],
  ];
  $("#metrics").innerHTML = metricData.map(([label, value, note]) => `
    <div class="metric"><div class="metric-label">${label}</div><div class="metric-value">${value}</div><p class="metric-note">${note}</p></div>`).join("");
  $("#edge-count").textContent = `${edgeCount} checked reuse edges`;

  $("#recent-results").innerHTML = [...state.entries].sort((a, b) => b.updated.localeCompare(a.updated)).slice(0, 5).map((entry) => `
    <article class="result-item" data-entry-id="${escapeHtml(entry.id)}" tabindex="0">
      <div><span class="result-title">${escapeHtml(entry.title)}</span><span class="result-decl mono">${escapeHtml(entry.statement)}</span></div>
      ${statusBadge(entry.status)}
      <span class="dependency-count">${entry.dependencies.length} ${entry.dependencies.length === 1 ? "dependency" : "dependencies"}</span>
    </article>`).join("");
  $$("[data-entry-id]", $("#recent-results")).forEach((item) => {
    const open = () => selectEntry(item.dataset.entryId);
    item.addEventListener("click", open);
    item.addEventListener("keydown", (event) => { if (event.key === "Enter") open(); });
  });
  renderWorkPreview();
  renderLineage();
}

/*! ## Work journal rendering

The board is the observational half of the workspace: it reports what the CLI recorded rather
than collecting anything. Everything shown here comes from `work/*.json` by way of
`web/data/work.json`, which every journal mutation republishes. */

function renderWork() {
  $("#work-count").textContent = state.workItems.length;
  const generated = $("#work-generated");
  if (generated) {
    generated.textContent = state.workError
      ? state.workError
      : state.work
        ? `Journal written ${formatTime(state.work.generated)}`
        : "No journal yet";
  }
  // Re-render only on a real change. Polling that rebuilt the DOM every few seconds would drop
  // the user's text selection and scroll position for no reason.
  const signature = JSON.stringify([state.workError, state.workItems.map((item) => [item.id, item.updated, item.stage, item.attempts])]);
  if (signature !== state.workSignature) {
    state.workSignature = signature;
    renderWorkBoard();
    renderWorkPreview();
    if (state.catalog) renderOverview();
  }
}

function renderWorkBoard() {
  const board = $("#work-board");
  if (!board) return;
  const problems = state.work?.problems ?? [];
  // A file that failed to decode is shown, not skipped. Work silently missing from the board a
  // human is relying on is worse than a visible complaint about a broken file.
  const problemBanner = problems.length
    ? `<div class="work-problems"><strong>${problems.length} journal file(s) could not be read</strong>${problems.map((problem) => `<span>${escapeHtml(problem)}</span>`).join("")}</div>`
    : "";
  const errorBanner = state.workError
    ? `<div class="work-problems"><strong>Journal unavailable</strong><span>${escapeHtml(state.workError)}</span></div>`
    : "";
  $("#work-empty").classList.toggle("hidden", state.workItems.length > 0 || problems.length > 0 || Boolean(state.workError));
  const columns = WORK_STAGES
    .filter(([stage]) => state.workItems.some((item) => item.stage === stage) || ["exploring", "drafting", "clean"].includes(stage))
    .map(([stage, label, hint]) => {
      const items = state.workItems.filter((item) => item.stage === stage);
      return `<section class="work-column">
        <div class="queue-column-header"><h2 title="${escapeHtml(hint)}">${label}</h2><span>${items.length}</span></div>
        <div class="queue-items">${items.map(workCard).join("") || `<p class="subtle">None</p>`}</div>
      </section>`;
    }).join("");
  board.innerHTML = errorBanner + problemBanner + `<div class="work-columns">${columns}</div>`;
  $$("[data-work-entry]", board).forEach((button) => button.addEventListener("click", () => selectEntry(button.dataset.workEntry)));
}

function workCard(item) {
  const check = item.lastCheck;
  // The verdict alone is not what makes the journal worth keeping. What a later session needs
  // is why it failed, what it reused, and what it rests on.
  const verdict = check
    ? `<div class="work-verdict ${check.clean ? "clean" : "failed"}">
         <strong>${check.clean ? "Lean accepted the draft" : "Not acceptable yet"}</strong>
         <span>${formatTime(check.checkedAt)} · ${check.declarations} declaration${check.declarations === 1 ? "" : "s"}</span>
       </div>
       ${check.errors.length ? `<ul class="work-errors">${check.errors.slice(0, 3).map((error) => `<li>${escapeHtml(error)}</li>`).join("")}</ul>` : ""}
       ${check.diagnostics.length && !check.errors.length ? `<ul class="work-errors">${check.diagnostics.slice(0, 2).map((line) => `<li>${escapeHtml(line.trim())}</li>`).join("")}</ul>` : ""}
       ${check.reuses.length ? `<div class="work-reuse"><span class="detail-label">Reuses</span>${check.reuses.map((id) => `<button class="dependency-link" data-work-entry="${escapeHtml(id)}">${escapeHtml(titleFor(id))} →</button>`).join("")}</div>` : ""}
       ${check.axioms.length ? `<div class="tag-row">${check.axioms.map((axiom) => `<span class="tag">${escapeHtml(axiom)}</span>`).join("")}</div>` : ""}`
    : `<p class="subtle">No check recorded yet.</p>`;
  return `<article class="queue-card work-card">
    <h3>${escapeHtml(item.title)}</h3>
    ${item.goal ? `<p>${escapeHtml(item.goal)}</p>` : ""}
    ${item.note ? `<p class="work-note">${escapeHtml(item.note)}</p>` : ""}
    ${item.entry ? `<p class="subtle">Registered as <button class="dependency-link" data-work-entry="${escapeHtml(item.entry)}">${escapeHtml(titleFor(item.entry))} →</button></p>` : ""}
    ${verdict}
    <div class="queue-card-footer">
      <span class="mono">${escapeHtml(item.id)}</span>
      <span>${item.attempts} attempt${item.attempts === 1 ? "" : "s"}</span>
      ${item.draft ? `<span class="mono work-draft" title="${escapeHtml(item.draft)}">${escapeHtml(basename(item.draft))}</span>` : ""}
    </div>
  </article>`;
}

function renderWorkPreview() {
  const container = $("#work-preview");
  if (!container) return;
  if (!state.workItems.length) {
    container.innerHTML = `<div class="empty-queue"><span>No work recorded.</span><code>frontier work add "&lt;title&gt;"</code></div>`;
    return;
  }
  container.innerHTML = state.workItems.slice(0, 4).map((item) => `
    <article class="queue-preview-item">
      <strong>${escapeHtml(item.title)}</strong>
      <div class="queue-preview-meta">
        <span class="work-stage stage-${escapeHtml(item.stage)}">${escapeHtml(item.stage)}</span>
        <span>·</span>
        <span>${item.attempts} attempt${item.attempts === 1 ? "" : "s"}</span>
        ${item.lastCheck ? `<span>·</span><span>${item.lastCheck.clean ? "clean" : "failing"}</span>` : ""}
      </div>
    </article>`).join("");
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
    `<button class="lineage-node" data-lineage-id="${escapeHtml(entry.id)}"><strong>${escapeHtml(entry.title)}</strong><span>${escapeHtml(entry.statement)}</span></button>`,
    index < chain.length - 1 ? `<span class="lineage-arrow" aria-hidden="true">→</span>` : "",
  ]).join("");
  $$("[data-lineage-id]").forEach((button) => button.addEventListener("click", () => selectEntry(button.dataset.lineageId)));
}

function filteredEntries() {
  return state.entries.filter((entry) => {
    if (state.status !== "all" && entry.status !== state.status) return false;
    if (state.literature !== "all" && entry.literature !== state.literature) return false;
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
    <tr data-row-id="${escapeHtml(entry.id)}" class="${entry.id === state.selectedId ? "selected" : ""}">
      <td><span class="table-title">${escapeHtml(entry.title)}</span><span class="table-decl mono">${escapeHtml(entry.statement)}</span></td>
      <td>${statusBadge(entry.status)}</td>
      <td>${literatureBadge(entry.literature)}</td>
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
    ? entry.dependencies.map((id) => `<button class="dependency-link" data-dependency-id="${escapeHtml(id)}">${escapeHtml(titleFor(id))} →</button>`).join("")
    : `<span class="subtle">No catalog dependencies</span>`;
  const sanityChecks = (entry.sanityChecks ?? []).length
    ? (entry.sanityChecks ?? []).map((check) => `<div class="trust-row"><code>${escapeHtml(check.name)}</code></div><pre class="type-block">${escapeHtml(check.type)}</pre>`).join("")
    : `<span class="subtle">None</span>`;
  $("#detail-panel").innerHTML = `
    <div class="tag-row">${statusBadge(entry.status)}${literatureBadge(entry.literature)}</div>
    <h2>${escapeHtml(entry.title)}</h2>
    <p class="detail-summary">${escapeHtml(entry.summary)}</p>
    ${formalizationNote(entry)}
    <div class="detail-section"><span class="detail-label">Lean proposition</span><pre class="type-block">${escapeHtml(entry.statementType)}</pre></div>
    <div class="detail-section"><span class="detail-label">Dependencies</span>${dependencies}</div>
    <div class="detail-section"><span class="detail-label">Tags</span><div class="tag-row">${entry.tags.map((tag) => `<span class="tag">${escapeHtml(tag)}</span>`).join("")}</div></div>
    <div class="detail-section">
      <span class="detail-label">Trust audit</span>
      <div class="trust-row"><span>Certificate</span><code>${escapeHtml(entry.certificate || "none")}</code></div>
      <div class="trust-row"><span>Evidence</span><strong>${escapeHtml(entry.evidence || "none")}</strong></div>
      ${entry.baseTheory ? `<div class="trust-row"><span>Relative to</span><strong>${escapeHtml(entry.baseTheory)}</strong></div>` : ""}
      <div class="trust-row"><span>Axioms</span><strong>${entry.axioms.length}</strong></div>
      <div class="tag-row">${entry.axioms.map((axiom) => `<span class="tag">${escapeHtml(axiom)}</span>`).join("") || `<span class="tag">axiom-free</span>`}</div>
    </div>
    <div class="detail-section">
      <span class="detail-label">Sanity checks</span>
      <p class="subtle">Checked lemmas guarding against mis-formalization. Not research results.</p>
      ${sanityChecks}
    </div>
    <div class="detail-section">
      <span class="detail-label">Provenance</span>
      <div class="trust-row"><span>Authors</span><strong>${escapeHtml(entry.authors.join(", ") || "none")}</strong></div>
      ${(entry.tooling ?? []).length ? `<div class="trust-row"><span>Tooling</span><strong>${escapeHtml((entry.tooling ?? []).join(", "))}</strong></div>` : ""}
      ${entry.citation ? `<p class="detail-summary">${escapeHtml(entry.citation)}</p>` : ""}
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
    return `<button class="graph-node ${entry.id === state.selectedId ? "active" : ""}" data-graph-id="${escapeHtml(entry.id)}" style="left:${position.x}px;top:${position.y}px"><strong>${escapeHtml(entry.title)}</strong><span>${entry.dependencies.length} dependencies · ${escapeHtml(entry.status)}</span></button>`;
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
  if (state.catalog) renderOverview();
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
  return `<article class="queue-card"><h3>${escapeHtml(item.title)}</h3><p>${escapeHtml(item.informal)}</p><div class="queue-card-footer"><i class="priority priority-${escapeHtml(item.priority)}"></i><span>${escapeHtml(displayTopic(item.topic))}</span><button class="mini-button" data-queue-action="scaffold" data-id="${escapeHtml(item.id)}">Lean</button><button class="mini-button" data-queue-action="advance" data-id="${escapeHtml(item.id)}">Advance</button><button class="mini-button" data-queue-action="edit" data-id="${escapeHtml(item.id)}">Edit</button></div></article>`;
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

// The path out of browser-local scratch. A note is only ever a note until something checks it,
// so the dialog hands over the two commands that make it durable and audited rather than
// leaving the reader to find them in the README.
function commandsFor(item) {
  const file = `${pascalCase(item.title)}.lean`;
  const id = slugify(item.title);
  return [
    `frontier work add ${shellQuote(item.title)} --goal ${shellQuote(item.informal)}`,
    `frontier check --work ${id} ${file}`,
  ].join("\n");
}

function shellQuote(value) {
  return `'${String(value ?? "").replaceAll("'", "'\\''")}'`;
}

function showScaffold(item) {
  state.scaffoldItem = item;
  $("#scaffold-code").textContent = scaffoldFor(item);
  $("#scaffold-commands").textContent = commandsFor(item);
  $("#scaffold-dialog").showModal();
}

async function copyScaffold() {
  await navigator.clipboard.writeText($("#scaffold-code").textContent);
  showToast("Lean scaffold copied");
}

async function copyCommands() {
  await navigator.clipboard.writeText($("#scaffold-commands").textContent);
  showToast("Commands copied");
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

const CLOSED_STATUSES = ["conditional", "proved", "disproved", "independent", "undecidable"];

function isClosedStatus(status) {
  return CLOSED_STATUSES.includes(status);
}

function statusBadge(status) {
  return `<span class="status-badge status-${escapeHtml(status)}" title="What this repository has checked">${escapeHtml(status)}</span>`;
}

function literatureBadge(literature) {
  const label = literature === "unresolved" ? "open problem" : `lit: ${literature}`;
  return `<span class="status-badge literature-${escapeHtml(literature)}" title="What the mathematical literature knows, independent of this repository">${escapeHtml(label)}</span>`;
}

/** Spell out the status/literature combination in words, since the pair is the whole point. */
function formalizationNote(entry) {
  if (!isClosedStatus(entry.status) && entry.literature === "unresolved") {
    return `<p class="detail-note">Unresolved in the literature and unresolved here. This is a genuine research target.</p>`;
  }
  if (!isClosedStatus(entry.status)) {
    return `<p class="detail-note">Settled in the literature (${escapeHtml(entry.literature)}) but not yet formalized in this repository. This is a formalization task, not an open problem.</p>`;
  }
  if (entry.literature === "unresolved") {
    return `<p class="detail-note">Checked here by Lean, with no literature reference recorded. Verify this is genuinely new before citing it as such.</p>`;
  }
  return "";
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
function basename(path) { return String(path).split("/").pop(); }

// Journal timestamps are full UTC instants rather than the catalog's dates, because the point
// of following along is knowing whether something happened a minute or a week ago.
function formatTime(instant) {
  if (!instant) return "";
  const parsed = new Date(instant);
  if (Number.isNaN(parsed.getTime())) return instant;
  const elapsed = (Date.now() - parsed.getTime()) / 1000;
  if (elapsed < 60) return "just now";
  if (elapsed < 3600) return `${Math.floor(elapsed / 60)}m ago`;
  if (elapsed < 86400) return `${Math.floor(elapsed / 3600)}h ago`;
  return new Intl.DateTimeFormat("en", { month: "short", day: "numeric", hour: "numeric", minute: "2-digit" }).format(parsed);
}
const HTML_ESCAPES = { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" };

// Escapes the quote characters as well as `&<>`. The quotes are the point: this output is
// interpolated into attribute values as often as into text, and the obvious implementation —
// a `textContent` round-trip through a detached node — escapes only `&<>`. A journal draft
// path or a catalog id containing `"` would close the attribute and inject markup, which is
// exactly what calling an escaping function is supposed to prevent.
function escapeHtml(value) {
  return String(value).replace(/[&<>"']/g, (character) => HTML_ESCAPES[character]);
}

let toastTimer;
function showToast(message) {
  const toast = $("#toast");
  toast.textContent = message;
  toast.classList.add("show");
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => toast.classList.remove("show"), 1800);
}
