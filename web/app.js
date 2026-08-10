import * as d3 from "https://cdn.jsdelivr.net/npm/d3@7/+esm";

const query = new URLSearchParams(window.location.search);
const requestedGraph = query.get("graph");
const requestedTheorem = query.get("theorem");
const REPO_ROOT = window.location.pathname.includes("/web/") ? "../" : "./";
const THEOREMS_URL = "./theorems.json";
const DATA_URLS = [`${REPO_ROOT}MathNetwork/Graph/project.json`];
const KIND_LABELS = {
  proposition: "Propositions",
  "proof-family": "Proof families",
  concept: "Concepts",
  source: "Sources",
};
const KIND_COLORS = {
  proposition: "#366b80",
  "proof-family": "#a66a2a",
  concept: "#4c7d74",
  source: "#795a76",
};
const PROOF_COLORS = ["#d16b5d", "#3f7f8f", "#b27a2d", "#7a6397", "#4f8b73", "#b05d91", "#6d7fbd", "#9b7a4b"];
const VERIFICATION = {
  checked: { glyph: "✓", label: "Lean-checked", className: "checked" },
  "imported-checked": { glyph: "↗", label: "Imported + checked", className: "imported" },
  formalized: { glyph: "○", label: "Formalized statement", className: "formalized" },
  planned: { glyph: "·", label: "Planned", className: "planned" },
  informal: { glyph: "?", label: "Informal", className: "informal" },
};
const ROUTE_KIND_LABELS = {
  "library-complete": "library baseline",
  "pedagogical-narrow": "narrow pedagogical route",
  "foundation-comparison": "foundation comparison",
  computational: "computational route",
};
const GITHUB_REPO = "https://github.com/liuyao12/math-net";

const state = {
  graph: null,
  theorems: [],
  theoremNumber: requestedTheorem || null,
  selectedId: null,
  selectedProofId: null,
  search: "",
  kinds: new Set(Object.keys(KIND_LABELS)),
  route: "all",
  simulation: null,
  sourceRequest: 0,
  focusDistances: new Map(),
  showImplementation: false,
};

const $ = (selector) => document.querySelector(selector);
const svg = d3.select("#network");
const stage = $("#graph-stage");

function escapeHtml(value) {
  return String(value ?? "").replace(/[&<>"']/g, (character) => ({
    "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;",
  }[character]));
}

const LEAN_KEYWORDS = new Set([
  "theorem", "lemma", "def", "abbrev", "example", "axiom", "opaque", "structure", "class",
  "inductive", "namespace", "end", "section", "variable", "universe", "open", "where",
  "let", "in", "if", "then", "else", "match", "with", "fun", "by", "do", "have", "show", "from",
  "forall", "exists", "include", "omit", "return", "termination_by", "decreasing_by", "deriving",
]);
const LEAN_TACTICS = new Set([
  "simp", "simpa", "rw", "rfl", "exact", "apply", "refine", "constructor", "intro", "intros", "cases",
  "induction", "rcases", "obtain", "norm_num", "ring", "ring_nf", "linarith", "nlinarith", "omega",
  "aesop", "positivity", "field_simp", "norm_cast", "push_cast", "decide", "assumption", "contradiction",
]);

function highlightLean(source) {
  const tokenPattern = /--[^\n]*|\/-[\s\S]*?-\/|"(?:\\.|[^"\\])*"|`[^`]*`|\b\d+(?:\.\d+)?\b|[A-Za-z_][A-Za-z0-9_'.]*|./gs;
  const tokens = String(source).match(tokenPattern) || [];
  let previousWord = "";
  let declarationName = false;
  let namespaceName = false;
  return tokens.map((token) => {
    const escaped = escapeHtml(token);
    if (token.startsWith("--") || token.startsWith("/-")) return `<span class="lean-comment">${escaped}</span>`;
    if (token.startsWith('"') || token.startsWith("`") ) return `<span class="lean-string">${escaped}</span>`;
    if (/^\d/.test(token)) return `<span class="lean-number">${escaped}</span>`;
    const word = token;
    let highlighted = escaped;
    if (LEAN_TACTICS.has(word)) highlighted = `<span class="lean-tactic">${escaped}</span>`;
    else if (LEAN_KEYWORDS.has(word)) {
      highlighted = `<span class="lean-keyword">${escaped}</span>`;
      declarationName = ["theorem", "lemma", "def", "abbrev", "example", "axiom", "opaque", "structure", "class", "inductive"].includes(word);
      namespaceName = ["namespace", "open"].includes(word);
    } else if (declarationName) {
      highlighted = `<span class="lean-declaration">${escaped}</span>`;
      declarationName = false;
    } else if (namespaceName) {
      highlighted = `<span class="lean-namespace">${escaped}</span>`;
      namespaceName = false;
    } else if (/^[A-Z][A-Za-z0-9_'.]*$/.test(word)) highlighted = `<span class="lean-type">${escaped}</span>`;
    else if (/^[a-z_][A-Za-z0-9_']*$/.test(word) && ["(", "{", ":"].includes(previousWord)) highlighted = `<span class="lean-variable">${escaped}</span>`;
    if (/^[A-Za-z_][A-Za-z0-9_'.]*$/.test(word)) previousWord = word;
    else if (!/^\s+$/.test(word)) previousWord = word;
    return highlighted;
  }).join("") || "";
}

function sourceFileFor(node) {
  const local = (node.formalizations || []).find((item) => item.file)?.file;
  if (local) return local;
  if (node.module?.startsWith("MathNetwork.")) return `${node.module.replaceAll(".", "/")}.lean`;
  if (node.locator?.startsWith("mathlib/")) {
    return `${node.locator.slice("mathlib/".length).replaceAll(".", "/")}.lean`;
  }
  return null;
}

function sourceUrlFor(node) {
  const file = sourceFileFor(node);
  if (!file) return null;
  if (node.locator?.startsWith("mathlib/")) {
    return `https://raw.githubusercontent.com/leanprover-community/mathlib4/master/${file}`;
  }
  return `${REPO_ROOT}${file}`;
}

function githubUrlFor(node, item = null) {
  const file = item?.file || sourceFileFor(node);
  if (file?.startsWith("MathNetwork/")) return `${GITHUB_REPO}/blob/main/${file}`;
  const locator = item?.locator || node.locator;
  if (locator?.startsWith("mathlib/")) {
    const file = `${locator.slice("mathlib/".length).replaceAll(".", "/")}.lean`;
    return `https://github.com/leanprover-community/mathlib4/blob/master/${file}`;
  }
  return null;
}

function declarationSource(text, name) {
  const short = name.split(".").pop();
  const escaped = short.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const declaration = new RegExp(`^\\s*(theorem|lemma|def|noncomputable def|example|axiom|instance|class|structure|inductive)\\s+${escaped}\\b`, "m");
  const match = declaration.exec(text);
  if (!match) return null;
  const start = text.lastIndexOf("\n", match.index) + 1;
  const rest = text.slice(match.index + match[0].length);
  const next = rest.search(/\n(?=\s*(?:theorem|lemma|def|noncomputable def|example|axiom)\s+)/);
  return text.slice(start, next < 0 ? text.length : match.index + match[0].length + next + 1).trim();
}

async function loadProofSource(node, container, request) {
  const file = sourceFileFor(node);
  const formalization = (node.formalizations || []).find((item) => item.file);
  if (!file) {
    container.textContent = "No source locator is available for this generated declaration. The statement above is the checked declaration type.";
    container.classList.remove("pending");
    return;
  }
  const path = sourceUrlFor(node);
  try {
    const response = await fetch(path);
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    const text = await response.text();
    if (request !== state.sourceRequest) return;
    const source = declarationSource(text, formalization?.name || node.namespace || node.label);
    const code = source || `-- Source file: ${file}\n-- The declaration is elaborated or generated in this module.\n\n${text}`;
    container.innerHTML = `<code>${highlightLean(code)}</code>`;
    container.classList.remove("pending");
  } catch (error) {
    if (request !== state.sourceRequest) return;
    container.textContent = `Source unavailable for ${file}. The checked declaration is shown above.`;
    container.classList.remove("pending");
  }
}

function nodeMap() {
  return new Map(state.graph.nodes.map((node) => [node.id, node]));
}

function isSearchMatch(node) {
  if (!state.search) return true;
  const formalizationNames = (node.formalizations || []).map((item) => item.name);
  const haystack = [node.label, node.namespace, node.module, node.description, node.statement, node.method, ...formalizationNames, ...(node.tags || [])]
    .filter(Boolean).join(" ").toLowerCase();
  return haystack.includes(state.search.toLowerCase());
}

function searchFocus(nodes, edges) {
  if (!state.search) return new Set(nodes.map((node) => node.id));
  const focus = new Set(nodes.filter(isSearchMatch).map((node) => node.id));
  let changed = true;
  while (changed) {
    changed = false;
    edges.forEach((edge) => {
      if (focus.has(edge.target.id) && !focus.has(edge.source.id)) {
        focus.add(edge.source.id);
        changed = true;
      }
      if (focus.has(edge.source.id) && !focus.has(edge.target.id)) {
        focus.add(edge.target.id);
        changed = true;
      }
    });
  }
  return focus;
}

function routeMatch(node, edges) {
  if (state.route === "all") return true;
  if (node.id === state.route) return true;
  return edges.some((edge) => edge.source.id === state.route && edge.target.id === node.id);
}

function focusDistances(nodeId, edges, maxDepth = 3) {
  const distances = new Map([[nodeId, 0]]);
  const adjacency = new Map();
  edges.forEach((edge) => {
    // Edges point from a used declaration to the proof that uses it. For a
    // selected theorem, walk only upstream so the canvas remains a readable
    // dependency tree rather than expanding through every dependent theorem.
    if (!adjacency.has(edge.target.id)) adjacency.set(edge.target.id, []);
    adjacency.get(edge.target.id).push(edge.source.id);
  });
  let frontier = [nodeId];
  for (let depth = 1; depth <= maxDepth; depth += 1) {
    const next = [];
    frontier.forEach((current) => (adjacency.get(current) || []).forEach((neighbor) => {
      if (!distances.has(neighbor)) { distances.set(neighbor, depth); next.push(neighbor); }
    }));
    frontier = next;
  }
  return distances;
}

function visibleGraph() {
  const nodesById = nodeMap();
  const edgeData = state.graph.edges
    .filter((edge) => edge.relation === "used-in-proof")
    .filter((edge) => !state.selectedProofId || edge.proof === state.selectedProofId)
    .map((edge) => ({ ...edge, source: nodesById.get(edge.source.id), target: nodesById.get(edge.target.id) }))
    .filter((edge) => edge.source && edge.target);
  const candidateNodes = state.graph.nodes.filter((node) => state.kinds.has(node.kind));
  state.focusDistances = state.selectedId ? focusDistances(state.selectedId, edgeData, 3) : new Map();
  const focus = searchFocus(candidateNodes, edgeData);
  const visibleNodes = candidateNodes.filter((node) => {
    if (state.selectedId && !state.focusDistances.has(node.id)) return false;
    if (state.search && !focus.has(node.id)) return false;
    if (node.kind === "proof-family" && state.route !== "all" && node.id !== state.route) return false;
    return true;
  });
  const allowed = new Set(visibleNodes.map((node) => node.id));
  const visibleEdges = edgeData.filter((edge) => allowed.has(edge.source.id) && allowed.has(edge.target.id));
  if (state.route !== "all") {
    const routeNode = nodesById.get(state.route);
    const adjacent = new Set([state.route]);
    visibleEdges.forEach((edge) => {
      if (edge.source.id === state.route) adjacent.add(edge.target.id);
      if (edge.target.id === state.route) adjacent.add(edge.source.id);
    });
    return { nodes: visibleNodes.filter((node) => adjacent.has(node.id) || node.id === routeNode?.id), edges: visibleEdges.filter((edge) => adjacent.has(edge.source.id) && adjacent.has(edge.target.id)) };
  }
  return { nodes: visibleNodes, edges: visibleEdges };
}

function kindControls() {
  const container = $("#kind-filters");
  Object.entries(KIND_LABELS).forEach(([key, label]) => {
    const wrapper = document.createElement("label");
    wrapper.className = "filter-option";
    wrapper.innerHTML = `<input type="checkbox" data-kind="${key}" checked><span class="filter-dot ${key}"></span><span>${label}</span>`;
    wrapper.querySelector("input").addEventListener("change", (event) => {
      event.target.checked ? state.kinds.add(key) : state.kinds.delete(key);
      draw();
    });
    container.append(wrapper);
  });
}

function routeControls() {
  const select = $("#route-filter");
  state.graph.nodes.filter((node) => node.kind === "proof-family").forEach((node) => {
    const option = document.createElement("option");
    option.value = node.id;
    option.textContent = node.label;
    select.append(option);
  });
  select.addEventListener("change", (event) => { state.route = event.target.value; draw(); });
}

function theoremForGraph() {
  if (requestedGraph === "fermat") return "20";
  if (requestedGraph === "euler") return "17";
  return null;
}

function populateTheoremSelect() {
  const select = $("#theorem-select");
  state.theorems.forEach((theorem) => {
    const option = document.createElement("option");
    option.value = String(theorem.number);
    option.textContent = `${String(theorem.number).padStart(2, "0")} · ${theorem.title}`;
    select.append(option);
  });
  state.theoremNumber = state.theoremNumber || null;
  if (state.theoremNumber) select.value = String(state.theoremNumber);
  updateTheoremNote();
  select.addEventListener("change", (event) => {
    const number = event.target.value;
    if (!number) {
      const next = new URL(window.location.href);
      next.searchParams.delete("theorem");
      history.replaceState(null, "", next);
      state.theoremNumber = null;
      updateTheoremNote();
      return;
    }
    const theorem = state.theorems.find((item) => String(item.number) === number);
    const next = new URL(window.location.href);
    next.searchParams.set("theorem", number);
    next.searchParams.delete("graph");
    history.pushState(null, "", next);
    state.theoremNumber = number;
    updateTheoremNote();
    selectTheoremNode();
  });
}

function updateTheoremNote() {
  const note = $("#theorem-note");
  const theorem = state.theorems.find((item) => String(item.number) === String(state.theoremNumber));
  if (!theorem) {
    note.textContent = "Official catalogue · choose a theorem to inspect its status.";
    return;
  }
  note.innerHTML = theorem.graph
    ? `<span class="theorem-ready">✓ included in project graph</span> · focus available`
    : "catalogued · dependency graph not imported yet";
}

function selectTheoremNode() {
  const theorem = state.theorems.find((item) => String(item.number) === String(state.theoremNumber));
  const node = state.graph?.nodes.find((item) => theorem?.namespace === item.namespace ||
    (theorem?.namespace && (item.formalizations || []).some((formalization) => formalization.name === theorem.namespace)));
  if (node) selectNode(node.id);
}

function legend() {
  const container = $("#legend");
  Object.entries(KIND_LABELS).forEach(([key, label]) => {
    const item = document.createElement("span");
    item.className = "legend-item";
    item.innerHTML = `<span class="legend-dot ${key}"></span>${label}`;
    container.append(item);
  });
  const labels = proofLabels();
  if (labels.size) {
    const heading = document.createElement("div");
    heading.className = "legend-heading";
    heading.textContent = "Arrow colors · proof provenance";
    container.append(heading);
    const proofContainer = document.createElement("div");
    proofContainer.className = "legend-proofs";
    [...labels.entries()].forEach(([id, label]) => {
      const item = document.createElement("span");
      item.className = "legend-item";
      item.innerHTML = `<span class="legend-line" style="background:${proofColor(id)}"></span>${escapeHtml(label)}`;
      proofContainer.append(item);
    });
    container.append(proofContainer);
  }
}

function labelFor(node) {
  return node.label.length > 29 ? `${node.label.slice(0, 27)}…` : node.label;
}

function verificationFor(node) {
  return VERIFICATION[node.verification?.state] || VERIFICATION.informal;
}

function verificationText(node) {
  const meta = node.verification || {};
  const status = verificationFor(node);
  const condition = meta.conditional ? " · conditional on stated hypotheses" : "";
  const scope = meta.scope === "local-with-imports" ? " · local route with imported lemmas" : "";
  return `${status.glyph} ${status.label}${condition}${scope}`;
}

function isMajorNode(node) {
  return node.kind !== "source" || node.declarationKind === "proposition";
}

function proofColor(proofId = "") {
  for (const node of state.graph?.nodes || []) {
    const proof = (node.proofs || []).find((item) => item.id === proofId);
    if (proof?.color) return proof.color;
  }
  let hash = 0;
  for (const character of proofId) hash = ((hash << 5) - hash + character.charCodeAt(0)) | 0;
  return PROOF_COLORS[Math.abs(hash) % PROOF_COLORS.length];
}

function proofLabels() {
  const labels = new Map();
  state.graph.nodes.forEach((node) => (node.proofs || []).forEach((proof) => labels.set(proof.id, proof.label)));
  state.graph.edges.forEach((edge) => { if (edge.proof && !labels.has(edge.proof)) labels.set(edge.proof, edge.proof); });
  return labels;
}

function nodeNeighbors(nodeId) {
  const map = nodeMap();
  return state.graph.edges.flatMap((edge) => {
    if (edge.source.id === nodeId) return [{ relation: edge.relation, node: map.get(edge.target.id), direction: "out" }];
    if (edge.target.id === nodeId) return [{ relation: edge.relation, node: map.get(edge.source.id), direction: "in" }];
    return [];
  }).filter((item) => item.node);
}

function selectNode(nodeId) {
  state.selectedId = nodeId;
  state.selectedProofId = null;
  renderInspector();
  draw();
}

function selectProof(proofId) {
  state.selectedProofId = proofId;
  renderInspector();
  draw();
}

function renderInspector() {
  const content = $("#inspector-content");
  const node = nodeMap().get(state.selectedId);
  if (!node) {
    state.sourceRequest += 1;
    content.innerHTML = `<div class="empty-inspector"><div class="empty-glyph">◎</div><p>Click a node to inspect its statement, verification status, and proof dependencies.</p></div>`;
    return;
  }
  const sourceRequest = ++state.sourceRequest;
  const neighbors = nodeNeighbors(node.id);
  const github = githubUrlFor(node);
  const formalizations = (node.formalizations || []).map((item) => {
    const file = item.file ? `<br><span>${escapeHtml(item.file)}${item.anchor ? ` · ${escapeHtml(item.anchor)}` : ""}</span>` : "";
    const github = githubUrlFor(node, item);
    const link = github ? ` <a href="${escapeHtml(github)}" target="_blank" rel="noreferrer">GitHub ↗</a>` : "";
    return `<div class="formalization">${escapeHtml(item.language)} · ${escapeHtml(item.name)}${link}${file}</div>`;
  }).join("");
  const tags = (node.tags || []).map((tag) => `<span class="tag">${escapeHtml(tag)}</span>`).join("");
  const routes = node.assumptions ? node.assumptions.map((item) => `<span class="tag">${escapeHtml(item)}</span>`).join("") : "";
  const mergeNote = node.declarationCount > 1
    ? `<div class="detail-block"><div class="detail-label">Merged proposition</div><p>Exact checked statement shared by ${node.declarationCount} declarations. Each formalization below remains available as a separate proof/source route.</p></div>`
    : "";
  const depthNote = Number.isInteger(node.dependencyDepth)
    ? `<div class="detail-block"><div class="detail-label">Dependency layer</div><p>Imported mathlib declaration · layer ${node.dependencyDepth} of the bounded closure.</p></div>`
    : "";
  const proofs = (node.proofs || []).map((proof) => `<div class="proof-row ${state.selectedProofId === proof.id ? "selected" : ""}"><button class="proof-select" data-proof="${escapeHtml(proof.id)}">${escapeHtml(proof.label)}${proof.routeKind ? `<small>${escapeHtml(ROUTE_KIND_LABELS[proof.routeKind] || proof.routeKind)}</small>` : ""}</button><span class="proof-status">${escapeHtml(proof.status || "planned")}</span></div>`).join("");
  const incoming = neighbors.filter(({ direction }) => direction === "in");
  const outgoing = neighbors.filter(({ direction }) => direction === "out");
  const neighborRows = [
    incoming.length ? `<div class="detail-label">Proof dependencies</div>${incoming.map(({ node: neighbor }) => `<div class="relation-row"><span class="relation-name">used in proof</span><button class="neighbor" data-neighbor="${escapeHtml(neighbor.id)}">${escapeHtml(neighbor.label)}</button></div>`).join("")}` : "",
    outgoing.length ? `<div class="detail-label">Used in these proofs</div>${outgoing.map(({ node: neighbor }) => `<div class="relation-row"><span class="relation-name">proof target</span><button class="neighbor" data-neighbor="${escapeHtml(neighbor.id)}">${escapeHtml(neighbor.label)}</button></div>`).join("")}` : "",
  ].join("");
  content.innerHTML = `
    <span class="node-kind ${escapeHtml(node.kind)}">${escapeHtml(KIND_LABELS[node.kind])}</span>
    <div class="verification-badge ${verificationFor(node).className}"><span>${verificationFor(node).glyph}</span>${verificationText(node)}</div>
    <h2>${escapeHtml(node.label)}</h2>
    ${mergeNote}
    ${depthNote}
    ${node.method && node.statement ? `<div class="detail-block"><div class="detail-label">Method</div><p>${escapeHtml(node.method)}</p></div>` : ""}
    ${tags ? `<div class="detail-block"><div class="detail-label">Tags</div><div class="tag-list">${tags}</div></div>` : ""}
    ${routes ? `<div class="detail-block"><div class="detail-label">Assumptions</div><div class="tag-list">${routes}</div></div>` : ""}
    ${node.verification?.note ? `<div class="detail-block"><div class="detail-label">Verification note</div><p>${escapeHtml(node.verification.note)}</p></div>` : ""}
    ${formalizations ? `<div class="detail-block"><div class="detail-label">Formalization</div>${formalizations}</div>` : ""}
    ${github && !formalizations ? `<div class="detail-block"><div class="detail-label">Source</div><div class="formalization"><a href="${escapeHtml(github)}" target="_blank" rel="noreferrer">Open declaration on GitHub ↗</a></div></div>` : ""}
    <div class="detail-block"><div class="detail-label">Lean proof source · quoted code</div><blockquote class="proof-source pending" id="proof-source"><code>Loading declaration…</code></blockquote></div>
    ${proofs ? `<div class="detail-block"><div class="detail-label">Proofs · select one to filter dependencies</div><div class="proof-list">${proofs}</div></div>` : ""}
    ${neighborRows ? `<div class="detail-block"><div class="neighbor-list">${neighborRows}</div></div>` : ""}
  `;
  content.querySelectorAll("[data-neighbor]").forEach((button) => button.addEventListener("click", () => selectNode(button.dataset.neighbor)));
  content.querySelectorAll("[data-proof]").forEach((button) => button.addEventListener("click", () => selectProof(button.dataset.proof)));
  loadProofSource(node, content.querySelector("#proof-source"), sourceRequest);
}

function updateHighlight() {
  // visibleGraph has already computed the bounded, upstream dependency
  // neighborhood. Reuse it here so the status text and opacity treatment
  // describe exactly the graph on screen.
  const neighborhood = state.selectedId ? new Set(state.focusDistances.keys()) : new Set();
  svg.selectAll(".node-dot").classed("selected", (node) => node.id === state.selectedId).classed("dimmed", (node) => state.selectedId && !neighborhood.has(node.id));
  svg.selectAll(".node-label").classed("dimmed", (node) => state.selectedId && !neighborhood.has(node.id));
  svg.selectAll(".graph-link").classed("dimmed", (edge) => state.selectedId && (!neighborhood.has(edge.source.id) || !neighborhood.has(edge.target.id)));
  const focusStatus = $("#focus-status");
  if (focusStatus) {
    const selected = state.selectedId ? nodeMap().get(state.selectedId) : null;
    focusStatus.textContent = selected
      ? `${neighborhood.size} nodes in 3-level focus · ${selected.label}`
      : "all theorem nodes shown · select a theorem to focus";
  }
}

function dependencyRanks(nodes, edges) {
  const ranks = new Map(nodes.map((item) => [item.id, 0]));
  // Edges point from a used declaration to the proof that uses it. Repeated
  // relaxation gives a readable top-to-bottom layering while remaining robust
  // if an imported graph contains a small cycle.
  const maxPasses = nodes.length > 400 ? 12 : nodes.length;
  for (let pass = 0; pass < maxPasses; pass += 1) {
    let changed = false;
    edges.forEach((edge) => {
      const next = Math.min(nodes.length - 1, (ranks.get(edge.source.id) || 0) + 1);
      if (next > (ranks.get(edge.target.id) || 0)) {
        ranks.set(edge.target.id, next);
        changed = true;
      }
    });
    if (!changed) break;
  }
  return ranks;
}

function straightLinkPath(edge) {
  const x1 = edge.source.x;
  const y1 = edge.source.y;
  const x2 = edge.target.x;
  const y2 = edge.target.y;
  return `M${x1},${y1} L${x2},${y2}`;
}

function draw() {
  if (!state.graph) return;
  const { nodes, edges } = visibleGraph();
  $("#visible-node-count").textContent = nodes.length;
  $("#visible-edge-count").textContent = edges.length;
  svg.selectAll("*").remove();
  const width = stage.clientWidth;
  const height = stage.clientHeight;
  svg.attr("viewBox", `0 0 ${width} ${height}`);
  const defs = svg.append("defs");
  defs.append("marker").attr("id", "arrow-used-in-proof").attr("viewBox", "0 -4 8 8").attr("refX", 20).attr("refY", 0).attr("markerWidth", 5).attr("markerHeight", 5).attr("orient", "auto").append("path").attr("d", "M0,-4L8,0L0,4").attr("fill", "context-stroke");
  const root = svg.append("g");
  svg.call(d3.zoom().scaleExtent([0.35, 3]).on("zoom", (event) => root.attr("transform", event.transform)));
  const labels = proofLabels();
  const maxFocusDistance = Math.max(0, ...nodes.map((node) => state.focusDistances.get(node.id) || 0));
  const ranks = state.selectedId
    ? new Map(nodes.map((item) => [item.id, maxFocusDistance - (state.focusDistances.get(item.id) || 0)]))
    : dependencyRanks(nodes, edges);
  const maxRank = Math.max(0, ...Array.from(ranks.values()));
  const layerGap = Math.max(38, Math.min(105, (height - 90) / Math.max(1, maxRank)));
  const largeGraph = nodes.length > 400;
  const nodesByRank = d3.group(nodes, (item) => ranks.get(item.id) || 0);
  nodesByRank.forEach((layer, rank) => layer.forEach((item, index) => {
    item.x = width * (index + 1) / (layer.length + 1);
    item.y = rank * layerGap + 45;
  }));
  const link = root.append("g").attr("aria-hidden", "true").selectAll("path").data(edges, (edge) => edge.id).join("path")
    .attr("class", "graph-link used-in-proof")
    .classed("implementation-link", (edge) => !isMajorNode(edge.source) && !isMajorNode(edge.target))
    .attr("stroke", (edge) => proofColor(edge.proof))
    .attr("marker-end", "url(#arrow-used-in-proof)");
  link.append("title").text((edge) => `proof: ${labels.get(edge.proof) || edge.proof || "unknown"}\n${edge.description || "used in proof"}`);
  const node = root.append("g").selectAll("g").data(nodes, (item) => item.id).join("g").attr("role", "button").attr("aria-label", (item) => item.label).classed("major-node", (item) => isMajorNode(item)).classed("implementation-node", (item) => !isMajorNode(item)).on("click", (_, item) => selectNode(item.id)).call(d3.drag().on("start", (event, item) => { if (!state.simulation) return; if (!event.active) state.simulation.alphaTarget(0.3).restart(); item.fx = item.x; item.fy = item.y; }).on("drag", (event, item) => { if (!state.simulation) return; item.fx = event.x; item.fy = event.y; }).on("end", (event, item) => { if (!state.simulation) return; if (!event.active) state.simulation.alphaTarget(0); item.fx = null; item.fy = null; }));
  node.append("circle").attr("class", "node-dot").classed("implementation", (item) => !isMajorNode(item)).attr("data-focus-distance", (item) => state.focusDistances.get(item.id) ?? "").attr("r", (item) => item.kind === "proof-family" ? 10 : isMajorNode(item) && item.kind === "proposition" ? 8 : isMajorNode(item) ? 6 : 4).attr("fill", (item) => KIND_COLORS[item.kind]);
  node.append("text").attr("class", "node-label").classed("implementation", (item) => !isMajorNode(item)).attr("data-focus-distance", (item) => state.focusDistances.get(item.id) ?? "").attr("x", 13).attr("y", 4).text((item) => `${verificationFor(item).glyph} ${labelFor(item)}`).classed("hidden", (item) => (!state.showImplementation && !isMajorNode(item)) || (item.label.length > 31 && nodes.length > 12));
  state.simulation?.stop();
  state.simulation = null;
  if (largeGraph) {
    link.attr("d", straightLinkPath);
    node.attr("transform", (item) => `translate(${item.x},${item.y})`);
  } else {
    state.simulation = d3.forceSimulation(nodes).force("link", d3.forceLink(edges).id((item) => item.id).distance(105).strength(0.3)).force("y", d3.forceY((item) => (ranks.get(item.id) || 0) * layerGap + 45).strength(0.9)).force("x", d3.forceX(width / 2).strength(0.08)).force("charge", d3.forceManyBody().strength(-260)).force("collide", d3.forceCollide().radius((item) => item.kind === "proof-family" ? 30 : 25)).on("tick", () => {
      link.attr("d", straightLinkPath);
      node.attr("transform", (item) => `translate(${item.x},${item.y})`);
    });
  }
  updateHighlight();
}

async function load() {
  try {
    const [responses, theoremResponse] = await Promise.all([
      Promise.all(DATA_URLS.map((url) => fetch(url))),
      fetch(THEOREMS_URL),
    ]);
    const failed = responses.find((response) => !response.ok);
    if (failed) throw new Error(`Could not load ${DATA_URLS.join(", ")}`);
    const graphs = await Promise.all(responses.map((response) => response.json()));
    if (theoremResponse.ok) state.theorems = await theoremResponse.json();
    state.graph = graphs.length === 1 ? graphs[0] : {
      schemaVersion: graphs[0].schemaVersion,
      graphId: "math-net-project",
      label: "math-net project: Fermat + Euler applications",
      nodes: graphs.flatMap((graph) => graph.nodes),
      edges: graphs.flatMap((graph) => graph.edges),
    };
    $("#graph-badge").textContent = `${state.graph.nodes.length} nodes · ${state.graph.edges.length} links`;
    $("#network-title").textContent = state.graph.label;
    $(".data-source code").textContent = DATA_URLS.map((url) => url.split("/").pop()).join(" + ");
    $("#loading-state").remove();
    populateTheoremSelect();
    kindControls();
    routeControls();
    legend();
    selectTheoremNode();
    draw();
  } catch (error) {
    const loading = $("#loading-state");
    loading.classList.add("error");
    loading.textContent = "The graph could not load. Serve the repository root, then open /web/.";
    console.error(error);
  }
}

$("#search").addEventListener("input", (event) => { state.search = event.target.value.trim(); draw(); });
$("#reset").addEventListener("click", () => {
  state.selectedId = null;
  state.selectedProofId = null;
  state.search = "";
  state.route = "all";
  $("#search").value = "";
  $("#route-filter").value = "all";
  document.querySelectorAll("#kind-filters input[type=checkbox]").forEach((input) => { input.checked = true; });
  state.showImplementation = false;
  $("#show-implementation").checked = false;
  state.kinds = new Set(Object.keys(KIND_LABELS));
  renderInspector();
  draw();
});
$("#clear-selection").addEventListener("click", () => { state.selectedId = null; state.selectedProofId = null; renderInspector(); draw(); });
$("#show-implementation").addEventListener("change", (event) => { state.showImplementation = event.target.checked; draw(); });
window.addEventListener("resize", () => draw());
load();
