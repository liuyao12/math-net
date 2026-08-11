import * as d3 from "https://cdn.jsdelivr.net/npm/d3@7/+esm";

const query = new URLSearchParams(window.location.search);
const requestedGraph = query.get("graph");
const requestedTheorem = query.get("theorem");
const REPO_ROOT = window.location.pathname.includes("/web/") ? "../" : "./";
const THEOREMS_URL = "./theorems.json";
const DATA_URLS = [`${REPO_ROOT}MathNetwork/Graph/project.json`];
const DECLARATION_LABELS = {
  theorem: "Theorems",
  opaque: "Opaque declarations",
  conjecture: "Axioms",
  definition: "Definitions",
  quotient: "Quotients",
  inductive: "Inductives",
  constructor: "Constructors",
  recursor: "Recursors",
  "proof-family": "Proof families",
  proposition: "Propositions",
  concept: "Definitions",
  source: "Imported declarations",
};
const DECLARATION_COLORS = {
  theorem: "#366b80",
  opaque: "#366b80",
  conjecture: "#b45e4d",
  definition: "#4c7d74",
  quotient: "#4c7d74",
  inductive: "#795a76",
  constructor: "#795a76",
  recursor: "#795a76",
  "proof-family": "#a66a2a",
  proposition: "#366b80",
  concept: "#4c7d74",
  source: "#795a76",
};
const DECLARATION_BACKGROUNDS = {
  theorem: "#dbecee",
  opaque: "#dbecee",
  conjecture: "#f1d9d4",
  definition: "#dcebe5",
  quotient: "#dcebe5",
  inductive: "#eadfe8",
  constructor: "#eadfe8",
  recursor: "#eadfe8",
  proposition: "#dbecee",
  concept: "#dcebe5",
  source: "#eadfe8",
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
  local: "math-net",
  mathlib: "mathlib",
  "library-complete": "library baseline",
  "pedagogical-narrow": "narrow pedagogical route",
  "foundation-comparison": "foundation comparison",
  computational: "computational route",
  "computable-analysis": "computable-analysis",
};
const GITHUB_REPO = "https://github.com/liuyao12/math-net";
const COMPUTABLE_ANALYSIS_REPO = "https://github.com/liuyao12/computable-analysis";

const state = {
  graph: null,
  theorems: [],
  theoremNumber: requestedTheorem || theoremForGraph() || "1",
  focusId: null,
  selectedId: null,
  selectedProofId: null,
  search: "",
  kinds: new Set(),
  simulation: null,
  settleTimer: null,
  sourceRequest: 0,
  focusDistances: new Map(),
  showImplementation: false,
  showLandmarks: true,
  revealDepth: Infinity,
  revealLimit: Infinity,
  revealTimer: null,
  revealSteps: [],
  revealCursor: 0,
  revealedIds: new Set(),
  layoutPositions: new Map(),
  layoutVelocities: new Map(),
  expandedDistances: new Map(),
  inspectionAnchor: null,
  revealPaused: false,
  revealPauseReason: null,
  inspectionPaused: false,
  resumeReveal: null,
  revealCapped: false,
  zoomTransform: d3.zoomIdentity,
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

function sourceFileFor(node, proof = null) {
  if (proof?.locator?.startsWith("mathlib/")) {
    return `${proof.locator.slice("mathlib/".length).replaceAll(".", "/")}.lean`;
  }
  if (proof?.locator?.startsWith("computable-analysis/")) {
    return `${proof.locator.slice("computable-analysis/".length).replaceAll(".", "/")}.lean`;
  }
  const local = proof?.file || (node.formalizations || []).find((item) => item.file)?.file;
  if (local) return local;
  if (node.module?.startsWith("MathNetwork.")) return `${node.module.replaceAll(".", "/")}.lean`;
  if (node.locator?.startsWith("mathlib/")) {
    return `${node.locator.slice("mathlib/".length).replaceAll(".", "/")}.lean`;
  }
  if (node.locator?.startsWith("computable-analysis/")) {
    return `${node.locator.slice("computable-analysis/".length).replaceAll(".", "/")}.lean`;
  }
  return null;
}

function sourceUrlFor(node, proof = null) {
  const file = sourceFileFor(node, proof);
  const locator = proof?.locator || node.locator;
  if (!file) return null;
  if (locator?.startsWith("mathlib/")) {
    return `https://raw.githubusercontent.com/leanprover-community/mathlib4/master/${file}`;
  }
  if (locator?.startsWith("computable-analysis/")) {
    return `https://raw.githubusercontent.com/liuyao12/computable-analysis/main/${file}`;
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
  if (locator?.startsWith("computable-analysis/")) {
    const file = `${locator.slice("computable-analysis/".length).replaceAll(".", "/")}.lean`;
    return `${COMPUTABLE_ANALYSIS_REPO}/blob/main/${file}`;
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
  const proof = (node.proofs || []).find((item) => item.id === state.selectedProofId) || null;
  const file = sourceFileFor(node, proof);
  const formalization = proof
    ? { file: proof.file, name: proof.declaration }
    : (node.formalizations || []).find((item) => item.file);
  if (!file) {
    container.textContent = "No source locator is available for this generated declaration. The statement above is the checked declaration type.";
    container.classList.remove("pending");
    return;
  }
  const path = sourceUrlFor(node, proof);
  try {
    const response = await fetch(path);
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    const text = await response.text();
    if (request !== state.sourceRequest) return;
    const source = declarationSource(text, formalization?.name || proof?.declaration || node.namespace || node.label);
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

function declarationKindFor(node) {
  if (node?.declarationKind) return node.declarationKind;
  if (node?.kind === "proposition") return node.role || "theorem";
  return node?.kind || "definition";
}

function declarationLabelFor(kind) {
  return DECLARATION_LABELS[kind] || `${kind.slice(0, 1).toUpperCase()}${kind.slice(1)}s`;
}

function declarationColorFor(node) {
  return DECLARATION_COLORS[declarationKindFor(node)] || DECLARATION_COLORS.source;
}

function declarationBackgroundFor(node) {
  return DECLARATION_BACKGROUNDS[declarationKindFor(node)] || DECLARATION_BACKGROUNDS.source;
}

function declarationClassFor(node) {
  return declarationKindFor(node).replace(/[^a-z0-9-]/gi, "-");
}

function isImplementationNode(node) {
  return node?.presentation?.category === "implementation" ||
    (!node?.presentation && node?.kind === "source" && ["definition", "quotient", "constructor", "recursor"].includes(declarationKindFor(node)));
}

function presentationCategory(node) {
  return node?.presentation?.category || (isImplementationNode(node) ? "implementation" : "supporting");
}

function isMathematicalNode(node) {
  return presentationCategory(node) === "mathematical";
}

function isBackgroundNode(node) {
  return ["routine", "implementation"].includes(presentationCategory(node));
}

function isLandmark(node) {
  return Boolean(node?.importance?.landmark);
}

function isExpansionBoundary(node) {
  return declarationKindFor(node) === "inductive";
}

function availableDeclarationKinds() {
  return [...new Set((state.graph?.nodes || []).map(declarationKindFor))].sort((left, right) => {
    const order = ["theorem", "opaque", "conjecture", "definition", "quotient", "inductive", "constructor", "recursor"];
    return (order.indexOf(left) < 0 ? 99 : order.indexOf(left)) - (order.indexOf(right) < 0 ? 99 : order.indexOf(right)) || left.localeCompare(right);
  });
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

function proofRouteEdges(edges, focusId, proofId) {
  if (!proofId || !focusId) return edges;
  // A proof selection identifies the proof term at the focus node. Its
  // dependencies are themselves declarations with their own proof edges, so
  // retain the entire upstream closure after selecting the focus edge. The
  // old implementation kept only one proof id and silently removed the
  // theorems used by that proof's dependencies.
  const selected = edges.filter((edge) => edge.target.id === focusId && edge.proof === proofId);
  const result = [];
  const includedEdges = new Set();
  const frontier = new Set();
  selected.forEach((edge) => {
    result.push(edge);
    includedEdges.add(edge.id);
    frontier.add(edge.source.id);
  });
  while (frontier.size) {
    const next = new Set();
    edges.forEach((edge) => {
      if (!frontier.has(edge.target.id) || includedEdges.has(edge.id)) return;
      includedEdges.add(edge.id);
      result.push(edge);
      next.add(edge.source.id);
    });
    frontier.clear();
    next.forEach((id) => frontier.add(id));
  }
  return result;
}

function visibleGraph() {
  const nodesById = nodeMap();
  const allEdgeData = state.graph.edges
    .filter((edge) => edge.relation === "used-in-proof")
    .map((edge) => ({ ...edge, source: nodesById.get(edge.source.id), target: nodesById.get(edge.target.id) }))
    .filter((edge) => edge.source && edge.target);
  const edgeData = proofRouteEdges(allEdgeData, state.focusId, state.selectedProofId);
  const candidateNodes = state.graph.nodes.filter((node) => state.kinds.has(declarationKindFor(node)) &&
    (state.showImplementation || !isBackgroundNode(node) || node.id === state.focusId || node.id === state.selectedId));
  state.focusDistances = state.focusId ? focusDistances(state.focusId, edgeData, 5) : new Map();
  state.expandedDistances.forEach((distance, id) => {
    if (!state.focusDistances.has(id) || distance < state.focusDistances.get(id)) state.focusDistances.set(id, distance);
  });
  const focus = searchFocus(candidateNodes, edgeData);
  const visibleNodes = candidateNodes.filter((node) => {
    if (state.focusId && !state.focusDistances.has(node.id)) return false;
    if (state.focusId && state.revealDepth !== Infinity && !state.revealedIds.has(node.id)) return false;
    if (state.search && !focus.has(node.id)) return false;
    return true;
  }).filter((node, index) => !state.focusId && state.revealLimit !== Infinity ? index < state.revealLimit : true);
  const allowed = new Set(visibleNodes.map((node) => node.id));
  const visibleEdges = edgeData.filter((edge) => allowed.has(edge.source.id) && allowed.has(edge.target.id));
  // Contract suppressed routine/implementation nodes. The visual graph stays
  // connected without pretending that the omitted declarations vanished from
  // Lean's actual proof term.
  if (!state.showImplementation) {
    const incoming = new Map();
    edgeData.forEach((edge) => {
      if (!incoming.has(edge.target.id)) incoming.set(edge.target.id, []);
      incoming.get(edge.target.id).push(edge);
    });
    const shortcuts = [];
    visibleNodes.forEach((target) => {
      const queue = (incoming.get(target.id) || []).map((edge) => ({ edge, hidden: [] }));
      const visited = new Set();
      while (queue.length) {
        const { edge, hidden } = queue.shift();
        const source = edge.source;
        if (allowed.has(source.id)) {
          if (hidden.length) shortcuts.push({
            ...edge,
            id: `contracted-${source.id}-${target.id}-${edge.proof || "none"}`,
            source,
            target,
            description: `used in proof through ${hidden.length} suppressed routine declaration${hidden.length === 1 ? "" : "s"}`,
            contracted: true,
          });
          continue;
        }
        if (!isBackgroundNode(source) || visited.has(source.id)) continue;
        visited.add(source.id);
        (incoming.get(source.id) || []).forEach((upstream) => queue.push({ edge: upstream, hidden: [...hidden, source.id] }));
      }
    });
    const known = new Set(visibleEdges.map((edge) => `${edge.source.id}:${edge.target.id}:${edge.proof || ""}`));
    shortcuts.forEach((edge) => {
      const identity = `${edge.source.id}:${edge.target.id}:${edge.proof || ""}`;
      if (!known.has(identity)) {
        known.add(identity);
        visibleEdges.push(edge);
      }
    });
  }
  const connected = new Set();
  visibleEdges.forEach((edge) => { connected.add(edge.source.id); connected.add(edge.target.id); });
  const connectedNodes = visibleNodes.filter((node) => node.id === state.focusId || connected.has(node.id));
  const connectedIds = new Set(connectedNodes.map((node) => node.id));
  return { nodes: connectedNodes, edges: visibleEdges.filter((edge) => connectedIds.has(edge.source.id) && connectedIds.has(edge.target.id)) };
}

function kindControls() {
  const container = $("#kind-filters");
  container.replaceChildren();
  availableDeclarationKinds().forEach((key) => {
    const label = declarationLabelFor(key);
    const wrapper = document.createElement("label");
    wrapper.className = "filter-option";
    wrapper.innerHTML = `<input type="checkbox" data-kind="${escapeHtml(key)}" checked><span class="filter-dot" style="background:${declarationColorFor({ declarationKind: key })}"></span><span>${escapeHtml(label)}</span>`;
    wrapper.querySelector("input").addEventListener("change", (event) => {
      event.target.checked ? state.kinds.add(key) : state.kinds.delete(key);
      draw();
    });
    container.append(wrapper);
  });
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
  state.theoremNumber = state.theoremNumber || "1";
  if (state.theoremNumber) select.value = String(state.theoremNumber);
  updateTheoremNote();
  select.addEventListener("change", (event) => {
    const number = event.target.value;
    if (!number) {
      const next = new URL(window.location.href);
      next.searchParams.delete("theorem");
      history.replaceState(null, "", next);
      state.theoremNumber = null;
      state.focusId = null;
      state.selectedId = null;
      state.layoutPositions.clear();
      state.layoutVelocities.clear();
      state.expandedDistances.clear();
      state.inspectionAnchor = null;
      state.revealedIds.clear();
      updateTheoremNote();
      updateWorkspaceContext();
      draw();
      return;
    }
    const theorem = state.theorems.find((item) => String(item.number) === number);
    const next = new URL(window.location.href);
    next.searchParams.set("theorem", number);
    next.searchParams.delete("graph");
    history.pushState(null, "", next);
    state.theoremNumber = number;
    state.focusId = null;
    state.selectedId = null;
    state.selectedProofId = null;
    state.layoutPositions.clear();
    state.layoutVelocities.clear();
    state.expandedDistances.clear();
    state.inspectionAnchor = null;
    state.revealedIds.clear();
    if (state.revealTimer) window.clearTimeout(state.revealTimer);
    state.revealTimer = null;
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
  if (node) {
    state.focusId = node.id;
    state.revealDepth = 0;
    state.revealLimit = Infinity;
    selectNode(node.id, true);
  } else {
    state.revealDepth = Infinity;
    state.revealLimit = 220;
    renderInspector();
    updateWorkspaceContext();
    draw();
  }
  beginProgressiveReveal();
}

function beginProgressiveReveal() {
  if (state.revealTimer) window.clearTimeout(state.revealTimer);
  state.revealTimer = null;
  state.revealPaused = false;
  state.revealPauseReason = null;
  state.inspectionPaused = false;
  state.resumeReveal = null;
  if (!state.graph) return;
  const focused = Boolean(state.focusId);
  if (focused) {
    state.revealDepth = 0;
    state.revealLimit = Infinity;
    state.revealedIds = new Set([state.focusId]);
    const nodeIds = new Set(state.graph.nodes.map((node) => node.id));
    const adjacency = new Map();
    proofRouteEdges(
      state.graph.edges.filter((edge) => edge.relation === "used-in-proof"),
      state.focusId,
      state.selectedProofId,
    ).forEach((edge) => {
        if (!adjacency.has(edge.target.id)) adjacency.set(edge.target.id, []);
        adjacency.get(edge.target.id).push(edge.source.id);
      });
    const steps = [];
    const seen = new Set([state.focusId]);
    const maxFocusNodes = 80;
    const queue = [{ id: state.focusId, depth: 0 }];
    state.revealCapped = false;
    while (queue.length) {
      const parent = queue.shift();
      const parentNode = nodeIds.has(parent.id) ? nodeMap().get(parent.id) : null;
      if (isExpansionBoundary(parentNode)) continue;
      const children = [];
      const existing = [];
      (adjacency.get(parent.id) || []).slice().sort().forEach((neighbor) => {
        if (!nodeIds.has(neighbor)) return;
        if (seen.has(neighbor)) {
          existing.push(neighbor);
          return;
        }
        if (seen.size >= maxFocusNodes) {
          state.revealCapped = true;
          return;
        }
        seen.add(neighbor);
        children.push(neighbor);
      });
      if (children.length || existing.length) {
        steps.push({ parentId: parent.id, nodeIds: children, existingIds: existing });
        children.forEach((id) => queue.push({ id, depth: parent.depth + 1 }));
      }
    }
    state.revealSteps = steps;
    state.revealCursor = 0;
  } else {
    state.revealDepth = Infinity;
    state.revealLimit = state.graph.nodes.length > 250 ? 220 : Infinity;
    state.revealSteps = [];
    state.revealCapped = false;
    state.revealCursor = 0;
  }
  draw();
  const advance = () => {
    if (focused) {
      if (viewportHasEdgeNode()) {
        state.revealPaused = true;
        state.revealPauseReason = "viewport";
        state.revealTimer = null;
        updateHighlight();
        return;
      }
      if (state.revealCursor >= state.revealSteps.length) {
        state.revealTimer = null;
        return;
      }
      state.revealSteps[state.revealCursor].nodeIds.forEach((id) => state.revealedIds.add(id));
      state.revealCursor += 1;
    } else {
      if (state.revealLimit >= state.graph.nodes.length) { state.revealTimer = null; return; }
      state.revealLimit = Math.min(state.graph.nodes.length, state.revealLimit + 220);
    }
    draw();
    state.revealTimer = window.setTimeout(advance, focused ? 260 : 280);
  };
  state.resumeReveal = () => {
    if (state.inspectionPaused) {
      state.inspectionPaused = false;
      state.simulation?.alpha(0.22).restart();
    }
    if (!state.revealPaused || state.revealCursor >= state.revealSteps.length) {
      state.revealPaused = false;
      state.revealPauseReason = null;
      updateHighlight();
      return;
    }
    state.revealPaused = false;
    state.revealPauseReason = null;
    state.revealTimer = window.setTimeout(advance, 80);
    updateHighlight();
  };
  state.revealTimer = window.setTimeout(advance, 260);
}

function viewportHasEdgeNode() {
  if (!state.graph || !state.focusId) return false;
  const height = stage.clientHeight;
  return state.graph.nodes
    .filter((node) => state.revealedIds.has(node.id))
    .some((node) => {
      if (!Number.isFinite(node.y)) return false;
      const screenY = state.zoomTransform.applyY(node.y);
      return screenY < 28 || screenY > height - 28;
    });
}

function resumeRevealIfVisible() {
  if (state.revealPaused && !viewportHasEdgeNode()) state.resumeReveal?.();
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
  return isMathematicalNode(node);
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

function renderProofLegend() {
  const container = $("#proof-legend");
  if (!container || !state.graph) return;
  const labels = proofLabels();
  const proofMeta = new Map();
  state.graph.nodes.forEach((node) => (node.proofs || []).forEach((proof) => proofMeta.set(proof.id, proof)));
  const usedProofs = new Set(state.graph.edges.map((edge) => edge.proof).filter(Boolean));
  const grouped = new Map();
  [...usedProofs].forEach((proofId) => {
    const proof = proofMeta.get(proofId);
    const key = proof?.routeKind || proofId;
    if (!grouped.has(key)) grouped.set(key, { id: proofId, label: ROUTE_KIND_LABELS[key] || labels.get(proofId) || key });
  });
  const entries = [...grouped.values()]
    .sort((left, right) => left.label.localeCompare(right.label));
  container.innerHTML = entries.length
    ? `<span class="legend-heading">Arrow colors · proof routes</span>${entries.map((entry) => `<span class="legend-item"><span class="legend-line" style="background:${escapeHtml(proofColor(entry.id))}"></span><span>${escapeHtml(entry.label)}</span></span>`).join("")}`
    : "";
}

function nodeNeighbors(nodeId) {
  const map = nodeMap();
  return state.graph.edges.flatMap((edge) => {
    if (edge.source.id === nodeId) return [{ relation: edge.relation, node: map.get(edge.target.id), direction: "out" }];
    if (edge.target.id === nodeId) return [{ relation: edge.relation, node: map.get(edge.source.id), direction: "in" }];
    return [];
  }).filter((item) => item.node);
}

function selectNode(nodeId, redraw = false) {
  const hadFocus = Boolean(state.focusId);
  if (hadFocus) {
    state.simulation?.stop();
    state.inspectionPaused = true;
    state.revealPaused = true;
    state.revealPauseReason = "inspection";
    if (state.revealTimer) {
      window.clearTimeout(state.revealTimer);
      state.revealTimer = null;
    }
  }
  if (!hadFocus) state.focusId = nodeId;
  state.selectedId = nodeId;
  state.selectedProofId = null;
  const expanded = expandNodeDependencies(nodeId, false);
  renderInspector();
  updateWorkspaceContext();
  if (redraw || !hadFocus || expanded) draw();
  else updateHighlight();
}

function selectProof(proofId) {
  state.selectedProofId = proofId;
  renderInspector();
  draw();
}

function expandNodeDependencies(nodeId, redraw = true) {
  const node = nodeMap().get(nodeId);
  if (!node || isExpansionBoundary(node)) return;
  if (Number.isFinite(node.x) && Number.isFinite(node.y)) {
    state.inspectionAnchor = { id: nodeId, x: node.x, y: node.y };
  }
  const dependencies = state.graph.edges
    .filter((edge) => edge.relation === "used-in-proof" && edge.target.id === nodeId)
    .map((edge) => edge.source.id);
  const parentDistance = state.focusDistances.get(nodeId) ?? 0;
  dependencies.forEach((id) => {
    state.revealedIds.add(id);
    const distance = parentDistance + 1;
    if (!state.expandedDistances.has(id) || distance < state.expandedDistances.get(id)) state.expandedDistances.set(id, distance);
  });
  if (!dependencies.length) return false;
  state.revealPaused = true;
  state.revealPauseReason = "inspection";
  if (state.revealTimer) {
    window.clearTimeout(state.revealTimer);
    state.revealTimer = null;
  }
  if (redraw) draw();
  return true;
}

function scheduleSimulationStop(delay = 900) {
  if (state.settleTimer) window.clearTimeout(state.settleTimer);
  if (!state.simulation) return;
  state.settleTimer = window.setTimeout(() => {
    state.simulation?.stop();
    state.settleTimer = null;
  }, delay);
}

function hasHiddenDependencies(nodeId, visibleNodes) {
  if (isExpansionBoundary(nodeMap().get(nodeId))) return false;
  const visibleIds = new Set(visibleNodes.map((node) => node.id));
  return state.graph.edges.some((edge) => edge.relation === "used-in-proof" && edge.target.id === nodeId &&
    !visibleIds.has(edge.source.id) && state.kinds.has(declarationKindFor(nodeMap().get(edge.source.id))));
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
  const comparison = node.comparison;
  const comparisonNote = comparison
    ? `<div class="detail-block comparison-block"><div class="detail-label">Checked comparison</div><p>${escapeHtml(comparison.identity)}. The routes below are proof terms for this one proposition; their dependency edges can therefore meet at this node.</p>${comparison.registry ? `<div class="comparison-registry">Registry: <code>${escapeHtml(comparison.registry)}</code></div>` : ""}</div>`
    : "";
  const depthNote = Number.isInteger(node.dependencyDepth)
    ? `<div class="detail-block"><div class="detail-label">Dependency layer</div><p>Imported declaration · layer ${node.dependencyDepth}.${node.dependencyBoundary ? " Expansion stops here at a Lean structure boundary; click the node’s marker to inspect any indexed dependencies." : ""}</p></div>`
    : "";
  const importance = node.importance
    ? `<div class="detail-block"><div class="detail-label">Structural importance</div><p><strong>${escapeHtml(node.importance.score)}</strong>/100 · ${escapeHtml(node.importance.directUses)} direct proof uses · ${escapeHtml(node.importance.downstreamNodes)} downstream declarations.</p><p class="muted-note">Heuristic based on reuse and downstream reach, not proof length. ${escapeHtml(node.importance.landmark ? "Marked as a structural landmark." : "Not currently marked as a landmark.")}</p></div>`
    : "";
  const presentation = node.presentation
    ? `<div class="detail-block"><div class="detail-label">Graph role</div><p><strong>${escapeHtml(node.presentation.category)}</strong> · ${escapeHtml(node.presentation.reason)}</p><p class="muted-note">Presentation heuristic, not a logical distinction in Lean.</p></div>`
    : "";
  const proofs = (node.proofs || []).map((proof) => `<div class="proof-row ${state.selectedProofId === proof.id ? "selected" : ""}"><button class="proof-select" data-proof="${escapeHtml(proof.id)}"><span class="proof-color" style="background:${escapeHtml(proof.color || proofColor(proof.id))}"></span>${escapeHtml(proof.label)}${proof.routeKind ? `<small>${escapeHtml(ROUTE_KIND_LABELS[proof.routeKind] || proof.routeKind)}</small>` : ""}</button><span class="proof-status">${escapeHtml(proof.status || "planned")}</span></div>`).join("");
  const incoming = neighbors.filter(({ direction }) => direction === "in");
  const outgoing = neighbors.filter(({ direction }) => direction === "out");
  const neighborRows = [
    incoming.length ? `<div class="detail-label">Proof dependencies</div>${incoming.map(({ node: neighbor }) => `<div class="relation-row"><span class="relation-name">used in proof</span><button class="neighbor" data-neighbor="${escapeHtml(neighbor.id)}">${escapeHtml(neighbor.label)}</button></div>`).join("")}` : "",
    outgoing.length ? `<div class="detail-label">Used in these proofs</div>${outgoing.map(({ node: neighbor }) => `<div class="relation-row"><span class="relation-name">proof target</span><button class="neighbor" data-neighbor="${escapeHtml(neighbor.id)}">${escapeHtml(neighbor.label)}</button></div>`).join("")}` : "",
  ].join("");
  content.innerHTML = `
    <span class="node-kind ${escapeHtml(declarationClassFor(node))}" style="color:${escapeHtml(declarationColorFor(node))};background:${escapeHtml(declarationBackgroundFor(node))}">${escapeHtml(declarationKindFor(node))}</span>
    <div class="verification-badge ${verificationFor(node).className}"><span>${verificationFor(node).glyph}</span>${verificationText(node)}</div>
    <h2>${escapeHtml(node.label)}</h2>
    ${mergeNote}
    ${comparisonNote}
    ${depthNote}
    ${presentation}
    ${importance}
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

function updateWorkspaceContext() {
  const context = $("#workspace-context");
  const back = $("#back-to-theorem");
  if (!context || !back) return;
  const map = nodeMap();
  const focus = state.focusId ? map.get(state.focusId) : null;
  const selected = state.selectedId ? map.get(state.selectedId) : null;
  context.textContent = focus ? `Theorem · ${focus.label}` : "Choose a theorem to begin";
  const title = $("#network-title");
  if (title) title.textContent = focus ? `${focus.label} · dependency neighborhood` : "Mathematical landscape";
  back.hidden = !focus || !selected || selected.id === focus.id;
  back.setAttribute("aria-label", focus ? `Return to theorem ${focus.label}` : "Return to theorem");
}

function updateHighlight() {
  // visibleGraph has already computed the bounded, upstream dependency
  // neighborhood. Reuse it here so the theorem focus remains stable while a
  // neighboring node is inspected.
  const neighborhood = state.focusId ? new Set(state.focusDistances.keys()) : new Set();
  svg.selectAll(".node-dot").classed("selected", (node) => node.id === state.selectedId).classed("dimmed", (node) => state.focusId && !neighborhood.has(node.id));
  svg.selectAll(".node-label").classed("dimmed", (node) => state.focusId && !neighborhood.has(node.id));
  svg.selectAll(".graph-link")
    .classed("dimmed", (edge) => state.focusId && (!neighborhood.has(edge.source.id) || !neighborhood.has(edge.target.id)))
    .classed("selected-edge", (edge) => Boolean(state.selectedId) && (edge.source.id === state.selectedId || edge.target.id === state.selectedId));
  const visibleNodes = visibleGraph().nodes;
  svg.selectAll(".node-expand").classed("hidden", (node) => node.id !== state.selectedId || !hasHiddenDependencies(node.id, visibleNodes));
  const focusStatus = $("#focus-status");
  if (focusStatus) {
    const focus = state.focusId ? nodeMap().get(state.focusId) : null;
    const visibleCount = state.focusId && state.revealDepth !== Infinity
      ? state.revealedIds.size
      : neighborhood.size;
    const nextStep = state.revealSteps[state.revealCursor];
    const parent = nextStep ? nodeMap().get(nextStep.parentId) : null;
    const revealText = state.revealPaused
      ? state.revealPauseReason === "inspection"
        ? "paused while inspecting · click to continue"
        : "paused at viewport edge · click to continue"
      : nextStep
        ? `expanding ${parent?.label || "node"} · ${state.revealCursor + 1}/${state.revealSteps.length}`
        : state.revealCapped
          ? "focused neighborhood capped at 80 nodes"
        : "BFS loaded";
    focusStatus.textContent = focus
      ? `${visibleCount}/${neighborhood.size} nodes · ${revealText} · ${focus.label}`
      : state.revealLimit !== Infinity
        ? `${Math.min(state.revealLimit, state.graph.nodes.length)}/${state.graph.nodes.length} nodes loading · select a theorem to focus`
        : "all theorem nodes shown · select a theorem to focus";
  }
}

function dependencyRanks(nodes, edges) {
  const ranks = new Map(nodes.map((item) => [item.id, 0]));
  // Edges point from a used declaration to the declaration whose proof uses
  // it. Kahn's algorithm gives a finite longest-path layering and, unlike
  // repeated relaxation, cannot inflate ranks forever when imported
  // typeclass declarations contain a small cycle.
  const outgoing = new Map(nodes.map((item) => [item.id, []]));
  const indegree = new Map(nodes.map((item) => [item.id, 0]));
  edges.forEach((edge) => {
    outgoing.get(edge.source.id)?.push(edge);
    indegree.set(edge.target.id, (indegree.get(edge.target.id) || 0) + 1);
  });
  const queue = nodes.filter((item) => indegree.get(item.id) === 0).map((item) => item.id);
  const processed = new Set();
  while (queue.length) {
    const sourceId = queue.shift();
    processed.add(sourceId);
    (outgoing.get(sourceId) || []).forEach((edge) => {
      const targetId = edge.target.id;
      ranks.set(targetId, Math.max(ranks.get(targetId) || 0, (ranks.get(sourceId) || 0) + 1));
      const nextDegree = (indegree.get(targetId) || 0) - 1;
      indegree.set(targetId, nextDegree);
      if (nextDegree === 0) queue.push(targetId);
    });
  }
  // Keep cyclic implementation clusters compact. Their internal edges are
  // rendered without arrowheads below, while acyclic edges still flow from
  // an upper rank to a lower one.
  const remaining = nodes.filter((item) => !processed.has(item.id));
  if (remaining.length) {
    const remainingIds = new Set(remaining.map((item) => item.id));
    const base = Math.max(0, ...edges
      .filter((edge) => remainingIds.has(edge.target.id) && !remainingIds.has(edge.source.id))
      .map((edge) => (ranks.get(edge.source.id) || 0) + 1));
    remaining.forEach((item) => ranks.set(item.id, Math.max(ranks.get(item.id) || 0, base)));
  }
  return ranks;
}

function proofRouteSides(nodes, edges, focusId) {
  const sides = new Map();
  const focus = nodes.find((node) => node.id === focusId);
  if (!focus || !(focus.proofs || []).length) return sides;
  if (state.selectedProofId) {
    // Once one proof is selected, its upstream closure is the subject of the
    // view. Keep that route on the central spine; repository lanes are useful
    // only while comparing multiple routes at the merged proposition.
    const incoming = new Map();
    edges.forEach((edge) => {
      if (!incoming.has(edge.target.id)) incoming.set(edge.target.id, []);
      incoming.get(edge.target.id).push(edge);
    });
    const queue = [focusId];
    sides.set(focusId, 0);
    while (queue.length) {
      const targetId = queue.shift();
      (incoming.get(targetId) || []).forEach((edge) => {
        if (sides.has(edge.source.id)) return;
        sides.set(edge.source.id, 0);
        queue.push(edge.source.id);
      });
    }
    return sides;
  }
  const groupForProof = new Map();
  const groups = [];
  (focus.proofs || []).forEach((proof) => {
    const key = proof.routeKind === "local" ? "local" : proof.routeKind || proof.id;
    if (!groups.includes(key)) groups.push(key);
    groupForProof.set(proof.id, key);
  });
  const groupSide = new Map(groups.map((group, index) => [group, groups.length < 2 ? 0 : index === 0 ? -1 : index === groups.length - 1 ? 1 : 0]));
  const incoming = new Map();
  edges.forEach((edge) => {
    if (!incoming.has(edge.target.id)) incoming.set(edge.target.id, []);
    incoming.get(edge.target.id).push(edge);
  });
  const queue = [focusId];
  sides.set(focusId, 0);
  while (queue.length) {
    const targetId = queue.shift();
    (incoming.get(targetId) || []).forEach((edge) => {
      const edgeSide = targetId === focusId ? groupSide.get(groupForProof.get(edge.proof)) ?? 0 : sides.get(targetId) ?? 0;
      if (!sides.has(edge.source.id)) {
        sides.set(edge.source.id, edgeSide);
        queue.push(edge.source.id);
      } else if (sides.get(edge.source.id) !== edgeSide) {
        sides.set(edge.source.id, 0);
      }
    });
  }
  return sides;
}

function theoremLike(node) {
  return node?.kind === "proposition" || ["theorem", "opaque", "axiom", "proposition"].includes(declarationKindFor(node));
}

function coreNodeFor(nodes) {
  if (!state.selectedProofId || !state.focusId) return null;
  const focus = nodes.find((node) => node.id === state.focusId);
  if (!focus) return null;
  const focusWords = new Set((`${focus.namespace || ""} ${focus.label || ""}`.toLowerCase().match(/[a-z][a-z0-9]+/g) || []).filter((word) => word.length > 3));
  const candidates = nodes.filter((node) => {
    const distance = state.focusDistances.get(node.id);
    return node.id !== state.focusId && theoremLike(node) && distance >= 2 && distance <= 3;
  });
  return candidates.sort((left, right) => {
    const rank = (node) => {
      const words = `${node.namespace || ""} ${node.label || ""}`.toLowerCase().match(/[a-z][a-z0-9]+/g) || [];
      const overlap = words.filter((word) => focusWords.has(word)).length;
      return (state.focusDistances.get(node.id) || 0) * 100 + overlap * 20 + (node.importance?.score || 0);
    };
    return rank(right) - rank(left);
  })[0]?.id || null;
}

function straightLinkPath(edge) {
  const x1 = edge.source.x;
  const y1 = edge.source.y;
  const x2 = edge.target.x;
  const y2 = edge.target.y;
  return `M${x1},${y1} L${x2},${y2}`;
}

function curvedLinkPath(edge) {
  const x1 = edge.source.x;
  const y1 = edge.source.y;
  const x2 = edge.target.x;
  const y2 = edge.target.y;
  const dy = y2 - y1;
  if (Math.abs(dy) < 10) {
    return `M${x1},${y1} L${x2},${y2}`;
  }
  return `M${x1},${y1} C${x1},${y1 + dy * 0.42} ${x2},${y2 - dy * 0.42} ${x2},${y2}`;
}

function routedLinkPath(edge, nodes = []) {
  const x1 = edge.source.x;
  const y1 = edge.source.y;
  const x2 = edge.target.x;
  const y2 = edge.target.y;
  const dy = y2 - y1;
  if (Math.abs(dy) < 10) return `M${x1},${y1} L${x2},${y2}`;
  const obstacles = nodes
    .filter((node) => node.id !== edge.source.id && node.id !== edge.target.id)
    .filter((node) => Number.isFinite(node.x) && Number.isFinite(node.y))
    .map((node) => ({
      node,
      halfWidth: Math.max(14, labelFor(node).length * 3.2 + 10),
      halfHeight: 13,
    }))
    .filter(({ node }) => node.y > Math.min(y1, y2) + 12 && node.y < Math.max(y1, y2) - 12)
    .sort((left, right) => Math.abs(left.node.y - (y1 + dy * 0.5)) - Math.abs(right.node.y - (y1 + dy * 0.5)));
  const obstacle = obstacles.find(({ node, halfWidth, halfHeight }) => {
    const t = (node.y - y1) / dy;
    const pathX = x1 + (x2 - x1) * t;
    return Math.abs(pathX - node.x) < halfWidth + 7 && Math.abs(node.y - (y1 + dy * t)) < halfHeight + 7;
  });
  if (!obstacle) return curvedLinkPath(edge);
  const { node, halfWidth, halfHeight } = obstacle;
  const t = (node.y - y1) / dy;
  const pathX = x1 + (x2 - x1) * t;
  const detourX = pathX <= node.x ? node.x - halfWidth - 12 : node.x + halfWidth + 12;
  const beforeY = node.y - halfHeight - 7;
  const afterY = node.y + halfHeight + 7;
  return `M${x1},${y1} C${x1},${y1 + dy * 0.28} ${detourX},${beforeY - 18} ${detourX},${beforeY} C${detourX},${afterY} ${x2},${y2 - dy * 0.28} ${x2},${y2}`;
}

function topDownForce(edges, ranks, gap = 26) {
  const force = () => {
    edges.forEach((edge) => {
      if (edge.source === edge.target) return;
      if ((ranks.get(edge.source.id) || 0) >= (ranks.get(edge.target.id) || 0)) return;
      const overlap = edge.source.y + gap - edge.target.y;
      if (overlap > 0) {
        const shift = overlap * 0.45;
        edge.source.y -= shift;
        edge.target.y += shift;
      }
    });
  };
  return force;
}

function enforceTopDown(nodes, edges, ranks, focusId, gap = 26) {
  const ordered = nodes.slice().sort((a, b) => (ranks.get(a.id) || 0) - (ranks.get(b.id) || 0));
  for (let pass = 0; pass < ordered.length; pass += 1) {
    edges.forEach((edge) => {
      if (edge.source === edge.target) return;
      if ((ranks.get(edge.source.id) || 0) >= (ranks.get(edge.target.id) || 0)) return;
      const overlap = edge.source.y + gap - edge.target.y;
      if (overlap <= 0) return;
      if (edge.target.id === focusId) {
        edge.source.y -= overlap;
      } else if (edge.source.id === focusId) {
        edge.target.y += overlap;
      } else {
        edge.source.y -= overlap * 0.5;
        edge.target.y += overlap * 0.5;
      }
    });
  }
}

function labelCollisionForce(nodes) {
  const active = nodes.filter((node) => isMajorNode(node) && (nodes.length <= 12 || node.label.length <= 31));
  const widthOf = (node) => Math.max(30, labelFor(node).length * 6.2 + 20);
  const boxOf = (node) => {
    const width = widthOf(node);
    return { left: node.x + 10, right: node.x + 10 + width, top: node.y - 10, bottom: node.y + 10, width };
  };
  const force = () => {
    for (let pass = 0; pass < 3; pass += 1) {
      active.forEach((left, i) => {
        const leftBox = boxOf(left);
        active.slice(i + 1).forEach((right) => {
          const rightBox = boxOf(right);
          if (leftBox.right < rightBox.left || rightBox.right < leftBox.left || leftBox.bottom < rightBox.top || rightBox.bottom < leftBox.top) return;
          const horizontal = Math.min(leftBox.right, rightBox.right) - Math.max(leftBox.left, rightBox.left) + 4;
          const vertical = Math.min(leftBox.bottom, rightBox.bottom) - Math.max(leftBox.top, rightBox.top) + 4;
          if (horizontal < vertical) {
            const direction = left.x <= right.x ? -1 : 1;
            left.x += direction * horizontal * 0.55;
            right.x -= direction * horizontal * 0.55;
          } else {
            const direction = left.y <= right.y ? -1 : 1;
            left.y += direction * vertical * 0.55;
            right.y -= direction * vertical * 0.55;
          }
        });
        nodes.forEach((right) => {
          if (right === left) return;
          const box = boxOf(left);
          const radius = right.kind === "proof-family" ? 10 : isMajorNode(right) ? 8 : 5;
          const inside = right.x + radius > box.left && right.x - radius < box.right && right.y + radius > box.top && right.y - radius < box.bottom;
          if (inside) {
            const direction = right.y >= left.y ? -1 : 1;
            left.y += direction * (Math.min(box.bottom, right.y + radius) - Math.max(box.top, right.y - radius) + 6) * 0.55;
          }
        });
      });
    }
  };
  return force;
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
  defs.append("marker").attr("id", "arrow-used-in-proof").attr("viewBox", "0 -3 6 6").attr("refX", 14).attr("refY", 0).attr("markerWidth", 3.5).attr("markerHeight", 3.5).attr("orient", "auto").append("path").attr("d", "M0,-3L6,0L0,3").attr("fill", "context-stroke");
  const root = svg.append("g");
  const zoom = d3.zoom().scaleExtent([0.35, 3]).on("zoom", (event) => {
    state.zoomTransform = event.transform;
    root.attr("transform", event.transform);
    resumeRevealIfVisible();
  });
  svg.call(zoom).property("__zoom", state.zoomTransform);
  root.attr("transform", state.zoomTransform);
  const labels = proofLabels();
  // Keep the dependency direction visible in the layout.  Edges point from
  // a used declaration to the declaration whose proof uses it, so repeated
  // relaxation places prerequisites above their proof targets.  Distance
  // from the focus is still used for fading, but no longer flattens peers
  // into one horizontal band.
  const topologyRanks = dependencyRanks(nodes, edges);
  const routeSides = proofRouteSides(nodes, edges, state.focusId);
  const coreId = coreNodeFor(nodes);
  const maxFocusDistance = Math.max(0, ...nodes.map((node) => state.focusDistances.get(node.id) || 0));
  const rawRanks = new Map(nodes.map((item) => {
    // Distance supplies the main top-to-bottom dependency hierarchy. The
    // topological rank breaks ties, so a declaration used by a peer rises
    // above that peer instead of sharing the focuser's direct-dependency row.
    const distance = state.focusId ? (state.focusDistances.get(item.id) || 0) : 0;
    const distanceRank = state.focusId ? (maxFocusDistance - distance) * (nodes.length + 1) : 0;
    return [item.id, distanceRank + (topologyRanks.get(item.id) || 0)];
  }));
  const rankValues = [...new Set(rawRanks.values())].sort((a, b) => a - b);
  const rankIndex = new Map(rankValues.map((value, index) => [value, index]));
  const ranks = new Map([...rawRanks.entries()].map(([id, value]) => [id, rankIndex.get(value)]));
  const maxRank = Math.max(0, ...Array.from(ranks.values()));
  // Treat the viewport as a window onto the layout, not as a height to fill.
  // This keeps a focused theorem compact when its dependency depth is small.
  const layerGap = Math.max(22, Math.min(64, (height - 90) / Math.max(1, maxRank)));
  const occupiedHeight = maxRank * layerGap + 40;
  const graphTop = Math.max(32, (height - occupiedHeight) / 2);
  const nodesByRank = d3.group(nodes, (item) => ranks.get(item.id) || 0);
  const maxLayerSize = Math.max(1, ...Array.from(nodesByRank.values()).map((layer) => layer.length));
  const columnGap = Math.min(112, Math.max(72, (width - 80) / Math.max(1, maxLayerSize)));
  const lanePositions = new Map();
  nodesByRank.forEach((layer) => d3.group(layer, (item) => routeSides.get(item.id) || 0).forEach((lane, side) => {
    lane.forEach((item, index) => lanePositions.set(item.id, { side: Number(side), index, size: lane.length }));
  }));
  const laneOffset = Math.min(150, Math.max(78, width * 0.16));
  nodesByRank.forEach((layer, rank) => layer.forEach((item) => {
    const lane = lanePositions.get(item.id) || { side: 0, index: 0, size: 1 };
    const targetX = item.id === state.focusId
      ? width / 2
      : width / 2 + lane.side * laneOffset + (lane.index - (lane.size - 1) / 2) * columnGap * 0.72;
    const targetY = item.id === coreId
      ? height * 0.5
      : item.id === state.focusId
      ? height * 0.74
      : graphTop + rank * layerGap;
    const previous = state.layoutPositions.get(item.id);
    if (previous) {
      item.x = previous.x;
      item.y = previous.y;
      const velocity = state.layoutVelocities.get(item.id);
      item.vx = velocity?.x ?? 0;
      item.vy = velocity?.y ?? 0;
      if (item.id === state.focusId && (item.y < 40 || item.y > height - 40)) {
        item.x = width / 2;
        item.y = height * 0.74;
        item.vx = 0;
        item.vy = 0;
      }
    } else {
      const neighbor = edges.find((edge) => edge.source.id === item.id && state.layoutPositions.has(edge.target.id)) ||
        edges.find((edge) => edge.target.id === item.id && state.layoutPositions.has(edge.source.id));
      const neighborPosition = neighbor && state.layoutPositions.get(
        neighbor.source.id === item.id ? neighbor.target.id : neighbor.source.id,
      );
      item.x = neighborPosition?.x ?? targetX;
      item.y = neighborPosition?.y ?? targetY;
      item.vx = 0;
      item.vy = 0;
    }
    if (state.inspectionAnchor?.id === item.id) {
      item.x = state.inspectionAnchor.x;
      item.y = state.inspectionAnchor.y;
      item.fx = state.inspectionAnchor.x;
      item.fy = state.inspectionAnchor.y;
      item.vx = 0;
      item.vy = 0;
    }
    item.targetX = targetX;
    item.targetY = targetY;
  }));
  const link = root.append("g").attr("aria-hidden", "true").selectAll("path").data(edges, (edge) => edge.id).join("path")
    .attr("class", "graph-link used-in-proof")
    .classed("implementation-link", (edge) => !isMajorNode(edge.source) && !isMajorNode(edge.target))
    .classed("cycle-link", (edge) => (ranks.get(edge.source.id) || 0) >= (ranks.get(edge.target.id) || 0))
    .attr("stroke", (edge) => proofColor(edge.proof))
    // Arrowheads are reserved for edges touching a major declaration.  The
    // complete edge remains visible, while implementation-level chains do
    // not turn into a field of tiny overlapping triangles.
    .attr("marker-end", (edge) => edge.source.y + 5 < edge.target.y && (isMajorNode(edge.source) || isMajorNode(edge.target)) ? "url(#arrow-used-in-proof)" : null);
  link.append("title").text((edge) => `proof: ${labels.get(edge.proof) || edge.proof || "unknown"}\n${edge.description || "used in proof"}`);
  const node = root.append("g").selectAll("g").data(nodes, (item) => item.id).join("g").attr("role", "button").attr("aria-label", (item) => item.label).classed("graph-node", true).classed("major-node", (item) => isMajorNode(item)).classed("implementation-node", (item) => presentationCategory(item) === "implementation").classed("landmark-node", (item) => state.showLandmarks && isLandmark(item)).on("click", (event, item) => { event.stopPropagation(); selectNode(item.id); }).call(d3.drag().on("start", (event, item) => { state.simulation?.stop(); item.fx = item.x; item.fy = item.y; }).on("drag", (event, item) => { item.x = event.x; item.y = event.y; item.fx = event.x; item.fy = event.y; node.attr("transform", (candidate) => `translate(${candidate.x},${candidate.y})`); link.attr("d", (edge) => routedLinkPath(edge, nodes)); }).on("end", (event, item) => { item.fx = null; item.fy = null; state.layoutPositions.set(item.id, { x: item.x, y: item.y }); if (state.selectedId === item.id) state.inspectionAnchor = { id: item.id, x: item.x, y: item.y }; resumeRevealIfVisible(); }));
  node.append("circle").attr("class", "node-dot").classed("implementation", (item) => presentationCategory(item) === "implementation").classed("supporting", (item) => presentationCategory(item) === "supporting").classed("landmark", (item) => state.showLandmarks && isLandmark(item)).attr("data-focus-distance", (item) => state.focusDistances.get(item.id) ?? "").attr("r", (item) => item.kind === "proof-family" ? 10 : isMajorNode(item) && declarationKindFor(item) === "theorem" ? 8 : isMajorNode(item) ? 6 : 4).attr("fill", declarationColorFor);
  node.append("text").attr("class", "node-label").classed("implementation", (item) => presentationCategory(item) === "implementation").classed("supporting", (item) => presentationCategory(item) === "supporting").classed("routine", (item) => presentationCategory(item) === "routine").attr("data-focus-distance", (item) => state.focusDistances.get(item.id) ?? "").attr("x", 13).attr("y", 4).text((item) => `${verificationFor(item).glyph} ${labelFor(item)}`).classed("hidden", (item) => (!state.showImplementation && isBackgroundNode(item)) || (item.label.length > 31 && nodes.length > 12));
  const expanders = node.append("g").attr("class", "node-expand").attr("transform", "translate(0,-18)")
    .classed("hidden", (item) => item.id !== state.selectedId || !hasHiddenDependencies(item.id, nodes))
    .attr("role", "button")
    .attr("aria-label", (item) => `Expand dependencies of ${item.label}`)
    .on("click", (event, item) => { event.stopPropagation(); expandNodeDependencies(item.id); });
  expanders.append("circle").attr("r", 7);
  expanders.append("text").text("+");
  state.simulation?.stop();
  if (state.settleTimer) window.clearTimeout(state.settleTimer);
  state.settleTimer = null;
  state.simulation = null;
  // Focused neighborhoods should settle organically.  The rank calculation
  // supplies only a soft vertical preference; it must not turn the graph into
  // a stack of quantized horizontal bands.
  const staticLayout = nodes.length > 500;
  if (staticLayout) {
    link.attr("d", (edge) => routedLinkPath(edge, nodes));
    node.attr("transform", (item) => state.inspectionAnchor?.id === item.id
      ? `translate(${state.inspectionAnchor.x},${state.inspectionAnchor.y})`
      : `translate(${item.targetX},${item.targetY})`);
    nodes.forEach((item) => {
      if (state.inspectionAnchor?.id !== item.id) {
        item.x = item.targetX;
        item.y = item.targetY;
      }
      state.layoutPositions.set(item.id, { x: item.targetX, y: item.targetY });
    });
    link.attr("d", (edge) => routedLinkPath(edge, nodes));
  } else {
    state.simulation = d3.forceSimulation(nodes)
      .force("link", d3.forceLink(edges).id((item) => item.id).distance(state.focusId ? 104 : 82).strength(state.focusId ? 0.34 : 0.22))
      .force("y", d3.forceY((item) => item.id === coreId ? height * 0.5 : item.id === state.focusId ? height * 0.74 : graphTop + (ranks.get(item.id) || 0) * layerGap).strength((item) => item.id === state.focusId || item.id === coreId ? 0.92 : state.focusId ? 0.08 : 1.2))
      .force("x", d3.forceX((item) => item.id === state.focusId ? width / 2 : item.targetX ?? width / 2).strength((item) => item.id === state.focusId ? 0.76 : routeSides.has(item.id) && routeSides.get(item.id) !== 0 ? 0.42 : 0.12))
      .force("charge", d3.forceManyBody().strength(state.focusId ? -230 : -180))
      .force("collide", d3.forceCollide().radius((item) => item.kind === "proof-family" ? 26 : 21))
      .force("labels", labelCollisionForce(nodes))
      .force("top-down", topDownForce(edges, ranks))
      .alpha(0.22)
      .alphaDecay(0.16)
      .velocityDecay(0.72)
      .on("tick", () => {
      enforceTopDown(nodes, edges, ranks, state.focusId);
      const focusNode = nodes.find((item) => item.id === state.focusId);
      if (focusNode && !Number.isFinite(focusNode.fy)) {
        // The focus is an anchor for the whole progressive layout. Keep it
        // in a safe lower band while the top-down constraint moves its
        // prerequisites above it; otherwise a new frontier can briefly push
        // the theorem below the visible stage.
        focusNode.x = width / 2;
        focusNode.y = Math.max(height * 0.6, Math.min(height * 0.82, focusNode.y));
        focusNode.vx = 0;
        focusNode.vy = 0;
      }
      nodes.forEach((item) => {
        state.layoutPositions.set(item.id, { x: item.x, y: item.y });
        state.layoutVelocities.set(item.id, { x: item.vx || 0, y: item.vy || 0 });
      });
      link.attr("d", (edge) => routedLinkPath(edge, nodes))
        .attr("marker-end", (edge) => edge.source.y + 5 < edge.target.y && (isMajorNode(edge.source) || isMajorNode(edge.target)) ? "url(#arrow-used-in-proof)" : null);
      node.attr("transform", (item) => `translate(${item.x},${item.y})`);
      });
    scheduleSimulationStop();
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
    state.kinds = new Set(availableDeclarationKinds());
    $(".data-source code").textContent = DATA_URLS.map((url) => url.split("/").pop()).join(" + ");
    $("#loading-state").remove();
    populateTheoremSelect();
    kindControls();
    renderProofLegend();
    selectTheoremNode();
    updateWorkspaceContext();
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
  state.focusId = null;
  state.selectedProofId = null;
  state.layoutPositions.clear();
  state.layoutVelocities.clear();
  state.expandedDistances.clear();
  state.inspectionAnchor = null;
  state.revealedIds.clear();
  if (state.revealTimer) window.clearTimeout(state.revealTimer);
  state.revealTimer = null;
  state.revealPaused = false;
  state.revealPauseReason = null;
  state.inspectionPaused = false;
  state.resumeReveal = null;
  state.revealDepth = Infinity;
  state.revealLimit = Infinity;
  state.theoremNumber = null;
  state.search = "";
  $("#search").value = "";
  $("#theorem-select").value = "";
  document.querySelectorAll("#kind-filters input[type=checkbox]").forEach((input) => { input.checked = true; });
  state.showImplementation = false;
  state.showLandmarks = true;
  $("#show-implementation").checked = false;
  $("#show-landmarks").checked = true;
  state.kinds = new Set(availableDeclarationKinds());
  const next = new URL(window.location.href);
  next.searchParams.delete("theorem");
  next.searchParams.delete("graph");
  history.replaceState(null, "", next);
  updateTheoremNote();
  renderInspector();
  updateWorkspaceContext();
  draw();
});
$("#clear-selection").addEventListener("click", () => {
  state.selectedId = null;
  state.focusId = null;
  state.selectedProofId = null;
  state.layoutPositions.clear();
  state.layoutVelocities.clear();
  state.expandedDistances.clear();
  state.inspectionAnchor = null;
  state.revealedIds.clear();
  if (state.revealTimer) window.clearTimeout(state.revealTimer);
  state.revealTimer = null;
  state.revealPaused = false;
  state.inspectionPaused = false;
  state.resumeReveal = null;
  state.theoremNumber = null;
  $("#theorem-select").value = "";
  const next = new URL(window.location.href);
  next.searchParams.delete("theorem");
  history.replaceState(null, "", next);
  updateTheoremNote();
  renderInspector();
  updateWorkspaceContext();
  draw();
});
$("#back-to-theorem").addEventListener("click", () => {
  if (state.focusId) selectNode(state.focusId);
});
$("#show-implementation").addEventListener("change", (event) => { state.showImplementation = event.target.checked; draw(); });
$("#show-landmarks").addEventListener("change", (event) => { state.showLandmarks = event.target.checked; draw(); });
$("#focus-status").addEventListener("click", () => state.resumeReveal?.());
window.addEventListener("resize", () => draw());
load();
