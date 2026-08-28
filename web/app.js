import * as d3 from "https://cdn.jsdelivr.net/npm/d3@7/+esm";
import dagre from "https://cdn.jsdelivr.net/npm/@dagrejs/dagre@1.1.5/+esm";

const query = new URLSearchParams(window.location.search);
const requestedGraph = query.get("graph");
const requestedTheorem = query.get("theorem");
const requestedDeclaration = query.get("declaration");
const requestedComparison = query.get("comparison");
const requestedRoute = query.get("route");
const REPO_ROOT = window.location.pathname.includes("/web/") ? "../" : "./";
// The HTML entry point versions this module on every publish. Reuse that
// revision for graph assets so the interface and its extracted Lean data can
// never be served from different deployments by a CDN cache.
const APP_REVISION = new URL(import.meta.url).searchParams.get("v") || "dev";
const versionedAsset = (url) => `${url}${url.includes("?") ? "&" : "?"}v=${encodeURIComponent(APP_REVISION)}`;
const THEOREMS_URL = versionedAsset("./theorems.json");
const COMPARISONS_URL = versionedAsset(`${REPO_ROOT}MathNetwork/Graph/comparisons.json`);
const READER_STATEMENTS_URL = versionedAsset(`${REPO_ROOT}MathNetwork/Graph/reader-statements.json`);
const SOURCE_REVISIONS_URL = versionedAsset(`${REPO_ROOT}MathNetwork/Graph/source-revisions.json`);
const DATA_URLS = [versionedAsset(`${REPO_ROOT}MathNetwork/Graph/project.json`)];
const comparisonSliceUrl = (comparisonId) => versionedAsset(
  `${REPO_ROOT}MathNetwork/Graph/slices/${encodeURIComponent(comparisonId)}.json`,
);
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
  structure: "Structures",
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
  structure: "#795a76",
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
  structure: "#eadfe8",
};
const REPOSITORIES = {
  mathlib: { label: "mathlib", color: "#3f7f8f" },
  "computable-analysis": { label: "computable-analysis", color: "#a45b38" },
  "tao-analysis": { label: "Tao Analysis", color: "#65799b" },
  "math-net": { label: "math-net", color: "#7a6397" },
  unknown: { label: "unclassified source", color: "#7f8589" },
};
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
// Focused views read from prerequisites above toward a theorem below. Keep
// that theorem in the lower-middle, not on the viewport edge, so it remains
// visible while additional prerequisite layers are revealed.
const FOCUS_Y_FRACTION = 0.62;

const state = {
  graph: null,
  theorems: [],
  comparisons: [],
  comparisonsByDeclaration: new Map(),
  readerStatements: {},
  sourceRevisions: {},
  graphPromise: null,
  graphPartial: false,
  // A bare visit begins with the proof-landscape overview. Deep links retain
  // their theorem or graph focus through the query parameters.
  theoremNumber: requestedTheorem || theoremForGraph() || null,
  focusId: null,
  coreId: null,
  selectedId: null,
  selectedProofId: null,
  search: "",
  kinds: new Set(),
  simulation: null,
  settleTimer: null,
  sourceRequest: 0,
  focusDistances: new Map(),
  showImplementation: false,
  showSupporting: false,
  showLandmarks: true,
  revealDepth: Infinity,
  revealLimit: Infinity,
  revealTimer: null,
  revealSteps: [],
  revealCursor: 0,
  revealedIds: new Set(),
  layoutPositions: new Map(),
  layoutVelocities: new Map(),
  pinnedPositions: new Map(),
  expandedDistances: new Map(),
  inspectionAnchor: null,
  rankTransition: null,
  rankTransitionFrame: null,
  rankSettleStarts: null,
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

function sourceRevision(repository) {
  return state.sourceRevisions?.[repository]?.revision || "main";
}

function sourceUrlFor(node, proof = null) {
  const file = sourceFileFor(node, proof);
  const locator = proof?.locator || node.locator;
  if (!file) return null;
  // A math-net adapter can deliberately delegate to a theorem imported from
  // another repository. Its source file is nevertheless local, and must win
  // over the canonicalized node locator when the inspector fetches code.
  if (file.startsWith("MathNetwork/")) {
    return `https://raw.githubusercontent.com/liuyao12/math-net/main/${file}`;
  }
  if (locator?.startsWith("mathlib/")) {
    return `https://raw.githubusercontent.com/leanprover-community/mathlib4/${sourceRevision("mathlib")}/${file}`;
  }
  if (locator?.startsWith("computable-analysis/")) {
    return `https://raw.githubusercontent.com/liuyao12/computable-analysis/${sourceRevision("computable-analysis")}/${file}`;
  }
  // GitHub Pages publishes the web directory, not the repository root.
  // Use the canonical raw source for math-net declarations so Lean code is
  // available in the deployed inspector as well as during local development.
  return `https://raw.githubusercontent.com/liuyao12/math-net/main/${file}`;
}

function githubUrlFor(node, item = null) {
  const file = item?.file || sourceFileFor(node, item);
  if (file?.startsWith("MathNetwork/")) return `${GITHUB_REPO}/blob/main/${file}`;
  const locator = item?.locator || node.locator;
  if (locator?.startsWith("mathlib/")) {
    const file = `${locator.slice("mathlib/".length).replaceAll(".", "/")}.lean`;
    return `https://github.com/leanprover-community/mathlib4/blob/${sourceRevision("mathlib")}/${file}`;
  }
  if (locator?.startsWith("computable-analysis/")) {
    const file = `${locator.slice("computable-analysis/".length).replaceAll(".", "/")}.lean`;
    return `${COMPUTABLE_ANALYSIS_REPO}/blob/${sourceRevision("computable-analysis")}/${file}`;
  }
  return null;
}

function declarationSource(text, name) {
  const short = name.split(".").pop();
  const escaped = short.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const declaration = new RegExp(`^\\s*(?:(?:protected|private)\\s+)?(?:(?:noncomputable)\\s+)?(theorem|lemma|def|abbrev|example|axiom|opaque|instance|class|structure|inductive)\\s+${escaped}\\b`, "m");
  const match = declaration.exec(text);
  if (!match) return null;
  const start = text.lastIndexOf("\n", match.index) + 1;
  const rest = text.slice(match.index + match[0].length);
  const next = rest.search(/\n(?=\s*(?:theorem|lemma|def|noncomputable def|example|axiom)\s+)/);
  return text.slice(start, next < 0 ? text.length : match.index + match[0].length + next + 1).trim();
}

function compactLeanSource(source, { maxLines = 32, maxLineLength = 260 } = {}) {
  const lines = String(source).trim().split("\n");
  const shortened = lines.map((line) => line.length <= maxLineLength
    ? line
    : `${line.slice(0, maxLineLength - 42)}  -- … ${line.length - maxLineLength + 42} characters omitted`);
  if (shortened.length <= maxLines) return shortened.join("\n");
  const head = Math.ceil(maxLines * 0.7);
  const tail = maxLines - head;
  return [
    ...shortened.slice(0, head),
    `-- … ${shortened.length - head - tail} source lines omitted; open the full file on GitHub`,
    ...shortened.slice(-tail),
  ].join("\n");
}

function declarationSignature(source) {
  const proofStart = source.search(/:=\s*(?:by\b|\n)/);
  const signature = proofStart >= 0 ? source.slice(0, proofStart).trimEnd() : source;
  return compactLeanSource(signature, { maxLines: 12, maxLineLength: 220 });
}

async function loadDeclarationSignature(node, container, request, selectedProof = null) {
  const proof = selectedProof || (node.proofs || []).find((item) => item.id === state.selectedProofId) || null;
  const file = sourceFileFor(node, proof);
  const formalization = proof
    ? { file: proof.file, name: proof.declaration }
    : (node.formalizations || []).find((item) => item.file);
  if (!file) {
    container.textContent = "Lean source is unavailable for this generated declaration.";
    container.classList.remove("pending");
    return;
  }
  try {
    const response = await fetch(sourceUrlFor(node, proof));
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    const source = declarationSource(await response.text(), formalization?.name || proof?.declaration || node.namespace || node.label);
    if (request !== state.sourceRequest) return;
    container.innerHTML = `<code>${highlightLean(source ? declarationSignature(source) : `-- ${node.label}: declaration signature could not be isolated from ${file}`)}</code>`;
  } catch (_) {
    if (request !== state.sourceRequest) return;
    container.textContent = `Source unavailable for ${file}.`;
  }
  container.classList.remove("pending");
}

async function loadProofSource(node, container, request, selectedProof = null) {
  const proof = selectedProof || (node.proofs || []).find((item) => item.id === state.selectedProofId) || null;
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
    const code = source
      ? compactLeanSource(source)
      : `-- Source file: ${file}\n-- ${node.label} is elaborated or generated in this module.\n-- Its declaration cannot be isolated reliably from source text; use the GitHub link for the full file.`;
    container.innerHTML = `<code>${highlightLean(code)}</code>`;
    container.classList.remove("pending");
  } catch (error) {
    if (request !== state.sourceRequest) return;
    container.textContent = `Source unavailable for ${file}. The checked declaration is shown above.`;
    container.classList.remove("pending");
  }
}

function nodeMap() {
  return new Map((state.graph?.nodes || []).map((node) => [node.id, node]));
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

function isSuppressedNode(node) {
  const category = presentationCategory(node);
  if (category === "supporting") return !state.showSupporting;
  if (category === "routine" || category === "implementation") return !state.showImplementation;
  return false;
}

function isLandmark(node) {
  return Boolean(node?.importance?.landmark);
}

function isStructureNode(node) {
  return node?.role === "structure";
}

function mathematicalRole(node) {
  return node?.mathematicalRole?.category || (isStructureNode(node) ? "interface" : "supporting");
}

function isMathematicalFoundation(node) {
  return mathematicalRole(node) === "foundation";
}

function isReaderFacingStructure(node) {
  // Lean's `structure` is a representation choice, not evidence that the
  // declaration belongs in a mathematical first reading. Foundations always
  // remain visible; other interfaces must also be structurally important in
  // the indexed proof landscape. Every omitted structure remains reachable
  // through the ordinary expansion controls.
  return isMathematicalFoundation(node) || (isStructureNode(node) && isLandmark(node) && !isImplementationNode(node));
}

function readingPriority(node) {
  if (!node) return -Infinity;
  if (node.comparison?.routes?.length > 1) return 9000;
  if (isMathematicalNode(node)) return 7000 + (node.importance?.score || 0);
  if (node.importance?.landmark) return 6000 + (node.importance?.score || 0);
  // Structures remain visible, but are foundations along a proof route rather
  // than privileged roots of every focused graph.
  if (isMathematicalFoundation(node)) return 5000 + (node.importance?.score || 0);
  if (isStructureNode(node)) return 3500 + (node.importance?.score || 0);
  if (presentationCategory(node) === "supporting") return 1000 + (node.importance?.score || 0);
  return node.importance?.score || 0;
}

function ambientNodesForFocus(nodes) {
  const focus = nodes.find((node) => node.id === state.focusId);
  if (focus?.comparison?.registry === "irrational-sqrt-two" || focus?.namespace === "MathNetwork.SqrtTwo.irrational") {
    return new Set(nodes.filter((node) => node.namespace === "Real" || node.label === "Real").map((node) => node.id));
  }
  return new Set();
}

function displayLabelFor(node) {
  return node?.label || "unnamed declaration";
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

function searchCandidates(query) {
  if (!state.graph || query.trim().length < 2) return [];
  const needle = query.trim().toLowerCase();
  return state.graph.nodes
    .filter((node) => isMathematicalNode(node) && isSearchMatch({ ...node, label: node.label || "" }))
    .map((node) => {
      const label = node.label.toLowerCase();
      const namespace = (node.namespace || "").toLowerCase();
      const score = label === needle ? 0 : label.startsWith(needle) ? 1 : namespace.startsWith(needle) ? 2 : 3;
      return { node, score };
    })
    .sort((left, right) => left.score - right.score || Number(isLandmark(right.node)) - Number(isLandmark(left.node)) || left.node.label.localeCompare(right.node.label))
    .slice(0, 8)
    .map(({ node }) => node);
}

function renderSearchResults() {
  const container = $("#search-results");
  if (!state.graph && state.search.trim().length >= 2) {
    container.innerHTML = `<div class="search-result-meta">Loading declaration index…</div>`;
    return;
  }
  const matches = searchCandidates(state.search);
  container.innerHTML = matches.map((node) => `<button class="search-result" role="option" data-search-node="${escapeHtml(node.id)}"><span class="search-result-name">${escapeHtml(node.label)}</span><span class="search-result-meta">${escapeHtml(declarationKindFor(node))}${node.namespace ? ` · ${escapeHtml(node.namespace)}` : ""}</span></button>`).join("");
  container.querySelectorAll("[data-search-node]").forEach((button) => button.addEventListener("click", () => focusDeclaration(button.dataset.searchNode)));
}

function focusDeclaration(nodeId) {
  const node = nodeMap().get(nodeId);
  if (!node) return;
  state.focusId = nodeId;
  state.selectedId = nodeId;
  state.selectedProofId = null;
  state.theoremNumber = null;
  state.search = "";
  state.layoutPositions.clear();
  state.layoutVelocities.clear();
  state.pinnedPositions.clear();
  state.expandedDistances.clear();
  state.inspectionAnchor = null;
  $("#search").value = "";
  $("#search-results").replaceChildren();
  $("#theorem-select").value = "";
  const comparisonSelect = $("#comparison-select");
  if (comparisonSelect) comparisonSelect.value = node.comparison?.registry || "";
  const next = new URL(window.location.href);
  next.searchParams.delete("theorem");
  next.searchParams.delete("graph");
  next.searchParams.set("declaration", node.namespace || node.id);
  if (node.comparison?.registry) next.searchParams.set("comparison", node.comparison.registry);
  else next.searchParams.delete("comparison");
  next.searchParams.delete("route");
  history.replaceState(null, "", next);
  updateTheoremNote();
  renderInspector();
  updateWorkspaceContext();
  beginProgressiveReveal();
}

async function openComparison(comparisonId) {
  if (!state.graph || state.graphPartial) await loadComparisonSlice(comparisonId);
  const node = comparisonNode(comparisonId);
  if (node) focusDeclaration(node.id);
}

function comparisonNode(comparisonId) {
  const comparison = state.comparisons.find((candidate) => candidate.id === comparisonId);
  const declarations = new Set((comparison?.routes || []).map((route) => route.declaration));
  return state.graph?.nodes.find((candidate) =>
    candidate.comparison?.registry === comparisonId ||
    declarations.has(candidate.namespace) ||
    (candidate.proofs || []).some((proof) => declarations.has(proof.declaration)));
}

function comparisonRecordForNode(node) {
  if (!node) return null;
  const focusedSliceComparison = node.id === state.focusId && state.graph?.focusComparison;
  const focusedSliceRecord = focusedSliceComparison && state.comparisons.find((comparison) => comparison.id === focusedSliceComparison);
  if (focusedSliceRecord) return focusedSliceRecord;
  const registeredId = node.comparison?.registry;
  const registered = registeredId && state.comparisons.find((comparison) => comparison.id === registeredId);
  if (registered) return registered;
  const declarations = [node.namespace, ...(node.proofs || []).map((proof) => proof.declaration)].filter(Boolean);
  return declarations.map((declaration) => state.comparisonsByDeclaration.get(declaration)).find(Boolean) || node.comparison || null;
}

function focusDistances(nodeId, edges) {
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
  let depth = 0;
  while (frontier.length) {
    depth += 1;
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

function upstreamPath(focusId, targetId, edges) {
  if (!focusId || !targetId) return new Set();
  const incoming = new Map();
  edges.forEach((edge) => {
    if (!incoming.has(edge.target.id)) incoming.set(edge.target.id, []);
    incoming.get(edge.target.id).push(edge.source.id);
  });
  const queue = [focusId];
  const previous = new Map([[focusId, null]]);
  while (queue.length) {
    const current = queue.shift();
    if (current === targetId) break;
    (incoming.get(current) || []).forEach((sourceId) => {
      if (previous.has(sourceId)) return;
      previous.set(sourceId, current);
      queue.push(sourceId);
    });
  }
  if (!previous.has(targetId)) return new Set();
  const path = new Set();
  for (let current = targetId; current !== null; current = previous.get(current)) path.add(current);
  return path;
}

function upstreamDependencies(rootId, edges, maxDepth = 1) {
  if (!rootId) return new Set();
  const incoming = new Map();
  edges.forEach((edge) => {
    if (!incoming.has(edge.target.id)) incoming.set(edge.target.id, []);
    incoming.get(edge.target.id).push(edge.source.id);
  });
  const dependencies = new Set([rootId]);
  let frontier = [rootId];
  for (let depth = 0; depth < maxDepth && frontier.length; depth += 1) {
    const next = [];
    frontier.forEach((targetId) => (incoming.get(targetId) || []).forEach((sourceId) => {
      if (dependencies.has(sourceId)) return;
      dependencies.add(sourceId);
      next.push(sourceId);
    }));
    frontier = next;
  }
  return dependencies;
}

function visibleGraph() {
  const nodesById = nodeMap();
  const allEdgeData = state.graph.edges
    .filter((edge) => edge.relation === "used-in-proof")
    .map((edge) => ({ ...edge, source: nodesById.get(edge.source.id), target: nodesById.get(edge.target.id) }))
    // Canonicalization can merge two declarations with the same displayed
    // identity.  Their extraction edge then becomes a self-loop, which says
    // nothing useful in a dependency view and cannot be top-down.
    .filter((edge) => edge.source && edge.target && edge.source.id !== edge.target.id);
  const edgeData = proofRouteEdges(allEdgeData, state.focusId, state.selectedProofId);
  state.focusDistances = state.focusId ? focusDistances(state.focusId, edgeData) : new Map();
  const coreId = coreNodeFor(state.graph.nodes);
  state.coreId = coreId;
  const corePath = coreId ? upstreamPath(state.focusId, coreId, edgeData) : new Set();
  const core = coreId ? nodesById.get(coreId) : null;
  // A foundation-aligned comparison is specifically about how the same
  // mathematical criterion is expressed over two real-number constructions.
  // Retain the *actual Lean dependency paths* to those representations; no
  // explanatory relationship edges are invented here.
  const foundationPaths = new Set();
  (core?.comparison?.foundations || []).forEach((foundation) => {
    const anchor = state.graph.nodes.find((node) => node.namespace === foundation.declaration);
    if (anchor) upstreamPath(coreId, anchor.id, edgeData).forEach((id) => foundationPaths.add(id));
  });
  // Keep the core theorem's *direct* inputs in view even when they are
  // normally background declarations. Further foundations stay behind the
  // node's explicit expander; two raw extraction levels can be hundreds of
  // typeclass/projection details rather than mathematical content.
  const coreDependencies = coreId
    ? new Set([...upstreamDependencies(coreId, edgeData)].filter((id) => isMajorNode(nodesById.get(id))))
    : new Set();
  // A structure used directly by the focus is part of the mathematical
  // statement readers need first; its construction details stay collapsed.
  const focusStructures = new Set(state.focusId
    ? edgeData.filter((edge) => edge.target.id === state.focusId && isReaderFacingStructure(edge.source)).map((edge) => edge.source.id)
    : []);
  const ambientIds = ambientNodesForFocus(state.graph.nodes);
  const forcedIds = new Set([...corePath, ...coreDependencies, ...foundationPaths, ...focusStructures, ...ambientIds]);
  const manuallyExpandedIds = new Set(state.expandedDistances.keys());
  const candidateNodes = state.graph.nodes.filter((node) => state.kinds.has(declarationKindFor(node)) &&
    (!isSuppressedNode(node) || isReaderFacingStructure(node) || node.id === state.focusId || node.id === state.selectedId || forcedIds.has(node.id) || manuallyExpandedIds.has(node.id)));
  state.expandedDistances.forEach((distance, id) => {
    if (!state.focusDistances.has(id) || distance < state.focusDistances.get(id)) state.focusDistances.set(id, distance);
  });
  const focus = searchFocus(candidateNodes, edgeData);
  const visibleNodes = candidateNodes.filter((node) => {
    if (state.focusId && !state.focusDistances.has(node.id) && !forcedIds.has(node.id)) return false;
    if (state.focusId && state.revealDepth !== Infinity && !state.revealedIds.has(node.id) && !forcedIds.has(node.id)) return false;
    if (state.search && !focus.has(node.id)) return false;
    return true;
  }).filter((node, index) => !state.focusId && state.revealLimit !== Infinity ? index < state.revealLimit : true);
  const allowed = new Set(visibleNodes.map((node) => node.id));
  const visibleEdges = edgeData.filter((edge) => allowed.has(edge.source.id) && allowed.has(edge.target.id));
  // Contract suppressed routine/implementation nodes. The visual graph stays
  // connected without pretending that the omitted declarations vanished from
  // Lean's actual proof term.
  if (candidateNodes.length < state.graph.nodes.length) {
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
  // Ambient boundary nodes, such as ℝ in the √2 view, are deliberately
  // retained even when their immediate implementation bridge is collapsed.
  // They name the mathematical object in play without opening its foundation.
  const connectedNodes = visibleNodes.filter((node) => node.id === state.focusId || forcedIds.has(node.id) || connected.has(node.id));
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
  const indexed = document.createElement("optgroup");
  indexed.label = "Indexed theorem neighborhoods";
  const catalogued = document.createElement("optgroup");
  catalogued.label = "Catalogue only — graph not yet imported";
  state.theorems.forEach((theorem) => {
    const option = document.createElement("option");
    option.value = String(theorem.number);
    option.textContent = `${String(theorem.number).padStart(2, "0")} · ${theorem.title}`;
    if (theorem.graph) indexed.append(option);
    else {
      option.disabled = true;
      catalogued.append(option);
    }
  });
  select.append(indexed, catalogued);
  if (state.theoremNumber) select.value = String(state.theoremNumber);
  updateTheoremNote();
  select.addEventListener("change", (event) => {
    const number = event.target.value;
    $("#comparison-select").value = "";
    if (!number) {
      const next = new URL(window.location.href);
      next.searchParams.delete("theorem");
      next.searchParams.delete("declaration");
      next.searchParams.delete("comparison");
      next.searchParams.delete("route");
      history.replaceState(null, "", next);
      state.theoremNumber = null;
      state.focusId = null;
      state.selectedId = null;
      state.layoutPositions.clear();
      state.layoutVelocities.clear();
      state.pinnedPositions.clear();
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
    next.searchParams.delete("declaration");
    next.searchParams.delete("comparison");
    next.searchParams.delete("route");
    history.pushState(null, "", next);
    state.theoremNumber = number;
    state.focusId = null;
    state.selectedId = null;
    state.selectedProofId = null;
    state.layoutPositions.clear();
    state.layoutVelocities.clear();
    state.pinnedPositions.clear();
    state.expandedDistances.clear();
    state.inspectionAnchor = null;
    state.revealedIds.clear();
    if (state.revealTimer) window.clearTimeout(state.revealTimer);
    state.revealTimer = null;
    updateTheoremNote();
    selectTheoremNode();
  });
}

function populateComparisonSelect() {
  const select = $("#comparison-select");
  if (!select) return;
  const comparisons = state.comparisons
    .filter((comparison) => comparison.routes?.length > 0)
    .sort((left, right) => left.title.localeCompare(right.title));
  const groups = [
    ["exact", "Exact merged propositions"],
    ["benchmark", "Concrete checked benchmarks"],
    ["foundation-aligned", "Foundation-aligned routes"],
    ["presentation", "Checked applications"],
  ];
  groups.forEach(([alignment, label]) => {
    const items = comparisons.filter((comparison) => alignment === "benchmark"
      ? !comparison.alignment && comparison.routes?.length <= 1
      : alignment === "exact"
        ? !comparison.alignment && comparison.routes?.length > 1
        : comparison.alignment === alignment);
    if (!items.length) return;
    const group = document.createElement("optgroup");
    group.label = label;
    items.forEach((comparison) => {
    const option = document.createElement("option");
    option.value = comparison.id;
    const routeSummary = comparison.alignment === "foundation-aligned"
      ? "foundation-aligned"
      : comparison.alignment === "presentation"
        ? "checked presentation"
        : comparison.routes?.length > 1
          ? `${comparison.routes.length} exact routes`
          : "checked benchmark";
    option.textContent = `${comparison.title} · ${routeSummary}`;
    group.append(option);
  });
    select.append(group);
  });
  select.addEventListener("change", (event) => {
    if (event.target.value) openComparison(event.target.value);
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
    ? `<span class="theorem-ready">✓ indexed Lean dependency neighborhood</span> · choose it to inspect the mathematical spine`
    : "catalogued · dependency graph not imported yet";
}

async function selectTheoremNode() {
  await ensureGraph();
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
    const visibleSeen = new Set([state.focusId]);
    // This is a budget of reader-facing mathematics, not a number of Lean
    // generations.  It lets a narrow route continue through structures and
    // implementation details while preventing broad infrastructure fans from
    // taking over the initial canvas.
    const interestingNode = (node) => Boolean(node?.comparison) || isMathematicalNode(node) || isLandmark(node) || isReaderFacingStructure(node);
    const maxInterestingNodes = 56;
    const maxVisibleNodes = 92;
    let interestingCount = interestingNode(nodeMap().get(state.focusId)) ? 1 : 0;
    const queue = [{ id: state.focusId, depth: 0 }];
    state.revealCapped = false;
    while (queue.length) {
      const parent = queue.shift();
      // A familiar mathematical object is a useful default endpoint. This is
      // deliberately narrower than Lean's `structure` kind: interfaces and
      // representation constructions still reveal their prerequisites.
      if (isMathematicalFoundation(nodeMap().get(parent.id))) continue;
      const children = [];
      const existing = [];
      const branchBudget = parent.depth === 0 ? 8 : parent.depth === 1 ? 6 : 4;
      let branchInterestingCount = 0;
      (adjacency.get(parent.id) || []).slice()
        .sort((left, right) => readingPriority(nodeMap().get(right)) - readingPriority(nodeMap().get(left)) || left.localeCompare(right))
        .forEach((neighbor) => {
        if (!nodeIds.has(neighbor)) return;
        if (seen.has(neighbor)) {
          if (!isSuppressedNode(nodeMap().get(neighbor)) || isReaderFacingStructure(nodeMap().get(neighbor))) existing.push(neighbor);
          return;
        }
        const neighborNode = nodeMap().get(neighbor);
        const visibleNeighbor = !isSuppressedNode(neighborNode) || isReaderFacingStructure(neighborNode);
        const countsAsInteresting = visibleNeighbor && interestingNode(neighborNode);
        if (visibleNeighbor && (visibleSeen.size >= maxVisibleNodes || children.length >= branchBudget ||
          (countsAsInteresting && (interestingCount >= maxInterestingNodes || branchInterestingCount >= branchBudget)))) {
          state.revealCapped = true;
          return;
        }
        seen.add(neighbor);
        if (visibleNeighbor) {
          visibleSeen.add(neighbor);
          children.push(neighbor);
          if (countsAsInteresting) {
            interestingCount += 1;
            branchInterestingCount += 1;
          }
        }
        // Hidden Lean infrastructure is traversed so a later mathematical
        // theorem can still be discovered, but it does not create an empty
        // animation batch in the reader-facing graph.
        if (!visibleNeighbor) queue.push({ id: neighbor, depth: parent.depth + 1 });
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
      const step = state.revealSteps[state.revealCursor];
      step.nodeIds.forEach((id) => state.revealedIds.add(id));
      state.revealCursor += 1;
    } else {
      if (state.revealLimit >= state.graph.nodes.length) { state.revealTimer = null; return; }
      state.revealLimit = Math.min(state.graph.nodes.length, state.revealLimit + 220);
    }
    draw();
    // A new parent batch can introduce an extra rank which moves the already
    // visible top layer upward.  Treat the addition as provisional: do not
    // leave half-visible declarations beyond the viewport merely because the
    // previous frontier happened to fit.  The same batch resumes naturally
    // once panning or zooming provides room.
    if (focused && viewportHasEdgeNode()) {
      const step = state.revealSteps[state.revealCursor - 1];
      step?.nodeIds.forEach((id) => state.revealedIds.delete(id));
      state.revealCursor -= 1;
      state.revealPaused = true;
      state.revealPauseReason = "viewport";
      draw();
      state.revealTimer = null;
      updateHighlight();
      return;
    }
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

function disambiguatingContext(node) {
  const short = displayLabelFor(node);
  const namespaceParts = String(node.namespace || "").split(".").filter(Boolean);
  const namespaceContext = namespaceParts.slice(0, -1).at(-1);
  if (namespaceContext && namespaceContext !== short) return namespaceContext;
  const moduleParts = String(node.module || node.locator || "").split(/[./]/).filter(Boolean);
  const moduleContext = moduleParts.at(-1);
  if (moduleContext && moduleContext !== short) return moduleContext;
  return moduleParts[0] || namespaceParts[0] || "Lean";
}

function labelFor(node, peers = null) {
  const label = displayLabelFor(node);
  // A short Lean identifier is normally the most legible graph label. When
  // several visible declarations share it, show the real namespace/module
  // context rather than making distinct proof routes visually indistinct.
  const collides = peers?.some((candidate) => candidate.id !== node.id && displayLabelFor(candidate) === label);
  const visible = collides ? `${disambiguatingContext(node)}.${label}` : label;
  return visible.length > 29 ? `${visible.slice(0, 27)}…` : visible;
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
  return isMathematicalNode(node) || isReaderFacingStructure(node);
}

function repositoryForProof(proof) {
  if (!proof) return "unknown";
  if (proof.repository && REPOSITORIES[proof.repository]) return proof.repository;
  if (proof.routeKind === "local") return "math-net";
  if (proof.routeKind === "mathlib" || proof.locator?.startsWith("mathlib/")) return "mathlib";
  if (proof.routeKind === "computable-analysis") return "computable-analysis";
  if (proof.file?.startsWith("MathNetwork/")) return "math-net";
  return "unknown";
}

function repositoryForFormalization(formalization) {
  if (formalization?.repository === "mathlib4" || formalization?.locator?.startsWith("mathlib/")) return "mathlib";
  if (formalization?.repository === "computable-analysis" || formalization?.locator?.startsWith("computable-analysis/")) return "computable-analysis";
  if (formalization?.name?.startsWith("MathNetwork.")) return "math-net";
  return null;
}

function repositoriesForNode(node) {
  // An adapter records a useful alternative declaration, but its repository
  // should not make a theorem look like it has another proof. Prefer bodies;
  // fall back to adapters only for a declaration with no inspectable body.
  const routeProofs = (node.proofs || []).filter((proof) => proof.proofKind !== "delegation");
  const repositories = new Set((routeProofs.length ? routeProofs : (node.proofs || [])).map(repositoryForProof));
  if (!repositories.size) (node.formalizations || []).map(repositoryForFormalization).filter(Boolean).forEach((repository) => repositories.add(repository));
  if (!repositories.size && node.locator?.startsWith("mathlib/")) repositories.add("mathlib");
  if (!repositories.size && node.locator?.startsWith("computable-analysis/")) repositories.add("computable-analysis");
  if (!repositories.size && node.file?.startsWith("MathNetwork/")) repositories.add("math-net");
  if (!repositories.size && node.namespace?.startsWith("MathNetwork.")) repositories.add("math-net");
  if (!repositories.size) repositories.add("unknown");
  return [...repositories].sort((left, right) => REPOSITORIES[left].label.localeCompare(REPOSITORIES[right].label));
}

function repositoryColor(repository) {
  return (REPOSITORIES[repository] || REPOSITORIES.unknown).color;
}

function proofColor(proofId = "") {
  for (const node of state.graph?.nodes || []) {
    const proof = (node.proofs || []).find((item) => item.id === proofId);
    if (proof) return repositoryColor(repositoryForProof(proof));
  }
  return repositoryColor("unknown");
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
  const proofMeta = new Map();
  state.graph.nodes.forEach((node) => (node.proofs || []).forEach((proof) => proofMeta.set(proof.id, proof)));
  const usedProofs = new Set(state.graph.edges.map((edge) => edge.proof).filter(Boolean));
  const grouped = new Set();
  [...usedProofs].forEach((proofId) => {
    const proof = proofMeta.get(proofId);
    grouped.add(repositoryForProof(proof));
  });
  const entries = [...grouped]
    .map((id) => ({ id, label: (REPOSITORIES[id] || REPOSITORIES.unknown).label }))
    .sort((left, right) => left.label.localeCompare(right.label));
  const evidence = { exact: 0, aligned: 0, presentation: 0 };
  state.graph.nodes.forEach((node) => {
    const alignment = node.comparison?.alignment;
    if (alignment === "exact") evidence.exact += 1;
    else if (alignment === "foundation-aligned") evidence.aligned += 1;
    else if (alignment === "presentation") evidence.presentation += 1;
  });
  const evidenceLegend = `<span class="legend-heading evidence-heading">Comparison evidence</span><span class="legend-item evidence-exact">${evidence.exact} exact merged</span><span class="legend-item evidence-aligned">${evidence.aligned} foundation-aligned</span><span class="legend-item evidence-presentation">${evidence.presentation} checked presentation</span>`;
  const roleLegend = `<span class="legend-heading role-heading">Mathematical reading</span><span class="legend-item"><span class="role-glyph declaration" aria-hidden="true"></span>declaration</span><span class="legend-item"><span class="role-glyph interface" aria-hidden="true"></span>Lean interface</span><span class="legend-item"><span class="role-glyph foundation" aria-hidden="true"></span>mathematical foundation</span><span class="legend-item"><span class="role-glyph implementation" aria-hidden="true"></span>implementation detail</span>`;
  container.innerHTML = entries.length
    ? `<span class="legend-heading">Repository colors · nodes and proof arrows</span>${entries.map((entry) => `<span class="legend-item"><span class="legend-dot repository-dot" style="background:${escapeHtml(repositoryColor(entry.id))}"></span><span>${escapeHtml(entry.label)}</span></span>`).join("")}${evidenceLegend}${roleLegend}`
    : "";
}

function nodeRadius(item, coreId, ambientIds) {
  return isStructureNode(item) ? 16 : item.id === state.focusId ? 13 : item.id === coreId ? 12 : ambientIds.has(item.id) ? 8 : item.kind === "proof-family" ? 10 : isMajorNode(item) && declarationKindFor(item) === "theorem" ? 8 : isMajorNode(item) ? 6 : 4;
}

function pieSlicePath(index, count, radius) {
  const start = -Math.PI / 2 + (index * 2 * Math.PI / count);
  const end = -Math.PI / 2 + ((index + 1) * 2 * Math.PI / count);
  const x1 = radius * Math.cos(start);
  const y1 = radius * Math.sin(start);
  const x2 = radius * Math.cos(end);
  const y2 = radius * Math.sin(end);
  return `M0,0 L${x1},${y1} A${radius},${radius} 0 ${end - start > Math.PI ? 1 : 0} 1 ${x2},${y2} Z`;
}

function nodeNeighbors(nodeId) {
  const map = nodeMap();
  const neighbors = new Map();
  state.graph.edges.forEach((edge) => {
    const direction = edge.source.id === nodeId ? "out" : edge.target.id === nodeId ? "in" : null;
    if (!direction) return;
    const neighborId = direction === "out" ? edge.target.id : edge.source.id;
    const neighbor = map.get(neighborId);
    if (!neighbor || neighborId === nodeId) return;
    const key = `${direction}:${neighborId}`;
    if (!neighbors.has(key)) neighbors.set(key, { relation: edge.relation, node: neighbor, direction, proofs: new Set() });
    if (edge.proof) neighbors.get(key).proofs.add(edge.proof);
  });
  return [...neighbors.values()]
    .map((item) => ({ ...item, proofs: [...item.proofs] }))
    .sort((left, right) => Number(isMajorNode(right.node)) - Number(isMajorNode(left.node)) || left.node.label.localeCompare(right.node.label));
}

function proofDependencySummaries(nodeId, proofs) {
  if (!proofs?.length || !state.graph) return new Map();
  const dependencies = new Map(proofs.map((proof) => [proof.id, new Set()]));
  state.graph.edges.forEach((edge) => {
    if (edge.relation === "used-in-proof" && edge.target.id === nodeId && edge.source.id !== nodeId && dependencies.has(edge.proof)) {
      dependencies.get(edge.proof).add(edge.source.id);
    }
  });
  const useCount = new Map();
  dependencies.forEach((ids) => ids.forEach((id) => useCount.set(id, (useCount.get(id) || 0) + 1)));
  return new Map(proofs.map((proof) => {
    const ids = dependencies.get(proof.id) || new Set();
    const shared = [...ids].filter((id) => useCount.get(id) === proofs.length).length;
    const routeOnly = [...ids].filter((id) => useCount.get(id) === 1).length;
    return [proof.id, { total: ids.size, shared, routeOnly }];
  }));
}

function proofDependencyDifference(nodeId, proofs) {
  if (!proofs?.length || !state.graph) return null;
  const dependencies = new Map(proofs.map((proof) => [proof.id, new Set()]));
  state.graph.edges.forEach((edge) => {
    if (edge.relation === "used-in-proof" && edge.target.id === nodeId && edge.source.id !== nodeId && dependencies.has(edge.proof)) {
      dependencies.get(edge.proof).add(edge.source.id);
    }
  });
  const useCount = new Map();
  dependencies.forEach((ids) => ids.forEach((id) => useCount.set(id, (useCount.get(id) || 0) + 1)));
  const readable = (ids) => [...ids]
    .map((id) => nodeMap().get(id))
    .filter((node) => node && (isMathematicalNode(node) || isReaderFacingStructure(node)))
    .sort((left, right) => readingPriority(right) - readingPriority(left) || displayLabelFor(left).localeCompare(displayLabelFor(right)));
  return {
    shared: readable([...useCount].filter(([, count]) => count === proofs.length).map(([id]) => id)),
    routes: proofs.map((proof) => ({
      proof,
      routeOnly: readable([...(dependencies.get(proof.id) || [])].filter((id) => useCount.get(id) === 1)),
    })),
  };
}

function mathematicalPrerequisites(nodeId, proofId, limit = 7) {
  if (!nodeId || !state.graph) return [];
  const map = nodeMap();
  const incoming = new Map();
  proofRouteEdges(
    state.graph.edges.filter((edge) => edge.relation === "used-in-proof"),
    nodeId,
    proofId,
  ).forEach((edge) => {
    if (!incoming.has(edge.target.id)) incoming.set(edge.target.id, []);
    incoming.get(edge.target.id).push(edge.source.id);
  });
  const results = new Map();
  const queue = (incoming.get(nodeId) || []).map((id) => ({ id, through: 0, distance: 1 }));
  const seen = new Set([nodeId]);
  while (queue.length) {
    const current = queue.shift();
    if (seen.has(current.id)) continue;
    seen.add(current.id);
    const candidate = map.get(current.id);
    if (!candidate) continue;
    const meaningful = isMathematicalNode(candidate) || isMathematicalFoundation(candidate) ||
      (current.distance === 1 && isReaderFacingStructure(candidate));
    if (meaningful) {
      const previous = results.get(candidate.id);
      if (!previous || current.through < previous.through) results.set(candidate.id, { ...current, node: candidate });
      continue;
    }
    (incoming.get(current.id) || []).forEach((sourceId) => queue.push({
      id: sourceId,
      through: current.through + 1,
      distance: current.distance + 1,
    }));
  }
  return [...results.values()]
    .sort((left, right) => readingPriority(right.node) - readingPriority(left.node) || left.through - right.through || displayLabelFor(left.node).localeCompare(displayLabelFor(right.node)))
    .slice(0, limit);
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
  // Inspecting a prerequisite should not silently change the selected proof
  // route of the focused theorem. A new focus (search, theorem picker, or an
  // unfocused graph click) starts in the all-routes view instead.
  if (!hadFocus) state.selectedProofId = null;
  renderInspector();
  updateWorkspaceContext();
  if (redraw || !hadFocus) draw();
  else updateHighlight();
}

function selectProof(proofId) {
  state.selectedProofId = proofId;
  const focus = state.focusId && nodeMap().get(state.focusId);
  const proof = focus && (focus.proofs || []).find((item) => item.id === proofId);
  if (proof) {
    const next = new URL(window.location.href);
    next.searchParams.set("declaration", focus.namespace || focus.id);
    next.searchParams.set("route", proof.declaration);
    history.replaceState(null, "", next);
  }
  renderInspector();
  // A route has a different upstream closure. Rebuild the progressive
  // neighborhood from the selected proof rather than retaining reveal steps
  // calculated for the previous, merged view.
  if (state.focusId) beginProgressiveReveal();
  else draw();
}

function selectAllProofs() {
  state.selectedProofId = null;
  const next = new URL(window.location.href);
  next.searchParams.delete("route");
  history.replaceState(null, "", next);
  renderInspector();
  if (state.focusId) beginProgressiveReveal();
  else draw();
}

function expandNodeDependencies(nodeId, redraw = true) {
  const node = nodeMap().get(nodeId);
  if (!node) return;
  if (Number.isFinite(node.x) && Number.isFinite(node.y)) {
    state.inspectionAnchor = { id: nodeId, x: node.x, y: node.y };
  }
  // Focus slices deliberately stop after a few upstream generations. At that
  // boundary, preserve the reader's selected node and promote to the full
  // declaration graph rather than implying it has no further prerequisites.
  if (state.graphPartial && (state.graph.partialBoundaryNodes || []).includes(nodeId)) {
    ensureGraph().then(() => expandNodeDependencies(nodeId, redraw));
    return true;
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
  state.rankTransition = Number.isFinite(node.x) && Number.isFinite(node.y)
    ? { id: nodeId, x: node.x, y: node.y }
    : null;
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
  if (state.graphPartial && (state.graph.partialBoundaryNodes || []).includes(nodeId)) return true;
  const visibleIds = new Set(visibleNodes.map((node) => node.id));
  return state.graph.edges.some((edge) => edge.relation === "used-in-proof" && edge.target.id === nodeId &&
    !visibleIds.has(edge.source.id) && state.kinds.has(declarationKindFor(nodeMap().get(edge.source.id))));
}

function renderInspector() {
  const content = $("#inspector-content");
  const node = nodeMap().get(state.selectedId);
  if (!node) {
    state.sourceRequest += 1;
    const comparisons = state.comparisons
      .filter((comparison) => comparison.title)
      .sort((left, right) => left.title.localeCompare(right.title));
    const comparisonCard = (comparison) => {
      const routes = comparison.routes || [];
      const exactMerge = !comparison.alignment && routes.length > 1;
      const alignment = comparison.alignment === "foundation-aligned"
        ? "foundation-aligned"
        : comparison.alignment === "presentation"
          ? "checked presentation"
          : exactMerge
            ? `${routes.length} exact proof routes`
            : "checked concrete benchmark";
      const verification = comparison.alignment === "foundation-aligned"
        ? "✓ routes Lean-checked · bridge pending"
        : comparison.alignment === "presentation"
          ? "✓ Lean-checked route"
          : exactMerge
            ? `✓ Lean exact merge · ${routes.length} routes`
            : "✓ Lean-checked benchmark";
      const repositories = [...new Set(routes.map((route) => route.repository))];
      const href = `?comparison=${encodeURIComponent(comparison.id)}`;
      return `<a class="comparison-overview-card" href="${escapeHtml(href)}"><span class="comparison-overview-title">${escapeHtml(comparison.title)}</span><span class="comparison-overview-description">${escapeHtml(comparison.description || comparison.note || "")}</span><span class="comparison-overview-meta comparison-repositories">${repositories.map((repository) => `<span class="proof-color" style="background:${escapeHtml(repositoryColor(repository))}"></span>${escapeHtml((REPOSITORIES[repository] || REPOSITORIES.unknown).label)}`).join(" ")} · ${escapeHtml(alignment)}</span><span class="comparison-overview-verification">${escapeHtml(verification)}</span></a>`;
    };
    const overviewGroups = [
      ["exact", "Exact merged propositions", "Lean has checked that the route statements are definitionally identical."],
      ["benchmark", "Concrete checked benchmarks", "A fully checked low-level problem with one current route; its comparison belongs upstream or remains to be added."],
      ["foundation-aligned", "Foundation-aligned routes", "The mathematical target is aligned, but a representation bridge is still explicit."],
      ["presentation", "Checked applications", "One complete route is ready for inspection and for a future comparison."],
    ].map(([alignment, title, description]) => ({ alignment, title, description,
      nodes: comparisons.filter((comparison) => alignment === "benchmark"
        ? !comparison.alignment && comparison.routes?.length <= 1
        : alignment === "exact"
          ? !comparison.alignment && comparison.routes?.length > 1
          : comparison.alignment === alignment) }))
      .filter((group) => group.nodes.length);
    const groupedCards = (group) => {
      if (group.alignment !== "presentation") return `<div class="comparison-overview-list">${group.nodes.map(comparisonCard).join("")}</div>`;
      const areas = new Map();
      group.nodes.forEach((comparison) => {
        const area = comparison.area || "General mathematics";
        if (!areas.has(area)) areas.set(area, []);
        areas.get(area).push(comparison);
      });
      return [...areas.entries()]
        .sort(([left], [right]) => left.localeCompare(right))
        .map(([area, nodes]) => `<section class="comparison-area-group"><h4>${escapeHtml(area)}</h4><div class="comparison-overview-list">${nodes.map(comparisonCard).join("")}</div></section>`)
        .join("");
    };
    const overview = comparisons.length
      ? `<div class="comparison-overview"><div class="detail-label">Proof landscapes</div><p>Browse exact proof comparisons, explicit foundation boundaries, and single checked applications that are ready for a future comparison.</p>${overviewGroups.map((group) => `<section class="comparison-overview-group"><h3>${escapeHtml(group.title)}</h3><p>${escapeHtml(group.description)}</p>${groupedCards(group)}</section>`).join("")}</div>`
      : "";
    const readerGuide = `<section class="reader-guide"><div class="detail-label">How to read a proof landscape</div><ol><li>Choose a concrete problem or comparison. The selected result stays low in the graph.</li><li>Read upward: every arrow means the upper declaration is <em>used in the Lean proof</em> of the lower one.</li><li>Colors identify the repository supplying a proof route. Select a route to see its own mathematical prerequisites.</li><li>Click any node for its checked statement and source; gold-outlined squares are familiar mathematical foundations, while faded nodes are formal plumbing.</li></ol></section>`;
    content.innerHTML = `<div class="empty-inspector"><div class="empty-glyph">◎</div><p>Select a declaration to inspect its Lean statement, verification status, and proof dependencies.</p>${readerGuide}${overview}</div>`;
    return;
  }
  const sourceRequest = ++state.sourceRequest;
  const neighbors = nodeNeighbors(node.id);
  const github = githubUrlFor(node);
  const focusedTheorem = state.focusId ? nodeMap().get(state.focusId) : null;
  const focusedRoute = focusedTheorem && (focusedTheorem.proofs || []).find((proof) => proof.id === state.selectedProofId);
  const proofList = node.proofs || [];
  const independentProofs = proofList.filter((proof) => proof.proofKind !== "delegation");
  const comparison = comparisonRecordForNode(node);
  const hasProofComparison = Boolean(comparison);
  const isCheckedPresentation = comparison?.alignment === "presentation";
  const isExactComparison = comparison?.alignment === "exact";
  // A checked alias is navigable provenance, but it does not contribute a
  // proof branch or a mathematical difference between routes.
  const proofDependencies = proofDependencySummaries(node.id, independentProofs);
  const proofDifference = proofDependencyDifference(node.id, independentProofs);
  const delegations = new Map();
  (node.proofDelegations || []).forEach((delegation) => {
    if (!delegations.has(delegation.proof)) delegations.set(delegation.proof, []);
    delegations.get(delegation.proof).push(delegation);
  });
  const selectedProof = (node.proofs || []).find((item) => item.id === state.selectedProofId) || null;
  // For a theorem with aliases, the theorem body is the natural statement and
  // source to show first. An adapter remains inspectable below, but does not
  // displace the underlying proof as the reader's starting point.
  const activeProof = selectedProof || (!hasProofComparison || isCheckedPresentation
    ? (independentProofs[0] || proofList[0] || null)
    : (proofList.length === 1 ? proofList[0] : null));
  const routePrerequisites = activeProof ? mathematicalPrerequisites(node.id, activeProof.id) : [];
  const routePrerequisiteNote = routePrerequisites.length
    ? `<div class="detail-block mathematical-prerequisites"><div class="detail-label">Mathematical prerequisites in this route</div><p>Nearest named results on actual Lean proof-use paths. Compiler and representation details are folded, never removed.</p><div class="tag-list">${routePrerequisites.map(({ node: prerequisite, through }) => `<button class="neighbor" data-neighbor="${escapeHtml(prerequisite.id)}">${escapeHtml(labelFor(prerequisite, state.graph.nodes))}${through ? ` <small>through ${through} formal detail${through === 1 ? "" : "s"}</small>` : ""}</button>`).join("")}</div></div>`
    : proofList.length > 1
      ? `<div class="detail-block mathematical-prerequisites"><div class="detail-label">Mathematical prerequisites</div><p>Select a colored proof route above to see its nearest named prerequisites. The displayed graph can still show all routes together.</p></div>`
      : "";
  const formalizations = (node.formalizations || []).map((item) => {
    const file = item.file ? `<br><span>${escapeHtml(item.file)}${item.anchor ? ` · ${escapeHtml(item.anchor)}` : ""}</span>` : "";
    const github = githubUrlFor(node, item);
    const link = github ? ` <a href="${escapeHtml(github)}" target="_blank" rel="noreferrer">GitHub ↗</a>` : "";
    return `<div class="formalization">${escapeHtml(item.language)} · ${escapeHtml(item.name)}${link}${file}</div>`;
  }).join("");
  const tags = (node.tags || []).map((tag) => `<span class="tag">${escapeHtml(tag)}</span>`).join("");
  const routes = node.assumptions ? node.assumptions.map((item) => `<span class="tag">${escapeHtml(item)}</span>`).join("") : "";
  const mergeNote = node.declarationCount > 1 && node.comparison?.alignment !== "foundation-aligned" && !isCheckedPresentation
    ? `<div class="detail-block"><div class="detail-label">Merged proposition</div><p>Exact checked statement shared by ${node.declarationCount} declarations.${hasProofComparison ? " The independent proof bodies below remain separate routes." : " Some declarations are checked aliases of another theorem; they are retained as provenance, not counted as alternative proofs."}</p></div>`
    : "";
  const comparisonId = comparison?.registry || comparison?.id;
  const readerStatement = comparisonId && state.readerStatements[comparisonId];
  const readerTitle = comparison?.title && comparison.title !== displayLabelFor(node)
    ? `<p class="reader-title">${escapeHtml(comparison.title)}</p>`
    : "";
  const readerStatementPanel = readerStatement?.statement
    ? `<div class="detail-block reader-statement"><div class="detail-label">Mathematical statement</div><p>${escapeHtml(readerStatement.statement)}</p><p class="muted-note">Reader-oriented summary; the checked Lean statement follows.</p></div>`
    : "";
  const proofIdeaPanel = activeProof?.routeDescription
    ? `<div class="detail-block proof-idea"><div class="detail-label">Proof idea · ${escapeHtml((REPOSITORIES[repositoryForProof(activeProof)] || REPOSITORIES.unknown).label)}${activeProof.routeTitle ? ` · ${escapeHtml(activeProof.routeTitle)}` : ""}</div><p>${escapeHtml(activeProof.routeDescription)}</p><p class="muted-note">Curated route description; the dependency graph and checked Lean source below record its formal realization.</p></div>`
    : proofList.length > 1
      ? `<div class="detail-block proof-idea"><div class="detail-label">Proof ideas</div><p>Select a colored proof route to read its mathematical strategy and inspect its own prerequisites.</p></div>`
      : "";
  const comparisonIdentity = comparison?.identity || (comparison?.alignment === "foundation-aligned"
    ? "The mathematical target is aligned across two distinct formal foundations"
    : comparison?.alignment === "presentation"
      ? "A checked application retained as a future comparison target"
      : proofList.length > 1
        ? "The independent routes are checked against one identical Lean proposition"
        : "A checked concrete benchmark");
  const allRouteStatement = !activeProof && hasProofComparison && proofList.length > 1
    ? comparison?.alignment === "foundation-aligned"
      ? `<div class="comparison-statements">${proofList.map((proof) => `<div class="comparison-statement"><div class="comparison-statement-label"><span class="proof-color" style="background:${escapeHtml(repositoryColor(repositoryForProof(proof)))}"></span>${escapeHtml((REPOSITORIES[repositoryForProof(proof)] || REPOSITORIES.unknown).label)} route</div><pre class="proof-source pending" data-route-statement="${escapeHtml(proof.id)}"><code>Loading Lean declaration…</code></pre></div>`).join("")}</div>`
      : `<pre class="proof-source pending" data-route-statement="${escapeHtml(proofList[0].id)}"><code>Loading Lean declaration…</code></pre>`
    : null;
  const formalStatementHeading = activeProof
    ? `Formal statement · ${escapeHtml((REPOSITORIES[repositoryForProof(activeProof)] || REPOSITORIES.unknown).label)} route`
    : comparison?.alignment === "foundation-aligned"
      ? "Route statements · foundation-aligned, not definitionally identical"
      : hasProofComparison && proofList.length > 1
        ? "Shared formal statement · exact checked merge"
        : "Formal statement";
  const routeContext = focusedTheorem && focusedRoute && node.id !== focusedTheorem.id
    ? `<div class="route-context"><span class="proof-color" style="background:${escapeHtml(repositoryColor(repositoryForProof(focusedRoute)))}"></span><span>Viewing a dependency of <button class="route-context-theorem" data-neighbor="${escapeHtml(focusedTheorem.id)}">${escapeHtml(displayLabelFor(focusedTheorem))}</button> via <strong>${escapeHtml(focusedRoute.label)}</strong>.</span></div>`
    : "";
  const focusedGraphNote = state.graphPartial
    ? `<div class="detail-block"><div class="detail-label">Focused dependency slice</div><p>This initial view is an adaptive mathematical neighborhood: it follows actual Lean proof-use dependencies beyond structures, while reserving space for substantive declarations rather than stopping after a fixed number of generations.${(state.graph.partialBoundaryNodes || []).includes(node.id) ? " This declaration has additional indexed prerequisites; use its + marker or double-click it to load the complete landscape." : " Expand a boundary declaration to continue into the complete landscape."}</p></div>`
    : "";
  const comparisonNote = comparison
    ? `<div class="detail-block comparison-block"><div class="detail-label">${comparison.alignment === "foundation-aligned" ? "Foundation-aligned comparison" : comparison.alignment === "presentation" ? "Checked presentation" : "Checked comparison"}</div>${comparison.title ? `<h3 class="comparison-title">${escapeHtml(comparison.title)}</h3>` : ""}${comparison.description ? `<p>${escapeHtml(comparison.description)}</p>` : ""}<p class="muted-note">${escapeHtml(comparisonIdentity)}.${comparison.alignment === "foundation-aligned" ? " The colored routes remain distinct Lean declarations; their dependencies expose the two foundations rather than claiming definitional equality." : comparison.alignment === "presentation" ? " This is one fully checked route, retained as an application and a future comparison target; it makes no claim of a second route." : " The routes below are proof terms for this one proposition; their dependency edges can therefore meet at this node."}</p>${comparison.kernelCheck ? `<p class="muted-note">${escapeHtml(comparison.kernelCheck)}</p>` : ""}${comparison.routeAudit ? `<p class="muted-note">${escapeHtml(comparison.routeAudit)}</p>` : ""}${comparison.note ? `<p class="muted-note">${escapeHtml(comparison.note)}</p>` : ""}${(comparison.externalRoutes || []).length ? `<div class="external-route-list"><div class="detail-label">Related external routes · not merged</div>${comparison.externalRoutes.map((route) => `<div class="external-route"><span class="proof-color" style="background:${escapeHtml(repositoryColor(route.repository))}"></span><span><a href="${escapeHtml(route.sourceUrl)}" target="_blank" rel="noreferrer">${escapeHtml(route.repository)} · ${escapeHtml(route.title)} ↗</a><small>${escapeHtml(route.status)} · ${escapeHtml(route.declaration)}</small><small>${escapeHtml(route.description)}</small></span></div>`).join("")}</div>` : ""}${comparison.registry ? `<div class="comparison-registry">Registry: <code>${escapeHtml(comparison.registry)}</code></div>` : ""}</div>`
    : "";
  const foundationAnchors = (comparison?.foundations || []).map((foundation) => {
    const anchor = state.graph.nodes.find((item) => item.namespace === foundation.declaration);
    const name = anchor ? displayLabelFor(anchor) : foundation.declaration;
    return `<button class="neighbor" data-neighbor="${escapeHtml(anchor?.id || "")}"><span class="proof-color" style="background:${escapeHtml(repositoryColor(foundation.repository))}"></span>${escapeHtml((REPOSITORIES[foundation.repository] || REPOSITORIES.unknown).label)} · ${escapeHtml(name)}</button>`;
  }).join("");
  const mathematicalCore = comparison?.mathematicalCore;
  const mathematicalCoreNode = mathematicalCore && state.graph.nodes.find((item) => item.namespace === mathematicalCore);
  const mathematicalCoreAnchor = mathematicalCoreNode
    ? `<div class="detail-block"><div class="detail-label">Shared rational core</div><div class="tag-list"><button class="neighbor" data-neighbor="${escapeHtml(mathematicalCoreNode.id)}">${escapeHtml(displayLabelFor(mathematicalCoreNode))}</button></div></div>`
    : "";
  const depthNote = Number.isInteger(node.dependencyDepth)
    ? `<div class="detail-block"><div class="detail-label">Dependency layer</div><p>Imported declaration · layer ${node.dependencyDepth}.${node.dependencyBoundary ? " Expansion stops at this boundary; use the + marker or double-click to inspect its indexed dependencies." : ""}</p></div>`
    : "";
  const structureNote = isStructureNode(node)
    ? `<div class="detail-block structure-note"><div class="detail-label">Lean declaration kind</div><p>This is a Lean <code>structure</code> (kernel representation: an inductive declaration). That technical kind is separate from its mathematical role below.</p></div>`
    : "";
  const importance = node.importance
    ? `<div class="detail-block"><div class="detail-label">Structural importance</div><p><strong>${escapeHtml(node.importance.score)}</strong>/100 · ${escapeHtml(node.importance.directUses)} direct proof uses · ${escapeHtml(node.importance.downstreamNodes)} downstream declarations.</p><p class="muted-note">Heuristic based on reuse and downstream reach, not proof length. ${escapeHtml(node.importance.landmark ? "Marked as a structural landmark." : "Not currently marked as a landmark.")}</p></div>`
    : "";
  const presentation = node.presentation
    ? `<div class="detail-block"><div class="detail-label">Graph role</div><p><strong>${escapeHtml(node.presentation.category)}</strong> · ${escapeHtml(node.presentation.reason)}</p><p class="muted-note">Presentation heuristic, not a logical distinction in Lean.</p></div>`
    : "";
  const semanticRole = node.mathematicalRole
    ? `<div class="detail-block"><div class="detail-label">Mathematical role</div><p><strong>${escapeHtml(node.mathematicalRole.label || node.mathematicalRole.category)}</strong> · ${escapeHtml(node.mathematicalRole.reason)}</p><p class="muted-note">${escapeHtml(node.mathematicalRole.source)}. ${isMathematicalFoundation(node) ? "The default view stops here; use the + marker or double-click to inspect its formal construction." : "This classification affects presentation, never Lean checking."}</p></div>`
    : "";
  const allProofsControl = isExactComparison && proofList.length > 1
    ? `<button class="proof-all ${state.selectedProofId ? "" : "selected"}" data-all-proofs><span class="proof-all-glyph">◎</span>All proof routes <small>merged comparison</small></button>`
    : "";
  const proofs = proofList.map((proof) => {
    const summary = proofDependencies.get(proof.id);
    const delegated = (delegations.get(proof.id) || []).map((delegation) => delegation.declaration).join(", ");
    const proofRepository = repositoryForProof(proof);
    const proofRepositoryLabel = (REPOSITORIES[proofRepository] || REPOSITORIES.unknown).label;
    const declarationName = String(proof.declaration || proof.label || "").split(".").pop();
    const routeLabel = delegated
      ? `${proofRepositoryLabel} · adapter`
      : `${proofRepositoryLabel} · ${proof.routeTitle || declarationName}`;
    const routeKind = proof.proofKind === "delegation"
      ? "checked adapter"
      : proof.proofKind === "computation"
        ? "kernel-reduced calculation"
        : proof.repository
        ? proofRepositoryLabel
        : (ROUTE_KIND_LABELS[proof.routeKind] || proof.routeKind);
    const directInputs = summary && isExactComparison
      ? proof.proofKind === "computation"
        ? `<small class="proof-dependency-summary">0 named direct inputs · kernel reduction</small>`
        : `<small class="proof-dependency-summary">${summary.total} direct inputs · ${summary.routeOnly} route-only · ${summary.shared} shared</small>`
      : "";
    const auditNote = proof.audit?.nativeDecide
      ? `<small class="proof-audit computational">sorry-free · uses native_decide computation</small>`
      : proof.audit?.sorryFree
        ? `<small class="proof-audit">sorry-free route</small>`
        : "";
    const delegationNote = delegated ? `<small class="proof-delegation">delegates to ${escapeHtml(delegated)}</small>` : "";
    const methodDescription = proof.routeDescription ? `<small class="proof-method">${escapeHtml(proof.routeDescription)}</small>` : "";
    const leanDeclaration = proof.routeTitle ? `<small class="proof-declaration">Lean · ${escapeHtml(declarationName)}</small>` : "";
    return `<div class="proof-row ${state.selectedProofId === proof.id ? "selected" : ""}"><button class="proof-select" data-proof="${escapeHtml(proof.id)}"><span class="proof-color" style="background:${escapeHtml(repositoryColor(proofRepository))}"></span><span>${escapeHtml(routeLabel)}${routeKind ? `<small>${escapeHtml(routeKind)}</small>` : ""}${leanDeclaration}${methodDescription}${directInputs}${auditNote}${delegationNote}</span></button><span class="proof-status">${escapeHtml(proof.status || "planned")}</span></div>`;
  }).join("");
  const dependencyButtons = (nodes) => {
    const shown = nodes.slice(0, 5);
    const more = nodes.length > shown.length ? `<span class="route-more">+${nodes.length - shown.length} more</span>` : "";
    return `${shown.map((dependency) => `<button class="neighbor" data-neighbor="${escapeHtml(dependency.id)}">${escapeHtml(displayLabelFor(dependency))}</button>`).join("")}${more}`;
  };
  const routeDifference = isExactComparison && proofDifference && proofList.length > 1 &&
    (proofDifference.shared.length || proofDifference.routes.some((route) => route.routeOnly.length))
    ? `<div class="detail-block route-difference"><div class="detail-label">Where proof routes diverge · direct mathematical inputs</div>${proofDifference.shared.length ? `<div class="route-difference-row"><span class="route-difference-name">Shared</span><div class="tag-list">${dependencyButtons(proofDifference.shared)}</div></div>` : ""}${proofDifference.routes.map(({ proof, routeOnly }) => routeOnly.length ? `<div class="route-difference-row"><span class="route-difference-name"><span class="proof-color" style="background:${escapeHtml(repositoryColor(repositoryForProof(proof)))}"></span>${escapeHtml((REPOSITORIES[repositoryForProof(proof)] || REPOSITORIES.unknown).label)} only</span><div class="tag-list">${dependencyButtons(routeOnly)}</div></div>` : "").join("")}</div>`
    : "";
  const proofSources = (node.proofs || []).map((proof) => {
    const proofGithub = githubUrlFor(node, proof);
    const sourceLink = proofGithub
      ? ` <a class="source-route-link" href="${escapeHtml(proofGithub)}" target="_blank" rel="noreferrer">Open on GitHub ↗</a>`
      : "";
    return `<div class="detail-block proof-source-route"><div class="detail-label"><span class="proof-color" style="background:${escapeHtml(repositoryColor(repositoryForProof(proof)))}"></span>${escapeHtml((REPOSITORIES[repositoryForProof(proof)] || REPOSITORIES.unknown).label)} · ${escapeHtml(proof.declaration)}${sourceLink}</div><pre class="proof-source pending" data-proof-source="${escapeHtml(proof.id)}"><code>Loading declaration…</code></pre></div>`;
  }).join("");
  const incoming = neighbors.filter(({ direction }) => direction === "in");
  const outgoing = neighbors.filter(({ direction }) => direction === "out");
  const relationRows = (entries, label) => entries.length
    ? `<div class="detail-label">${label} · ${entries.length}</div>${entries.map(({ node: neighbor, proofs: proofIds }) => `<div class="relation-row"><span class="relation-name">${proofIds.length > 1 ? `${proofIds.length} proof routes` : "direct use"}</span><button class="neighbor" data-neighbor="${escapeHtml(neighbor.id)}">${escapeHtml(displayLabelFor(neighbor))}</button></div>`).join("")}`
    : "";
  const neighborRows = [
    relationRows(incoming, "Direct proof dependencies"),
    relationRows(outgoing, "Used by direct proof targets"),
  ].join("");
  const provenance = [
    structureNote,
    semanticRole,
    depthNote,
    presentation,
    importance,
    node.verification?.note ? `<div class="detail-block"><div class="detail-label">Verification note</div><p>${escapeHtml(node.verification.note)}</p></div>` : "",
    formalizations ? `<div class="detail-block"><div class="detail-label">Formalization</div>${formalizations}</div>` : "",
    github && !formalizations ? `<div class="detail-block"><div class="detail-label">Source</div><div class="formalization"><a href="${escapeHtml(github)}" target="_blank" rel="noreferrer">Open declaration on GitHub ↗</a></div></div>` : "",
  ].join("");
  content.innerHTML = `
    <span class="node-kind ${escapeHtml(declarationClassFor(node))}" style="color:${escapeHtml(declarationColorFor(node))};background:${escapeHtml(declarationBackgroundFor(node))}">${escapeHtml(declarationKindFor(node))}</span>
    <div class="verification-badge ${verificationFor(node).className}"><span>${verificationFor(node).glyph}</span>${verificationText(node)}</div>
    <h2>${escapeHtml(displayLabelFor(node))}</h2>
    ${readerTitle}
    ${routeContext}
    ${focusedGraphNote}
    ${readerStatementPanel}
    ${proofIdeaPanel}
    <div class="detail-block declaration-signature"><div class="detail-label">${formalStatementHeading}</div>${allRouteStatement || `<pre class="proof-source pending" id="declaration-signature"><code>Loading Lean declaration…</code></pre>`}</div>
    ${mergeNote}${comparisonNote}
    ${node.method && node.statement ? `<div class="detail-block"><div class="detail-label">Method</div><p>${escapeHtml(node.method)}</p></div>` : ""}
    ${tags ? `<div class="detail-block"><div class="detail-label">Tags</div><div class="tag-list">${tags}</div></div>` : ""}
    ${routes ? `<div class="detail-block"><div class="detail-label">Assumptions</div><div class="tag-list">${routes}</div></div>` : ""}
    ${proofs ? `<div class="detail-block"><div class="detail-label">${isCheckedPresentation ? "Checked Lean route and adapter" : hasProofComparison ? "Proof routes and checked aliases · select a route to filter dependencies" : "Lean declarations and checked aliases"}</div><div class="proof-list">${allProofsControl}${proofs}</div></div>` : ""}
    ${routeDifference}
    ${routePrerequisiteNote}
    ${mathematicalCoreAnchor}
    ${foundationAnchors ? `<div class="detail-block"><div class="detail-label">Native real foundations</div><div class="tag-list">${foundationAnchors}</div></div>` : ""}
    ${proofSources || `<div class="detail-block"><div class="detail-label">Lean proof source</div><pre class="proof-source pending" id="proof-source"><code>Loading declaration…</code></pre></div>`}
    ${neighborRows ? `<div class="detail-block"><div class="neighbor-list">${neighborRows}</div></div>` : ""}
    ${provenance ? `<details class="provenance"><summary>Checked provenance and formalization</summary><div class="provenance-content">${provenance}</div></details>` : ""}
  `;
  content.querySelectorAll("[data-neighbor]").forEach((button) => button.addEventListener("click", () => selectNode(button.dataset.neighbor)));
  content.querySelectorAll("[data-proof]").forEach((button) => button.addEventListener("click", () => selectProof(button.dataset.proof)));
  content.querySelector("[data-all-proofs]")?.addEventListener("click", selectAllProofs);
  if (node.proofs?.length) {
    node.proofs.forEach((proof) => loadProofSource(node, content.querySelector(`[data-proof-source="${proof.id}"]`), sourceRequest, proof));
  } else {
    loadProofSource(node, content.querySelector("#proof-source"), sourceRequest, activeProof);
  }
  if (activeProof) {
    loadDeclarationSignature(node, content.querySelector("#declaration-signature"), sourceRequest, activeProof);
  } else if (allRouteStatement) {
    const statementProofs = comparison?.alignment === "foundation-aligned" ? proofList : proofList.slice(0, 1);
    statementProofs.forEach((proof) => loadDeclarationSignature(node, content.querySelector(`[data-route-statement="${proof.id}"]`), sourceRequest, proof));
  }
}

function updateWorkspaceContext() {
  const context = $("#workspace-context");
  const back = $("#back-to-theorem");
  const copyLink = $("#copy-link");
  if (!context || !back) return;
  const map = nodeMap();
  const focus = state.focusId ? map.get(state.focusId) : null;
  const selected = state.selectedId ? map.get(state.selectedId) : null;
  const focusTitle = comparisonRecordForNode(focus)?.title || focus?.label;
  context.textContent = focus ? `Theorem · ${focusTitle}` : "Choose a theorem to begin";
  const title = $("#network-title");
  if (title) title.textContent = focus ? `${focusTitle} · dependency neighborhood` : "Mathematical landscape";
  back.hidden = !focus || !selected || selected.id === focus.id;
  back.setAttribute("aria-label", focus ? `Return to theorem ${focusTitle}` : "Return to theorem");
  if (copyLink) copyLink.hidden = !focus;
}

function updateHighlight() {
  // visibleGraph has already computed the bounded, upstream dependency
  // neighborhood. Reuse it here so the theorem focus remains stable while a
  // neighboring node is inspected.
  const neighborhood = state.focusId ? new Set(state.focusDistances.keys()) : new Set();
  svg.selectAll(".node-dot").classed("selected", (node) => node.id === state.selectedId).classed("dimmed", (node) => state.focusId && !neighborhood.has(node.id));
  svg.selectAll(".node-structure").classed("selected", (node) => node.id === state.selectedId).classed("dimmed", (node) => state.focusId && !neighborhood.has(node.id));
  svg.selectAll(".node-pie").classed("dimmed", (node) => state.focusId && !neighborhood.has(node.id));
  svg.selectAll(".node-label").classed("dimmed", (node) => state.focusId && !neighborhood.has(node.id));
  svg.selectAll(".graph-link")
    .classed("dimmed", (edge) => state.focusId && (!neighborhood.has(edge.source.id) || !neighborhood.has(edge.target.id)))
    .classed("selected-edge", (edge) => Boolean(state.selectedId) && (edge.source.id === state.selectedId || edge.target.id === state.selectedId));
  const visibleNodes = visibleGraph().nodes;
  svg.selectAll(".node-expand").classed("hidden", (node) => node.id !== state.selectedId || !hasHiddenDependencies(node.id, visibleNodes));
  const focusStatus = $("#focus-status");
  if (focusStatus) {
    const focus = state.focusId ? nodeMap().get(state.focusId) : null;
    const visibleCount = svg.selectAll(".graph-node").size();
    const nextStep = state.revealSteps[state.revealCursor];
    const revealText = state.revealPaused
      ? state.revealPauseReason === "inspection"
        ? "paused while inspecting · click to continue"
        : "paused at viewport edge · click to continue"
      : nextStep
        ? "discovering Lean prerequisites"
        : state.revealCapped
          ? "focused neighborhood capped at 80 nodes"
        : "proof neighborhood loaded";
    focusStatus.textContent = focus
      ? `${visibleCount} shown · ${revealText} · ${focus.label}`
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

function directedLayout(nodes, edges, width, height) {
  // Dagre supplies a deterministic, valid initial ordering. It is then
  // refined by a constrained force pass below, rather than used as the final
  // drawing: that lets nearby branches find a more natural arrangement.
  const graph = new dagre.graphlib.Graph({ multigraph: true });
  graph.setGraph({ rankdir: "TB", ranksep: 58, nodesep: 42, edgesep: 16, marginx: 18, marginy: 24 });
  graph.setDefaultEdgeLabel(() => ({}));
  nodes.forEach((node) => {
    const labelWidth = Math.min(250, Math.max(56, labelFor(node, nodes).length * 6.6 + 32));
    graph.setNode(node.id, { width: labelWidth, height: 30 });
  });
  edges.forEach((edge) => graph.setEdge(edge.source.id, edge.target.id, {}, edge.id));
  dagre.layout(graph);
  const positions = nodes.map((node) => ({ id: node.id, ...graph.node(node.id) }));
  const minX = Math.min(...positions.map((item) => item.x));
  const maxX = Math.max(...positions.map((item) => item.x));
  const minY = Math.min(...positions.map((item) => item.y));
  const maxY = Math.max(...positions.map((item) => item.y));
  // Preserve vertical rank separation independently of width. A uniform
  // scale turns a broad proof graph into a nearly horizontal tangle merely
  // because its labels need several columns; the vertical order is the
  // principal reading structure for this view.
  const scaleX = Math.min(1, (width - 64) / Math.max(1, maxX - minX));
  const scaleY = Math.min(1, (height - 92) / Math.max(1, maxY - minY));
  const offsetX = (width - (maxX - minX) * scaleX) / 2 - minX * scaleX;
  const offsetY = Math.max(32, (height - (maxY - minY) * scaleY) * 0.68) - minY * scaleY;
  positions.forEach((position) => {
    const node = nodes.find((item) => item.id === position.id);
    const pinned = state.pinnedPositions.get(node.id);
    node.x = pinned?.x ?? position.x * scaleX + offsetX;
    node.y = pinned?.y ?? position.y * scaleY + offsetY;
    node.vx = 0;
    node.vy = 0;
    node.targetX = node.x;
    node.targetY = node.y;
    state.layoutPositions.set(node.id, { x: node.x, y: node.y });
    state.layoutVelocities.set(node.id, { x: 0, y: 0 });
  });
}

function theoremLike(node) {
  return node?.kind === "proposition" || ["theorem", "opaque", "axiom", "proposition"].includes(declarationKindFor(node));
}

function semanticTokens(text) {
  const identifiers = String(text || "").match(/[A-Za-z][A-Za-z0-9_'.]*/g) || [];
  const tokens = new Set();
  identifiers.forEach((identifier) => {
    const normalized = identifier.toLowerCase();
    if (normalized.length >= 4 && !normalized.startsWith("inst") && !normalized.includes("hyg")) tokens.add(normalized);
    identifier.replace(/([a-z])([A-Z])/g, "$1 $2").split(/[_.']/).forEach((part) => {
      const word = part.toLowerCase();
      if (word.length >= 4 && !word.startsWith("inst") && !word.includes("hyg")) tokens.add(word);
    });
  });
  return tokens;
}

function theoremTitleForFocus() {
  return state.theorems.find((theorem) => String(theorem.number) === String(state.theoremNumber))?.title || "";
}

function coreNodeFor(nodes) {
  if (!state.focusId) return null;
  const focus = nodes.find((node) => node.id === state.focusId);
  if (!focus) return null;
  const neighborhood = nodes.filter((node) => state.focusDistances.has(node.id) && isMathematicalNode(node));
  // A foundation-aligned comparison may nominate a real-free proposition as
  // its mathematical center. It is checked Lean code, not a synthetic edge;
  // the two implementation-specific criteria remain separate proof routes.
  const declaredCore = neighborhood
    .map((node) => node.comparison?.mathematicalCore)
    .find(Boolean);
  const declaredCoreNode = declaredCore && nodes.find((node) => node.namespace === declaredCore);
  if (declaredCoreNode) return declaredCoreNode.id;
  const tokenFrequency = new Map();
  neighborhood.forEach((node) => semanticTokens(`${node.namespace || ""} ${node.statement || ""}`).forEach((token) => {
    tokenFrequency.set(token, (tokenFrequency.get(token) || 0) + 1);
  }));
  const focusTokens = semanticTokens(`${focus.namespace || ""} ${focus.statement || ""} ${theoremTitleForFocus()}`);
  const candidates = neighborhood.filter((node) => {
    const distance = state.focusDistances.get(node.id);
    return node.id !== state.focusId && isMathematicalNode(node) && theoremLike(node) && distance >= 1 && distance <= 4;
  });
  return candidates.sort((left, right) => {
    const rank = (node) => {
      const tokens = semanticTokens(`${node.namespace || ""} ${node.statement || ""}`);
      const semanticOverlap = [...tokens].filter((token) => focusTokens.has(token)).reduce((total, token) =>
        total + Math.log((neighborhood.length + 1) / ((tokenFrequency.get(token) || 0) + 1)), 0);
      const distance = state.focusDistances.get(node.id) || 0;
      const bridge = /\bIff\b/.test(node.statement || "") && semanticOverlap > 0 ? 18 : 0;
      const directUse = node.importance?.directUses || 0;
      return semanticOverlap * 42 + bridge + Math.log1p(directUse) * 4 + (node.importance?.score || 0) * 0.08 - Math.abs(distance - 2) * 7;
    };
    return rank(right) - rank(left);
  })[0]?.id || null;
}

function straightLinkPath(edge) {
  const offset = edge.parallelOffset || 0;
  const x1 = edge.source.x + offset;
  const y1 = edge.source.y;
  const x2 = edge.target.x + offset;
  const y2 = edge.target.y;
  return `M${x1},${y1} L${x2},${y2}`;
}

function curvedLinkPath(edge) {
  const offset = edge.parallelOffset || 0;
  const x1 = edge.source.x + offset;
  const y1 = edge.source.y;
  const x2 = edge.target.x + offset;
  const y2 = edge.target.y;
  const dy = y2 - y1;
  const handle = Math.max(18, Math.abs(dy) * 0.42) * Math.sign(dy || 1);
  return `M${x1},${y1} C${x1},${y1 + handle} ${x2},${y2 - handle} ${x2},${y2}`;
}

function routedLinkPath(edge, nodes = []) {
  // Deliberately no obstacle-routing detours here. A cubic with endpoint
  // tangents vertical and control points between its endpoint heights is
  // monotone in y, so it crosses each horizontal line at most once.
  return curvedLinkPath(edge);
}

function separateParallelProofEdges(edges) {
  const byEndpoints = d3.group(edges, (edge) => `${edge.source.id}→${edge.target.id}`);
  byEndpoints.forEach((parallel) => {
    const byRepository = d3.group(parallel, (edge) => proofColor(edge.proof));
    const coloredRoutes = [...byRepository.entries()].sort(([left], [right]) => left.localeCompare(right));
    coloredRoutes.forEach(([, routeEdges], index) => {
      const offset = (index - (coloredRoutes.length - 1) / 2) * 8;
      routeEdges.forEach((edge) => { edge.parallelOffset = offset; });
    });
  });
}

function topDownForce(edges, ranks, coreId, gap = 26) {
  const force = () => {
    edges.forEach((edge) => {
      if (edge.source === edge.target) return;
      const overlap = edge.source.y + gap - edge.target.y;
      if (overlap > 0) {
        const shift = overlap * 0.45;
        if (edge.target.id === coreId) edge.source.y -= shift * 2;
        else if (edge.source.id === coreId) edge.target.y += shift * 2;
        else {
          edge.source.y -= shift;
          edge.target.y += shift;
        }
      }
    });
  };
  return force;
}

function enforceTopDown(nodes, edges, ranks, focusId, coreId, gap = 26) {
  const ordered = nodes.slice().sort((a, b) => (ranks.get(a.id) || 0) - (ranks.get(b.id) || 0));
  for (let pass = 0; pass < ordered.length; pass += 1) {
    edges.forEach((edge) => {
      if (edge.source === edge.target) return;
      const overlap = edge.source.y + gap - edge.target.y;
      if (overlap <= 0) return;
      if (edge.target.id === focusId || edge.target.id === coreId) {
        edge.source.y -= overlap;
      } else if (edge.source.id === focusId || edge.source.id === coreId) {
        edge.target.y += overlap;
      } else {
        edge.source.y -= overlap * 0.5;
        edge.target.y += overlap * 0.5;
      }
    });
  }
}

function horizontalLabelCollisionForce(nodes) {
  const active = nodes.filter((node) => isMajorNode(node) && (nodes.length <= 12 || node.label.length <= 31));
  const widthOf = (node) => Math.max(30, labelFor(node, nodes).length * 6.2 + 20);
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
          const direction = left.x <= right.x ? -1 : 1;
          left.x += direction * horizontal * 0.55;
          right.x -= direction * horizontal * 0.55;
        });
        nodes.forEach((right) => {
          if (right === left) return;
          const box = boxOf(left);
          const radius = right.kind === "proof-family" ? 10 : isMajorNode(right) ? 8 : 5;
          const inside = right.x + radius > box.left && right.x - radius < box.right && right.y + radius > box.top && right.y - radius < box.bottom;
          if (inside) left.x += (right.x >= left.x ? -1 : 1) * (radius + 9);
        });
      });
    }
  };
  return force;
}

function structuralRankPositions(nodesByRank, edges, ranks, width, allNodes) {
  // This is the coordinate-assignment half of a Sugiyama-style drawing.
  // Dagre provides the first order, then alternating barycentric sweeps order
  // every rank from its *actual* neighbours.  In particular there is no
  // notion of a repository, a proof family, or a preferred left/right side
  // here: independent proof branches separate because their incidences in
  // the dependency graph are different.
  const neighbours = new Map(allNodes.map((node) => [node.id, []]));
  edges.forEach((edge) => {
    neighbours.get(edge.source.id)?.push(edge.target.id);
    neighbours.get(edge.target.id)?.push(edge.source.id);
  });
  const rankValues = [...nodesByRank.keys()].sort((left, right) => left - right);
  const order = new Map();
  rankValues.forEach((rank) => {
    nodesByRank.get(rank).slice().sort((left, right) =>
      (left.x ?? 0) - (right.x ?? 0) || left.id.localeCompare(right.id),
    ).forEach((node, index) => order.set(node.id, index));
  });
  const rankOf = (id) => ranks.get(id) || 0;
  const barycenter = (node, rank, direction) => {
    const adjacent = (neighbours.get(node.id) || [])
      .filter((id) => direction * (rankOf(id) - rank) > 0)
      .map((id) => order.get(id))
      .filter(Number.isFinite);
    if (!adjacent.length) return null;
    return d3.mean(adjacent);
  };
  // Alternating upward/downward passes substantially reduce crossings while
  // retaining a deterministic answer when two nodes have the same neighbours.
  for (let pass = 0; pass < 6; pass += 1) {
    const direction = pass % 2 === 0 ? -1 : 1;
    const orderedRanks = direction < 0 ? rankValues.slice().reverse() : rankValues;
    orderedRanks.forEach((rank) => {
      const layer = nodesByRank.get(rank);
      layer.sort((left, right) => {
        const leftBarycenter = barycenter(left, rank, direction);
        const rightBarycenter = barycenter(right, rank, direction);
        if (leftBarycenter != null && rightBarycenter != null && leftBarycenter !== rightBarycenter) {
          return leftBarycenter - rightBarycenter;
        }
        if (leftBarycenter != null && rightBarycenter == null) return -1;
        if (rightBarycenter != null && leftBarycenter == null) return 1;
        return (left.x ?? 0) - (right.x ?? 0) || left.id.localeCompare(right.id);
      });
      layer.forEach((node, index) => order.set(node.id, index));
    });
  }
  const positions = new Map();
  rankValues.forEach((rank) => {
    const layer = nodesByRank.get(rank);
    const gaps = 18;
    const widths = layer.map((node) => Math.max(34, Math.min(220, labelFor(node, allNodes).length * 6.4 + 28)));
    const totalWidth = widths.reduce((sum, item) => sum + item, 0) + gaps * Math.max(0, layer.length - 1);
    const scale = totalWidth > width - 44 ? (width - 44) / totalWidth : 1;
    let cursor = (width - totalWidth * scale) / 2;
    layer.forEach((node, index) => {
      const nodeWidth = widths[index] * scale;
      positions.set(node.id, cursor + nodeWidth / 2);
      cursor += nodeWidth + gaps * scale;
    });
  });
  return positions;
}

function proofBranchTargets(nodes, edges, width) {
  // In an all-routes view, proof use itself determines a branch membership:
  // start from each direct dependency edge of the focused proposition and
  // carry that membership upstream. Nodes reached by more than one route are
  // shared and stay in the centre. This is a graph-theoretic layout hint,
  // rather than a repository-specific left/right convention.
  const focus = state.focusId && nodeMap().get(state.focusId);
  const routes = !state.selectedProofId && focus
    ? (focus.proofs || []).filter((proof) => proof.proofKind !== "delegation")
    : [];
  if (routes.length < 2) return new Map();
  const routeIndex = new Map(routes.map((proof, index) => [proof.id, index]));
  const memberships = new Map(nodes.map((node) => [node.id, new Set()]));
  const incoming = new Map();
  edges.forEach((edge) => {
    if (!incoming.has(edge.target.id)) incoming.set(edge.target.id, []);
    incoming.get(edge.target.id).push(edge);
  });
  const queue = [];
  (incoming.get(focus.id) || []).forEach((edge) => {
    const index = routeIndex.get(edge.proof);
    if (index == null) return;
    memberships.get(edge.source.id)?.add(index);
    queue.push([edge.source.id, index]);
  });
  while (queue.length) {
    const [targetId, index] = queue.shift();
    (incoming.get(targetId) || []).forEach((edge) => {
      const membership = memberships.get(edge.source.id);
      if (!membership || membership.has(index)) return;
      membership.add(index);
      queue.push([edge.source.id, index]);
    });
  }
  const targets = new Map();
  const center = width / 2;
  nodes.forEach((node) => {
    const membership = memberships.get(node.id);
    if (!membership?.size || membership.size !== 1) return;
    const [index] = membership;
    // Keep each branch away from the viewport edge, leaving room for Lean
    // labels while visibly separating alternative arguments.
    targets.set(node.id, width * ((index + 1) / (routes.length + 1)));
  });
  targets.set(focus.id, center);
  return targets;
}

function rankLockedLayout(nodes, edges, ranks, width, height, coreId) {
  // `directedLayout` supplies a stable seed before this constrained pass.
  // Later reveal batches retain that seed as a suggestion, but never freeze
  // ordinary declarations horizontally: the graph may still settle into a
  // less crossed and less crowded arrangement.
  const focusRank = ranks.get(state.focusId) || Math.max(0, ...ranks.values());
  // The focused theorem is deliberately placed low in the viewport so its
  // prerequisites read upward.  Compress only as much as necessary to keep
  // the already-selected mathematical spine in view; otherwise a comparison
  // with several genuine intermediate lemmas would begin above the canvas.
  const rankGap = Math.max(24, Math.min(52,
    (height * FOCUS_Y_FRACTION - 42) / Math.max(1, focusRank)));
  const branchTargets = proofBranchTargets(nodes, edges, width);
  nodes.forEach((node) => {
    node.targetX = node.id === coreId || node.id === state.focusId
      ? width / 2
      : branchTargets.get(node.id) ?? node.targetX ?? node.x;
    node.targetY = height * FOCUS_Y_FRACTION - (focusRank - (ranks.get(node.id) || 0)) * rankGap;
    node.rankY = node.targetY;
    node.y = node.rankY;
    node.vx = 0;
    node.vy = 0;
    node.fx = null;
    node.fy = null;
  });
  // Keep the directed-layout seed as the positional suggestion. Dagre's
  // crossing minimisation sees the actual dependency graph; ordinary forces
  // then resolve labels and node collisions without knowing proof identity.
  nodes.forEach((node) => { node.x = node.targetX; });
  // Run forces only within each fixed rank. `fy` prevents the simulation
  // from changing proof height, while charge, link tension, and collision
  // make siblings and neighboring routes separate horizontally.
  nodes.forEach((node) => {
    node.fy = node.rankY;
    const pinned = state.pinnedPositions.get(node.id);
    node.fx = pinned ? pinned.x : node.id === coreId ? width / 2 : null;
  });
  d3.forceSimulation(nodes)
    .force("x", d3.forceX((node) => node.targetX).strength((node) => branchTargets.has(node.id) ? 0.28 : 0.13))
    .force("link", d3.forceLink(edges).id((node) => node.id).distance(92).strength(0.12))
    .force("charge", d3.forceManyBody().strength(-150))
    .force("collide", d3.forceCollide().radius((node) => Math.max(18, Math.min(52, labelFor(node, nodes).length * 3.3 + 14))).strength(0.9))
    .force("labels", horizontalLabelCollisionForce(nodes))
    .stop()
    .tick(120);
  // Collision forces can create a very wide intermediate configuration when
  // one proof route has many more direct inputs than another.  Fit each
  // rank's settled horizontal extent back into the visible stage while
  // preserving its order and relative spacing.  This is a viewport
  // constraint, not a second layout: vertical rank and the branch ordering
  // found above remain unchanged.
  const horizontalMargin = 28;
  const usableWidth = Math.max(1, width - horizontalMargin * 2);
  d3.group(nodes, (node) => node.rankY).forEach((layer) => {
    const halfWidth = (node) => Math.max(16, Math.min(105, labelFor(node, nodes).length * 3.2 + 14));
    const left = Math.min(...layer.map((node) => node.x - halfWidth(node)));
    const right = Math.max(...layer.map((node) => node.x + halfWidth(node)));
    const extent = Math.max(1, right - left);
    if (extent > usableWidth) {
      const scale = usableWidth / extent;
      layer.forEach((node) => { node.x = horizontalMargin + (node.x - left) * scale; });
      return;
    }
    const shift = Math.max(horizontalMargin - left, Math.min(width - horizontalMargin - right, (width - (left + right)) / 2));
    layer.forEach((node) => { node.x += shift; });
  });
  // Do not shift the whole diagram down merely to fit a newly discovered
  // prerequisite layer. The focus theorem is a reading anchor. Layers that
  // would leave the viewport are handled by progressive-reveal pausing,
  // rather than pushing the theorem out of sight.
  nodes.forEach((node) => {
    node.y = node.rankY;
    node.fx = null;
    node.fy = null;
    state.layoutPositions.set(node.id, { x: node.x, y: node.y });
    state.layoutVelocities.set(node.id, { x: 0, y: 0 });
  });
}

function draw() {
  if (!state.graph) return;
  if (state.rankTransitionFrame) {
    cancelAnimationFrame(state.rankTransitionFrame);
    state.rankTransitionFrame = null;
  }
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
  // A node double-click is reserved for dependency expansion, not zooming.
  svg.on("dblclick.zoom", null);
  root.attr("transform", state.zoomTransform);
  const labels = proofLabels();
  // Keep the dependency direction visible in the layout.  Edges point from
  // a used declaration to the declaration whose proof uses it, so repeated
  // relaxation places prerequisites above their proof targets.  Distance
  // from the focus is still used for fading, but no longer flattens peers
  // into one horizontal band.
  const topologyRanks = dependencyRanks(nodes, edges);
  const coreId = state.coreId && nodes.some((node) => node.id === state.coreId) ? state.coreId : coreNodeFor(nodes);
  const ambientIds = ambientNodesForFocus(state.graph.nodes);
  const focusDependencyIds = new Set(edges
    .filter((edge) => edge.target.id === state.focusId)
    .map((edge) => edge.source.id));
  separateParallelProofEdges(edges);
  state.coreId = coreId;
  // Vertical rank is determined *only* by Lean's used-in-proof relation.
  // A former focus-distance adjustment could outweigh a topological rank,
  // making a genuine dependency edge slope upwards.  Discovery distance is
  // useful for fading and progressive reveal, but it must never participate
  // in a directed drawing's vertical constraint.
  const rawRanks = new Map(nodes.map((item) => [item.id, topologyRanks.get(item.id) || 0]));
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
  // Derive a horizontal position from graph incidence, not declaration names
  // or route provenance. This preserves the structure found by Dagre and
  // refines it as further dependency batches are revealed.
  const rankPositions = structuralRankPositions(nodesByRank, edges, ranks, width, nodes);
  nodesByRank.forEach((layer, rank) => layer.forEach((item) => {
    const position = rankPositions.get(item.id) ?? width / 2;
    const targetX = item.id === state.focusId || item.id === coreId
      ? width / 2
      : position;
    const targetY = item.id === coreId
      ? height * 0.5
      : item.id === state.focusId
      ? height * FOCUS_Y_FRACTION
      : graphTop + rank * layerGap;
    const previous = state.layoutPositions.get(item.id);
    if (previous && item.id !== coreId) {
      item.x = previous.x;
      item.y = previous.y;
      const velocity = state.layoutVelocities.get(item.id);
      item.vx = velocity?.x ?? 0;
      item.vy = velocity?.y ?? 0;
      if (item.id === state.focusId && (item.y < 40 || item.y > height - 40)) {
        item.x = width / 2;
        item.y = height * FOCUS_Y_FRACTION;
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
    if (item.id === coreId) {
      // The core is an orientation point, not merely another particle in the
      // force simulation. Keep it centered until the reader deliberately
      // drags it.
      item.fx = targetX;
      item.fy = targetY;
    }
  }));
  const link = root.append("g").attr("aria-hidden", "true").selectAll("path").data(edges, (edge) => edge.id).join("path")
    .attr("class", "graph-link used-in-proof")
    .classed("implementation-link", (edge) => !isMajorNode(edge.source) && !isMajorNode(edge.target))
    .classed("cycle-link", (edge) => (ranks.get(edge.source.id) || 0) >= (ranks.get(edge.target.id) || 0))
    .classed("focus-edge", (edge) => edge.target.id === state.focusId)
    .attr("stroke", (edge) => proofColor(edge.proof))
    // Arrowheads are reserved for edges touching a major declaration.  The
    // complete edge remains visible, while implementation-level chains do
    // not turn into a field of tiny overlapping triangles.
    .attr("marker-end", (edge) => edge.source.y + 5 < edge.target.y && (isMajorNode(edge.source) || isMajorNode(edge.target)) ? "url(#arrow-used-in-proof)" : null);
  link.append("title").text((edge) => `proof: ${labels.get(edge.proof) || edge.proof || "unknown"}\n${edge.description || "used in proof"}`);
  const node = root.append("g").selectAll("g").data(nodes, (item) => item.id).join("g").attr("role", "button").attr("aria-label", (item) => displayLabelFor(item)).classed("graph-node", true).classed("major-node", (item) => isMajorNode(item)).classed("foundation-node", isMathematicalFoundation).classed("core-node", (item) => item.id === coreId).classed("focus-node", (item) => item.id === state.focusId).classed("ambient-node", (item) => ambientIds.has(item.id)).classed("direct-dependency", (item) => focusDependencyIds.has(item.id)).classed("implementation-node", (item) => presentationCategory(item) === "implementation").classed("landmark-node", (item) => state.showLandmarks && isLandmark(item)).on("click", (event, item) => { event.stopPropagation(); selectNode(item.id); }).on("dblclick", (event, item) => { event.stopPropagation(); if (hasHiddenDependencies(item.id, nodes)) expandNodeDependencies(item.id); }).call(d3.drag().on("start", (event, item) => { state.simulation?.stop(); item.fx = item.x; item.fy = item.rankY ?? item.y; }).on("drag", (event, item) => { item.x = event.x; item.y = item.rankY ?? item.y; item.fx = event.x; item.fy = item.y; node.attr("transform", (candidate) => `translate(${candidate.x},${candidate.y})`); link.attr("d", (edge) => routedLinkPath(edge, nodes)); }).on("end", (event, item) => { item.fx = null; item.fy = null; state.layoutPositions.set(item.id, { x: item.x, y: item.y }); state.pinnedPositions.set(item.id, { x: item.x, y: item.rankY ?? item.y }); if (state.selectedId === item.id) state.inspectionAnchor = { id: item.id, x: item.x, y: item.y }; resumeRevealIfVisible(); }));
  // Lean encodes structures as inductives internally. Their rounded cards
  // mark a representation boundary: they are substantial objects, but their
  // fields and construction details remain collapsed until expanded.
  node.append("rect").attr("class", "node-structure")
    .classed("foundation", isMathematicalFoundation)
    .classed("hidden", (item) => !isStructureNode(item))
    .attr("x", -16).attr("y", -12).attr("width", 32).attr("height", 24).attr("rx", 6)
    .attr("fill", (item) => repositoryColor(repositoriesForNode(item)[0]));
  // A merged declaration can have checked proof terms from more than one
  // repository. Render its disk as a pie, rather than assigning it a fourth
  // misleading color; single-source declarations remain solid repository color.
  node.each(function (item) {
    const repositories = repositoriesForNode(item);
    if (repositories.length < 2) return;
    const radius = nodeRadius(item, coreId, ambientIds);
    d3.select(this).append("g").attr("class", "node-pie").attr("aria-hidden", "true")
      .selectAll("path").data(repositories).join("path")
      .attr("d", (_, index) => pieSlicePath(index, repositories.length, radius))
      .attr("fill", (repository) => repositoryColor(repository));
  });
  node.append("circle").attr("class", "node-dot").classed("structure", isStructureNode).classed("core", (item) => item.id === coreId).classed("focus", (item) => item.id === state.focusId).classed("ambient", (item) => ambientIds.has(item.id)).classed("direct-dependency", (item) => focusDependencyIds.has(item.id)).classed("implementation", (item) => presentationCategory(item) === "implementation").classed("supporting", (item) => presentationCategory(item) === "supporting").classed("landmark", (item) => state.showLandmarks && isLandmark(item)).attr("data-focus-distance", (item) => state.focusDistances.get(item.id) ?? "").attr("r", (item) => nodeRadius(item, coreId, ambientIds)).attr("fill", (item) => {
    const repositories = repositoriesForNode(item);
    return repositories.length === 1 ? repositoryColor(repositories[0]) : "transparent";
  });
  node.append("text").attr("class", "node-label").classed("structure", isStructureNode).classed("core", (item) => item.id === coreId).classed("focus", (item) => item.id === state.focusId).classed("ambient", (item) => ambientIds.has(item.id)).classed("direct-dependency", (item) => focusDependencyIds.has(item.id)).classed("implementation", (item) => presentationCategory(item) === "implementation").classed("supporting", (item) => presentationCategory(item) === "supporting").classed("routine", (item) => presentationCategory(item) === "routine").attr("data-focus-distance", (item) => state.focusDistances.get(item.id) ?? "").attr("x", (item) => isStructureNode(item) ? 22 : 16).attr("y", 4).text((item) => `${verificationFor(item).glyph} ${labelFor(item, nodes)}`).classed("hidden", (item) => (isSuppressedNode(item) && item.id !== state.selectedId && item.id !== state.focusId && !ambientIds.has(item.id)) || (item.id !== coreId && !ambientIds.has(item.id) && labelFor(item, nodes).length > 31 && nodes.length > 12));
  node.append("text").attr("class", "node-route-count")
    .classed("hidden", (item) => !(item.comparison && (item.proofs || []).length > 1))
    .attr("x", (item) => isStructureNode(item) ? 22 : 16).attr("y", 17)
    .text((item) => `${item.proofs?.length || 0} ${item.comparison?.alignment === "foundation-aligned" ? "aligned routes" : "routes"}`);
  const expanders = node.append("g").attr("class", "node-expand").attr("transform", "translate(0,-18)")
    .classed("hidden", (item) => item.id !== state.selectedId || !hasHiddenDependencies(item.id, nodes))
    .attr("role", "button")
    .attr("aria-label", (item) => `Expand dependencies of ${displayLabelFor(item)}`)
    .on("click", (event, item) => { event.stopPropagation(); expandNodeDependencies(item.id); });
  expanders.append("circle").attr("r", 7);
  expanders.append("text").text("+");
  state.simulation?.stop();
  if (state.settleTimer) window.clearTimeout(state.settleTimer);
  state.settleTimer = null;
  state.simulation = null;
  if (state.focusId) {
    // Dagre is useful only for an initial seed. Re-running it for every
    // progressive reveal batch was resetting nodes to a left-biased layout,
    // after which the constrained layout visibly pulled them right again.
    // Settled coordinates are now retained across batches.
    if (!state.layoutPositions.size) directedLayout(nodes, edges, width, height);
    rankLockedLayout(nodes, edges, ranks, width, height, coreId);
    node.attr("transform", (item) => `translate(${item.x},${item.y})`);
    link.attr("d", (edge) => routedLinkPath(edge, nodes))
      .attr("marker-end", (edge) => edge.source.y + 5 < edge.target.y && (isMajorNode(edge.source) || isMajorNode(edge.target)) ? "url(#arrow-used-in-proof)" : null);
    state.rankTransition = null;
    state.rankSettleStarts = null;
    updateHighlight();
    return;
  }
  // The unfocused full landscape remains deliberately loose and exploratory;
  // focused theorem views above use Dagre's strict directed layout.
  const staticLayout = nodes.length > 500;
  if (staticLayout) {
    nodes.forEach((item) => {
      if (state.inspectionAnchor?.id !== item.id) {
        item.x = item.targetX;
        item.y = item.targetY;
      }
    });
    enforceTopDown(nodes, edges, ranks, state.focusId, coreId);
    node.attr("transform", (item) => `translate(${item.x},${item.y})`);
    nodes.forEach((item) => state.layoutPositions.set(item.id, { x: item.x, y: item.y }));
    link.attr("d", (edge) => routedLinkPath(edge, nodes));
  } else {
    state.simulation = d3.forceSimulation(nodes)
      .force("link", d3.forceLink(edges).id((item) => item.id).distance(state.focusId ? 104 : 82).strength(state.focusId ? 0.34 : 0.22))
      .force("y", d3.forceY((item) => item.id === coreId ? height * 0.5 : item.id === state.focusId ? height * FOCUS_Y_FRACTION : graphTop + (ranks.get(item.id) || 0) * layerGap).strength((item) => item.id === state.focusId || item.id === coreId ? 0.92 : state.focusId ? 0.08 : 1.2))
      .force("x", d3.forceX((item) => item.id === state.focusId || item.id === coreId ? width / 2 : item.targetX ?? width / 2).strength((item) => item.id === state.focusId || item.id === coreId ? 0.94 : 0.12))
      .force("charge", d3.forceManyBody().strength(state.focusId ? -230 : -180))
      .force("collide", d3.forceCollide().radius((item) => item.kind === "proof-family" ? 26 : 21))
      .force("labels", horizontalLabelCollisionForce(nodes))
      .force("top-down", topDownForce(edges, ranks, coreId))
      .alpha(0.22)
      .alphaDecay(0.16)
      .velocityDecay(0.72)
      .on("tick", () => {
      enforceTopDown(nodes, edges, ranks, state.focusId, coreId);
      const focusNode = nodes.find((item) => item.id === state.focusId);
      if (focusNode && !Number.isFinite(focusNode.fy)) {
        // The focus is an anchor for the whole progressive layout. Keep it
        // in a safe lower band while the top-down constraint moves its
        // prerequisites above it; otherwise a new frontier can briefly push
        // the theorem below the visible stage.
        focusNode.x = width / 2;
        focusNode.y = Math.max(height * 0.52, Math.min(height * 0.74, focusNode.y));
        focusNode.vx = 0;
        focusNode.vy = 0;
      }
      // Anchoring the selected theorem changes its y-coordinate after the
      // simulation forces have run.  Apply the hard ordering last, so an
      // anchor can never leave an incoming or outgoing proof edge reversed.
      enforceTopDown(nodes, edges, ranks, state.focusId, coreId);
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

async function ensureGraph() {
  if (state.graph && !state.graphPartial) return state.graph;
  if (state.graphPromise) return state.graphPromise;
  state.graphPromise = (async () => {
    const responses = await Promise.all(DATA_URLS.map((url) => fetch(url)));
    const failed = responses.find((response) => !response.ok);
    if (failed) throw new Error(`Could not load ${DATA_URLS.join(", ")}`);
    const graphs = await Promise.all(responses.map((response) => response.json()));
    const graph = graphs.length === 1 ? graphs[0] : {
      schemaVersion: graphs[0].schemaVersion,
      graphId: "math-net-project",
      label: "math-net project: Fermat + Euler applications",
      nodes: graphs.flatMap((graph) => graph.nodes),
      edges: graphs.flatMap((graph) => graph.edges),
    };
    installGraph(graph, "project.json");
    return state.graph;
  })();
  const pending = state.graphPromise;
  try {
    return await pending;
  } finally {
    if (state.graphPromise === pending) state.graphPromise = null;
  }
}

function installGraph(graph, sourceName) {
  state.graph = graph;
  state.graphPartial = Boolean(graph.partial);
  const scope = state.graphPartial ? "focused" : "project";
  $("#graph-badge").textContent = `${graph.nodes.length} nodes · ${graph.edges.length} links · ${scope}`;
  state.kinds = new Set(availableDeclarationKinds());
  $(".data-source code").textContent = sourceName;
  $("#loading-state").remove();
  kindControls();
  renderProofLegend();
}

async function loadComparisonSlice(comparisonId) {
  if (state.graph && state.graphPartial && state.graph.focusComparison === comparisonId) return state.graph;
  if (state.graph && !state.graphPartial) return state.graph;
  if (state.graphPromise) return state.graphPromise;
  state.graphPromise = (async () => {
    const response = await fetch(comparisonSliceUrl(comparisonId));
    if (!response.ok) throw new Error(`Could not load focused graph for ${comparisonId}`);
    const graph = await response.json();
    installGraph(graph, `slices/${comparisonId}.json`);
    return state.graph;
  })();
  const pending = state.graphPromise;
  try {
    return await pending;
  } finally {
    if (state.graphPromise === pending) state.graphPromise = null;
  }
}

async function load() {
  try {
    const [theoremResponse, comparisonResponse, sourceRevisionResponse, readerStatementsResponse] = await Promise.all([
      fetch(THEOREMS_URL),
      fetch(COMPARISONS_URL),
      fetch(SOURCE_REVISIONS_URL),
      fetch(READER_STATEMENTS_URL),
    ]);
    if (theoremResponse.ok) state.theorems = await theoremResponse.json();
    if (comparisonResponse.ok) {
      state.comparisons = (await comparisonResponse.json()).comparisons || [];
      state.comparisonsByDeclaration = new Map(state.comparisons.flatMap((comparison) =>
        (comparison.routes || []).map((route) => [route.declaration, comparison]),
      ));
    }
    if (sourceRevisionResponse.ok) state.sourceRevisions = (await sourceRevisionResponse.json()).repositories || {};
    if (readerStatementsResponse.ok) state.readerStatements = (await readerStatementsResponse.json()).statements || {};
    const exact = state.comparisons.filter((comparison) => !comparison.alignment && comparison.routes?.length > 1).length;
    const aligned = state.comparisons.filter((comparison) => comparison.alignment === "foundation-aligned").length;
    const presentations = state.comparisons.filter((comparison) => comparison.alignment === "presentation" ||
      (!comparison.alignment && comparison.routes?.length <= 1)).length;
    $("#graph-badge").textContent = `${exact} exact · ${aligned} aligned · ${presentations} applications`;
    populateTheoremSelect();
    populateComparisonSelect();
    const needsGraph = Boolean(requestedDeclaration || requestedComparison || state.theoremNumber);
    if (requestedComparison) await loadComparisonSlice(requestedComparison);
    else if (needsGraph) await ensureGraph();
    const declaration = state.graph && ((requestedDeclaration && state.graph.nodes.find((node) => node.namespace === requestedDeclaration || node.id === requestedDeclaration)) ||
      (requestedComparison && comparisonNode(requestedComparison)));
    if (declaration) {
      focusDeclaration(declaration.id);
      const route = requestedRoute && (declaration.proofs || []).find((proof) => proof.declaration === requestedRoute);
      if (route) selectProof(route.id);
    } else if (state.theoremNumber) {
      await selectTheoremNode();
    } else {
      // The landing page is a proof-landscape catalogue, not an invitation
      // to render every imported declaration.  Building the full unfocused
      // graph here made the hosted page appear to hang before a reader could
      // choose a theorem.  A focused selection still renders its actual
      // dependency neighborhood immediately.
      renderInspector();
      $("#loading-state").remove();
      $("#visible-node-count").textContent = "0";
      $("#visible-edge-count").textContent = "0";
    }
    updateWorkspaceContext();
  } catch (error) {
    const loading = $("#loading-state");
    loading.classList.add("error");
    loading.textContent = "The graph could not load. Serve the repository root, then open /web/.";
    console.error(error);
  }
}

$("#search").addEventListener("input", (event) => {
  state.search = event.target.value.trim();
  renderSearchResults();
  if (state.search.length >= 2 && !state.graph) {
    ensureGraph().then(() => renderSearchResults()).catch(() => renderSearchResults());
  }
  if (!state.search && state.graph) draw();
});
$("#search").addEventListener("keydown", (event) => {
  if (event.key === "Escape") {
    event.currentTarget.value = "";
    state.search = "";
    renderSearchResults();
    draw();
  }
  if (event.key === "Enter") {
    const first = $("#search-results [data-search-node]");
    if (first) {
      event.preventDefault();
      focusDeclaration(first.dataset.searchNode);
    }
  }
});
$("#fit-layout").addEventListener("click", () => {
  state.zoomTransform = d3.zoomIdentity;
  state.pinnedPositions.clear();
  state.inspectionAnchor = null;
  draw();
});
$("#reset").addEventListener("click", () => {
  state.selectedId = null;
  state.focusId = null;
  state.selectedProofId = null;
  state.layoutPositions.clear();
  state.layoutVelocities.clear();
  state.pinnedPositions.clear();
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
  $("#search-results").replaceChildren();
  $("#theorem-select").value = "";
  $("#comparison-select").value = "";
  document.querySelectorAll("#kind-filters input[type=checkbox]").forEach((input) => { input.checked = true; });
  state.showImplementation = false;
  state.showSupporting = false;
  state.showLandmarks = true;
  $("#show-implementation").checked = false;
  $("#show-supporting").checked = false;
  $("#show-landmarks").checked = true;
  state.kinds = new Set(availableDeclarationKinds());
  const next = new URL(window.location.href);
  next.searchParams.delete("theorem");
  next.searchParams.delete("graph");
  next.searchParams.delete("declaration");
  next.searchParams.delete("comparison");
  next.searchParams.delete("route");
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
  state.pinnedPositions.clear();
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
  $("#comparison-select").value = "";
  const next = new URL(window.location.href);
  next.searchParams.delete("theorem");
  next.searchParams.delete("declaration");
  next.searchParams.delete("comparison");
  next.searchParams.delete("route");
  history.replaceState(null, "", next);
  updateTheoremNote();
  renderInspector();
  updateWorkspaceContext();
  draw();
});
$("#back-to-theorem").addEventListener("click", () => {
  if (state.focusId) selectNode(state.focusId);
});
$("#copy-link").addEventListener("click", async (event) => {
  const button = event.currentTarget;
  const original = "Copy link";
  try {
    await navigator.clipboard.writeText(window.location.href);
    button.textContent = "Copied";
  } catch (_) {
    button.textContent = "Copy unavailable";
  }
  window.setTimeout(() => { button.textContent = original; }, 1500);
});
$("#show-implementation").addEventListener("change", (event) => { state.showImplementation = event.target.checked; draw(); });
$("#show-supporting").addEventListener("change", (event) => { state.showSupporting = event.target.checked; draw(); });
$("#show-landmarks").addEventListener("change", (event) => { state.showLandmarks = event.target.checked; draw(); });
$("#focus-status").addEventListener("click", () => state.resumeReveal?.());
window.addEventListener("resize", () => draw());
load();
