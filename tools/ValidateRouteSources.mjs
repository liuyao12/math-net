#!/usr/bin/env node
/**
 * Verify that every curated route can display its authored Lean declaration.
 *
 * The browser deliberately shows source code rather than an elaborated type
 * whenever possible.  This script mirrors its source-resolution and
 * declaration-isolation rules against the published source revisions.
 * It is a networked release check, not a replacement for Lean checking.
 */

import fs from "node:fs";

const graph = JSON.parse(fs.readFileSync("MathNetwork/Graph/project.json", "utf8"));
const comparisons = JSON.parse(fs.readFileSync("MathNetwork/Graph/comparisons.json", "utf8")).comparisons || [];
const revisions = JSON.parse(fs.readFileSync("MathNetwork/Graph/source-revisions.json", "utf8")).repositories || {};
const byProof = new Map(graph.nodes.flatMap((node) =>
  (node.proofs || []).map((proof) => [proof.declaration, { node, proof }]),
));

function sourceUrlFor(node, proof) {
  if (proof?.locator?.startsWith("mathlib/")) {
    const file = `${proof.locator.slice("mathlib/".length).replaceAll(".", "/")}.lean`;
    return `https://raw.githubusercontent.com/leanprover-community/mathlib4/${revisions.mathlib?.revision}/${file}`;
  }
  if (proof?.locator?.startsWith("computable-analysis/")) {
    const file = `${proof.locator.slice("computable-analysis/".length).replaceAll(".", "/")}.lean`;
    return `https://raw.githubusercontent.com/liuyao12/computable-analysis/${revisions["computable-analysis"]?.revision}/${file}`;
  }
  const file = proof?.file || (node.formalizations || []).find((item) => item.file)?.file ||
    (node.module?.startsWith("MathNetwork.") ? `${node.module.replaceAll(".", "/")}.lean` : null);
  if (!file) return null;
  if (file.startsWith("MathNetwork/")) return `https://raw.githubusercontent.com/liuyao12/math-net/main/${file}`;
  const locator = proof?.locator || node.locator;
  if (locator?.startsWith("mathlib/")) {
    return `https://raw.githubusercontent.com/leanprover-community/mathlib4/${revisions.mathlib?.revision}/${file}`;
  }
  if (locator?.startsWith("computable-analysis/")) {
    return `https://raw.githubusercontent.com/liuyao12/computable-analysis/${revisions["computable-analysis"]?.revision}/${file}`;
  }
  return `https://raw.githubusercontent.com/liuyao12/math-net/main/${file}`;
}

function containsDeclaration(source, declaration) {
  const short = declaration.split(".").pop().replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const modifiers = "(?:(?:protected|private|noncomputable|unsafe|partial|scoped|local)\\s+)*";
  const kinds = "(?:theorem|lemma|def|abbrev|example|axiom|opaque|instance|class|structure|inductive)";
  return new RegExp(`^\\s*${modifiers}${kinds}\\s+${short}\\b`, "m").test(source);
}

const routes = comparisons.flatMap((comparison) =>
  (comparison.routes || []).map((route) => ({ ...route, comparison: comparison.id })),
);
const failures = [];
let isolated = 0;

for (const route of routes) {
  const record = byProof.get(route.declaration);
  const url = record && sourceUrlFor(record.node, record.proof);
  try {
    const response = url && await fetch(url);
    const source = response?.ok ? await response.text() : "";
    if (response?.ok && containsDeclaration(source, route.declaration)) {
      isolated += 1;
    } else {
      failures.push({ comparison: route.comparison, declaration: route.declaration, status: response?.status || 0, url });
    }
  } catch (error) {
    failures.push({ comparison: route.comparison, declaration: route.declaration, status: String(error), url });
  }
}

if (failures.length) {
  console.error("route-source validation failed:");
  failures.forEach((failure) => console.error(`- ${failure.comparison} · ${failure.declaration} (${failure.status})\n  ${failure.url || "no source locator"}`));
  process.exit(1);
}
console.log(`validated authored source for ${isolated} curated proof routes`);
