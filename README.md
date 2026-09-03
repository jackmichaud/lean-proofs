# Frontier

Frontier is a Lean-checked mathematical research registry and workspace. It records conjectures,
proofs, counterexamples, independence results, and undecidability reductions as reusable research
artifacts. Lean is the verifier; Frontier supplies the catalog, trust audit, dependency graph,
library discovery, and research queue around it.

Every record carries two independent fields: `status`, what *this repository* has kernel-checked,
and `literature`, what *mathematics* knows. Catalan's conjecture is `open` here and `proved` in
the literature — a formalization task, not a research frontier. Collapsing those into one field
is how a registry ends up advertising settled theorems as open problems.

Each result is resolved against the compiled Lean environment, checked for a status-appropriate
certificate, audited against an enforced axiom allowlist, and linked to the catalog results it
reuses.

## Start

```bash
make check
make serve
```

Then open [http://127.0.0.1:4173](http://127.0.0.1:4173). The web workspace includes the theorem
library, proof dependency graph, and a browser-local conjecture queue that exports Lean scaffolds.

`make check` is the full gate and is what CI runs: it builds, audits every entry, verifies the
committed web catalog still matches the registry, and drives the workspace in a real browser.
The browser step skips with a notice if no Chrome DevTools Protocol endpoint is reachable:

```bash
chrome --headless=new --remote-debugging-port=9222
```

## CLI

```bash
lake exe frontier validate
lake exe frontier list fermat
lake exe frontier show catalan-conjecture
lake exe frontier search pow_card
lake exe frontier suggest fermat-zmod
lake exe frontier graph
lake exe frontier policy
lake exe frontier export web/data/catalog.json
```

`search` finds declarations by name across every imported Lean module, ranked exact → final
component → prefix → substring. `suggest` ranks imported theorems by inverse-document-frequency
weighted overlap of the constants in their statements, so a shared `ZMod` outranks a shared `Nat`.
`policy` prints the axiom allowlist and the reason each denied axiom is denied.

## Trust

`frontier validate` enforces an axiom allowlist rather than reporting axioms as a footnote.
`propext`, `Classical.choice`, and `Quot.sound` are accepted; `sorryAx`, `Lean.ofReduceBool`
(`native_decide`), and `Lean.trustCompiler` are rejected, and anything else is an error. Statements
and sanity checks are audited alongside certificates.

Read [docs/architecture.md](docs/architecture.md#what-validation-does-not-establish) for what
validation does *not* establish — faithfulness of the formalization, the substance of a relative
`undecidable`/`independent` classification, vacuity, and novelty are all outside what the kernel
decides.

## Layout

- `Leanproofs/Registry.lean`: statuses, literature states, evidence kinds, registry records.
- `Leanproofs/Catalog.lean`: durable, version-controlled theorem catalog.
- `Leanproofs/CLI.lean`: environment audit, discovery, graph, and JSON export.
- `Leanproofs/Main.lean`: the executable. Thin, and its import list is load-bearing — see the
  module docstring for why the catalog is read out of the environment rather than linked.
- `Leanproofs/Fermat.lean`, `Leanproofs/Catalan.lean`: checked mathematical results.
- `web/`: research workspace and generated catalog data.
- `scripts/`: catalog comparison and browser QA.
- `docs/`: trust model, architecture, and contribution workflow.
- `external/`: git-ignored scratch. **Not compiled and not verified by anything** — a `sorry`
  grep over an unbuilt file proves nothing. Move work into `Leanproofs/` to have it checked.

The project is pinned to Lean and mathlib `v4.33.1`. See
[docs/README.md](docs/README.md) for the documentation index, [docs/adding-results.md](docs/adding-results.md)
before adding a claim, and [docs/architecture.md](docs/architecture.md) for the product and trust
boundaries. The proof-system graph hierarchy is described in [docs/graph-model.md](docs/graph-model.md),
and agent-facing retrieval is outlined in [docs/retrieval-and-agents.md](docs/retrieval-and-agents.md).
