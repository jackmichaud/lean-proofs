# Frontier

Frontier is a Lean-checked mathematical research registry and workspace. It records conjectures,
proofs, counterexamples, independence results, and undecidability reductions as reusable research
artifacts. Lean is the verifier; Frontier supplies the catalog, trust audit, dependency graph,
library discovery, and research queue around it.

The current catalog contains a five-result derivation of Fermat's little theorem. Each result is
resolved against the compiled Lean environment, checked for a status-appropriate certificate,
audited for transitive axioms and `sorryAx`, and linked to the catalog results it reuses.

## Start

```bash
make check
make serve
```

Then open [http://127.0.0.1:4173](http://127.0.0.1:4173). The web workspace includes the theorem
library, proof dependency graph, and a browser-local conjecture queue that exports Lean scaffolds.

## CLI

```bash
lake exe frontier validate
lake exe frontier list fermat
lake exe frontier show fermat-zmod
lake exe frontier search pow_card
lake exe frontier suggest fermat-zmod
lake exe frontier graph
lake exe frontier export web/data/catalog.json
```

`search` finds declarations by name across every imported Lean module. `suggest` ranks imported
theorems by the non-generic constants they share with a registered statement, providing a first
pass at library reuse before proof search begins.

## Layout

- `Leanproofs/Registry.lean`: research statuses, evidence kinds, and registry records.
- `Leanproofs/Catalog.lean`: durable, version-controlled theorem catalog.
- `Leanproofs/CLI.lean`: environment audit, discovery, graph, and JSON export.
- `Leanproofs/Fermat.lean`: checked mathematical results.
- `web/`: research workspace and generated catalog data.
- `docs/`: trust model, architecture, and contribution workflow.

The project is pinned to Lean and mathlib `v4.33.1`. See
[docs/adding-results.md](docs/adding-results.md) before adding a claim and
[docs/architecture.md](docs/architecture.md) for the product and trust boundaries.
