# Adding research results

Each catalog record connects human research metadata to one or two compiled Lean declarations.
Keep theorem code in a topic module and metadata in `Leanproofs/Catalog.lean`.

## Proved statement

An existing theorem can serve as both statement and certificate:

```lean
{
  id := "my-result"
  title := "My result"
  summary := "A precise one-sentence statement."
  status := .proved
  topic := "number-theory"
  tags := #["prime", "example"]
  statement := ``MyNamespace.myTheorem
  certificate? := some ``MyNamespace.myTheorem
  evidence? := some .proof
  authors := #["Author Name"]
  created := "2026-08-31"
  updated := "2026-08-31"
}
```

## Open or disproved statement

Give an unresolved claim a named `Prop`. A later counterexample must prove its negation:

```lean
def claim : Prop := ∀ n : Nat, proposedProperty n

theorem claim_counterexample : ¬ claim := by
  -- checked counterexample proof
```

Register `claim` with status `.open` and no certificate while it is unresolved. For the disproof,
use status `.disproved`, certificate `claim_counterexample`, and evidence `.counterexample`.
Frontier checks that the certificate type is definitionally equal to `¬ claim`.

## Undecidability or independence

Formalize the theory, decision problem, encoding, and reduction or model construction in Lean. The
registered certificate must be the theorem proving that metamathematical result. Use
`.undecidable` with `.reduction` or `.metatheorem`, and `.independent` with `.modelConstruction` or
`.metatheorem`. Name the base theory in the title or summary; these classifications are never
absolute labels.

## Validate and publish

Import the topic module from `Leanproofs.lean`, add its catalog entry, then run:

```bash
make check
make catalog
```

`make check` builds the executable, audits every certificate, verifies frontend syntax, generates a
fresh catalog into `build/`, and compares it with the committed web catalog. `make catalog` updates
`web/data/catalog.json` after an intentional registry change.

Before starting a proof, inspect existing work:

```bash
lake exe frontier search <name-fragment>
lake exe frontier suggest <registry-id>
```

Dependencies between registered results are discovered from proof terms on the next validation and
export; do not maintain them manually.
