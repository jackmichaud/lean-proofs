# Frontier architecture

Frontier separates mathematical truth from research workflow. The Lean kernel decides whether a
certificate type-checks. The registry decides what that certificate is evidence for. The UI makes
the resulting knowledge base searchable and operational, but it is never part of the trust base.

```text
informal conjecture
        |
        v
formal Lean proposition ---> mathlib/catalog retrieval ---> proof or counterexample search
        |                                                       |
        +----------------------- Lean certificate <-------------+
                                    |
                                    v
                       audit + dependency extraction
                                    |
                                    v
                     catalog JSON + research workspace
```

## Trust boundary

The trusted result is a compiled Lean declaration and its transitive assumptions. `frontier
validate` imports the compiled project environment and checks:

1. Every statement and certificate name resolves.
2. Statements denote propositions and certificates are Lean theorems.
3. A `proved` certificate has the statement as its type.
4. A `disproved` certificate has the negation of the statement as its type.
5. Conditional, independence, and undecidability certificates prove their registered metatheorem.
6. Status and evidence kind agree.
7. Closed results have certificates and open results do not.
8. No certificate transitively depends on `sorryAx`.
9. Catalog identifiers are unique.

The export includes all other transitive axioms, such as `Classical.choice`, `propext`, and
`Quot.sound`. These are visible assumptions, not validation failures. A future policy layer can
restrict acceptable axiom sets per project or result.

## Status semantics

| Status | Meaning | Accepted evidence |
| --- | --- | --- |
| `formalizing` | The informal claim is not yet represented faithfully in Lean. | None |
| `open` | The formal statement is fixed but unresolved. | None |
| `conditional` | A result follows from explicit additional hypotheses. | Conditional proof |
| `proved` | The registered proposition has a Lean proof. | Proof |
| `disproved` | The negation of the registered proposition has a Lean proof. | Counterexample |
| `independent` | Independence is proved relative to an explicitly formalized theory. | Model construction or metatheorem |
| `undecidable` | Undecidability is proved for an explicitly formalized decision problem. | Reduction or metatheorem |

Independence and undecidability are relative mathematical statements. Their certificates prove a
formal metatheorem, usually by model construction or reduction to a known undecidable problem.
Merely labeling a difficult conjecture `undecidable` is invalid research metadata.

## Knowledge reuse

Frontier extracts direct catalog dependencies from constants used in certificate bodies. This
produces a checked proof lineage without asking authors to maintain a second dependency list.

The catalog covers curated research artifacts. The imported Lean environment is broader: it
includes mathlib and project dependencies. `frontier search` locates known declarations by name,
while `frontier suggest` ranks theorem statements that share domain-specific constants with the
selected result. Later retrieval layers can add semantic embeddings, premise-selection models,
and external literature without changing the kernel trust boundary.

## Product horizon

The current system is the durable substrate for proof planning, parallel tactic/model search,
finite counterexample generation, computer-algebra integrations, and reduction libraries. No
search layer can decide every proposition. Frontier should instead report precise outcomes:
verified proof, verified disproof, certified metatheoretic classification, exhausted bounded
search, or an explicit unresolved gap.
