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

1. Every statement, certificate, and sanity-check name resolves.
2. Statements denote propositions and certificates are Lean theorems.
3. A `proved` certificate is definitionally equal to the statement.
4. A `disproved` certificate is definitionally equal to the negation of the statement.
5. A `conditional`, `independent`, or `undecidable` certificate is definitionally equal to the
   registered statement — see the limits below, because this check is weaker than it sounds.
6. Status and evidence kind agree.
7. Closed results have certificates and open results do not.
8. `independent` and `undecidable` entries name their base theory.
9. Every statement, certificate, and sanity check satisfies the axiom policy.
10. Unresolved entries carry at least one sanity check.
11. Literature states that assert something about published mathematics carry a citation.
12. Catalog identifiers are unique and dates are ISO-8601.

### Axiom policy

The kernel reports which axioms a proof rests on; Frontier turns that report into a decision
rather than a footnote. Run `lake exe frontier policy` for the current lists.

Allowed: `propext`, `Classical.choice`, `Quot.sound` — the three assumptions of ordinary
classical mathematics as formalized in mathlib.

Denied, each for a specific reason:

| Axiom | Why it is rejected |
| --- | --- |
| `sorryAx` | The proof is incomplete. |
| `Lean.ofReduceBool` | Introduced by `native_decide`. It trusts the Lean compiler and runtime, which are outside the kernel and have had soundness bugs. |
| `Lean.trustCompiler` | Places the compiler inside the trust base. |

Anything else is a validation *error*, not a note. This has to be enforced now rather than
later: the roadmap accepts Lean from automated agents, and an unnoticed `native_decide` is a
soundness hole that an agent optimizing for "make the build pass" will find. Widening the
allowlist is a deliberate, reviewable edit to `Leanproofs/CLI.lean`.

Statements are audited too, not only certificates. A statement is usually a `def _ : Prop`
that no certificate points at, so auditing only certificates would let an `open` entry built
out of `sorry` display as clean.

### What validation does not establish

These limits are load-bearing; the checks above are worth exactly as much as this list is
honest.

- **Faithfulness.** Lean checks that the certificate proves the registered proposition. Nothing
  checks that the proposition means what the English summary says. A mis-formalized statement
  that is trivially true will validate. `sanityChecks` exist to attack this specific gap and are
  required on unresolved entries, but they are evidence, not proof.
- **Relative classifications.** Check 5 is definitional equality against the registered
  statement, which is the *same* check `proved` gets. It does not verify that the statement is
  genuinely a metatheorem about the named base theory. `baseTheory?` is required so the claim is
  at least explicit and reviewable, but calling something `undecidable` is a claim the reviewer
  must check, not one the kernel checks.
- **Vacuity.** A statement with unsatisfiable hypotheses is vacuously true and will validate.
  A satisfiability witness is the standard sanity check against this.
- **Novelty.** `literature` is maintainer-asserted metadata. Nothing verifies a citation.

## Two axes: status and literature

Every record carries two independent fields, and reading either alone is misleading.

- `status` is what **this repository** has formalized and kernel-checked.
- `literature` is what **mathematics** knows, independent of this repository.

Collapsing them was the registry's worst failure mode. Catalan's conjecture is `status := .open`
because nothing here formalizes Mihăilescu's proof, and `literature := .proved` because it has
been a theorem since 2002. A single "open" field would have advertised a settled theorem as an
open problem — the exact error a research registry exists to prevent.

The combinations mean different work:

| status | literature | Reading |
| --- | --- | --- |
| unresolved | `unresolved` | A genuine research target. |
| unresolved | `proved` / `disproved` / `folklore` | Formalization backlog. The mathematics is known; typing it into Lean is the task. |
| closed | `proved` / `disproved` | Formalized a known result. The usual case for a library. |
| closed | `unresolved` | Claims a new result. Warrants scrutiny before being described as one. |

A `literature` state other than `unresolved` asserts something about published mathematics and
therefore requires a citation. The web workspace reports the two axes as separate metrics —
"research frontier" versus "formalization backlog" — for the same reason.

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

Frontier extracts catalog dependencies from the proof term, so authors never maintain a second
dependency list.

The extraction walks the certificate's transitive constants and records the *minimal* catalog
ancestors: traversal stops descending at a registered declaration, so an entry's dependencies
are its nearest registered ancestors rather than every ancestor. Without this, every entry in a
chain would list every entry below it and the graph would degenerate to a transitive closure
that shows nothing. Axioms are still collected through registered intermediates, because an
axiom must be audited no matter how many catalog entries it passes under.

The catalog covers curated research artifacts. The imported Lean environment is broader: it
includes mathlib and project dependencies.

- `frontier search` locates declarations by name across everything imported. Matches are ranked
  exact, then final-component, then prefix, then substring, so the top of the list is stable and
  meaningful rather than whichever entries the hash map yielded first.
- `frontier suggest` ranks theorems by inverse-document-frequency-weighted overlap of the
  constants in the two propositions. Plain overlap counting is dominated by `Nat` and `Eq`, which
  appear everywhere and carry no signal; IDF weighting makes a shared `ZMod` outrank a shared
  `Nat` without any model or index. It is a ranking heuristic, and only that.

Later retrieval layers can add semantic embeddings, premise-selection models, and external
literature without changing the kernel trust boundary.

The long-term reuse loop is `prove -> verify -> store -> retrieve -> prove harder results`. A
successful proof can add a named Lean declaration to the library; later goals can retrieve that
declaration as a premise and avoid rediscovering the proof. The key search problem is premise
selection: ranking a small, useful candidate set from the much larger graph of verified
mathematics.

Frontier uses a hierarchical graph model rather than a single graph for every purpose. The current
system exposes the kernel-audited dependency graph; future proof search should add proof-state
graphs whose edges are Lean-verified transitions. See [graph-model.md](graph-model.md) for the
knowledge graph, dependency graph, and proof graph boundaries.

Frontier can expose retrieval and submission through MCP without weakening this boundary. Agents
may search theorem indexes, retrieve candidate premises, and submit Lean code into staging, but
only Lean-validated and intentionally promoted declarations become trusted catalog knowledge. See
[retrieval-and-agents.md](retrieval-and-agents.md) for the vector retrieval, MCP, submission, and
web workspace design.

## Product horizon

The current system is the durable substrate for proof planning, parallel tactic/model search,
finite counterexample generation, computer-algebra integrations, and reduction libraries. No
search layer can decide every proposition. Frontier should instead report precise outcomes:
verified proof, verified disproof, certified metatheoretic classification, exhausted bounded
search, or an explicit unresolved gap.
