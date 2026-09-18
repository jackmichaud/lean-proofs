# Adding research results

Each catalog record connects human research metadata to compiled Lean declarations. Keep theorem
code in a topic module and metadata in `Leanproofs/Catalog.lean`.

## Work in a draft first

A catalog entry is the *last* step, not the first. Registering a claim means editing two Lean
files and rebuilding, which is the wrong loop to iterate a proof in. Write a plain `.lean` file
and check it directly:

```bash
lake exe frontier check Draft.lean
```

That elaborates the file against the compiled environment and reports Lean's diagnostics, every
declaration it defines, the axioms each one rests on, and which catalog results the proofs
reuse. Nothing touches the registry, and the axiom policy applied is the same code that gates a
real entry — so a draft that reports clean will not surprise you at `validate` time.

Two limits worth knowing. A draft can only `import` modules that `Leanproofs` already imports,
because the process cannot pull new modules into a live environment; add the import to the
project and rebuild if you need one. And elaboration is bounded by `--heartbeats`, because
non-termination is the ordinary failure mode of a generated proof rather than an edge case.

Once the draft is clean, move it into `Leanproofs/`, import it from `Leanproofs.lean`, and write
the catalog entry.

### Record it, so it survives

`check` is stateless. Attach it to a work item to keep the current result across sessions:

```bash
lake exe frontier work add "Formalize X" --goal 'the proposition'
lake exe frontier check --work formalize-x Draft.lean
```

The item carries the draft path, the attempt count, and the latest report — axioms, catalog
reuse, and Lean's diagnostics — which lets a later session resume from the current state. A new
check replaces that report; the journal does not yet retain each historical run. Append-only
attempt and check history is planned. A passing check sets the stage to `clean`; a later failing
one moves it back, so the board cannot advertise a draft that has since broken. When the result
is registered, close the loop:

```bash
lake exe frontier work set formalize-x --stage registered --entry <catalog id>
```

That stage requires a catalog entry that exists, so it cannot be claimed early.

Before writing anything, read the two axes in [architecture.md](architecture.md#two-axes-status-and-literature).
`status` is what this repository has checked; `literature` is what mathematics knows. Getting
this pair wrong is the most damaging mistake you can make in the catalog, and validation cannot
catch it for you.

## Proved statement

An existing theorem can serve as both statement and certificate:

```lean
{
  id := "my-result"
  title := "My result"
  summary := "A precise one-sentence statement."
  status := .proved
  literature := .proved
  citation? := some "Author, Title, Journal 12 (2001), 3–45."
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

Use `literature := .unresolved` only if you believe the result is genuinely new. That combination
— closed here, unresolved in the literature — is a novelty claim, and the workspace flags it as
one. Search first.

## Open or unresolved statement

Give an unresolved claim a named `Prop`. A later counterexample must prove its negation:

```lean
def claim : Prop := ∀ n : Nat, proposedProperty n

theorem claim_counterexample : ¬ claim := by
  -- checked counterexample proof
```

Register `claim` with status `.open` and no certificate while it is unresolved. For the disproof,
use status `.disproved`, certificate `claim_counterexample`, and evidence `.counterexample`.
Frontier checks that the certificate type is definitionally equal to `¬ claim`.

### Sanity checks are required

Every unresolved entry must list at least one `sanityChecks` declaration. This is not
bureaucracy. A `def _ : Prop` that nothing has been proved about is exactly where
mis-formalization hides: Lean will happily accept a statement whose hypotheses are
contradictory, whose quantifiers are in the wrong order, or that is trivially true — and an
`open` entry has no certificate whose type-checking would have caught it.

Sanity checks are validated like any other declaration (they must be theorems, and they must
satisfy the axiom policy), but they are never counted as research results. Useful kinds:

```lean
-- The hypotheses are satisfiable, so the statement is not vacuously true.
theorem hypotheses_satisfiable : ∃ x y a b : ℕ, 1 < x ∧ 1 < y ∧ … := …

-- A worked instance behaves as expected.
theorem exceptional_solution : (3 : ℕ) ^ 2 = 2 ^ 3 + 1 := by rfl

-- Exhausted bounded search: no small counterexample. Usually `by decide`.
theorem no_small_counterexample : ∀ x < 12, … := by decide
```

The bounded-search check is the highest-value one. Most formalization errors produce a small
counterexample, so a `decide` over a modest range catches them immediately — and if it *fails*,
you have learned something far more important than a passing build.

## Undecidability or independence

Formalize the theory, decision problem, encoding, and reduction or model construction in Lean. The
registered certificate must be the theorem proving that metamathematical result. Use
`.undecidable` with `.reduction` or `.metatheorem`, and `.independent` with `.modelConstruction` or
`.metatheorem`.

`baseTheory?` is required for these statuses and validation rejects the entry without it. Be
aware of what the check is worth: Frontier verifies the certificate proves the registered
statement, exactly as it does for `.proved`. It does *not* verify that the statement is a real
metatheorem about the theory you named. Reviewers must check that; the kernel will not.

## Provenance

`authors` lists the humans responsible for the claim and is required. `tooling` lists automated
assistance — a model, a tactic search, a code generator. Tools go in `tooling`, not `authors`:
attribution of mathematical responsibility is to people, and mixing the two makes it impossible
to tell who to ask about a proof.

## Validate and publish

Import the topic module from `Leanproofs.lean`, add its catalog entry, then run:

```bash
make check
make catalog
```

`make check` builds the executable, audits every entry, checks the web workspace, and compares a
fresh export against the committed catalog. The comparison is *structural*: pretty-printed Lean
types move with the toolchain, so a mathlib bump reports rendering drift as information rather
than failing the build. Any change to ids, statuses, certificates, dependencies, axioms, or
metadata does fail it.

`make catalog` updates `web/data/catalog.json` after an intentional registry change. Commit that
file with the change that caused it; CI enforces that they agree.

Before starting a proof, inspect existing work:

```bash
lake exe frontier search <name-fragment>
lake exe frontier search <name-fragment> --definitions
lake exe frontier suggest <registry-id>
lake exe frontier suggest --goal '<the proposition you are trying to prove>'
lake exe frontier policy
```

`suggest --goal` is the one to reach for on new work: it elaborates the proposition against the
imported environment and ranks premises for it, so you do not have to register a claim before
the tool will help you prove it.

Dependencies between registered results are discovered from proof terms on the next validation and
export; do not maintain them manually.

## Scratch work

Lean under `external/` is git-ignored and is **not** part of the build. Nothing there is compiled
by `lake build` or seen by `frontier validate`, so a `grep` for `sorry` over it proves nothing —
an unbuilt file has no verified content at all. Move a file into `Leanproofs/` and import it from
`Leanproofs.lean` to have it checked.
