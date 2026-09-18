# Working in Frontier

Frontier is a Lean-checked mathematical research registry. Lean decides what is true; this
repository supplies the catalog, trust audit, dependency graph, premise retrieval, and work
journal around it.

Read this first, then [README.md](README.md#agent-interface) for the request protocol and
[docs/adding-results.md](docs/adding-results.md) before registering anything.

## The loop

Do not start by editing the registry. A catalog entry is the last step. The loop is:

```bash
lake exe frontier work add "Short title" --goal "what you are trying to prove"
lake exe frontier suggest --goal '<the Lean proposition>'   # find premises
lake exe frontier prove --goal '<the Lean proposition>'     # open a proof state
lake exe frontier prove --state 1 --tactic 'intro n'        # step, read the new goal
lake exe frontier prove --state 2 --tactic 'simp'           # until it closes
#   ... save the scaffold `prove` hands back as Draft.lean ...
lake exe frontier check --work <item id> Draft.lean         # elaborate and audit
#   ... iterate until clean ...
#   then move the file into Leanproofs/, import it, add the catalog entry
```

`prove` is the tactic-level loop. Do not guess a whole proof and compile it: open the goal, apply
one tactic, read the goal state that comes back. Each step returns a new state id, and a block
that fails leaves the state it was tried against usable, so exploring costs nothing. When the
goal closes, `prove` hands back a `theorem` scaffold to save and `check`.

**`closed` is not `complete`.** A tactic block reports an unknown identifier as a *message* and
returns `sorry`, so `exact nonsense_lemma` and `sorry` both leave no goals. `complete` is the
field that means anything: no goals, no errors, and a proof term inside the axiom policy. Read
that one.

`check` reports Lean's diagnostics, the axioms every declaration rests on, and which catalog
results the proofs reuse. It does not touch the registry, so it is cheap to run and cheap to
fail. `--work` records the report against a journal item, which is the only reason any of it
survives your session.

Typed agent sessions use durable, attempt-scoped proof state ids. After restarting `frontier
serve`, read the attempt with `research.attempt.get`, choose the exact recorded branch you want,
and call `proof.rehydrate` before inspecting or extending that state. Replay is checked against
the current Lean environment and fails explicitly if the recorded branch has drifted.

## Use a session

Importing mathlib with the delaborators loaded costs about twenty seconds, and every one-shot
command pays it in full. If you are making more than a couple of calls, open a session:

```bash
printf '%s\n' '{"apiVersion":"frontier.agent/v1","requestId":"req-1","operation":"research.attempt.create","attemptId":"add-zero","params":{"title":"Prove add_zero","goal":"Formalize the additive identity","proposition":"∀ n : ℕ, n + 0 = n"},"provenance":{"kind":"agent","name":"research-agent","runId":"run-1","model":"model-name"}}' \
  | lake exe frontier serve
```

One versioned JSON request envelope per line in, one correlated JSON response per line out.
Begin with `capabilities.get`; supported operations include declaration search, premise
retrieval, independent batch tactic evaluation, proof-state inspection, and attempt history
reads. Pin later requests to the environment id returned by the session. Premise retrieval and
proof operations require the attempt id and record their inputs and outcomes in that attempt's
event stream. Use `research.attempt.list` and `research.attempt.get` when resuming work. Legacy
argument arrays and bare commands are not accepted. `--json` works on any one-shot command too.

## Things that will trip you up

- **A draft can only `import` what `Leanproofs` already imports.** The process cannot pull new
  modules into a live environment. `Leanproofs` imports mathlib in full — see
  `Leanproofs/Library.lean` — so in practice `import Mathlib` and any of its modules are
  available, and anything else needs the import added to the project and a rebuild.
- **`native_decide` is rejected.** It rests on an axiom that trusts the compiler and runtime,
  outside the kernel. So is `sorry`. The axiom allowlist is `propext`, `Classical.choice`,
  `Quot.sound`, and *nothing else* — see `lake exe frontier policy`. Do not widen it to make a
  build pass; that is a soundness hole, and it is checked on statements and sanity checks as
  well as certificates.
- **`external/` is not compiled and not verified by anything.** Grepping it for `sorry` proves
  nothing about an unbuilt file. Only `Leanproofs/` is checked.
- **Unresolved entries need a sanity check.** A `def _ : Prop` that nothing has been proved
  about is where mis-formalization hides. A satisfiability witness or a bounded `decide` catches
  the common errors; see [docs/adding-results.md](docs/adding-results.md).
- **`status` and `literature` are different fields.** `status` is what this repository has
  checked; `literature` is what mathematics knows. A known theorem you have not formalized is
  `status := .open, literature := .proved` — formalization backlog, not an open problem.
  Getting this pair wrong is the most damaging mistake available, and validation cannot catch
  it for you.
- **You are `tooling`, not `authors`.** Mathematical responsibility is attributed to people.

## What the kernel does not decide

`frontier validate` passing means a certificate type-checks against a registered proposition.
It does not mean the proposition says what the English summary says, that a relative
`undecidable` claim is really a metatheorem, that the hypotheses are satisfiable, or that the
result is novel. See
[docs/architecture.md](docs/architecture.md#what-validation-does-not-establish). Do not
describe a validated entry as more than it is.

## Before you finish

```bash
make check    # negative fixtures, registry audit, catalog sync, browser QA
make catalog  # only after an intentional registry change; commit the result
```

`make check` runs `lake exe frontier-test` first, on purpose: a green `validate` proves nothing
if the audit has stopped rejecting bad entries.
