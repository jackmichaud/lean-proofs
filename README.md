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
lake exe frontier check Draft.lean
lake exe frontier search pow_card
lake exe frontier suggest fermat-zmod
lake exe frontier suggest --goal '∀ (p : ℕ) [Fact p.Prime] (a : ZMod p), a ^ p = a'
lake exe frontier prove --goal '∀ n : ℕ, n + 0 = n'
lake exe frontier prove --state 1 --tactic 'intro n'
lake exe frontier work add "Formalize X" --goal 'the proposition'
lake exe frontier check --work formalize-x Draft.lean
lake exe frontier work list
lake exe frontier graph
lake exe frontier policy
lake exe frontier export web/data/catalog.json
lake exe frontier serve
```

`check` elaborates a draft Lean file against the compiled environment and reports Lean's
diagnostics, the axiom policy, and which catalog results the draft's proofs reuse. It does not
touch the registry, so it — not a catalog edit — is the loop to iterate in.

`prove` is the loop *below* that one. `check` takes a whole file and reports what Lean said,
which is the wrong granularity for searching for a proof: it cannot answer "what is the goal
after `intro n`" or "does `simp` close this", so the only way to use it is to guess a complete
proof and read an error. `prove` opens a proof state from a proposition, advances it one tactic
block at a time, and reports the outstanding goals with their hypotheses after each. State ids
persist across requests in a `frontier serve` session, so a prefix does not have to be resent;
a block that fails is discarded rather than recorded, leaving the state it was tried against
usable. When the goal closes, `prove` emits a `theorem` scaffold to save and `check`.

`prove` reports `closed` and `complete` separately, and the difference is the whole point.
Tactic elaboration reports an unknown identifier as a *message* and returns `sorry`, so `exact
nonsense_lemma` and `sorry` alike leave no goals outstanding. `complete` requires all three of
no goals, no errors, and an assembled proof term that satisfies the axiom policy — the standard
`validate` holds a registered certificate to. A `native_decide` that closes a goal is reported
as `closed` and not `complete`, with the offending axiom named.

`search` finds declarations by name across every imported Lean module, ranked exact → final
component → prefix → substring; `--definitions` widens it past theorems and axioms. Both
commands range over mathlib in full: the corpus is what the root module imports, so
`Leanproofs` imports all of it for that reason alone (see `Leanproofs/Library.lean`).

`suggest` ranks imported theorems by cosine-style inverse-document-frequency weighted overlap
of the constants in their statements, so a shared `ZMod` outranks a shared `Nat`. Two terms
beyond plain overlap earn their place. Conclusions are weighted above hypotheses, because
concluding in the shape being proved says more than mentioning it in a side condition. And the
score is normalized by the candidate's own information content — without that, every candidate
containing all of the goal's constants attains the same maximum, a large tied bucket forms at
the top, and alphabetical order decides the ranking. It takes a registry id or a
`--goal` written as a Lean term, because the proposition you want premises for is usually one
you just wrote. For a registry id it excludes every entry that transitively depends on the
target: those are exactly the premises that would make the proof circular. `policy` prints the
axiom allowlist and the reason each denied axiom is denied.

## Work journal

`check` is stateless: it tells you whether a file is acceptable and forgets. The journal is
where the work between "here is a goal" and "here is a catalog entry" lives — one append-only
JSONL event stream per attempt under `work/`, committed, so its history survives the session
that produced it. Readers and writers coordinate through operating-system file locks. A batch is
validated and assigned IDs while holding its stream lock, then committed by atomic rename, so
concurrent agents see either the complete previous history or the complete next history.

```bash
lake exe frontier work add "Formalize X" --goal 'the proposition' --note 'why it is stuck'
lake exe frontier check --work formalize-x Draft.lean   # records axioms, reuse, diagnostics
lake exe frontier work list --stage blocked
lake exe frontier work set formalize-x --stage registered --entry <catalog id>
lake exe frontier work abandon formalize-x --reason 'superseded by another approach'
```

The journal is **untrusted**: a record of attempts, not evidence about mathematics, and it says
so in its own exported data. Two stages cannot be asserted by hand — `clean` is written only by
a `check --work` that actually passed, and `registered` requires naming a catalog entry that
exists. A board whose stages could be typed in would be a progress bar an agent could fill in.

Every mutation republishes `web/data/work.json`, and the workspace reloads it while the tab is
visible, so the page follows along with work as it happens rather than showing the last commit.
This is a local tool: nothing in `work` is executed, and `check` is *not* a submission
endpoint — see [docs/retrieval-and-agents.md](docs/retrieval-and-agents.md).

## Agent interface

Start at [AGENTS.md](AGENTS.md) for the loop. Add `--json` to any command for machine-readable
output.

Importing mathlib with the delaborators loaded costs about twenty seconds, and every one-shot
command pays it. `frontier serve` imports once and then answers requests on stdin — one request
per line, one JSON response per line:

```bash
printf '%s\n' '{"apiVersion":"frontier.agent/v1","requestId":"req-1","operation":"declarations.search","params":{"query":"pow_card","limit":3,"includeDefinitions":false},"provenance":{"kind":"agent","name":"example-agent","runId":"run-1","model":"model-name"}}' | lake exe frontier serve
```

Each line is a versioned request envelope with an operation-specific `params` object, caller
`provenance`, and a unique `requestId`. Responses preserve that correlation id and report the
loaded environment identifier; clients may send it back as `environment` to reject accidental
execution against a different snapshot. Start with `capabilities.get` to discover the supported
operations. Legacy argument arrays and bare commands are intentionally rejected. EOF ends the
session.

Research operations are attempt-scoped. `research.attempt.create` creates the append-only stream
and may open an initial Lean proposition; `premises.retrieve` records its ranked candidates, and
`proof.evaluateBatch` records every proposed tactic and verifier outcome against a state owned by
that attempt. `research.attempt.list` and `research.attempt.get` let a later session discover and
reconstruct that work. Typed proof state ids are durable and attempt-scoped, rather than addresses
into one process's cache. After a restart, `proof.rehydrate` replays an explicitly selected branch,
checks its goals and completion status against the recorded observations, and makes that state live
again. This makes branching and failed approaches durable research data without treating them as
mathematical evidence.

The premise corpus is prepared once per session — every imported theorem reduced to sorted
constant arrays and an IDF mass — on the first `suggest`. That call pays for the whole corpus;
each one after it costs a fraction of a second rather than the seconds a rescan of mathlib
would.

## Trust

`frontier validate` enforces an axiom allowlist rather than reporting axioms as a footnote.
`propext`, `Classical.choice`, and `Quot.sound` are accepted; `sorryAx`, `Lean.ofReduceBool`
(`native_decide`), and `Lean.trustCompiler` are rejected, and anything else is an error. Statements
and sanity checks are audited alongside certificates. The same policy runs on drafts, so
`frontier check` rejects a `sorry` or a `native_decide` before it can reach the registry.

`lake exe frontier-test` is the negative half of that claim: fixtures that are *supposed* to
fail, asserting that they do. A green `validate` over correct entries is no evidence that an
incorrect one would be rejected, and rejecting is the whole job. It runs first in `make check`
and first in CI.

Read [docs/architecture.md](docs/architecture.md#what-validation-does-not-establish) for what
validation does *not* establish — faithfulness of the formalization, the substance of a relative
`undecidable`/`independent` classification, vacuity, and novelty are all outside what the kernel
decides.

## Layout

- `Leanproofs/Library.lean`: imports mathlib in full. Proves nothing; it is what makes the
  premise corpus and the set of modules a draft may use the whole library rather than a slice.
- `Leanproofs/Knowledge/Model.lean`: normalized claims, formalizations, certificates, citations,
  sanity checks, and semantic relations.
- `Leanproofs/Registry.lean`: joined read views over the normalized knowledge graph.
- `Leanproofs/Catalog.lean`: durable, version-controlled normalized theorem catalog.
- `Leanproofs/Frontier/`: audit, proof interaction, retrieval, typed API, and environment identity.
- `Leanproofs/CLI.lean`: thin public facade over the Frontier modules.
- `Leanproofs/Journal.lean`: the work journal. Untrusted, durable, never part of an audit.
- `Leanproofs/Main.lean`: the executable. Thin, and its import list is load-bearing — see the
  module docstring for why the catalog is read out of the environment rather than linked.
- `Leanproofs/Test.lean`, `Leanproofs/TestMain.lean`: negative fixtures for the audit.
- `Leanproofs/Fermat.lean`, `Leanproofs/Catalan.lean`: checked mathematical results.
- `web/`: research workspace, generated catalog data, and the published work journal.
- `work/`: the work journal itself, one append-only JSONL event stream per attempt.
- `scripts/`: catalog comparison and browser QA.
- `docs/`: trust model, architecture, and contribution workflow.
- `external/`: git-ignored scratch. **Not compiled and not verified by anything** — a `sorry`
  grep over an unbuilt file proves nothing. Move work into `Leanproofs/` to have it checked.

The project is pinned to Lean and mathlib `v4.33.1`. See
[docs/README.md](docs/README.md) for the documentation index, [docs/adding-results.md](docs/adding-results.md)
before adding a claim, and [docs/architecture.md](docs/architecture.md) for the product and trust
boundaries. The proof-system graph hierarchy is described in [docs/graph-model.md](docs/graph-model.md),
and agent-facing retrieval is outlined in [docs/retrieval-and-agents.md](docs/retrieval-and-agents.md).
