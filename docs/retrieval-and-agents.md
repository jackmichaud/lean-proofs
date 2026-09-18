# Retrieval and Agent Architecture

Frontier can support vector database retrieval, theorem search, MCP-accessible tools, agent proof
submission, and a user-facing proof graph without expanding the trusted base. The core rule is
simple: agents may propose and submit; Lean verifies; Frontier records only audited results as
trusted knowledge.

```text
Lean project + Frontier catalog
        |
        v
verified declarations, propositions, dependencies, axioms
        |
        v
retrieval indexes + graph indexes
        |
        v
MCP tools, agents, search UI, proof submission queue
```

## Build Order

Sequence matters more than the component list. The bottleneck today is not retrieval
infrastructure — it is that the catalog contains six entries. A vector database over six
theorems retrieves nothing that `frontier search` does not.

Recommended order, cheapest and highest-value first:

0. **Done.** A machine-readable interface to what already exists. Every one-shot command takes
   `--json`, and `frontier serve` answers versioned, typed newline-delimited JSON requests
   against an environment imported once instead of once per command. Requests carry correlation,
   provenance, and optional environment pinning. This was the actual blocker: an agent cannot
   iterate against a tool that costs twenty seconds a call and returns column-aligned prose.
1. **Read-only MCP tools** over that interface. With `serve` in place this is a thin adapter
   from MCP tool calls to request lines, not new infrastructure.
2. **Lexical and symbolic retrieval over mathlib.** Largely done. `frontier suggest` does
   cosine-normalized IDF-weighted constant overlap with conclusions weighted above hypotheses,
   over a registry id or an arbitrary elaborated `--goal`, against all of mathlib. Note that
   the normalization is not a refinement: unnormalized overlap ties every candidate covering
   the goal's constants and hands the ranking to alphabetical order, so the feature did not
   work at all without it. What remains — namespace locality, graph distance, deeper type-shape
   matching — is cheap and, for premise selection, competitive with dense retrieval. Hybrid
   systems beat pure vector search on this task consistently; this is the baseline to beat.
3. **Proof-state interaction.** Done: `frontier prove`. A proposition opens a proof state, a
   tactic block advances it, and the outstanding goals come back with their hypotheses; state
   ids persist across requests in a session. `frontier check` is *not* this — it elaborates a
   whole file and reports the result, which is a compile loop, not a tactic-level search loop.

   This was expected to wrap `leanprover-community/repl` rather than use Lean's `Elab.Tactic`
   directly, and the reasoning against hand-rolling was sound as far as it went: a REPL
   subprocess brings maintained environment setup and goal serialization, and a local
   interaction layer drifts on toolchain bumps. Memory decided it the other way. The `frontier`
   process already holds mathlib at roughly 5.7GB resident plus the premise index, and a `repl`
   subprocess with its own `import Mathlib` would hold several gigabytes more for a second copy
   of the same environment — against a design whose whole premise is one long-lived process
   that imports once. `prove` therefore drives `Elab.Tactic` against the environment already
   loaded, so tactics see exactly the declarations `check` and `suggest` do. The surface
   exposed to drift is four stable entry points; see the `## Proof state` section of
   `Leanproofs/Frontier/Proof.lean` for the resulting interaction boundary.

   Two findings from building it are worth carrying forward, because both were silent:

   - **A suspended elaborator state does not survive being resumed in a later run.** Hygienic
     binder names, the name generator, instance caches, and the metavariable context are all
     per-run. Resuming one, `intro p hp a` succeeded and the next `exact ZMod.pow_card a` then
     failed to synthesize an instance printed in its own goal. `prove` replays the accepted
     script in a single run instead, which makes the goal states it reports the same ones Lean
     produces when compiling the assembled proof.
   - **A proof term must be audited in the post-elaboration environment.** `native_decide`
     emits a fresh axiom while it runs; audited against the environment as it was beforehand
     it appears axiom-free, and a `native_decide` proof is reported as clean.
4. **Embeddings**, once there is enough content and a lexical baseline to measure against.

Adding a vector database first is the tempting order and the wrong one: it is the component
that most looks like progress and least changes what the system can prove.

## Retrieval Layer

A vector database is useful, but it should be one signal in a hybrid retrieval system rather than
the only ranking mechanism. Frontier should index multiple views of the same declaration:

- Lean declaration name
- pretty-printed theorem type
- namespace and imported module
- catalog title, summary, topic, tags, and status
- direct and transitive dependencies
- transitive axioms
- optional docstrings or informal explanations
- future proof-search traces

Recommended retrieval signals:

- exact and fuzzy name search
- symbolic overlap between goal constants and theorem constants
- namespace, module, topic, and tag locality
- graph distance from related definitions or catalog entries
- vector similarity over statements and informal descriptions
- historical success from prior proof attempts
- Lean feedback from rejected tactic or term candidates

The retrieval layer ranks premises. It does not certify them. A premise only matters for truth when
Lean accepts a proof term or tactic script that uses it.

## MCP Agent Boundary

Frontier can expose an MCP server so any capable agent can inspect the theorem library, retrieve
premises, attempt inference, and submit candidate proofs. Useful tools include:

- `search_theorems`: find declarations by name, text, namespace, topic, or tag
- `retrieve_premises`: rank likely premises for a formal goal
- `show_result`: inspect statement, certificate, status, dependencies, and axioms
- `show_dependencies`: traverse direct or transitive dependency neighborhoods
- `submit_proof`: place candidate Lean code into a staging queue
- `validate_submission`: run Lean and return errors, goals, dependencies, and axioms
- `promote_submission`: convert a validated submission into a curated catalog entry

MCP tools should be designed for least authority. External agents should not directly mutate the
trusted catalog. They submit candidates into staging; Frontier validates them; a human or policy
layer promotes reusable results.

## Executing Submitted Lean Is Arbitrary Code Execution

This is a prerequisite for `submit_proof`, not a later hardening pass. Checking a Lean file is
not a sandboxed pure computation. Elaboration runs arbitrary code at compile time:
`#eval` performs IO, `run_cmd` and macros execute during elaboration, `initialize` blocks run on
import, and `implemented_by` swaps in unverified implementations. Anything that can submit a
`.lean` file to a validator that builds it can run code on the validator.

Requirements before any submission endpoint accepts input:

- **Process isolation.** Build each submission in a container or VM, not in the repository
  checkout. No network, no credentials in the environment, a read-only mathlib cache, a
  writable scratch directory, and a fresh filesystem per submission.
- **Resource limits.** Wall-clock timeout, memory cap, and disk quota. Non-termination is the
  default failure mode of generated proofs, not an edge case.
- **Syntactic prescreen** before elaboration, rejecting or flagging `unsafe`, `implemented_by`,
  `extern`, `initialize`, `run_cmd`, `#eval`, and macro definitions. A prescreen is a filter, not
  a security boundary — it is defence in depth behind the sandbox, never a substitute.
- **Axiom policy at the gate.** Run the same check `frontier validate` runs. `native_decide` is
  the one to watch: it produces a proof the kernel accepts on the strength of
  `Lean.ofReduceBool`, which trusts the compiler and runtime. It is denied by policy, and an
  agent optimizing for a green build will discover it if the gate is missing.
- **Concurrency limits and rate limiting**, since each validation costs minutes of CPU.

Treat submitted Lean the way you would treat submitted C: as hostile input to a compiler.

## Submission States

Agent output should move through explicit states:

| State | Meaning |
| --- | --- |
| `draft` | Unchecked generated Lean or informal strategy |
| `submitted` | Candidate proof received by Frontier |
| `checking` | Lean build or focused validation is running |
| `rejected` | Lean rejected the candidate, timed out, or found a policy violation |
| `verified` | Lean accepted the declaration and Frontier audited dependencies and axioms |
| `promoted` | A verified result was intentionally added to the durable catalog |

This prevents a noisy proof-search workspace from polluting the reusable library. Many generated
lemmas may be valid but too specific to promote.

## Storage Boundaries

Frontier should keep four stores distinct:

| Store | Contents | Trusted? |
| --- | --- | --- |
| Lean source | durable declarations and proofs | yes, after build |
| Catalog JSON | audited metadata, dependencies, axioms | derived from Lean |
| Work journal (`work/`) | local attempts, check reports, stages | no |
| Retrieval index | embeddings, lexical indexes, graph indexes | no |
| Submission queue | agent drafts, failures, proof traces | no |

## Local work journal versus submission queue

These are two different stores and conflating them would be a security error, so the difference
is worth stating plainly.

The **work journal** exists today (`Leanproofs/Journal.lean`, `frontier work`). It records what
an agent working *in this checkout* is already doing: goals, draft paths, stages, and the
attempt count and latest report from `frontier check --work`. Each check replaces that report;
append-only attempt and check history is planned. Nothing in the journal is executed. Reading a
journal file is not running it, and the sandbox requirements above do not apply, because there
is no untrusted party — the code being checked is the local agent's own, which it could have
run anyway.

The **submission queue** does not exist and must not be built before the sandbox does. It
accepts Lean from somewhere else, which means building it, which means arbitrary code
execution. `frontier check` and `frontier serve` are local developer tools for exactly this
reason: the only thing separating them from that hazard is that nothing remote can reach them.

The journal has a stage named `clean`, and it is written only by a `check --work` that passed —
never by hand, the same way a closed registry status requires a certificate. `registered`
likewise requires naming a catalog entry that exists. This matters because a journal is the
thing a later session trusts to decide what is done, and a stage an agent could simply assert
would make it a progress bar rather than a record.

The vector database can always be rebuilt from Lean source, catalog export, and approved metadata.
It should not be the system of record for mathematical truth.

## Web Workspace

The user-facing site should make the trusted backbone legible:

- show proved, open, disproved, conditional, independent, and undecidable results
- traverse proof dependencies and axiom support
- inspect direct and transitive neighborhoods
- search theorem statements, tags, topics, and names
- show pending submissions separately from verified results
- display why a proof was rejected or which Lean errors remain
- expose promoted results as reusable graph nodes

The site is an operations and understanding layer. It can make the knowledge graph pleasant to
explore, but it remains outside the trust base.

The work-in-progress view is the first of these. It reads the published journal, groups items
by stage, and shows each item's last check — the verdict, the axiom-policy violations, Lean's
diagnostics, and the catalog results the draft reuses. Three properties are load-bearing:

- It is **observational**. It reports what the CLI recorded and collects nothing. The intake
  dialog that does collect something is browser-local scratch, kept in a separate view and
  labelled as such, because a static page cannot write to the journal.
- It **reloads while visible**, so a human watching a running agent sees progress without
  refreshing. A hidden tab does not poll.
- It is **visibly untrusted**, and never summed into a kernel-audited count. Journal items,
  browser-local notes, and catalog entries are three different kinds of thing; a metric that
  added any two of them would report a typed-in conjecture as part of the verified frontier.

## Recommended Milestones

Ordered by value per unit of work, following the build order above.

1. **Done.** Stable declaration records in the catalog export: name, denoted proposition, kind,
   catalog metadata, minimal dependencies, and audited axioms, at `schemaVersion` 2.
2. **Done.** `--json` on every one-shot command, and a typed `frontier.agent/v1` protocol for a
   warm environment. Native operations cover capabilities, environment description, attempt
   creation and history reads, declaration search, premise retrieval, independent batch tactic
   evaluation, proof-state inspection, and checked branch rehydration after a process restart.
   Typed proof states have durable attempt-scoped ids; process-local Lean state addresses are not
   serialized. Attempt-scoped retrievals and proof evaluations append their complete inputs and
   outcomes to the research event stream. Session responses expose a source-aware SHA-256
   environment fingerprint for pinning. `frontier check` remains the local propose-check-iterate
   loop that does not require editing the registry.
3. **Done.** Negative fixtures for the audit (`lake exe frontier-test`), including that a
   `sorry` and a `native_decide` are rejected in a draft. The gate is only worth what its
   rejections are worth, and those were previously untested.
4. **Done.** A durable local work journal (`frontier work`, `check --work`), published to
   `web/data/work.json` on every mutation and displayed by the workspace separately from
   audited results. This is the local half of staging; it needs no sandbox because it accepts
   nothing from anywhere. See the section above for why that is not the same as milestone 8.
5. Add an MCP server over `frontier serve`. A thin adapter now, not new infrastructure.
6. Extend lexical and symbolic ranking beyond the current IDF-weighted constant overlap, and
   record its hit rate so later work has a baseline.
7. **Done.** Retain the in-process `Elab.Tactic` proof-state interaction. It reuses the warm
   mathlib environment, and accepted scripts are replayed in one elaborator run so reported
   states match the assembled proof. Revisit an external REPL only if its isolation or
   maintenance benefits can justify loading a second environment.
8. Add proof submission staging with Lean validation and structured feedback — **only after the
   sandbox requirements above are met**, since this is the step that executes untrusted code.
   Note that `frontier check` builds submitted Lean in-process and is therefore a *local
   developer tool*, not a submission endpoint; pointing it at untrusted input without the
   sandbox above is exactly the arbitrary-code-execution hazard described in the previous
   section. The same applies to `frontier serve`, which speaks a request protocol and so is the
   component someone will be tempted to put behind a socket.
9. Add a promotion workflow for turning useful verified submissions into catalog entries.
10. Add embeddings, measured against the milestone 6 baseline.
