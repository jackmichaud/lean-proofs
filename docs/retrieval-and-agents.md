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

1. **Read-only MCP tools** over the existing export. The catalog JSON already carries names,
   propositions, dependencies, axioms, and status; wrapping it is a small amount of work and
   immediately useful to any agent.
2. **Lexical and symbolic retrieval over mathlib.** `frontier suggest` already does IDF-weighted
   constant overlap. Extending that — namespace locality, graph distance, type-shape matching —
   is cheap and, for premise selection, competitive with dense retrieval. Hybrid systems beat
   pure vector search on this task consistently; build the lexical half first so there is a
   baseline to beat.
3. **Proof-state interaction**, by wrapping the existing Lean REPL rather than writing one.
   `leanprover-community/repl` and LeanDojo already solve environment setup, tactic execution,
   and goal serialization. A hand-rolled interaction layer is a large amount of work that
   duplicates maintained tooling and drifts on every toolchain bump.
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
| Retrieval index | embeddings, lexical indexes, graph indexes | no |
| Submission queue | agent drafts, failures, proof traces | no |

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

## Recommended Milestones

Ordered by value per unit of work, following the build order above.

1. **Done.** Stable declaration records in the catalog export: name, denoted proposition, kind,
   catalog metadata, minimal dependencies, and audited axioms, at `schemaVersion` 2.
2. Add an MCP server with read-only search and inspection tools over that export. No new
   infrastructure required.
3. Extend lexical and symbolic ranking beyond the current IDF-weighted constant overlap, and
   record its hit rate so later work has a baseline.
4. Wrap `leanprover-community/repl` for proof-state interaction. Do not write one.
5. Add proof submission staging with Lean validation and structured feedback — **only after the
   sandbox requirements above are met**, since this is the step that executes untrusted code.
6. Add a promotion workflow for turning useful verified submissions into catalog entries.
7. Extend the web workspace to browse trusted results and staged submissions separately.
8. Add embeddings, measured against the milestone 3 baseline.
