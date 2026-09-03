# Frontier graph model

Frontier treats mathematical work as a hierarchy of graphs. Lean remains the verifier, but the
surrounding system can use graph structure for retrieval, audit, search, and user-facing research
navigation.

```text
mathematical knowledge graph
        |
        v
proof dependency graph
        |
        v
fine-grained proof graph
        |
        v
Lean kernel verification
```

## Knowledge Graph

The knowledge graph is the broad mathematical map. Nodes are concepts, theories, definitions,
named results, proof techniques, and research areas. Edges describe mathematical relationships such
as `specializes`, `generalizes`, `defines`, `motivates`, `analogous-to`, and `used-in-area`.

This graph is not itself trusted evidence for a theorem. Its job is retrieval and orientation:
given a goal about finite fields, it should point toward `ZMod`, cyclic groups, finite field
theorems, Fermat-style lemmas, and related catalog entries.

Initial Frontier representation:

- catalog topics and tags
- Lean declaration names and pretty-printed propositions
- future semantic embeddings or literature links

## Dependency Graph

The proof dependency graph is the current checked Frontier graph. Nodes are catalog entries and
Lean declarations. Edges mean `uses`, directed from dependency to dependent result.

```text
axiom/definition/lemma --> theorem
```

For registered results, Frontier derives catalog dependencies from the constants the certificate
transitively uses. The walk stops descending at a registered declaration, so the recorded edges
are to *minimal* catalog ancestors. A five-step chain therefore renders as a chain rather than as
a complete graph, and "which result does this directly reuse" has a meaningful answer.

Axiom collection deliberately does not stop at registered declarations: an axiom must be audited
however many catalog entries it passes beneath. Frontier audits the axioms of statements and
sanity checks as well as certificates, and enforces an allowlist rather than merely reporting
what it finds. See [architecture.md](architecture.md#axiom-policy).

This graph answers questions such as:

- Which registered results does this theorem reuse?
- Which results depend on this lemma?
- Which axioms support this certificate?
- Does any closed certificate transitively depend on `sorryAx`?

This level is excellent for trust audit and premise retrieval, but too coarse to model proof
generation by itself.

## Reuse Loop

Reuse is the main operational payoff of the graph. Once Lean verifies a theorem, Frontier can treat
it as a reusable node instead of rediscovering its proof. The durable loop is:

```text
prove --> verify --> store --> retrieve --> prove harder results
```

For a new goal, the system should:

1. retrieve relevant existing nodes, including definitions, axioms, lemmas, and theorems
2. search for a proof using those results plus new intermediate steps
3. ask Lean to verify every proposed proof transition
4. store useful new intermediate results as named Lean declarations when they are broadly reusable
5. expose those declarations to later retrieval and proof search

The dependency graph also gives transitive context. If a target resembles a known theorem, its
neighborhood can reveal supporting lemmas, definitions, and earlier results that are not obvious
from name search alone.

## Proof Graph

The fine-grained proof graph models proof search. Nodes are Lean proof states, and edges are
verified transitions produced by tactics, term elaboration, rewriting, simplification, induction,
or calls to known theorems.

```text
proof state -- valid inference --> proof state -- valid inference --> solved
```

Each edge should carry enough data to replay or audit the transition:

- input goals and local context
- action kind, such as tactic, term, rewrite, theorem application, or split
- generated subgoals
- referenced declarations
- Lean result: accepted, rejected, timeout, or error
- cost and heuristic score

Lean verifies every accepted transition. The AI layer proposes actions, ranks branches, and chooses
where to search next, but it does not become part of the trust base.

## Search Architecture

Given a formal goal, proof generation becomes graph search over Lean-checked transitions:

```text
goal proposition
      |
      v
initial proof state
      |
      v
candidate action generation
      |
      v
Lean verifies transition
      |
      v
new proof states
```

Useful search strategies include best-first search, beam search, Monte Carlo tree search, learned
premise selection, theorem retrieval, and LLM-guided tactic proposal. The dependency graph supplies
trusted reusable premises. The knowledge graph supplies broader mathematical context.

The central retrieval problem is premise selection: given one proof goal and a large graph of
verified mathematics, identify the small set of declarations most likely to unlock a proof.
Frontier can combine several signals without changing the trust model:

- symbolic overlap between the goal and candidate theorem types
- graph distance from related catalog nodes
- tags, topics, namespaces, and imported modules
- transitive dependency neighborhoods
- successful historical proof-search traces
- learned embeddings or ranking models

These signals only rank candidates. A retrieved premise becomes part of a proof only when Lean
accepts the resulting term or tactic transition.

For the agent-facing retrieval and submission interface around these graphs, see
[retrieval-and-agents.md](retrieval-and-agents.md).

## Data Boundaries

Frontier should keep these graph levels distinct:

| Level | Trusted? | Primary Use |
| --- | --- | --- |
| Knowledge graph | No | retrieval, discovery, topic navigation |
| Dependency graph | Kernel-audited after extraction | trust audit, reuse lineage, impact analysis |
| Proof graph | Trusted only per Lean-accepted transition | automated proving and proof reconstruction |

The durable certificate is still a Lean declaration. Search traces are operational artifacts: useful
for debugging, training, replay, and ranking, but not a substitute for a compiled proof.

## Near-Term Milestones

1. **Done.** Minimal-ancestor catalog dependency graph, with axiom auditing under an enforced
   allowlist.
2. Add stable JSON fields for graph nodes and edges when downstream tools need them.
3. Record failed and successful proof-search transitions outside the trusted catalog.
4. Promote successful proof traces into ordinary Lean source files.
5. Validate the resulting declarations through `frontier validate`.

Proof-search transitions should come from wrapping the existing Lean REPL rather than a
bespoke interaction layer; see the build order in
[retrieval-and-agents.md](retrieval-and-agents.md#build-order).
