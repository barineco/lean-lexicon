# Lean Lexicon

[日本語](README-ja.md)

Formal verification of AT Protocol's Lexicon as a typed universe in Lean 4 / Mathlib.

**zero sorry, zero axiom, zero opaque.** Lean v4.29.0, Mathlib v4.29.0.

## Overview

Lexicon is recast as a **typed universe**. Each endpoint is a morphism between types; using an API means composing morphisms to reach a goal.

```
createSession: {identifier, password} → {accessJwt, did, ...}
getProfile:    {accessJwt, actor}     → {profileViewDetailed}
```

Composing the two yields `{identifier, password} → createSession → getProfile → {profileViewDetailed}`. This path is a **witness** for the operation sequence.

## Lean's Role

[Laplan](https://github.com/barineco/laplan)'s solver finds paths. Lean provides a **semantic guarantee** proof layer for those results, covering path correctness, constraint effects, and missing-information classification.

## Formalized Conclusions

### Paths and Reachability

- Paths are constructive proofs of reachability: the sequence of endpoint names returned by BFS forms a witness from the marking to the goal (Witness).
- Search soundness: `search` and `searchAll` return recipes that constitute constructive proofs of the Petri net reachability relation (Witness).
- Constraints refine reachability: adding annotations (subtype inclusion, ownership) strictly refines the path set (ConstraintProfiles).
- Annotations are non-recoverable from types: endpoints with identical code shapes are indistinguishable without annotations, yielding over-approximation at the pruning-only boundary (NonRecoverability).

### Preconditions and Needs Classification

- Preconditions are not input fields: implicit preconditions such as JWT or capability cannot be derived from input types alone (RequirementSatisfaction).
- Screen data requirements fall into 4 dispositions: `alreadySatisfied` / `witnessAvailable` / `recoverableByRecipe` / `needsUserAction`. Boundary-pruned requirements collapse into `needsUserAction` (Needs).

Precondition satisfaction sources fall into 5 kinds:

| Source | Example |
|---|---|
| User-provided | Password |
| Already in marking | Value from a previous operation |
| Other endpoint's output | Auth token returned by createSession |
| Derived from ownership | Own repo from login did |
| Derived from type inclusion | did → at-identifier |

### Universe Separation and Category Structure

- Lexicon₀ (types) / Lexicon₁ (morphisms) universe separation: encoding is non-canonical, presentation is not unique (Universe).
- Categorical structure of morphisms: associativity and left / right unit laws hold (Transition).
- Branching is a type-structure consequence: `if` reduces to union dispatch followed by morphism composition, not a new primitive (Transition).

### Monotonicity and Level Collapse

- Guard and fire monotonicity: monotone with respect to marking inclusion (WSTS membership) (Monotonicity).
- Consume-aware fire monotonicity: `(m \ C) ∪ P` is likewise monotone (Monotonicity).
- No inhibitor arcs: only positive membership tests are used; token addition never disables a transition (Monotonicity).
- Levels above Lex1 collapse: composition, branching, and enumeration all stay in Lex1. The distinction between Lex2 (functor) and Lex1 (morph) is observational granularity, not computational kind (Collapse).

### Termination

- Consume-aware path induction: `RichReachesBy` describes paths with exclusive consumption (Termination).
- Universe closure: fire stays within a finite fact universe (Termination).
- Visited-set termination: the search space is bounded by `2^|U|` and the gap strictly decreases at each step (Termination).
- Cycle revisit: consumes cycles return to the initial marking (basis for visited-set detection) (Termination).

### Bridge Mechanism

For two endpoints (`self_profile_from_login`, `feed_options`), the Bridge module strict-matches Rust solver recipes against Lean-side `search` / `searchAll` results. Judgments are existential / universal propositions, and compatibility is classified into shape / semantically / fully. The registry currently holds these 2 goals and 5 choices.

## Four Perspectives

**Tarski universe**: Lexicon schemas are type names (codes); endpoint behavior is type content (interpretation). Type names alone do not determine interpretation. Annotations fix interpretation.

**Petri net**: Endpoints are transitions, types are places, values are tokens. Firing an endpoint moves tokens. Reaching a goal token configuration is a reachability problem.

**Tactic mode**: API usage reads like a Lean proof. Apply endpoints to the goal (desired data), transforming hypotheses (held data) to close the goal. Unreachability corresponds to "unprovable under these premises."

**Category theory**: Endpoints as morphisms, types as objects form a category. Associativity, identity, and unit laws are proven. Codegen is a functor from this category to a target language category. Branching is derived from union dispatch and morphism composition.

## Module Structure

| File | Role |
|---|---|
| `Basic` | Base type definitions (TypeExpr: atom, array, object, union) |
| `Annotation` | Minimal annotations for preconditions and state effects |
| `AnnotationTable` | Per-endpoint annotation table |
| `Refinement` | Machine-derivable properties from type structure |
| `Canonical` | Machine derivation and annotation composition |
| `Interpretation` | Semantics from types and annotations to marking-level meaning |
| `Reachability` | Goal reachability judgment |
| `Search` | Bounded proof search |
| `Witness` | Search results read as reachability proofs |
| `ConstraintProfiles` | Reachability changes under constraint addition/removal |
| `NonRecoverability` | Proof that constraints cannot be recovered without annotations |
| `RequirementSatisfaction` | Precondition satisfaction source classification |
| `Needs` | Screen data classified as reachable or blocked |
| `Bridge` | Cross-validation against solver search results |
| `Universe` | Lexicon₀/₁ universe separation, encoding non-canonicity |
| `Transition` | Category structure, composition equivalence, type-level branching |
| `Monotonicity` | Guard and firing monotonicity; no inhibitor arcs (WSTS membership). Includes RichTransition (with consumes) monotonicity |
| `Termination` | Consume-aware model termination. Formal justification of visited-set search termination |
| `Collapse` | Levels above Lex1 collapse: composition, branching, enumeration all stay in Lex1 |

`*Demo`, `Observe`, `Diff`, `Materialize`, `GoalSelection` are concrete verification and experiment modules, not listed above.

### Dependencies

```text
Basic
├── Annotation
│   └── AnnotationTable
├── Refinement
│   └── Canonical
├── Interpretation
│   ├── Universe
│   └── Transition
├── Reachability
│   ├── Monotonicity [← Transition]
│   │   └── Termination
│   └── Search
│       └── Witness
│           ├── Bridge
│           └── Collapse [← Transition]
├── ConstraintProfiles
├── NonRecoverability
└── RequirementSatisfaction
    └── Needs
```

### Correspondence with Laplan Solver

| lean-lexicon | Laplan |
|---|---|
| `Basic` | Type definitions (`.lex` type declarations) |
| `Annotation` | Rule constraints (capability, consumes) |
| `Search` | Solver (BFS path search) |
| `Witness` | Recipe |
| `Needs` | `EndpointKind` endpoint diagnosis |
| `Monotonicity` (RichTransition) | Solver Execute mode (with consumes) |
| `Termination` (RichReachesBy) | Solver visited-set termination guarantee |
| `Collapse` | Solver max_depth parameter (justification for bounded search) |

## Build

```bash
lake build
```
