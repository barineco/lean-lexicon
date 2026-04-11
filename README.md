# Lean Lexicon

[日本語](README-ja.md)

Formal verification of AT Protocol's Lexicon as a typed universe in Lean 4 / Mathlib.

**183 theorems/lemmas, zero sorry.** Lean v4.29.0, Mathlib v4.29.0.

## Overview

Lexicon is recast as a **typed universe**. Each endpoint is a morphism between types; using an API means composing morphisms to reach a goal.

```
createSession: {identifier, password} → {accessJwt, did, ...}
getProfile:    {accessJwt, actor}     → {profileViewDetailed}
```

Composing the two yields `{identifier, password} → createSession → getProfile → {profileViewDetailed}`. This path is a **witness** for the operation sequence.

## Lean's Role

[Laplan](https://github.com/barineco/laplan)'s solver finds paths. Lean provides **semantic guarantees** for those results: a proof layer covering path correctness, constraint effects, and missing-information classification.

## Verified Theorems

### Paths and Reachability

| Theorem group | Module | Content |
|---|---|---|
| Paths are reachability proofs | Witness | A sequence of endpoint names constitutes a serial witness to the goal |
| Constraints change reachability | ConstraintProfiles | Adding subtype inclusion or ownership narrows the path count |
| Annotations are non-recoverable from types | NonRecoverability | Identical type structures yield different reachability under different annotations |

Constraint effects on concrete goals:

| Goal | Condition for path opening | Paths |
|---|---|---|
| Own profile retrieval | Subtype inclusion added | 1 |
| Own repo read | Ownership added | 1 |
| Own repo write | All constraints added | 1 |
| Feed retrieval | Invariant across constraints (structurally isomorphic) | 3 |

### Preconditions and Needs Assessment

| Theorem group | Module | Content |
|---|---|---|
| Preconditions ≠ input fields | RequirementSatisfaction | Implicit preconditions (JWT, etc.) do not appear in input fields |
| 5-layer needs assessment | Needs | Screen data requirements classified into 5 levels (verified across 8 screens) |

Precondition satisfaction sources:

| Source | Example |
|---|---|
| User-provided | Password |
| Already in marking | Value from a previous operation |
| Endpoint output | Auth token returned by createSession |
| Derived from ownership | Own repo from login did |
| Derived from type inclusion | did → at-identifier |

Five assessment layers:

| Assessment | Meaning |
|---|---|
| already satisfied | Already in marking |
| witness available | Reachable via serial recipe |
| recoverable by recipe | Recoverable with an additional recipe |
| needs user action | User interaction required |
| pruned by boundary | Annotation-side discriminator missing |

### Universe Separation and Category Structure

| Theorem group | Module | Content |
|---|---|---|
| Lexicon₀/₁ universe separation | Universe | Encoding non-canonicity (presentation method is non-unique) |
| Transition category structure | Transition | Associativity, unit laws, composition equivalence |
| Branching is a consequence of type structure | Transition | branch = union dispatch + morphism composition |

Key individual theorems:

| Theorem | Content |
|---|---|
| `encoding_noncanonical` | Two encodings return distinct LexValues |
| `no_injection_to_finite` | Injection into finite types is impossible |
| `Transition.seq_assoc` | Associativity of composition |
| `Transition.id_seq` / `seq_id` | Left and right unit laws |
| `timeline_equiv_follows_then_feed` | getTimeline ≈ getFollows ; map(getAuthorFeed) |
| `double_refresh_blocked` | Double use of refresh token is impossible (linear use) |
| `branch_is_dispatch_then_seq` | branch = union dispatch + morphism composition |
| `timed_filter_expiry` | Timed token expiry |

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
| `Canonical` | Machine derivation + annotation composition |
| `Interpretation` | Semantics from types + annotations to marking-level meaning |
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
│   └── Search
│       └── Witness
│           └── Bridge
├── ConstraintProfiles
├── NonRecoverability
└── RequirementSatisfaction
    └── Needs
```

### Correspondence with Laplan Solver

| lean-lexicon | Laplan |
|---|---|
| `Basic` | Type definitions (`.lex` type declarations) |
| `Annotation` | Morphism constraints (capability, consumes) |
| `Search` | Solver (BFS path search) |
| `Witness` | Serial recipe |
| `Needs` | Needs assessment (5-layer diagnostics) |

## Build

```bash
lake build
```
