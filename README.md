# SelfImprovementProof

A Lean 4 mechanization of the impossibility and decidability results from
*The Self-Improvement Problem*.

## What is proved

- **Theorem 1** — No total computable certifier is simultaneously sound and
  complete for strict semantic improvement.
- **Theorem 2** — No proposal-respecting total computable searcher is
  simultaneously sound and weakly complete across all proposal enumerators.
- **Theorem 3** — Under bounded evaluation (`T` steps) and a finite proposal
  budget (`B` candidates), an exhaustive searcher is sound and weakly
  complete with respect to the bounded score `J_T`.

## Project structure

```
SelfImprovementProof/
├── lakefile.toml                      Lake build configuration
├── lean-toolchain                     Pinned Lean version (v4.29.0)
├── Main.lean                          Executable entry point
├── SelfImprovementProof.lean          Library root
└── SelfImprovementProof/
    ├── Basic.lean                     Re-exports all modules
    ├── Defs.lean                      ComputationModel, J, J_bounded,
    │                                  soundness/completeness predicates
    ├── Theorem1.lean                  Diagonal certifier impossibility
    ├── Theorem2.lean                  Diagonal searcher impossibility
    └── Theorem3.lean                  Bounded exhaustive searcher (positive)
```

## Building

Requires [`elan`](https://github.com/leanprover/elan) (the Lean version
manager). Lean 4.29.0 will be fetched automatically based on
`lean-toolchain`.

```bash
lake build
```

To run the executable stub:

```bash
lake exe selfimprovementproof
```

## Scope of the formalization

The development is structured around an abstract `ComputationModel`
(see `Defs.lean`) that axiomatizes:

- a universal partial computable function `φ`,
- the existence of programs that halt on input 0 with outputs 0 and 1,
- **Kleene's Recursion Theorem** (fixed-point property),
- two `s-m-n`–style construction principles used for the diagonal
  arguments in Theorems 1 and 2.

Given these closure properties, the case-analysis structure of all three
proofs is mechanically checked. The recursion-theoretic infrastructure
itself is taken as axiomatic; it is classical and could in principle be
discharged against Mathlib's `Computability.Partrec`. Theorem 3
constructs the exhaustive searcher concretely and proves both soundness
and weak completeness by induction on the proposal budget.
