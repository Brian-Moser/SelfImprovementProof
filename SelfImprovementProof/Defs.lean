/-
  The Self-Improvement Problem — Formalization in Lean 4

  This formalizes the impossibility results from "The Self-Improvement Problem":
  no total computable certifier/searcher can be simultaneously sound and complete
  for semantic improvement, when candidates can self-reference the gate.

  The proof follows the structure of the halting problem: assume a decider exists,
  build a self-referential program that does the opposite, derive contradiction.
  Self-reference is achieved via Kleene's Recursion Theorem.
-/

/-- An acceptable computation model axiomatizing partial computable functions,
    Kleene's Recursion Theorem, and basic program construction (s-m-n). -/
structure ComputationModel where
  /-- Universal partial computable function: `φ p x` is the result of
      running program `p` on input `x`. `none` means divergence. -/
  φ : Nat → Nat → Option Nat

  /-- There exists a program that halts on input 0 and outputs 0. -/
  exists_program_output_zero : ∃ p, φ p 0 = some 0

  /-- There exists a program that halts on input 0 and outputs 1. -/
  exists_program_output_one : ∃ p, φ p 0 = some 1

  /-- Kleene's Recursion Theorem (Fixed-Point Theorem):
      For any total computable function `f : Nat → Nat`, there exists an index `e`
      such that programs `e` and `f(e)` have identical behavior on all inputs. -/
  kleene : ∀ f : Nat → Nat, ∃ e, ∀ x, φ e x = φ (f e) x

  /-- s-m-n–like construction for certifier diagonalization:
      Given any total computable certifier `V` and a base program `p`,
      there is a total computable function `f` that maps each index `e` to
      a program `f(e)` which on input 0 evaluates `V(p, e)` and flips:
      outputs 0 when V accepts, outputs 1 when V rejects. -/
  smn_certifier : ∀ (V : Nat → Nat → Bool) (p : Nat),
    ∃ f : Nat → Nat, ∀ e, φ (f e) 0 = if V p e then some 0 else some 1

  /-- Combined diagonal for the searcher (Theorem 2):
      consequence of s-m-n (searcher + enumerator wrapping) composed with Kleene.
      Given a searcher S, an enumerator family Enum, and a base program p,
      there exist a fixed-point enumerator index eStar and candidate q such that:
      - q is the first proposal for p under eStar
      - all other proposals for p under eStar are just p itself
      - q's output on input 0 flips based on whether S returns q -/
  searcher_diagonal : ∀ (S : Nat → Nat → Option Nat) (Enum : Nat → Nat → Nat → Nat) (p : Nat),
    ∃ eStar q,
      Enum eStar p 0 = q ∧
      (∀ i, i > 0 → Enum eStar p i = p) ∧
      φ q 0 = if S p eStar = some q then some 0 else some 1

/-! ## Semantic score functional -/

/-- The semantic score: `J(p) = 1` if program `p` halts on input 0 and
    outputs 1, and `J(p) = 0` otherwise. This may be uncomputable. -/
noncomputable def J (M : ComputationModel) (p : Nat) : Nat :=
  if M.φ p 0 = some 1 then 1 else 0

/-! ## Certifier definitions (Theorem 1) -/

/-- A certifier is sound if it only accepts strict improvements. -/
def CertifierSound (M : ComputationModel) (V : Nat → Nat → Bool) : Prop :=
  ∀ p q, V p q = true → J M q > J M p

/-- A certifier is complete if it accepts all strict improvements. -/
def CertifierComplete (M : ComputationModel) (V : Nat → Nat → Bool) : Prop :=
  ∀ p q, J M q > J M p → V p q = true

/-! ## Searcher definitions (Theorem 2) -/

/-- A proposal enumerator family: `Enum e p i` is the `i`-th proposal
    from enumerator `e` for base agent `p`. -/
abbrev EnumFamily := Nat → Nat → Nat → Nat

/-- A searcher is proposal-respecting if any returned candidate
    appears in the enumerator's proposal list. -/
def ProposalRespecting (S : Nat → Nat → Option Nat) (Enum : EnumFamily) : Prop :=
  ∀ p e q, S p e = some q → ∃ i, q = Enum e p i

/-- A searcher is sound if every returned candidate is a strict improvement. -/
def SearcherSound (M : ComputationModel) (S : Nat → Nat → Option Nat) : Prop :=
  ∀ p e q, S p e = some q → J M q > J M p

/-- A searcher is weakly complete if it finds *some* improvement whenever
    the enumerator's proposals contain one. -/
def SearcherWeaklyComplete (M : ComputationModel) (S : Nat → Nat → Option Nat)
    (Enum : EnumFamily) : Prop :=
  ∀ p e, (∃ i, J M (Enum e p i) > J M p) → S p e ≠ none

/-! ## Bounded evaluation definitions (Theorem 3) -/

/-- Bounded score: `J_bounded eval T p = 1` if evaluating program `p` on input 0
    for at most `T` steps yields output 1, and 0 otherwise. -/
noncomputable def J_bounded (eval : Nat → Nat → Nat → Option Nat) (T : Nat) (p : Nat) : Nat :=
  if eval p 0 T = some 1 then 1 else 0
