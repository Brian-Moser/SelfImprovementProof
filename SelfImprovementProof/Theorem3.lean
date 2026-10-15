/-
  Theorem 3: A Decidable Escape Hatch Under Bounded Evaluation

  Under two standard restrictions — bounded evaluation (at most T steps)
  and finite proposals (at most B candidates) — exhaustive simulation
  yields a terminating searcher that is sound and weakly complete
  with respect to the *bounded* score J_T.

  The diagonal construction from Theorems 1–2 breaks because the
  adversarial program q cannot embed the searcher S_{T,B} as a subroutine
  within its own T-step evaluation budget.
-/

import SelfImprovementProof.Defs

/-- The exhaustive bounded searcher (auxiliary, counting up from 0).
    Checks proposals at indices 0, 1, ..., fuel-1 and returns the
    first strict improvement w.r.t. the bounded score, or none. -/
noncomputable def exhaustiveSearchAux
    (eval : Nat → Nat → Nat → Option Nat) (Enum : EnumFamily)
    (T : Nat) (p : Nat) (e : Nat) (jP : Nat) : (idx : Nat) → (fuel : Nat) → Option Nat
  | _, 0 => none
  | idx, fuel + 1 =>
    let candidate := Enum e p idx
    let jC := J_bounded eval T candidate
    if jC > jP then some candidate
    else exhaustiveSearchAux eval Enum T p e jP (idx + 1) fuel

/-- Wrapper: search through proposals 0, 1, ..., B-1. -/
noncomputable def exhaustiveSearcher
    (eval : Nat → Nat → Nat → Option Nat) (Enum : EnumFamily)
    (T B : Nat) (p : Nat) (e : Nat) : Option Nat :=
  exhaustiveSearchAux eval Enum T p e (J_bounded eval T p) 0 B

/-- If the aux searcher returns some q, then J_bounded q > jP. -/
theorem exhaustiveSearchAux_sound
    (eval : Nat → Nat → Nat → Option Nat) (Enum : EnumFamily)
    (T : Nat) (p : Nat) (e : Nat) (jP : Nat) (idx fuel : Nat) (q : Nat) :
    exhaustiveSearchAux eval Enum T p e jP idx fuel = some q →
    J_bounded eval T q > jP := by
  induction fuel generalizing idx with
  | zero => simp [exhaustiveSearchAux]
  | succ n ih =>
    intro h
    simp only [exhaustiveSearchAux] at h
    split at h
    · next hgt => exact Option.some.inj h ▸ hgt
    · exact ih (idx + 1) h

/-- The exhaustive searcher is sound w.r.t. the bounded score J_T. -/
theorem exhaustiveSearcher_sound
    (eval : Nat → Nat → Nat → Option Nat) (Enum : EnumFamily) (T B : Nat) :
    ∀ p e q, exhaustiveSearcher eval Enum T B p e = some q →
      J_bounded eval T q > J_bounded eval T p := by
  intro p e q h
  exact exhaustiveSearchAux_sound eval Enum T p e _ 0 B q h

/-- If there's an improvement at some index in [idx, idx+fuel), the aux returns some. -/
theorem exhaustiveSearchAux_complete
    (eval : Nat → Nat → Nat → Option Nat) (Enum : EnumFamily)
    (T : Nat) (p : Nat) (e : Nat) (jP : Nat) (idx fuel : Nat) :
    (∃ j, j ≥ idx ∧ j < idx + fuel ∧ J_bounded eval T (Enum e p j) > jP) →
    exhaustiveSearchAux eval Enum T p e jP idx fuel ≠ none := by
  induction fuel generalizing idx with
  | zero =>
    intro ⟨j, _, hj, _⟩; omega
  | succ n ih =>
    intro ⟨j, hjge, hjlt, hj⟩
    simp only [exhaustiveSearchAux]
    split
    · simp  -- found an improvement at idx, done
    · next hle =>
      -- Didn't find at idx, recurse on [idx+1, idx+1+n)
      apply ih
      -- j must be > idx (since idx itself isn't an improvement)
      by_cases hjidx : j = idx
      · subst hjidx; exact absurd hj hle
      · exact ⟨j, by omega, by omega, hj⟩

/-- The exhaustive searcher is weakly complete w.r.t. the bounded score J_T. -/
theorem exhaustiveSearcher_weaklyComplete
    (eval : Nat → Nat → Nat → Option Nat) (Enum : EnumFamily) (T B : Nat) :
    ∀ p e, (∃ i, i < B ∧ J_bounded eval T (Enum e p i) > J_bounded eval T p) →
      exhaustiveSearcher eval Enum T B p e ≠ none := by
  intro p e ⟨i, hiB, hImprove⟩
  exact exhaustiveSearchAux_complete eval Enum T p e _ 0 B
    ⟨i, by omega, by omega, hImprove⟩

/-- **Theorem 3** (Sound and weakly complete total search under bounded
    horizon and finite proposals).

    Under bounded evaluation (T steps) and a finite proposal budget (B
    candidates), the exhaustive searcher is both sound and weakly complete
    with respect to the bounded score J_T.

    This is the "decidable escape hatch": bounding computation neutralizes
    the self-referential diagonal that drives Theorems 1 and 2. -/
theorem bounded_search_sound_and_weakly_complete
    (eval : Nat → Nat → Nat → Option Nat) (Enum : EnumFamily) (T B : Nat) :
    (∀ p e q, exhaustiveSearcher eval Enum T B p e = some q →
      J_bounded eval T q > J_bounded eval T p) ∧
    (∀ p e, (∃ i, i < B ∧ J_bounded eval T (Enum e p i) > J_bounded eval T p) →
      exhaustiveSearcher eval Enum T B p e ≠ none) :=
  ⟨exhaustiveSearcher_sound eval Enum T B,
   exhaustiveSearcher_weaklyComplete eval Enum T B⟩
