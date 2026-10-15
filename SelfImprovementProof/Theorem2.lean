/-
  Theorem 2: No Sound-and-Weakly-Complete Proposal-Respecting Searcher

  Even replacing certification with search does not help: for every
  proposal-respecting total computable searcher S, there exists an
  adversarial enumerator that forces S to violate soundness or weak
  completeness.

  Proof structure:
    1. Fix base p with J(p) = 0.
    2. By the searcher diagonal axiom (s-m-n + Kleene), obtain a fixed-point
       enumerator index e* and adversarial candidate q with:
       - Enum(e*, p, 0) = q  and  Enum(e*, p, i) = p for i > 0
       - φ(q, 0) flips based on whether S(p, e*) returns q
    3. Case split on S(p, e*): both cases yield a contradiction.
-/

import SelfImprovementProof.Defs

-- Re-use helpers from Theorem1
import SelfImprovementProof.Theorem1

/-- **Theorem 2** (No sound-and-weakly-complete searcher).
    For the fixed score J, no proposal-respecting total computable
    searcher S is simultaneously sound and weakly complete for all
    enumerators. -/
theorem no_sound_and_weakly_complete_searcher (M : ComputationModel)
    (S : Nat → Nat → Option Nat)
    (Enum : EnumFamily)
    (hResp : ProposalRespecting S Enum) :
    ¬ (SearcherSound M S ∧ SearcherWeaklyComplete M S Enum) := by
  intro ⟨hSound, hWComplete⟩
  -- Fix base program p with φ(p, 0) = some 0, so J(p) = 0
  obtain ⟨p, hp⟩ := M.exists_program_output_zero
  have hJp : J M p = 0 := J_eq_zero_of_output_zero M hp
  -- Searcher diagonal: get e*, q with the flip property
  obtain ⟨eStar, q, hEnum0, hEnumRest, hFlip⟩ := M.searcher_diagonal S Enum p
  -- Case split on whether S(p, e*) = some q
  by_cases hS : S p eStar = some q
  · -- Case A: S(p, e*) = some q
    -- Then φ(q, 0) = some 0, so J(q) = 0
    simp [hS] at hFlip
    have hJq : J M q = 0 := J_eq_zero_of_output_zero M hFlip
    -- But soundness requires J(q) > J(p), and both are 0
    have := hSound p eStar q hS
    omega
  · -- Case B: S(p, e*) ≠ some q
    -- Then φ(q, 0) = some 1, so J(q) = 1 > 0 = J(p)
    simp [hS] at hFlip
    have hJq : J M q = 1 := J_eq_one_of_output_one M hFlip
    have hImproves : J M q > J M p := by omega
    -- q = Enum(e*, p, 0), so ∃ i, J(Enum(e*, p, i)) > J(p)
    have hExists : ∃ i, J M (Enum eStar p i) > J M p :=
      ⟨0, hEnum0 ▸ hImproves⟩
    -- By weak completeness, S(p, e*) ≠ none
    have hNotNone := hWComplete p eStar hExists
    -- S(p, e*) = some q' for some q'
    match hSome : S p eStar with
    | none => exact absurd hSome hNotNone
    | some q' =>
      -- q' ≠ q (since S p eStar ≠ some q)
      have hNeq : q' ≠ q := by
        intro heq; subst heq; exact hS hSome
      -- q' is proposal-respecting: q' = Enum(e*, p, i) for some i
      obtain ⟨i, hi⟩ := hResp p eStar q' hSome
      -- If i = 0, then q' = Enum(e*, p, 0) = q, contradicting q' ≠ q
      -- If i > 0, then q' = p, so J(q') = J(p), contradicting soundness
      by_cases hi0 : i = 0
      · subst hi0; rw [hEnum0] at hi; exact absurd hi hNeq
      · have hpos : i > 0 := Nat.pos_of_ne_zero hi0
        rw [hEnumRest i hpos] at hi
        -- q' = p, so J(q') = J(p), but soundness says J(q') > J(p)
        have := hSound p eStar q' hSome
        rw [hi] at this
        omega
