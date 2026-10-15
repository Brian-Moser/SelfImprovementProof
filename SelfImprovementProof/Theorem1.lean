/-
  Theorem 1: No Sound-and-Complete Improvement Certifier

  For the semantic score J(p) = 1{φ_p(0) halts and outputs 1},
  no total computable certifier V : Nat × Nat → {0,1} can be simultaneously
  sound (V(p,q)=1 ⟹ J(q)>J(p)) and complete (J(q)>J(p) ⟹ V(p,q)=1).

  Proof structure (follows the halting-problem diagonal):
    1. Fix a base program p with φ_p(0) = 0, so J(p) = 0.
    2. By s-m-n, build f mapping each e to a program that checks V(p,e) and flips.
    3. By Kleene's Recursion Theorem, get a fixed point q with φ_q = φ_{f(q)}.
    4. Case split on V(p,q): both cases yield a contradiction.
-/

import SelfImprovementProof.Defs

/-- Key diagonal lemma: for any certifier V and base program p,
    there exists a self-referential program q whose output on input 0
    is the flip of V's decision about q. -/
theorem diagonal_certifier (M : ComputationModel) (V : Nat → Nat → Bool) (p : Nat) :
    ∃ q, M.φ q 0 = if V p q then some 0 else some 1 := by
  -- Step 1: by s-m-n, get f such that φ(f(e), 0) = flip of V(p, e)
  obtain ⟨f, hf⟩ := M.smn_certifier V p
  -- Step 2: by Kleene's recursion theorem, get fixed point q
  obtain ⟨q, hq⟩ := M.kleene f
  -- Step 3: combine — φ(q, 0) = φ(f(q), 0) = flip of V(p, q)
  exact ⟨q, by rw [hq 0, hf q]⟩

/-- Helper: if φ(p, 0) = some 0, then J(p) = 0. -/
theorem J_eq_zero_of_output_zero (M : ComputationModel) {p : Nat}
    (h : M.φ p 0 = some 0) : J M p = 0 := by
  unfold J; simp [h]

/-- Helper: if φ(p, 0) = some 1, then J(p) = 1. -/
theorem J_eq_one_of_output_one (M : ComputationModel) {p : Nat}
    (h : M.φ p 0 = some 1) : J M p = 1 := by
  unfold J; simp [h]

/-- **Theorem 1** (No sound-and-complete improvement certifier).
    No total computable certifier V can simultaneously satisfy soundness
    and completeness for the semantic score J. -/
theorem no_sound_and_complete_certifier (M : ComputationModel) (V : Nat → Nat → Bool) :
    ¬ (CertifierSound M V ∧ CertifierComplete M V) := by
  intro ⟨hSound, hComplete⟩
  -- Fix a base program p with φ(p, 0) = some 0, so J(p) = 0
  obtain ⟨p, hp⟩ := M.exists_program_output_zero
  have hJp : J M p = 0 := J_eq_zero_of_output_zero M hp
  -- Diagonal construction: get q with φ(q,0) = flip of V(p,q)
  obtain ⟨q, hq⟩ := diagonal_certifier M V p
  -- Case split on V(p, q)
  cases hV : V p q with
  | false =>
    -- V(p, q) = false, so φ(q, 0) = some 1, hence J(q) = 1
    simp [hV] at hq
    have hJq : J M q = 1 := J_eq_one_of_output_one M hq
    -- Completeness requires V(p, q) = true, since J(q) = 1 > 0 = J(p)
    have hImproves : J M q > J M p := by omega
    have hVtrue := hComplete p q hImproves
    -- But V(p, q) = false, contradiction
    rw [hV] at hVtrue
    exact Bool.noConfusion hVtrue
  | true =>
    -- V(p, q) = true, so φ(q, 0) = some 0, hence J(q) = 0
    simp [hV] at hq
    have hJq : J M q = 0 := J_eq_zero_of_output_zero M hq
    -- Soundness requires J(q) > J(p), but both are 0
    have := hSound p q hV
    omega
