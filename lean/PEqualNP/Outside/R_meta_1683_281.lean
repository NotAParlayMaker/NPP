import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_1683_281
    (orbitCircuit :
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
        (∀ (t : Fin 13) (x y : Fin (13 + 13) → Bool),
          (∀ p, x (Fin.castAdd 13 p) = y (Fin.castAdd 13 (p + t))) →
          (∀ w, x (Fin.natAdd 13 w) = y (Fin.natAdd 13 (w + t))) →
          circuitFun 26 C x = circuitFun 26 C y) ∧
        (∀ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)),
          circuitFun 26 C (fun k => decide (k = Fin.castAdd 13 d ∨ k = Fin.natAdd 13 (0 : Fin 13))) = true) ∧
        (∀ m ∈ ([(0,8191),(1,3054),(3,972),(5,2984),(9,2914),(11,832),(17,2788),
          (33,2506),(49,2240),(65,2950),(145,548),(161,266),(207,768),(349,2560),
          (467,516),(629,2176),(873,2050),(1191,264),(1917,2048),(8191,0)] : List (ℕ × ℕ)),
          circuitFun 26 C (fun k => Fin.addCases (motive := fun _ => Bool)
            (fun p : Fin 13 => m.1.testBit p.val) (fun w : Fin 13 => m.2.testBit w.val) k) = false))
    (orbitTable :
      let I : Fin 13 → Fin 13 → Prop := fun p w =>
        ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd
      ∀ P : Finset (Fin 13),
        (∀ v : Fin 13, v ∉ P → ∃ w : Fin 13, (∀ p ∈ P, ¬ I p w) ∧ I v w) →
        ((∃ w : Fin 13, ∀ p ∈ P, I p w) ∨
          (∃ v : Fin 13, ∀ w : Fin 13, (∀ p ∈ P, ¬ I p w) → I v w)) →
        ∃ m ∈ ([(0,8191),(1,3054),(3,972),(5,2984),(9,2914),(11,832),(17,2788),
          (33,2506),(49,2240),(65,2950),(145,548),(161,266),(207,768),(349,2560),
          (467,516),(629,2176),(873,2050),(1191,264),(1917,2048),(8191,0)] : List (ℕ × ℕ)),
          ∃ t : Fin 13,
            (∀ p : Fin 13, decide (p + t ∈ P) = m.1.testBit p.val) ∧
            (∀ w : Fin 13, decide (∀ p ∈ P, ¬ I p (w + t)) = m.2.testBit w.val)) :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)) := by
  obtain ⟨C, hmono, hsize, hshift, hpos, hneg⟩ := orbitCircuit
  have apart (p w : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 w := by
    intro he
    have hl := p.isLt
    have hv := congrArg Fin.val he
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have apart' (w p : Fin 13) : Fin.natAdd 13 w ≠ Fin.castAdd 13 p :=
    (apart p w).symm
  have pc (i j : Fin 13) : Fin.castAdd 13 i = Fin.castAdd 13 j ↔ i = j := by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun j : Fin (13 + 13) => j.val) h)
    · exact congrArg (Fin.castAdd 13)
  have lc (i j : Fin 13) : Fin.natAdd 13 i = Fin.natAdd 13 j ↔ i = j := by
    constructor
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd] at hv
      exact Fin.ext (Nat.add_left_cancel hv)
    · exact congrArg (Fin.natAdd 13)
  have decEq (a b : Prop) [Decidable a] [Decidable b] (h : a ↔ b) :
      decide a = decide b := by
    by_cases ha : a
    · have hb := h.mp ha
      simp [ha, hb]
    · have hb : ¬ b := fun htrue => ha (h.mpr htrue)
      simp [ha, hb]
  refine ⟨C, hmono, hsize, ?_, ?_⟩
  · intro p w hp
    obtain ⟨d, hd, rfl⟩ := hp
    let x : Fin (13 + 13) → Bool := fun k =>
      decide (k = Fin.castAdd 13 d ∨ k = Fin.natAdd 13 (0 : Fin 13))
    let y : Fin (13 + 13) → Bool := fun k =>
      decide (k = Fin.castAdd 13 (w + d) ∨ k = Fin.natAdd 13 w)
    change circuitFun 26 C y = true
    have heq : circuitFun 26 C x = circuitFun 26 C y := by
      apply hshift w
      · intro i
        have hi : i + w = w + d ↔ i = d := by
          rw [add_comm w d, add_right_cancel_iff]
        simp only [x, y, pc, apart, or_false, hi]
      · intro i
        have hi : i + w = w ↔ i = 0 := by
          simpa only [zero_add] using (add_right_cancel_iff : i + w = 0 + w ↔ i = 0)
        simp only [x, y, lc, apart', false_or, hi]
    exact heq.symm.trans (hpos d hd)
  · intro P hmax hdeg
    obtain ⟨m, hm, t, hpoint, hline⟩ := orbitTable P hmax hdeg
    let I : Fin 13 → Fin 13 → Prop := fun p w =>
      ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd
    let x : Fin (13 + 13) → Bool := fun k => Fin.addCases (motive := fun _ => Bool)
      (fun p : Fin 13 => m.1.testBit p.val) (fun w : Fin 13 => m.2.testBit w.val) k
    let y : Fin (13 + 13) → Bool := fun k =>
      decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
        (∃ w : Fin 13, k = Fin.natAdd 13 w ∧ (∀ p ∈ P, ¬ I p w)))
    have ypoint (i : Fin 13) : y (Fin.castAdd 13 i) = decide (i ∈ P) := by
      apply decEq
      constructor
      · intro h
        rcases h with ⟨p, hp, he⟩ | ⟨w, he, _⟩
        · have heq := (pc i p).mp he
          subst p
          exact hp
        · exact (apart i w he).elim
      · intro h
        exact Or.inl ⟨i, h, rfl⟩
    have yline (i : Fin 13) : y (Fin.natAdd 13 i) = decide (∀ p ∈ P, ¬ I p i) := by
      apply decEq
      constructor
      · intro h
        rcases h with ⟨p, _, he⟩ | ⟨w, he, hw⟩
        · exact (apart p i he.symm).elim
        · have heq := (lc i w).mp he
          subst w
          exact hw
      · intro h
        exact Or.inr ⟨i, rfl, h⟩
    change circuitFun 26 C y = false
    have heq : circuitFun 26 C x = circuitFun 26 C y := by
      apply hshift t
      · intro i
        simpa only [x, Fin.addCases_left, ypoint] using (hpoint i).symm
      · intro i
        simpa only [x, Fin.addCases_right, yline] using (hline i).symm
    exact heq.symm.trans (hneg m hm)
