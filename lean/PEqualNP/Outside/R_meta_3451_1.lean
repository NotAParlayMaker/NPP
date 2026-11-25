import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3451_1
    (hAO2 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ x y : Fin n → Bool, f x ≠ f y) →
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
      PEqualNP.MetaComplexity.circuitFun n C = f →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack n D →
        PEqualNP.MetaComplexity.circuitFun n D = f →
        C.size ≤ D.size) →
      PEqualNP.TopForm.IsAO2 n C)
    (hOneHot : ∀ (N : ℕ) (I : Fin N → Fin N → Prop),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      (∃ p l : Fin N, I p l) →
      have good : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun D =>
        PEqualNP.TopForm.IsAO2 (N + N) D ∧
        ∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true;
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        good C →
        (∀ D' : PEqualNP.CircuitLowerBounds.Circuit, good D' → C.size ≤ D'.size) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          good D ∧ D.size ≤ C.size ∧
          ∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
            ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false)
    (hNonInc : ∀ (N : ℕ) (I : Fin N → Fin N → Prop),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      (∃ p l : Fin N, I p l) →
      have good : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun D =>
        PEqualNP.TopForm.IsAO2 (N + N) D ∧
        ∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true;
      have oneHot : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun D =>
        ∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
          ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false;
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        good C →
        (∀ D' : PEqualNP.CircuitLowerBounds.Circuit, good D' → C.size ≤ D'.size) →
        oneHot C →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          good D ∧ D.size ≤ C.size ∧ oneHot D ∧
          ∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            ∀ p0 l0 : Fin N, ¬ I p0 l0 →
              (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  intro N I _ C h4 hM hR hF
  by_cases hEdge : ∃ p l : Fin N, I p l
  · have hAO_to_mono : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (N + N) D →
        PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D := by
      intro D hD
      refine ⟨fun g hg => ⟨?_, ?_⟩, hD.2.1⟩
      · exact Or.elim (hD.1 g hg) (fun h => by simp [h]) (fun h => by simp [h])
      · rw [hD.2.2 g hg]
    have hmin_ex : ∀ k : ℕ, ∀ C' : PEqualNP.CircuitLowerBounds.Circuit,
        C'.size = k →
        PEqualNP.MetaComplexity.Monotone2 C' →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C' →
        (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C' z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        ∃ C0 : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 C0 ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C0 ∧
          C0.size ≤ C'.size ∧
          (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C0 z = true ↔
            ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
          ∀ D' : PEqualNP.CircuitLowerBounds.Circuit,
            PEqualNP.MetaComplexity.Monotone2 D' →
            PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D' →
            (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D' z = true ↔
              ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
            C0.size ≤ D'.size := by
      intro k
      refine Nat.strongRecOn k ?_
      intro k ih C' hsz hm hr hf
      by_cases hlt : ∃ C'' : PEqualNP.CircuitLowerBounds.Circuit,
          C''.size < k ∧
          PEqualNP.MetaComplexity.Monotone2 C'' ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C'' ∧
          (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C'' z = true ↔
            ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
      · exact hlt.elim fun C'' hC'' =>
          (ih C''.size hC''.1 C'' rfl hC''.2.1 hC''.2.2.1 hC''.2.2.2).elim fun C0 hC0 =>
            ⟨C0, hC0.1, hC0.2.1, le_trans hC0.2.2.1 (by have := hC''.1; omega), hC0.2.2.2.1, hC0.2.2.2.2⟩
      · refine ⟨C', hm, hr, le_rfl, hf, fun D' hm' hr' hf' => ?_⟩
        by_contra hgt
        exact hlt ⟨D', by omega, hm', hr', hf'⟩
    exact (hmin_ex C.size C rfl hM hR hF).elim fun C0 hC0 => by
      have hm0 := hC0.1
      have hr0 := hC0.2.1
      have hle0 := hC0.2.2.1
      have hf0 := hC0.2.2.2.1
      have hmin0 := hC0.2.2.2.2
      have hnonconst : ∃ x y : Fin (N + N) → Bool,
          PEqualNP.MetaComplexity.circuitFun (N + N) C0 x ≠
          PEqualNP.MetaComplexity.circuitFun (N + N) C0 y := by
        refine ⟨fun _ => false, fun _ => true, ?_⟩
        have hfx : PEqualNP.MetaComplexity.circuitFun (N + N) C0 (fun _ => false) = false :=
          Bool.eq_false_iff.mpr fun hv =>
            ((hf0 (fun _ => false)).mp hv).elim fun _ hp =>
              hp.elim fun _ hl => Bool.noConfusion hl.2.1
        have hfy : PEqualNP.MetaComplexity.circuitFun (N + N) C0 (fun _ => true) = true :=
          hEdge.elim fun p hp => hp.elim fun l hpl => (hf0 (fun _ => true)).mpr ⟨p, l, hpl, rfl, rfl⟩
        rw [hfx, hfy]
        decide
      have hAO0 : PEqualNP.TopForm.IsAO2 (N + N) C0 := by
        refine hAO2 (N + N) (PEqualNP.MetaComplexity.circuitFun (N + N) C0) C0 hnonconst hm0 hr0 rfl ?_
        intro D' hm' hr' hfeq
        refine hmin0 D' hm' hr' (fun z => ?_)
        rw [congrFun hfeq z]
        exact hf0 z
      have hminAO0 : ∀ D' : PEqualNP.CircuitLowerBounds.Circuit,
          (PEqualNP.TopForm.IsAO2 (N + N) D' ∧
            ∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D' z = true ↔
              ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
          C0.size ≤ D'.size := by
        intro D' hD'
        have hmr := hAO_to_mono D' hD'.1
        exact hmin0 D' hmr.1 hmr.2 hD'.2
      exact (hOneHot N I h4 hEdge C0 ⟨hAO0, hf0⟩ hminAO0).elim fun D1 hD1 => by
        have hminAO1 : ∀ D' : PEqualNP.CircuitLowerBounds.Circuit,
            (PEqualNP.TopForm.IsAO2 (N + N) D' ∧
              ∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D' z = true ↔
                ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
            D1.size ≤ D'.size :=
          fun D' hD' => le_trans hD1.2.1 (hminAO0 D' hD')
        exact (hNonInc N I h4 hEdge D1 hD1.1 hminAO1 hD1.2.2).elim fun D hD => by
          have hmrD := hAO_to_mono D hD.1.1
          exact ⟨D, hmrD.1, hmrD.2, le_trans hD.2.1 (le_trans hD1.2.1 hle0), hD.1.2, hD.2.2.2, hD.2.2.1⟩
  · refine ⟨{ gates := [], output := N + N }, ?_, ?_, Nat.zero_le _, ?_, ?_, ?_⟩
    · intro _ h
      exact False.elim (List.not_mem_nil h)
    · intro _ h
      exact absurd h (Nat.not_lt_zero _)
    · intro z
      refine ⟨fun htr => ?_, fun hex => hex.elim fun p hp => hp.elim fun l hl => absurd ⟨p, l, hl.1⟩ hEdge⟩
      have hfl : PEqualNP.MetaComplexity.circuitFun (N + N) { gates := [], output := N + N } z = false := by
        unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
        simp
      rw [hfl] at htr
      exact Bool.noConfusion htr
    · intro _ h
      exact absurd h (Nat.not_lt_zero _)
    · intro _ h
      exact absurd h (Nat.not_lt_zero _)
