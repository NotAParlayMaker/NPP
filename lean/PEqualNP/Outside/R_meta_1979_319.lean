import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Prove monotonicity of Monotone2 circuits and greedy extension of any generic false pair
-- (P, W) to a maximal generic false pair of PG(2,3). This reduces L-meta-1979 to:
-- (1) classifying maximal generic false pairs into the 8 orbit reps under <Z/13Z, *3, duality>,
-- (2) synthesizing a <=63-gate Monotone2 circuit on the 52 incident pairs and 8 orbit families.
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_1979_319
    (hOrbit :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let reps : List (ℕ × ℕ) :=
        [(7, 904), (13, 2848), (19, 708), (21, 2720), (25, 2656), (37, 2440), (41, 2370), (133, 808)]
      let row := fun (z : ℕ × ℕ) (m t : Fin 13) (dual : Bool) =>
        let bit := fun (a b : ℕ) (i : Fin 13) =>
          if dual then b.testBit (-(m * i + t)).val else a.testBit (m * i + t).val
        Fin.append (bit z.1 z.2) (bit z.2 z.1)
      let ok := fun (P W : Finset (Fin 13)) =>
        (∀ p ∈ P, ∀ w ∈ W, p - w ∉ D) ∧
        (∀ w : Fin 13, (P.filter fun p => p - w ∈ D).card ≤ 2) ∧
        (∀ p : Fin 13, (W.filter fun w => p - w ∈ D).card ≤ 2)
      ∀ P W : Finset (Fin 13), ok P W →
        (∀ p : Fin 13, p ∉ P → ¬ ok (insert p P) W) →
        (∀ w : Fin 13, w ∉ W → ¬ ok P (insert w W)) →
        ∃ z ∈ reps, ∃ m ∈ ([1, 3, 9] : List (Fin 13)), ∃ t : Fin 13, ∃ dual : Bool,
          (fun i : Fin (13 + 13) => decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨
            (∃ w ∈ W, i = Fin.natAdd 13 w))) = row z m t dual)
    (hSynth :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let reps : List (ℕ × ℕ) :=
        [(7, 904), (13, 2848), (19, 708), (21, 2720), (25, 2656), (37, 2440), (41, 2370), (133, 808)]
      let row := fun (z : ℕ × ℕ) (m t : Fin 13) (dual : Bool) =>
        let bit := fun (a b : ℕ) (i : Fin 13) =>
          if dual then b.testBit (-(m * i + t)).val else a.testBit (m * i + t).val
        Fin.append (bit z.1 z.2) (bit z.2 z.1)
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
        (∀ p w : Fin 13, p - w ∈ D →
          circuitFun (13 + 13) C
            (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 w)) = true) ∧
        (∀ z ∈ reps, ∀ m ∈ ([1, 3, 9] : List (Fin 13)), ∀ t : Fin 13, ∀ dual : Bool,
          circuitFun (13 + 13) C (row z m t dual) = false)) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∈ x3, ∀ x7 ∈ x4, x5 - x7 ∉ x1) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x7 - x6 ∈ x1}.card ≤ (2 : ℕ)) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 - x8 ∈ x1}.card ≤ (2 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x9 ∈ x3, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ x9 ∈ x4, x8 = Fin.natAdd (13 : ℕ) x9)) = Bool.false := by
  classical
  dsimp only
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  let ok := fun (P W : Finset (Fin 13)) =>
    (∀ p ∈ P, ∀ w ∈ W, p - w ∉ D) ∧
    (∀ w : Fin 13, (P.filter fun p => p - w ∈ D).card ≤ 2) ∧
    (∀ p : Fin 13, (W.filter fun w => p - w ∈ D).card ≤ 2)
  -- Step 1: Monotonicity of Monotone2 circuits
  have fold_mono : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ i, w1.getD i false = true → w2.getD i false = true) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) w1).getD i false = true →
           (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) w2).getD i false = true := by
    intro gs
    induction gs with
    | nil => intro _ w1 w2 _ hle i hi; exact hle i hi
    | cons g rest ih =>
      intro hgs w1 w2 hlen hle
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
      · simp [hlen]
      · intro i hi
        by_cases hlt : i < w1.length
        · rw [List.getD_append _ _ _ _ hlt] at hi
          rw [List.getD_append _ _ _ _ (by omega)]
          exact hle i hi
        · by_cases heq : i = w1.length
          · subst heq
            rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero] at hi
            rw [hlen, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero]
            rcases hgs g (List.mem_cons_self ..) with hand | hor
            · rw [hand] at hi ⊢
              change (g.inputs.map fun k => w1.getD k false).all id = true at hi
              change (g.inputs.map fun k => w2.getD k false).all id = true
              rw [List.all_eq_true] at hi ⊢
              intro b hb
              rw [List.mem_map] at hb
              obtain ⟨k, hk, rfl⟩ := hb
              exact hle k (hi _ (List.mem_map_of_mem hk))
            · rw [hor] at hi ⊢
              change (g.inputs.map fun k => w1.getD k false).any id = true at hi
              change (g.inputs.map fun k => w2.getD k false).any id = true
              rw [List.any_eq_true] at hi ⊢
              obtain ⟨b, hb, hbt⟩ := hi
              rw [List.mem_map] at hb
              obtain ⟨k, hk, rfl⟩ := hb
              exact ⟨w2.getD k false, List.mem_map_of_mem hk, hle k hbt⟩
          · have hge : (w1 ++ [g.op.eval (g.inputs.map fun k => w1.getD k false)]).length ≤ i := by
              simp; omega
            rw [List.getD_eq_default _ _ hge] at hi
            cases hi
  have circuit_mono : ∀ (C : Circuit), Monotone2 C →
      ∀ (x y : Fin (13 + 13) → Bool), (∀ i, x i = true → y i = true) →
      circuitFun (13 + 13) C y = false → circuitFun (13 + 13) C x = false := by
    intro C hM x y hxy hy
    apply Bool.eq_false_iff.mpr
    intro hx
    have hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      have hmem := (hM g hg).1
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
    have hle : ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
      intro i hi
      by_cases hlt : i < 13 + 13
      · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn] at hi
        rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn]
        exact hxy ⟨i, hlt⟩ hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        cases hi
    have hyt : circuitFun (13 + 13) C y = true :=
      fold_mono C.gates hgs (List.ofFn x) (List.ofFn y) (by simp) hle C.output hx
    rw [hy] at hyt
    cases hyt
  -- Step 2: Every generic false pair extends to a maximal generic false pair
  have extend_max : ∀ k (P W : Finset (Fin 13)),
      26 - (P.card + W.card) = k → ok P W →
      ∃ P' W' : Finset (Fin 13), P ⊆ P' ∧ W ⊆ W' ∧ ok P' W' ∧
        (∀ p : Fin 13, p ∉ P' → ¬ ok (insert p P') W') ∧
        (∀ w : Fin 13, w ∉ W' → ¬ ok P' (insert w W')) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro P W hk hok
      have hPc : P.card ≤ 13 := by
        simpa using (Finset.card_le_univ P)
      have hWc : W.card ≤ 13 := by
        simpa using (Finset.card_le_univ W)
      by_cases hP : ∃ p : Fin 13, p ∉ P ∧ ok (insert p P) W
      · obtain ⟨p, hp, hok'⟩ := hP
        have hcard : (insert p P).card = P.card + 1 := Finset.card_insert_of_notMem hp
        have hPc' : (insert p P).card ≤ 13 := by simpa using (Finset.card_le_univ (insert p P))
        obtain ⟨P', W', hsubP, hsubW, hokM, hmP, hmW⟩ :=
          ih (26 - ((insert p P).card + W.card)) (by omega) (insert p P) W rfl hok'
        exact ⟨P', W', (Finset.subset_insert p P).trans hsubP, hsubW, hokM, hmP, hmW⟩
      · by_cases hW : ∃ w : Fin 13, w ∉ W ∧ ok P (insert w W)
        · obtain ⟨w, hw, hok'⟩ := hW
          have hcard : (insert w W).card = W.card + 1 := Finset.card_insert_of_notMem hw
          have hWc' : (insert w W).card ≤ 13 := by simpa using (Finset.card_le_univ (insert w W))
          obtain ⟨P', W', hsubP, hsubW, hokM, hmP, hmW⟩ :=
            ih (26 - (P.card + (insert w W).card)) (by omega) P (insert w W) rfl hok'
          exact ⟨P', W', hsubP, (Finset.subset_insert w W).trans hsubW, hokM, hmP, hmW⟩
        · push Not at hP hW
          exact ⟨P, W, Finset.Subset.refl _, Finset.Subset.refl _, hok, hP, hW⟩
  -- Step 3: Combine hSynth, extend_max, hOrbit, and circuit_mono
  obtain ⟨C, hM, hSize, hPos, hNeg⟩ := hSynth
  refine ⟨C, hM, hSize, hPos, ?_⟩
  intro P W hDisj hDegP hDegW
  obtain ⟨P', W', hsubP, hsubW, hokM, hmP, hmW⟩ :=
    extend_max (26 - (P.card + W.card)) P W rfl ⟨hDisj, hDegP, hDegW⟩
  obtain ⟨z, hz, m, hm, t, dual, hrow⟩ := hOrbit P' W' hokM hmP hmW
  apply circuit_mono C hM _ (fun i : Fin (13 + 13) =>
      decide ((∃ p ∈ P', i = Fin.castAdd 13 p) ∨ (∃ w ∈ W', i = Fin.natAdd 13 w)))
  · intro i hi
    rw [decide_eq_true_iff] at hi ⊢
    rcases hi with ⟨p, hp, rfl⟩ | ⟨w, hw, rfl⟩
    · exact Or.inl ⟨p, hsubP hp, rfl⟩
    · exact Or.inr ⟨w, hsubW hw, rfl⟩
  · rw [hrow]
    exact hNeg z hz m hm t dual
