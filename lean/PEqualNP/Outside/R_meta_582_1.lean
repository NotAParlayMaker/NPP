import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_582_1
    (finiteSearch : ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 26 ∧
      (∀ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) →
        C.eval (List.ofFn fun i : Fin 14 => decide (i = u ∨ i = v)) = true) ∧
      (∀ m ∈ ([127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256] : List ℕ), C.eval (List.ofFn fun i : Fin 14 => m.testBit i.val) = false))
    (independentCover : ∀ x : Fin 14 → Bool,
      (∀ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) → x u = false ∨ x v = false) →
      ∃ m ∈ ([127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256] : List ℕ), ∀ i : Fin 14, x i = true → m.testBit i.val = true) : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 26 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  obtain ⟨C, hC, hsize, hpos, hneg⟩ := finiteSearch
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have gateMono (op : GateOp) (hOp : op = .and ∨ op = .or) (idx : List ℕ)
      (f g : ℕ → Bool) (h : ∀ i, f i = true → g i = true) :
      op.eval (idx.map f) = true → op.eval (idx.map g) = true := by
    rcases hOp with rfl | rfl
    · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      intro hall _ hmem
      obtain ⟨i, hi, rfl⟩ := hmem
      exact h i (hall (f i) ⟨i, hi, rfl⟩)
    · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨_, ⟨i, hi, rfl⟩, hfi⟩
      exact ⟨g i, ⟨i, hi, rfl⟩, h i hfi⟩
  have foldMono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      ∀ a b : List Bool, a.length = b.length →
        (∀ i, a.getD i false = true → b.getD i false = true) →
        ∀ i, (gs.foldl step a).getD i false = true → (gs.foldl step b).getD i false = true := by
    induction gs with
    | nil => intro a b _ h; exact h
    | cons gate tail ih =>
      intro a b hl h
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg))
      · simp [step, hl]
      · intro i hi
        dsimp [step] at hi ⊢
        by_cases hia : i < a.length
        · rw [List.getD_append _ _ _ _ hia] at hi
          rw [List.getD_append _ _ _ _ (by omega)]
          exact h i hi
        · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
          rw [List.getD_append_right _ _ _ _ (by omega), ← hl]
          by_cases he : i - a.length = 0
          · rw [he] at hi ⊢
            simp only [List.getD_cons_zero] at hi ⊢
            exact gateMono gate.op (hgs gate List.mem_cons_self) _ _ _ h hi
          · obtain ⟨k, hk⟩ : ∃ k, i - a.length = k + 1 := ⟨i - a.length - 1, by omega⟩
            rw [hk] at hi
            simp at hi
  have evalMono {x y : Fin 14 → Bool} (hxy : ∀ i, x i = true → y i = true) :
      C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
    have hop : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := by
      intro g hg
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1
    change (C.gates.foldl step (List.ofFn x)).getD C.output false = true →
      (C.gates.foldl step (List.ofFn y)).getD C.output false = true
    apply foldMono C.gates hop _ _ (by simp) ?_ C.output
    intro i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
    by_cases hlt : i < 14
    · simpa [hlt] using hxy ⟨i, hlt⟩ (by simpa [hlt] using hi)
    · simp [hlt] at hi
  refine ⟨C, hC, hsize, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    by_contra hn
    have hInd (u v : Fin 14) (he : (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ))) :
        x u = false ∨ x v = false := by
      by_cases hu : x u = true
      · by_cases hv : x v = true
        · exact (hn ⟨u, v, he, hu, hv⟩).elim
        · exact Or.inr (Bool.eq_false_iff.mpr hv)
      · exact Or.inl (Bool.eq_false_iff.mpr hu)
    obtain ⟨m, hm, hsubset⟩ := independentCover x hInd
    have hmTrue := evalMono hsubset hx
    rw [hneg m hm] at hmTrue
    exact Bool.false_ne_true hmTrue
  · rintro ⟨u, v, he, hu, hv⟩
    apply evalMono (x := fun i => decide (i = u ∨ i = v)) _ (hpos u v he)
    intro i hi
    rcases decide_eq_true_eq.mp hi with rfl | rfl
    · exact hu
    · exact hv
