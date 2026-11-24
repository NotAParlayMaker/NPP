import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_3124 :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (¬∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[(1 : ℕ)]? = Option.some x6) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  have tab : ∀ jf : Fin 9, jf ≠ 0 → ∃ k : Fin 9,
      (fun (y : Fin 9 → Bool) => y (0 : Fin (9 : ℕ)) && y (1 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (2 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (3 : Fin (9 : ℕ)) || y (3 : Fin (9 : ℕ)) && y (4 : Fin (9 : ℕ)) || y (4 : Fin (9 : ℕ)) && y (0 : Fin (9 : ℕ)) || y (0 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (6 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (3 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (5 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (6 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (8 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ))) (fun i => decide (i = k)) ≠
        (fun (y : Fin 9 → Bool) => y (0 : Fin (9 : ℕ)) && y (1 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (2 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (3 : Fin (9 : ℕ)) || y (3 : Fin (9 : ℕ)) && y (4 : Fin (9 : ℕ)) || y (4 : Fin (9 : ℕ)) && y (0 : Fin (9 : ℕ)) || y (0 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (6 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (3 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (5 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (6 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (8 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ)))
          (Function.update (fun i => decide (i = k)) jf (!decide (jf = k))) := by
    decide +kernel
  intro xs hxs C fan _ hnone
  refine Classical.byContradiction fun hall => ?_
  let F : (Fin 9 → Bool) → Bool := fun y => y (0 : Fin (9 : ℕ)) && y (1 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (2 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (3 : Fin (9 : ℕ)) || y (3 : Fin (9 : ℕ)) && y (4 : Fin (9 : ℕ)) || y (4 : Fin (9 : ℕ)) && y (0 : Fin (9 : ℕ)) || y (0 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (6 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (3 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (5 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (6 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (8 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ))
  let W : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [!x 0]
  let v : (Fin 9 → Bool) → Bool := fun x =>
    PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => (W x).getD x9 false) xs)
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hc : ∀ x, (C.gates.foldl step (W x ++ [v x])).getD C.output false = F x := by
    intro x
    by_contra hne
    exact hall ⟨x, hne⟩
  have hWlen : ∀ x, (W x).length = 10 := by intro x; simp [W]
  have snoc_lt : ∀ (l : List Bool) (a : Bool) (k : ℕ), k < l.length →
      (l ++ [a]).getD k false = l.getD k false :=
    fun l a k h => List.getD_append _ _ _ _ h
  have snoc_eq : ∀ (l : List Bool) (a : Bool) (k : ℕ), k = l.length →
      (l ++ [a]).getD k false = a := by
    intro l a k h; subst h; simp
  have big : ∀ (l : List Bool) (k : ℕ), l.length ≤ k → l.getD k false = false :=
    fun l k h => List.getD_eq_default _ _ h
  have snoc_gt : ∀ (l : List Bool) (a : Bool) (k : ℕ), l.length < k →
      (l ++ [a]).getD k false = false := by
    intro l a k h; exact big _ _ (by simp; omega)
  have getD_W : ∀ x (k : ℕ) (hk : k < 9), (W x).getD k false = x ⟨k, hk⟩ := by
    intro x k hk
    show (List.ofFn x ++ [!x 0]).getD k false = x ⟨k, hk⟩
    rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact hk),
      List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hk]
  have getD_W9 : ∀ x, (W x).getD 9 false = !x 0 := by
    intro x; simp [W, List.getD_eq_getElem?_getD]
  have getD_Wbig : ∀ x (k : ℕ), 10 ≤ k → (W x).getD k false = false := by
    intro x k hk; exact big _ _ (by rw [hWlen]; exact hk)
  have hflat : (C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).length ≤ 2 := by
    rcases hg : C.gates with _ | ⟨g, _ | ⟨g', rest⟩⟩
    · simp
    · have h := (fan g (by rw [hg]; exact List.mem_singleton_self g)).2
      simpa using h
    · exact absurd ⟨g', by rw [hg]; rfl⟩ hnone
  let R : List ℕ := xs ++ C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs ++ [C.output]
  have hR : R.length ≤ 5 := by
    simp only [R, List.length_append, List.length_singleton]
    omega
  obtain ⟨j, hjmem, hjR⟩ : ∃ j, j ∈ Finset.Icc 1 8 ∧ j ∉ R.toFinset := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    calc R.toFinset.card ≤ R.length := List.toFinset_card_le R
      _ ≤ 5 := hR
      _ < (Finset.Icc 1 8).card := by simp
  have hj18 := Finset.mem_Icc.1 hjmem
  have hjR' : j ∉ R := fun h => hjR (List.mem_toFinset.2 h)
  have hxsj : j ∉ xs := fun h => hjR' (by simp [R, h])
  have hout : C.output ≠ j := fun h => hjR' (by simp [R, h])
  have hnotread : ∀ g ∈ C.gates, j ∉ g.inputs := by
    intro g hg hj
    exact hjR' (by simp only [R, List.mem_append, List.mem_flatMap]; exact Or.inl (Or.inr ⟨g, hg, hj⟩))
  let jf : Fin 9 := ⟨j, by omega⟩
  let flip : (Fin 9 → Bool) → (Fin 9 → Bool) := fun x => Function.update x jf (!x jf)
  have Wagree : ∀ x i, i ≠ j → (W x).getD i false = (W (flip x)).getD i false := by
    intro x i hi
    by_cases h9 : i < 9
    · rw [getD_W x i h9, getD_W _ i h9]
      have hne : (⟨i, h9⟩ : Fin 9) ≠ jf := fun e => hi (congrArg Fin.val e)
      exact (Function.update_of_ne hne _ _).symm
    · by_cases h99 : i = 9
      · subst h99
        rw [getD_W9, getD_W9]
        have hne : (0 : Fin 9) ≠ jf := by
          intro e
          have := congrArg Fin.val e
          simp only [jf, Fin.val_zero] at this
          omega
        rw [show flip x 0 = x 0 from Function.update_of_ne hne _ _]
      · rw [getD_Wbig x i (by omega), getD_Wbig _ i (by omega)]
  have Aagree : ∀ x i, i ≠ j →
      (W x ++ [v x]).getD i false = (W (flip x) ++ [v (flip x)]).getD i false := by
    intro x i hi
    by_cases h10 : i < 10
    · rw [snoc_lt (W x) (v x) i (by rw [hWlen]; exact h10),
        snoc_lt (W (flip x)) (v (flip x)) i (by rw [hWlen]; exact h10)]
      exact Wagree x i hi
    · by_cases h11 : i = 10
      · rw [snoc_eq (W x) (v x) i (by rw [hWlen]; exact h11),
          snoc_eq (W (flip x)) (v (flip x)) i (by rw [hWlen]; exact h11)]
        show PEqualNP.CircuitLowerBounds.GateOp.or.eval
            (List.map (fun (x9 : ℕ) => (W x).getD x9 false) xs) =
          PEqualNP.CircuitLowerBounds.GateOp.or.eval
            (List.map (fun (x9 : ℕ) => (W (flip x)).getD x9 false) xs)
        congr 1
        apply List.map_congr_left
        intro i' hi'
        exact Wagree x i' (fun e => hxsj (e ▸ hi'))
      · rw [snoc_gt (W x) (v x) i (by rw [hWlen]; omega),
          snoc_gt (W (flip x)) (v (flip x)) i (by rw [hWlen]; omega)]
  have agree : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (A B : List Bool),
      (∀ g ∈ gs, j ∉ g.inputs) → A.length = B.length → j < A.length →
      (∀ i, i ≠ j → A.getD i false = B.getD i false) →
      ∀ i, i ≠ j → (gs.foldl step A).getD i false = (gs.foldl step B).getD i false := by
    intro gs
    induction gs with
    | nil => intro A B _ _ _ h; exact h
    | cons g gs ih =>
      intro A B hg hl hj h
      have e : g.op.eval (g.inputs.map fun i => A.getD i false) =
          g.op.eval (g.inputs.map fun i => B.getD i false) := by
        congr 1
        apply List.map_congr_left
        intro i hi
        exact h i (fun e => hg g List.mem_cons_self (e ▸ hi))
      simp only [List.foldl_cons]
      apply ih (step A g) (step B g) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      · simp only [step, List.length_append, List.length_singleton, hl]
      · simp only [step, List.length_append, List.length_singleton]; omega
      · intro i hi
        show (A ++ [g.op.eval (g.inputs.map fun i => A.getD i false)]).getD i false =
          (B ++ [g.op.eval (g.inputs.map fun i => B.getD i false)]).getD i false
        rw [e]
        by_cases h1 : i < A.length
        · rw [snoc_lt A _ i h1, snoc_lt B _ i (by omega)]; exact h i hi
        · by_cases h2 : i = A.length
          · rw [snoc_eq A _ i h2, snoc_eq B _ i (by omega)]
          · rw [snoc_gt A _ i (by omega), snoc_gt B _ i (by omega)]
  have hj0 : jf ≠ 0 := by
    intro e
    have := congrArg Fin.val e
    simp only [jf, Fin.val_zero] at this
    omega
  obtain ⟨k, hk⟩ := tab jf hj0
  let x0 : Fin 9 → Bool := fun i => decide (i = k)
  have same : (C.gates.foldl step (W x0 ++ [v x0])).getD C.output false =
      (C.gates.foldl step (W (flip x0) ++ [v (flip x0)])).getD C.output false :=
    agree C.gates _ _ hnotread (by simp [hWlen]) (by simp [hWlen]; omega) (Aagree x0) C.output hout
  exact hk ((hc x0).symm.trans (same.trans (hc (flip x0))))
