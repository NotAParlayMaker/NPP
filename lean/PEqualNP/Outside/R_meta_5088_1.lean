import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The wire agreement and list lookup arguments adapt L_meta_1411 at upstream
-- commit 0a921b61a150ebbb31acd66d8470f49f08876459.
-- Two raw false operands mask all literal-reading AND gates in the eliminated case.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_5088_1
    (separate : let F : (Fin 10 → Bool) → Bool := fun x => (((((((((((((((x 0 && x 1) || (x 1 && x 2)) || (x 2 && x 3)) || (x 3 && x 4)) || (x 4 && x 0)) || (x 0 && x 5)) || (x 1 && x 6)) || (x 2 && x 7)) || (x 3 && x 8)) || (x 4 && x 9)) || (x 5 && x 7)) || (x 7 && x 9)) || (x 9 && x 6)) || (x 6 && x 8)) || (x 8 && x 5)); ∀ k l : Fin 10, k ≠ 0 → l ≠ 0 → ∃ x : Fin 10 → Bool, x 0 = false ∧ x k = false ∧ x l = false ∧ F x = false ∧ F (Function.update x 0 true) = true)
    (remaining : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (18 : ℕ) →       have x4 : ℕ := List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => if x4.op.eval [Bool.false] = Bool.true then x4.inputs.head? == Option.some (0 : ℕ) || x4.inputs.head? == Option.some (10 : ℕ) else x4.inputs.contains (0 : ℕ) || x4.inputs.contains (10 : ℕ)) x1.gates;       (1 : ℕ) ≤ x4 → x4 ≤ (2 : ℕ) → (∀ k l : Fin 10, k ≠ 0 → l ≠ 0 → ∃ g ∈ x1.gates, ¬((0 ∉ g.inputs ∧ 10 ∉ g.inputs) ∨ (g.op = GateOp.and ∧ (k.val ∈ g.inputs ∨ l.val ∈ g.inputs)))) → ∃ (x7 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [!x7 (0 : Fin (10 : ℕ))]) ≠ (x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (18 : ℕ) →       have x4 : ℕ := List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => if x4.op.eval [Bool.false] = Bool.true then x4.inputs.head? == Option.some (0 : ℕ) || x4.inputs.head? == Option.some (10 : ℕ) else x4.inputs.contains (0 : ℕ) || x4.inputs.contains (10 : ℕ)) x1.gates;       (1 : ℕ) ≤ x4 → x4 ≤ (2 : ℕ) → ∃ (x7 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [!x7 (0 : Fin (10 : ℕ))]) ≠ (x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) := by
  let target (x : Fin 10 → Bool) : Bool := (((((((((((((((x 0 && x 1) || (x 1 && x 2)) || (x 2 && x 3)) || (x 3 && x 4)) || (x 4 && x 0)) || (x 0 && x 5)) || (x 1 && x 6)) || (x 2 && x 7)) || (x 3 && x 8)) || (x 4 && x 9)) || (x 5 && x 7)) || (x 7 && x 9)) || (x 9 && x 6)) || (x 6 && x 8)) || (x 8 && x 5))
  have two_and_separation : ∀ k l : Fin 10, k ≠ 0 → l ≠ 0 →
      ∃ x : Fin 10 → Bool, x 0 = false ∧ x k = false ∧ x l = false ∧
        target x = false ∧ target (Function.update x 0 true) = true := separate
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  have wires_cons (g : Gate) (gs : List Gate) (w : List Bool) :
      wiresFrom (g :: gs) w = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
  have snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
      (L ++ [S]).getD j d = L.getD j d := by
    by_cases hj : j < L.length
    · exact List.getD_append _ _ _ _ hj
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
  have snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by simp
  have original_value (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
      (wiresFrom gs w).getD j false = w.getD j false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [wires_cons,ih _ (by simp; omega)]
      exact List.getD_append _ _ _ _ hj

  have and_mask (ins : List ℕ) (w : List Bool) (k : ℕ) (hk : k ∈ ins)
      (hz : w.getD k false = false) :
      GateOp.and.eval (ins.map fun i => w.getD i false) = false := by
    induction ins with
    | nil => simp at hk
    | cons a ins ih =>
      simp only [List.mem_cons] at hk
      rcases hk with rfl | hk
      · change (w.getD k false && GateOp.and.eval (ins.map fun i => w.getD i false)) = false
        rw [hz]
        rfl
      · change (w.getD a false && GateOp.and.eval (ins.map fun i => w.getD i false)) = false
        rw [ih hk,Bool.and_false]

  let masked (k l : ℕ) (g : Gate) : Prop :=
    (0 ∉ g.inputs ∧ 10 ∉ g.inputs) ∨ (g.op = .and ∧ (k ∈ g.inputs ∨ l ∈ g.inputs))

  have agreement (k l : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
      (∀ g ∈ gs, masked k l g) → w.length = w'.length →
      k < w.length → l < w.length →
      w.getD k false = false → w.getD l false = false →
      w'.getD k false = false → w'.getD l false = false →
      (∀ j, j ≠ 0 → j ≠ 10 → w.getD j false = w'.getD j false) →
      ∀ j, j ≠ 0 → j ≠ 10 → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
    induction gs with
    | nil => intro w w' _ _ _ _ _ _ _ _ h; exact h
    | cons g gs ih =>
      intro w w' hh hl hk hll hzk hzl hzk' hzl' h
      have eq : g.op.eval (g.inputs.map fun i => w.getD i false) =
          g.op.eval (g.inputs.map fun i => w'.getD i false) := by
        rcases hh g List.mem_cons_self with hno | ⟨hop,hmem⟩
        · congr 1
          exact List.map_congr_left (fun i hi => h i (fun e => hno.1 (e ▸ hi)) (fun e => hno.2 (e ▸ hi)))
        · rw [hop]
          rcases hmem with hm | hm
          · rw [and_mask _ _ k hm hzk,and_mask _ _ k hm hzk']
          · rw [and_mask _ _ l hm hzl,and_mask _ _ l hm hzl']
      rw [wires_cons,wires_cons]
      apply ih _ _ (fun g' hg' => hh g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
        (by simp; omega) (by simp; omega)
        ((List.getD_append _ _ _ _ hk).trans hzk)
        ((List.getD_append _ _ _ _ hll).trans hzl)
        ((List.getD_append _ _ _ _ (by omega)).trans hzk')
        ((List.getD_append _ _ _ _ (by omega)).trans hzl')
      intro j hj hj10
      by_cases he : j = w.length
      · subst j
        rw [snoc_eq,hl,snoc_eq]
        exact eq
      · rw [snoc_ne _ _ _ _ he,snoc_ne _ _ _ _ (by omega)]
        exact h j hj hj10

  let input (x : Fin 10 → Bool) : List Bool := List.ofFn x ++ [!x 0]
  have input_raw (x : Fin 10 → Bool) (i : Fin 10) : (input x).getD i.val false = x i := by
    unfold input
    rw [List.getD_append _ _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
    simp only [List.getElem_ofFn]

  have no_two_raw_and_readers (C : Circuit) (k l : Fin 10) (hk : k ≠ 0) (hl : l ≠ 0)
      (shape : ∀ g ∈ C.gates, masked k.val l.val g) :
      ∃ x : Fin 10 → Bool, C.eval (input x) ≠ target x := by
    by_contra correct
    push_neg at correct
    have ho0 : C.output ≠ 0 := by
      intro ho
      have hc := correct (fun i => decide (i = 0))
      change (wiresFrom C.gates _).getD C.output false = _ at hc
      rw [ho,original_value _ _ _ (by simp [input])] at hc
      have hv := input_raw (fun i : Fin 10 => decide (i = 0)) 0
      change (input fun i : Fin 10 => decide (i = 0)).getD 0 false = true at hv
      rw [hv] at hc
      norm_num [target] at hc
    have ho10 : C.output ≠ 10 := by
      intro ho
      have hc := correct (fun _ => false)
      change (wiresFrom C.gates _).getD C.output false = _ at hc
      rw [ho,original_value _ _ _ (by simp [input])] at hc
      norm_num [input,target] at hc
    obtain ⟨x,hx0,hxk,hxl,hfx,hfy⟩ := two_and_separation k l hk hl
    let y := Function.update x 0 true
    have hsame : ∀ j, j ≠ 0 → j ≠ 10 → (input x).getD j false = (input y).getD j false := by
      intro j hj hj10
      by_cases hjlt : j < 10
      · have hn : (⟨j,hjlt⟩ : Fin 10) ≠ 0 := by intro he; exact hj (congrArg Fin.val he)
        rw [input_raw x ⟨j,hjlt⟩,input_raw y ⟨j,hjlt⟩]
        exact (Function.update_of_ne hn true x).symm
      · rw [List.getD_eq_default _ _ (by simp [input]; omega),List.getD_eq_default _ _ (by simp [input]; omega)]
    have ee := agreement k.val l.val C.gates (input x) (input y) shape (by simp [input])
      (by simp [input]; omega) (by simp [input]; omega)
      ((input_raw x k).trans hxk) ((input_raw x l).trans hxl)
      (by rw [input_raw]; simpa only [y,Function.update_of_ne hk] using hxk)
      (by rw [input_raw]; simpa only [y,Function.update_of_ne hl] using hxl)
      hsame C.output ho0 ho10
    change C.eval (input x) = C.eval (input y) at ee
    rw [correct x,correct y,hfx,hfy] at ee
    cases ee
  intro C hfan hsize r hmin hmax
  by_cases hmask : ∃ k l : Fin 10, k ≠ 0 ∧ l ≠ 0 ∧ ∀ g ∈ C.gates, masked k.val l.val g
  · obtain ⟨k,l,hk,hl,hshape⟩ := hmask
    exact no_two_raw_and_readers C k l hk hl hshape
  · apply remaining C hfan hsize hmin hmax
    intro k l hk hl
    by_contra hall
    push_neg at hall
    exact hmask ⟨k,l,hk,hl,hall⟩
