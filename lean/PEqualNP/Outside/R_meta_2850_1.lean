import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2850_1 (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → (15 : ℕ) ≤ x1.size) (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → (∃ (x4 : Fin x1.gates.length) (x5 : ℕ), x5 ≠ (0 : ℕ) ∧ ((x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ((x1.gates.get x4).inputs = [(0 : ℕ), x5] ∨ (x1.gates.get x4).inputs = [x5, (0 : ℕ)])) → ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then !x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → x2 = Bool.true → ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then x2 != x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro C x2 hf hs hread hx2
  subst hx2
  have ebne : ∀ b : Bool, (true != b) = !b := by decide
  by_cases hex : ∃ (x4 : Fin C.gates.length) (x5 : ℕ), x5 ≠ 0 ∧
      ((C.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        (C.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      ((C.gates.get x4).inputs = [0, x5] ∨ (C.gates.get x4).inputs = [x5, 0])
  · obtain ⟨x7, hx7⟩ := h2 C hf hs hread hex
    exact ⟨x7, by simp only [ebne]; exact hx7⟩
  by_contra hne
  push_neg at hne
  have he : ∀ x : Fin 9 → Bool,
      C.eval (List.ofFn (fun i : Fin 9 => if i = 0 then !x 0 else x i)) = (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))) := by
    intro x
    have h := hne x
    simp only [ebne] at h
    exact h
  have fin : ∀ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' →
      C'.gates.length ≤ 14 → (∀ x : Fin 9 → Bool, C'.eval (List.ofFn x) = (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))) → False := by
    intro C' hf' hs' he'
    have h15 := h1 C' hf' (funext fun x => he' x)
    have : C'.size = C'.gates.length := rfl
    omega
  have getD_snoc : ∀ (w : List Bool) (b : Bool) (k : ℕ), (w ++ [b]).getD k false =
      if k < w.length then w.getD k false else if k = w.length then b else false := by
    intro w b k
    simp only [List.getD_eq_getElem?_getD]
    split_ifs with h1 h2
    · rw [List.getElem?_append_left h1]
    · subst h2; simp
    · rw [List.getElem?_append_right (by omega)]
      have : k - w.length ≠ 0 := by omega
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero this
      rw [hm]; simp
  have rel_step : ∀ (w w' : List Bool) (v : Bool), (0 < (w).length ∧ (w).length = (w').length ∧ (∀ k : ℕ, k ≠ 0 → (w).getD k false = (w').getD k false) ∧ (w').getD 0 false = !((w).getD 0 false)) → (0 < (w ++ [v]).length ∧ (w ++ [v]).length = (w' ++ [v]).length ∧ (∀ k : ℕ, k ≠ 0 → (w ++ [v]).getD k false = (w' ++ [v]).getD k false) ∧ (w' ++ [v]).getD 0 false = !((w ++ [v]).getD 0 false)) := by
    intro w w' v h
    obtain ⟨h0, hl, hk, hz⟩ := h
    refine ⟨by simp, by simp [hl], ?_, ?_⟩
    · intro k hk0
      rw [getD_snoc, getD_snoc, ← hl]
      split_ifs
      · exact hk k hk0
      · rfl
      · rfl
    · rw [getD_snoc, getD_snoc, ← hl]
      simp only [h0, ite_true]
      exact hz
  have grel_same : ∀ g : PEqualNP.CircuitLowerBounds.Gate, g.inputs.contains 0 = false →
      (∀ w w' : List Bool, (0 < (w).length ∧ (w).length = (w').length ∧ (∀ k : ℕ, k ≠ 0 → (w).getD k false = (w').getD k false) ∧ (w').getD 0 false = !((w).getD 0 false)) → (g).op.eval ((g).inputs.map fun i => w'.getD i false) = (g).op.eval ((g).inputs.map fun i => w.getD i false)) := by
    intro g hc w w' h
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi0 : i ≠ 0 := by
      rintro rfl
      have : g.inputs.contains 0 = true := List.elem_iff.mpr hi
      rw [hc] at this
      exact Bool.false_ne_true this
    exact (h.2.2.1 i hi0).symm
  have rel_fold_same : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, g.inputs.contains 0 = false) → ∀ w w' : List Bool, (0 < (w).length ∧ (w).length = (w').length ∧ (∀ k : ℕ, k ≠ 0 → (w).getD k false = (w').getD k false) ∧ (w').getD 0 false = !((w).getD 0 false)) →
      (0 < (gs.foldl (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length ∧ (gs.foldl (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length = (gs.foldl (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').length ∧ (∀ k : ℕ, k ≠ 0 → (gs.foldl (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD k false = (gs.foldl (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD k false) ∧ (gs.foldl (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD 0 false = !((gs.foldl (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD 0 false)) := by
    intro gs
    induction gs with
    | nil => intro _ w w' h; exact h
    | cons g gs ih =>
      intro hc w w' h
      simp only [List.foldl_cons]
      have e := grel_same g (hc g List.mem_cons_self) w w' h
      apply ih (fun g' hg' => hc g' (List.mem_cons_of_mem _ hg'))
      rw [e]
      exact rel_step _ _ _ h
  have fold_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      ∃ t, gs.foldl (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_⟩
      simp only [List.foldl_cons]
      rw [ht]
      simp
  have getD_ofFn9 : ∀ (f : Fin 9 → Bool) (k : ℕ),
      (List.ofFn f).getD k false = if h : k < 9 then f ⟨k, h⟩ else false := by
    intro f k
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    split_ifs with h
    · simp [h]
    · simp [h]
  have rel_flip : ∀ x : Fin 9 → Bool,
      (0 < (List.ofFn (fun i : Fin 9 => if i = 0 then !x 0 else x i)).length ∧ (List.ofFn (fun i : Fin 9 => if i = 0 then !x 0 else x i)).length = (List.ofFn x).length ∧ (∀ k : ℕ, k ≠ 0 → (List.ofFn (fun i : Fin 9 => if i = 0 then !x 0 else x i)).getD k false = (List.ofFn x).getD k false) ∧ (List.ofFn x).getD 0 false = !((List.ofFn (fun i : Fin 9 => if i = 0 then !x 0 else x i)).getD 0 false)) := by
    intro x
    refine ⟨by simp, by simp, ?_, ?_⟩
    · intro k hk
      rw [getD_ofFn9, getD_ofFn9]
      by_cases h : k < 9
      · rw [dif_pos h, dif_pos h]
        have : (⟨k, h⟩ : Fin 9) ≠ 0 := fun e => hk (congrArg Fin.val e)
        rw [if_neg this]
      · rw [dif_neg h, dif_neg h]
    · rw [getD_ofFn9, getD_ofFn9]
      simp
  by_cases hout : C.output = 0
  · have h := he (fun _ => false)
    obtain ⟨t, ht⟩ := fold_prefix C.gates
      (List.ofFn (fun i : Fin 9 => if i = 0 then !(fun _ : Fin 9 => false) 0 else (fun _ : Fin 9 => false) i))
    have hev : C.eval (List.ofFn (fun i : Fin 9 => if i = 0 then !(fun _ : Fin 9 => false) 0 else (fun _ : Fin 9 => false) i)) =
        (C.gates.foldl (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (fun i : Fin 9 => if i = 0 then !(fun _ : Fin 9 => false) 0 else (fun _ : Fin 9 => false) i))).getD C.output false := rfl
    rw [hev, ht, hout, List.getD_append _ _ _ _ (by simp)] at h
    revert h
    decide
  have hs' : C.gates.length ≤ 14 := hs
  by_cases hall : ∀ g ∈ C.gates, g.inputs.contains 0 = false
  · apply fin C hf hs'
    intro x
    have hr := rel_fold_same C.gates hall _ _ (rel_flip x)
    have e1 : C.eval (List.ofFn x) = (C.gates.foldl (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD C.output false := rfl
    have e2 : C.eval (List.ofFn (fun i : Fin 9 => if i = 0 then !x 0 else x i)) =
        (C.gates.foldl (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (fun i : Fin 9 => if i = 0 then !x 0 else x i))).getD C.output false := rfl
    rw [e1, ← hr.2.2.1 _ hout, ← e2]
    exact he x
  push_neg at hall
  obtain ⟨g0, hg0, hc0⟩ := hall
  have hc0' : g0.inputs.contains 0 = true := by simpa using hc0
  obtain ⟨j, hj, hjg⟩ := List.getElem_of_mem hg0
  have hget : C.gates.get ⟨j, hj⟩ = C.gates[j] := rfl
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.drop_eq_getElem_cons hj]
  have hother : ∀ g ∈ C.gates.take j ++ C.gates.drop (j + 1), g.inputs.contains 0 = false := by
    rw [hsplit, List.filter_append, List.filter_cons_of_pos (by rw [hjg]; exact hc0')] at hread
    simp only [List.length_append, List.length_cons] at hread
    have hA : (C.gates.take j).filter (fun g => g.inputs.contains 0) = [] :=
      List.eq_nil_of_length_eq_zero (by omega)
    have hB : (C.gates.drop (j + 1)).filter (fun g => g.inputs.contains 0) = [] :=
      List.eq_nil_of_length_eq_zero (by omega)
    rw [List.filter_eq_nil_iff] at hA hB
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · simpa using hA g hg
    · simpa using hB g hg
  have key : ∀ g' : PEqualNP.CircuitLowerBounds.Gate,
      (g'.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
        PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
        g'.inputs.length ≤ 2) → (∀ w w' : List Bool, (0 < (w).length ∧ (w).length = (w').length ∧ (∀ k : ℕ, k ≠ 0 → (w).getD k false = (w').getD k false) ∧ (w').getD 0 false = !((w).getD 0 false)) → (g').op.eval ((g').inputs.map fun i => w'.getD i false) = (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => w.getD i false)) → False := by
    intro g' hg' hg
    apply fin ⟨C.gates.take j ++ g' :: C.gates.drop (j + 1), C.output⟩
    · intro g hg
      have hg2 : g ∈ C.gates.take j ++ g' :: C.gates.drop (j + 1) := hg
      simp only [List.mem_append, List.mem_cons] at hg2
      rcases hg2 with hg2 | hg2 | hg2
      · exact hf g (List.mem_of_mem_take hg2)
      · subst hg2; exact hg'
      · exact hf g (List.mem_of_mem_drop hg2)
    · show (C.gates.take j ++ g' :: C.gates.drop (j + 1)).length ≤ 14
      simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
      omega
    · intro x
      have r1 := rel_fold_same (C.gates.take j)
        (fun g hg => hother g (List.mem_append_left _ hg)) _ _ (rel_flip x)
      have r2 := rel_step _ _ ((C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
        ((C.gates.take j).foldl (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (fun i : Fin 9 => if i = 0 then !x 0 else x i))).getD i false)) r1
      have e := hg _ _ r1
      have r3 := rel_fold_same (C.gates.drop (j + 1))
        (fun g hg => hother g (List.mem_append_right _ hg)) _ _ r2
      have e1 : (⟨C.gates.take j ++ g' :: C.gates.drop (j + 1), C.output⟩ :
          PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) =
          ((C.gates.take j ++ g' :: C.gates.drop (j + 1)).foldl (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD C.output false := rfl
      have e2 : C.eval (List.ofFn (fun i : Fin 9 => if i = 0 then !x 0 else x i)) =
          (C.gates.foldl (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (fun i : Fin 9 => if i = 0 then !x 0 else x i))).getD C.output false := rfl
      rw [e1, ← he x, e2]
      conv_rhs => rw [hsplit]
      simp only [List.foldl_append, List.foldl_cons]
      rw [e]
      exact (r3.2.2.1 _ hout).symm
  rw [hjg] at key
  have hfj := hf _ (List.getElem_mem hj)
  rw [hjg] at hfj
  obtain ⟨hop, hlen⟩ := hfj
  obtain ⟨op, ins⟩ := g0
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp at hc0'
  · have ha : a = 0 := (by simpa using hc0' : 0 = a).symm
    subst ha
    rcases hop with rfl | rfl | rfl
    · exact key ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ (by simp) (fun w w' h => by
        simp only [List.map_cons, List.map_nil]
        rw [h.2.2.2]
        cases w.getD 0 false <;> rfl)
    · exact key ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ (by simp) (fun w w' h => by
        simp only [List.map_cons, List.map_nil]
        rw [h.2.2.2]
        cases w.getD 0 false <;> rfl)
    · exact key ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0]⟩ (by simp) (fun w w' h => by
        simp only [List.map_cons, List.map_nil]
        rw [h.2.2.2]
        cases w.getD 0 false <;> rfl)
  · have hab : a = 0 ∨ b = 0 := by
      simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
        beq_iff_eq] at hc0'
      rcases hc0' with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    rcases hop with rfl | rfl | rfl
    · by_cases ha : a = 0
      · by_cases hb : b = 0
        · subst ha; subst hb
          exact key ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ (by simp) (fun w w' h => by
            simp only [List.map_cons, List.map_nil]
            rw [h.2.2.2]
            cases w.getD 0 false <;> rfl)
        · subst ha
          exact hex ⟨⟨j, hj⟩, b, hb, Or.inl (by rw [hget, hjg]), Or.inl (by rw [hget, hjg])⟩
      · have hb : b = 0 := hab.resolve_left ha
        subst hb
        exact hex ⟨⟨j, hj⟩, a, ha, Or.inl (by rw [hget, hjg]), Or.inr (by rw [hget, hjg])⟩
    · by_cases ha : a = 0
      · by_cases hb : b = 0
        · subst ha; subst hb
          exact key ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ (by simp) (fun w w' h => by
            simp only [List.map_cons, List.map_nil]
            rw [h.2.2.2]
            cases w.getD 0 false <;> rfl)
        · subst ha
          exact hex ⟨⟨j, hj⟩, b, hb, Or.inr (by rw [hget, hjg]), Or.inl (by rw [hget, hjg])⟩
      · have hb : b = 0 := hab.resolve_left ha
        subst hb
        exact hex ⟨⟨j, hj⟩, a, ha, Or.inr (by rw [hget, hjg]), Or.inr (by rw [hget, hjg])⟩
    · by_cases ha : a = 0
      · subst ha
        exact key ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0]⟩ (by simp) (fun w w' h => by
          simp only [List.map_cons, List.map_nil]
          rw [h.2.2.2]
          cases w.getD 0 false <;> rfl)
      · have hb : b = 0 := hab.resolve_left ha
        subst hb
        exact key ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [a, 0]⟩ (by simp) (fun w w' h => by
          show (!(w'.getD a false)) = !(w.getD a false)
          rw [h.2.2.1 a ha])
  · simp at hlen
