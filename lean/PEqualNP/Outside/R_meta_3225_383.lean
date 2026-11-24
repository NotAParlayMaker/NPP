import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3225_383
    (rawInputs :
      let read := fun g : Gate =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun j => decide (j = 6))
      let input := fun (b : Bool) (y : Fin 8 → Bool) =>
        [y 1, y 0, y 4, y 7, y 5, y 2, b, y 6, y 3, y 1 || b]
      let H := fun y : Fin 8 → Bool =>
        y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 4 || y 1 && y 5 ||
        y 2 && y 6 || y 3 && y 7 || y 4 && y 6 || y 5 && y 7 || y 7 && y 4
      ∀ D : Circuit, FanInTwo D → D.size = 14 → D.gates.countP read ≤ 1 →
        (∃ g ∈ D.gates, g.op = GateOp.or ∧ 6 ∈ g.inputs ∧
          ∀ j ∈ g.inputs, j ∈ ([1,3,4,5,6] : List ℕ)) →
        (∀ y, D.eval (input false y) = H y) →
        ∃ y, D.eval (input true y) ≠ (H y || y 0 || y 3))
    (generatedInput :
      let read := fun g : Gate =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun j => decide (j = 6))
      let input := fun (b : Bool) (y : Fin 8 → Bool) =>
        [y 1, y 0, y 4, y 7, y 5, y 2, b, y 6, y 3, y 1 || b]
      let H := fun y : Fin 8 → Bool =>
        y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 4 || y 1 && y 5 ||
        y 2 && y 6 || y 3 && y 7 || y 4 && y 6 || y 5 && y 7 || y 7 && y 4
      ∀ D : Circuit, FanInTwo D → D.size = 14 → D.gates.countP read ≤ 1 →
        (∃ g ∈ D.gates, g.op = GateOp.or ∧ 6 ∈ g.inputs ∧
          ∃ j ∈ g.inputs, 10 ≤ j) →
        (∀ y, D.eval (input false y) = H y) →
        ∃ y, D.eval (input true y) ≠ (H y || y 0 || y 3)) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (14 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∃ x8 ∈ x4.gates, x8.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (6 : ℕ) ∈ x8.inputs) → (∀ (x9 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x9) = x3 x9) → ∃ (x10 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x10) ≠ (x3 x10 || x10 (0 : Fin (8 : ℕ)) || x10 (3 : Fin (8 : ℕ))) := by
  let reads (g : Gate) :=
    (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun j => decide (j = 6))
  let input (b : Bool) (y : Fin 8 → Bool) :=
    [y 1, y 0, y 4, y 7, y 5, y 2, b, y 6, y 3, y 1 || b]
  let H (y : Fin 8 → Bool) :=
    y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 4 || y 1 && y 5 ||
    y 2 && y 6 || y 3 && y 7 || y 4 && y 6 || y 5 && y 7 || y 7 && y 4
  change ∀ D : Circuit, FanInTwo D → D.size = 14 → D.gates.countP reads ≤ 1 →
    (∃ g ∈ D.gates, g.op = GateOp.or ∧ 6 ∈ g.inputs) →
    (∀ y, D.eval (input false y) = H y) →
    ∃ y, D.eval (input true y) ≠ (H y || y 0 || y 3)
  intro D fan size count marked low
  by_contra! high
  obtain ⟨chosen, chosenMem, chosenOr, chosenReads⟩ := marked
  by_cases internal : ∃ j ∈ chosen.inputs, 10 ≤ j
  · obtain ⟨y, hy⟩ := generatedInput D fan size count
      ⟨chosen, chosenMem, chosenOr, chosenReads, internal⟩ low
    exact hy (high y)
  have chosenRead : reads chosen = true := by
    change (if chosen.op.eval [false,false] then chosen.inputs.take 1 else chosen.inputs).any
      (fun j => decide (j = 6)) = true
    rw [chosenOr]
    change chosen.inputs.any (fun j => decide (j = 6)) = true
    exact List.any_eq_true.mpr ⟨6, chosenReads, rfl⟩
  have short : (D.gates.filter reads).length ≤ 1 := by
    rwa [← List.countP_eq_length_filter]
  have sameMem (ys : List Gate) (h : ys.length ≤ 1) (g k : Gate)
      (hg : g ∈ ys) (hk : k ∈ ys) : g = k := by
    cases ys with
    | nil => simp at hg
    | cons p rest =>
      cases rest with
      | nil => exact (List.mem_singleton.mp hg).trans (List.mem_singleton.mp hk).symm
      | cons q qs => simp at h
  have unique (g : Gate) (hg : g ∈ D.gates) (hr : reads g = true) : g = chosen := by
    exact sameMem _ short g chosen
      (List.mem_filter.mpr ⟨hg, hr⟩) (List.mem_filter.mpr ⟨chosenMem, chosenRead⟩)
  let step (values : List Bool) (g : Gate) :=
    values ++ [g.op.eval (g.inputs.map fun i => values.getD i false)]
  have preserve (gs : List Gate) (a : List Bool) (i : ℕ) (hi : i < a.length) :
      (gs.foldl step a).getD i false = a.getD i false := by
    induction gs generalizing a with
    | nil => rfl
    | cons g rest ih =>
      change (rest.foldl step (step a g)).getD i false = _
      have larger : i < (step a g).length := by simp [step]; omega
      rw [ih _ larger]
      exact List.getD_append _ _ _ _ hi
  have outputNotControl : D.output ≠ 6 := by
    intro e
    let x : Fin 8 → Bool := fun j => decide (j = 0 ∨ j = 1)
    have hx := low x
    change (D.gates.foldl step (input false x)).getD D.output false = H x at hx
    rw [e, preserve _ _ _ (by decide)] at hx
    exact (by decide : (input false x).getD 6 false ≠ H x) hx
  have ignored (g : Gate) (hg : g ∈ D.gates) (hread : reads g = false)
      (a b : List Bool) (heq : ∀ i, i ≠ 6 → a.getD i false = b.getD i false) :
      g.op.eval (g.inputs.map fun i => a.getD i false) =
        g.op.eval (g.inputs.map fun i => b.getD i false) := by
    have ops : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (fan g hg).1
    have mapEq (h : g.inputs.any (fun j => decide (j = 6)) = false) :
        g.inputs.map (fun i => a.getD i false) = g.inputs.map (fun i => b.getD i false) := by
      apply List.map_congr_left
      intro j hj
      apply heq
      intro eq
      exact (List.any_eq_false.mp h j hj) (by simp [eq])
    change (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
      (fun j => decide (j = 6)) = false at hread
    rcases ops with op | op | op
    · rw [op] at hread
      rw [mapEq hread]
    · rw [op] at hread
      rw [mapEq hread]
    · rw [op] at hread ⊢
      change (g.inputs.take 1).any (fun j => decide (j = 6)) = false at hread
      cases hin : g.inputs with
      | nil => rfl
      | cons i rest =>
        have ine : i ≠ 6 := by
          intro ei
          subst i
          simp [hin] at hread
        change (!a.getD i false) = (!b.getD i false)
        rw [heq i ine]
  have masked (j : ℕ) (hj : j ∈ chosen.inputs) (hraw : j < 10) (hneq : j ≠ 6)
      (a b : List Bool) (ha : a.length = 10) (hb : b.length = 10)
      (heq : ∀ i, i ≠ 6 → a.getD i false = b.getD i false)
      (hTrue : a.getD j false = true) : D.eval a = D.eval b := by
    have run (gs : List Gate) (hm : ∀ g ∈ gs, g ∈ D.gates)
        (s t : List Bool) (hlen : s.length = t.length) (hmin : 10 ≤ s.length)
        (h : ∀ i, i ≠ 6 → s.getD i false = t.getD i false)
        (ht : s.getD j false = true) :
        ∀ i, i ≠ 6 → (gs.foldl step s).getD i false = (gs.foldl step t).getD i false := by
      induction gs generalizing s t with
      | nil => exact h
      | cons g gs ih =>
        intro i hi
        have hg : g ∈ D.gates := hm g (by simp)
        let v := g.op.eval (g.inputs.map fun k => s.getD k false)
        have val : g.op.eval (g.inputs.map fun k => t.getD k false) = v := by
          cases hr : reads g
          · exact (ignored g hg hr s t h).symm
          · obtain rfl := unique g hg hr
            have yes (w : List Bool) (hw : w.getD j false = true) :
                g.op.eval (g.inputs.map fun k => w.getD k false) = true := by
              rw [chosenOr]
              change (g.inputs.map fun k => w.getD k false).any id = true
              exact List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨j, hj, hw⟩, rfl⟩
            exact (yes t ((h j hneq).symm.trans ht)).trans (yes s ht).symm
        change (gs.foldl step (s ++ [v])).getD i false =
          (gs.foldl step (t ++ [g.op.eval (g.inputs.map fun k => t.getD k false)])).getD i false
        rw [val]
        apply ih (fun k hk => hm k (by simp [hk])) (s ++ [v]) (t ++ [v])
          (by simp [hlen]) (by simp; omega) _ _ i hi
        · intro k hk
          by_cases kin : k < s.length
          · rw [List.getD_append _ _ _ _ kin, List.getD_append _ _ _ _ (by omega)]
            exact h k hk
          · rw [List.getD_append_right _ _ _ _ (by omega),
                List.getD_append_right _ _ _ _ (by omega), hlen]
        · rw [List.getD_append _ _ _ _ (by omega), ht]
    exact run D.gates (fun _ hm => hm) a b (ha.trans hb.symm) (by omega) heq hTrue
      D.output outputNotControl
  have excluded (j : ℕ) (hj : j ∈ chosen.inputs) (bad : j ∈ ([0,2,7,8,9] : List ℕ)) :
      False := by
    let y (i : Fin 8) : Bool := decide (i = 1 ∨ i = 3 ∨ (j = 2 ∧ i = 4) ∨ (j = 7 ∧ i = 6))
    have casesJ : j = 0 ∨ j = 2 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by simpa using bad
    have lengths : j < 10 ∧ j ≠ 6 := by omega
    have trueWire : (input false y).getD j false = true := by
      rcases casesJ with rfl | rfl | rfl | rfl | rfl <;> decide
    have difference : H y ≠ (H y || y 0 || y 3) := by
      rcases casesJ with rfl | rfl | rfl | rfl | rfl <;> decide
    have inputsAgree (i : ℕ) (hi : i ≠ 6) :
        (input false y).getD i false = (input true y).getD i false := by
      by_cases small : i < 10
      · interval_cases i <;> first | rfl | contradiction
      · rw [List.getD_eq_default _ _ (by change 10 ≤ i; omega),
            List.getD_eq_default _ _ (by change 10 ≤ i; omega)]
    have equality := masked j hj lengths.1 lengths.2 _ _ rfl rfl inputsAgree trueWire
    rw [low, high] at equality
    exact difference equality
  have remaining (i : ℕ) (hi : i ∈ chosen.inputs) : i ∈ ([1,3,4,5,6] : List ℕ) := by
    have small : i < 10 := by
      by_contra! h
      exact internal ⟨i, hi, h⟩
    have noBad : i ∉ ([0,2,7,8,9] : List ℕ) := excluded i hi
    interval_cases i <;> (first | decide | exact (noBad (by decide)).elim)
  obtain ⟨y, hy⟩ := rawInputs D fan size count
    ⟨chosen, chosenMem, chosenOr, chosenReads, remaining⟩ low
  exact hy (high y)
