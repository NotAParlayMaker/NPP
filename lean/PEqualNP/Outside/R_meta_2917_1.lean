import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2917_1
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x2 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x2) = (x2 (0 : Fin (9 : ℕ)) && x2 (1 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (2 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (3 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (4 : Fin (9 : ℕ)) || x2 (4 : Fin (9 : ℕ)) && x2 (0 : Fin (9 : ℕ)) || x2 (0 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (6 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (5 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (8 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x4 : ℕ) => Bool.true) Bool.true x3.op) x1.gates)
    (h2 : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     (5 : ℕ) ≤ x1.headD (10 : ℕ) ∧ x1.headD (10 : ℕ) ≤ (8 : ℕ) →       ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.FanInTwo x4 →           x4.size ≤ (13 : ℕ) → (∀ (x5 : PEqualNP.CircuitLowerBounds.Gate), x5 ∈ x4.gates → x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x6 ∈ x4.gates ∧ (0 : ℕ) ∈ x6.inputs) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     (5 : ℕ) ≤ x1.headD (10 : ℕ) ∧ x1.headD (10 : ℕ) ≤ (8 : ℕ) →       ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.FanInTwo x4 →           x4.size ≤ (13 : ℕ) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro pins hlen hhead D hfan hsize
  by_cases hnot : ∀ (g : PEqualNP.CircuitLowerBounds.Gate), g ∈ D.gates → g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not
  · by_cases hr : ∃ (g : PEqualNP.CircuitLowerBounds.Gate), g ∈ D.gates ∧ (0 : ℕ) ∈ g.inputs
    · exact h2 pins hlen hhead D hfan hsize hnot hr
    have h0 : ∀ g ∈ D.gates, 0 ∉ g.inputs := fun g hg h => hr ⟨g, hg, h⟩
    have hop : ∀ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      intro g hg
      rcases (hfan g hg).1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (hnot g hg)
    have pre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (a : List Bool) (i : ℕ), i < a.length →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a).getD i false = a.getD i false := by
      intro gs
      induction gs with
      | nil => intro a i _; rfl
      | cons g gs ih =>
        intro a i hi
        show (gs.foldl _ (a ++ [_])).getD i false = _
        rw [ih _ i (by simp; omega)]
        rw [List.getD_append _ _ _ _ hi]
    have mono : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (a b : List Bool),
        (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        (∀ g ∈ gs, 0 ∉ g.inputs) → a.length = b.length →
        (∀ i, i ≠ 0 → a.getD i false = true → b.getD i false = true) →
        ∀ i, i ≠ 0 → (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a).getD i false = true →
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b).getD i false = true := by
      intro gs
      induction gs with
      | nil => intro a b _ _ _ hab; exact hab
      | cons g gs ih =>
        intro a b hop h0 hl hab
        have hg : ∀ j ∈ g.inputs, a.getD j false = true → b.getD j false = true :=
          fun j hj => hab j (fun e => h0 g (List.mem_cons_self) (e ▸ hj))
        have hval : g.op.eval (g.inputs.map fun i => a.getD i false) = true →
            g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
          rcases hop g List.mem_cons_self with h | h
          · rw [h]
            show (g.inputs.map fun i => a.getD i false).all id = true → (g.inputs.map fun i => b.getD i false).all id = true
            simp only [List.all_eq_true, List.mem_map, id]
            intro H x ⟨j, hj, e⟩
            subst e
            exact hg j hj (H _ ⟨j, hj, rfl⟩)
          · rw [h]
            show (g.inputs.map fun i => a.getD i false).any id = true → (g.inputs.map fun i => b.getD i false).any id = true
            simp only [List.any_eq_true, List.mem_map, id]
            rintro ⟨x, ⟨j, hj, rfl⟩, hx⟩
            exact ⟨_, ⟨j, hj, rfl⟩, hg j hj hx⟩
        apply ih (a ++ [_]) (b ++ [_]) (fun q hq => hop q (List.mem_cons_of_mem _ hq))
          (fun q hq => h0 q (List.mem_cons_of_mem _ hq)) (by simp [hl])
        intro i hi h
        rcases lt_trichotomy i a.length with hlt | heq | hgt
        · rw [List.getD_append _ _ _ _ hlt] at h
          rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
          exact hab i hi h
        · subst heq
          rw [List.getD_append_right _ _ _ _ (le_refl _)] at h
          rw [hl, List.getD_append_right _ _ _ _ (le_refl _)]
          simp only [Nat.sub_self, List.getD_cons_zero] at h ⊢
          exact hval h
        · rw [List.getD_eq_default _ _ (by simp; omega)] at h
          exact absurd h Bool.false_ne_true
    cases pins with
    | nil => exact absurd hhead.2 (by decide)
    | cons p rest =>
    have hp : 5 ≤ p ∧ p ≤ 8 := hhead
    obtain ⟨hp1, hp2⟩ := hp
    by_cases hout : D.output = 0
    · refine ⟨fun i : Fin 9 => decide (i.val = 0), ?_⟩
      have hw : PEqualNP.CircuitLowerBounds.GateOp.not.eval ((p :: rest).map fun i => (List.ofFn (fun i : Fin 9 => decide (i.val = 0)) ++ [!(fun i : Fin 9 => decide (i.val = 0)) 0]).getD i false) = true := by
        show (!((List.ofFn (fun i : Fin 9 => decide (i.val = 0)) ++ [!(fun i : Fin 9 => decide (i.val = 0)) 0]).getD p false)) = true
        interval_cases p <;> decide
      have hv : D.eval ((List.ofFn (fun i : Fin 9 => decide (i.val = 0)) ++ [!(fun i : Fin 9 => decide (i.val = 0)) 0]) ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval ((p :: rest).map fun i => (List.ofFn (fun i : Fin 9 => decide (i.val = 0)) ++ [!(fun i : Fin 9 => decide (i.val = 0)) 0]).getD i false)]) = true := by
        rw [hw]
        change (List.foldl (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) _ D.gates).getD D.output false = true
        rw [hout, pre D.gates _ 0 (by simp)]
        decide
      dsimp only
      intro hc
      exact absurd (hc.symm.trans hv) (by decide)
    by_contra hall
    have hw1 : PEqualNP.CircuitLowerBounds.GateOp.not.eval ((p :: rest).map fun i => (List.ofFn (fun i : Fin 9 => decide (i.val < 2)) ++ [!(fun i : Fin 9 => decide (i.val < 2)) 0]).getD i false) = true := by
      show (!((List.ofFn (fun i : Fin 9 => decide (i.val < 2)) ++ [!(fun i : Fin 9 => decide (i.val < 2)) 0]).getD p false)) = true
      interval_cases p <;> decide
    have hw0 : PEqualNP.CircuitLowerBounds.GateOp.not.eval ((p :: rest).map fun i => (List.ofFn (fun i : Fin 9 => decide (i.val = 1)) ++ [!(fun i : Fin 9 => decide (i.val = 1)) 0]).getD i false) = true := by
      show (!((List.ofFn (fun i : Fin 9 => decide (i.val = 1)) ++ [!(fun i : Fin 9 => decide (i.val = 1)) 0]).getD p false)) = true
      interval_cases p <;> decide
    have e1 : D.eval ((List.ofFn (fun i : Fin 9 => decide (i.val < 2)) ++ [!(fun i : Fin 9 => decide (i.val < 2)) 0]) ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval ((p :: rest).map fun i => (List.ofFn (fun i : Fin 9 => decide (i.val < 2)) ++ [!(fun i : Fin 9 => decide (i.val < 2)) 0]).getD i false)]) = true := by
      have h := (not_exists.mp hall) (fun i : Fin 9 => decide (i.val < 2))
      by_contra hne
      apply h
      dsimp only
      intro hc
      exact hne (hc.trans (by decide))
    have e0 : D.eval ((List.ofFn (fun i : Fin 9 => decide (i.val = 1)) ++ [!(fun i : Fin 9 => decide (i.val = 1)) 0]) ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval ((p :: rest).map fun i => (List.ofFn (fun i : Fin 9 => decide (i.val = 1)) ++ [!(fun i : Fin 9 => decide (i.val = 1)) 0]).getD i false)]) = false := by
      have h := (not_exists.mp hall) (fun i : Fin 9 => decide (i.val = 1))
      by_contra hne
      apply h
      dsimp only
      intro hc
      exact hne (hc.trans (by decide))
    rw [hw1] at e1
    rw [hw0] at e0
    change (List.foldl (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) _ D.gates).getD D.output false = true at e1
    have hm := mono D.gates ((List.ofFn (fun i : Fin 9 => decide (i.val < 2)) ++ [!(fun i : Fin 9 => decide (i.val < 2)) 0]) ++ [true]) ((List.ofFn (fun i : Fin 9 => decide (i.val = 1)) ++ [!(fun i : Fin 9 => decide (i.val = 1)) 0]) ++ [true]) hop h0 (by simp) (by
      intro i hi h
      by_cases hlt : i < 11
      · revert h
        interval_cases i <;> first | exact absurd rfl hi | decide
      · rw [List.getD_eq_default _ _ (by simp; omega)] at h
        exact absurd h Bool.false_ne_true) D.output hout e1
    change (List.foldl (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) _ D.gates).getD D.output false = false at e0
    rw [e0] at hm
    exact Bool.false_ne_true hm
  · obtain ⟨g, hg, hgop⟩ : ∃ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
      by_contra hc
      exact hnot (fun g hg he => hc ⟨g, hg, he⟩)
    by_contra hall
    let C : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ :: ⟨PEqualNP.CircuitLowerBounds.GateOp.not, pins⟩ :: D.gates, D.output⟩
    have hw : ∀ y : List Bool, C.wires y = D.wires ((y ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval ([0].map fun i => y.getD i false)]) ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (pins.map fun i => (y ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval ([0].map fun i => y.getD i false)]).getD i false)]) := fun y => rfl
    have key : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = D.eval ((List.ofFn x ++ [!x 0]) ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (pins.map fun i => (List.ofFn x ++ [!x 0]).getD i false)]) := by
      intro x
      have e0 : (List.ofFn x).getD 0 false = x 0 := by simp
      have e1 : PEqualNP.CircuitLowerBounds.GateOp.not.eval ([0].map fun i => (List.ofFn x).getD i false) = !x 0 := by
        show (!((List.ofFn x).getD 0 false)) = !x 0
        rw [e0]
      show (C.wires (List.ofFn x)).getD D.output false = (D.wires _).getD D.output false
      rw [hw, e1]
    have hC : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
      intro x
      rw [key x]
      have h := (not_exists.mp hall) x
      by_contra hne
      exact h hne
    have hfC : PEqualNP.MetaComplexity.FanInTwo C := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨Or.inr (Or.inr rfl), by decide⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨Or.inr (Or.inr rfl), hlen⟩
      exact hfan q hq
    have hb := h1 C hfC hC
    have hcnt : List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x4 : ℕ) => Bool.true) Bool.true x3.op) C.gates = List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x4 : ℕ) => Bool.true) Bool.true x3.op) D.gates := by
      show List.countP _ (_ :: _ :: D.gates) = _
      rw [List.countP_cons_of_neg Bool.false_ne_true, List.countP_cons_of_neg Bool.false_ne_true]
    have hlt : List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x4 : ℕ) => Bool.true) Bool.true x3.op) D.gates < D.gates.length := by
      rw [List.countP_eq_length_filter]
      apply List.length_filter_lt_length_iff_exists.mpr
      refine ⟨g, hg, ?_⟩
      rw [hgop]
      decide
    have hs : D.gates.length ≤ 13 := hsize
    omega
