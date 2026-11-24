import PEqualNP.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_1936_56
    (hDeg : ∀ args : List ℕ, (args = [] ∨ args = [10] ∨ ∃ i : Fin 10, args = [i.val]) →
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) →
        ∃ (x6 : Fin (9 : ℕ) → Bool),
          have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];
          x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) args)]) ≠
            (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) ||
              x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
              x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (hPos : ∀ args : List ℕ, (args ∈ [[0, 1], [0, 2], [0, 3], [0, 4], [0, 6], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [1, 8], [2, 3], [2, 4], [2, 6], [2, 7], [2, 8], [3, 4], [3, 6], [4, 6], [6, 7]]) →
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) →
        ∃ (x6 : Fin (9 : ℕ) → Bool),
          have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];
          x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) args)]) ≠
            (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) ||
              x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (hNeg : ∀ args : List ℕ, (args ∈ [[1, 9], [2, 9], [3, 9], [4, 9], [6, 9]]) →
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) →
        ∃ (x6 : Fin (9 : ℕ) → Bool),
          have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];
          x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) args)]) ≠
            (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) →
        ∃ (x6 : Fin (9 : ℕ) → Bool),
          have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];
          x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠
            (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  let edge (x : Fin 9 → Bool) : Bool :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let W (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0]
  let andVal (args : List ℕ) (x : Fin 9 → Bool) :=
    PEqualNP.CircuitLowerBounds.GateOp.and.eval
      (args.map fun i => (W x).getD i false)
  let Bad (args : List ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) :=
    ∃ x : Fin 9 → Bool, C.eval (W x ++ [andVal args x]) ≠ edge x
  let pos : List (List ℕ) := [[0, 1], [0, 2], [0, 3], [0, 4], [0, 6], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [1, 8], [2, 3], [2, 4], [2, 6], [2, 7], [2, 8], [3, 4], [3, 6], [4, 6], [6, 7]]
  let neg : List (List ℕ) := [[1, 9], [2, 9], [3, 9], [4, 9], [6, 9]]
  let σ : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
  let perm (i : ℕ) : ℕ := if h : i < 9 then (σ ⟨i, h⟩).val else i
  let changeGate (g : PEqualNP.CircuitLowerBounds.Gate) :
      PEqualNP.CircuitLowerBounds.Gate := ⟨g.op, g.inputs.map perm⟩
  let changeCircuit (C : PEqualNP.CircuitLowerBounds.Circuit) :
      PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map changeGate, perm C.output⟩
  have auto : ∀ x : Fin 9 → Bool, edge (fun i => x (σ i)) = edge x := by
    intro x
    change ((x 0 && x 5) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 1) || (x 5 && x 7) || (x 8 && x 6) ||
      (x 3 && x 2) || (x 1 && x 6) || (x 7 && x 2) || (x 2 && x 1)) = edge x
    unfold edge
    ac_rfl
  have permSmall (i : ℕ) (hi : i < 9) : perm i < 9 := by
    simp [perm, hi]
  have lookup (x : Fin 9 → Bool) (tail : List Bool) (i : ℕ) :
      (List.ofFn (fun j => x (σ j)) ++ tail).getD i false =
        (List.ofFn x ++ tail).getD (perm i) false := by
    by_cases hi : i < 9
    · have hpi := permSmall i hi
      rw [List.getD_append _ _ _ _ (by simpa using hi),
        List.getD_append _ _ _ _ (by simpa using hpi)]
      rw [List.getD_eq_getElem _ _ (by simpa using hi),
        List.getD_eq_getElem _ _ (by simpa using hpi)]
      simp only [List.getElem_ofFn, perm, dite_eq_left hi]
    · have hpi : perm i = i := dite_eq_right hi
      rw [hpi, List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi)]
      simp
  let step (ws : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have foldLookup (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (x : Fin 9 → Bool) (tail : List Bool) (i : ℕ) :
      (gs.foldl step (List.ofFn (fun j => x (σ j)) ++ tail)).getD i false =
        ((gs.map changeGate).foldl step (List.ofFn x ++ tail)).getD (perm i) false := by
    induction gs generalizing tail with
    | nil => exact lookup x tail i
    | cons g gs ih =>
      simp only [List.foldl_cons, List.map_cons, step, changeGate]
      have inputs_eq :
          (g.inputs.map fun k => (List.ofFn (fun j => x (σ j)) ++ tail).getD k false) =
            (g.inputs.map perm).map (fun k => (List.ofFn x ++ tail).getD k false) := by
        simp only [List.map_map, Function.comp_def, lookup]
      change (gs.foldl step _).getD i false = ((gs.map changeGate).foldl step _).getD (perm i) false
      rw [inputs_eq, List.append_assoc, List.append_assoc]
      exact ih _
  have renamedFan (C : PEqualNP.CircuitLowerBounds.Circuit)
      (h : PEqualNP.MetaComplexity.FanInTwo C) :
      PEqualNP.MetaComplexity.FanInTwo (changeCircuit C) := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    simpa [changeGate] using h a ha
  have reflect (args : List ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (h : Bad (args.map perm) (changeCircuit C)) : Bad args C := by
    obtain ⟨x, hx⟩ := h
    let y : Fin 9 → Bool := fun i => x (σ i)
    have hy0 : y 0 = x 0 := rfl
    have hg : andVal args y = andVal (args.map perm) x := by
      simp only [andVal, W, List.map_map, Function.comp_def, hy0]
      rw [show (args.map fun i => (List.ofFn y ++ [!x 0]).getD i false) =
          (args.map fun i => (List.ofFn x ++ [!x 0]).getD (perm i) false) by
        simp only [y, lookup]]
    refine ⟨y, ?_⟩
    rw [show edge y = edge x from auto x]
    change (C.gates.foldl step (W y ++ [andVal args y])).getD C.output false ≠ _
    rw [hg]
    simpa only [Bad, W, y, hy0, List.append_assoc, List.singleton_append,
      foldLookup, changeCircuit, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, step] using hx
  have transfer (args rep : List ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (heq : ∀ x, andVal args x = andVal rep x) (h : Bad rep C) : Bad args C := by
    obtain ⟨x, hx⟩ := h
    refine ⟨x, ?_⟩
    simpa only [heq] using hx
  have swapArgs (a b : ℕ) (x : Fin 9 → Bool) :
      andVal [a, b] x = andVal [b, a] x := by
    simp [andVal, PEqualNP.CircuitLowerBounds.GateOp.eval, Bool.and_comm]
  have falseWire (i : ℕ) (hi : 10 ≤ i) (x : Fin 9 → Bool) : (W x).getD i false = false :=
    List.getD_eq_default _ _ (by simpa [W] using hi)
  have complement (x : Fin 9 → Bool) : andVal [0, 9] x = andVal [10] x := by
    have h0 : (W x).getD 0 false = x 0 := by
      rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
      simp
    have h9 : (W x).getD 9 false = !x 0 := by
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp
    simp only [andVal, List.map_cons, List.map_nil,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [h0, h9, falseWire 10 (by decide)]
    cases x 0 <;> rfl
  have covers : ∀ a b : Fin 10, a < b →
      (a.val = 0 ∧ b.val = 9) ∨ [a.val, b.val] ∈ pos ++ neg ∨
        [min (perm a.val) (perm b.val), max (perm a.val) (perm b.val)] ∈ pos ++ neg := by
    intro a b
    fin_cases a <;> fin_cases b <;> decide
  intro args hlen C hfan hsize
  change Bad args C
  have useRep (C' : PEqualNP.CircuitLowerBounds.Circuit)
      (hfan' : PEqualNP.MetaComplexity.FanInTwo C') (hsize' : C'.size ≤ 13)
      (r : List ℕ) (hr : r ∈ pos ++ neg) : Bad r C' := by
    rcases List.mem_append.mp hr with h | h
    · exact hPos r h C' hfan' hsize'
    · exact hNeg r h C' hfan' hsize'
  have useDeg (r : List ℕ) (hr : r = [] ∨ r = [10] ∨ ∃ i : Fin 10, r = [i.val]) :
      Bad r C := hDeg r hr C hfan hsize
  have useFalse : Bad [10] C := useDeg [10] (Or.inr (Or.inl rfl))
  have ordered (a b : ℕ) (hab : a < b) (hb : b < 10) : Bad [a, b] C := by
    have ha : a < 10 := by omega
    rcases covers ⟨a, ha⟩ ⟨b, hb⟩ hab with hcomp | hrep | hrep
    · obtain ⟨rfl, rfl⟩ := hcomp
      exact transfer [0, 9] [10] C complement useFalse
    · exact useRep C hfan hsize [a, b] hrep
    · apply reflect [a, b] C
      have hsize' : (changeCircuit C).size ≤ 13 := by
        simpa [changeCircuit, PEqualNP.CircuitLowerBounds.Circuit.size] using hsize
      have hb' := useRep (changeCircuit C) (renamedFan C hfan) hsize' _ hrep
      change Bad [perm a, perm b] (changeCircuit C)
      by_cases hp : perm a ≤ perm b
      · simpa only [min_eq_left hp, max_eq_right hp] using hb'
      · have hp' : perm b ≤ perm a := by omega
        apply transfer [perm a, perm b] [perm b, perm a] _ (swapArgs _ _)
        simpa only [min_eq_right hp', max_eq_left hp'] using hb'
  cases args with
  | nil => exact useDeg [] (Or.inl rfl)
  | cons a tail =>
    cases tail with
    | nil =>
      by_cases ha : a < 10
      · exact useDeg [a] (Or.inr (Or.inr ⟨⟨a, ha⟩, rfl⟩))
      · apply transfer [a] [10] C _ useFalse
        intro x
        simp only [andVal, List.map_cons, List.map_nil,
          PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        rw [falseWire a (by omega), falseWire 10 (by decide)]
    | cons b tail =>
      have hnil : tail = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at hlen
        omega
      subst tail
      by_cases ha : a < 10
      · by_cases hb : b < 10
        · rcases lt_trichotomy a b with hab | rfl | hba
          · exact ordered a b hab hb
          · apply transfer [a, a] [a] C _ (useDeg [a] (Or.inr (Or.inr ⟨⟨a, ha⟩, rfl⟩)))
            intro x
            simp [andVal, PEqualNP.CircuitLowerBounds.GateOp.eval]
          · exact transfer [a, b] [b, a] C (swapArgs a b) (ordered b a hba ha)
        · apply transfer [a, b] [10] C _ useFalse
          intro x
          simp only [andVal, List.map_cons, List.map_nil,
            PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          simp only [falseWire b (by omega), falseWire 10 (by decide), Bool.and_false]
      · apply transfer [a, b] [10] C _ useFalse
        intro x
        simp only [andVal, List.map_cons, List.map_nil,
          PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        simp only [falseWire a (by omega), falseWire 10 (by decide), Bool.false_and]
