import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_3170_461
    (ordinary : ∀ C : Circuit, FanInTwo C → circuitFun 9 C = (fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 15 ≤ C.size)
    (distinct : ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x 1 || x 5]) ≠ (fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       (∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  let F : (Fin 9 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  have repeated (j : Fin 9) (C : Circuit) (legal : FanInTwo C) (budget : C.size ≤ 13) :
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x j]) ≠ F x := by
    by_contra! agree
    let remapWire (i : ℕ) := if i = 10 then j.val else if 10 < i then i - 1 else i
    let remapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map remapWire⟩
    let first : Gate := ⟨.not, [0]⟩
    let D : Circuit := ⟨first :: C.gates.map remapGate, remapWire C.output⟩
    have fan : FanInTwo D := by
      intro g hg
      change g ∈ first :: C.gates.map remapGate at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp [first]
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hg
        simpa [remapGate] using legal r hr
    have size : D.size = 1 + C.size := by
      change (first :: C.gates.map remapGate).length = 1 + C.gates.length
      simp only [List.length_cons, List.length_map, Nat.add_comm]
    have same (x : Fin 9 → Bool) : circuitFun 9 D x = C.eval (List.ofFn x ++ [!x 0, x j]) := by
      let w := List.ofFn x ++ [!x 0]
      have length : w.length = 10 := by simp [w]
      have hj : w.getD j.val false = x j := by
        change (List.ofFn x ++ [!x 0]).getD j.val false = x j
        rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      let step (inputs : List Bool) (g : Gate) :=
        g.op.eval (g.inputs.map fun i => inputs.getD i false)
      have read (extra : List Bool) (i : ℕ) :
          ((w ++ [x j]) ++ extra).getD i false = (w ++ extra).getD (remapWire i) false := by
        change (w ++ (x j :: extra)).getD i false = (w ++ extra).getD (remapWire i) false
        simp only [List.getD_eq_getElem?_getD]
        by_cases atAlias : i = 10
        · subst i
          simp only [remapWire, ite_true]
          rw [List.getElem?_append_right (by omega), length, Nat.sub_self]
          rw [List.getD_eq_getElem?_getD] at hj
          rw [List.getElem?_append_left (l₁ := w) (l₂ := extra) (by omega)]
          simpa using hj.symm
        by_cases before : i < 10
        · simp only [remapWire, atAlias, ite_false, show ¬ 10 < i by omega]
          rw [List.getElem?_append_left (l₁ := w) (l₂ := x j :: extra) (by omega),
            List.getElem?_append_left (l₁ := w) (l₂ := extra) (by omega)]
        · simp only [remapWire, atAlias, ite_false, show 10 < i by omega, ite_true]
          rw [List.getElem?_append_right (l₁ := w) (l₂ := x j :: extra) (by omega),
            List.getElem?_append_right (l₁ := w) (l₂ := extra) (by omega), length]
          have shift : i - 10 = i - 1 - 10 + 1 := by omega
          rw [shift]
          rfl
      have sim (gs : List Gate) (extra : List Bool) :
          (gs.foldl (fun ys g => ys ++ [step ys g]) ((w ++ [x j]) ++ extra)).getD C.output false =
          ((gs.map remapGate).foldl (fun ys g => ys ++ [step ys g]) (w ++ extra)).getD (remapWire C.output) false := by
        induction gs generalizing extra with
        | nil => exact read extra C.output
        | cons g gs ih =>
          rw [List.map_cons, List.foldl_cons, List.foldl_cons]
          have next : step ((w ++ [x j]) ++ extra) g = step (w ++ extra) (remapGate g) := by
            simp only [step, remapGate, List.map_map]
            congr 1
            exact List.map_congr_left (fun i _ => read extra i)
          rw [next]
          simpa only [List.append_assoc] using ih (extra ++ [step (w ++ extra) (remapGate g)])
      have hw : List.ofFn x ++ [step (List.ofFn x) first] = w := rfl
      change ((C.gates.map remapGate).foldl (fun ys g => ys ++ [step ys g])
        (List.ofFn x ++ [step (List.ofFn x) first])).getD (remapWire C.output) false =
        (C.gates.foldl (fun ys g => ys ++ [step ys g]) (List.ofFn x ++ [!x 0, x j])).getD C.output false
      rw [hw]
      simpa only [List.append_nil, w, List.append_assoc, List.singleton_append] using (sim C.gates []).symm
    have equal : circuitFun 9 D = F := funext fun x => (same x).trans (agree x)
    have bound := ordinary D fan equal
    omega
  intro pins length _ support C legal budget
  obtain ⟨a, b, rfl⟩ : ∃ a b, pins = [a, b] := by
    cases pins with
    | nil => simp at length
    | cons a tail =>
      cases tail with
      | nil => simp at length
      | cons b remaining =>
        cases remaining with
        | nil => exact ⟨a, b, rfl⟩
        | cons c more => simp at length
  have first := support a (by simp)
  have second := support b (by simp)
  have at1 (x : Fin 9 → Bool) : (List.ofFn x ++ [!x 0]).getD 1 false = x 1 := rfl
  have at5 (x : Fin 9 → Bool) : (List.ofFn x ++ [!x 0]).getD 5 false = x 5 := rfl
  have evalOr (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
    change (a || (b || false)) = (a || b)
    rw [Bool.or_false]
  rcases first with rfl | rfl <;> rcases second with rfl | rfl
  · obtain ⟨x, mismatch⟩ := repeated 1 C legal budget
    exact ⟨x, by simpa [evalOr, at1] using mismatch⟩
  · obtain ⟨x, mismatch⟩ := distinct C legal budget
    exact ⟨x, by simpa [evalOr, at1, at5] using mismatch⟩
  · obtain ⟨x, mismatch⟩ := distinct C legal budget
    exact ⟨x, by simpa [evalOr, at1, at5, Bool.or_comm] using mismatch⟩
  · obtain ⟨x, mismatch⟩ := repeated 5 C legal budget
    exact ⟨x, by simpa [evalOr, at5] using mismatch⟩
