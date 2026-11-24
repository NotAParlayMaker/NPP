import PEqualNP.Defs
import Mathlib.Data.Fin.VecNotation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2836_1
    (caseA : ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
      (∀ x : Fin 9 → Bool,
        C.eval (List.ofFn (Function.update x 0 false) ++ [x 0 || x 4, x 0 || x 3]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5)) → False)
    (caseB : ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
      (∀ x : Fin 9 → Bool,
        C.eval (List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 1]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5)) → False)
    (caseD : ∀ (C : Circuit) (a : Fin 9), a ≠ 0 → a ≠ 4 → FanInTwo C → C.size ≤ 13 →
      (∀ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [false, x 0 || x 4 || x a]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5)) → False) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : (Fin (9 : ℕ) → Bool) → Bool := fun (x2 : Fin (9 : ℕ) → Bool) => x2 (0 : Fin (9 : ℕ)) && x2 (1 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (2 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (3 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (4 : Fin (9 : ℕ)) || x2 (4 : Fin (9 : ℕ)) && x2 (0 : Fin (9 : ℕ)) || x2 (0 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (6 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (5 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (8 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ));   PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → ((∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) = x2 x5) ∨ (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ))]) = x2 x5) ∨ (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ))]) = x2 x5) ∨ ∃ (x5 : Fin (9 : ℕ)), x5 ≠ (0 : Fin (9 : ℕ)) ∧ x5 ≠ (4 : Fin (9 : ℕ)) ∧ ∀ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [Bool.false, x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 x5]) = x2 x6) → False := by
  intro C
  let edge (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  dsimp only
  intro legal small cases
  rcases cases with h | h | h | ⟨a,h0,h4,h⟩
  · exact caseA C legal small h
  · exact caseB C legal small h
  · let p : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]
    have fix : ∀ i : Fin 9, p i = 4 ↔ i = 4 := by decide
    have invariance (x : Fin 9 → Bool) : edge (x ∘ p) = edge x := by
      change (x 0 && x 5 || x 5 && x 8 || x 8 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 1 || x 5 && x 7 || x 8 && x 6 || x 3 && x 2 || x 1 && x 6 ||
        x 7 && x 2 || x 2 && x 1) = edge x
      simp [edge, Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
    let mapWire (i : ℕ) : ℕ := if lt : i < 9 then (p ⟨i,lt⟩).val else i
    let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map mapWire⟩
    let D : Circuit := ⟨C.gates.map mapGate, mapWire C.output⟩
    have legalD : FanInTwo D := by
      intro g hg
      obtain ⟨old,oldMem,rfl⟩ := List.mem_map.mp hg
      have ok := legal old oldMem
      exact ⟨ok.1, by simpa [mapGate] using ok.2⟩
    have smallD : D.size ≤ 13 := by
      change (C.gates.map mapGate).length ≤ 13
      rw [List.length_map]
      exact small
    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have mapSmall (i n : ℕ) (enough : 9 ≤ n) : mapWire i < n ↔ i < n := by
      by_cases hi : i < 9
      · have bound := (p ⟨i,hi⟩).isLt
        simp only [mapWire, dite_eq_left hi]
        omega
      · simp [mapWire, hi]
    have replay (gs : List Gate) (u v : List Bool) (len : u.length = v.length)
        (enough : 9 ≤ u.length)
        (agree : ∀ i, u.getD i false = v.getD (mapWire i) false) :
        ∀ i, (gs.foldl step u).getD i false =
          ((gs.map mapGate).foldl step v).getD (mapWire i) false := by
      induction gs generalizing u v with
      | nil => exact agree
      | cons g gs ih =>
        have eq : g.op.eval (g.inputs.map fun i => u.getD i false) =
            (mapGate g).op.eval ((mapGate g).inputs.map fun i => v.getD i false) := by
          simp only [mapGate, List.map_map]
          exact congrArg g.op.eval (List.map_congr_left (fun i _ => agree i))
        simp only [List.getD_eq_getElem?_getD] at eq
        simp only [List.foldl_cons, List.map_cons]
        refine ih (step u g) (step v (mapGate g)) (by simp [step,len]) (by simp [step]; omega) ?_
        intro i
        by_cases hi : i < u.length
        · have hj : mapWire i < v.length := by rw [← len]; exact (mapSmall i _ enough).2 hi
          simpa only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
            List.getElem?_append_left hj] using agree i
        · have notInput : ¬i < 9 := by omega
          have same : mapWire i = i := by simp [mapWire, notInput]
          have hj : v.length ≤ i := by omega
          simp only [step, same, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : u.length ≤ i),
            List.getElem?_append_right hj, len]
          rw [eq]
    apply caseB D legalD smallD
    intro x
    let y := x ∘ p
    let tail := [x 0 || x 4, x 4 || x 1]
    let u := List.ofFn (Function.update y 4 false) ++ tail
    let v := List.ofFn (Function.update x 4 false) ++ tail
    have agree (i : ℕ) : u.getD i false = v.getD (mapWire i) false := by
      by_cases hi : i < 9
      · have hj := (p ⟨i,hi⟩).isLt
        simp only [u,v,List.getD_eq_getElem?_getD, mapWire, dite_eq_left hi]
        rw [List.getElem?_append_left (by simp [hi]), List.getElem?_append_left (by simp [hj]),
          List.getElem?_eq_getElem (by simp [hi]), List.getElem?_eq_getElem (by simp [hj]),
          List.getElem_ofFn, List.getElem_ofFn]
        change Function.update y 4 false ⟨i,hi⟩ = Function.update x 4 false (p ⟨i,hi⟩)
        by_cases fixed : (⟨i,hi⟩ : Fin 9) = 4
        · have atFour := (fix _).2 fixed
          rw [atFour, fixed, Function.update_self, Function.update_self]
        · have notFour : p ⟨i,hi⟩ ≠ 4 := fun eq => fixed ((fix _).1 eq)
          rw [Function.update_of_ne fixed, Function.update_of_ne notFour]
          rfl
      · have ge : 9 ≤ i := by omega
        simp only [u,v,mapWire,dite_eq_right hi,List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by simpa using ge : (List.ofFn (Function.update y 4 false)).length ≤ i),
          List.getElem?_append_right (by simpa using ge : (List.ofFn (Function.update x 4 false)).length ≤ i),
          List.length_ofFn]
    have eqOut : C.eval u = D.eval v :=
      replay C.gates u v (by simp [u,v]) (by simp [u]) agree C.output
    change D.eval v = edge x
    rw [← eqOut]
    have source : C.eval u = edge y := h y
    rw [source]
    exact invariance x
  · exact caseD C a h0 h4 legal small h
