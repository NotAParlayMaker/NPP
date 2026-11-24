import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2891_1
    (binaryBound : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 8 → Bool, C.eval (List.ofFn x) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
         (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
         (x 5 && x 7) || (x 7 && x 4))) →
      11 ≤ C.gates.countP (fun g =>
        !(GateOp.rec false false true (fun _ => false) false g.op)))
    (fewNot : ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 12 ∧
      C.gates.countP (fun g => GateOp.rec false false true (fun _ => false) false g.op) ≤ 1 ∧
      ∀ x : Fin 8 → Bool, C.eval (List.ofFn x ++ [!(x 1)]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
         (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
         (x 5 && x 7) || (x 7 && x 4))) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 ∧ x1.size ≤ (12 : ℕ) ∧ ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [!x2 (1 : Fin (8 : ℕ))]) = (x2 (0 : Fin (8 : ℕ)) && x2 (1 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (2 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (3 : Fin (8 : ℕ)) || x2 (0 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (5 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (4 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (5 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (7 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ))) := by
  rintro ⟨C, fan, size, eval⟩
  let first : Gate := ⟨.not, [1]⟩
  let D : Circuit := ⟨first :: C.gates, C.output⟩
  have fanD : FanInTwo D := by
    intro g hg
    change g ∈ first :: C.gates at hg
    rcases List.mem_cons.mp hg with h | h
    · subst g
      simp [first]
    · exact fan g h
  have prepend (x : Fin 8 → Bool) :
      D.eval (List.ofFn x) = C.eval (List.ofFn x ++ [!(x 1)]) := by
    have bit : (List.ofFn x).getD 1 false = x 1 := by simp
    change (C.wires (List.ofFn x ++ [!((List.ofFn x).getD 1 false)])).getD C.output false =
      (C.wires (List.ofFn x ++ [!(x 1)])).getD C.output false
    rw [bit]
  let isNot (g : Gate) : Bool := GateOp.rec false false true (fun _ => false) false g.op
  have many : 11 ≤ C.gates.countP (fun g => !(isNot g)) := by
    have h := binaryBound D fanD (fun x => (prepend x).trans (eval x))
    change 11 ≤ (first :: C.gates).countP (fun g => !(isNot g)) at h
    simpa [List.countP_cons, first, isNot] using h
  have partition (gs : List Gate) : gs.length =
      gs.countP isNot + gs.countP (fun g => !(isNot g)) := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      cases tag : isNot g <;> simp [List.countP_cons, tag] <;> omega
  have split := partition C.gates
  change C.gates.length ≤ 12 at size
  have one : C.gates.countP isNot ≤ 1 := by omega
  exact fewNot ⟨C, fan, size, one, eval⟩
