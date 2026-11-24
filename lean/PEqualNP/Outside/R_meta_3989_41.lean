import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

-- The suffix replay follows the checked reduction R_meta_1673_512.
-- Two distinct negation positions save two gates when compiling that suffix.
theorem PEqualNP.Outside.R_meta_3989_41
    (compile : ∀ C : Circuit, FanInTwo C → ∃ (B : BinaryCircuit) (p : Bool),
      (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) ∧ B.size + notCount C ≤ C.size ∧
      ∀ w : List Bool, w.length = 10 → (B.eval (w ++ [false]) != p) = C.eval w)
    (signedBound : ∀ (B : BinaryCircuit) (p : Bool), (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) →
      (∀ x : Fin 9 → Bool, (B.eval (List.ofFn x ++ [x 0 || x 2, false]) != p) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      13 ≤ B.size)
    : have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∃ (x4 : Fin x2.gates.length) (x5 : Fin x2.gates.length), x4 < x5 ∧ ↑x4 = (3 : ℕ) ∧ (x2.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x2.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x6 : Fin x2.gates.length), (x2.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not → x6 = x4 ∨ x6 = x5) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) → (∀ (x7 : ℕ), x7 = (0 : ℕ) ∨ x7 = (2 : ℕ) → ∃ x9 ∈ List.drop (1 : ℕ) x2.gates, x1 x9 x7) → (16 : ℕ) ≤ x2.size := by
  intro reads C fan positions first computes _
  let target := fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  let row := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 2]
  let step := fun (w : List Bool) (a : Gate) =>
    w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)]
  have keep (s : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (s.foldl step w).getD i false = w.getD i false := by
    induction s generalizing w with
    | nil => rfl
    | cons a rest ih =>
      rw [List.foldl_cons, ih]
      · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp [step]
        omega
  rcases C with ⟨gates,o⟩
  cases gates with
  | nil =>
    have h := first (fun _ => true)
    change false = true at h
    exact Bool.noConfusion h
  | cons g gs =>
    let D : Circuit := ⟨gs,o⟩
    have tailFan : FanInTwo D := fun a ha => fan a (List.mem_cons_of_mem _ ha)
    have front (x : Fin 9 → Bool) :
        step (List.ofFn x) g = row x := by
      have h := first x
      change (gs.foldl step (step (List.ofFn x) g)).getD 9 false = _ at h
      rw [keep _ _ _ (by simp [step])] at h
      have hread : (step (List.ofFn x) g).getD 9 false =
          g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
        change (List.ofFn x ++ [_]).getD 9 false = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
        simp
      rw [hread] at h
      change List.ofFn x ++ [_] = List.ofFn x ++ [_]
      rw [h]
    have correct (x : Fin 9 → Bool) : D.eval (row x) = target x := by
      have e := congrFun computes x
      change (gs.foldl step (step (List.ofFn x) g)).getD o false = target x at e
      rw [front x] at e
      exact e

    obtain ⟨a,b,hab,ha,hopA,hopB,_⟩ := positions
    let pred : Gate → Bool := fun v =>
      @decide (v.op = GateOp.not) (lineDegreeGateOpDecEq _ _)
    have two (ls : List Gate) (i j : Fin ls.length) (h : i < j)
        (hi : pred (ls.get i) = true) (hj : pred (ls.get j) = true) :
        2 ≤ ls.countP pred := by
      induction ls with
      | nil => exact Fin.elim0 i
      | cons v vs ih =>
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => exact (lt_irrefl _ h).elim
          | succ j =>
            have hp : 0 < vs.countP pred :=
              List.countP_pos_iff.mpr ⟨_, List.get_mem vs j, hj⟩
            change pred v = true at hi
            rw [List.countP_cons]
            simp only [hi,ite_true]
            omega
        | succ i =>
          cases j using Fin.cases with
          | zero => exact (Fin.not_lt_zero _ h).elim
          | succ j =>
            have hk := ih i j (by simpa using h) hi hj
            simp only [List.countP_cons]
            split <;> omega
    have hn : 2 ≤ notCount D := by
      change 2 ≤ (gs.filter pred).length
      rw [← List.countP_eq_length_filter]
      cases a using Fin.cases with
      | zero => simp at ha
      | succ i =>
        cases b using Fin.cases with
        | zero => exact (Fin.not_lt_zero _ hab).elim
        | succ j =>
          exact two gs i j (by simpa using hab)
            (by simpa [pred] using hopA) (by simpa [pred] using hopB)
    obtain ⟨B,p,shape,cost,replay⟩ := compile D tailFan
    have bound := signedBound B p shape (fun x => by
      change (B.eval (row x ++ [false]) != p) = target x
      exact (replay (row x) (by simp [row])).trans (correct x))
    have tailBound : 15 ≤ D.size := by omega
    exact Nat.succ_le_succ tailBound


