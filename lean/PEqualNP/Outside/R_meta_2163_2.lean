import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Supply the fixed OR and the second gate value as two more input wires.
-- A negation in the second position leaves at most one negation in the suffix.
-- An empty negation reads false, represented by wire ten before the second gate.
theorem PEqualNP.Outside.R_meta_2163_2
    (neg : ∀ (D : Circuit) (wire : ℕ), FanInTwo D → D.size ≤ 13 →
      (∀ i j : Fin D.gates.length, (D.gates.get i).op = GateOp.not → (D.gates.get j).op = GateOp.not → i = j) →
      ∃ x : Fin 9 → Bool, let w := List.ofFn x ++ [x 0 || x 2]
        D.eval (w ++ [!w.getD wire false]) ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x)
    (binary : ∀ (D : Circuit) (b : Bool) (ins : List ℕ), FanInTwo D → D.size ≤ 13 → ins.length ≤ 2 →
      (∀ i j k : Fin D.gates.length, (D.gates.get i).op = GateOp.not → (D.gates.get j).op = GateOp.not → (D.gates.get k).op = GateOp.not → i = j ∨ i = k ∨ j = k) →
      ∃ x : Fin 9 → Bool, let w := List.ofFn x ++ [x 0 || x 2]
        let v := ins.map (fun i => w.getD i false)
        D.eval (w ++ [if b then v.all id else v.any id]) ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 ≠ x4 ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro ⟨gs, out⟩ fan nots first heval
  by_contra! small
  obtain ⟨a, b, ab, ha, hb, hall⟩ := nots
  cases gs with
  | nil => exact Fin.elim0 a
  | cons g gs =>
    cases gs with
    | nil =>
      change Fin 1 at a b
      exact ab (Subsingleton.elim a b)
    | cons t tail =>
      let D : Circuit := ⟨tail, out⟩
      have hd : FanInTwo D := fun z hz =>
        fan z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz))
      have sz : D.size ≤ 13 := by
        change (g :: t :: tail).length < 16 at small
        change tail.length ≤ 13
        simp only [List.length_cons] at small
        omega
      have keep (s : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
          ((Circuit.mk s 0).wires w).getD j false = w.getD j false := by
        induction s generalizing w with
        | nil => rfl
        | cons z s ih =>
          change ((Circuit.mk s 0).wires (w ++ [_])).getD j false = _
          rw [ih _ (by simp; omega)]
          exact List.getD_append _ _ _ _ hj
      let val := fun (x : Fin 9 → Bool) => g.op.eval (g.inputs.map (fun i => (List.ofFn x).getD i false))
      have fixed (x : Fin 9 → Bool) : val x = (x 0 || x 2) := by
        have h := first x
        change ((Circuit.mk (t :: tail) 0).wires (List.ofFn x ++ [val x])).getD 9 false = _ at h
        rw [keep _ _ _ (by simp)] at h
        simpa [List.getD_eq_getElem?_getD, List.getElem?_append] using h
      let W := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 2]
      have run (x : Fin 9 → Bool) :
          D.eval (W x ++ [t.op.eval (t.inputs.map (fun i => (W x).getD i false))]) = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x := by
        have h := congrFun heval x
        change D.eval ((List.ofFn x ++ [val x]) ++ [t.op.eval (t.inputs.map (fun i => (List.ofFn x ++ [val x]).getD i false))]) = _ at h
        simpa only [fixed, W] using h
      have pigeon (i j k : Fin (g :: t :: tail).length)
          (hi : ((g :: t :: tail).get i).op = GateOp.not)
          (hj : ((g :: t :: tail).get j).op = GateOp.not)
          (hk : ((g :: t :: tail).get k).op = GateOp.not) : i = j ∨ i = k ∨ j = k := by
        rcases hall i hi with rfl | rfl <;> rcases hall j hj with h | h <;>
          rcases hall k hk with h' | h' <;> grind
      obtain ⟨ht, hlen⟩ := fan t (by simp)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      have bound : ∀ i j k : Fin D.gates.length, (D.gates.get i).op = GateOp.not →
          (D.gates.get j).op = GateOp.not → (D.gates.get k).op = GateOp.not →
          i = j ∨ i = k ∨ j = k := by
        intro i j k hi hj hk
        simpa using pigeon i.succ.succ j.succ.succ k.succ.succ hi hj hk
      rcases ht with hand | hor | hn
      · obtain ⟨x, bad⟩ := binary D true t.inputs hd sz hlen bound
        exact bad (by simpa only [hand, GateOp.eval, W, ite_true] using run x)
      · obtain ⟨x, bad⟩ := binary D false t.inputs hd sz hlen bound
        exact bad (by simpa only [hor, GateOp.eval, W, Bool.false_eq_true, ite_false] using run x)
      · have one : ∀ i j : Fin D.gates.length, (D.gates.get i).op = GateOp.not →
            (D.gates.get j).op = GateOp.not → i = j := by
          intro i j hi hj
          have h := pigeon (0 : Fin (t :: tail).length).succ i.succ.succ j.succ.succ hn hi hj
          rcases h with h | h | h
          · have z := congrArg Fin.val h
            simp only [Fin.val_succ, Fin.val_zero] at z
            omega
          · have z := congrArg Fin.val h
            simp only [Fin.val_succ, Fin.val_zero] at z
            omega
          · simpa using h
        cases htins : t.inputs with
        | nil =>
          obtain ⟨x, bad⟩ := neg D 10 hd sz one
          apply bad
          have h : (W x).getD 10 false = false := List.getD_eq_default _ _ (by simp [W])
          change D.eval (W x ++ [!(W x).getD 10 false]) = _
          rw [h]
          simpa only [hn, htins, List.map_nil, GateOp.eval, List.headD_nil] using run x
        | cons i rest =>
          obtain ⟨x, bad⟩ := neg D i hd sz one
          exact bad (by simpa only [hn, htins, List.map_cons, GateOp.eval, List.headD_cons, W] using run x)
