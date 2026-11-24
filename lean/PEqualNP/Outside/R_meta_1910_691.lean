import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_1910_691
    (shared : let read (g : Gate) (i : ℕ) := g.inputs[0]? = some i ∨ g.op ≠ .not ∧ i ∈ g.inputs
      ∀ D : Circuit, FanInTwo D → D.output ≠ 4 → D.output ≠ 6 →
      (∀ g ∈ D.gates, read g 4 ↔ read g 6) →
      D.eval [true,false,false,false,true,false,false,false,false,true] =
        D.eval [true,false,false,false,false,false,true,false,false,true])
    (separate : let read (g : Gate) (i : ℕ) := g.inputs[0]? = some i ∨ g.op ≠ .not ∧ i ∈ g.inputs
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
      (∀ v ∈ ([4,6] : List ℕ), ∃! j : Fin D.gates.length, read (D.gates.get j) v) →
      (∀ j : Fin D.gates.length, ¬(read (D.gates.get j) 4 ∧ read (D.gates.get j) 6)) →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 4 || x 6]) ≠ f x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) →       (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) →         (∀ x5 ∈ [(4 : ℕ), (6 : ℕ)],             ∃! x7 : Fin (List.drop (1 : ℕ) x1.gates).length,               have x8 : PEqualNP.CircuitLowerBounds.Gate := (List.drop (1 : ℕ) x1.gates).get x7;               x8.inputs[(0 : ℕ)]? = Option.some x5 ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5 ∈ x8.inputs) →           (16 : ℕ) ≤ x1.size := by
  intro C fan first target reader
  by_contra! small
  cases C with
  | mk gates output =>
    cases gates with
    | nil =>
      obtain ⟨i, _⟩ := reader 4 (by decide)
      exact Fin.elim0 i
    | cons g tail =>
      let D : Circuit := ⟨tail, output⟩
      let inputs (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 || x 6]
      let F (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      let read (g : Gate) (i : ℕ) := g.inputs[0]? = some i ∨ g.op ≠ .not ∧ i ∈ g.inputs
      have fd : FanInTwo D := fun k hk => fan k (List.mem_cons_of_mem _ hk)
      have sd : D.size ≤ 14 := by
        change (g :: tail).length < 16 at small
        change tail.length ≤ 14
        simp only [List.length_cons] at small
        omega
      have unique : ∀ v ∈ ([4,6] : List ℕ), ∃! j : Fin D.gates.length, read (D.gates.get j) v :=
        reader
      have keep (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
          ((Circuit.mk gs 0).wires w).getD j false = w.getD j false := by
        induction gs generalizing w with
        | nil => rfl
        | cons k gs ih =>
          change ((Circuit.mk gs 0).wires (w ++ [_])).getD j false = _
          rw [ih _ (by simp; omega)]
          exact List.getD_append _ _ _ _ hj
      have run (x : Fin 9 → Bool) : D.eval (inputs x) = F x := by
        let bit := g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)
        have h := first x
        change ((Circuit.mk tail 0).wires (List.ofFn x ++ [bit])).getD 9 false = _ at h
        rw [keep _ _ _ (by simp)] at h
        have hb : bit = (x 4 || x 6) := by
          simpa [List.getD_eq_getElem?_getD, List.getElem?_append] using h
        have ev := congrFun target x
        change D.eval (List.ofFn x ++ [bit]) = _ at ev
        rw [hb] at ev
        simp only [Bool.or_assoc] at ev
        simp only [F, List.any_cons, List.any_nil, Bool.or_false]
        exact ev
      have nonOutput (i : Fin 9) : D.output ≠ i.val := by
        intro eq
        let x : Fin 9 → Bool := fun j => j == i
        have primary : (inputs x).getD i.val false = x i := by
          unfold inputs
          rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp),
            List.getElem_ofFn]
        have live : D.eval (inputs x) = true := by
          change ((Circuit.mk tail 0).wires (inputs x)).getD output false = true
          have inRange : i.val < (inputs x).length := by
            have bound := i.isLt
            simp only [inputs,List.length_append,List.length_ofFn,List.length_cons,List.length_nil]
            omega
          rw [show output = i.val from eq, keep _ _ _ inRange, primary]
          simp [x]
        have off : F x = false := by
          fin_cases i <;> decide
        exact Bool.noConfusion (live.symm.trans ((run x).trans off))
      have splitReaders (j : Fin D.gates.length) : ¬(read (D.gates.get j) 4 ∧ read (D.gates.get j) 6) := by
        intro both
        obtain ⟨a, _, ua⟩ := unique 4 (by decide)
        obtain ⟨b, _, ub⟩ := unique 6 (by decide)
        have ja : j = a := ua j both.1
        have jb : j = b := ub j both.2
        have agree (k : Gate) (hk : k ∈ D.gates) : read k 4 ↔ read k 6 := by
          obtain ⟨i, hi, eq⟩ := List.mem_iff_getElem.mp hk
          let p : Fin D.gates.length := ⟨i, hi⟩
          rw [← show D.gates.get p = k from eq]
          constructor
          · intro h
            rw [show p = j from (ua p h).trans ja.symm]
            exact both.2
          · intro h
            rw [show p = j from (ub p h).trans jb.symm]
            exact both.1
        have same := shared D fd (nonOutput 4) (nonOutput 6) agree
        let x : Fin 9 → Bool := fun i => i == 0 || i == 4
        let y : Fin 9 → Bool := fun i => i == 0 || i == 6
        have xt : D.eval [true,false,false,false,true,false,false,false,false,true] = true :=
          (run x).trans (by decide)
        have yf : D.eval [true,false,false,false,false,false,true,false,false,true] = false :=
          (run y).trans (by decide)
        exact Bool.noConfusion (xt.symm.trans (same.trans yf))
      obtain ⟨x, bad⟩ := separate D fd sd unique splitReaders
      exact bad (run x)
