import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_5040_1
    (hAnd : ∀ C : Circuit, Monotone2 C → C.size ≤ 63 → C.output + 1 = 26 + C.size →
      (∀ z ∈ C.gates.zipIdx, ∀ w ∈ z.1.inputs, w < 26 + z.2 ∨ w = 89) →
      ¬ HasLineDegree 26 (Finset.Ico 13 26) C 1 →
      ¬ HasLineDegree 26 (Finset.range 13) C 1 →
      (∀ l d : Fin 13, d ∈ ([0, 1, 3, 9] : List (Fin 13)) →
        circuitFun 26 C (fun i => Fin.addCases (fun p => decide (p = l + d)) (fun w => decide (w = l)) i) = true) →
      (∀ k ∈ ([7405575, 23330829, 5799955, 22282261, 21757977, 21233693, 3735587, 19988517, 3211303] ++ [19415081, 7372867, 24117317, 7340103, 23085129, 23068749, 22052945, 5275731, 22020181] ++ [19939425, 19923045, 18890857, 6389891, 6619269, 6357127, 6570121, 6553741, 6324419] ++ [6308041, 21512457, 21528849, 4751635, 21496089, 17318185, 20988233, 21004625, 17891877] : List ℕ), ∀ t : Fin 13,
        circuitFun 26 C (fun i => Fin.addCases (fun p => k.testBit (p - t).val)
          (fun l => k.testBit (13 + (l - t).val)) i) = false) →
      ∀ g : Gate, C.gates.getLast? = some g → g.op = GateOp.and → False)
    (hOr : ∀ C : Circuit, Monotone2 C → C.size ≤ 63 → C.output + 1 = 26 + C.size →
      (∀ z ∈ C.gates.zipIdx, ∀ w ∈ z.1.inputs, w < 26 + z.2 ∨ w = 89) →
      ¬ HasLineDegree 26 (Finset.Ico 13 26) C 1 →
      ¬ HasLineDegree 26 (Finset.range 13) C 1 →
      (∀ l d : Fin 13, d ∈ ([0, 1, 3, 9] : List (Fin 13)) →
        circuitFun 26 C (fun i => Fin.addCases (fun p => decide (p = l + d)) (fun w => decide (w = l)) i) = true) →
      (∀ k ∈ ([7405575, 23330829, 5799955, 22282261, 21757977, 21233693, 3735587, 19988517, 3211303] ++ [19415081, 7372867, 24117317, 7340103, 23085129, 23068749, 22052945, 5275731, 22020181] ++ [19939425, 19923045, 18890857, 6389891, 6619269, 6357127, 6570121, 6553741, 6324419] ++ [6308041, 21512457, 21528849, 4751635, 21496089, 17318185, 20988233, 21004625, 17891877] : List ℕ), ∀ t : Fin 13,
        circuitFun 26 C (fun i => Fin.addCases (fun p => k.testBit (p - t).val)
          (fun l => k.testBit (13 + (l - t).val)) i) = false) →
      ∀ g : Gate, C.gates.getLast? = some g → g.op = GateOp.or → False) :
    have x1 : List ℕ :=   have x1 : List ℕ :=     have x1 : List ℕ :=       have x1 : List ℕ := [(21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)];       (6308041 : ℕ) :: (21512457 : ℕ) :: (21528849 : ℕ) :: (4751635 : ℕ) :: x1;     have x2 : List ℕ := (6619269 : ℕ) :: (6357127 : ℕ) :: (6570121 : ℕ) :: (6553741 : ℕ) :: (6324419 : ℕ) :: x1;     (19939425 : ℕ) :: (19923045 : ℕ) :: (18890857 : ℕ) :: (6389891 : ℕ) :: x2;   have x2 : List ℕ :=     have x2 : List ℕ := (23085129 : ℕ) :: (23068749 : ℕ) :: (22052945 : ℕ) :: (5275731 : ℕ) :: (22020181 : ℕ) :: x1;     (19415081 : ℕ) :: (7372867 : ℕ) :: (24117317 : ℕ) :: (7340103 : ℕ) :: x2;   have x3 : List ℕ := (21757977 : ℕ) :: (21233693 : ℕ) :: (3735587 : ℕ) :: (19988517 : ℕ) :: (3211303 : ℕ) :: x2;   (7405575 : ℕ) :: (23330829 : ℕ) :: (5799955 : ℕ) :: (22282261 : ℕ) :: x3; ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ x2.output + (1 : ℕ) = (26 : ℕ) + x2.size ∧ (∀ x3 ∈ x2.gates.zipIdx, ∀ x5 ∈ x3.1.inputs, x5 < (26 : ℕ) + x3.2 ∨ x5 = (89 : ℕ)) ∧ ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) ∧ ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x4 = (0 : Fin (13 : ℕ)) ∨ x4 = (1 : Fin (13 : ℕ)) ∨ x4 = (3 : Fin (13 : ℕ)) ∨ x4 = (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) (x3 + x4) ∨ x6 = Fin.natAdd (13 : ℕ) x3)) = Bool.true) ∧ ∀ x3 ∈ x1, ∀ (x5 : Fin (13 : ℕ)), (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x6 : Fin (26 : ℕ)) => Decidable.decide ((∃ (x7 : Fin (13 : ℕ)), x3.testBit ↑(x7 - x5) = Bool.true ∧ x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x3.testBit ((13 : ℕ) + ↑(x7 - x5)) = Bool.true ∧ x6 = Fin.natAdd (13 : ℕ) x7)) = Bool.false := by
  classical
  intro rows hex
  obtain ⟨C, hmono, hsize, hshape, hinputs, hico, hrange, hpos, hneg⟩ := hex
  have cross (p l : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
    intro e
    have h := congrArg Fin.val e
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h
    omega
  have back (l p : Fin 13) : Fin.natAdd 13 l ≠ Fin.castAdd 13 p := (cross p l).symm
  have ci (p q : Fin 13) : Fin.castAdd 13 p = Fin.castAdd 13 q ↔ p = q := by
    simp [Fin.ext_iff]
  have ni (p q : Fin 13) : Fin.natAdd 13 p = Fin.natAdd 13 q ↔ p = q := by
    simp [Fin.ext_iff]
  have hp2 : ∀ l d : Fin 13, d ∈ ([0, 1, 3, 9] : List (Fin 13)) →
      circuitFun 26 C (fun i => Fin.addCases (fun p => decide (p = l + d))
        (fun w => decide (w = l)) i) = true := by
    intro l d hd
    have hd' : d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 9 := by simpa using hd
    have h := hpos l d hd'
    convert h using 2
    funext i
    induction i using Fin.addCases (m := 13) (n := 13)
    · simp only [Fin.addCases_left, ci, ni, cross, back] <;> simp
    · simp only [Fin.addCases_right, ci, ni, cross, back] <;> simp
  have hn2 : ∀ k ∈ ([7405575, 23330829, 5799955, 22282261, 21757977, 21233693, 3735587, 19988517, 3211303] ++ [19415081, 7372867, 24117317, 7340103, 23085129, 23068749, 22052945, 5275731, 22020181] ++ [19939425, 19923045, 18890857, 6389891, 6619269, 6357127, 6570121, 6553741, 6324419] ++ [6308041, 21512457, 21528849, 4751635, 21496089, 17318185, 20988233, 21004625, 17891877] : List ℕ), ∀ t : Fin 13,
      circuitFun 26 C (fun i => Fin.addCases (fun p => k.testBit (p - t).val)
        (fun l => k.testBit (13 + (l - t).val)) i) = false := by
    intro k hk t
    have h := hneg k hk t
    convert h using 2
    funext i
    induction i using Fin.addCases (m := 13) (n := 13)
    · simp only [Fin.addCases_left, ci, ni, cross, back] <;> simp
    · simp only [Fin.addCases_right, ci, ni, cross, back] <;> simp
  cases hlast : C.gates.getLast? with
  | none =>
      have hempty : C.gates = [] := List.getLast?_eq_none_iff.mp hlast
      have hsize0 : C.size = 0 := by
        change C.gates.length = 0
        simp [hempty]
      have positive (l : Fin 13) : circuitFun 26 C (fun i =>
          decide (i = Fin.castAdd 13 l ∨ i = Fin.natAdd 13 l)) = true := by
        simpa using hpos l 0 (Or.inl rfl)
      have keep {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α)
          (i : ℕ) (z : α) (hi : i < w.length) :
          (gs.foldl (fun l g => l ++ [f l g]) w).getD i z = w.getD i z := by
        induction gs generalizing w with
        | nil => rfl
        | cons g gs ih =>
            change (gs.foldl (fun l g => l ++ [f l g]) (w ++ [f w g])).getD i z = _
            rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]
      let f (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)
      have houtLo : 26 ≤ C.output := by
        by_contra hlt
        have hi : C.output < 26 := by omega
        let i : Fin 26 := ⟨C.output, hi⟩
        let input (l : Fin 13) (i : Fin 26) :=
          decide (i = Fin.castAdd 13 l ∨ i = Fin.natAdd 13 l)
        have read (l : Fin 13) : input l i = true := by
          have h := positive l
          change (C.gates.foldl (fun w g => w ++ [f w g]) (List.ofFn (input l))).getD C.output false = true at h
          rw [keep f _ _ _ _ (by simpa only [List.length_ofFn] using hi),
            List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi),
            List.getElem_ofFn] at h
          exact h
        have disjoint : ∀ j : Fin 26, (input 0 j && input 1 j) = false := by decide
        have contra := disjoint i
        rw [read 0, read 1] at contra
        exact Bool.noConfusion contra
      omega
  | some g =>
      have hgmem : g ∈ C.gates := List.mem_of_getLast? hlast
      have hopset := (hmono g hgmem).1
      have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
        simpa using hopset
      rcases hop with ha | ho
      · exact hAnd C hmono hsize hshape hinputs hico hrange hp2 hn2 g hlast ha
      · exact hOr C hmono hsize hshape hinputs hico hrange hp2 hn2 g hlast ho
