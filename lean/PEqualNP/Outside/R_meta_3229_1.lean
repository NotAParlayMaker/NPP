import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 1500000 in
set_option maxRecDepth 12000 in
theorem PEqualNP.Outside.R_meta_3229_1
    (normalize : ∀ C : Circuit, C.gates.length = 14 → Monotone2 C →
      ∃ D : Circuit, D.gates.length = 14 ∧ D.output = C.output ∧
        (∀ j : Fin 14,
        let g := D.gates.getD j.val ⟨.or, []⟩
        g = ⟨.and, []⟩ ∨ ∃ a b : Fin 25,
          (a.val < 10+j.val ∨ a.val = 24) ∧ (b.val < 10+j.val ∨ b.val = 24) ∧ a ≤ b ∧
          (g = ⟨.and,[a.val,b.val]⟩ ∨ g = ⟨.or,[a.val,b.val]⟩)) ∧
        ∀ x : List Bool, x.length = 10 → D.eval x = C.eval x)
    (lastGate : ∀ D : Circuit, D.gates.length = 14 → D.output = 23 → Monotone2 D →
      (∀ m ∈ ([515, 6, 524, 536, 529, 545, 66, 132, 776, 160, 320, 288] : List ℕ), D.eval (List.ofFn fun i : Fin 10 => m.testBit i.val) = true) →
      (∀ m ∈ ([554, 50, 581, 616, 116, 650, 713, 208, 773, 276, 897, 402] : List ℕ), D.eval (List.ofFn fun i : Fin 10 => m.testBit i.val) = false) →
      (∀ w ∈ (D.gates.getD 13 ⟨.or, []⟩).inputs, 10 ≤ w))
    (andCase : ∀ D : Circuit, D.gates.length = 14 → D.output = 23 →
      (∀ j : Fin 14,
        let g := D.gates.getD j.val ⟨.or, []⟩
        g = ⟨.and, []⟩ ∨ ∃ a b : Fin 25,
          (a.val < 10+j.val ∨ a.val = 24) ∧ (b.val < 10+j.val ∨ b.val = 24) ∧ a ≤ b ∧
          (g = ⟨.and,[a.val,b.val]⟩ ∨ g = ⟨.or,[a.val,b.val]⟩)) →
      (D.gates.getD 13 ⟨.or, []⟩).op = .and → (∀ w ∈ (D.gates.getD 13 ⟨.or, []⟩).inputs, 10 ≤ w) →
      (∀ m ∈ ([515, 6, 524, 536, 529, 545, 66, 132, 776, 160, 320, 288] : List ℕ), D.eval (List.ofFn fun i : Fin 10 => m.testBit i.val) = true) →
      (∀ m ∈ ([554, 50, 581, 616, 116, 650, 713, 208, 773, 276, 897, 402] : List ℕ), D.eval (List.ofFn fun i : Fin 10 => m.testBit i.val) = false) →
      (∃ m ∈ ([3, 12, 24, 17, 33, 264] : List ℕ), D.eval (List.ofFn fun i : Fin 10 => m.testBit i.val) = false) →
      (∃ m ∈ ([562, 628, 720, 788, 914] : List ℕ), D.eval (List.ofFn fun i : Fin 10 => m.testBit i.val) = true) → False)
    (orCase : ∀ D : Circuit, D.gates.length = 14 → D.output = 23 →
      (∀ j : Fin 14,
        let g := D.gates.getD j.val ⟨.or, []⟩
        g = ⟨.and, []⟩ ∨ ∃ a b : Fin 25,
          (a.val < 10+j.val ∨ a.val = 24) ∧ (b.val < 10+j.val ∨ b.val = 24) ∧ a ≤ b ∧
          (g = ⟨.and,[a.val,b.val]⟩ ∨ g = ⟨.or,[a.val,b.val]⟩)) →
      (D.gates.getD 13 ⟨.or, []⟩).op = .or → (∀ w ∈ (D.gates.getD 13 ⟨.or, []⟩).inputs, 10 ≤ w) →
      (∀ m ∈ ([515, 6, 524, 536, 529, 545, 66, 132, 776, 160, 320, 288] : List ℕ), D.eval (List.ofFn fun i : Fin 10 => m.testBit i.val) = true) →
      (∀ m ∈ ([554, 50, 581, 616, 116, 650, 713, 208, 773, 276, 897, 402] : List ℕ), D.eval (List.ofFn fun i : Fin 10 => m.testBit i.val) = false) →
      (∃ m ∈ ([3, 12, 24, 17, 33, 264] : List ℕ), D.eval (List.ofFn fun i : Fin 10 => m.testBit i.val) = false) →
      (∃ m ∈ ([562, 628, 720, 788, 914] : List ℕ), D.eval (List.ofFn fun i : Fin 10 => m.testBit i.val) = true) → False) :

  have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => (∃ x2 ∈ [(3 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (264 : ℕ)], x1.eval ((List.ofFn fun (x3 : Fin (9 : ℕ)) => x2.testBit ↑x3) ++ [Bool.false]) = Bool.false) ∧ ∃ x2 ∈ [(50 : ℕ), (116 : ℕ), (208 : ℕ), (276 : ℕ), (402 : ℕ)], x1.eval ((List.ofFn fun (x3 : Fin (9 : ℕ)) => x2.testBit ↑x3) ++ [Bool.true]) = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Bool := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) => x2.eval ((List.ofFn fun (x4 : Fin (9 : ℕ)) => x3.testBit ↑x4) ++ [x3.testBit (0 : ℕ) || x3.testBit (3 : ℕ)]); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x3.gates.length = (14 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x3 → x3.output = (23 : ℕ) → x1 x3 → (∀ x8 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (264 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ)], x2 x3 x8 = Bool.true) → ¬∀ x9 ∈ [(42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)], x2 x3 x9 = Bool.false := by

  dsimp only
  intro C length basis output usesExtra positive negative
  obtain ⟨D, dLen, dOut, dShape, agree⟩ := normalize C length basis
  have dBasis : Monotone2 D := by
    intro g hg
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hg
    let k : Fin 14 := ⟨j, by omega⟩
    have hGet : D.gates.getD k.val ⟨.or, []⟩ = g := by
      rw [List.getD_eq_getElem _ _ hj, he]
    have h := dShape k
    dsimp only at h
    rw [hGet] at h
    rcases h with rfl | ⟨a,b,_,_,_,rfl | rfl⟩ <;> simp
  have dOutput : D.output = 23 := dOut.trans output
  have posTable : ∀ r ∈ ([515,6,524,536,529,545,66,132,776,160,320,288] : List ℕ),
      ∃ m ∈ ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ),
        List.ofFn (fun i : Fin 10 => r.testBit i.val) =
          List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [m.testBit 0 || m.testBit 3] := by
    decide +kernel
  have negTable : ∀ r ∈ ([554,50,581,616,116,650,713,208,773,276,897,402] : List ℕ),
      ∃ m ∈ ([42,50,69,104,116,138,201,208,261,276,385,402] : List ℕ),
        List.ofFn (fun i : Fin 10 => r.testBit i.val) =
          List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [m.testBit 0 || m.testBit 3] := by
    decide +kernel
  have lowTable : ∀ m ∈ ([3,12,24,17,33,264] : List ℕ),
      List.ofFn (fun i : Fin 10 => m.testBit i.val) =
        List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [false] := by
    decide +kernel
  have highTable : ∀ m ∈ ([50,116,208,276,402] : List ℕ),
      ∃ r ∈ ([562,628,720,788,914] : List ℕ),
        List.ofFn (fun i : Fin 10 => r.testBit i.val) =
          List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [true] := by
    decide +kernel
  have evalEq (r : ℕ) : D.eval (List.ofFn fun i : Fin 10 => r.testBit i.val) =
      C.eval (List.ofFn fun i : Fin 10 => r.testBit i.val) :=
    agree _ (by simp)
  have yes : ∀ r ∈ ([515,6,524,536,529,545,66,132,776,160,320,288] : List ℕ),
      D.eval (List.ofFn fun i : Fin 10 => r.testBit i.val) = true := by
    intro r hr
    obtain ⟨m,hm,he⟩ := posTable r hr
    rw [evalEq,he]
    exact positive m hm
  have no : ∀ r ∈ ([554,50,581,616,116,650,713,208,773,276,897,402] : List ℕ),
      D.eval (List.ofFn fun i : Fin 10 => r.testBit i.val) = false := by
    intro r hr
    obtain ⟨m,hm,he⟩ := negTable r hr
    rw [evalEq,he]
    exact negative m hm
  have rejectLow : ∃ r ∈ ([3,12,24,17,33,264] : List ℕ),
      D.eval (List.ofFn fun i : Fin 10 => r.testBit i.val) = false := by
    obtain ⟨m,hm,hval⟩ := usesExtra.1
    exact ⟨m,hm,by rw [evalEq,lowTable m hm]; exact hval⟩
  have acceptHigh : ∃ r ∈ ([562,628,720,788,914] : List ℕ),
      D.eval (List.ofFn fun i : Fin 10 => r.testBit i.val) = true := by
    obtain ⟨m,hm,hval⟩ := usesExtra.2
    obtain ⟨r,hr,he⟩ := highTable m hm
    exact ⟨r,hr,by rw [evalEq,he]; exact hval⟩
  have last := lastGate D dLen dOutput dBasis yes no
  have hlast : 13 < D.gates.length := by omega
  have ops := (dBasis D.gates[13] (List.getElem_mem hlast)).1
  rw [← List.getD_eq_getElem D.gates ⟨.or, []⟩ hlast] at ops
  rcases ops with ha | ho
  · exact andCase D dLen dOutput dShape ha last yes no rejectLow acceptHigh
  · exact orCase D dLen dOutput dShape ho last yes no rejectLow acceptHigh
