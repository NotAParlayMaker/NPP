import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

theorem PEqualNP.Outside.R_meta_1920_519
    (compile : ∀ C : Circuit, FanInTwo C → ∃ (B : BinaryCircuit) (p : Bool),
      (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) ∧ B.size + notCount C ≤ C.size ∧
      ∀ w : List Bool, w.length = 9 → (B.eval (w ++ [false]) != p) = C.eval w)
    (signedBound : ∀ (B : BinaryCircuit) (p : Bool), (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) →
      (∀ x : Fin 9 → Bool, (B.eval (List.ofFn x ++ [false]) != p) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      14 ≤ B.size)
    (monotoneBound : ∀ C : Circuit, Monotone2 C →
      (∀ m ∈ ([3,6,12,17,22,24,33,66,82,132,148,160,176,264,288,304,320,336] : List ℕ),
        C.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [!m.testBit 4]) = true) →
      (∀ m ∈ ([42,50,69,100,104,116,138,201,208,261,276,385,386,402] : List ℕ),
        C.eval (List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [!m.testBit 4]) = false) →
      15 ≤ C.size) :∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate), x1.length = (15 : ℕ) → x1.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(4 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (∀ (x4 : Fin x1.length), (∃ (x5 : ℕ) (x6 : ℕ), x5 ≤ x6 ∧ x6 ≤ (9 : ℕ) + ↑x4 ∧ (x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∨ x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate })) ∨ ∃ x5 ≤ (9 : ℕ) + ↑x4, x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x5] : PEqualNP.CircuitLowerBounds.Gate }) → ∃ (x5 : Fin (9 : ℕ) → Bool), { gates := x1, output := (23 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x5) ≠ (fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) x5 := by
  intro gates length head shape
  let C : Circuit := ⟨gates,23⟩
  let target := fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  let pred : Gate → Bool := fun g =>
    @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _)
  change ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠ target x
  by_contra lacks
  have eval (x : Fin 9 → Bool) : C.eval (List.ofFn x) = target x := by
    by_contra h
    exact lacks ⟨x,h⟩
  have fan : FanInTwo C := by
    intro g hg
    obtain ⟨i,hg'⟩ := List.mem_iff_get.mp hg
    rw [← hg']
    rcases shape i with ⟨a,b,_,_,hop⟩ | ⟨a,_,hop⟩
    · rcases hop with hop | hop
      · rw [hop]; exact ⟨Or.inl rfl, Nat.le_refl 2⟩
      · rw [hop]; exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
    · rw [hop]; exact ⟨Or.inr (Or.inr rfl), by change 1 ≤ 2; decide⟩
  cases gates with
  | nil => cases head
  | cons g tail =>
    have hg : g = ⟨GateOp.not,[4]⟩ := Option.some.inj head
    let D : Circuit := ⟨tail,23⟩
    have dLen : D.size = 14 := by
      change tail.length = 14
      simp only [List.length_cons] at length
      omega
    have fanD : FanInTwo D := fun a ha => fan a (List.mem_cons_of_mem _ ha)
    let row := fun x : Fin 9 → Bool => List.ofFn x ++ [!x 4]
    have correct (x : Fin 9 → Bool) : D.eval (row x) = target x := by
      have e := eval x
      let step := fun (w : List Bool) (a : Gate) =>
        w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)]
      change (tail.foldl step (step (List.ofFn x) g)).getD 23 false = _ at e
      rw [hg] at e
      have read : (List.ofFn x).getD 4 false = x 4 := by
        have h : 4 < (List.ofFn x).length := by simp
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
        simp only [List.getElem_ofFn,Option.getD_some] <;> rfl
      change (tail.foldl step (List.ofFn x ++ [!((List.ofFn x).getD 4 false)])).getD 23 false = _ at e
      rw [read] at e
      exact e
    by_cases zero : notCount D = 0
    · have monotone : Monotone2 D := by
        intro a ha
        have hno : a.op ≠ GateOp.not := by
          intro h
          have hm : a ∈ D.gates.filter pred :=
            List.mem_filter.mpr ⟨ha, by simp [pred,h]⟩
          have hnil : D.gates.filter pred = [] := List.eq_nil_of_length_eq_zero zero
          rw [hnil] at hm
          exact List.not_mem_nil hm
        have fg := fanD a ha
        rcases fg.1 with h | h | h
        · exact ⟨Or.inl h,fg.2⟩
        · exact ⟨Or.inr h,fg.2⟩
        · exact (hno h).elim
      have bound := monotoneBound D monotone (by
        intro m hm
        change D.eval (row (fun i => m.testBit i.val)) = true
        rw [correct]
        have tests : ∀ m ∈ ([3,6,12,17,22,24,33,66,82,132,148,160,176,264,288,304,320,336] : List ℕ),
            target (fun i => m.testBit i.val) = true := by decide +kernel
        exact tests m hm) (by
        intro m hm
        change D.eval (row (fun i => m.testBit i.val)) = false
        rw [correct]
        have tests : ∀ m ∈ ([42,50,69,100,104,116,138,201,208,261,276,385,386,402] : List ℕ),
            target (fun i => m.testBit i.val) = false := by decide +kernel
        exact tests m hm)
      omega
    · have hasTwo : 2 ≤ notCount C := by
        change 2 ≤ ((g::tail).filter pred).length
        rw [hg]
        simp only [List.filter_cons]
        have hhead : pred (⟨GateOp.not,[4]⟩ : Gate) = true := by
          simp [pred]
        simp [hhead]
        have htail : (tail.filter pred).length = notCount D := rfl
        omega
      obtain ⟨B,p,corner,cost,replay⟩ := compile C fan
      have bound := signedBound B p corner (fun x =>
        (replay (List.ofFn x) (by simp)).trans (eval x))
      have cLen : C.size = 15 := length
      omega
