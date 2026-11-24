import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

theorem PEqualNP.Outside.R_meta_2375_523
    (compile : ∀ (C : Circuit) (o : ℕ), FanInTwo C → ∃ (B : BinaryCircuit) (r : ℕ) (p q : Bool),
      (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) ∧ B.size + notCount C ≤ C.size ∧
      ∀ w : List Bool, w.length = 10 →
        let a := B.wires (w ++ [false])
        let b := C.wires w
        (a.getD B.output false != p) = b.getD C.output false ∧ (a.getD r false != q) = b.getD o false)
    (signedBound : ∀ (B : BinaryCircuit) (o : ℕ) (p q : Bool), (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) →
      let l := fun x : Fin 10 → Bool => ((B.wires (List.ofFn x ++ [false])).getD B.output false != p)
      let r := fun x : Fin 10 → Bool => ((B.wires (List.ofFn x ++ [false])).getD o false != q)
      (∃ x, l x = true ∧ r x = false) → (∃ x, l x = false ∧ r x = true) →
      (∀ x, (l x && r x) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) → 18 ≤ B.size)
    (monotoneBound : ∀ (C : Circuit) (o : ℕ), Monotone2 C →
      let l := fun x : Fin 10 → Bool => (C.wires (List.ofFn x)).getD C.output false
      let r := fun x : Fin 10 → Bool => (C.wires (List.ofFn x)).getD o false
      (∃ x, l x = true ∧ r x = false) → (∃ x, l x = false ∧ r x = true) →
      (∀ m ∈ ([3,6,12,17,24,33,66,132,160,264,288,320,528,576,640] : List ℕ), (l (fun i => m.testBit i.val) && r (fun i => m.testBit i.val)) = true) →
      (∀ m ∈ ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ), (l (fun i => m.testBit i.val) && r (fun i => m.testBit i.val)) = false) →
      19 ≤ C.size) :∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.true → x9 x12 x3 = Bool.true ∧ x9 x12 x4 = Bool.true) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.false ∧ x9 x13 x3 = Bool.true ∧ x9 x13 x4 = Bool.true := by
  dsimp only
  intro g D a b fanG fanD small leftOnly rightOnly pos
  let C : Circuit := ⟨g :: D.gates,a⟩
  let l := fun x : Fin 10 → Bool => (C.wires (List.ofFn x)).getD a false
  let r := fun x : Fin 10 → Bool => (C.wires (List.ofFn x)).getD b false
  let F := fun x : Fin 10 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
  change (∃ x, l x = true ∧ r x = false) at leftOnly
  change (∃ x, l x = false ∧ r x = true) at rightOnly
  change (∀ x, F x = true → l x = true ∧ r x = true) at pos
  change ∃ x, F x = false ∧ l x = true ∧ r x = true
  by_contra lacks
  have comp (x : Fin 10 → Bool) : (l x && r x) = F x := by
    cases h : F x
    · cases hl : l x <;> cases hr : r x
      · rfl
      · rfl
      · rfl
      · exact (lacks ⟨x,h,hl,hr⟩).elim
    · obtain ⟨hl,hr⟩ := pos x h
      simp [hl,hr]
  have size : C.size ≤ 18 := by
    change D.gates.length + 1 ≤ 18
    change D.gates.length ≤ 17 at small
    omega
  have fan : FanInTwo C := by
    intro h hh
    rcases List.mem_cons.mp hh with e | hh
    · subst h
      exact fanG g (by simp)
    · exact fanD h hh
  by_cases zero : notCount C = 0
  · have mono : Monotone2 C := by
      intro g hg
      have hno : g.op ≠ GateOp.not := by
        intro e
        let pred : Gate → Bool := fun v =>
          @decide (v.op = GateOp.not) (lineDegreeGateOpDecEq _ _)
        have hm : g ∈ C.gates.filter pred := List.mem_filter.mpr ⟨hg, by simp [pred,e]⟩
        have hnil : C.gates.filter pred = [] := List.eq_nil_of_length_eq_zero zero
        rw [hnil] at hm
        exact List.not_mem_nil hm
      have fg := fan g hg
      rcases fg.1 with h | h | h
      · exact ⟨Or.inl h,fg.2⟩
      · exact ⟨Or.inr h,fg.2⟩
      · exact (hno h).elim
    have bound := monotoneBound C b mono leftOnly rightOnly (by
      intro m hm
      change (l (fun i => m.testBit i.val) && r (fun i => m.testBit i.val)) = true
      rw [comp]
      have tests : ∀ m ∈ ([3,6,12,17,24,33,66,132,160,264,288,320,528,576,640] : List ℕ),
          F (fun i => m.testBit i.val) = true := by decide +kernel
      exact tests m hm) (by
      intro m hm
      change (l (fun i => m.testBit i.val) && r (fun i => m.testBit i.val)) = false
      rw [comp]
      have tests : ∀ m ∈ ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ),
          F (fun i => m.testBit i.val) = false := by decide +kernel
      exact tests m hm)
    omega
  · obtain ⟨B,o,p,q,shape,cost,replay⟩ := compile C b fan
    have eq (x : Fin 10 → Bool) :
        ((B.wires (List.ofFn x ++ [false])).getD B.output false != p) = l x ∧
        ((B.wires (List.ofFn x ++ [false])).getD o false != q) = r x :=
      replay (List.ofFn x) (by simp)
    have bound := signedBound B o p q shape (by
      obtain ⟨x,hl,hr⟩ := leftOnly
      exact ⟨x,(eq x).1.trans hl,(eq x).2.trans hr⟩) (by
      obtain ⟨x,hl,hr⟩ := rightOnly
      exact ⟨x,(eq x).1.trans hl,(eq x).2.trans hr⟩) (by
      intro x
      dsimp only
      rw [(eq x).1,(eq x).2]
      exact comp x)
    omega