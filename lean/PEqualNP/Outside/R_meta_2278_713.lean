import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2278_713
    (geometry : ∀ f : Fin 10 → Fin 10, (∀ i, f (f i) = i) → ¬ ((f 0 ∈ ([1,8] : List (Fin 10)) ∨ f 6 ∈ ([1,8] : List (Fin 10))) ∧
      (f 0 ∈ ([3,9] : List (Fin 10)) ∨ f 6 ∈ ([3,9] : List (Fin 10))) ∧
      (f 0 ∈ ([2,8] : List (Fin 10)) ∨ f 6 ∈ ([2,8] : List (Fin 10))) ∧
      (f 4 ∈ ([0,8] : List (Fin 10)) ∨ f 7 ∈ ([0,8] : List (Fin 10)))))
    (core : let f := fun x : Fin 14 → Bool => ∃ a b : Fin 14,
       14*a.val+b.val ∈ ([7,8,10,21,23,27,36,40,41,49,53,54,66,67,69,79,80,82,92,93,95] : List ℕ) ∧ x a = true ∧ x b = true
     let test := fun x : Fin 14 → Bool =>
       (f x ∧ ∀ i, x i = true → ¬ f (Function.update x i false)) ∨
       (¬ f x ∧ ∀ i, x i = false → f (Function.update x i true))
     ∀ C : Circuit, Monotone2 C →
       (∀ x, test x → (C.eval (List.ofFn x ++ [x 0 || x 1]) = true ↔ f x)) → C.gates.countP (fun g => GateOp.casesOn g.op true false false (fun _ => false) false) ≤ 6 →
       ∃ f : Fin 10 → Fin 10, (∀ i, f (f i) = i) ∧ (f 0 ∈ ([1,8] : List (Fin 10)) ∨ f 6 ∈ ([1,8] : List (Fin 10))) ∧
      (f 0 ∈ ([3,9] : List (Fin 10)) ∨ f 6 ∈ ([3,9] : List (Fin 10))) ∧
      (f 0 ∈ ([2,8] : List (Fin 10)) ∨ f 6 ∈ ([2,8] : List (Fin 10))) ∧
      (f 4 ∈ ([0,8] : List (Fin 10)) ∨ f 7 ∈ ([0,8] : List (Fin 10))))
    (budget : let f := fun x : Fin 14 → Bool => ∃ a b : Fin 14,
       14*a.val+b.val ∈ ([7,8,10,21,23,27,36,40,41,49,53,54,66,67,69,79,80,82,92,93,95] : List ℕ) ∧ x a = true ∧ x b = true
     let test := fun x : Fin 14 → Bool =>
       (f x ∧ ∀ i, x i = true → ¬ f (Function.update x i false)) ∨
       (¬ f x ∧ ∀ i, x i = false → f (Function.update x i true))
     ∀ C : Circuit, Monotone2 C →
       (∀ x, test x → (C.eval (List.ofFn x ++ [x 0 || x 1]) = true ↔ f x)) → 7 ≤ C.gates.countP (fun g => GateOp.casesOn g.op true false false (fun _ => false) false) → 26 ≤ C.size) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 : Fin (14 : ℕ) → Bool), x3 x6 → (x4.eval (List.ofFn x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x6 (0 : Fin (14 : ℕ)), x6 (1 : Fin (14 : ℕ))]]) = Bool.true ↔ x2 x6)) → (26 : ℕ) ≤ x4.size := by
  let edges : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
  let codes : List ℕ := [7,8,10,21,23,27,36,40,41,49,53,54,66,67,69,79,80,82,92,93,95]
  have encoded : ∀ a b : Fin 14, (a.val,b.val) ∈ edges ↔ 14*a.val+b.val ∈ codes := by
    dsimp only [edges,codes]
    decide
  let hit := fun x : Fin 14 → Bool => ∃ a b : Fin 14, (a.val,b.val) ∈ edges ∧ x a = true ∧ x b = true
  let packed := fun x : Fin 14 → Bool => ∃ a b : Fin 14, 14*a.val+b.val ∈ codes ∧ x a = true ∧ x b = true
  have eq : hit = packed := by
    funext x
    apply propext
    simp only [hit,packed,encoded]
  let extremal := fun (F : (Fin 14 → Bool) → Prop) (x : Fin 14 → Bool) =>
    (F x ∧ ∀ i, x i = true → ¬ F (Function.update x i false)) ∨
    (¬ F x ∧ ∀ i, x i = false → F (Function.update x i true))
  dsimp only
  intro C mono rows
  change ∀ x, extremal hit x → (C.eval (List.ofFn x ++ [GateOp.or.eval [x 0,x 1]]) = true ↔ hit x) at rows
  rw [eq] at rows
  have tests : ∀ x, extremal packed x → (C.eval (List.ofFn x ++ [x 0 || x 1]) = true ↔ packed x) := by
    have free (x : Fin 14 → Bool) : GateOp.or.eval [x 0,x 1] = (x 0 || x 1) := by
      cases x 0 <;> cases x 1 <;> rfl
    simpa only [free] using rows
  by_cases low : C.gates.countP (fun g => GateOp.casesOn g.op true false false (fun _ => false) false) ≤ 6
  · obtain ⟨f,inv,allFour⟩ := core C mono tests low
    exact False.elim (geometry f inv allFour)
  · exact budget C mono tests (by omega)
