import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2768_713
    (splitter : ∀ C : Circuit, C.gates[0]? = some ⟨GateOp.or,[0,3]⟩ →
      (∀ g ∈ C.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∨
        ∃ i : ℕ, g = ⟨GateOp.not,[i]⟩) →
      C.gates.countP (fun g => g.op.eval [false]) = 1 →
      ∃ A B : Circuit, A.size+B.size+2=C.size ∧ Monotone2 A ∧ Monotone2 B ∧
      let w := fun x : Fin 9 → Bool => A.wires (List.ofFn x ++ [x 0 || x 3])
      let h := fun x => (w x).getD A.output false
      let k := fun x t => B.eval (w x ++ [t])
      Monotone h ∧ (∀ x y, x ≤ y → ∀ a b : Bool, a ≤ b → k x a ≤ k y b) ∧
      ∀ x, k x (!(h x)) = circuitFun 9 C x)
    (diamond : ∀ (n : ℕ) (f h : (Fin n → Bool) → Bool) (k : (Fin n → Bool) → Bool → Bool),
    Monotone f → Monotone h →
    (∀ x y, x ≤ y → ∀ a b : Bool, a ≤ b → k x a ≤ k y b) →
    (∀ x, k x (!(h x)) = f x) → (∀ b, ∃ x, k x b ≠ f x) →
    ∃ e i : Fin n → Bool, ∀ a b t : Bool, let x := if a then (if b then (fun j => e j || i j) else e)
        else (if b then i else (fun j => e j && i j))
      h x = b ∧ k x t = ((a && b) || ((a || b) && t)))
    (fixed : let f := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ A B : Circuit, Monotone2 A → Monotone2 B → A.size+B.size=13 →
      ∀ t : Bool, ∃ x : Fin 9 → Bool, B.eval (A.wires (List.ofFn x ++ [x 0 || x 3]) ++ [t]) ≠ f x)
    (obstruction : let f := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ A B : Circuit, Monotone2 A → Monotone2 B → A.size+B.size=13 →
      let w := fun x : Fin 9 → Bool => A.wires (List.ofFn x ++ [x 0 || x 3])
      let h := fun x => (w x).getD A.output false
      let k := fun x t => B.eval (w x ++ [t])
      (∃ e i : Fin 9 → Bool, ∀ a b t : Bool, let x := if a then (if b then (fun j => e j || i j) else e)
        else (if b then i else (fun j => e j && i j))
      h x = b ∧ k x t = ((a && b) || ((a || b) && t))) →
      ∃ x, k x (!(h x)) ≠ f x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (x1.gates.length = (15 : ℕ) ∧       x1.output = (23 : ℕ) ∧         x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧           ∀ (x2 : ℕ) (x3 : x2 < x1.gates.length),             have x4 : PEqualNP.CircuitLowerBounds.Gate := x1.gates[x2];             have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 < (9 : ℕ) + x2 ∨ x5 = (24 : ℕ);             have x6 : ℕ → ℕ := fun (x6 : ℕ) => if x6 < (9 : ℕ) then x6 else if x6 = (24 : ℕ) then (9 : ℕ) else x6 + (1 : ℕ);             x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } ∨ (∃ (x7 : ℕ), x5 x7 ∧ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x7] : PEqualNP.CircuitLowerBounds.Gate }) ∨ ∃ (x7 : ℕ) (x8 : ℕ), x5 x7 ∧ x5 x8 ∧ x6 x7 ≤ x6 x8 ∧ (x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate } ∨ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate })) →     List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op.eval [Bool.false]) x1.gates = (1 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) := by
  intro C form count same
  obtain ⟨len,_out,first,description⟩ := form
  have good : ∀ g ∈ C.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∨
        ∃ i : ℕ, g = ⟨GateOp.not,[i]⟩ := by
    intro g mem
    obtain ⟨j,hj,eq⟩ := List.getElem_of_mem mem
    obtain z | ⟨i,_ok,z⟩ | ⟨i,j,_v,_w,_order,z | z⟩ := description j hj
    · rw [← eq,z]
      exact Or.inl ⟨by simp,by decide⟩
    · exact Or.inr ⟨i,eq.symm.trans z⟩
    · rw [← eq,z]
      exact Or.inl ⟨by simp,Nat.le_refl 2⟩
    · rw [← eq,z]
      exact Or.inl ⟨by simp,Nat.le_refl 2⟩
  obtain ⟨A,B,sz,mA,mB,mh,mk,computes⟩ := splitter C first good count
  have cost : A.size+B.size=13 := by
    change A.size + B.size + 2 = C.gates.length at sz
    omega
  let f := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  have mf : Monotone f := by
    intro x y le
    have land : ∀ a b c d : Bool, a ≤ c → b ≤ d → (a && b) ≤ (c && d) := by decide
    have lor : ∀ a b c d : Bool, a ≤ c → b ≤ d → (a || b) ≤ (c || d) := by decide
    dsimp only [f]
    repeat' first | apply lor | apply land | exact le _
  let w := fun x : Fin 9 → Bool => A.wires (List.ofFn x ++ [x 0 || x 3])
  let h := fun x => (w x).getD A.output false
  let k := fun x t => B.eval (w x ++ [t])
  have ok : ∀ x, k x (!(h x)) = f x := fun x => (computes x).trans (congrFun same x)
  have stable : ∀ t, ∃ x, k x t ≠ f x := fixed A B mA mB cost
  have witness := diamond 9 f h k mf mh mk ok stable
  obtain ⟨x,bad⟩ := obstruction A B mA mB cost witness
  exact bad (ok x)
