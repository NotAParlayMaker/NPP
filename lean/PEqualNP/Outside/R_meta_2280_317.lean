import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The seven masks give the actual line neighbors of the seven points.
-- A counterexample must have an AND active on an independent pair. The
-- automorphisms preserving the extra OR move it into one of the listed rows.
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2280_317
    (normalize :
      let F (x : Fin 14 → Bool) := ∃ a b : Fin 14,
        (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD a.val 0).testBit b.val=true ∧ x a=true ∧ x b=true
      let L (r : Fin 14) (x : Fin 14 → Bool) := List.ofFn x ++ [GateOp.or.eval [x 0,x r]]
      let B (C : Circuit) (r : Fin 14) := (r=7 ∨ r=9) ∧ Monotone2 C ∧ C.size≤25 ∧
        ∀ x, ((F x ∧ ∀ v, x v=true → ¬F (Function.update x v false)) ∨
          ¬F x ∧ ∀ v, x v=false → F (Function.update x v true)) → (C.eval (L r x)=true ↔ F x)
      let H (C : Circuit) (r : Fin 14) := ∃ m ∈ (if r=7 then [314,541] else [127,244,2565] : List ℕ),
        ∃ (k : ℕ) (g : Gate), C.gates[k]?=some g ∧ g.op=.and ∧
          (C.wires (L r (fun i => m.testBit i.val))).getD (15+k) false=true
      ∀ (C : Circuit) (r : Fin 14), B C r → ∃ D : Circuit, B D r ∧ H D r)
    (exclude :
      let F (x : Fin 14 → Bool) := ∃ a b : Fin 14,
        (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD a.val 0).testBit b.val=true ∧ x a=true ∧ x b=true
      let L (r : Fin 14) (x : Fin 14 → Bool) := List.ofFn x ++ [GateOp.or.eval [x 0,x r]]
      let B (C : Circuit) (r : Fin 14) := (r=7 ∨ r=9) ∧ Monotone2 C ∧ C.size≤25 ∧
        ∀ x, ((F x ∧ ∀ v, x v=true → ¬F (Function.update x v false)) ∨
          ¬F x ∧ ∀ v, x v=false → F (Function.update x v true)) → (C.eval (L r x)=true ↔ F x)
      let H (C : Circuit) (r : Fin 14) := ∃ m ∈ (if r=7 then [314,541] else [127,244,2565] : List ℕ),
        ∃ (k : ℕ) (g : Gate), C.gates[k]?=some g ∧ g.op=.and ∧
          (C.wires (L r (fun i => m.testBit i.val))).getD (15+k) false=true
      ∀ (C : Circuit) (r : Fin 14), B C r → ¬H C r) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin (14 : ℕ)), x5 = (7 : Fin (14 : ℕ)) ∨ x5 = (9 : Fin (14 : ℕ)) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x8 : Fin (14 : ℕ) → Bool), x3 x8 → (x4.eval (List.ofFn x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x8 (0 : Fin (14 : ℕ)), x8 x5]]) = Bool.true ↔ x2 x8)) → (26 : ℕ) ≤ x4.size := by
  dsimp only
  intro C r hr mono good
  by_contra! hsmall
  let F (x : Fin 14 → Bool) := ∃ a b : Fin 14,
    (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD a.val 0).testBit b.val=true ∧ x a=true ∧ x b=true
  let E (x : Fin 14 → Bool) := ∃ a b : Fin 14, (a.val,b.val) ∈ ([(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)] : List (ℕ × ℕ)) ∧ x a=true ∧ x b=true
  have same : F=E := by
    funext x; apply propext
    have h : ∀ a b : Fin 14, ((([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD a.val 0).testBit b.val=true) ↔
        (a.val,b.val) ∈ ([(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)] : List (ℕ × ℕ)) := by decide +kernel
    simp only [F,E,h]
  obtain ⟨D,hd,hot⟩ := normalize C r ⟨hr,mono,by omega,by
    change ∀ x, ((F x ∧ ∀ v, x v=true → ¬F (Function.update x v false)) ∨
      ¬F x ∧ ∀ v, x v=false → F (Function.update x v true)) → (_ ↔ F x)
    rw [same]
    exact good⟩
  exact exclude D r hd hot
