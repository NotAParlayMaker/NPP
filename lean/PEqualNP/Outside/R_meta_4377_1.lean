import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 40000 in
set_option maxHeartbeats 7000000 in
theorem PEqualNP.Outside.R_meta_4377_1
    (ext : let decode (m : ℕ) : Finset (Fin 9) := Finset.univ.filter (fun i : Fin 9 => m.testBit i.val)
      let bits (m : ℕ) (i : Fin 9) := m.testBit i.val
      let edge (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
        List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      let input (T : Finset (Fin 9)) (x : Fin 9 → Bool) :=
        List.ofFn x ++ [x 0 || x 4, decide (∃ i ∈ T, x i = true)]
      ∀ k ∈ ([3, 5, 6, 9, 10, 12, 18, 20, 24, 34, 36, 65, 66, 68, 72, 80, 96, 132, 192, 260] : List ℕ),
        ∀ C : Circuit, Monotone2 C →
        (∀ m ∈ ([3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288, 42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ),
          C.eval (input (decode k) (bits m)) = edge (bits m)) →
        ∀ x : Fin 9 → Bool, C.eval (input (decode k) x) = edge x)
    (bound : let decode (m : ℕ) : Finset (Fin 9) := Finset.univ.filter (fun i : Fin 9 => m.testBit i.val)
      let edge (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
        List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      let input (T : Finset (Fin 9)) (x : Fin 9 → Bool) :=
        List.ofFn x ++ [x 0 || x 4, decide (∃ i ∈ T, x i = true)]
      ∀ k ∈ ([3, 5, 6, 9, 10, 12, 18, 20, 24, 34, 36, 65, 66, 68, 72, 80, 96, 132, 192, 260] : List ℕ),
        ∀ C : Circuit, Monotone2 C →
        (∀ x : Fin 9 → Bool, C.eval (input (decode k) x) = edge x) →
        (14 : ℕ) ≤ C.size) :
    have x1 : ℕ → Finset (Fin (9 : ℕ)) := fun (x1 : ℕ) => {x2 : Fin (9 : ℕ) | x1.testBit ↑x2 = Bool.true}; have x2 : ℕ → Fin (9 : ℕ) → Bool := fun (x2 : ℕ) (x3 : Fin (9 : ℕ)) => x2.testBit ↑x3; have x3 : (Fin (9 : ℕ) → Bool) → Bool := fun (x3 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x4 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x3 x4.1 && x3 x4.2; have x4 : Finset (Fin (9 : ℕ)) → (Fin (9 : ℕ) → Bool) → List Bool := fun (x4 : Finset (Fin (9 : ℕ))) (x5 : Fin (9 : ℕ) → Bool) => List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x6 ∈ x4, x5 x6 = Bool.true)]; ∀ x5 ∈ [(3 : ℕ), (5 : ℕ), (6 : ℕ), (9 : ℕ), (10 : ℕ), (12 : ℕ), (18 : ℕ), (20 : ℕ), (24 : ℕ), (34 : ℕ), (36 : ℕ), (65 : ℕ), (66 : ℕ), (68 : ℕ), (72 : ℕ), (80 : ℕ), (96 : ℕ), (132 : ℕ), (192 : ℕ), (260 : ℕ)], ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (13 : ℕ) → ∃ x10 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (264 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ), (42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)], x7.eval (x4 (x1 x5) (x2 x10)) ≠ x3 (x2 x10) := by
  intro x1 x2 x3 x4 k hk C hmono hsize
  by_contra hcon
  push Not at hcon
  let decode (m : ℕ) : Finset (Fin 9) := Finset.univ.filter (fun i : Fin 9 => m.testBit i.val)
  let bits (m : ℕ) (i : Fin 9) := m.testBit i.val
  let edge (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
    List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let input (T : Finset (Fin 9)) (x : Fin 9 → Bool) :=
    List.ofFn x ++ [x 0 || x 4, decide (∃ i ∈ T, x i = true)]
  have hagree : ∀ m ∈ ([3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288, 42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ),
      C.eval (input (decode k) (bits m)) = edge (bits m) := by
    intro m hm
    exact hcon m hm
  have hall : ∀ x : Fin 9 → Bool, C.eval (input (decode k) x) = edge x :=
    ext k hk C hmono hagree
  have h14 : (14 : ℕ) ≤ C.size := bound k hk C hmono hall
  omega
