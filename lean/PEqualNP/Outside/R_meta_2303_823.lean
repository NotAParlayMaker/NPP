import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2303_823
    (normalize : let row (x : Fin 9 → Bool) := List.ofFn x ++ [x 0]
      ∀ C : Circuit, FanInTwo C →
        (∀ B : Circuit, FanInTwo B → (∀ x, B.eval (row x) = C.eval (row x)) → C.size ≤ B.size) →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ D.output ≤ 10+C.size ∧
        (∀ j : Fin D.gates.length, ∀ i ∈ (D.gates.get j).inputs, i ≤ 10 + j.val) ∧ (∀ xs : List Bool, xs.length = 10 → D.eval xs = C.eval xs) ∧
        (let forced (j : ℕ) (x : Fin 9 → Bool) (b : Bool) :=
        (Circuit.mk (D.gates.drop (j+1)) D.output).eval
          ((Circuit.mk (D.gates.take j) 0).wires (row x) ++ [b])
      ∀ j < D.size, ∀ a < 10+j, ∃ x : Fin 9 → Bool,
        let w := D.wires (row x)
        w.getD (10+j) false ≠ w.getD a false ∧ forced j x false ≠ forced j x true))
    (finite : let truth (x : Fin 9 → Bool) := ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any fun p =>
        (List.ofFn x).getD (p / 9) false && (List.ofFn x).getD (p % 9) false
      let row (x : Fin 9 → Bool) := List.ofFn x ++ [x 0]
      ∀ D : Circuit, FanInTwo D → D.size = 14 → D.output ≤ 24 →
      (∀ j : Fin D.gates.length, ∀ i ∈ (D.gates.get j).inputs, i ≤ 10 + j.val) →
      (let forced (j : ℕ) (x : Fin 9 → Bool) (b : Bool) :=
        (Circuit.mk (D.gates.drop (j+1)) D.output).eval
          ((Circuit.mk (D.gates.take j) 0).wires (row x) ++ [b])
      ∀ j < D.size, ∀ a < 10+j, ∃ x : Fin 9 → Bool,
        let w := D.wires (row x)
        w.getD (10+j) false ≠ w.getD a false ∧ forced j x false ≠ forced j x true) →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 6]) ≠ truth x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (14 : ℕ) → (∀ (x4 : Fin (9 : ℕ) → Bool), x4 (0 : Fin (9 : ℕ)) = Bool.true ∨ x4 (6 : Fin (9 : ℕ)) = Bool.false → x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ))]) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → (∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → (∀ (x7 : Fin (9 : ℕ) → Bool), x5.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ))]) = x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ))])) → (14 : ℕ) ≤ x5.size) → ∃ (x6 : Fin (9 : ℕ) → Bool), x6 (0 : Fin (9 : ℕ)) = Bool.false ∧ x6 (6 : Fin (9 : ℕ)) = Bool.true ∧ x1.eval (List.ofFn x6 ++ [Bool.true]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro C fan size agree minimum
  let row (x : Fin 9 → Bool) := List.ofFn x ++ [x 0]
  let truth (x : Fin 9 → Bool) := ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any fun p =>
        (List.ofFn x).getD (p / 9) false && (List.ofFn x).getD (p % 9) false
  let graph (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  have target_ok (x : Fin 9 → Bool) : truth x = graph x := by
    change ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 5 && x 7) || ((x 6 && x 8) || ((x 8 && x 5) || false)))))))))))) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    simp only [Bool.or_assoc, Bool.or_false]
  have minC : ∀ B : Circuit, FanInTwo B →
      (∀ x, B.eval (row x) = C.eval (row x)) → C.size ≤ B.size := by
    rw [size]
    exact minimum
  obtain ⟨D, legal, sameSize, output, wires, same, sensitive⟩ := normalize C fan minC
  obtain ⟨x, bad⟩ := finite D legal (sameSize.trans size) (by omega) wires sensitive
  have fail : C.eval (List.ofFn x ++ [x 0 || x 6]) ≠ graph x := by
    intro hx
    exact bad ((same _ (by simp)).trans (hx.trans (target_ok x).symm))
  cases h0 : x 0 <;> cases h6 : x 6
  · exact False.elim (fail (by simpa only [graph,h0,h6,Bool.false_or] using agree x (Or.inr h6)))
  · exact ⟨x,h0,h6, by simpa only [graph,h0,h6,Bool.false_or] using fail⟩
  · exact False.elim (fail (by simpa only [graph,h0,h6,Bool.true_or] using agree x (Or.inl h0)))
  · exact False.elim (fail (by simpa only [graph,h0,h6,Bool.true_or] using agree x (Or.inl h0)))
