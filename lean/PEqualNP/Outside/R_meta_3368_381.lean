import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Input four is permanently false. Keep it as an explicit zero wire in every candidate.
-- This leaves a search over earlier-wire operands with fixed gate arities.
theorem PEqualNP.Outside.R_meta_3368_381
    (normalize : ∀ (n z : ℕ) (C : Circuit),
      z < n → FanInTwo C →
    ∃ D : Circuit, D.size = C.size ∧ D.output < n + D.size ∧
      (∀ i g, D.gates[i]? = some g →
        (∀ w ∈ g.inputs, w < n+i) ∧
        ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∨
           g.op = .not ∧ g.inputs.length = 1)) ∧
      ∀ x : List Bool, x.length = n → x.getD z false = false → D.eval x = C.eval x)
    (bounded :
      let E := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9))
      ∀ D : Circuit, D.size ≤ 13 → D.output < 11 + D.size →
        (∀ i g, D.gates[i]? = some g → (∀ w ∈ g.inputs, w < 11+i) ∧
          ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∨
            g.op = .not ∧ g.inputs.length = 1)) →
        ∃ x : Fin 9 → Bool, D.eval (List.ofFn (Function.update x 4 false) ++
          [x 0 || x 4, x 4 || x 1]) ≠ E.any (fun e => x e.1 && x e.2)) : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (13 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ))]) = x1 x5) → False := by
  intro target C fan size eval
  obtain ⟨D,sizeD,out,legal,correct⟩ := normalize 11 4 C (by decide) fan
  obtain ⟨x,diff⟩ := bounded D (sizeD ▸ size) out legal
  let ws := List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 1]
  have len : ws.length = 11 := by simp [ws]
  have zero : ws.getD 4 false = false := by
    dsimp only [ws]
    rw [List.getD_append _ _ _ _ (by simp),
      List.getD_eq_getElem (List.ofFn (Function.update x 4 false)) false (by simp),
      List.getElem_ofFn]
    simp
  exact diff ((correct ws len zero).trans (eval x))
