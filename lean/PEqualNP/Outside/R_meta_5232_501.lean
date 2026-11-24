import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_5232_501
    (monotoneLower : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (10 : ℕ) C →
      C.size ≤ (19 : ℕ) →
      (10 : ℕ) ≤ C.output →
      C.output < (10 : ℕ) + C.size →
      ∃ (x7 : Fin (10 : ℕ) → Bool),
        C.eval (List.ofFn x7) ≠
          (x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)))) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (11 : ℕ) x1 → x1.size ≤ (18 : ℕ) → (11 : ℕ) ≤ x1.output → x1.output < (11 : ℕ) + x1.size → ∃ (x7 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ))]) ≠ (x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) := by
  intro C hMono hRB hSize hLo hHi
  let g0 : Gate := ⟨GateOp.or, [0, 2]⟩
  let D : Circuit := ⟨g0 :: C.gates, C.output⟩
  have hDMono : Monotone2 D := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hmem
    · exact ⟨Set.mem_insert_of_mem _ rfl, by simp [g0]⟩
    · exact hMono g hmem
  have hDRB : ReadsBack 10 D := by
    intro j hj i hi
    cases j with
    | zero =>
      change i ∈ ([0, 2] : List ℕ) at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    | succ k =>
      have hk : k < C.gates.length := by
        change k + 1 < C.gates.length + 1 at hj
        omega
      have hgate : gateAt D (k + 1) = gateAt C k := rfl
      rw [hgate] at hi
      have hlt := hRB k hk i hi
      omega
  have hDSize : D.size ≤ 19 := by
    change C.gates.length + 1 ≤ 19
    change C.gates.length ≤ 18 at hSize
    omega
  have hDLo : 10 ≤ D.output := by
    change 10 ≤ C.output
    omega
  have hDHi : D.output < 10 + D.size := by
    change C.output < 10 + (C.gates.length + 1)
    change C.output < 11 + C.gates.length at hHi
    omega
  obtain ⟨x, hx⟩ := monotoneLower D hDMono hDRB hDSize hDLo hDHi
  refine ⟨x, ?_⟩
  have hEval : D.eval (List.ofFn x) = C.eval (List.ofFn x ++ [x 0 || x 2]) := by
    have key : ((List.ofFn x).getD 0 false || ((List.ofFn x).getD 2 false || false)) = (x 0 || x 2) := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, Bool.or_false]
      rfl
    show (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn x ++ [(List.ofFn x).getD 0 false || ((List.ofFn x).getD 2 false || false)])).getD
        C.output false = _
    rw [key]
    rfl
  rw [← hEval]
  exact hx
