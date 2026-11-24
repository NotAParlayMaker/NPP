import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1747

open PEqualNP.CircuitLowerBounds

def C0 : Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [44, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [45, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [46, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [47, 43] }], output := 48 }

theorem ofFn13 (x : Fin 13 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12] := by
  simp [List.ofFn_succ]

-- The circuit reads only the points 0, 1, 2, 5 and the lines 0, 1, 2, 4.
def form (a0 a1 a2 a5 b0 b1 b2 b4 : Bool) : Bool :=
  (b0 || b1 || b2 || b4) && (b0 || b1 || a2 || a5) && (b0 || a1 || a2 || b4) &&
  (a0 || b1 || b2 || a5) && (a0 || a1 || b2 || b4) && (a0 || a1 || a2 || a5)

theorem ev0 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
    b12 : Bool) :
    C0.eval ([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12] ++
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]) = form a0 a1 a2 a5 b0 b1 b2 b4 := by
  simp only [C0, Circuit.eval, Circuit.wires, List.foldl, List.map, List.cons_append,
    List.nil_append, List.getD_cons_zero, List.getD_cons_succ, GateOp.eval, List.all_cons,
    List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false, form]

-- A line missing the point set holds none of its points; then the formula is false.
theorem form_false (a0 a1 a2 a5 b0 b1 b2 b4 : Bool)
    (h0 : b0 = true → a0 = false ∧ a1 = false) (h1 : b1 = true → a1 = false ∧ a2 = false)
    (h2 : b2 = true → a2 = false ∧ a5 = false) (h4 : b4 = true → a0 = false ∧ a5 = false) :
    form a0 a1 a2 a5 b0 b1 b2 b4 = false := by
  revert h0 h1 h2 h4
  cases a0 <;> cases a1 <;> cases a2 <;> cases a5 <;> cases b0 <;> cases b1 <;> cases b2 <;>
    cases b4 <;> decide

theorem incident_rows : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
    form (decide ((0 : Fin 13) = p)) (decide ((1 : Fin 13) = p)) (decide ((2 : Fin 13) = p))
      (decide ((5 : Fin 13) = p)) (decide ((0 : Fin 13) = l)) (decide ((1 : Fin 13) = l))
      (decide ((2 : Fin 13) = l)) (decide ((4 : Fin 13) = l)) =
    decide (((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 1), (2, 2), (5, 4)] : List (ℕ × ℕ))) := by
  decide

theorem miss (Q : Finset (Fin 13)) (v a : Fin 13)
    (h : decide (∀ r ∈ Q, r - v ∉ ({0, 1, 3, 9} : Finset (Fin 13))) = true)
    (ha : a - v ∈ ({0, 1, 3, 9} : Finset (Fin 13))) : decide (a ∈ Q) = false := by
  rw [decide_eq_true_iff] at h
  rw [decide_eq_false_iff_not]
  intro haQ
  exact h a haQ ha

end PEqualNP.Outside.L_meta_1747

theorem PEqualNP.Outside.L_meta_1747 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [44, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [45, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [46, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [47, 43] }], output := 48 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 23 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (13 + 13) C ∧
  (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
     C.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l)))
       = decide (((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 1), (2, 2), (5, 4)] : List (ℕ × ℕ)))) ∧
  (∀ Q : Finset (Fin 13), Q.card = 4 →
     (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
     C.eval (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q))
             ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) := by
  intro C hC
  have hC0 : C = PEqualNP.Outside.L_meta_1747.C0 := hC
  subst hC0
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · unfold PEqualNP.MetaComplexity.NestedCover.ReadsBack
    decide
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_1747.C0, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro p l hpl
    rw [PEqualNP.Outside.L_meta_1747.ofFn13, PEqualNP.Outside.L_meta_1747.ofFn13,
      PEqualNP.Outside.L_meta_1747.ev0]
    exact PEqualNP.Outside.L_meta_1747.incident_rows p l hpl
  · intro Q _ _
    rw [PEqualNP.Outside.L_meta_1747.ofFn13, PEqualNP.Outside.L_meta_1747.ofFn13,
      PEqualNP.Outside.L_meta_1747.ev0]
    apply PEqualNP.Outside.L_meta_1747.form_false
    · intro h
      exact ⟨PEqualNP.Outside.L_meta_1747.miss Q 0 0 h (by decide),
        PEqualNP.Outside.L_meta_1747.miss Q 0 1 h (by decide)⟩
    · intro h
      exact ⟨PEqualNP.Outside.L_meta_1747.miss Q 1 1 h (by decide),
        PEqualNP.Outside.L_meta_1747.miss Q 1 2 h (by decide)⟩
    · intro h
      exact ⟨PEqualNP.Outside.L_meta_1747.miss Q 2 2 h (by decide),
        PEqualNP.Outside.L_meta_1747.miss Q 2 5 h (by decide)⟩
    · intro h
      exact ⟨PEqualNP.Outside.L_meta_1747.miss Q 4 0 h (by decide),
        PEqualNP.Outside.L_meta_1747.miss Q 4 5 h (by decide)⟩
