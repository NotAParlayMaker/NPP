import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1928_67
    (binary_cost : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      13 + D.gates.countP (fun g => GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op) ≤ D.size)
    (monotone_cost : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 && x 4]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      15 ≤ D.size)
    (one_or_two_cost : ∀ D : Circuit, FanInTwo D →
      1 ≤ D.gates.countP (fun g => GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op) → D.gates.countP (fun g => GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op) ≤ 2 →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 && x 4]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      15 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (∃ (x4 : Fin (9 : ℕ) → Bool), (x4 (0 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ))) = Bool.false ∧ x1.eval (List.ofFn x4 ++ [Bool.false]) ≠ (fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) x4) ∨ ∃ (x4 : Fin (9 : ℕ) → Bool), (x4 (0 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ))) = Bool.true ∧ x1.eval (List.ofFn x4 ++ [Bool.true]) = Bool.false := by
  intro D hfan hsmall
  classical
  by_contra hn
  have hfull (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 0 && x 4]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    cases e : (x 0 && x 4) with
    | false =>
      have he : (x 4 && x 0) = false := by rwa [Bool.and_comm]
      simp only [he, Bool.or_false]
      by_contra bad
      exact hn (Or.inl ⟨x, e, bad⟩)
    | true =>
      have he : (x 4 && x 0) = true := by rwa [Bool.and_comm]
      simp only [he, Bool.or_true, Bool.true_or]
      cases hv : D.eval (List.ofFn x ++ [true]) with
      | false => exact False.elim (hn (Or.inr ⟨x, e, hv⟩))
      | true => rfl
  let isNot := fun g : Gate => GateOp.rec (motive := fun _ => Bool)
      false false true (fun _ => false) false g.op
  let C : Circuit := ⟨⟨GateOp.and, [0, 4]⟩ :: D.gates, D.output⟩
  have hcFan : FanInTwo C := by
    intro g hg
    change g ∈ _ :: D.gates at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp
    · exact hfan g hg
  have hcEval (x : Fin 9 → Bool) : C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    rw [← hfull x]
    have pins (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt]
      rfl
    have ha := pins 0
    have hb := pins 4
    change (List.ofFn x).getD 0 false = x 0 at ha
    change (List.ofFn x).getD 4 false = x 4 at hb
    change D.eval (List.ofFn x ++ [((List.ofFn x).getD 0 false && ((List.ofFn x).getD 4 false && true))]) = _
    rw [ha, hb, Bool.and_true]
  have hc := binary_cost C hcFan hcEval
  have countC : C.gates.countP isNot = D.gates.countP isNot := by
    simp [C, isNot]
  have sizeC : C.size = D.size + 1 := by rfl
  change 13 + C.gates.countP isNot ≤ C.size at hc
  rw [countC, sizeC] at hc
  have upper : D.gates.countP isNot ≤ 2 := by omega
  by_cases zero : D.gates.countP isNot = 0
  · have hm : Monotone2 D := by
      intro g hg
      obtain ⟨ops, arity⟩ := hfan g hg
      have off : isNot g = false := by
        have all := List.countP_eq_zero.mp zero
        simpa using all g hg
      refine ⟨?_, arity⟩
      rcases ops with ha | hb | hn
      · exact Or.inl ha
      · exact Or.inr hb
      · change g.op = GateOp.not at hn
        simp [isNot, hn] at off
    have := monotone_cost D hm hfull
    omega
  · have positive : 1 ≤ D.gates.countP isNot := by omega
    have := one_or_two_cost D hfan positive upper hfull
    omega
