import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_269 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 9]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 10]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 14]⟩], output := 15 } :
      PEqualNP.CircuitLowerBounds.Circuit) →
    (PEqualNP.MetaComplexity.Monotone2 C ∧
      (∃ A : Finset ℕ, A.card ≤ 3 ∧
        ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
          C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧
    (∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 5, (u.val, v.val) ∈
        ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3),
          (2, 4), (3, 4)] : List (ℕ × ℕ)) ∧
        x u = true ∧ x v = true)) := by
  intro C hC
  subst C
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · refine ⟨{0, 5, 10}, by decide, ?_⟩
    intro j g hg hop
    have hj : j < 11 := by
      by_contra h
      push_neg at h
      rw [List.getElem?_eq_none (by change 11 ≤ j; omega)] at hg
      simp at hg
    interval_cases j <;> (simp at hg; subst g; simp_all)
  · intro x
    let edges : List (Fin 5 × Fin 5) :=
      [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
    have edges_spec :
        edges.any (fun p => x p.1 && x p.2) = true ↔
          ∃ u v : Fin 5, (u.val, v.val) ∈ edges.map (fun p => (p.1.val, p.2.val)) ∧
            x u = true ∧ x v = true := by
      rw [List.any_eq_true]
      constructor
      · rintro ⟨⟨u, v⟩, huv, hbits⟩
        exact ⟨u, v, List.mem_map_of_mem huv, Bool.and_eq_true_iff.mp hbits⟩
      · rintro ⟨u, v, huv, hu, hv⟩
        obtain ⟨⟨a, b⟩, hab, heq⟩ := List.mem_map.mp huv
        have ha : a = u := Fin.ext (congrArg Prod.fst heq)
        have hb : b = v := Fin.ext (congrArg Prod.snd heq)
        subst a
        subst b
        exact ⟨(u, v), hab, Bool.and_eq_true_iff.mpr ⟨hu, hv⟩⟩
    change _ ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ edges.map (fun p => (p.1.val, p.2.val)) ∧
      x u = true ∧ x v = true
    rw [← edges_spec]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl_cons, List.foldl_nil, List.ofFn_succ, List.ofFn_zero,
      List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id, Bool.and_true, Bool.or_false, edges,
      Bool.and_eq_true, Bool.or_eq_true]
    grind
