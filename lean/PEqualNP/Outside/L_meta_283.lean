import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_283 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → (PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 2 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst C
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · refine ⟨{3, 8}, by decide, ?_⟩
    intro j g hj hop
    by_cases h : j < 9
    · interval_cases j <;> simp at hj <;> subst hj <;> simp_all
    · rw [List.getElem?_eq_none (by change 9 ≤ j; omega)] at hj
      simp at hj
  · intro x
    let edges : List (Fin 6 × Fin 6) :=
      [(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4)]
    have edges_spec :
        edges.any (fun p => x p.1 && x p.2) = true ↔
          ∃ u v : Fin 6, (u.val, v.val) ∈ edges.map (fun p => (p.1.val, p.2.val)) ∧
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
    change _ ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ edges.map (fun p => (p.1.val, p.2.val)) ∧
      x u = true ∧ x v = true
    rw [← edges_spec]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl_cons, List.foldl_nil, List.ofFn_succ, List.ofFn_zero,
      List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id, Bool.and_true, Bool.or_false, edges,
      Bool.and_eq_true, Bool.or_eq_true]
    grind
