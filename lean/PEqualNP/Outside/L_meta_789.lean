import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_789 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 8]⟩], output := 9 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 5 ∧ (∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst C
  refine ⟨?_, rfl, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · intro x
    let edges : List (Fin 5 × Fin 5) := [(0, 1), (1, 2), (2, 3), (3, 4)]
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
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := rfl
    rw [hx]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl_cons, List.foldl_nil,
      List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id, Bool.and_true, Bool.or_false, edges,
      Bool.and_eq_true, Bool.or_eq_true]
    grind
