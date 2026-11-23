import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_944

open PEqualNP.CircuitLowerBounds

private def edges : List (Fin 8 × Fin 8) := [(0, 1), (0, 2), (1, 2), (3, 4), (3, 7), (4, 7), (5, 6), (5, 7), (6, 7)]

private theorem edge_iff (x : Fin 8 → Bool) :
    edges.any (fun e => x e.1 && x e.2) = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ edges.map (fun e => (e.1.val, e.2.val)) ∧
        x u = true ∧ x v = true := by
  simp only [List.any_eq_true, Bool.and_eq_true, List.mem_map, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, hm, ha, hb⟩
    exact ⟨a, b, ⟨a, b, hm, rfl, rfl⟩, ha, hb⟩
  · rintro ⟨u, v, ⟨a, b, hm, hu, hv⟩, ha, hb⟩
    rw [← Fin.ext hu] at ha
    rw [← Fin.ext hv] at hb
    exact ⟨a, b, hm, ha, hb⟩

private theorem value_eq (x : Fin 8 → Bool) :
    (({ gates := [⟨.or, [2, 1]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [5, 13]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [7, 15]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [17, 12]⟩, ⟨.or, [18, 14]⟩, ⟨.or, [19, 16]⟩], output := 20 }) : Circuit).eval (List.ofFn x) = edges.any (fun e => x e.1 && x e.2) := by
  simp [Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ, edges,
    List.getD_eq_getElem?_getD] <;>
    (apply Bool.eq_iff_iff.mpr; simp only [Bool.and_eq_true, Bool.or_eq_true]; tauto)

end PEqualNP.Outside.L_meta_944

theorem PEqualNP.Outside.L_meta_944 : (∀ C1 : PEqualNP.CircuitLowerBounds.Circuit, C1 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 16]⟩], output := 20 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C1 ∧ C1.size = 13 ∧ (∀ x1 : Fin 8 → Bool, (C1.eval (List.ofFn x1) = true ↔ ∃ u1 v1 : Fin 8, (u1.val, v1.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 7), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x1 u1 = true ∧ x1 v1 = true))) := by
  intro C hC
  subst C
  refine ⟨?_, rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    exact (congrArg (· = true) (PEqualNP.Outside.L_meta_944.value_eq x)).to_iff.trans (PEqualNP.Outside.L_meta_944.edge_iff x)
