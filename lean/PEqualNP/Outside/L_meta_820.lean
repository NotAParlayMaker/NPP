import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_820

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C0 : Circuit :=
  { gates := [⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [8, 2]⟩, ⟨GateOp.and, [1, 9]⟩,
      ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [10, 12]⟩,
      ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [14, 4]⟩, ⟨GateOp.and, [3, 15]⟩,
      ⟨GateOp.or, [13, 16]⟩], output := 17 }

def E : List (ℕ × ℕ) := [(0, 1), (0, 5), (1, 2), (1, 7), (2, 3), (3, 4), (3, 6), (4, 5)]

def F (a0 a1 a2 a3 a4 a5 a6 a7 : Bool) : Bool :=
  (a0 && a1) || ((a0 && a5) || ((a1 && a2) || ((a1 && a7) ||
    ((a2 && a3) || ((a3 && a4) || ((a3 && a6) || (a4 && a5)))))))

lemma table : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool,
    C0.eval [a0, a1, a2, a3, a4, a5, a6, a7] = F a0 a1 a2 a3 a4 a5 a6 a7 := by
  decide

lemma rhs (x : Fin 8 → Bool) :
    (∃ u v : Fin 8, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true) ↔
      F (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) = true := by
  constructor
  · rintro ⟨u, v, hm, hu, hv⟩
    fin_cases u <;> fin_cases v <;> simp_all [E, F]
  · intro h
    simp only [F, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨0, 1, by simp [E], h1, h2⟩
    · exact ⟨0, 5, by simp [E], h1, h2⟩
    · exact ⟨1, 2, by simp [E], h1, h2⟩
    · exact ⟨1, 7, by simp [E], h1, h2⟩
    · exact ⟨2, 3, by simp [E], h1, h2⟩
    · exact ⟨3, 4, by simp [E], h1, h2⟩
    · exact ⟨3, 6, by simp [E], h1, h2⟩
    · exact ⟨4, 5, by simp [E], h1, h2⟩

lemma fan : FanInTwo C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_820

theorem PEqualNP.Outside.L_meta_820 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 16]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 5), (1, 2), (1, 7), (2, 3), (3, 4), (3, 6), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  refine ⟨PEqualNP.Outside.L_meta_820.fan, rfl, fun x => ?_⟩
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    simp [List.ofFn_succ]
  have h := PEqualNP.Outside.L_meta_820.table (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  have h2 := PEqualNP.Outside.L_meta_820.rhs x
  rw [hl]
  exact h.symm ▸ h2.symm
