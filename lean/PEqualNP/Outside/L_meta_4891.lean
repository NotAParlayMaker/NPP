import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4891 : ∀ (x1 : Fin (63 : ℕ) → Bool) (x2 x3 : Fin (63 : ℕ) → Fin (89 : ℕ)), (∀ (x4 : Fin (63 : ℕ)), ↑(x2 x4) < (26 : ℕ) + ↑x4 ∧ ↑(x3 x4) < (26 : ℕ) + ↑x4 ∧ x2 x4 ≤ x3 x4) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size = (63 : ℕ) ∧ ∀ (x6 : Fin (26 : ℕ) → Bool), x5.eval (List.ofFn x6) = (fun (x7 : Fin (26 : ℕ) → Bool) => (List.foldl (fun (x8 : List Bool) (x9 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) => x8 ++ [bif x9.1 then x8.getD (↑x9.2.1) Bool.false && x8.getD (↑x9.2.2) Bool.false else x8.getD (↑x9.2.1) Bool.false || x8.getD (↑x9.2.2) Bool.false]) (List.ofFn x7) (List.ofFn fun (x8 : Fin (63 : ℕ)) => (x1 x8, x2 x8, x3 x8))).getD (88 : ℕ) Bool.false) x6 := by
  intro x1 x2 x3 _
  refine ⟨⟨(List.ofFn fun (k : Fin 63) => (x1 k, x2 k, x3 k)).map
      (fun t => ⟨if t.1 = true then PEqualNP.CircuitLowerBounds.GateOp.and
        else PEqualNP.CircuitLowerBounds.GateOp.or, [(t.2.1 : ℕ), (t.2.2 : ℕ)]⟩), 88⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨t, _, rfl⟩ := hg
    rcases t with ⟨b, i, j⟩
    cases b <;> simp
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x6
    have hstep : (fun (w : List Bool) (t : Bool × Fin 89 × Fin 89) =>
        w ++ [(if t.1 = true then PEqualNP.CircuitLowerBounds.GateOp.and
          else PEqualNP.CircuitLowerBounds.GateOp.or).eval
            (([(t.2.1 : ℕ), (t.2.2 : ℕ)] : List ℕ).map fun i => w.getD i false)]) =
        (fun (x8 : List Bool) (x9 : Bool × Fin 89 × Fin 89) =>
          x8 ++ [bif x9.1 then x8.getD (↑x9.2.1) Bool.false && x8.getD (↑x9.2.2) Bool.false
            else x8.getD (↑x9.2.1) Bool.false || x8.getD (↑x9.2.2) Bool.false]) := by
      funext w t
      rcases t with ⟨b, i, j⟩
      cases b <;> simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl_map]
    rw [hstep]
