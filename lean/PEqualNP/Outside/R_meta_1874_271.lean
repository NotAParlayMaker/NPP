import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The two signals are gates: an input wire is false at the pair of point 0 and line 0 or at
-- the pair of point 1 and line 1. Each gate is an AND or an OR, and the statement is the same
-- with the two signals exchanged. So three cases remain: both OR, both AND, one of each.
theorem PEqualNP.Outside.R_meta_1874_271
    (bothOr : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10);           have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8);           have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ);           have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false;           (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∧ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∨ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Finset (Fin (13 : ℕ))), x11 x15 ∧ x12 x2 (x10 x15) = Bool.false ∧ x12 x3 (x10 x15) = Bool.true) → (∃ (x16 : Finset (Fin (13 : ℕ))), x11 x16 ∧ x12 x3 (x10 x16) = Bool.false ∧ x12 x2 (x10 x16) = Bool.true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x2 - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x3 - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 26 ≤ x2 ∧ 26 ≤ x3) → (63 : ℕ) ≤ x1.size)
    (bothAnd : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10);           have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8);           have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ);           have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false;           (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∧ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∨ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Finset (Fin (13 : ℕ))), x11 x15 ∧ x12 x2 (x10 x15) = Bool.false ∧ x12 x3 (x10 x15) = Bool.true) → (∃ (x16 : Finset (Fin (13 : ℕ))), x11 x16 ∧ x12 x3 (x10 x16) = Bool.false ∧ x12 x2 (x10 x16) = Bool.true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x2 - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x3 - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ 26 ≤ x2 ∧ 26 ≤ x3) → (63 : ℕ) ≤ x1.size)
    (andOr : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10);           have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8);           have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ);           have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false;           (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∧ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∨ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Finset (Fin (13 : ℕ))), x11 x15 ∧ x12 x2 (x10 x15) = Bool.false ∧ x12 x3 (x10 x15) = Bool.true) → (∃ (x16 : Finset (Fin (13 : ℕ))), x11 x16 ∧ x12 x3 (x10 x16) = Bool.false ∧ x12 x2 (x10 x16) = Bool.true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x2 - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x3 - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 26 ≤ x2 ∧ 26 ≤ x3) → (63 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10);           have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8);           have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ);           have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false;           (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∧ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∨ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Finset (Fin (13 : ℕ))), x11 x15 ∧ x12 x2 (x10 x15) = Bool.false ∧ x12 x3 (x10 x15) = Bool.true) → (∃ (x16 : Finset (Fin (13 : ℕ))), x11 x16 ∧ x12 x3 (x10 x16) = Bool.false ∧ x12 x2 (x10 x16) = Bool.true) → (63 : ℕ) ≤ x1.size := by
  intro C a b hmono hback ha hb
  dsimp only
  intro P1 P2 P3 P4
  have hpre : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      have h1 := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i
        (by rw [List.length_append]; omega)
      have h2 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false
          = w.getD i false := List.getD_append _ _ _ _ hi
      exact h1.trans h2
  have hinput : ∀ i : ℕ, i < 26 →
      ((((List.ofFn fun (k : Fin 13) => decide (k = 0)) ++ List.ofFn fun (k : Fin 13) => decide (k = 0)).getD i false
        && ((List.ofFn fun (k : Fin 13) => decide (k = 1)) ++ List.ofFn fun (k : Fin 13) => decide (k = 1)).getD i false)
        = false) := by decide
  have hgate : ∀ c : ℕ,
      (∀ (p l : Fin 13), p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
        (C.wires ((List.ofFn fun (k : Fin 13) => decide (k = p)) ++ List.ofFn fun (k : Fin 13) => decide (k = l))).getD c false = true) →
      26 ≤ c := by
    intro c hc
    by_contra hlt
    have hc26 : c < 26 := by omega
    have e0 := hc 0 0 (by decide)
    have e1 := hc 1 1 (by decide)
    rw [show C.wires _ = C.gates.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) _ from rfl, hpre _ _ c (by simp; omega)] at e0 e1
    have := hinput c hc26
    rw [e0, e1] at this
    exact absurd this (by decide)
  have hga : 26 ≤ a := hgate a (fun p l h => (P1 p l h).1)
  have hgb : 26 ≤ b := hgate b (fun p l h => (P1 p l h).2)
  have hop : ∀ c : ℕ, 26 ≤ c → c < 26 + C.size →
      (NestedCover.gateAt C (c - 26)).op = GateOp.and ∨ (NestedCover.gateAt C (c - 26)).op = GateOp.or := by
    intro c h1 h2
    have hj : c - 26 < C.gates.length := by
      have : C.size = C.gates.length := rfl
      omega
    have hmem : NestedCover.gateAt C (c - 26) ∈ C.gates := by
      show C.gates.getD (c - 26) _ ∈ C.gates
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    exact (hmono _ hmem).1
  rcases hop a hga ha with hA | hA <;> rcases hop b hgb hb with hB | hB
  · exact bothAnd C a b hmono hback ha hb P1 P2 P3 P4 ⟨hA, hB, hga, hgb⟩
  · exact andOr C a b hmono hback ha hb P1 P2 P3 P4 ⟨hA, hB, hga, hgb⟩
  · exact andOr C b a hmono hback hb ha (fun p l h => ⟨(P1 p l h).2, (P1 p l h).1⟩)
      (fun Q hQ => (P2 Q hQ).symm) P4 P3 ⟨hB, hA, hgb, hga⟩
  · exact bothOr C a b hmono hback ha hb P1 P2 P3 P4 ⟨hA, hB, hga, hgb⟩
