import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The two signals are gates: an input wire is false at the edge of vertices 0 and 7 or at the
-- edge of vertices 1 and 9. Each gate is an AND or an OR, and the statement is the same with
-- the two signals exchanged. So three cases remain: both OR, both AND, one of each.
theorem PEqualNP.Outside.R_meta_2708_352
    (bothOr : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∧ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∨ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), ¬x8 x12 ∧ x9 x2 x12 = Bool.false ∧ x9 x3 x12 = Bool.true) → (∃ (x13 : Fin (14 : ℕ) → Bool), ¬x8 x13 ∧ x9 x3 x13 = Bool.false ∧ x9 x2 x13 = Bool.true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x2 - 14)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x3 - 14)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 14 ≤ x2 ∧ 14 ≤ x3) → (26 : ℕ) ≤ x1.size)
    (bothAnd : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∧ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∨ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), ¬x8 x12 ∧ x9 x2 x12 = Bool.false ∧ x9 x3 x12 = Bool.true) → (∃ (x13 : Fin (14 : ℕ) → Bool), ¬x8 x13 ∧ x9 x3 x13 = Bool.false ∧ x9 x2 x13 = Bool.true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x2 - 14)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x3 - 14)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ 14 ≤ x2 ∧ 14 ≤ x3) → (26 : ℕ) ≤ x1.size)
    (andOr : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∧ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∨ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), ¬x8 x12 ∧ x9 x2 x12 = Bool.false ∧ x9 x3 x12 = Bool.true) → (∃ (x13 : Fin (14 : ℕ) → Bool), ¬x8 x13 ∧ x9 x3 x13 = Bool.false ∧ x9 x2 x13 = Bool.true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x2 - 14)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x3 - 14)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 14 ≤ x2 ∧ 14 ≤ x3) → (26 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∧ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∨ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), ¬x8 x12 ∧ x9 x2 x12 = Bool.false ∧ x9 x3 x12 = Bool.true) → (∃ (x13 : Fin (14 : ℕ) → Bool), ¬x8 x13 ∧ x9 x3 x13 = Bool.false ∧ x9 x2 x13 = Bool.true) → (26 : ℕ) ≤ x1.size := by
  intro C a b hmono ha hb
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
  have hinput : ∀ i : ℕ, i < 14 →
      (((List.ofFn (fun k : Fin 14 => decide (k = 0 ∨ k = 7))).getD i false && (List.ofFn (fun k : Fin 14 => decide (k = 1 ∨ k = 9))).getD i false) = false) := by decide
  have hta : ∃ (u v : Fin 14), ((u : ℕ), (v : ℕ)) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ (fun k : Fin 14 => decide (k = 0 ∨ k = 7)) u = true ∧ (fun k : Fin 14 => decide (k = 0 ∨ k = 7)) v = true :=
    ⟨0, 7, by decide, rfl, rfl⟩
  have htb : ∃ (u v : Fin 14), ((u : ℕ), (v : ℕ)) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ (fun k : Fin 14 => decide (k = 1 ∨ k = 9)) u = true ∧ (fun k : Fin 14 => decide (k = 1 ∨ k = 9)) v = true :=
    ⟨1, 9, by decide, rfl, rfl⟩
  have hgate : ∀ c : ℕ,
      (C.wires (List.ofFn (fun k : Fin 14 => decide (k = 0 ∨ k = 7)))).getD c false = true →
      (C.wires (List.ofFn (fun k : Fin 14 => decide (k = 1 ∨ k = 9)))).getD c false = true → 14 ≤ c := by
    intro c e0 e1
    by_contra hlt
    have hc14 : c < 14 := by omega
    rw [show C.wires _ = C.gates.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) _ from rfl, hpre _ _ c (by simp; omega)] at e0 e1
    have h := hinput c hc14
    rw [e0, e1] at h
    exact absurd h (by decide)
  have hga : 14 ≤ a := hgate a (P1 _ hta).1 (P1 _ htb).1
  have hgb : 14 ≤ b := hgate b (P1 _ hta).2 (P1 _ htb).2
  have hop : ∀ c : ℕ, 14 ≤ c → c < 14 + C.size →
      (NestedCover.gateAt C (c - 14)).op = GateOp.and ∨ (NestedCover.gateAt C (c - 14)).op = GateOp.or := by
    intro c h1 h2
    have hj : c - 14 < C.gates.length := by
      have : C.size = C.gates.length := rfl
      omega
    have hmem : NestedCover.gateAt C (c - 14) ∈ C.gates := by
      show C.gates.getD (c - 14) _ ∈ C.gates
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    exact (hmono _ hmem).1
  rcases hop a hga ha with hA | hA <;> rcases hop b hgb hb with hB | hB
  · exact bothAnd C a b hmono ha hb P1 P2 P3 P4 ⟨hA, hB, hga, hgb⟩
  · exact andOr C a b hmono ha hb P1 P2 P3 P4 ⟨hA, hB, hga, hgb⟩
  · exact andOr C b a hmono hb ha (fun x h => ⟨(P1 x h).2, (P1 x h).1⟩)
      (fun x h => (P2 x h).symm) P4 P3 ⟨hB, hA, hgb, hga⟩
  · exact bothOr C a b hmono ha hb P1 P2 P3 P4 ⟨hA, hB, hga, hgb⟩
