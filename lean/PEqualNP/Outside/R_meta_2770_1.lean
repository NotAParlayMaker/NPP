import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2770_1
    (hCountBinary : ∀ C : Circuit, FanInTwo C → circuitFun 9 C = (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) →
      13 ≤ C.gates.countP (fun g => g.op.eval [true] && decide (2 ≤ g.inputs.length ∧ g.inputs.Nodup)))
    (hResidual : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (x1.gates.length = (15 : ℕ) ∧       x1.output = (23 : ℕ) ∧         x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧           ∀ (x2 : ℕ) (x3 : x2 < x1.gates.length),             have x4 : PEqualNP.CircuitLowerBounds.Gate := x1.gates[x2];             have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 < (9 : ℕ) + x2 ∨ x5 = (24 : ℕ);             have x6 : ℕ → ℕ := fun (x6 : ℕ) => if x6 < (9 : ℕ) then x6 else if x6 = (24 : ℕ) then (9 : ℕ) else x6 + (1 : ℕ);             (∃ (x7 : ℕ), x5 x7 ∧ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x7] : PEqualNP.CircuitLowerBounds.Gate }) ∨ ∃ (x7 : ℕ) (x8 : ℕ), x5 x7 ∧ x5 x8 ∧ x6 x7 < x6 x8 ∧ (x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate } ∨ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate })) →     List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op.eval [Bool.false]) x1.gates = (2 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (x1.gates.length = (15 : ℕ) ∧       x1.output = (23 : ℕ) ∧         x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧           ∀ (x2 : ℕ) (x3 : x2 < x1.gates.length),             have x4 : PEqualNP.CircuitLowerBounds.Gate := x1.gates[x2];             have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 < (9 : ℕ) + x2 ∨ x5 = (24 : ℕ);             have x6 : ℕ → ℕ := fun (x6 : ℕ) => if x6 < (9 : ℕ) then x6 else if x6 = (24 : ℕ) then (9 : ℕ) else x6 + (1 : ℕ);             x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } ∨ (∃ (x7 : ℕ), x5 x7 ∧ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x7] : PEqualNP.CircuitLowerBounds.Gate }) ∨ ∃ (x7 : ℕ) (x8 : ℕ), x5 x7 ∧ x5 x8 ∧ x6 x7 ≤ x6 x8 ∧ (x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate } ∨ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate })) →     (2 : ℕ) ≤ List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op.eval [Bool.false]) x1.gates → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) := by
  intro C hShape hTwo hfun
  obtain ⟨hLen, hOut, hFirst, hGates⟩ := hShape
  have hfan : FanInTwo C := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have h := hGates j hj
    dsimp only at h
    rcases h with ho | ⟨a, _, ho⟩ | ⟨a, b, _, _, _, ho | ho⟩ <;>
      rw [ho] <;> simp
  let binary (g : Gate) := g.op.eval [true] && decide (2 ≤ g.inputs.length ∧ g.inputs.Nodup)
  let unary (g : Gate) := g.op.eval [false]
  have handFalse : GateOp.and.eval [false] = false := rfl
  have horFalse : GateOp.or.eval [false] = false := rfl
  have hnotTrue : GateOp.not.eval [true] = false := rfl
  have hDisj : ∀ g ∈ C.gates, ¬(binary g = true ∧ unary g = true) := by
    intro g hg
    have h := (hfan g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h
    · simp only [unary, h, handFalse, Bool.false_eq_true, and_false, not_false_eq_true]
    · simp only [unary, h, horFalse, Bool.false_eq_true, and_false, not_false_eq_true]
    · simp only [binary, h, hnotTrue, Bool.false_and, Bool.false_eq_true, false_and, not_false_eq_true]
  have hCount (gs : List Gate) (h : ∀ g ∈ gs, ¬(binary g = true ∧ unary g = true)) :
      gs.countP binary + gs.countP unary = gs.countP (fun g => binary g || unary g) := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      have hTail := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
      have hHead := h g List.mem_cons_self
      cases hb : binary g <;> cases hu : unary g
      · simpa [List.countP_cons, hb, hu] using hTail
      · simp [hb, hu]
        omega
      · simp [hb, hu]
        omega
      · exact False.elim (hHead ⟨hb, hu⟩)
  have hBinary := hCountBinary C hfan hfun
  change 13 ≤ C.gates.countP binary at hBinary
  change 2 ≤ C.gates.countP unary at hTwo
  have hsum := hCount C.gates hDisj
  have hle := List.countP_le_length (p := fun g => binary g || unary g) (l := C.gates)
  have hU : C.gates.countP unary = 2 := by omega
  have hall : ∀ g ∈ C.gates, (binary g || unary g) = true :=
    List.countP_eq_length.mp (by omega)
  apply hResidual C ?_ hU hfun
  refine ⟨hLen, hOut, hFirst, ?_⟩
  intro j hj
  have h := hGates j hj
  dsimp only at h ⊢
  have htag := hall C.gates[j] (List.getElem_mem hj)
  rcases h with hConst | ⟨a, ha, hNot⟩ | ⟨a, b, ha, hb, hs, hop⟩
  · rw [hConst] at htag
    change false = true at htag
    contradiction
  · exact Or.inl ⟨a, ha, hNot⟩
  · apply Or.inr
    refine ⟨a, b, ha, hb, ?_, hop⟩
    have hBinaryGate : binary C.gates[j] = true := by
      rcases hop with ho | ho
      · simpa only [unary, ho, handFalse, Bool.or_false] using htag
      · simpa only [unary, ho, horFalse, Bool.or_false] using htag
    have hn := (of_decide_eq_true (Bool.and_eq_true_iff.mp hBinaryGate).2).2
    have hab : a ≠ b := by
      have hnd : ([a, b] : List ℕ).Nodup := by
        rcases hop with ho | ho <;> simpa only [ho] using hn
      simpa using hnd
    apply lt_of_le_of_ne hs
    intro hr
    split_ifs at hr <;> omega
