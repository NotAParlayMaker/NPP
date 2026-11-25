import Mathlib
import PEqualNP.Defs

-- Split on the AND gates. In the first case every AND gate either has its first operand below
-- its second on single inputs or is true on at most one single input, and every AND gate whose
-- operands cross an incident pair it separates is below the output on every input with at most
-- two true bits. Then the walk to such a gate and the star count bound the incident pairs by the
-- gates. The second case is the step with that condition false, stated through the same wire
-- values: positive and negative inputs as sets, the counted pairs as an intersection of lists.
theorem PEqualNP.Outside.R_meta_4346_812
    (h1 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (have v := fun (w : ℕ) (S : Finset (Fin (x2 + x2))) => (x5.wires (List.ofFn fun i => decide (i ∈ S))).getD w false; ∀ (j a b : ℕ), x5.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ → have t := v (x2 + x2 + j); ((∀ (w : Fin (x2 + x2)), v a {w} ≤ v b {w}) ∨ ∀ (u w : Fin (x2 + x2)), t {u} = true → t {w} = true → u = w) ∧ ∀ (p l : Fin x2) (u w : Fin (x2 + x2)), x3 p l → (!t {Fin.castAdd x2 p} && !t {Fin.natAdd x2 l} && (v a {Fin.castAdd x2 p} && v b {Fin.natAdd x2 l} || v a {Fin.natAdd x2 l} && v b {Fin.castAdd x2 p}) && t {u, w}) ≤ v x5.output {u, w}) → (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x12 x13 : Fin x2), x3 x12 x13 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12 ∨ x15 = Fin.natAdd x2 x13)) = Bool.true) → (∀ (x13 : Fin (x2 + x2) → Bool), Fintype.card { x14 : Fin x2 // x13 (Fin.natAdd x2 x14) = Bool.true } ≤ x1 → (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size)
    (h2 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), have v := fun (w : ℕ) (S : Finset (Fin (x2 + x2))) => (x5.wires (List.ofFn fun i => decide (i ∈ S))).getD w false; ¬(∀ (j a b : ℕ), (⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ : PEqualNP.CircuitLowerBounds.Gate) ∈ x5.gates[j]? → ((∀ (w : Fin (x2 + x2)), v a {w} ≤ v b {w}) ∨ ∀ (u w : Fin (x2 + x2)), v (x2 + x2 + j) {u} = true → v (x2 + x2 + j) {w} = true → u = w) ∧ ∀ (p l : Fin x2) (u w : Fin (x2 + x2)), x3 p l → (!v (x2 + x2 + j) {Fin.castAdd x2 p} && !v (x2 + x2 + j) {Fin.natAdd x2 l} && (v a {Fin.castAdd x2 p} && v b {Fin.natAdd x2 l} || v a {Fin.natAdd x2 l} && v b {Fin.castAdd x2 p}) && v (x2 + x2 + j) {u, w}) ≤ v x5.output {u, w}) → (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (p l : Fin x2), x3 p l → v x5.output {Fin.castAdd x2 p, Fin.natAdd x2 l} = true) → (∀ (S : Finset (Fin (x2 + x2))), Fintype.card { l : Fin x2 // Fin.natAdd x2 l ∈ S } ≤ x1 → (∀ (p l : Fin x2), x3 p l → Fin.castAdd x2 p ∈ S → Fin.natAdd x2 l ∉ S) → v x5.output S = false) → (2 : ℕ) * Fintype.card { c : Fin x2 × Fin x2 // x3 c.1 c.2 ∧ (PEqualNP.ReadK.readVectors x5 (x2 + x2) [↑c.1, x2 + ↑c.2] 2).getD x5.output [] ∩ [[2, 2], [1, 1], [2, 1]] ≠ [] } < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : ℕ :=     Fintype.card       { x6 : Fin x2 × Fin x2 //         have x7 : List (List ℕ) := (PEqualNP.ReadK.readVectors x5 (x2 + x2) [↑x6.1, x2 + ↑x6.2] (2 : ℕ)).getD x5.output [];         x3 x6.1 x6.2 ∧ ([(2 : ℕ), (2 : ℕ)] ∈ x7 ∨ [(1 : ℕ), (1 : ℕ)] ∈ x7 ∨ [(2 : ℕ), (1 : ℕ)] ∈ x7) };   (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x12 x13 : Fin x2), x3 x12 x13 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12 ∨ x15 = Fin.natAdd x2 x13)) = Bool.true) → (∀ (x13 : Fin (x2 + x2) → Bool), Fintype.card { x14 : Fin x2 // x13 (Fin.natAdd x2 x14) = Bool.true } ≤ x1 → (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.false) → (2 : ℕ) * x6 < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro x1 x2 x3 x4 x5
  dsimp only
  intro hq hN hdeg huniq hAO hpos hneg hfew
  by_cases hc : (have v := fun (w : ℕ) (S : Finset (Fin (x2 + x2))) => (x5.wires (List.ofFn fun i => decide (i ∈ S))).getD w false; ∀ (j a b : ℕ), x5.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ → have t := v (x2 + x2 + j); ((∀ (w : Fin (x2 + x2)), v a {w} ≤ v b {w}) ∨ ∀ (u w : Fin (x2 + x2)), t {u} = true → t {w} = true → u = w) ∧ ∀ (p l : Fin x2) (u w : Fin (x2 + x2)), x3 p l → (!t {Fin.castAdd x2 p} && !t {Fin.natAdd x2 l} && (v a {Fin.castAdd x2 p} && v b {Fin.natAdd x2 l} || v a {Fin.natAdd x2 l} && v b {Fin.castAdd x2 p}) && t {u, w}) ≤ v x5.output {u, w})
  · exact h1 x1 x2 x3 x5 hc hq hN hdeg huniq hAO hpos hneg
  · refine h2 x1 x2 x3 x5 hc hq hN hdeg huniq hAO ?_ ?_ (lt_of_eq_of_lt ?_ hfew)
    · intro p l hpl
      have e : (fun i : Fin (x2 + x2) => decide (i ∈ ({Fin.castAdd x2 p, Fin.natAdd x2 l} : Finset (Fin (x2 + x2))))) =
          fun i => decide (i = Fin.castAdd x2 p ∨ i = Fin.natAdd x2 l) := by
        funext i
        simp
      show (x5.wires (List.ofFn fun i => decide (i ∈ ({Fin.castAdd x2 p, Fin.natAdd x2 l} : Finset (Fin (x2 + x2)))))).getD x5.output false = true
      rw [e]
      exact hpos p l hpl
    · intro S hS hno
      exact hneg (fun i => decide (i ∈ S)) (by simpa using hS) (by simpa using fun p l hpl hp hl => hno p l hpl hp hl)
    · have key : ∀ L : List (List ℕ), L ∩ [[2, 2], [1, 1], [2, 1]] ≠ [] ↔ ([2, 2] ∈ L ∨ [1, 1] ∈ L ∨ [2, 1] ∈ L) := by
        intro L
        constructor
        · intro h
          obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ h
          rcases List.mem_inter_iff.1 hy with ⟨hyL, hyM⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hyM
          rcases hyM with rfl | rfl | rfl <;> simp [hyL]
        · intro h hnil
          have hno : ∀ y, y ∈ L → y ∈ [[2, 2], [1, 1], [2, 1]] → False := fun y hL hM => by
            have hm := List.mem_inter_iff.2 ⟨hL, hM⟩
            rw [hnil] at hm
            simp at hm
          rcases h with hy | hy | hy <;> exact hno _ hy (by simp)
      congr 1
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun c => and_congr_right fun _ => key _)
