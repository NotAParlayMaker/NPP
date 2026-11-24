import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_1692_1

open PEqualNP.CircuitLowerBounds

/-- Cut for `L-meta-1692`: child 1 rules out an AND gate that reads an AND gate,
child 2 assumes one; a case split on that question gives the recorded statement. -/
theorem PEqualNP.Outside.R_meta_1692_1 :
    (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 26 + (i : ℕ)) → (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l))) = true) → (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) → (∀ (i : Fin gates.length) (w : ℕ), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → w ∈ (gates.get i).inputs → ∀ j : Fin gates.length, w = 26 + (j : ℕ) → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) → 64 ≤ gates.length) →
    (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 26 + (i : ℕ)) → (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l))) = true) → (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) → (∃ (i : Fin gates.length) (w : ℕ), w ∈ (gates.get i).inputs ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ j : Fin gates.length, w = 26 + (j : ℕ) ∧ (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and) → 64 ≤ gates.length) →
    (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 26 + (i : ℕ)) → (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l))) = true) → (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) → 64 ≤ gates.length) := by
  classical
  intro h1 h2 gates out hop hbound hin hquad
  by_cases h : (∃ (i : Fin gates.length) (w : ℕ), w ∈ (gates.get i).inputs ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ j : Fin gates.length, w = 26 + (j : ℕ) ∧ (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and)
  · exact h2 gates out hop hbound hin hquad h
  · refine h1 gates out hop hbound hin hquad ?_
    intro i w hopi hw j heq
    rcases (hop (gates.get j) (List.get_mem gates j)).1 with hja | hjo
    · exact absurd ⟨i, w, hw, hopi, j, heq, hja⟩ h
    · exact hjo

end PEqualNP.Outside.R_meta_1692_1
