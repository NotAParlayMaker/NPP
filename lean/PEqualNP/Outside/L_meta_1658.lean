import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1658 :
  ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (S : Finset (Fin n)) (k0 : ℕ) (Bd : Finset ℕ) (Kc : Finset ℕ),
  (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
  (∀ k : ℕ, ∀ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g → ∀ i ∈ g.inputs, i < n + k) →
  k0 < gates.length →
  (∀ u : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun uk : Fin n => decide (uk = u)))).getD (n + k0) false = true ↔ u ∈ S) →
  k0 ∈ Kc →
  (∀ k1 ∈ Kc, ∀ (g1 : PEqualNP.CircuitLowerBounds.Gate) (k2 : ℕ), gates[k1]? = some g1 → n + k2 ∈ g1.inputs → k2 < k1 →
    (∀ u1 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u1k : Fin n => decide (u1k = u1)))).getD (n + k2) false = true → u1 ∈ S) → k2 ∈ Kc) →
  (∀ bw ∈ Bd, ∃ (bk : ℕ) (bg : PEqualNP.CircuitLowerBounds.Gate),
    (∀ bK : Set ℕ, k0 ∈ bK →
      (∀ k1 ∈ bK, ∀ (g1 : PEqualNP.CircuitLowerBounds.Gate) (k2 : ℕ), gates[k1]? = some g1 → n + k2 ∈ g1.inputs → k2 < k1 →
        (∀ u1 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u1k : Fin n => decide (u1k = u1)))).getD (n + k2) false = true → u1 ∈ S) → k2 ∈ bK) → bk ∈ bK) ∧
    gates[bk]? = some bg ∧ bg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ bw ∈ bg.inputs ∧
    ¬ (∀ u2 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u2k : Fin n => decide (u2k = u2)))).getD bw false = true → u2 ∈ S)) →
  Bd.card ≤ 2 * Kc.card := by
  classical
  intro n gates S k0 Bd Kc fanin _ _ _ root closed boundary
  let inputs (k : ℕ) : Finset ℕ := ((gates[k]?).map (fun g => g.inputs.toFinset)).getD ∅
  have cover : Bd ⊆ Kc.biUnion inputs := by
    intro w hw
    obtain ⟨k,g,core,look,_,read,_⟩ := boundary w hw
    exact Finset.mem_biUnion.mpr ⟨k,core (Kc : Set ℕ) root closed,by simpa [inputs,look] using read⟩
  have cost (k : ℕ) : (inputs k).card≤2 := by
    cases look : gates[k]? with
    | none => simp [inputs,look]
    | some g =>
      have mem : g ∈ gates := List.mem_of_getElem? look
      simpa [inputs,look] using g.inputs.toFinset_card_le.trans (fanin g mem).2
  calc
    Bd.card ≤ (Kc.biUnion inputs).card := Finset.card_le_card cover
    _ ≤ ∑ k∈Kc, (inputs k).card := Finset.card_biUnion_le
    _ ≤ ∑ _k∈Kc, 2 := Finset.sum_le_sum (fun k _ => cost k)
    _ = 2*Kc.card := by simp [Nat.mul_comm]
