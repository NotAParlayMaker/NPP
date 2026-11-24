import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1658 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (S : Finset (Fin n)) (k0 : ℕ) (Bd : Finset ℕ) (Kc : Finset ℕ),
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
  intro n gates S k0 Bd Kc hnorm _ _ _ hk0 hclose hboundary
  let inputsAt (k : ℕ) : Finset ℕ :=
    ((gates[k]?).map (fun g => g.inputs.toFinset)).getD ∅
  have hinputsAt (k : ℕ) : (inputsAt k).card ≤ 2 := by
    cases hk : gates[k]? with
    | none => simp [inputsAt, hk]
    | some g =>
      simp only [inputsAt, hk, Option.map_some, Option.getD_some]
      exact (List.toFinset_card_le g.inputs).trans (hnorm g (List.mem_of_getElem? hk)).2
  have hcover : Bd ⊆ Kc.biUnion inputsAt := by
    intro bw hbw
    obtain ⟨bk, bg, hbk, hget, _, hbwin, _⟩ := hboundary bw hbw
    have hbkK : bk ∈ Kc := hbk (↑Kc) hk0 (by
      intro k1 hk1 g1 k2 hg1 hinput hlt hsubset
      exact hclose k1 hk1 g1 k2 hg1 hinput hlt hsubset)
    exact Finset.mem_biUnion.mpr ⟨bk, hbkK, by simp [inputsAt, hget, hbwin]⟩
  calc
    Bd.card ≤ (Kc.biUnion inputsAt).card := Finset.card_le_card hcover
    _ ≤ Kc.card * 2 := Finset.card_biUnion_le_card_mul Kc inputsAt 2 (fun k _ => hinputsAt k)
    _ = 2 * Kc.card := Nat.mul_comm _ _
