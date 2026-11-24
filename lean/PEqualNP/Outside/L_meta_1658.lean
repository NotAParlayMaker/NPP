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
  intro n gates S k0 Bd Kc hg _ _ _ hk0 hcl hBd
  classical
  have hsub : Bd ⊆ Kc.biUnion (fun k => ((gates[k]?).elim [] (fun g => g.inputs)).toFinset) := by
    intro bw hbw
    obtain ⟨bk, bg, hin, hget, _, hmem, _⟩ := hBd bw hbw
    have hbk : bk ∈ (↑Kc : Set ℕ) := by
      apply hin (↑Kc : Set ℕ) (Finset.mem_coe.2 hk0)
      intro k1 hk1 g1 k2 h1 h2 h3 h4
      exact Finset.mem_coe.2 (hcl k1 (Finset.mem_coe.1 hk1) g1 k2 h1 h2 h3 h4)
    rw [Finset.mem_biUnion]
    refine ⟨bk, Finset.mem_coe.1 hbk, ?_⟩
    rw [hget]
    simpa using hmem
  have hk : ∀ k ∈ Kc, (((gates[k]?).elim [] (fun g => g.inputs)).toFinset).card ≤ 2 := by
    intro k _
    cases h : gates[k]? with
    | none => simp
    | some g =>
      have h2 := (hg g (List.mem_of_getElem? h)).2
      exact le_trans (List.toFinset_card_le _) h2
  calc Bd.card ≤ (Kc.biUnion (fun k => ((gates[k]?).elim [] (fun g => g.inputs)).toFinset)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Kc, (((gates[k]?).elim [] (fun g => g.inputs)).toFinset).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Kc, 2 := Finset.sum_le_sum hk
    _ = 2 * Kc.card := by simp [mul_comm]
