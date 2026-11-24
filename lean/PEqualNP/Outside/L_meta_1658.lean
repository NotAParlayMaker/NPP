import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1658

open PEqualNP.CircuitLowerBounds

-- The wires read by gate k, as a finite set (empty past the end of the list).
def ins (gates : List Gate) (k : ℕ) : Finset ℕ :=
  match gates[k]? with
  | some g => g.inputs.toFinset
  | none => ∅

theorem ins_card (gates : List Gate) (hg : ∀ g ∈ gates, g.inputs.length ≤ 2) (k : ℕ) :
    (ins gates k).card ≤ 2 := by
  unfold ins
  split
  · rename_i g hk
    exact (List.toFinset_card_le _).trans (hg g (List.mem_of_getElem? hk))
  · simp

theorem mem_ins (gates : List Gate) (k : ℕ) (g : Gate) (hk : gates[k]? = some g) (w : ℕ)
    (hw : w ∈ g.inputs) : w ∈ ins gates k := by
  unfold ins
  rw [hk]
  exact List.mem_toFinset.mpr hw

end PEqualNP.Outside.L_meta_1658

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
  intro n gates S k0 Bd Kc hgates _ _ _ hk0 hclosed hBd
  have hsub : Bd ⊆ Kc.biUnion (PEqualNP.Outside.L_meta_1658.ins gates) := by
    intro bw hbw
    obtain ⟨bk, bg, hcore, hbg, _, hbw_in, _⟩ := hBd bw hbw
    have hbk : bk ∈ Kc := by
      have := hcore (↑Kc : Set ℕ) (Finset.mem_coe.mpr hk0) (by
        intro k1 hk1 g1 k2 h1 h2 h3 h4
        exact Finset.mem_coe.mpr (hclosed k1 (Finset.mem_coe.mp hk1) g1 k2 h1 h2 h3 h4))
      exact Finset.mem_coe.mp this
    rw [Finset.mem_biUnion]
    exact ⟨bk, hbk, PEqualNP.Outside.L_meta_1658.mem_ins gates bk bg hbg bw hbw_in⟩
  calc Bd.card ≤ (Kc.biUnion (PEqualNP.Outside.L_meta_1658.ins gates)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Kc, (PEqualNP.Outside.L_meta_1658.ins gates k).card := Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Kc, 2 := Finset.sum_le_sum (fun k _ =>
        PEqualNP.Outside.L_meta_1658.ins_card gates (fun g hg => (hgates g hg).2) k)
    _ = 2 * Kc.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
