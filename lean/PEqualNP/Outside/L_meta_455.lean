import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_455

theorem nbhd_v (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a))
    (v : Fin n) :
    ∀ a ∈ Finset.univ.filter (fun w => G.Adj v w),
      ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w), ¬ G.Adj a b := by
  intro a ha b hb hab
  rw [Finset.mem_filter] at ha hb
  exact htri v a b ⟨ha.2, hab, hb.2.symm⟩

theorem nbhd_u (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a))
    (u : Fin n) :
    ∀ a ∈ Finset.univ.filter (fun w => G.Adj u w),
      ∀ b ∈ Finset.univ.filter (fun w => G.Adj u w), ¬ G.Adj a b := by
  intro a ha b hb hab
  rw [Finset.mem_filter] at ha hb
  exact htri u a b ⟨ha.2, hab, hb.2.symm⟩

theorem cross (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a))
    (hcycle : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (u v : Fin n) (huv : G.Adj u v) :
    ∀ a ∈ (Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u)) ∪
            (Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v)),
      ∀ b ∈ (Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u)) ∪
             (Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v)),
        ¬ G.Adj a b := by
  intro a ha b hb hab
  have ha' : (G.Adj v a ∧ a ≠ u) ∨ (G.Adj u a ∧ a ≠ v) := by
    rcases Finset.mem_union.mp ha with h | h
    · rw [Finset.mem_filter] at h
      exact Or.inl h.2
    · rw [Finset.mem_filter] at h
      exact Or.inr h.2
  have hb' : (G.Adj v b ∧ b ≠ u) ∨ (G.Adj u b ∧ b ≠ v) := by
    rcases Finset.mem_union.mp hb with h | h
    · rw [Finset.mem_filter] at h
      exact Or.inl h.2
    · rw [Finset.mem_filter] at h
      exact Or.inr h.2
  rcases ha' with ⟨hva, haneu⟩ | ⟨hua, hanev⟩
  · rcases hb' with ⟨hvb, _⟩ | ⟨hub, hbnev⟩
    · exact htri v a b ⟨hva, hab, hvb.symm⟩
    · exact hcycle v a b u (Ne.symm hbnev) haneu ⟨hva, hab, hub.symm, huv⟩
  · rcases hb' with ⟨hvb, hbneu⟩ | ⟨hub, _⟩
    · exact hcycle u a b v (Ne.symm hbneu) hanev ⟨hua, hab, hvb.symm, huv.symm⟩
    · exact htri u a b ⟨hua, hab, hub.symm⟩

end PEqualNP.Outside.L_meta_455

theorem PEqualNP.Outside.L_meta_455 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)) →
    (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
    ∀ u v : Fin n, G.Adj u v →
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj v w),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w), ¬ G.Adj a b) ∧
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj u w),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj u w), ¬ G.Adj a b) ∧
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
              Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
              Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v), ¬ G.Adj a b) := by
  intro n G _ htri hcycle u v huv
  exact ⟨PEqualNP.Outside.L_meta_455.nbhd_v n G htri v,
    PEqualNP.Outside.L_meta_455.nbhd_u n G htri u,
    PEqualNP.Outside.L_meta_455.cross n G htri hcycle u v huv⟩
