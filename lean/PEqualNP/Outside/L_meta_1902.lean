import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1902

open PEqualNP.BicliqueBlockCost

def sm {n : ℕ} (p : Block n) : Finset (Fin n) := if p.1.card ≤ 1 then p.1 else p.2

def bg {n : ℕ} (p : Block n) : Finset (Fin n) := if p.1.card ≤ 1 then p.2 else p.1

theorem sm_card {n : ℕ} (G : SimpleGraph (Fin n)) (p : Block n) (hp : IsBlock G p)
    (h : p.1.card ≤ 1 ∨ p.2.card ≤ 1) : (sm p).card = 1 := by
  have h1 := Finset.card_pos.mpr hp.2.1
  have h2 := Finset.card_pos.mpr hp.2.2.1
  unfold sm
  split_ifs with h0
  · omega
  · omega

theorem cost_eq {n : ℕ} (G : SimpleGraph (Fin n)) (p : Block n) (hp : IsBlock G p)
    (h : p.1.card ≤ 1 ∨ p.2.card ≤ 1) : blockCost p = (bg p).card := by
  have h1 := Finset.card_pos.mpr hp.2.1
  have h2 := Finset.card_pos.mpr hp.2.2.1
  unfold blockCost bg
  split_ifs with h0
  · omega
  · omega

theorem cov {n : ℕ} (p : Block n) (u v : Fin n) (h : BlockCovers p u v) :
    (u ∈ sm p ∧ v ∈ bg p) ∨ (v ∈ sm p ∧ u ∈ bg p) := by
  unfold BlockCovers at h
  unfold sm bg
  split_ifs with h0
  · tauto
  · tauto

theorem main {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Block n)) (hF : IsBlockCover G F)
    (hs : ∀ p ∈ F, p.1.card ≤ 1 ∨ p.2.card ≤ 1) :
    ∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧
      G.edgeSet.ncard + S.card ≤ familyCost F + 1 := by
  classical
  refine ⟨F.biUnion sm, ?_, ?_⟩
  · intro u v huv
    obtain ⟨p, hp, hc⟩ := hF.2 u v huv
    rcases cov p u v hc with h | h
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨p, hp, h.1⟩)
    · exact Or.inr (Finset.mem_biUnion.mpr ⟨p, hp, h.1⟩)
  · have h1 : (F.biUnion sm).card ≤ F.card := by
      calc (F.biUnion sm).card ≤ ∑ p ∈ F, (sm p).card := Finset.card_biUnion_le
        _ = ∑ p ∈ F, 1 :=
            Finset.sum_congr rfl (fun p hp => sm_card G p (hF.1 p hp) (hs p hp))
        _ = F.card := by simp
    have hsub : G.edgeSet ⊆
        ↑(F.biUnion (fun p => (sm p ×ˢ bg p).image (fun x => s(x.1, x.2)))) := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        rw [SimpleGraph.mem_edgeSet] at he
        obtain ⟨p, hp, hc⟩ := hF.2 u v he
        rw [Finset.mem_coe, Finset.mem_biUnion]
        refine ⟨p, hp, Finset.mem_image.mpr ?_⟩
        rcases cov p u v hc with h | h
        · exact ⟨(u, v), Finset.mem_product.mpr h, rfl⟩
        · exact ⟨(v, u), Finset.mem_product.mpr h, Sym2.eq_swap⟩
    have h2 : G.edgeSet.ncard ≤ ∑ p ∈ F, (bg p).card := by
      have ha := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset] at ha
      have hb : (F.biUnion (fun p => (sm p ×ˢ bg p).image (fun x => s(x.1, x.2)))).card
          ≤ ∑ p ∈ F, ((sm p ×ˢ bg p).image (fun x => s(x.1, x.2))).card :=
        Finset.card_biUnion_le
      have hc : ∑ p ∈ F, ((sm p ×ˢ bg p).image (fun x => s(x.1, x.2))).card
          ≤ ∑ p ∈ F, (bg p).card := by
        apply Finset.sum_le_sum
        intro p hp
        have hd : ((sm p ×ˢ bg p).image (fun x => s(x.1, x.2))).card ≤ (sm p ×ˢ bg p).card :=
          Finset.card_image_le
        rw [Finset.card_product, sm_card G p (hF.1 p hp) (hs p hp), one_mul] at hd
        exact hd
      omega
    have h3 : ∑ p ∈ F, blockCost p = ∑ p ∈ F, (bg p).card :=
      Finset.sum_congr rfl (fun p hp => cost_eq G p (hF.1 p hp) (hs p hp))
    unfold familyCost
    rw [h3]
    omega

end PEqualNP.Outside.L_meta_1902

theorem PEqualNP.Outside.L_meta_1902 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (PEqualNP.BicliqueBlockCost.Block x1)), PEqualNP.BicliqueBlockCost.IsBlockCover x2 x3 → (∀ x5 ∈ x3, x5.1.card ≤ (1 : ℕ) ∨ x5.2.card ≤ (1 : ℕ)) → ∃ (x6 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x6 ∧ x2.edgeSet.ncard + x6.card ≤ PEqualNP.BicliqueBlockCost.familyCost x3 + (1 : ℕ) := by
  intro x1 x2 x3 h1 h2
  exact PEqualNP.Outside.L_meta_1902.main x2 x3 h1 h2
