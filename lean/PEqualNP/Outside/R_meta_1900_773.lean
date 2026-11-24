import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.BicliqueBlockCost PEqualNP.SharedBlockCost
open scoped BigOperators

theorem PEqualNP.Outside.R_meta_1900_773
    (extractShared : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
      (∃ u v, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      HasSharedBlockCost G C.size)
    (mergeCenters : ∀ (n c : ℕ) (G : SimpleGraph (Fin n)),
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      HasSharedBlockCost G c →
      ∃ (F : Finset (Block n)) (k : ℕ), IsBlockCover G F ∧
        HasOrCost n (F.image Prod.snd) k ∧ k + F.card + (F.card - 1) ≤ c ∧
        (∀ p ∈ F, p.1.card = 1) ∧
        (∀ p ∈ F, ∀ q ∈ F, p ≠ q → p.1 ≠ q.1))
    (chargeOr : ∀ (n k : ℕ) (B : Finset (Finset (Fin n))),
      (∀ s ∈ B, s.Nonempty) →
      (∀ s ∈ B, ∀ t ∈ B, s ≠ t → (s ∩ t).card ≤ 1) →
      HasOrCost n B k → (∑ s ∈ B, (s.card - 1)) ≤ k) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x3.size := by
  classical
  intro n G C hEdge hC4 hModel hComputes
  obtain ⟨F, k, cover, orCost, budget, centers, sep⟩ :=
    mergeCenters n C.size G hC4 (extractShared n G C hEdge hC4 hModel hComputes)
  let B := F.image Prod.snd
  have inter : ∀ p ∈ F, ∀ q ∈ F, p ≠ q → (p.2 ∩ q.2).card ≤ 1 := by
    intro p hp q hq hpq
    by_contra! many
    obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp many
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp (centers p hp)
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (centers q hq)
    have huv : u ≠ v := by
      intro h
      exact sep p hp q hq hpq (hu.trans (h ▸ hv.symm))
    have hpu : u ∈ p.1 := by simp [hu]
    have hqv : v ∈ q.1 := by simp [hv]
    obtain ⟨dP, _, _, adjP⟩ := cover.1 p hp
    obtain ⟨dQ, _, _, adjQ⟩ := cover.1 q hq
    obtain ⟨hap, haq⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbp, hbq⟩ := Finset.mem_inter.mp hb
    have ua := adjP u hpu a hap
    have ub := adjP u hpu b hbp
    have va := adjQ v hqv a haq
    have vb := adjQ v hqv b hbq
    exact hC4 u a v b ua.ne huv ub.ne va.ne.symm hab vb.ne ua va.symm vb ub.symm
  have hn : ∀ s ∈ B, s.Nonempty := by
    intro s hs
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
    exact (cover.1 p hp).2.2.1
  have hi : ∀ s ∈ B, ∀ t ∈ B, s ≠ t → (s ∩ t).card ≤ 1 := by
    intro s hs t ht hst
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
    exact inter p hp q hq (fun e => hst (congrArg Prod.snd e))
  have hCharge := chargeOr n k B hn hi orCost
  let F' := F.filter (fun p => 1 < p.2.card)
  have inj : Set.InjOn Prod.snd (↑F' : Set (Block n)) := by
    intro p hp q hq h
    have hp' := Finset.mem_filter.mp hp
    have hq' := Finset.mem_filter.mp hq
    by_contra hne
    have hbound := inter p hp'.1 q hq'.1 hne
    rw [← h, Finset.inter_self] at hbound
    omega
  have sumFiltered :
      (∑ p ∈ F, (p.2.card - 1)) = ∑ p ∈ F', (p.2.card - 1) := by
    simp only [F', Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    split
    · rfl
    · omega
  have sumImage :
      (∑ p ∈ F', (p.2.card - 1)) = ∑ s ∈ F'.image Prod.snd, (s.card - 1) :=
    (Finset.sum_image (f := fun s : Finset (Fin n) => s.card - 1)
      (fun _ ha _ hb eq => inj ha hb eq)).symm
  have subsetSides : F'.image Prod.snd ⊆ B := Finset.image_subset_image (Finset.filter_subset _ _)
  have paid : (∑ p ∈ F, (p.2.card - 1)) ≤ k := calc
    _ = _ := sumFiltered.trans sumImage
    _ ≤ ∑ s ∈ B, (s.card - 1) := Finset.sum_le_sum_of_subset subsetSides
    _ ≤ k := hCharge
  have total :
      (∑ p ∈ F, blockCost p) = (∑ p ∈ F, (p.2.card - 1)) + F.card := by
    calc
      _ = ∑ p ∈ F, ((p.2.card - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hNe := Finset.card_pos.mpr (cover.1 p hp).2.2.1
        unfold blockCost
        rw [centers p hp]
        omega
      _ = _ := by simp [Finset.sum_add_distrib]
  refine ⟨F, cover, ?_⟩
  unfold familyCost
  omega
