import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3362

lemma mul_le_add_of_le_one (a b : ℕ) (h : a ≤ 1 ∨ b ≤ 1) : a * b ≤ a + b := by
  rcases h with ha | hb
  · have ha' : a = 0 ∨ a = 1 := by omega
    rcases ha' with rfl | rfl <;> simp
  · have hb' : b = 0 ∨ b = 1 := by omega
    rcases hb' with rfl | rfl <;> simp

lemma solve (n d m : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I]
    (hdeg : ∀ l : Fin n, Fintype.card { p : Fin n // I p l } = d)
    (huniq : ∀ p q : Fin n, p ≠ q → ∃! l : Fin n, I p l ∧ I q l)
    (A B : Fin m → Finset (Fin n))
    (hbic : ∀ k : Fin m, ∀ p ∈ A k, ∀ l ∈ B k, I p l)
    (hcov : ∀ p l : Fin n, I p l → ∃ k : Fin m, p ∈ A k ∧ l ∈ B k) :
    n * d ≤ ∑ k : Fin m, ((A k).card + (B k).card) := by
  let S : Finset (Fin n × Fin n) := Finset.univ.filter (fun z => I z.1 z.2)
  have hS_eq : S = Finset.univ.biUnion (fun l : Fin n =>
      (Finset.univ.filter (fun p : Fin n => I p l)).image (fun p => (p, l))) := by
    ext ⟨p, l⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro hpl
      exact ⟨l, p, hpl, rfl, rfl⟩
    · rintro ⟨l', p', hp'l', rfl, rfl⟩
      exact hp'l'
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin n)) (fun l =>
      (Finset.univ.filter (fun p : Fin n => I p l)).image (fun p => (p, l))) := by
    intro l₁ _ l₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    rcases Finset.mem_image.mp hz₁ with ⟨p₁, _, rfl⟩
    rcases Finset.mem_image.mp hz₂ with ⟨p₂, _, heq⟩
    exact hne (Prod.mk.inj heq).2.symm
  have hS_card : S.card = n * d := by
    rw [hS_eq, Finset.card_biUnion hdisj]
    have hterm : ∀ l : Fin n,
        ((Finset.univ.filter (fun p : Fin n => I p l)).image (fun p => (p, l))).card = d := by
      intro l
      rw [Finset.card_image_of_injective _ (fun p₁ p₂ h => (Prod.mk.inj h).1)]
      rw [← Fintype.card_subtype]
      exact hdeg l
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hsub : S ⊆ Finset.univ.biUnion (fun k : Fin m => A k ×ˢ B k) := by
    intro ⟨p, l⟩ hmem
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    obtain ⟨k, hkA, hkB⟩ := hcov p l hmem
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, Finset.mem_product.mpr ⟨hkA, hkB⟩⟩
  have hS_le : S.card ≤ ∑ k : Fin m, (A k ×ˢ B k).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hsmall : ∀ k : Fin m, (A k).card ≤ 1 ∨ (B k).card ≤ 1 := by
    intro k
    by_contra hboth
    rw [not_or] at hboth
    have ha1 : 1 < (A k).card := by omega
    have hb1 : 1 < (B k).card := by omega
    obtain ⟨p₁, hp₁, p₂, hp₂, hpne⟩ := Finset.one_lt_card.mp ha1
    obtain ⟨l₁, hl₁, l₂, hl₂, hlne⟩ := Finset.one_lt_card.mp hb1
    obtain ⟨_, _, hu⟩ := huniq p₁ p₂ hpne
    have hl₁eq := hu l₁ ⟨hbic k p₁ hp₁ l₁ hl₁, hbic k p₂ hp₂ l₁ hl₁⟩
    have hl₂eq := hu l₂ ⟨hbic k p₁ hp₁ l₂ hl₂, hbic k p₂ hp₂ l₂ hl₂⟩
    exact hlne (hl₁eq.trans hl₂eq.symm)
  calc
    n * d = S.card := hS_card.symm
    _ ≤ ∑ k : Fin m, (A k ×ˢ B k).card := hS_le
    _ = ∑ k : Fin m, (A k).card * (B k).card := by
      refine Finset.sum_congr rfl fun k _ => ?_
      exact Finset.card_product (A k) (B k)
    _ ≤ ∑ k : Fin m, ((A k).card + (B k).card) := by
      refine Finset.sum_le_sum fun k _ => ?_
      exact mul_le_add_of_le_one (A k).card (B k).card (hsmall k)

end PEqualNP.Outside.L_meta_3362

theorem PEqualNP.Outside.L_meta_3362 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x1 → Fin x1 → Prop) [x5 : DecidableRel x4], (∀ (x6 : Fin x1), Fintype.card { x7 : Fin x1 // x4 x7 x6 } = x2) → (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x4 x7 x10 ∧ x4 x8 x10) → ∀ (x8 x9 : Fin x3 → Finset (Fin x1)), (∀ (x10 : Fin x3), ∀ x11 ∈ x8 x10, ∀ x13 ∈ x9 x10, x4 x11 x13) → (∀ (x11 x12 : Fin x1), x4 x11 x12 → ∃ (x14 : Fin x3), x11 ∈ x8 x14 ∧ x12 ∈ x9 x14) → x1 * x2 ≤ ∑ x12 : Fin x3, ((x8 x12).card + (x9 x12).card) := by
  exact PEqualNP.Outside.L_meta_3362.solve
