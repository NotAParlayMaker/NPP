import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_127

lemma matching (n : ℕ) (π : Equiv.Perm (Fin n × Bool)) :
    ∃ f : Fin n → Fin n, Function.Injective f ∧
      ∀ r, ∃ β : Bool, (π (r, β)).1 = f r := by
  classical
  let t : Fin n → Finset (Fin n) :=
    fun r => Finset.univ.image (fun β : Bool => (π (r, β)).1)
  have hall : ∀ s : Finset (Fin n), s.card ≤ (s.biUnion t).card := by
    intro s
    have hsub : (s.product (Finset.univ : Finset Bool)).image π ⊆
        (s.biUnion t).product (Finset.univ : Finset Bool) := by
      intro y hy
      obtain ⟨⟨r, β⟩, hr, rfl⟩ := Finset.mem_image.mp hy
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨r, (Finset.mem_product.mp hr).1,
        Finset.mem_image.mpr ⟨β, Finset.mem_univ _, rfl⟩⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ π.injective] at hc
    simp only [Finset.product_eq_sprod, Finset.card_product,
      Finset.card_univ, Fintype.card_bool] at hc
    omega
  obtain ⟨f, hf, ht⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  refine ⟨f, hf, fun r => ?_⟩
  obtain ⟨β, _, hβ⟩ := Finset.mem_image.mp (ht r)
  exact ⟨β, hβ⟩

lemma complement_injective (n : ℕ) (π : Equiv.Perm (Fin n × Bool))
    (f : Fin n → Fin n) (hf : Function.Injective f)
    (b : Fin n → Bool) (hb : ∀ r, (π (r, b r)).1 = f r) :
    Function.Injective (fun r => (π (r, !(b r))).1) := by
  have separate (r s : Fin n) : π (r, b r) ≠ π (s, !(b s)) := by
    intro h
    have hp := π.injective h
    have hrs : r = s := congrArg Prod.fst hp
    have hbits : b r = !(b s) := congrArg Prod.snd hp
    subst s
    cases hbr : b r <;> simp [hbr] at hbits
  intro r s h
  obtain ⟨t, ht⟩ := (Finite.surjective_of_injective hf) ((π (r, !(b r))).1)
  have ha : (π (t, b t)).1 = (π (r, !(b r))).1 := (hb t).trans ht
  have hc : (π (t, b t)).1 = (π (s, !(b s))).1 := ha.trans h
  have htr : (π (t, b t)).2 ≠ (π (r, !(b r))).2 :=
    fun e => separate t r (Prod.ext ha e)
  have hts : (π (t, b t)).2 ≠ (π (s, !(b s))).2 :=
    fun e => separate t s (Prod.ext hc e)
  have he : (π (r, !(b r))).2 = (π (s, !(b s))).2 := by
    cases htt : (π (t, b t)).2 <;> cases hrr : (π (r, !(b r))).2 <;>
      cases hss : (π (s, !(b s))).2 <;> simp_all
  exact congrArg Prod.fst (π.injective (Prod.ext h he))

end PEqualNP.Outside.L_lib_127

theorem PEqualNP.Outside.L_lib_127 : ∀ (n : ℕ) (π : Equiv.Perm (Fin n × Bool)), ∃ b : Fin n → Bool, ∃ π₀ π₁ : Equiv.Perm (Fin n), ∀ (ρ : Fin n) (β : Bool), (π (ρ, β)).1 = (if (β != b ρ) = true then π₁ else π₀) ρ := by
  classical
  intro n π
  obtain ⟨f, hf, h⟩ := PEqualNP.Outside.L_lib_127.matching n π
  choose b hb using h
  let π₀ : Equiv.Perm (Fin n) := Equiv.ofBijective f
    ⟨hf, Finite.surjective_of_injective hf⟩
  let g : Fin n → Fin n := fun r => (π (r, !(b r))).1
  have hg : Function.Injective g :=
    PEqualNP.Outside.L_lib_127.complement_injective n π f hf b hb
  let π₁ : Equiv.Perm (Fin n) := Equiv.ofBijective g
    ⟨hg, Finite.surjective_of_injective hg⟩
  refine ⟨b, π₀, π₁, fun ρ β => ?_⟩
  by_cases he : β = b ρ
  · subst β
    simpa [π₀, Equiv.ofBijective] using hb ρ
  · have hn : β = !(b ρ) := by
      cases β <;> cases hbr : b ρ <;> simp_all
    simp [hn, π₁, g, Equiv.ofBijective]
