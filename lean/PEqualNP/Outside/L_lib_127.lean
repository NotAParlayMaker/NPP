import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_127_aux

lemma hall_rows {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (t : Fin n → Finset (Fin n))
    (ht : ∀ i j, j ∈ t i ↔ ∃ b : Bool, (π (i,b)).1 = j) :
    ∀ s : Finset (Fin n), s.card ≤ (s.biUnion t).card := by
  intro s
  let A := s ×ˢ (Finset.univ : Finset Bool)
  let B := s.biUnion t ×ˢ (Finset.univ : Finset Bool)
  have hsub : A.image π ⊆ B := by
    intro y hy
    obtain ⟨⟨i,b⟩, h, rfl⟩ := Finset.mem_image.mp hy
    have hi : i ∈ s := (Finset.mem_product.mp h).1
    exact Finset.mem_product.mpr
      ⟨Finset.mem_biUnion.mpr ⟨i, hi, (ht i _).mpr ⟨b, rfl⟩⟩, Finset.mem_univ _⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ π.injective] at hcard
  simp [A, B, Finset.card_product] at hcard
  omega

lemma other_injective {n : ℕ} (π : Equiv.Perm (Fin n × Bool)) (b : Fin n → Bool)
    (p : Equiv.Perm (Fin n)) (h : ∀ i, (π (i, b i)).1 = p i) :
    Function.Injective (fun i => (π (i, !(b i))).1) := by
  intro i k hik
  change (π (i, !(b i))).1 = (π (k, !(b k))).1 at hik
  let j := (π (i, !(b i))).1
  let t := p.symm j
  have ht : (π (t, b t)).1 = j := (h t).trans (p.apply_symm_apply j)
  have avoid (v : Fin n) (hv : (π (v, !(b v))).1 = j) :
      (π (v, !(b v))).2 ≠ (π (t, b t)).2 := by
    intro hbits
    have eqpair := π.injective (Prod.ext (hv.trans ht.symm) hbits)
    have evt : v = t := congrArg Prod.fst eqpair
    have eno : (!(b v)) = b t := congrArg Prod.snd eqpair
    rw [← evt] at eno
    cases hval : b v <;> simp [hval] at eno
  have hi := avoid i rfl
  have hk := avoid k hik.symm
  have bit_unique (a c d : Bool) (ha : a ≠ d) (hc : c ≠ d) : a = c := by
    cases a <;> cases c <;> cases d <;> simp_all
  have hver := bit_unique _ _ _ hi hk
  exact congrArg Prod.fst (π.injective (Prod.ext hik hver))

end PEqualNP.Outside.L_lib_127_aux

open PEqualNP.Outside.L_lib_127_aux

theorem PEqualNP.Outside.L_lib_127 :
    ∀ (n : ℕ) (π : Equiv.Perm (Fin n × Bool)), ∃ b : Fin n → Bool, ∃ π₀ π₁ : Equiv.Perm (Fin n), ∀ (ρ : Fin n) (β : Bool), (π (ρ, β)).1 = (if (β != b ρ) = true then π₁ else π₀) ρ := by
  classical
  intro n π
  let t (i : Fin n) := (Finset.univ : Finset Bool).image (fun b => (π (i, b)).1)
  have ht (i j) : j ∈ t i ↔ ∃ b : Bool, (π (i, b)).1 = j := by
    simp only [t, Finset.mem_image, Finset.mem_univ, true_and]
  obtain ⟨f, hf, hrep⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp (hall_rows π t ht)
  let p := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have bits (i : Fin n) : ∃ b : Bool, (π (i, b)).1 = p i := (ht i (f i)).mp (hrep i)
  choose b hb using bits
  let q := Equiv.ofBijective (fun i => (π (i, !(b i))).1)
    (Finite.injective_iff_bijective.mp (other_injective π b p hb))
  refine ⟨b, p, q, ?_⟩
  intro i β
  by_cases h : β = b i
  · subst β
    simpa using hb i
  · have hb' : β = !(b i) := by cases β <;> cases hbi : b i <;> simp_all
    simpa only [show (β != b i) = true by simpa using h, ite_true] using
      (show (π (i, β)).1 = q i from congrArg (fun z => (π (i, z)).1) hb')
