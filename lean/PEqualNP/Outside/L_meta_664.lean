import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_664_aux

theorem card_comap {G : Type} [AddCommGroup G] [Finite G] (φ : G →+ G) (A : AddSubgroup G)
    (h : φ.range ⊔ A = ⊤) : Nat.card (A.comap φ) = Nat.card A := by
  have h1 : (A.comap φ).index = A.index := by
    rw [AddSubgroup.index_comap, ← AddSubgroup.relIndex_sup_right, h, AddSubgroup.relIndex_top_right]
  have h2 := (A.comap φ).card_mul_index
  have h3 := A.card_mul_index
  rw [h1, ← h3] at h2
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero AddSubgroup.index_ne_zero_of_finite) h2

theorem sup_top {G : Type} [AddCommGroup G] [Finite G] (R A : AddSubgroup G) (h2 : R.index = 2)
    (x : G) (hx : x ∈ A) (hxR : x ∉ R) : R ⊔ A = ⊤ := by
  rw [← AddSubgroup.index_eq_one]
  have hm := AddSubgroup.relIndex_mul_index (H := R) (K := R ⊔ A) le_sup_left
  rw [h2] at hm
  have hd : (R ⊔ A).index ∣ 2 := Dvd.intro_left _ hm
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
  · exact h
  · exfalso
    rw [h] at hm
    have h1 : R.relIndex (R ⊔ A) = 1 := by omega
    rw [AddSubgroup.relIndex_eq_one] at h1
    exact hxR (h1 (AddSubgroup.mem_sup_right hx))

theorem range_index {G : Type} [AddCommGroup G] [Finite G] (φ : G →+ G) (κ : G) (hκ : κ ≠ 0)
    (hker : ∀ t, φ t = 0 ↔ t = 0 ∨ t = κ) : φ.range.index = 2 := by
  have h1 := AddSubgroup.index_ker φ
  have h2 := φ.ker.card_mul_index
  have h3 := φ.range.card_mul_index
  have h4 : Nat.card φ.ker = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨0, by simp⟩, ⟨κ, (hker κ).2 (Or.inr rfl)⟩, ?_, ?_⟩
    · intro h
      exact hκ (Subtype.ext_iff.1 h).symm
    · ext ⟨t, ht⟩
      have := (hker t).1 ht
      simpa [Subtype.ext_iff] using this
  rw [h4, h1] at h2
  rw [← h2] at h3
  have h5 : 0 < Nat.card φ.range := Nat.card_pos
  nlinarith

theorem core (F : Type) [Field F] [Fintype F] [DecidableEq F] (φ : F →+ F) (A : AddSubgroup F)
    [DecidablePred (· ∈ A)] (a t0 : F) (ht0 : a + φ t0 ∈ A) (h : φ.range ⊔ A = ⊤) :
    (Finset.univ.filter (fun t : F => a + φ t ∈ A)).card = Nat.card A := by
  rw [← card_comap φ A h, ← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  refine
    { toFun := fun t => ⟨t.1 - t0, ?_⟩
      invFun := fun s => ⟨s.1 + t0, ?_⟩
      left_inv := fun t => Subtype.ext (by simp)
      right_inv := fun s => Subtype.ext (by simp) }
  · have h1 := A.sub_mem (Finset.mem_filter.1 t.2).2 ht0
    rw [AddSubgroup.mem_comap, map_sub]
    convert h1 using 1
    ring
  · have h1 := A.add_mem s.2 ht0
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [map_add]
    convert h1 using 1
    ring

theorem anis (F : Type) [Field F] (b : F) (hb : ∀ X : F, X ^ 2 + b * X + 1 ≠ 0) (x y : F)
    (h : x ^ 2 + b * x * y + y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst hy
    refine ⟨?_, rfl⟩
    simpa using h
  · exfalso
    apply hb (x / y)
    field_simp
    linear_combination h

theorem hom (F : Type) [Field F] [CharP F 2] (α β : F) :
    ∃ φ : F →+ F, ∀ t, φ t = α * t ^ 2 + β * t :=
  ⟨AddMonoidHom.mk' (fun t => α * t ^ 2 + β * t) (fun s t => by
    show α * (s + t) ^ 2 + β * (s + t) = _
    rw [CharTwo.add_sq]
    ring), fun _ => rfl⟩

end PEqualNP.Outside.L_meta_664_aux

open PEqualNP.Outside.L_meta_664_aux in
theorem PEqualNP.Outside.L_meta_664 : ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b : F), (∀ X : F, X ^ 2 + b * X + 1 ≠ 0) → ∀ (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F), d ≠ 0 → ((Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = 0 ∨ (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) ∧ (p = 0 → (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) := by
  intro F _ _ _ _ b hb A _ p d hd
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨φ, hφ⟩ := hom F (d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2) (b * (p.1 * d.2 + p.2 * d.1))
  have hα : d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2 ≠ 0 := by
    intro h
    obtain ⟨e1, e2⟩ := anis F b hb _ _ h
    exact hd (Prod.ext e1 e2)
  have hexp : ∀ t : F, (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2
      = (p.1 ^ 2 + b * p.1 * p.2 + p.2 ^ 2) + φ t := by
    intro t
    rw [hφ]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination (p.1 * d.1 * t + p.2 * d.2 * t) * h2
  have hfilter : (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A))
      = Finset.univ.filter (fun t : F => (p.1 ^ 2 + b * p.1 * p.2 + p.2 ^ 2) + φ t ∈ A) :=
    Finset.filter_congr (fun t _ => by rw [hexp t])
  rw [hfilter]
  have key : (∃ t0, (p.1 ^ 2 + b * p.1 * p.2 + p.2 ^ 2) + φ t0 ∈ A) →
      (Finset.univ.filter (fun t : F => (p.1 ^ 2 + b * p.1 * p.2 + p.2 ^ 2) + φ t ∈ A)).card = Nat.card A := by
    rintro ⟨t0, ht0⟩
    apply core F φ A _ t0 ht0
    by_cases hβ : b * (p.1 * d.2 + p.2 * d.1) = 0
    · have hinj : Function.Injective φ := by
        rw [injective_iff_map_eq_zero]
        intro t ht
        rw [hφ, hβ] at ht
        simpa [hα] using ht
      have hsur : Function.Surjective φ := Finite.surjective_of_injective hinj
      rw [AddMonoidHom.range_eq_top.2 hsur]
      simp
    · refine sup_top _ _ ?_ _ ht0 ?_
      · apply range_index φ (-(b * (p.1 * d.2 + p.2 * d.1)) / (d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2))
        · simpa [hα] using hβ
        · intro t
          rw [hφ]
          constructor
          · intro h
            have h' : t * ((d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2) * t + b * (p.1 * d.2 + p.2 * d.1)) = 0 := by
              linear_combination h
            rcases mul_eq_zero.1 h' with h3 | h3
            · exact Or.inl h3
            · right
              rw [eq_div_iff hα]
              linear_combination h3
          · rintro (rfl | rfl)
            · simp
            · field_simp
              ring
      · rintro ⟨s, hs⟩
        have h0 := hexp (t0 - s)
        rw [map_sub, hs] at h0
        have h0' : (p + (t0 - s) • d).1 ^ 2 + b * (p + (t0 - s) • d).1 * (p + (t0 - s) • d).2 + (p + (t0 - s) • d).2 ^ 2 = 0 := by
          rw [h0]
          ring
        obtain ⟨e1, e2⟩ := anis F b hb _ _ h0'
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2
        apply hβ
        linear_combination b * d.2 * e1 + b * d.1 * e2 - (b * (t0 - s) * d.1 * d.2) * h2
  refine ⟨?_, fun hp => key ⟨0, by subst hp; simp⟩⟩
  by_cases h : ∃ t0, (p.1 ^ 2 + b * p.1 * p.2 + p.2 ^ 2) + φ t0 ∈ A
  · exact Or.inr (key h)
  · left
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _ ht
    exact h ⟨t, ht⟩
