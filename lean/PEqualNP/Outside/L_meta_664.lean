import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_664_aux

open Finset

def f {F : Type} [Field F] (q c r t : F) : F := r + c * t + q * t ^ 2

lemma cardA {F : Type} [Field F] [Fintype F] [DecidableEq F] (A : AddSubgroup F)
    [DecidablePred (· ∈ A)] : (univ.filter (fun x : F => x ∈ A)).card = Nat.card A := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma lin {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (q r : F) (hq : q ≠ 0)
    (A : AddSubgroup F) [DecidablePred (· ∈ A)] :
    (univ.filter (fun t : F => f q 0 r t ∈ A)).card = Nat.card A := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hinj : Function.Injective (f q 0 r) := by
    intro t s h
    simp only [f] at h
    have h1 : q * (t - s) ^ 2 = 0 := by linear_combination h + (q * s ^ 2 - q * t * s) * h2
    rcases mul_eq_zero.1 h1 with h3 | h3
    · exact absurd h3 hq
    · exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h3)
  have hsurj : Function.Surjective (f q 0 r) := Finite.injective_iff_surjective.1 hinj
  rw [← cardA, ← Finset.card_image_of_injective _ hinj]
  congr 1
  ext y
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hy
    obtain ⟨t, rfl⟩ := hsurj y
    exact ⟨t, hy, rfl⟩

lemma quad {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (q c r : F) (hq : q ≠ 0)
    (hc : c ≠ 0) (hf : ∀ t, f q c r t ≠ 0) (A : AddSubgroup F) [DecidablePred (· ∈ A)] :
    (univ.filter (fun t : F => f q c r t ∈ A)).card = 0 ∨
      (univ.filter (fun t : F => f q c r t ∈ A)).card = Nat.card A := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨k, hk⟩ : ∃ k, q * k = c := ⟨c / q, by field_simp⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hc (by simpa using hk.symm)
  have hadd : ∀ t s u, f q c r (t + s + u) = f q c r t + f q c r s + f q c r u := by
    intro t s u
    simp only [f]
    linear_combination (q * (t * s + t * u + s * u) - r) * h2
  have hfib : ∀ t, univ.filter (fun s => f q c r s = f q c r t) = {t, t + k} := by
    intro t
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · intro h
      have h1 : (s - t) * (c + q * (s + t)) = 0 := by
        simp only [f] at h
        linear_combination h
      rcases mul_eq_zero.1 h1 with h3 | h3
      · left
        exact sub_eq_zero.1 h3
      · right
        have h4 : q * (s - (t + k)) = 0 := by linear_combination h3 - (q * t + c) * h2 - hk
        rcases mul_eq_zero.1 h4 with h5 | h5
        · exact absurd h5 hq
        · exact sub_eq_zero.1 h5
    · rintro (rfl | rfl)
      · rfl
      · simp only [f]
        linear_combination (c * k + q * t * k) * h2 + k * hk
  have hpair : ∀ t : F, ({t, t + k} : Finset F).card = 2 := by
    intro t
    apply card_pair
    intro h
    exact hk0 (by simpa using h)
  obtain ⟨S, hS⟩ : ∃ S : Finset F, S = univ.filter (fun t : F => f q c r t ∈ A) := ⟨_, rfl⟩
  rw [← hS]
  by_cases hem : S = ∅
  · left
    simp [hem]
  right
  obtain ⟨t0, ht0⟩ := nonempty_of_ne_empty hem
  have ha0 : f q c r t0 ∈ A := by
    rw [hS] at ht0
    simpa using ht0
  obtain ⟨I, hIdef⟩ : ∃ I : Finset F, I = univ.image (f q c r) := ⟨_, rfl⟩
  have hmemI : ∀ t, f q c r t ∈ I := by
    intro t
    rw [hIdef]
    exact mem_image_of_mem _ (mem_univ t)
  have hIex : ∀ y ∈ I, ∃ t, f q c r t = y := by
    intro y hy
    rw [hIdef] at hy
    obtain ⟨t, -, ht⟩ := mem_image.1 hy
    exact ⟨t, ht⟩
  have hI : Fintype.card F = I.card * 2 := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset F)) (t := I)
      (f := f q c r) (fun x _ => hmemI x)
    rw [Finset.card_univ] at h
    rw [h]
    apply Finset.sum_const_nat
    intro y hy
    obtain ⟨t, rfl⟩ := hIex y hy
    rw [hfib t]
    exact hpair t
  have hdisj : ∀ t u, f q c r u ≠ f q c r t + f q c r t0 := by
    intro t u h
    apply hf (u + t + t0)
    rw [hadd, h]
    linear_combination (f q c r t + f q c r t0) * h2
  have hcov : ∀ y, y ∈ I ∨ y + f q c r t0 ∈ I := by
    have hJ : (I.image (fun y => y + f q c r t0)).card = I.card :=
      card_image_of_injective _ (add_left_injective _)
    have hdj : Disjoint I (I.image (fun y => y + f q c r t0)) := by
      rw [Finset.disjoint_left]
      intro y hy hy2
      obtain ⟨u, rfl⟩ := hIex y hy
      obtain ⟨z, hz, hz2⟩ := mem_image.1 hy2
      obtain ⟨t, rfl⟩ := hIex z hz
      exact hdisj t u hz2.symm
    have hU : I ∪ I.image (fun y => y + f q c r t0) = univ := by
      apply Finset.eq_univ_of_card
      rw [card_union_of_disjoint hdj, hJ, hI]
      ring
    intro y
    have hy : y ∈ I ∪ I.image (fun y => y + f q c r t0) := by
      rw [hU]
      exact mem_univ y
    rcases mem_union.1 hy with h | h
    · left
      exact h
    · right
      obtain ⟨z, hz, rfl⟩ := mem_image.1 h
      have e : z + f q c r t0 + f q c r t0 = z := by linear_combination f q c r t0 * h2
      rw [e]
      exact hz
  obtain ⟨n, hn⟩ : ∃ n : F → ℕ, ∀ a, n a = (S.filter (fun t => f q c r t = a)).card :=
    ⟨_, fun _ => rfl⟩
  have hn1 : ∀ a, a ∈ A → a ∈ I → n a = 2 := by
    intro a ha hai
    obtain ⟨t, rfl⟩ := hIex a hai
    have e : S.filter (fun s => f q c r s = f q c r t) =
        univ.filter (fun s => f q c r s = f q c r t) := by
      ext s
      simp only [hS, mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨h ▸ ha, h⟩
    rw [hn, e, hfib t]
    exact hpair t
  have hn0 : ∀ a, a ∉ I → n a = 0 := by
    intro a ha
    rw [hn, card_eq_zero, filter_eq_empty_iff]
    intro s _ h
    exact ha (h ▸ hmemI s)
  have hnn : ∀ a, a ∈ A → n a + n (a + f q c r t0) = 2 := by
    intro a ha
    by_cases hai : a ∈ I
    · have h3 : a + f q c r t0 ∉ I := by
        intro h
        obtain ⟨t, rfl⟩ := hIex a hai
        obtain ⟨u, hu⟩ := hIex _ h
        exact hdisj t u hu
      rw [hn1 a ha hai, hn0 _ h3]
    · have h3 : a + f q c r t0 ∈ I := by
        rcases hcov a with h | h
        · exact absurd h hai
        · exact h
      rw [hn0 a hai, hn1 _ (A.add_mem ha ha0) h3]
  have hsum1 : S.card = ∑ a ∈ univ.filter (fun x : F => x ∈ A), n a := by
    have h := Finset.card_eq_sum_card_fiberwise (s := S) (t := univ.filter (fun x : F => x ∈ A))
      (f := f q c r) (fun t ht => by
        rw [hS] at ht
        simpa using ht)
    rw [h]
    exact Finset.sum_congr rfl (fun a _ => (hn a).symm)
  have hsum2 : ∑ a ∈ univ.filter (fun x : F => x ∈ A), n (a + f q c r t0) =
      ∑ a ∈ univ.filter (fun x : F => x ∈ A), n a := by
    refine Finset.sum_nbij' (fun a => a + f q c r t0) (fun a => a + f q c r t0) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      exact A.add_mem ha ha0
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      exact A.add_mem ha ha0
    · intro a _
      linear_combination f q c r t0 * h2
    · intro a _
      linear_combination f q c r t0 * h2
    · intro a _
      rfl
  have hsum3 : ∑ a ∈ univ.filter (fun x : F => x ∈ A), (n a + n (a + f q c r t0)) =
      (univ.filter (fun x : F => x ∈ A)).card * 2 := by
    apply Finset.sum_const_nat
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    exact hnn a ha
  rw [Finset.sum_add_distrib, hsum2, ← hsum1, cardA] at hsum3
  omega

lemma aniso {F : Type} [Field F] (b : F) (hb : ∀ X : F, X ^ 2 + b * X + 1 ≠ 0) (x y : F)
    (h : x ^ 2 + b * x * y + y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst hy
    have h1 : x ^ 2 = 0 := by linear_combination h
    exact ⟨pow_eq_zero_iff (two_ne_zero) |>.1 h1, rfl⟩
  · exfalso
    apply hb (x / y)
    field_simp
    linear_combination h

end PEqualNP.Outside.L_meta_664_aux

open PEqualNP.Outside.L_meta_664_aux in
theorem PEqualNP.Outside.L_meta_664 : ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b : F), (∀ X : F, X ^ 2 + b * X + 1 ≠ 0) → ∀ (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F), d ≠ 0 → ((Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = 0 ∨ (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) ∧ (p = 0 → (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) := by
  intro F _ _ _ _ b hb A _ p d hd
  obtain ⟨p1, p2⟩ := p
  obtain ⟨d1, d2⟩ := d
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have key : ∀ t : F, ((p1, p2) + t • (d1, d2)).1 ^ 2 + b * ((p1, p2) + t • (d1, d2)).1 * ((p1, p2) + t • (d1, d2)).2 + ((p1, p2) + t • (d1, d2)).2 ^ 2 = f (d1 ^ 2 + b * d1 * d2 + d2 ^ 2) (b * (p1 * d2 + p2 * d1)) (p1 ^ 2 + b * p1 * p2 + p2 ^ 2) t := by
    intro t
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, f]
    linear_combination (t * p1 * d1 + t * p2 * d2) * h2
  simp only [key]
  have hq : d1 ^ 2 + b * d1 * d2 + d2 ^ 2 ≠ 0 := by
    intro h
    obtain ⟨h1, h3⟩ := aniso b hb d1 d2 h
    apply hd
    rw [h1, h3]
    rfl
  by_cases hc : b * (p1 * d2 + p2 * d1) = 0
  · rw [hc]
    have h := lin (d1 ^ 2 + b * d1 * d2 + d2 ^ 2) (p1 ^ 2 + b * p1 * p2 + p2 ^ 2) hq A
    exact ⟨Or.inr h, fun _ => h⟩
  · refine ⟨quad _ _ _ hq hc ?_ A, ?_⟩
    · intro t ht
      rw [← key t] at ht
      obtain ⟨h1, h3⟩ := aniso b hb _ _ ht
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h3
      apply hc
      linear_combination b * d2 * h1 + b * d1 * h3 - b * t * d1 * d2 * h2
    · intro hp
      exfalso
      apply hc
      have e1 : p1 = 0 := congrArg Prod.fst hp
      have e2 : p2 = 0 := congrArg Prod.snd hp
      rw [e1, e2]
      ring
