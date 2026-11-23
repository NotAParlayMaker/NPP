import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_664

lemma index_range_eq {G : Type} [AddCommGroup G] [Finite G] (φ : G →+ G) :
    φ.range.index = Nat.card φ.ker := by
  have h4 := AddSubgroup.card_mul_index φ.ker
  have h5 := AddSubgroup.index_ker φ
  have h6 := AddSubgroup.card_mul_index φ.range
  have hr : 0 < Nat.card φ.range := Nat.card_pos
  rw [h5] at h4
  have : Nat.card φ.range * φ.range.index = Nat.card φ.range * Nat.card φ.ker := by
    rw [h6, ← h4, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hr this

lemma card_comap_eq {G : Type} [AddCommGroup G] [Finite G] (φ : G →+ G) (A : AddSubgroup G)
    (h : φ.range.relIndex A = φ.range.index) :
    Nat.card (A.comap φ) = Nat.card A := by
  have h1 := AddSubgroup.index_comap A φ
  have h2 := AddSubgroup.card_mul_index (A.comap φ)
  have h3 := AddSubgroup.relIndex_mul_card A φ.range
  have h4 := AddSubgroup.card_mul_index φ.ker
  have h5 := AddSubgroup.index_ker φ
  have h7 := AddSubgroup.relIndex_mul_card φ.range A
  have hj := index_range_eq φ
  rw [inf_comm] at h3
  rw [h, hj] at h7
  rw [h1] at h2
  rw [h5] at h4
  have hr : 0 < Nat.card φ.range := Nat.card_pos
  have hi : 0 < A.relIndex φ.range := by
    rcases Nat.eq_zero_or_pos (A.relIndex φ.range) with h0 | h0
    · rw [h0, zero_mul] at h3; omega
    · exact h0
  rw [← h7]
  apply Nat.eq_of_mul_eq_mul_right hi
  rw [h2, ← h4, ← h3]
  ring

lemma card_filter_eq {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] (φ : G →+ G)
    (A : AddSubgroup G) [DecidablePred (· ∈ A)] (q t0 : G) (ht0 : q + φ t0 ∈ A)
    (h : φ.range.relIndex A = φ.range.index) :
    (Finset.univ.filter (fun t : G => q + φ t ∈ A)).card = Nat.card A := by
  rw [← card_comap_eq φ A h]
  have e : (Finset.univ.filter (fun t : G => q + φ t ∈ A)) =
      (Finset.univ.filter (fun s : G => φ s ∈ A)).map (addLeftEmbedding t0) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      addLeftEmbedding_apply]
    constructor
    · intro ht
      refine ⟨t - t0, ?_, by abel⟩
      have : φ (t - t0) = (q + φ t) - (q + φ t0) := by rw [map_sub]; abel
      rw [this]; exact A.sub_mem ht ht0
    · rintro ⟨s, hs, rfl⟩
      rw [map_add, ← add_assoc]; exact A.add_mem ht0 hs
  rw [e, Finset.card_map]
  show _ = Nat.card {s // φ s ∈ A}
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma aniso {F : Type} [Field F] (b : F) (hb : ∀ X : F, X ^ 2 + b * X + 1 ≠ 0) (x : F × F)
    (hQ : x.1 ^ 2 + b * x.1 * x.2 + x.2 ^ 2 = 0) : x = 0 := by
  by_cases h2 : x.2 = 0
  · rw [h2] at hQ
    have : x.1 = 0 := by simpa using hQ
    exact Prod.ext this h2
  · exfalso
    apply hb (x.1 / x.2)
    have key : (x.1 / x.2) ^ 2 + b * (x.1 / x.2) + 1 =
        (x.1 ^ 2 + b * x.1 * x.2 + x.2 ^ 2) / x.2 ^ 2 := by
      field_simp
    rw [key, hQ, zero_div]

end PEqualNP.Outside.L_meta_664

theorem PEqualNP.Outside.L_meta_664 : ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b : F), (∀ X : F, X ^ 2 + b * X + 1 ≠ 0) → ∀ (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F), d ≠ 0 → ((Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = 0 ∨ (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) ∧ (p = 0 → (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) := by
  intro F _ _ _ _ b hb A _ p d hd
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨q, hq⟩ : ∃ q : F, q = p.1 ^ 2 + b * p.1 * p.2 + p.2 ^ 2 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : F, c = b * (p.1 * d.2 + p.2 * d.1) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : F, e = d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2 := ⟨_, rfl⟩
  have he0 : e ≠ 0 := fun h => hd (PEqualNP.Outside.L_meta_664.aniso b hb d (he ▸ h))
  let φ : F →+ F :=
    { toFun := fun t => e * t ^ 2 + c * t
      map_zero' := by simp
      map_add' := fun s t => by linear_combination (e * s * t) * h2 }
  have hφ : ∀ t, φ t = e * t ^ 2 + c * t := fun t => rfl
  have hfun : ∀ t : F, (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2
      = q + φ t := by
    intro t
    rw [hφ, hq, hc, he]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination (t * (p.1 * d.1 + p.2 * d.2)) * h2
  have key : ∀ t0, q + φ t0 ∈ A →
      (Finset.univ.filter (fun t : F => q + φ t ∈ A)).card = Nat.card A := by
    intro t0 ht0
    apply PEqualNP.Outside.L_meta_664.card_filter_eq φ A q t0 ht0
    by_cases hc0 : c = 0
    · have inj : Function.Injective φ := by
        rw [injective_iff_map_eq_zero]
        intro t ht
        rw [hφ, hc0, zero_mul, add_zero] at ht
        have : t ^ 2 = 0 := (mul_eq_zero.mp ht).resolve_left he0
        exact pow_eq_zero_iff (two_ne_zero) |>.mp this
      have htop : φ.range = ⊤ := AddMonoidHom.range_eq_top.mpr (Finite.surjective_of_injective inj)
      rw [htop, AddSubgroup.relIndex_top_left, AddSubgroup.index_top]
    ·
      have hq_nr : q ∉ φ.range := by
        rintro ⟨s, hs⟩
        have h0 : (p + s • d).1 ^ 2 + b * (p + s • d).1 * (p + s • d).2 + (p + s • d).2 ^ 2 = 0 := by
          rw [hfun, hs]; linear_combination q * h2
        have hpd := PEqualNP.Outside.L_meta_664.aniso b hb _ h0
        have e1 : p.1 = -(s * d.1) := by
          have := congrArg Prod.fst hpd
          simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_zero] at this
          linear_combination this
        have e2 : p.2 = -(s * d.2) := by
          have := congrArg Prod.snd hpd
          simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_zero] at this
          linear_combination this
        apply hc0
        rw [hc, e1, e2]
        linear_combination (-(b * s * d.1 * d.2)) * h2
      have hker : Nat.card φ.ker ≤ 2 := by
        have sub : (φ.ker : Set F) ⊆ {0, -(c / e)} := by
          intro t ht
          have ht' : e * t ^ 2 + c * t = 0 := ht
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          by_cases t0 : t = 0
          · left; exact t0
          · right
            have : e * t + c = 0 := by
              have : t * (e * t + c) = 0 := by linear_combination ht'
              exact (mul_eq_zero.mp this).resolve_left t0
            field_simp
            linear_combination this
        calc Nat.card φ.ker = (φ.ker : Set F).ncard := Nat.card_coe_set_eq _
          _ ≤ ({0, -(c / e)} : Set F).ncard := Set.ncard_le_ncard sub (Set.toFinite _)
          _ ≤ ({-(c / e)} : Set F).ncard + 1 := Set.ncard_insert_le _ _
          _ = 2 := by rw [Set.ncard_singleton]
      have hidx : φ.range.index = 2 := by
        have hne1 : φ.range.index ≠ 1 := by
          rw [Ne, AddSubgroup.index_eq_one]
          intro h; exact hq_nr (h ▸ AddSubgroup.mem_top q)
        have hne0 : φ.range.index ≠ 0 := by
          intro h0
          have := AddSubgroup.card_mul_index φ.range
          rw [h0, mul_zero] at this
          exact (Nat.card_pos (α := F)).ne this
        have := PEqualNP.Outside.L_meta_664.index_range_eq φ
        omega
      rw [hidx]
      have hdvd : φ.range.relIndex A ∣ 2 := hidx ▸ AddSubgroup.relIndex_dvd_index_of_normal φ.range A
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exfalso
        rw [AddSubgroup.relIndex_eq_one] at h1
        apply hq_nr
        obtain ⟨s, hs⟩ := h1 ht0
        refine ⟨s - t0, ?_⟩
        rw [map_sub, hs]; abel
      · exact h1
  simp only [hfun]
  refine ⟨?_, ?_⟩
  · rcases Finset.eq_empty_or_nonempty (Finset.univ.filter (fun t : F => q + φ t ∈ A)) with h | h
    · left; rw [h, Finset.card_empty]
    · right
      obtain ⟨t0, ht0⟩ := h
      exact key t0 (Finset.mem_filter.mp ht0).2
  · intro hp
    apply key 0
    rw [hq, hp, map_zero]
    simp
