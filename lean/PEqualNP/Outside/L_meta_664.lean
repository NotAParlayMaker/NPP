import Mathlib
import PEqualNP.Defs

section LMeta664Aux

private lemma two_eq_zero_char2 (F : Type) [Ring F] [CharP F 2] : (2 : F) = 0 := by
  simpa using CharP.cast_eq_zero F 2

private lemma char2_add_self {F : Type} [Ring F] [CharP F 2] (x : F) : x + x = 0 := by
  calc x + x = (2 : F) * x := (two_mul x).symm
    _ = 0 * x := by rw [two_eq_zero_char2 F]
    _ = 0 := zero_mul x

private lemma char2_add_eq_zero {F : Type} [Ring F] [CharP F 2] {a b : F} (h : a + b = 0) :
    a = b := by
  calc a = a + (a + b) := by rw [h, add_zero]
    _ = (a + a) + b := (add_assoc a a b).symm
    _ = 0 + b := by rw [char2_add_self]
    _ = b := zero_add b

private lemma b_ne_zero {F : Type} [Field F] [CharP F 2] (b : F)
    (hirr : ∀ X : F, X ^ 2 + b * X + 1 ≠ 0) : b ≠ 0 := by
  intro hb
  apply hirr 1
  rw [hb]
  calc (1 : F) ^ 2 + 0 * 1 + 1 = 1 + 1 := by ring
    _ = 0 := char2_add_self 1

private lemma qform_ne_zero {F : Type} [Field F] [CharP F 2] (b : F)
    (hirr : ∀ X : F, X ^ 2 + b * X + 1 ≠ 0) (d : F × F) (hd : d ≠ 0) :
    d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2 ≠ 0 := by
  rcases d with ⟨d1, d2⟩
  by_cases hd2 : d2 = 0
  · subst hd2
    have hd1 : d1 ≠ 0 := fun h => hd (Prod.ext h rfl)
    simpa [pow_two] using mul_ne_zero hd1 hd1
  · intro hq
    apply hirr (d1 / d2)
    have hmul : d2 ^ 2 * ((d1 / d2) ^ 2 + b * (d1 / d2) + 1) =
        d1 ^ 2 + b * d1 * d2 + d2 ^ 2 := by
      have h1 : d2 ^ 2 * (d1 / d2) ^ 2 = d1 ^ 2 := by
        rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero 2 hd2)]
      have h2 : d2 ^ 2 * (b * (d1 / d2)) = b * d1 * d2 := by
        calc d2 ^ 2 * (b * (d1 / d2)) = b * d2 * (d2 * (d1 / d2)) := by ring
          _ = b * d2 * d1 := by rw [mul_div_cancel₀ _ hd2]
          _ = b * d1 * d2 := by ring
      calc d2 ^ 2 * ((d1 / d2) ^ 2 + b * (d1 / d2) + 1)
          = d2 ^ 2 * (d1 / d2) ^ 2 + d2 ^ 2 * (b * (d1 / d2)) + d2 ^ 2 := by ring
        _ = d1 ^ 2 + b * d1 * d2 + d2 ^ 2 := by rw [h1, h2]
    rw [hq] at hmul
    exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 2 hd2)

private lemma c0_not_mem_range {F : Type} [Field F] [CharP F 2] (b β : F)
    (hirr : ∀ X : F, X ^ 2 + b * X + 1 ≠ 0) (hβ : β ≠ 0) :
    (β / b) ^ 2 ∉ Set.range (fun s : F => s ^ 2 + β * s) := by
  rintro ⟨s, hs⟩
  dsimp only at hs
  have hb : b ≠ 0 := b_ne_zero b hirr
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs
    have hsq : (β / b) ^ 2 = 0 := by
      calc (β / b) ^ 2 = 0 ^ 2 + β * 0 := hs.symm
        _ = 0 := by ring
    rcases div_eq_zero_iff.mp (sq_eq_zero_iff.mp hsq) with h1 | h2
    · exact hβ h1
    · exact hb h2
  have hbs : b * s ≠ 0 := mul_ne_zero hb hs0
  apply hirr (β / (b * s))
  have h1 : b ^ 2 * s ^ 2 * ((β / (b * s)) ^ 2 + b * (β / (b * s)) + 1) =
      b ^ 2 * (s ^ 2 + β * s) + β ^ 2 := by
    have ha : b ^ 2 * s ^ 2 * (β / (b * s)) ^ 2 = β ^ 2 := by
      calc b ^ 2 * s ^ 2 * (β / (b * s)) ^ 2
          = (b * s) ^ 2 * (β / (b * s)) ^ 2 := by ring
        _ = β ^ 2 := by rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero 2 hbs)]
    have hc : b ^ 2 * s ^ 2 * (b * (β / (b * s))) = b ^ 2 * (β * s) := by
      calc b ^ 2 * s ^ 2 * (b * (β / (b * s)))
          = b ^ 2 * s * ((b * s) * (β / (b * s))) := by ring
        _ = b ^ 2 * s * β := by rw [mul_div_cancel₀ _ hbs]
        _ = b ^ 2 * (β * s) := by ring
    calc b ^ 2 * s ^ 2 * ((β / (b * s)) ^ 2 + b * (β / (b * s)) + 1)
        = b ^ 2 * s ^ 2 * (β / (b * s)) ^ 2 + b ^ 2 * s ^ 2 * (b * (β / (b * s))) +
            b ^ 2 * s ^ 2 := by ring
      _ = β ^ 2 + b ^ 2 * (β * s) + b ^ 2 * s ^ 2 := by rw [ha, hc]
      _ = b ^ 2 * (s ^ 2 + β * s) + β ^ 2 := by ring
  rw [hs] at h1
  have h2 : b ^ 2 * (β / b) ^ 2 + β ^ 2 = 0 := by
    have hcancel : b ^ 2 * (β / b) ^ 2 = β ^ 2 := by
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero 2 hb)]
    rw [hcancel]
    exact char2_add_self (β ^ 2)
  rw [h2] at h1
  exact (mul_eq_zero.mp h1).resolve_left (mul_ne_zero (pow_ne_zero 2 hb) (pow_ne_zero 2 hs0))

private def artinSchreierHom (F : Type) [Field F] [CharP F 2] (β : F) : F →+ F where
  toFun s := s ^ 2 + β * s
  map_zero' := by simp
  map_add' x y := by
    have h2 : (2 : F) = 0 := two_eq_zero_char2 F
    calc (x + y) ^ 2 + β * (x + y)
        = (x ^ 2 + β * x) + (y ^ 2 + β * y) + (2 : F) * (x * y) := by ring
      _ = (x ^ 2 + β * x) + (y ^ 2 + β * y) := by rw [h2, zero_mul, add_zero]

private lemma qform_shift_char2 {F : Type} [Field F] [CharP F 2] (b : F) (p d : F × F)
    (t0 s : F) :
    (p.1 + (t0 + s) * d.1) ^ 2 + b * (p.1 + (t0 + s) * d.1) * (p.2 + (t0 + s) * d.2) +
      (p.2 + (t0 + s) * d.2) ^ 2 =
    ((p.1 + t0 * d.1) ^ 2 + b * (p.1 + t0 * d.1) * (p.2 + t0 * d.2) +
      (p.2 + t0 * d.2) ^ 2) +
    b * (p.1 * d.2 + p.2 * d.1) * s +
    (d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2) * s ^ 2 := by
  apply sub_eq_zero.mp
  have hfactor :
      ((p.1 + (t0 + s) * d.1) ^ 2 + b * (p.1 + (t0 + s) * d.1) * (p.2 + (t0 + s) * d.2) +
        (p.2 + (t0 + s) * d.2) ^ 2) -
      (((p.1 + t0 * d.1) ^ 2 + b * (p.1 + t0 * d.1) * (p.2 + t0 * d.2) +
        (p.2 + t0 * d.2) ^ 2) +
       b * (p.1 * d.2 + p.2 * d.1) * s +
       (d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2) * s ^ 2) =
      (2 : F) * (b * d.1 * d.2 * s * t0 + d.1 ^ 2 * s * t0 + d.1 * p.1 * s +
        d.2 ^ 2 * s * t0 + d.2 * p.2 * s) := by
    ring
  rw [hfactor, two_eq_zero_char2 F, zero_mul]

private lemma qform_at_t0_char2 {F : Type} [Field F] [CharP F 2] (b : F) (p d : F × F)
    (hqd : d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2 ≠ 0) :
    let qd := d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2
    let u := p.1 * d.2 + p.2 * d.1
    let t0 := (p.1 * d.1 + p.2 * d.2 + b * p.1 * d.2) / qd
    ((p.1 + t0 * d.1) ^ 2 + b * (p.1 + t0 * d.1) * (p.2 + t0 * d.2) +
      (p.2 + t0 * d.2) ^ 2) / qd = (u / qd) ^ 2 := by
  intro qd u t0
  dsimp only [qd, u, t0]
  set D := d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2
  set N := p.1 * d.1 + p.2 * d.2 + b * p.1 * d.2
  have hD : D ≠ 0 := hqd
  apply mul_left_cancel₀ (pow_ne_zero 3 hD)
  have hx : D * (p.1 + N / D * d.1) = D * p.1 + N * d.1 := by
    calc D * (p.1 + N / D * d.1) = D * p.1 + (D * (N / D)) * d.1 := by ring
      _ = D * p.1 + N * d.1 := by rw [mul_div_cancel₀ N hD]
  have hy : D * (p.2 + N / D * d.2) = D * p.2 + N * d.2 := by
    calc D * (p.2 + N / D * d.2) = D * p.2 + (D * (N / D)) * d.2 := by ring
      _ = D * p.2 + N * d.2 := by rw [mul_div_cancel₀ N hD]
  have hlhs : D ^ 3 *
      (((p.1 + N / D * d.1) ^ 2 + b * (p.1 + N / D * d.1) * (p.2 + N / D * d.2) +
        (p.2 + N / D * d.2) ^ 2) / D) =
      (D * p.1 + N * d.1) ^ 2 + b * (D * p.1 + N * d.1) * (D * p.2 + N * d.2) +
      (D * p.2 + N * d.2) ^ 2 := by
    calc D ^ 3 *
          (((p.1 + N / D * d.1) ^ 2 + b * (p.1 + N / D * d.1) * (p.2 + N / D * d.2) +
            (p.2 + N / D * d.2) ^ 2) / D)
        = D ^ 2 * (D * (((p.1 + N / D * d.1) ^ 2 +
            b * (p.1 + N / D * d.1) * (p.2 + N / D * d.2) +
            (p.2 + N / D * d.2) ^ 2) / D)) := by ring
      _ = D ^ 2 * ((p.1 + N / D * d.1) ^ 2 +
            b * (p.1 + N / D * d.1) * (p.2 + N / D * d.2) +
            (p.2 + N / D * d.2) ^ 2) := by rw [mul_div_cancel₀ _ hD]
      _ = (D * (p.1 + N / D * d.1)) ^ 2 +
            b * (D * (p.1 + N / D * d.1)) * (D * (p.2 + N / D * d.2)) +
            (D * (p.2 + N / D * d.2)) ^ 2 := by ring
      _ = (D * p.1 + N * d.1) ^ 2 + b * (D * p.1 + N * d.1) * (D * p.2 + N * d.2) +
            (D * p.2 + N * d.2) ^ 2 := by rw [hx, hy]
  have hrhs : D ^ 3 * ((p.1 * d.2 + p.2 * d.1) / D) ^ 2 =
      (p.1 * d.2 + p.2 * d.1) ^ 2 * D := by
    calc D ^ 3 * ((p.1 * d.2 + p.2 * d.1) / D) ^ 2
        = D * (D ^ 2 * ((p.1 * d.2 + p.2 * d.1) / D) ^ 2) := by ring
      _ = D * (p.1 * d.2 + p.2 * d.1) ^ 2 := by
          rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero 2 hD)]
      _ = (p.1 * d.2 + p.2 * d.1) ^ 2 * D := by ring
  rw [hlhs, hrhs]
  apply sub_eq_zero.mp
  have hfactor :
      ((D * p.1 + N * d.1) ^ 2 + b * (D * p.1 + N * d.1) * (D * p.2 + N * d.2) +
       (D * p.2 + N * d.2) ^ 2) -
      (p.1 * d.2 + p.2 * d.1) ^ 2 * D =
      (2 : F) *
      (b ^ 3 * d.1 ^ 2 * d.2 ^ 2 * p.1 * p.2 + b ^ 3 * d.1 * d.2 ^ 3 * p.1 ^ 2 +
       2 * b ^ 2 * d.1 ^ 3 * d.2 * p.1 * p.2 + 4 * b ^ 2 * d.1 ^ 2 * d.2 ^ 2 * p.1 ^ 2 +
       b ^ 2 * d.1 ^ 2 * d.2 ^ 2 * p.2 ^ 2 + 4 * b ^ 2 * d.1 * d.2 ^ 3 * p.1 * p.2 +
       b ^ 2 * d.2 ^ 4 * p.1 ^ 2 + b * d.1 ^ 4 * p.1 * p.2 +
       5 * b * d.1 ^ 3 * d.2 * p.1 ^ 2 + b * d.1 ^ 3 * d.2 * p.2 ^ 2 +
       6 * b * d.1 ^ 2 * d.2 ^ 2 * p.1 * p.2 + 3 * b * d.1 * d.2 ^ 3 * p.1 ^ 2 +
       3 * b * d.1 * d.2 ^ 3 * p.2 ^ 2 + 3 * b * d.2 ^ 4 * p.1 * p.2 +
       2 * d.1 ^ 4 * p.1 ^ 2 + 2 * d.1 ^ 3 * d.2 * p.1 * p.2 +
       2 * d.1 ^ 2 * d.2 ^ 2 * p.1 ^ 2 + 2 * d.1 ^ 2 * d.2 ^ 2 * p.2 ^ 2 +
       2 * d.1 * d.2 ^ 3 * p.1 * p.2 + 2 * d.2 ^ 4 * p.2 ^ 2) := by
    dsimp only [D, N]
    ring
  rw [hfactor, two_eq_zero_char2 F, zero_mul]

private lemma line_expand_char2 {F : Type} [Field F] [CharP F 2] (b : F) (p d : F × F)
    (hqd : d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2 ≠ 0) (s : F) :
    let qd := d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2
    let u := p.1 * d.2 + p.2 * d.1
    let t0 := (p.1 * d.1 + p.2 * d.2 + b * p.1 * d.2) / qd
    let β := b * u / qd
    let c0 := (u / qd) ^ 2
    ((p + (t0 + s) • d).1 ^ 2 + b * (p + (t0 + s) • d).1 * (p + (t0 + s) • d).2 +
      (p + (t0 + s) • d).2 ^ 2) / qd = s ^ 2 + β * s + c0 := by
  intro qd u t0 β c0
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.snd_add, Prod.smul_snd]
  rw [qform_shift_char2 b p d t0 s]
  have h0 : ((p.1 + t0 * d.1) ^ 2 + b * (p.1 + t0 * d.1) * (p.2 + t0 * d.2) +
      (p.2 + t0 * d.2) ^ 2) / qd = c0 := qform_at_t0_char2 b p d hqd
  calc (((p.1 + t0 * d.1) ^ 2 + b * (p.1 + t0 * d.1) * (p.2 + t0 * d.2) +
        (p.2 + t0 * d.2) ^ 2) + b * u * s + qd * s ^ 2) / qd
      = ((p.1 + t0 * d.1) ^ 2 + b * (p.1 + t0 * d.1) * (p.2 + t0 * d.2) +
          (p.2 + t0 * d.2) ^ 2) / qd + (b * u / qd) * s + (qd / qd) * s ^ 2 := by ring
    _ = c0 + β * s + 1 * s ^ 2 := by rw [h0, div_self hqd]
    _ = s ^ 2 + β * s + c0 := by ring

end LMeta664Aux

theorem PEqualNP.Outside.L_meta_664 :
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b : F),
    (∀ X : F, X ^ 2 + b * X + 1 ≠ 0) →
    ∀ (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F),
      d ≠ 0 →
      ((Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = 0 ∨
       (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) ∧
      (p = 0 → (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) := by
  intro F _ _ _ _ b hirr A _ p d hd
  have hqd : d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2 ≠ 0 := qform_ne_zero b hirr d hd
  set qd := d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2
  set u := p.1 * d.2 + p.2 * d.1
  set t0 := (p.1 * d.1 + p.2 * d.2 + b * p.1 * d.2) / qd
  set β := b * u / qd
  set c0 := (u / qd) ^ 2
  let Atilde : AddSubgroup F :=
    { carrier := { x | x * qd ∈ A }
      zero_mem' := by simp [A.zero_mem]
      add_mem' := fun hx hy => by simpa [add_mul] using A.add_mem hx hy
      neg_mem' := fun hx => by simpa [neg_mul] using A.neg_mem hx }
  letI : DecidablePred (· ∈ Atilde) := fun x => inferInstanceAs (Decidable (x * qd ∈ A))
  have hAtilde_card : Nat.card Atilde = Nat.card A := by
    refine Nat.card_congr (Equiv.ofBijective (fun x : Atilde => (⟨x.1 * qd, x.2⟩ : A)) ⟨?_, ?_⟩)
    · intro x y h
      ext
      exact mul_right_cancel₀ hqd (Subtype.ext_iff.mp h)
    · rintro ⟨a, ha⟩
      refine ⟨⟨a / qd, ?_⟩, ?_⟩
      · change (a / qd) * qd ∈ A
        rw [div_mul_cancel₀ a hqd]
        exact ha
      · ext
        exact div_mul_cancel₀ a hqd
  let S := Finset.univ.filter (fun s : F => artinSchreierHom F β s + c0 ∈ Atilde)
  have hcard_eq : (Finset.univ.filter (fun t : F =>
      (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = S.card := by
    symm
    refine Finset.card_bij (fun s _ => t0 + s) ?_ ?_ ?_
    · intro s hs
      dsimp only [S] at hs
      rw [Finset.mem_filter] at hs
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hexp := line_expand_char2 b p d hqd s
      dsimp only [artinSchreierHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hs hexp
      have hmul : ((p + (t0 + s) • d).1 ^ 2 + b * (p + (t0 + s) • d).1 * (p + (t0 + s) • d).2 +
          (p + (t0 + s) • d).2 ^ 2) = (s ^ 2 + β * s + c0) * qd := by
        rw [← hexp]
        exact (div_mul_cancel₀ _ hqd).symm
      rw [hmul]
      exact hs.2
    · intro s1 _ s2 _ h
      exact add_left_cancel h
    · intro t ht
      rw [Finset.mem_filter] at ht
      refine ⟨t - t0, ?_, add_sub_cancel t0 t⟩
      dsimp only [S]
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hexp := line_expand_char2 b p d hqd (t - t0)
      dsimp only [artinSchreierHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hexp ⊢
      rw [add_sub_cancel t0 t] at hexp
      change (((t - t0) ^ 2 + β * (t - t0) + c0) * qd) ∈ A
      rw [← hexp, div_mul_cancel₀ _ hqd]
      exact ht.2
  rw [hcard_eq, ← hAtilde_card]
  by_cases hβ : β = 0
  · have hu0 : u = 0 := by
      have hbu : b * u = 0 := (div_eq_zero_iff.mp hβ).resolve_right hqd
      exact (mul_eq_zero.mp hbu).resolve_left (b_ne_zero b hirr)
    have hc0 : c0 = 0 := by simp [c0, hu0]
    have hbij : Function.Bijective (artinSchreierHom F β) := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨?_, rfl⟩
      rw [injective_iff_map_eq_zero]
      intro s hs
      simp only [artinSchreierHom, hβ, zero_mul, add_zero, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        sq_eq_zero_iff] at hs
      exact hs
    have hScard : S.card = Nat.card Atilde := by
      rw [← Fintype.card_coe S, ← Nat.card_eq_fintype_card]
      refine Nat.card_congr ((Equiv.ofBijective _ hbij).subtypeEquiv (fun s => ?_))
      simp [S, hc0]
    exact ⟨Or.inr hScard, fun _ => hScard⟩
  · have hp_ne_zero : p ≠ 0 := by
      intro hp0
      apply hβ
      simp [β, u, hp0]
    refine ⟨?_, fun hp0 => absurd hp0 hp_ne_zero⟩
    let φ := artinSchreierHom F β
    letI : DecidablePred (· ∈ φ.range) :=
      fun y => decidable_of_iff (∃ x : F, φ x = y) AddMonoidHom.mem_range.symm
    letI : DecidablePred (· ∈ φ.ker) :=
      fun k => inferInstanceAs (Decidable (φ k = 0))
    have hker_set : (φ.ker : Set F) = ({0, β} : Set F) := by
      ext s
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, φ, artinSchreierHom,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hs
        have hfac : s * (s + β) = 0 := by
          calc s * (s + β) = s ^ 2 + β * s := by ring
            _ = 0 := hs
        rcases mul_eq_zero.mp hfac with rfl | h2
        · exact Or.inl rfl
        · exact Or.inr (char2_add_eq_zero h2)
      · rintro (rfl | rfl)
        · simp
        · calc β ^ 2 + β * β = β ^ 2 + β ^ 2 := by ring
            _ = 0 := char2_add_self _
    have hker_card : Nat.card φ.ker = 2 := by
      have hβ0 : (0 : F) ≠ β := Ne.symm hβ
      let eKer : φ.ker ≃ Bool :=
        { toFun := fun x => decide (x.1 = β)
          invFun := fun b => match b with
            | true => ⟨β, by
                rw [AddMonoidHom.mem_ker]
                dsimp only [φ, artinSchreierHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
                calc β ^ 2 + β * β = β ^ 2 + β ^ 2 := by ring
                  _ = 0 := char2_add_self _⟩
            | false => ⟨0, φ.ker.zero_mem⟩
          left_inv := fun x => by
            dsimp only
            have hx : x.1 ∈ ({0, β} : Set F) := hker_set ▸ x.2
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
            rcases hx with hx0 | hxβ
            · have hdf : decide (x.1 = β) = false := decide_eq_false (hx0 ▸ hβ0)
              rw [hdf]
              exact Subtype.ext hx0.symm
            · have hdt : decide (x.1 = β) = true := decide_eq_true hxβ
              rw [hdt]
              exact Subtype.ext hxβ.symm
          right_inv := fun b => by
            dsimp only
            cases b
            · simp [hβ0]
            · simp }
      rw [Nat.card_congr eKer]
      simp
    have hfiber : ∀ y ∈ φ.range, (Finset.univ.filter (fun s : F => φ s = y)).card = 2 := by
      rintro y ⟨s0, rfl⟩
      have heq : Finset.univ.filter (fun s : F => φ s = φ s0) =
          (Finset.univ.filter (fun k : F => k ∈ φ.ker)).image (fun k => s0 + k) := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
          AddMonoidHom.mem_ker]
        constructor
        · intro hs
          refine ⟨s - s0, ?_, add_sub_cancel s0 s⟩
          rw [map_sub, hs, sub_self]
        · rintro ⟨k, hk, rfl⟩
          rw [map_add, hk, add_zero]
      rw [heq, Finset.card_image_of_injective _ (add_right_injective s0)]
      rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← hker_card]
      refine Nat.card_congr (Equiv.subtypeEquivRight (fun k => ?_))
      simp
    let T := Finset.univ.filter (fun y : F => y ∈ φ.range ∧ y + c0 ∈ Atilde)
    have hScard_T : S.card = 2 * T.card := by
      have hbi : S = T.biUnion (fun y => Finset.univ.filter (fun s : F => φ s = y)) := by
        ext s
        simp only [S, T, φ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
          AddMonoidHom.mem_range]
        constructor
        · intro hs
          exact ⟨artinSchreierHom F β s, ⟨⟨s, rfl⟩, hs⟩, rfl⟩
        · rintro ⟨y, ⟨_, hy2⟩, rfl⟩
          exact hy2
      rw [hbi, Finset.card_biUnion]
      · rw [Finset.sum_congr rfl (fun y hy => hfiber y (Finset.mem_filter.mp hy).2.1)]
        simp [mul_comm]
      · intro y1 _ y2 _ hne
        exact Finset.disjoint_left.mpr fun s hs1 hs2 =>
          hne ((Finset.mem_filter.mp hs1).2.symm.trans (Finset.mem_filter.mp hs2).2)
    have hrange_index : φ.range.index = 2 := by
      have h1 : φ.range.index * Nat.card φ.range = Nat.card F :=
        AddSubgroup.index_mul_card φ.range
      have h2 : φ.ker.index * Nat.card φ.ker = Nat.card F :=
        AddSubgroup.index_mul_card φ.ker
      have h3 : φ.ker.index = Nat.card φ.range := by
        rw [AddSubgroup.index_eq_card]
        exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv
      rw [h3, hker_card, mul_comm] at h2
      have hpos : 0 < Nat.card φ.range := Nat.card_pos
      exact mul_right_cancel₀ hpos.ne' (h1.trans h2.symm)
    let K : AddSubgroup F := Atilde ⊓ φ.range
    by_cases hT : T.Nonempty
    · obtain ⟨y0, hy0⟩ := hT
      obtain ⟨_, hy0_rng, hy0_A⟩ := Finset.mem_filter.mp hy0
      have hnot_le : ¬ (Atilde ≤ φ.range) := by
        intro hle
        have hc0_rng : c0 ∈ φ.range := by
          have hsub : (y0 + c0) - y0 ∈ φ.range := φ.range.sub_mem (hle hy0_A) hy0_rng
          simpa using hsub
        have hc0_eq : c0 = (β / b) ^ 2 := by
          have hb : b ≠ 0 := b_ne_zero b hirr
          dsimp only [c0, β]
          rw [mul_div_assoc, mul_div_cancel_left₀ _ hb]
        obtain ⟨s, hs⟩ := hc0_rng
        exact c0_not_mem_range b β hirr hβ ⟨s, hs.trans hc0_eq⟩
      have hex_z : ∃ z, z ∈ Atilde ∧ z ∉ φ.range := by
        by_contra hall
        push_neg at hall
        exact hnot_le hall
      obtain ⟨z, hzA, hz_not_rng⟩ := hex_z
      have htwo_cosets : ∀ x : F, x ∈ φ.range ∨ x - z ∈ φ.range := by
        intro x
        letI : Fintype (F ⧸ φ.range) := Fintype.ofFinite _
        have hqcard : Fintype.card (F ⧸ φ.range) = 2 := by
          rw [← Nat.card_eq_fintype_card, ← AddSubgroup.index_eq_card, hrange_index]
        let qz : F ⧸ φ.range := QuotientAddGroup.mk z
        have hqz0 : qz ≠ 0 := by
          rw [ne_eq, QuotientAddGroup.eq_zero_iff]
          exact hz_not_rng
        have huniv : ({0, qz} : Finset (F ⧸ φ.range)) = Finset.univ := by
          apply Finset.eq_univ_of_card
          rw [Finset.card_pair hqz0.symm, hqcard]
        have hmem : (QuotientAddGroup.mk x : F ⧸ φ.range) ∈ ({0, qz} : Finset (F ⧸ φ.range)) := by
          rw [huniv]
          exact Finset.mem_univ _
        rcases Finset.mem_insert.mp hmem with h0 | h1
        · left
          rw [QuotientAddGroup.eq_zero_iff] at h0
          exact h0
        · right
          rw [Finset.mem_singleton] at h1
          have hrel : -x + z ∈ φ.range := QuotientAddGroup.eq.mp h1
          have hneg : -(-x + z) ∈ φ.range := φ.range.neg_mem hrel
          simpa [sub_eq_add_neg, add_comm] using hneg
      have hAtilde_2K : Nat.card Atilde = 2 * Nat.card K := by
        have hdisj : Disjoint (Set.range (fun k : K => (⟨k.1, (AddSubgroup.mem_inf.mp k.2).1⟩ : Atilde)))
            (Set.range (fun k : K => (⟨z + k.1, Atilde.add_mem hzA (AddSubgroup.mem_inf.mp k.2).1⟩ : Atilde))) := by
          rw [Set.disjoint_left]
          rintro _ ⟨k1, rfl⟩ ⟨k2, hk2⟩
          dsimp only at hk2
          have heq : z + k2.1 = k1.1 := Subtype.ext_iff.mp hk2
          have hz_rng : z ∈ φ.range := by
            have : k1.1 - k2.1 ∈ φ.range :=
              φ.range.sub_mem (AddSubgroup.mem_inf.mp k1.2).2 (AddSubgroup.mem_inf.mp k2.2).2
            rw [← heq, add_sub_cancel_right] at this
            exact this
          exact hz_not_rng hz_rng
        have hunion : (Set.range (fun k : K => (⟨k.1, (AddSubgroup.mem_inf.mp k.2).1⟩ : Atilde))) ∪
            (Set.range (fun k : K => (⟨z + k.1, Atilde.add_mem hzA (AddSubgroup.mem_inf.mp k.2).1⟩ : Atilde))) = Set.univ := by
          ext ⟨x, hxA⟩
          simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
          rcases htwo_cosets x with hxr | hxzr
          · exact Or.inl ⟨⟨x, AddSubgroup.mem_inf.mpr ⟨hxA, hxr⟩⟩, rfl⟩
          · refine Or.inr ⟨⟨x - z, AddSubgroup.mem_inf.mpr ⟨Atilde.sub_mem hxA hzA, hxzr⟩⟩, ?_⟩
            ext
            exact add_sub_cancel z x
        have hinj1 : Function.Injective (fun k : K => (⟨k.1, (AddSubgroup.mem_inf.mp k.2).1⟩ : Atilde)) := by
          intro k1 k2 h
          dsimp only at h
          exact Subtype.ext (Subtype.mk.inj h)
        have hinj2 : Function.Injective (fun k : K => (⟨z + k.1, Atilde.add_mem hzA (AddSubgroup.mem_inf.mp k.2).1⟩ : Atilde)) := by
          intro k1 k2 h
          dsimp only at h
          exact Subtype.ext (add_left_cancel (Subtype.mk.inj h))
        let e : K ⊕ K ≃ Atilde :=
          Equiv.ofBijective (Sum.elim (fun k : K => (⟨k.1, (AddSubgroup.mem_inf.mp k.2).1⟩ : Atilde))
            (fun k : K => (⟨z + k.1, Atilde.add_mem hzA (AddSubgroup.mem_inf.mp k.2).1⟩ : Atilde)))
            ⟨hinj1.sumElim hinj2 (fun k1 k2 h => Set.disjoint_left.mp hdisj ⟨k1, rfl⟩ ⟨k2, h.symm⟩),
             fun a => by
               have ha : a ∈ Set.univ := Set.mem_univ a
               rw [← hunion] at ha
               rcases ha with ⟨k, rfl⟩ | ⟨k, rfl⟩
               · exact ⟨Sum.inl k, rfl⟩
               · exact ⟨Sum.inr k, rfl⟩⟩
        rw [← Nat.card_congr e, Nat.card_sum, two_mul]
      have hT_card : T.card = Nat.card K := by
        rw [← Fintype.card_coe T, ← Nat.card_eq_fintype_card]
        refine Nat.card_congr (Equiv.ofBijective
          (fun y : T => (⟨y.1 - y0, AddSubgroup.mem_inf.mpr ⟨?_, ?_⟩⟩ : K)) ⟨?_, ?_⟩)
        · have hyA : y.1 + c0 ∈ Atilde := (Finset.mem_filter.mp y.2).2.2
          have hsub : (y.1 + c0) - (y0 + c0) ∈ Atilde := Atilde.sub_mem hyA hy0_A
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
        · exact φ.range.sub_mem (Finset.mem_filter.mp y.2).2.1 hy0_rng
        · intro y1 y2 h
          dsimp only at h
          exact Subtype.ext (sub_left_inj.mp (Subtype.ext_iff.mp h))
        · rintro ⟨k, hk⟩
          obtain ⟨hkA, hkrng⟩ := AddSubgroup.mem_inf.mp hk
          refine ⟨⟨y0 + k, ?_⟩, ?_⟩
          · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨φ.range.add_mem hy0_rng hkrng, ?_⟩
            have hadd : (y0 + c0) + k ∈ Atilde := Atilde.add_mem hy0_A hkA
            simpa [add_assoc, add_left_comm, add_comm] using hadd
          · ext
            simp
      right
      omega
    · left
      rw [Finset.not_nonempty_iff_eq_empty] at hT
      simp [hScard_T, hT]
