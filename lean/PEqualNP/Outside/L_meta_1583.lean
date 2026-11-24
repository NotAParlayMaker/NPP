import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1583

theorem modlem (N a : ℕ) (h : a < 2 * N) : a % N = if a < N then a else a - N := by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The next residue. -/
def s {N : ℕ} (hN : 0 < N) (z : Fin N) : Fin N := ⟨(z.val + 1) % N, Nat.mod_lt _ hN⟩

/-- The previous residue. -/
def r {N : ℕ} (hN : 0 < N) (z : Fin N) : Fin N :=
  if z.val = 0 then ⟨N - 1, by omega⟩ else ⟨z.val - 1, by have := z.isLt; omega⟩

theorem sval {N : ℕ} (hN : 0 < N) (z : Fin N) :
    (s hN z).val = if z.val + 1 < N then z.val + 1 else 0 := by
  have hz := z.isLt
  simp only [s]
  rw [modlem N _ (by omega)]
  split_ifs <;> omega

theorem rval {N : ℕ} (hN : 0 < N) (z : Fin N) :
    (r hN z).val = if z.val = 0 then N - 1 else z.val - 1 := by
  simp only [r]
  split_ifs <;> rfl

theorem rs {N : ℕ} (hN : 0 < N) (z : Fin N) : r hN (s hN z) = z := by
  have hz := z.isLt
  apply Fin.ext
  rw [rval, sval]
  have hN1 : N - 1 + 1 = N := Nat.sub_add_cancel hN
  split_ifs with h1 h2 h2
  all_goals first | omega | contradiction

theorem s_ne {N : ℕ} (hN : 0 < N) (h3 : 3 ≤ N) (z : Fin N) : s hN z ≠ z := by
  intro h
  have hz := z.isLt
  have := congrArg Fin.val h
  rw [sval] at this
  split_ifs at this <;> omega

theorem ss_ne {N : ℕ} (hN : 0 < N) (h3 : 3 ≤ N) (z : Fin N) : s hN (s hN z) ≠ z := by
  intro h
  have hz := z.isLt
  have := congrArg Fin.val h
  rw [sval, sval] at this
  split_ifs at this <;> omega

theorem r_ne {N : ℕ} (hN : 0 < N) (h3 : 3 ≤ N) (z : Fin N) : r hN z ≠ z := by
  intro h
  have hz := z.isLt
  have := congrArg Fin.val h
  rw [rval] at this
  split_ifs at this <;> omega

theorem rr_ne {N : ℕ} (hN : 0 < N) (h3 : 3 ≤ N) (z : Fin N) : r hN (r hN z) ≠ z := by
  intro h
  have hz := z.isLt
  have := congrArg Fin.val h
  rw [rval, rval] at this
  split_ifs at this <;> omega

theorem iter_val {N : ℕ} (hN : 0 < N) (z : Fin N) (k : ℕ) :
    ((s hN)^[k] z).val = (z.val + k) % N := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt z.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply', sval, ih]
    have hlt := Nat.mod_lt (z.val + k) hN
    have key : (z.val + (k + 1)) % N = ((z.val + k) % N + 1) % N := by
      have h := Nat.div_add_mod (z.val + k) N
      have e : z.val + (k + 1) = N * ((z.val + k) / N) + ((z.val + k) % N + 1) := by omega
      rw [e, Nat.mul_add_mod]
    rw [key]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h]
    · have h1 : (z.val + k) % N + 1 = N := by omega
      rw [h1, Nat.mod_self]

theorem reach {N : ℕ} (hN : 0 < N) (z z' : Fin N) : ∃ k : ℕ, (s hN)^[k] z = z' := by
  refine ⟨z'.val + (N - z.val), Fin.ext ?_⟩
  rw [iter_val]
  have h1 := z.isLt
  have h2 := z'.isLt
  rw [show z.val + (z'.val + (N - z.val)) = z'.val + N by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt h2]

end PEqualNP.Outside.L_meta_1583

open PEqualNP.Outside.L_meta_1583 in
theorem PEqualNP.Outside.L_meta_1583 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∃ sigma : Fin N → Fin N, (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧ (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y)) ∧
    ∀ (sigma : Fin N → Fin N) (x0 : Fin N) (B : Fin N → Fin N → Finset (Fin N)),
    (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧ (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y) → x0 ∈ T0 →
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ x ∈ T0, x ∈ L s → B s p = if p = x then (∅ : Finset (Fin N)) else {sigma x}) →
    (∀ s : Fin N, s ≠ i0 → ∀ r ∈ L i0 \ T0, r ∈ L s → ∀ p ∈ L s, B s p = {x0}) →
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, B s p ∩ L s = ∅ ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∧
      ∀ v ∈ L s, decide (v = p ∨ v ∈ B s p) = true ↔ v = p) ∧
    (∀ s s' : Fin N, s ≠ i0 → s' ≠ i0 → s ≠ s' → ¬ ((∃ p ∈ L s \ L s', (B s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, (B s' p ∩ L s).Nonempty))) := by
  classical
  intro q m N L i0 T0 _ hm3 _ _ _ hmeet _ hT0 hT0c
  have uniq : ∀ s : Fin N, s ≠ i0 → ∀ u ∈ L s, u ∈ L i0 → ∀ u' ∈ L s, u' ∈ L i0 → u = u' := by
    intro s hs u hu hu0 u' hu' hu0'
    exact Finset.card_le_one.1 (hmeet s i0 hs).le u (Finset.mem_inter.2 ⟨hu, hu0⟩) u'
      (Finset.mem_inter.2 ⟨hu', hu0'⟩)
  -- a line through a point of the base line off `T0` holds no point of `T0`
  have now : ∀ s : Fin N, s ≠ i0 → ∀ r ∈ L i0 \ T0, r ∈ L s → ∀ v ∈ T0, v ∉ L s := by
    intro s hs r hr hrs v hv hvs
    rw [Finset.mem_sdiff] at hr
    exact hr.2 ((uniq s hs v hvs (hT0 hv) r hrs hr.1) ▸ hv)
  have types : ∀ s : Fin N, s ≠ i0 → (∃ x ∈ T0, x ∈ L s) ∨ ∃ r ∈ L i0 \ T0, r ∈ L s := by
    intro s hs
    obtain ⟨z, hz⟩ := Finset.card_eq_one.1 (hmeet s i0 hs)
    have hzm : z ∈ L s ∩ L i0 := by rw [hz]; simp
    obtain ⟨hzs, hz0⟩ := Finset.mem_inter.1 hzm
    by_cases h : z ∈ T0
    · exact Or.inl ⟨z, h, hzs⟩
    · exact Or.inr ⟨z, Finset.mem_sdiff.2 ⟨hz0, h⟩, hzs⟩
  refine ⟨?_, ?_⟩
  · have hmpos : 0 < m := by omega
    let e : T0 ≃ Fin m := Finset.equivFinOfCardEq hT0c
    let sigma : Fin N → Fin N := fun v =>
      if h : v ∈ T0 then ((e.symm (s hmpos (e ⟨v, h⟩)) : T0) : Fin N) else v
    have hs1 : ∀ (v : Fin N) (h : v ∈ T0),
        sigma v = ((e.symm (s hmpos (e ⟨v, h⟩)) : T0) : Fin N) := by
      intro v h; simp only [sigma]; rw [dif_pos h]
    have hmem : ∀ v ∈ T0, sigma v ∈ T0 := by
      intro v h; rw [hs1 v h]; exact (e.symm _).2
    have hcode : ∀ (v : Fin N) (h : v ∈ T0), e ⟨sigma v, hmem v h⟩ = s hmpos (e ⟨v, h⟩) := by
      intro v h
      have : (⟨sigma v, hmem v h⟩ : T0) = e.symm (s hmpos (e ⟨v, h⟩)) := Subtype.ext (hs1 v h)
      rw [this]; simp
    have hiter : ∀ (k : ℕ) (v : Fin N) (h : v ∈ T0),
        sigma^[k] v = ((e.symm ((s hmpos)^[k] (e ⟨v, h⟩)) : T0) : Fin N) := by
      intro k
      induction k with
      | zero => intro v h; simp
      | succ k ih =>
        intro v h
        rw [Function.iterate_succ_apply, ih (sigma v) (hmem v h), hcode v h,
          Function.iterate_succ_apply]
    refine ⟨sigma, hmem, ?_, ?_⟩
    · intro x hx y hy hxy
      have hx' : x ∈ T0 := hx
      have hy' : y ∈ T0 := hy
      have h1 : e ⟨sigma x, hmem x hx'⟩ = e ⟨sigma y, hmem y hy'⟩ := by
        congr 1; exact Subtype.ext hxy
      rw [hcode x hx', hcode y hy'] at h1
      have h2 := congrArg (r hmpos) h1
      rw [rs, rs] at h2
      exact congrArg Subtype.val (e.injective h2)
    · intro x hx y hy
      obtain ⟨k, hk⟩ := reach hmpos (e ⟨x, hx⟩) (e ⟨y, hy⟩)
      refine ⟨k, ?_⟩
      rw [hiter k x hx, hk]; simp
  · rintro sigma x0 B ⟨hmap, _, htrans⟩ hx0 hB1 hB2
    -- a point of `T0` outside two given points
    have third : ∀ a b : Fin N, ∃ y ∈ T0, y ≠ a ∧ y ≠ b := by
      intro a b
      have hc : 1 ≤ ((T0.erase a).erase b).card := by
        have h1 := Finset.pred_card_le_card_erase (s := T0) (a := a)
        have h2 := Finset.pred_card_le_card_erase (s := T0.erase a) (a := b)
        omega
      obtain ⟨y, hy⟩ := Finset.card_pos.1 hc
      simp only [Finset.mem_erase] at hy
      exact ⟨y, hy.2.2, hy.2.1, hy.1⟩
    have hno : ∀ x ∈ T0, sigma x ≠ x ∧ sigma (sigma x) ≠ x := by
      intro x hx
      constructor
      · intro hfix
        obtain ⟨y, hy, hyx, _⟩ := third x x
        obtain ⟨k, hk⟩ := htrans x hx y hy
        rw [Function.iterate_fixed hfix] at hk
        exact hyx hk.symm
      · intro h2
        obtain ⟨y, hy, hyx, hys⟩ := third x (sigma x)
        obtain ⟨k, hk⟩ := htrans x hx y hy
        have hall : ∀ k : ℕ, sigma^[k] x = x ∨ sigma^[k] x = sigma x := by
          intro k
          induction k with
          | zero => left; rfl
          | succ k ih =>
            rw [Function.iterate_succ_apply']
            rcases ih with h | h
            · right; rw [h]
            · left; rw [h, h2]
        rcases hall k with h | h
        · exact hyx (hk.symm.trans h)
        · exact hys (hk.symm.trans h)
    have memB : ∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ v ∈ B s p,
        v ∈ T0 ∧ v ∉ L s ∧ ((∃ x ∈ T0, x ∈ L s ∧ v = sigma x) ∨ ∃ r ∈ L i0 \ T0, r ∈ L s) := by
      intro s hs p hp v hv
      rcases types s hs with ⟨x, hx, hxs⟩ | ⟨r, hr, hrs⟩
      · rw [hB1 s hs p hp x hx hxs] at hv
        by_cases hpx : p = x
        · rw [if_pos hpx] at hv; simp at hv
        · rw [if_neg hpx, Finset.mem_singleton] at hv
          subst hv
          refine ⟨hmap x hx, fun hin => ?_, Or.inl ⟨x, hx, hxs, rfl⟩⟩
          exact (hno x hx).1 (uniq s hs _ hin (hT0 (hmap x hx)) x hxs (hT0 hx))
      · rw [hB2 s hs r hr hrs p hp, Finset.mem_singleton] at hv
        subst hv
        exact ⟨hx0, now s hs r hr hrs _ hx0, Or.inr ⟨r, hr, hrs⟩⟩
    constructor
    · intro s hs p hp
      have hdisj : B s p ∩ L s = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro v hv
        rw [Finset.mem_inter] at hv
        exact (memB s hs p hp v hv.1).2.1 hv.2
      refine ⟨hdisj, ?_, ?_⟩
      · left
        rcases types s hs with ⟨x, hx, hxs⟩ | ⟨r, hr, hrs⟩
        · by_cases hpx : p = x
          · exact ⟨x, hx, by simp [hpx]⟩
          · refine ⟨sigma x, hmap x hx, ?_⟩
            rw [hB1 s hs p hp x hx hxs, if_neg hpx]; simp
        · refine ⟨x0, hx0, ?_⟩
          rw [hB2 s hs r hr hrs p hp]; simp
      · intro v hv
        constructor
        · intro h
          rcases of_decide_eq_true h with h | h
          · exact h
          · exact absurd hv (memB s hs p hp v h).2.1
        · intro h; simp [h]
    · rintro s s' hs hs' hss ⟨⟨p, hp, v, hv⟩, ⟨p', hp', v', hv'⟩⟩
      rw [Finset.mem_sdiff] at hp hp'
      rw [Finset.mem_inter] at hv hv'
      obtain ⟨hvT, _, hk⟩ := memB s hs p hp.1 v hv.1
      obtain ⟨hvT', _, hk'⟩ := memB s' hs' p' hp'.1 v' hv'.1
      rcases hk with ⟨x, hx, hxs, rfl⟩ | ⟨r, hr, hrs⟩
      · rcases hk' with ⟨x', hx', hxs', rfl⟩ | ⟨r', hr', hrs'⟩
        · have e1 : sigma x = x' := uniq s' hs' _ hv.2 (hT0 hvT) x' hxs' (hT0 hx')
          have e2 : sigma x' = x := uniq s hs _ hv'.2 (hT0 hvT') x hxs (hT0 hx)
          exact (hno x hx).2 (by rw [e1, e2])
        · exact now s' hs' r' hr' hrs' _ hvT hv.2
      · exact now s hs r hr hrs _ hvT' hv'.2
