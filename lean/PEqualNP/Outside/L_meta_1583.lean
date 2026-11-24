import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1583

lemma cycle_exists {α : Type} [Fintype α] [DecidableEq α] (T : Finset α) :
    ∃ f : α → α, (∀ x ∈ T, f x ∈ T) ∧ Set.InjOn f ↑T ∧
      (∀ x ∈ T, ∀ y ∈ T, ∃ k : ℕ, f^[k] x = y) := by
  obtain ⟨f, hf, _⟩ := T.exists_cycleOn
  refine ⟨f, hf.1.1, hf.1.2.1, ?_⟩
  intro x hx y hy
  obtain ⟨k, _, hk⟩ := hf.exists_pow_eq hx hy
  exact ⟨k, by simpa only [Equiv.Perm.coe_pow] using hk⟩

lemma no_two_cycle {α : Type} [DecidableEq α] (T : Finset α) (f : α → α)
    (hT : 3 ≤ T.card)
    (ht : ∀ x ∈ T, ∀ y ∈ T, ∃ k : ℕ, f^[k] x = y)
    (x : α) (hx : x ∈ T) : f (f x) ≠ x := by
  intro h2
  have ho : ∀ k : ℕ, f^[k] x = x ∨ f^[k] x = f x := by
    intro k
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · exact Or.inr (congrArg f h)
      · exact Or.inl ((congrArg f h).trans h2)
  have hs : T ⊆ {x, f x} := by
    intro y hy
    obtain ⟨k, hk⟩ := ht x hx y hy
    rcases ho k with h | h <;> simp [← hk, h]
  have hc := Finset.card_le_card hs
  have hp : ({x, f x} : Finset α).card ≤ 2 := by
    rcases Finset.card_pair_eq_one_or_two (a := x) (b := f x) with h | h <;> omega
  omega

lemma no_fixed {α : Type} [DecidableEq α] (T : Finset α) (f : α → α)
    (hT : 3 ≤ T.card)
    (ht : ∀ x ∈ T, ∀ y ∈ T, ∃ k : ℕ, f^[k] x = y)
    (x : α) (hx : x ∈ T) : f x ≠ x := by
  intro h
  apply no_two_cycle T f hT ht x hx
  rw [h, h]

lemma line_meet {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 s : Fin N)
    (h : (L s ∩ L i0).card = 1) :
    ∃ x, x ∈ L i0 ∧ x ∈ L s ∧ ∀ y, y ∈ L i0 → y ∈ L s → y = x := by
  obtain ⟨x, he⟩ := Finset.card_eq_one.mp h
  have hx : x ∈ L s ∩ L i0 := by rw [he]; simp
  refine ⟨x, (Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hx).1, ?_⟩
  intro y hy0 hys
  have hy : y ∈ L s ∩ L i0 := Finset.mem_inter.mpr ⟨hys, hy0⟩
  simpa [he] using hy

def marker {α : Type} [DecidableEq α] (T : Finset α) (sigma : α → α) (x0 a : α) : α :=
  if a ∈ T then sigma a else x0

def base {α : Type} [DecidableEq α] (T : Finset α) (sigma : α → α) (x0 a p : α) : Finset α :=
  if a ∈ T then if p = a then ∅ else {sigma a} else {x0}

lemma base_mem {α : Type} [DecidableEq α] (T : Finset α) (sigma : α → α)
    (x0 a p v : α) (h : v ∈ base T sigma x0 a p) : v = marker T sigma x0 a := by
  by_cases ha : a ∈ T <;> by_cases hp : p = a <;> simp_all [base, marker]

lemma marker_mem {α : Type} [DecidableEq α] (T : Finset α) (sigma : α → α)
    (x0 : α) (hx0 : x0 ∈ T) (hs : ∀ x ∈ T, sigma x ∈ T) (a : α) :
    marker T sigma x0 a ∈ T := by
  unfold marker
  split_ifs with h
  · exact hs a h
  · exact hx0

lemma base_hits {α : Type} [DecidableEq α] (T : Finset α) (sigma : α → α)
    (x0 : α) (hx0 : x0 ∈ T) (hs : ∀ x ∈ T, sigma x ∈ T) (a p : α) :
    ∃ v ∈ T, v = p ∨ v ∈ base T sigma x0 a p := by
  by_cases ha : a ∈ T
  · by_cases hp : p = a
    · exact ⟨a, ha, Or.inl hp.symm⟩
    · exact ⟨sigma a, hs a ha, Or.inr (by simp [base, ha, hp])⟩
  · exact ⟨x0, hx0, Or.inr (by simp [base, ha])⟩

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
  intro q m N L i0 T0 _ hm _ _ _ hlines _ hT hcard
  constructor
  · exact cycle_exists T0
  · intro sigma x0 B hsig hx0 hB hR
    obtain ⟨hsigma, hinj, htrans⟩ := hsig
    have hsize : 3 ≤ T0.card := by omega
    have hnf := no_fixed T0 sigma hsize htrans
    have hn2 := no_two_cycle T0 sigma hsize htrans
    have hdata : ∀ s : Fin N, s ≠ i0 → ∃ a : Fin N,
        a ∈ L i0 ∧ a ∈ L s ∧
        (∀ v, v ∈ L i0 → v ∈ L s → v = a) ∧
        ∀ p ∈ L s, B s p = base T0 sigma x0 a p := by
      intro s hs
      obtain ⟨a, ha0, has, hau⟩ := line_meet L i0 s (hlines s i0 hs)
      refine ⟨a, ha0, has, hau, ?_⟩
      intro p hp
      by_cases ha : a ∈ T0
      · simpa only [base, ite_eq_left ha] using hB s hs p hp a ha has
      · have har : a ∈ L i0 \ T0 := Finset.mem_sdiff.mpr ⟨ha0, ha⟩
        simpa only [base, ite_eq_right ha] using hR s hs a har has p hp
    have hmk := marker_mem T0 sigma x0 hx0 hsigma
    constructor
    · intro s hs p hp
      obtain ⟨a, ha0, has, hau, hb⟩ := hdata s hs
      have hmnot : marker T0 sigma x0 a ∉ L s := by
        intro hm
        have heq := hau _ (hT (hmk a)) hm
        by_cases ha : a ∈ T0
        · exact hnf a ha (by simpa [marker, ha] using heq)
        · have hax : x0 = a := by simpa [marker, ha] using heq
          exact ha (hax ▸ hx0)
      have hout : ∀ v ∈ B s p, v ∉ L s := by
        intro v hv
        rw [hb p hp] at hv
        rw [base_mem T0 sigma x0 a p v hv]
        exact hmnot
      refine ⟨?_, ?_, ?_⟩
      · apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        exact hout v (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2
      · left
        obtain ⟨v, hv, hvp⟩ := base_hits T0 sigma x0 hx0 hsigma a p
        refine ⟨v, hv, ?_⟩
        simp only [decide_eq_true_eq]
        rwa [hb p hp]
      · intro v hv
        simp only [decide_eq_true_eq]
        constructor
        · rintro (heq | hm)
          · exact heq
          · exact False.elim (hout v hm hv)
        · exact Or.inl
    · intro s s' hs hs' hss hconf
      obtain ⟨a, ha0, has, hau, hb⟩ := hdata s hs
      obtain ⟨a', ha0', has', hau', hb'⟩ := hdata s' hs'
      obtain ⟨⟨p, hp, v, hv⟩, ⟨p', hp', v', hv'⟩⟩ := hconf
      obtain ⟨hvB, hvs'⟩ := Finset.mem_inter.mp hv
      obtain ⟨hvB', hvs⟩ := Finset.mem_inter.mp hv'
      have hpLs := (Finset.mem_sdiff.mp hp).1
      have hpLs' := (Finset.mem_sdiff.mp hp').1
      rw [hb p hpLs] at hvB
      rw [hb' p' hpLs'] at hvB'
      have hv := base_mem T0 sigma x0 a p v hvB
      have hv' := base_mem T0 sigma x0 a' p' v' hvB'
      have hma : marker T0 sigma x0 a = a' := by
        apply hau'
        · exact hT (hmk a)
        · exact hv ▸ hvs'
      have hma' : marker T0 sigma x0 a' = a := by
        apply hau
        · exact hT (hmk a')
        · exact hv' ▸ hvs
      have haT : a ∈ T0 := hma' ▸ hmk a'
      have haT' : a' ∈ T0 := hma ▸ hmk a
      have hsa : sigma a = a' := by simpa [marker, haT] using hma
      have hsa' : sigma a' = a := by simpa [marker, haT'] using hma'
      exact hn2 a haT (by rw [hsa, hsa'])
