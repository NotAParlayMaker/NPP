import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1583

lemma mod_succ_inj {a b m : ℕ} (ha : a < m) (hb : b < m)
    (h : (a + 1) % m = (b + 1) % m) : a = b := by
  by_cases ha1 : a + 1 < m <;> by_cases hb1 : b + 1 < m
  · rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt hb1] at h
    omega
  · have hbm : b + 1 = m := by omega
    rw [Nat.mod_eq_of_lt ha1, hbm, Nat.mod_self] at h
    omega
  · have ham : a + 1 = m := by omega
    rw [ham, Nat.mod_self, Nat.mod_eq_of_lt hb1] at h
    omega
  · omega

lemma exists_cycle {N : ℕ} (T0 : Finset (Fin N)) (hcard : 3 ≤ T0.card) :
    ∃ sigma : Fin N → Fin N,
      (∀ x ∈ T0, sigma x ∈ T0) ∧
      Set.InjOn sigma ↑T0 ∧
      (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y) := by
  classical
  let xs : List (Fin N) := T0.toList
  have hnodup : xs.Nodup := Finset.nodup_toList T0
  have hlen : xs.length = T0.card := Finset.length_toList T0
  have hm : 0 < xs.length := by rw [hlen]; omega
  let sigma : Fin N → Fin N := fun x =>
    if hx : x ∈ T0 then
      xs[(xs.idxOf x + 1) % xs.length]'(Nat.mod_lt _ hm)
    else x
  have hclosed : ∀ x ∈ T0, sigma x ∈ T0 := by
    intro x hx
    simp only [sigma, hx, dite_true]
    exact Finset.mem_toList.mp (List.getElem_mem _)
  have hinj : Set.InjOn sigma ↑T0 := by
    intro x hx y hy hxy
    have hx' : x ∈ T0 := hx
    have hy' : y ∈ T0 := hy
    simp only [sigma, hx', hy', dite_true] at hxy
    have hidx : (xs.idxOf x + 1) % xs.length = (xs.idxOf y + 1) % xs.length :=
      (hnodup.getElem_inj_iff).mp hxy
    have hxlt : xs.idxOf x < xs.length := List.idxOf_lt_length_iff.mpr (Finset.mem_toList.mpr hx')
    have hylt : xs.idxOf y < xs.length := List.idxOf_lt_length_iff.mpr (Finset.mem_toList.mpr hy')
    have heq : xs.idxOf x = xs.idxOf y := mod_succ_inj hxlt hylt hidx
    have hgx := List.getElem_idxOf hxlt
    have hgy := List.getElem_idxOf hylt
    rw [← hgx, ← hgy]
    congr 1
  have hiter : ∀ k : ℕ, ∀ x ∈ T0,
      sigma^[k] x ∈ T0 ∧ xs.idxOf (sigma^[k] x) = (xs.idxOf x + k) % xs.length := by
    intro k
    induction k with
    | zero =>
      intro x hx
      have hxlt : xs.idxOf x < xs.length := List.idxOf_lt_length_iff.mpr (Finset.mem_toList.mpr hx)
      exact ⟨hx, by simp [Nat.mod_eq_of_lt hxlt]⟩
    | succ k ih =>
      intro x hx
      obtain ⟨hzT, hzidx⟩ := ih x hx
      rw [Function.iterate_succ_apply']
      refine ⟨hclosed _ hzT, ?_⟩
      simp only [sigma, hzT, dite_true]
      rw [List.Nodup.idxOf_getElem hnodup, hzidx]
      rw [Nat.mod_add_mod, Nat.add_assoc]
  refine ⟨sigma, hclosed, hinj, ?_⟩
  intro x hx y hy
  have hxlt : xs.idxOf x < xs.length := List.idxOf_lt_length_iff.mpr (Finset.mem_toList.mpr hx)
  have hylt : xs.idxOf y < xs.length := List.idxOf_lt_length_iff.mpr (Finset.mem_toList.mpr hy)
  let k : ℕ := (xs.length - xs.idxOf x) + xs.idxOf y
  refine ⟨k, ?_⟩
  obtain ⟨hkT, hkidx⟩ := hiter k x hx
  have hmod : (xs.idxOf x + k) % xs.length = xs.idxOf y := by
    have hsum : xs.idxOf x + k = xs.length + xs.idxOf y := by omega
    rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt hylt]
  rw [hmod] at hkidx
  have hklt : xs.idxOf (sigma^[k] x) < xs.length :=
    List.idxOf_lt_length_iff.mpr (Finset.mem_toList.mpr hkT)
  have hg1 := List.getElem_idxOf hklt
  have hg2 := List.getElem_idxOf hylt
  rw [← hg1, ← hg2]
  simp [hkidx]

lemma sigma_ne_self {N : ℕ} (T0 : Finset (Fin N)) (hcard : 3 ≤ T0.card)
    (sigma : Fin N → Fin N)
    (htrans : ∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y)
    {r : Fin N} (hr : r ∈ T0) : sigma r ≠ r := by
  intro hfix
  have hiter : ∀ k : ℕ, sigma^[k] r = r := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, hfix]
  have hsub : T0 ⊆ {r} := by
    intro y hy
    obtain ⟨k, hk⟩ := htrans r hr y hy
    rw [← hk, hiter k]
    exact Finset.mem_singleton_self r
  have hle := Finset.card_le_card hsub
  rw [Finset.card_singleton] at hle
  omega

lemma sigma_sigma_ne_self {N : ℕ} (T0 : Finset (Fin N)) (hcard : 3 ≤ T0.card)
    (sigma : Fin N → Fin N)
    (htrans : ∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y)
    {r : Fin N} (hr : r ∈ T0) : sigma (sigma r) ≠ r := by
  intro h2
  have hiter : ∀ k : ℕ, sigma^[k] r = r ∨ sigma^[k] r = sigma r := by
    intro k
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · exact Or.inr (by rw [h])
      · exact Or.inl (by rw [h, h2])
  have hsub : T0 ⊆ {r, sigma r} := by
    intro y hy
    obtain ⟨k, hk⟩ := htrans r hr y hy
    rw [← hk]
    rcases hiter k with h | h
    · simp [h]
    · simp [h]
  have hle := (Finset.card_le_card hsub).trans Finset.card_le_two
  omega

lemma inter_unique {N : ℕ} {L : Fin N → Finset (Fin N)}
    (hinter : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    {i s : Fin N} (hs : s ≠ i) :
    ∃ r : Fin N, r ∈ L i ∧ r ∈ L s ∧ ∀ v : Fin N, v ∈ L i → v ∈ L s → v = r := by
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (hinter i s hs.symm)
  have hmem : r ∈ L i ∩ L s := by rw [hr]; exact Finset.mem_singleton_self r
  refine ⟨r, (Finset.mem_inter.mp hmem).1, (Finset.mem_inter.mp hmem).2, ?_⟩
  intro v hvi hvs
  have hv : v ∈ L i ∩ L s := Finset.mem_inter.mpr ⟨hvi, hvs⟩
  rw [hr, Finset.mem_singleton] at hv
  exact hv

lemma partA {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N))
    (hcard : 3 ≤ T0.card) (hinter : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hsub : T0 ⊆ L i0)
    (sigma : Fin N → Fin N) (x0 : Fin N) (B : Fin N → Fin N → Finset (Fin N))
    (hclosed : ∀ x ∈ T0, sigma x ∈ T0)
    (htrans : ∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y)
    (hx0 : x0 ∈ T0)
    (hB1 : ∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ x ∈ T0, x ∈ L s →
      B s p = if p = x then (∅ : Finset (Fin N)) else {sigma x})
    (hB2 : ∀ s : Fin N, s ≠ i0 → ∀ r ∈ L i0 \ T0, r ∈ L s → ∀ p ∈ L s, B s p = {x0}) :
    ∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s,
      B s p ∩ L s = ∅ ∧
      ((∃ v ∈ T0, (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∨
        ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∧
      ∀ v ∈ L s, decide (v = p ∨ v ∈ B s p) = true ↔ v = p := by
  intro s hs p hp
  obtain ⟨r, hr0, hrs, huniq⟩ := inter_unique hinter hs
  by_cases hrT : r ∈ T0
  · have hB := hB1 s hs p hp r hrT hrs
    have hsig_ne : sigma r ≠ r := sigma_ne_self T0 hcard sigma htrans hrT
    have hsig_T : sigma r ∈ T0 := hclosed r hrT
    have hsig_nLs : sigma r ∉ L s := by
      intro hmem
      exact hsig_ne (huniq (sigma r) (hsub hsig_T) hmem)
    have hdisj : B s p ∩ L s = ∅ := by
      rw [hB]
      split_ifs
      · simp
      · ext v
        simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
        rintro rfl
        exact hsig_nLs
    refine ⟨hdisj, Or.inl ?_, ?_⟩
    · by_cases hpr : p = r
      · exact ⟨r, hrT, by simp [hpr]⟩
      · refine ⟨sigma r, hsig_T, ?_⟩
        simp [hB, hpr]
    · intro v hv
      have hvB : v ∉ B s p := by
        intro hmem
        have : v ∈ B s p ∩ L s := Finset.mem_inter.mpr ⟨hmem, hv⟩
        rw [hdisj] at this
        exact Finset.notMem_empty v this
      simp [hvB]
  · have hr_diff : r ∈ L i0 \ T0 := Finset.mem_sdiff.mpr ⟨hr0, hrT⟩
    have hB := hB2 s hs r hr_diff hrs p hp
    have hx0_ne : x0 ≠ r := by
      intro h
      rw [h] at hx0
      exact hrT hx0
    have hx0_nLs : x0 ∉ L s := by
      intro hmem
      exact hx0_ne (huniq x0 (hsub hx0) hmem)
    have hdisj : B s p ∩ L s = ∅ := by
      rw [hB]
      ext v
      simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro rfl
      exact hx0_nLs
    refine ⟨hdisj, Or.inl ⟨x0, hx0, ?_⟩, ?_⟩
    · simp [hB]
    · intro v hv
      have hvB : v ∉ B s p := by
        intro hmem
        have : v ∈ B s p ∩ L s := Finset.mem_inter.mpr ⟨hmem, hv⟩
        rw [hdisj] at this
        exact Finset.notMem_empty v this
      simp [hvB]

lemma B_subset_T0 {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N))
    (hinter : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (sigma : Fin N → Fin N) (x0 : Fin N) (B : Fin N → Fin N → Finset (Fin N))
    (hclosed : ∀ x ∈ T0, sigma x ∈ T0)
    (hx0 : x0 ∈ T0)
    (hB1 : ∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ x ∈ T0, x ∈ L s →
      B s p = if p = x then (∅ : Finset (Fin N)) else {sigma x})
    (hB2 : ∀ s : Fin N, s ≠ i0 → ∀ r ∈ L i0 \ T0, r ∈ L s → ∀ p ∈ L s, B s p = {x0})
    {s : Fin N} (hs : s ≠ i0) {p : Fin N} (hp : p ∈ L s) :
    B s p ⊆ T0 := by
  obtain ⟨r, hr0, hrs, _⟩ := inter_unique hinter hs
  by_cases hrT : r ∈ T0
  · rw [hB1 s hs p hp r hrT hrs]
    split_ifs
    · exact Finset.empty_subset T0
    · exact Finset.singleton_subset_iff.mpr (hclosed r hrT)
  · rw [hB2 s hs r (Finset.mem_sdiff.mpr ⟨hr0, hrT⟩) hrs p hp]
    exact Finset.singleton_subset_iff.mpr hx0

lemma partB {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N))
    (hcard : 3 ≤ T0.card) (hinter : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (sigma : Fin N → Fin N) (x0 : Fin N) (B : Fin N → Fin N → Finset (Fin N))
    (hclosed : ∀ x ∈ T0, sigma x ∈ T0)
    (htrans : ∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y)
    (hx0 : x0 ∈ T0)
    (hB1 : ∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ x ∈ T0, x ∈ L s →
      B s p = if p = x then (∅ : Finset (Fin N)) else {sigma x})
    (hB2 : ∀ s : Fin N, s ≠ i0 → ∀ r ∈ L i0 \ T0, r ∈ L s → ∀ p ∈ L s, B s p = {x0}) :
    ∀ s s' : Fin N, s ≠ i0 → s' ≠ i0 → s ≠ s' →
      ¬ ((∃ p ∈ L s \ L s', (B s p ∩ L s').Nonempty) ∧
         (∃ p ∈ L s' \ L s, (B s' p ∩ L s).Nonempty)) := by
  intro s s' hs hs' _ ⟨⟨p, hp, ⟨u, hu⟩⟩, ⟨p', hp', ⟨u', hu'⟩⟩⟩
  have hpLs : p ∈ L s := (Finset.mem_sdiff.mp hp).1
  have hpLs' : p' ∈ L s' := (Finset.mem_sdiff.mp hp').1
  have huB : u ∈ B s p := (Finset.mem_inter.mp hu).1
  have huLs' : u ∈ L s' := (Finset.mem_inter.mp hu).2
  have hu'B : u' ∈ B s' p' := (Finset.mem_inter.mp hu').1
  have hu'Ls : u' ∈ L s := (Finset.mem_inter.mp hu').2
  have huT : u ∈ T0 := B_subset_T0 L i0 T0 hinter sigma x0 B hclosed hx0 hB1 hB2 hs hpLs huB
  have hu'T : u' ∈ T0 := B_subset_T0 L i0 T0 hinter sigma x0 B hclosed hx0 hB1 hB2 hs' hpLs' hu'B
  have hBs : B s p = if p = u' then (∅ : Finset (Fin N)) else {sigma u'} :=
    hB1 s hs p hpLs u' hu'T hu'Ls
  have hBs' : B s' p' = if p' = u then (∅ : Finset (Fin N)) else {sigma u} :=
    hB1 s' hs' p' hpLs' u huT huLs'
  have hu_eq : u = sigma u' := by
    rw [hBs] at huB
    split_ifs at huB
    · exact absurd huB (Finset.notMem_empty u)
    · exact Finset.mem_singleton.mp huB
  have hu'_eq : u' = sigma u := by
    rw [hBs'] at hu'B
    split_ifs at hu'B
    · exact absurd hu'B (Finset.notMem_empty u')
    · exact Finset.mem_singleton.mp hu'B
  have hcyc : sigma (sigma u') = u' := by
    rw [← hu_eq, ← hu'_eq]
  exact sigma_sigma_ne_self T0 hcard sigma htrans hu'T hcyc

end PEqualNP.Outside.L_meta_1583

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
  intro q m N L i0 T0 _ hm _ _ _ hinter _ hsub hT0
  have hcard : 3 ≤ T0.card := by omega
  refine ⟨PEqualNP.Outside.L_meta_1583.exists_cycle T0 hcard, ?_⟩
  intro sigma x0 B ⟨hclosed, _, htrans⟩ hx0 hB1 hB2
  refine ⟨PEqualNP.Outside.L_meta_1583.partA L i0 T0 hcard hinter hsub sigma x0 B hclosed htrans hx0 hB1 hB2,
          PEqualNP.Outside.L_meta_1583.partB L i0 T0 hcard hinter sigma x0 B hclosed htrans hx0 hB1 hB2⟩
