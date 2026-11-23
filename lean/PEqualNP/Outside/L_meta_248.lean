import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_248 :
    ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos : Fin N → ℕ), 1 ≤ k → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → ∀ (L : ℕ) (c : ℕ → Fin N), 3 ≤ L → c L = c 0 → (∀ i : ℕ, i < L → E (c i) (c (i + 1))) → (∀ i j : ℕ, i < j → j < L → c i ≠ c j) → 2 * k + 1 ≤ L := by
  intro N k E pos hk ⟨hsym, hno00, hdeg⟩ L c hL hcL hcedge hcinj
  have hpos_ne : ∀ (v a b : Fin N), pos v ≠ 0 → pos v ≤ 2 * k →
      pos a + 1 = pos v → pos b = (pos v + 1) % (2 * k + 1) → pos a ≠ pos b := by
    intro v a b hv hvle ha hb
    by_cases hlt : pos v < 2 * k
    · have hmod : (pos v + 1) % (2 * k + 1) = pos v + 1 := Nat.mod_eq_of_lt (by omega)
      omega
    · have heq : pos v = 2 * k := by omega
      have hmod : (pos v + 1) % (2 * k + 1) = 0 := by
        rw [heq]
        exact Nat.mod_self (2 * k + 1)
      omega
  have hmain : ∀ (d : ℤ → Fin N),
      (∀ z : ℤ, d (z + (L : ℤ)) = d z) →
      (∀ z : ℤ, E (d z) (d (z + 1))) →
      (∀ z : ℤ, d z ≠ d (z + 2)) →
      (∃ z₀ : ℤ, pos (d z₀) ≠ 0 ∧ pos (d (z₀ + 1)) = (pos (d z₀) + 1) % (2 * k + 1)) →
      2 * k + 1 ≤ L := by
    intro d hper hedge hnoback ⟨z₀, hz₀_ne, hz₀_fwd⟩
    have step_fwd : ∀ z : ℤ, pos (d z) ≠ 0 → pos (d (z - 1)) + 1 = pos (d z) →
        pos (d (z + 1)) = (pos (d z) + 1) % (2 * k + 1) := by
      intro z hz hprev
      obtain ⟨hzle, a, b, hnb, ha, hb⟩ := hdeg (d z) hz
      have hab : pos a ≠ pos b := hpos_ne (d z) a b hz hzle ha hb
      have hEprev : E (d z) (d (z - 1)) := by
        have h1 := hedge (z - 1)
        have h2 : z - 1 + 1 = z := by omega
        rw [h2] at h1
        exact hsym _ _ h1
      have hEnext : E (d z) (d (z + 1)) := hedge z
      have hprev_ab : d (z - 1) = a ∨ d (z - 1) = b := (hnb _).mp hEprev
      have hnext_ab : d (z + 1) = a ∨ d (z + 1) = b := (hnb _).mp hEnext
      have hprev_eq_a : d (z - 1) = a := by
        rcases hprev_ab with h | h
        · exact h
        · rw [h] at hprev
          omega
      have hne : d (z - 1) ≠ d (z + 1) := by
        have h1 := hnoback (z - 1)
        have h2 : z - 1 + 2 = z + 1 := by omega
        rw [h2] at h1
        exact h1
      have hnext_eq_b : d (z + 1) = b := by
        rcases hnext_ab with h | h
        · exact absurd (hprev_eq_a.trans h.symm) hne
        · exact h
      rw [hnext_eq_b, hb]
    have step_bwd : ∀ z : ℤ, pos (d z) ≠ 0 → pos (d (z + 1)) = (pos (d z) + 1) % (2 * k + 1) →
        pos (d (z - 1)) + 1 = pos (d z) := by
      intro z hz hnext
      obtain ⟨hzle, a, b, hnb, ha, hb⟩ := hdeg (d z) hz
      have hab : pos a ≠ pos b := hpos_ne (d z) a b hz hzle ha hb
      have hEprev : E (d z) (d (z - 1)) := by
        have h1 := hedge (z - 1)
        have h2 : z - 1 + 1 = z := by omega
        rw [h2] at h1
        exact hsym _ _ h1
      have hEnext : E (d z) (d (z + 1)) := hedge z
      have hprev_ab : d (z - 1) = a ∨ d (z - 1) = b := (hnb _).mp hEprev
      have hnext_ab : d (z + 1) = a ∨ d (z + 1) = b := (hnb _).mp hEnext
      have hnext_eq_b : d (z + 1) = b := by
        rcases hnext_ab with h | h
        · rw [h] at hnext
          exact absurd (hnext.trans hb.symm) hab
        · exact h
      have hne : d (z - 1) ≠ d (z + 1) := by
        have h1 := hnoback (z - 1)
        have h2 : z - 1 + 2 = z + 1 := by omega
        rw [h2] at h1
        exact h1
      have hprev_eq_a : d (z - 1) = a := by
        rcases hprev_ab with h | h
        · exact h
        · exact absurd (h.trans hnext_eq_b.symm) hne
      rw [hprev_eq_a, ha]
    set p := pos (d z₀) with hp_def
    have hple : p ≤ 2 * k := (hdeg (d z₀) hz₀_ne).1
    have hbwd : ∀ t : ℕ, t ≤ p →
        pos (d (z₀ - (t : ℤ))) = p - t ∧
        pos (d (z₀ - (t : ℤ) + 1)) = (p - t + 1) % (2 * k + 1) := by
      intro t
      induction t with
      | zero =>
        intro _
        simp only [Nat.cast_zero, sub_zero, Nat.sub_zero]
        exact ⟨rfl, hz₀_fwd⟩
      | succ t ih =>
        intro ht
        have ⟨hcur, hnxt⟩ := ih (by omega)
        have hne0 : pos (d (z₀ - (t : ℤ))) ≠ 0 := by omega
        have hprev := step_bwd (z₀ - (t : ℤ)) hne0 (by rw [hcur]; exact hnxt)
        have hidx1 : z₀ - ((t + 1 : ℕ) : ℤ) = z₀ - (t : ℤ) - 1 := by omega
        have hidx2 : z₀ - ((t + 1 : ℕ) : ℤ) + 1 = z₀ - (t : ℤ) := by omega
        refine ⟨?_, ?_⟩
        · rw [hidx1]
          omega
        · rw [hidx2, hcur]
          have hlt : p - (t + 1) + 1 < 2 * k + 1 := by omega
          rw [Nat.mod_eq_of_lt hlt]
          omega
    set s : ℤ := z₀ - (p : ℤ)
    have hs0 : pos (d s) = 0 := by
      have h := (hbwd p (le_refl p)).1
      rw [Nat.sub_self] at h
      exact h
    have hs1 : pos (d (s + 1)) = 1 := by
      have h := (hbwd p (le_refl p)).2
      rw [Nat.sub_self, zero_add, Nat.mod_eq_of_lt (by omega)] at h
      exact h
    have hfwd : ∀ t : ℕ, t + 1 ≤ 2 * k →
        pos (d (s + (t : ℤ))) = t ∧ pos (d (s + ((t + 1 : ℕ) : ℤ))) = t + 1 := by
      intro t
      induction t with
      | zero =>
        intro _
        simp only [Nat.cast_zero, add_zero, zero_add, Nat.cast_one]
        exact ⟨hs0, hs1⟩
      | succ t ih =>
        intro ht
        have ⟨h0, h1⟩ := ih (by omega)
        have hne0 : pos (d (s + ((t + 1 : ℕ) : ℤ))) ≠ 0 := by omega
        have hidx_prev : s + ((t + 1 : ℕ) : ℤ) - 1 = s + (t : ℤ) := by omega
        have hidx_next : s + ((t + 1 : ℕ) : ℤ) + 1 = s + ((t + 2 : ℕ) : ℤ) := by omega
        have hstep := step_fwd (s + ((t + 1 : ℕ) : ℤ)) hne0 (by rw [hidx_prev]; omega)
        rw [hidx_next, h1] at hstep
        have hmod : (t + 1 + 1) % (2 * k + 1) = t + 2 := Nat.mod_eq_of_lt (by omega)
        exact ⟨h1, by rw [hstep, hmod]⟩
    have hpos_all : ∀ t : ℕ, t ≤ 2 * k → pos (d (s + (t : ℤ))) = t := by
      intro t ht
      cases t with
      | zero =>
        simp only [Nat.cast_zero, add_zero]
        exact hs0
      | succ m =>
        exact (hfwd m (by omega)).2
    by_contra hlt
    have hLle : L ≤ 2 * k := by omega
    have h0 : pos (d (s + ((0 : ℕ) : ℤ))) = 0 := hpos_all 0 (by omega)
    have hL' : pos (d (s + (L : ℤ))) = L := hpos_all L hLle
    have hEq : d (s + (L : ℤ)) = d (s + ((0 : ℕ) : ℤ)) := by
      rw [Nat.cast_zero, add_zero]
      exact hper s
    rw [hEq] at hL'
    omega
  let d : ℤ → Fin N := fun z => c (Int.toNat (z % (L : ℤ)))
  have hLpos : (0 : ℤ) < (L : ℤ) := by omega
  have hLne : (L : ℤ) ≠ 0 := by omega
  have hmod_nat : ∀ z : ℤ, ((Int.toNat (z % (L : ℤ)) : ℕ) : ℤ) = z % (L : ℤ) ∧
      Int.toNat (z % (L : ℤ)) < L := by
    intro z
    have h0 : 0 ≤ z % (L : ℤ) := Int.emod_nonneg z hLne
    have h1 : z % (L : ℤ) < (L : ℤ) := Int.emod_lt_of_pos z hLpos
    have hcast : ((Int.toNat (z % (L : ℤ)) : ℕ) : ℤ) = z % (L : ℤ) := Int.toNat_of_nonneg h0
    exact ⟨hcast, by omega⟩
  have hd_per : ∀ z : ℤ, d (z + (L : ℤ)) = d z := by
    intro z
    dsimp only [d]
    rw [Int.add_emod_right]
  have hd_edge : ∀ z : ℤ, E (d z) (d (z + 1)) := by
    intro z
    dsimp only [d]
    set m := Int.toNat (z % (L : ℤ))
    obtain ⟨hm_eq, hm_lt⟩ := hmod_nat z
    have hstep_mod : (z + 1) % (L : ℤ) = ((m : ℤ) + 1) % (L : ℤ) := by
      rw [Int.add_emod, hm_eq]
      have h1 : (1 : ℤ) % (L : ℤ) = 1 := Int.emod_eq_of_lt (by omega) (by omega)
      rw [h1]
    by_cases hmlt : m + 1 < L
    · have hmod1 : (z + 1) % (L : ℤ) = ((m + 1 : ℕ) : ℤ) := by
        rw [hstep_mod]
        have hlt1 : (m : ℤ) + 1 < (L : ℤ) := by omega
        rw [Int.emod_eq_of_lt (by omega) hlt1]
        omega
      rw [hmod1, Int.toNat_natCast]
      exact hcedge m hm_lt
    · have hmeq : m + 1 = L := by omega
      have hmod1 : (z + 1) % (L : ℤ) = 0 := by
        rw [hstep_mod]
        have h1 : (m : ℤ) + 1 = (L : ℤ) := by omega
        rw [h1, Int.emod_self]
      rw [hmod1]
      change E (c m) (c 0)
      rw [← hcL, ← hmeq]
      exact hcedge m hm_lt
  have hd_noback : ∀ z : ℤ, d z ≠ d (z + 2) := by
    intro z
    dsimp only [d]
    set m := Int.toNat (z % (L : ℤ))
    set m2 := Int.toNat ((z + 2) % (L : ℤ))
    obtain ⟨hm_eq, hm_lt⟩ := hmod_nat z
    obtain ⟨hm2_eq, hm2_lt⟩ := hmod_nat (z + 2)
    have hstep_mod : (z + 2) % (L : ℤ) = ((m : ℤ) + 2) % (L : ℤ) := by
      rw [Int.add_emod, hm_eq]
      have h2 : (2 : ℤ) % (L : ℤ) = 2 := Int.emod_eq_of_lt (by omega) (by omega)
      rw [h2]
    have hm_ne : m ≠ m2 := by
      by_cases hlt2 : m + 2 < L
      · have h1 : ((m : ℤ) + 2) % (L : ℤ) = (m : ℤ) + 2 :=
          Int.emod_eq_of_lt (by omega) (by omega)
        omega
      · have h1 : ((m : ℤ) + 2) % (L : ℤ) = (m : ℤ) + 2 - (L : ℤ) := by
          calc ((m : ℤ) + 2) % (L : ℤ)
            _ = (((m : ℤ) + 2 - (L : ℤ)) + (L : ℤ)) % (L : ℤ) := by congr 1; omega
            _ = ((m : ℤ) + 2 - (L : ℤ)) % (L : ℤ) := Int.add_emod_right _ _
            _ = (m : ℤ) + 2 - (L : ℤ) := Int.emod_eq_of_lt (by omega) (by omega)
        omega
    rcases lt_or_gt_of_ne hm_ne with hlt | hgt
    · exact hcinj m m2 hlt hm2_lt
    · exact Ne.symm (hcinj m2 m hgt hm_lt)
  have hex : ∃ z₀ : ℤ, pos (d z₀) ≠ 0 := by
    rcases hno00 _ _ (hd_edge 0) with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  obtain ⟨z₀, hz₀⟩ := hex
  obtain ⟨hle, a, b, hnb, ha, hb⟩ := hdeg (d z₀) hz₀
  have hnext_ab : d (z₀ + 1) = a ∨ d (z₀ + 1) = b := (hnb _).mp (hd_edge z₀)
  rcases hnext_ab with hnext_a | hnext_b
  · have hEprev : E (d z₀) (d (z₀ - 1)) := by
      have h1 := hd_edge (z₀ - 1)
      have h2 : z₀ - 1 + 1 = z₀ := by omega
      rw [h2] at h1
      exact hsym _ _ h1
    have hprev_ab : d (z₀ - 1) = a ∨ d (z₀ - 1) = b := (hnb _).mp hEprev
    have hne : d (z₀ - 1) ≠ d (z₀ + 1) := by
      have h1 := hd_noback (z₀ - 1)
      have h2 : z₀ - 1 + 2 = z₀ + 1 := by omega
      rw [h2] at h1
      exact h1
    have hprev_b : d (z₀ - 1) = b := by
      rcases hprev_ab with h | h
      · exact absurd (h.trans hnext_a.symm) hne
      · exact h
    let d' : ℤ → Fin N := fun z => d (-z)
    have hd'_per : ∀ z : ℤ, d' (z + (L : ℤ)) = d' z := by
      intro z
      dsimp only [d']
      have h1 := hd_per (-z - (L : ℤ))
      have h2 : -z - (L : ℤ) + (L : ℤ) = -z := by omega
      have h3 : -(z + (L : ℤ)) = -z - (L : ℤ) := by omega
      rw [h2] at h1
      rw [h3]
      exact h1.symm
    have hd'_edge : ∀ z : ℤ, E (d' z) (d' (z + 1)) := by
      intro z
      dsimp only [d']
      have h1 := hd_edge (-z - 1)
      have h2 : -z - 1 + 1 = -z := by omega
      have h3 : -(z + 1) = -z - 1 := by omega
      rw [h2] at h1
      rw [h3]
      exact hsym _ _ h1
    have hd'_noback : ∀ z : ℤ, d' z ≠ d' (z + 2) := by
      intro z
      dsimp only [d']
      have h1 := hd_noback (-z - 2)
      have h2 : -z - 2 + 2 = -z := by omega
      have h3 : -(z + 2) = -z - 2 := by omega
      rw [h2] at h1
      rw [h3]
      exact Ne.symm h1
    have hz₀' : pos (d' (-z₀)) ≠ 0 := by
      dsimp only [d']
      rw [neg_neg]
      exact hz₀
    have hz₀'_fwd : pos (d' (-z₀ + 1)) = (pos (d' (-z₀)) + 1) % (2 * k + 1) := by
      dsimp only [d']
      have h1 : -(-z₀ + 1) = z₀ - 1 := by omega
      rw [neg_neg, h1, hprev_b, hb]
    exact hmain d' hd'_per hd'_edge hd'_noback ⟨-z₀, hz₀', hz₀'_fwd⟩
  · exact hmain d hd_per hd_edge hd_noback ⟨z₀, hz₀, by rw [hnext_b, hb]⟩
