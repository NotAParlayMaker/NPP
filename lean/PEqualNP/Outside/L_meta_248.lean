import Mathlib

/-!
# Thread labellings force long cycles (L-meta-248)

A thread vertex (label `p` with `1 ≤ p ≤ 2k`) has exactly two neighbours, labelled `p - 1`
and `p + 1` (mod `2k + 1`). On a simple cycle of length at least `3`, a thread vertex uses
both of its edges, so both of its neighbours lie on the cycle. Starting from a thread vertex
on the cycle (every edge has one) and walking down and up the labels, the cycle contains a
vertex of every label `0, 1, ..., 2k`. These are `2k + 1` distinct vertices, so the cycle has
length at least `2k + 1`.
-/

theorem PEqualNP.Outside.L_meta_248 : ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos : Fin N → ℕ), 1 ≤ k → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → ∀ (L : ℕ) (c : ℕ → Fin N), 3 ≤ L → c L = c 0 → (∀ i : ℕ, i < L → E (c i) (c (i + 1))) → (∀ i j : ℕ, i < j → j < L → c i ≠ c j) → 2 * k + 1 ≤ L := by
  intro N k E pos _hk ⟨hsym, hedge, hthr⟩ L c hL hcL hE hinj
  -- the cycle is injective on indices below `L`
  have hne : ∀ i j, i < L → j < L → i ≠ j → c i ≠ c j := by
    intro i j hi hj hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact hinj i j h hj
    · exact fun e => hinj j i h hi e.symm
  -- every vertex at index `r < L` has two distinct cycle neighbours, at indices below `L`
  have hnb : ∀ r < L, ∃ s q, s < L ∧ q < L ∧ s ≠ q ∧ E (c r) (c s) ∧ E (c r) (c q) := by
    intro r hr
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · refine ⟨1, L - 1, by omega, by omega, by omega, by simpa using hE 0 (by omega), ?_⟩
      apply hsym
      have h := hE (L - 1) (by omega)
      rwa [show L - 1 + 1 = L by omega, hcL] at h
    · have hq : E (c r) (c (r - 1)) := by
        apply hsym
        have h := hE (r - 1) (by omega)
        rwa [show r - 1 + 1 = r by omega] at h
      by_cases hs : r + 1 < L
      · exact ⟨r + 1, r - 1, hs, by omega, by omega, hE r hr, hq⟩
      · have h := hE r hr
        rw [show r + 1 = L by omega, hcL] at h
        exact ⟨0, r - 1, by omega, by omega, by omega, h, hq⟩
  -- both neighbours of a thread vertex on the cycle are on the cycle
  have hcl : ∀ r < L, pos (c r) ≠ 0 → ∀ w, E (c r) w → ∃ r' < L, c r' = w := by
    intro r hr hp w hw
    obtain ⟨_, a, b, hab, _, _⟩ := hthr (c r) hp
    obtain ⟨s, q, hsL, hqL, hsq, hEs, hEq⟩ := hnb r hr
    have hx := (hab (c s)).1 hEs
    have hy := (hab (c q)).1 hEq
    have hxy : c s ≠ c q := hne s q hsL hqL hsq
    rcases (hab w).1 hw with rfl | rfl
    · rcases hx with hx | hx
      · exact ⟨s, hsL, hx⟩
      · rcases hy with hy | hy
        · exact ⟨q, hqL, hy⟩
        · exact absurd (hx.trans hy.symm) hxy
    · rcases hx with hx | hx
      · rcases hy with hy | hy
        · exact absurd (hx.trans hy.symm) hxy
        · exact ⟨q, hqL, hy⟩
      · exact ⟨s, hsL, hx⟩
  -- a thread vertex on the cycle
  obtain ⟨r0, hr0, hp0⟩ : ∃ r < L, pos (c r) ≠ 0 := by
    rcases hedge _ _ (hE 0 (by omega)) with h | h
    · exact ⟨0, by omega, h⟩
    · exact ⟨1, by omega, by simpa using h⟩
  have hp0le : pos (c r0) ≤ 2 * k := (hthr _ hp0).1
  -- walking down the labels
  have down : ∀ m, m ≤ pos (c r0) → ∃ r < L, pos (c r) = pos (c r0) - m := by
    intro m
    induction m with
    | zero => intro _; exact ⟨r0, hr0, by simp⟩
    | succ m ih =>
      intro hm
      obtain ⟨r, hr, hpr⟩ := ih (by omega)
      have hnz : pos (c r) ≠ 0 := by omega
      obtain ⟨_, a, b, hab, ha, _⟩ := hthr (c r) hnz
      obtain ⟨r', hr', hr'a⟩ := hcl r hr hnz a ((hab a).2 (Or.inl rfl))
      exact ⟨r', hr', by rw [hr'a]; omega⟩
  -- walking up the labels
  have up : ∀ m, pos (c r0) + m ≤ 2 * k → ∃ r < L, pos (c r) = pos (c r0) + m := by
    intro m
    induction m with
    | zero => intro _; exact ⟨r0, hr0, by simp⟩
    | succ m ih =>
      intro hm
      obtain ⟨r, hr, hpr⟩ := ih (by omega)
      have hnz : pos (c r) ≠ 0 := by omega
      obtain ⟨_, a, b, hab, _, hb⟩ := hthr (c r) hnz
      obtain ⟨r', hr', hr'b⟩ := hcl r hr hnz b ((hab b).2 (Or.inr rfl))
      refine ⟨r', hr', ?_⟩
      rw [hr'b, hb, hpr, Nat.mod_eq_of_lt (by omega)]
      omega
  -- every label `0, ..., 2k` occurs on the cycle
  have cov : ∀ q ≤ 2 * k, ∃ r < L, pos (c r) = q := by
    intro q hq
    by_cases h : q ≤ pos (c r0)
    · obtain ⟨r, hr, e⟩ := down (pos (c r0) - q) (by omega)
      exact ⟨r, hr, by omega⟩
    · obtain ⟨r, hr, e⟩ := up (q - pos (c r0)) (by omega)
      exact ⟨r, hr, by omega⟩
  -- count
  have hsub : Finset.range (2 * k + 1) ⊆ (Finset.range L).image (fun r => pos (c r)) := by
    intro q hq
    rw [Finset.mem_range] at hq
    obtain ⟨r, hr, h⟩ := cov q (by omega)
    exact Finset.mem_image.2 ⟨r, Finset.mem_range.2 hr, h⟩
  have h := (Finset.card_le_card hsub).trans Finset.card_image_le
  simpa using h
