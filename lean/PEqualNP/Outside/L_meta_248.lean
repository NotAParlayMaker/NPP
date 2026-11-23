import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_248 : ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos : Fin N → ℕ), 1 ≤ k → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → ∀ (L : ℕ) (c : ℕ → Fin N), 3 ≤ L → c L = c 0 → (∀ i : ℕ, i < L → E (c i) (c (i + 1))) → (∀ i j : ℕ, i < j → j < L → c i ≠ c j) → 2 * k + 1 ≤ L := by
  intro N k E pos hk ⟨symm, nz, thread⟩ L c hL close edge simple
  let S := (Finset.range L).image (fun i => pos (c i))
  have mem (x : ℕ) : x ∈ S ↔ ∃ i, i < L ∧ pos (c i) = x := by
    simp [S]
  have step (x : ℕ) (hx : x ∈ S) (hp : x ≠ 0) :
      x - 1 ∈ S ∧ (x + 1) % (2*k+1) ∈ S := by
    obtain ⟨i, hi, rfl⟩ := (mem x).mp hx
    obtain ⟨_, a, b, adj, ha, hb⟩ := thread (c i) hp
    let p := if i = 0 then L-1 else i-1
    let q := if i+1 = L then 0 else i+1
    have prev : E (c i) (c p) := by
      dsimp [p]
      split_ifs with h
      · subst i
        have e := symm _ _ (edge (L-1) (by omega))
        rwa [show L-1+1=L by omega, close] at e
      · have e := symm _ _ (edge (i-1) (by omega))
        rwa [show i-1+1=i by omega] at e
    have nextE : E (c i) (c q) := by
      dsimp [q]
      split_ifs with h
      · simpa [h, close] using edge i hi
      · exact edge i hi
    have bounds : p < L ∧ q < L ∧ p ≠ q := by
      dsimp [p,q]
      split_ifs <;> omega
    have diff : c p ≠ c q := by
      rcases lt_or_gt_of_ne bounds.2.2 with h | h
      · exact simple p q h bounds.2.1
      · exact (simple q p h bounds.1).symm
    have pm := (mem _).mpr ⟨p, bounds.1, rfl⟩
    have qm := (mem _).mpr ⟨q, bounds.2.1, rfl⟩
    have predEq : pos (c i) - 1 = pos a := by omega
    rw [predEq, ← hb]
    rcases (adj _).mp prev with h | h <;> rcases (adj _).mp nextE with g | g <;>
      simp_all
  obtain ⟨i, hi, hpos⟩ : ∃ i, i < L ∧ pos (c i) ≠ 0 := by
    rcases nz _ _ (edge 0 (by omega)) with h | h
    · exact ⟨0, by omega, h⟩
    · exact ⟨1, by omega, h⟩
  have down (x : ℕ) (hx : x ∈ S) (hp : 0 < x) : 1 ∈ S := by
    induction x with
    | zero => omega
    | succ n ih =>
      by_cases hn : n = 0
      · simpa [hn] using hx
      · exact ih (by simpa using (step _ hx (by omega)).1) (by omega)
  have one := down _ ((mem _).mpr ⟨i, hi, rfl⟩) (by omega)
  have up (n : ℕ) (hn : n+1 ≤ 2*k) : n+1 ∈ S := by
    induction n with
    | zero => exact one
    | succ n ih =>
      have h := (step (n+1) (ih (by omega)) (by omega)).2
      rwa [Nat.mod_eq_of_lt (by omega)] at h
  have sub : Finset.range (2*k+1) ⊆ S := by
    intro n hn
    have := Finset.mem_range.mp hn
    cases n with
    | zero => exact (step 1 one (by decide)).1
    | succ n => exact up n (by omega)
  simpa [S] using (Finset.card_le_card sub).trans (Finset.card_image_le)
