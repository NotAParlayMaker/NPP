import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_178 :
    ∀ (k N : ℕ) (Gh : SimpleGraph (Fin N)) (pos : Fin N → ℕ), (∀ u v : Fin N, Gh.Adj u v → pos u ≠ 0 ∨ pos v ≠ 0) → (∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, Gh.Adj v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → (∀ (L : ℕ) (c : ℕ → Fin N), 3 ≤ L → (∀ i j : ℕ, i < L → j < L → c i = c j → i = j) → (∀ i : ℕ, i < L → Gh.Adj (c i) (c ((i + 1) % L))) → 6 * k + 3 ≤ L) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) (e : RelEmbedding H.Adj Gh.Adj), (∀ (L : ℕ) (c : ℕ → Fin m), 3 ≤ L → (∀ i j : ℕ, i < L → j < L → c i = c j → i = j) → (∀ i : ℕ, i < L → H.Adj (c i) (c ((i + 1) % L))) → 6 * k + 3 ≤ L) ∧ ∀ u x y z : Fin m, H.Adj u x → H.Adj u y → H.Adj u z → x ≠ y → x ≠ z → y ≠ z → pos (e u) = 0 := by
  intro k N Gh pos hzero hdeg hgirth m H e
  constructor
  · intro L c hL hinj hcyc
    exact hgirth L (fun i => e (c i)) hL
      (fun i j hi hj h => hinj i j hi hj (e.injective h))
      (fun i hi => (e.map_rel_iff).mpr (hcyc i hi))
  · intro u x y z hux huy huz hxy hxz hyz
    by_contra hne
    obtain ⟨-, a, b, hnb, -, -⟩ := hdeg (e u) hne
    have hx : e x = a ∨ e x = b := (hnb (e x)).mp ((e.map_rel_iff).mpr hux)
    have hy : e y = a ∨ e y = b := (hnb (e y)).mp ((e.map_rel_iff).mpr huy)
    have hz : e z = a ∨ e z = b := (hnb (e z)).mp ((e.map_rel_iff).mpr huz)
    have hxy' : e x ≠ e y := fun h => hxy (e.injective h)
    have hxz' : e x ≠ e z := fun h => hxz (e.injective h)
    have hyz' : e y ≠ e z := fun h => hyz (e.injective h)
    rcases hx with h1 | h1 <;> rcases hy with h2 | h2 <;> rcases hz with h3 | h3 <;> simp_all
