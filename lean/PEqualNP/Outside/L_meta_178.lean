import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.RelIso.Basic

theorem PEqualNP.Outside.L_meta_178 :
    ∀ (k N : ℕ) (Gh : SimpleGraph (Fin N)) (pos : Fin N → ℕ),
      (∀ u v : Fin N, Gh.Adj u v → pos u ≠ 0 ∨ pos v ≠ 0) →
      (∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N,
        (∀ w : Fin N, Gh.Adj v w ↔ w = a ∨ w = b) ∧
        pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) →
      (∀ (L : ℕ) (c : ℕ → Fin N), 3 ≤ L →
        (∀ i j : ℕ, i < L → j < L → c i = c j → i = j) →
        (∀ i : ℕ, i < L → Gh.Adj (c i) (c ((i + 1) % L))) →
        6 * k + 3 ≤ L) →
      ∀ (m : ℕ) (H : SimpleGraph (Fin m)) (e : RelEmbedding H.Adj Gh.Adj),
        (∀ (L : ℕ) (c : ℕ → Fin m), 3 ≤ L →
          (∀ i j : ℕ, i < L → j < L → c i = c j → i = j) →
          (∀ i : ℕ, i < L → H.Adj (c i) (c ((i + 1) % L))) →
          6 * k + 3 ≤ L) ∧
        ∀ u x y z : Fin m, H.Adj u x → H.Adj u y → H.Adj u z →
          x ≠ y → x ≠ z → y ≠ z → pos (e u) = 0 :=
  fun _ _ _ _ _ hdeg hcyc _ _ e =>
    ⟨fun L c hL hinj hadj =>
        hcyc L (fun i => e (c i)) hL
          (fun i j hi hj heq => hinj i j hi hj (e.injective heq))
          (fun i hi => e.map_rel_iff.mpr (hadj i hi)),
     fun u x y z hux huy huz hxy hxz hyz =>
        Classical.byContradiction fun hne =>
          let ⟨_, a, b, hnb, _, _⟩ := hdeg (e u) hne
          match (hnb (e x)).mp (e.map_rel_iff.mpr hux),
                (hnb (e y)).mp (e.map_rel_iff.mpr huy),
                (hnb (e z)).mp (e.map_rel_iff.mpr huz) with
          | Or.inl hx, Or.inl hy, _ => hxy (e.injective (hx.trans hy.symm))
          | Or.inl hx, Or.inr _, Or.inl hz => hxz (e.injective (hx.trans hz.symm))
          | Or.inl _, Or.inr hy, Or.inr hz => hyz (e.injective (hy.trans hz.symm))
          | Or.inr _, Or.inl hy, Or.inl hz => hyz (e.injective (hy.trans hz.symm))
          | Or.inr hx, Or.inl _, Or.inr hz => hxz (e.injective (hx.trans hz.symm))
          | Or.inr hx, Or.inr hy, _ => hxy (e.injective (hx.trans hy.symm))⟩
