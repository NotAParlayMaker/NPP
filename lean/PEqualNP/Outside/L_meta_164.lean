import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_164 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) (t t1 t2 : ℕ), (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → (∃ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → a ∈ S ∨ b ∈ S) ∧ S.card = t1) → (∀ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → a ∈ S ∨ b ∈ S) → t1 ≤ S.card) → (∃ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → ¬ G.Adj v a → ¬ G.Adj v b → a ∈ S ∨ b ∈ S) ∧ S.card = t2) → (∀ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → ¬ G.Adj v a → ¬ G.Adj v b → a ∈ S ∨ b ∈ S) → t2 ≤ S.card) → t = min (t1 + 1) (t2 + (Finset.univ.filter (fun u : Fin n => G.Adj v u)).card) := by
  intro n G _ v t t1 t2 h0 hmin h1 hmin1 h2 hmin2
  classical
  let N : Finset (Fin n) := Finset.univ.filter (fun u => G.Adj v u)
  have memN (u : Fin n) : u ∈ N ↔ G.Adj v u := by simp [N]
  have upper1 : t ≤ t1 + 1 := by
    obtain ⟨S, hS, hc⟩ := h1
    have hcover : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G
        (insert v S) := by
      intro a b hab
      by_cases ha : a = v
      · exact Or.inl (by simp [ha])
      by_cases hb : b = v
      · exact Or.inr (by simp [hb])
      rcases hS a b hab ha hb with h | h
      · exact Or.inl (Finset.mem_insert_of_mem h)
      · exact Or.inr (Finset.mem_insert_of_mem h)
    have hcard := Finset.card_insert_le v S
    have hle := hmin (insert v S) hcover
    omega
  have upper2 : t ≤ t2 + N.card := by
    obtain ⟨S, hS, hc⟩ := h2
    have hcover : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G
        (S ∪ N) := by
      intro a b hab
      by_cases ha : a = v
      · exact Or.inr (Finset.mem_union_right S ((memN b).2 (ha ▸ hab)))
      by_cases hb : b = v
      · exact Or.inl (Finset.mem_union_right S ((memN a).2 (hb ▸ hab.symm)))
      by_cases hna : G.Adj v a
      · exact Or.inl (Finset.mem_union_right S ((memN a).2 hna))
      by_cases hnb : G.Adj v b
      · exact Or.inr (Finset.mem_union_right S ((memN b).2 hnb))
      rcases hS a b hab ha hb hna hnb with h | h
      · exact Or.inl (Finset.mem_union_left N h)
      · exact Or.inr (Finset.mem_union_left N h)
    have hcard := Finset.card_union_le S N
    have hle := hmin (S ∪ N) hcover
    omega
  have lower : min (t1 + 1) (t2 + N.card) ≤ t := by
    obtain ⟨S, hS, hc⟩ := h0
    by_cases hv : v ∈ S
    · have hcover : ∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v →
          a ∈ S.erase v ∨ b ∈ S.erase v := by
        intro a b hab ha hb
        rcases hS a b hab with h | h
        · exact Or.inl (Finset.mem_erase.2 ⟨ha, h⟩)
        · exact Or.inr (Finset.mem_erase.2 ⟨hb, h⟩)
      have hle := hmin1 (S.erase v) hcover
      have hcard := Finset.card_erase_add_one hv
      have hm : min (t1 + 1) (t2 + N.card) ≤ t1 + 1 := min_le_left _ _
      omega
    · have hNS : N ⊆ S := by
        intro u hu
        rcases hS v u ((memN u).1 hu) with h | h
        · exact False.elim (hv h)
        · exact h
      have hcover : ∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v →
          ¬ G.Adj v a → ¬ G.Adj v b →
          a ∈ S \ N ∨ b ∈ S \ N := by
        intro a b hab _ _ hna hnb
        rcases hS a b hab with h | h
        · exact Or.inl (Finset.mem_sdiff.2 ⟨h, fun hn => hna ((memN a).1 hn)⟩)
        · exact Or.inr (Finset.mem_sdiff.2 ⟨h, fun hn => hnb ((memN b).1 hn)⟩)
      have hle := hmin2 (S \ N) hcover
      have hcard := Finset.card_sdiff_add_card_eq_card hNS
      have hm : min (t1 + 1) (t2 + N.card) ≤ t2 + N.card := min_le_right _ _
      omega
  change t = min (t1 + 1) (t2 + N.card)
  exact Nat.le_antisymm (le_min upper1 upper2) lower
