import PEqualNP.Defs

/-! L-meta-3495: in a linear space where every line has q+1 points, if a set S of at most q lines
and a cover (points P, lines L) of every incidence satisfy P p → p lies on a line of S and no line
of S is in L, then P is exactly the union of S and L is exactly the complement of S. A line l
outside S that is not in L has all q+1 of its points on lines of S; distinct points of l land on
distinct lines of S (two lines sharing two points are equal), so q+1 ≤ q. -/

theorem PEqualNP.Outside.L_meta_3495 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) → ∀ (x7 : Finset (Fin x2)), x7.card ≤ x1 → ∀ (x9 x10 : Fin x2 → Prop), (∀ (x11 x12 : Fin x2), x3 x11 x12 → x9 x11 ∨ x10 x12) → (∀ (x12 : Fin x2), x9 x12 → ∃ x14 ∈ x7, x3 x12 x14) → (∀ x13 ∈ x7, ¬x10 x13) → (∀ (x14 : Fin x2), x9 x14 ↔ ∃ x15 ∈ x7, x3 x14 x15) ∧ ∀ (x14 : Fin x2), x10 x14 ↔ x14 ∉ x7 := by
  intro q N R inst hcard huniq S hS P L hcov hP hL
  refine ⟨fun p => ⟨hP p, fun ⟨l, hl, hpl⟩ => (hcov p l hpl).resolve_right (hL l hl)⟩,
    fun l => ⟨fun h hl => hL l hl h, fun hl => ?_⟩⟩
  by_contra hnl
  have hpt : ∀ p : { p : Fin N // R p l }, ∃ m : { m // m ∈ S }, R p.1 m.1 := by
    intro p
    obtain ⟨m, hm, hpm⟩ := hP p.1 ((hcov p.1 l p.2).resolve_right hnl)
    exact ⟨⟨m, hm⟩, hpm⟩
  choose f hf using hpt
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have hne' : a.1 ≠ b.1 := fun h => hne (Subtype.ext h)
    obtain ⟨k, _, hk⟩ := huniq a.1 b.1 hne'
    have hb : R b.1 (f a).1 := by rw [hab]; exact hf b
    have h1 : (f a).1 = k := hk _ ⟨hf a, hb⟩
    have h2 : l = k := hk _ ⟨a.2, b.2⟩
    exact hl (by rw [h2, ← h1]; exact (f a).2)
  have h3 := Fintype.card_le_of_injective f hinj
  have h4 : Fintype.card { m // m ∈ S } = S.card := Fintype.card_coe S
  rw [hcard l, h4] at h3
  omega
