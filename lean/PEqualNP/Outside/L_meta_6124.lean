import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6124

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6124

theorem PEqualNP.Outside.L_meta_6124 : ∀ (x1 : Type) (x2 x3 x4 : ℕ) (x5 : ℕ → Set x1) (x6 : Set x1), x4 < x2 + x3 → (∀ x8 < x2, ¬Disjoint (x5 x8) x6) → (∀ x9 < x3, ∃ x11 < x2 + x9, ∃ x12 < x2 + x9, x5 (x2 + x9) ∈ [x5 x11 ∪ x5 x12, x5 x11 ∩ x5 x12, x5 x11, ∅]) → Disjoint (x5 x4) x6 → ∀ x11 ∈ x5 x4, ∃ x13 < x3, ∃ x14 < x2 + x13, ∃ x15 < x2 + x13, x5 (x2 + x13) = x5 x14 ∩ x5 x15 ∧ ¬Disjoint (x5 x14) x6 ∧ ¬Disjoint (x5 x15) x6 ∧ Disjoint (x5 (x2 + x13)) x6 ∧ x11 ∈ x5 (x2 + x13) ∧ ∀ x16 < x2 + x13, x11 ∈ x5 x16 → ¬Disjoint (x5 x16) x6 := by
  intro X n m o S Q ho hin hg hd x hx
  classical
  have hex : ∃ w, w < n + m ∧ x ∈ S w ∧ Disjoint (S w) Q := ⟨o, ho, hx, hd⟩
  obtain ⟨hw, hxw, hdw⟩ := Nat.find_spec hex
  have hmin : ∀ w, w < Nat.find hex → x ∈ S w → ¬ Disjoint (S w) Q := by
    intro w hlt hxs hds
    exact Nat.find_min hex hlt ⟨by omega, hxs, hds⟩
  generalize Nat.find hex = w at hw hxw hdw hmin
  have hwn : n ≤ w := by
    by_contra hlt
    exact hin w (by omega) hdw
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  obtain ⟨a, ha, b, hb, h⟩ := hg j (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h
  · exfalso
    rw [h] at hxw hdw
    rcases hxw with hxa | hxb
    · exact hmin a ha hxa (hdw.mono_left Set.subset_union_left)
    · exact hmin b hb hxb (hdw.mono_left Set.subset_union_right)
  · have hxw' := hxw
    rw [h] at hxw'
    exact ⟨j, by omega, a, ha, b, hb, h, hmin a ha hxw'.1, hmin b hb hxw'.2, hdw, hxw, hmin⟩
  · exfalso
    rw [h] at hxw hdw
    exact hmin a ha hxw hdw
  · rw [h] at hxw
    exact hxw.elim
