import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5763

private theorem below_erase {s : Finset ℕ} {n : ℕ} (h : s ⊆ Finset.range (n+1)) :
    s.erase n ⊆ Finset.range n := by
  intro k hk
  obtain ⟨hne,hs⟩ := Finset.mem_erase.mp hk
  have hlt := Finset.mem_range.mp (h hs)
  apply Finset.mem_range.mpr
  omega

theorem bound {α : Type*} [DecidableEq α] (values : ℕ → Finset α) (left right : ℕ → ℕ)
    (n : ℕ) (joins roots : Finset ℕ)
    (hj : joins ⊆ Finset.range n) (hr : roots ⊆ Finset.range n)
    (leaf : ∀ k < n, k ∉ joins → (values k).card ≤ 1)
    (join : ∀ k ∈ joins, left k < k ∧ right k < k ∧ values k = values (left k) ∪ values (right k)) :
    (roots.biUnion values).card ≤ roots.card + joins.card := by
  induction n generalizing joins roots with
  | zero =>
    have : roots = ∅ := Finset.subset_empty.mp (by simpa using hr)
    simp [this]
  | succ n ih =>
    have nextLeaf (k : ℕ) (hk : k < n) (h : k ∉ joins.erase n) : (values k).card ≤ 1 := by
      apply leaf k (by omega)
      intro hm
      exact h (Finset.mem_erase.mpr ⟨by omega,hm⟩)
    have nextJoin (k : ℕ) (hk : k ∈ joins.erase n) := join k (Finset.mem_of_mem_erase hk)
    have take (s : Finset ℕ) (hs : s ⊆ Finset.range n) :=
      ih (joins.erase n) s (below_erase hj) hs nextLeaf nextJoin
    have he := below_erase hr
    by_cases hroot : n ∈ roots
    · have rootCount := Finset.card_erase_add_one hroot
      have unpack : roots.biUnion values = values n ∪ (roots.erase n).biUnion values := by
        rw [← Finset.biUnion_insert,Finset.insert_erase hroot]
      by_cases hjoin : n ∈ joins
      · obtain ⟨hl,hright,hval⟩ := join n hjoin
        let s := insert (left n) (insert (right n) (roots.erase n))
        have hs : s ⊆ Finset.range n := by
          simpa only [s,Finset.insert_subset_iff,Finset.mem_range] using And.intro hl (And.intro hright he)
        have same : roots.biUnion values = s.biUnion values := by
          rw [unpack,hval]
          simp only [s,Finset.biUnion_insert,Finset.union_assoc]
        have count1 := Finset.card_insert_le (left n) (insert (right n) (roots.erase n))
        have count2 := Finset.card_insert_le (right n) (roots.erase n)
        have joinCount := Finset.card_erase_add_one hjoin
        have result := take s hs
        rw [same]
        dsimp [s] at result ⊢
        omega
      · have size := leaf n (by omega) hjoin
        have result := take (roots.erase n) he
        rw [Finset.erase_eq_of_notMem hjoin] at result
        have upper := Finset.card_union_le (values n) ((roots.erase n).biUnion values)
        rw [unpack]
        omega
    · have result := take (roots.erase n) he
      rw [Finset.erase_eq_of_notMem hroot] at result
      exact result.trans (Nat.add_le_add_left (Finset.card_le_card (Finset.erase_subset n joins)) _)

end PEqualNP.Outside.L_meta_5763


theorem PEqualNP.Outside.L_meta_5763 : ∀ (x1 x2 x3 : ℕ) (x4 x5 : Finset ℕ) (x6 : ℕ → Finset (Fin x1 × Fin x2)) (x7 x8 : ℕ → ℕ), x4 ⊆ Finset.range x3 → x5 ⊆ Finset.range x3 → (∀ x11 < x3, x11 ∉ x4 → (x6 x11).card ≤ (1 : ℕ)) → (∀ x12 ∈ x4, x7 x12 < x12 ∧ x8 x12 < x12 ∧ x6 x12 = x6 (x7 x12) ∪ x6 (x8 x12)) → (x5.biUnion x6).card ≤ x5.card + x4.card := by
  intro n m k joins roots values left right
  exact PEqualNP.Outside.L_meta_5763.bound values left right k joins roots
