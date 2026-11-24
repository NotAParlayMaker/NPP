import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Insert

theorem PEqualNP.Outside.L_meta_4972 :
    ∀ (n m root : ℕ) (f : (Fin m → Bool) → ℕ → Finset ℕ),
    root < n + m →
    (∀ s, ∀ k < n, f s k = {k}) →
    (∀ i : Fin m, ∃ a < n + ↑i, ∃ b < n + ↑i,
      (∀ s, f s (n + ↑i) = f s a ∪ f s b) ∨
      (∀ s, f s (n + ↑i) = if s i = true then f s a else f s b) ∨
      ∀ s, f s (n + ↑i) = ∅) →
    ∀ (s : Fin m → Bool) (cut : ℕ),
      have mask : Fin m → Bool := fun i =>
        if ↑i < cut ∧ f s (n + ↑i) ⊆ f s root then s i else false
      f mask root ⊆ f (fun _ => false) root ∪ f s root ∧
        (m ≤ cut → f mask root = f s root) := by
  intro n m root f hr leaf gates s cut
  let mask : Fin m → Bool := fun i =>
    if ↑i < cut ∧ f s (n + ↑i) ⊆ f s root then s i else false
  let z : Fin m → Bool := fun _ => false
  have inv (k : ℕ) (hk : k < n + m) :
      (k < n + cut → f s k ⊆ f s root → f mask k = f s k) ∧
      f mask k ⊆ f z k ∪ f s root := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      by_cases hl : k < n
      · simp only [leaf _ _ hl]
        exact ⟨fun _ _ => trivial, Finset.subset_union_left⟩
      let i : Fin m := ⟨k - n, by omega⟩
      have ei : n + ↑i = k := by dsimp [i]; omega
      obtain ⟨a, ha, b, hb, gate⟩ := gates i
      rw [ei] at ha hb gate
      obtain ⟨ae, ab⟩ := ih a ha (lt_trans ha hk)
      obtain ⟨be, bb⟩ := ih b hb (lt_trans hb hk)
      rcases gate with g | g | g
      · constructor
        · intro hc hs
          rw [g s] at hs
          rw [g mask, g s, ae (by omega) (Finset.Subset.trans Finset.subset_union_left hs),
            be (by omega) (Finset.Subset.trans Finset.subset_union_right hs)]
        · rw [g mask, g z]
          intro t ht
          rcases Finset.mem_union.mp ht with ht | ht
          · rcases Finset.mem_union.mp (ab ht) with ht | ht
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ ht)
            · exact Finset.mem_union_right _ ht
          · rcases Finset.mem_union.mp (bb ht) with ht | ht
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ ht)
            · exact Finset.mem_union_right _ ht
      · have eqPart : k < n + cut → f s k ⊆ f s root → f mask k = f s k := by
          intro hc hs
          have hi : ↑i < cut ∧ f s (n + ↑i) ⊆ f s root := ⟨by omega, by simpa only [ei] using hs⟩
          have hm : mask i = s i := ite_eq_left hi
          rw [g mask, hm, g s]
          rw [g s] at hs
          by_cases ht : s i = true <;> simp only [ht, ite_true, ite_false] at hs ⊢
          · exact ae (by omega) hs
          · exact be (by omega) hs
        refine ⟨eqPart, ?_⟩
        by_cases hi : ↑i < cut ∧ f s (n + ↑i) ⊆ f s root
        · rw [ei] at hi
          rw [eqPart (by omega) hi.2]
          exact Finset.Subset.trans hi.2 Finset.subset_union_right
        · have hm : mask i = false := ite_eq_right hi
          simpa only [g mask, g z, hm, z, Bool.false_eq_true, ite_false] using bb
      · simp only [g]
        exact ⟨fun _ _ => trivial, Finset.empty_subset _⟩
  obtain ⟨he, hb⟩ := inv root hr
  exact ⟨hb, fun hc => he (by omega) (fun _ h => h)⟩
