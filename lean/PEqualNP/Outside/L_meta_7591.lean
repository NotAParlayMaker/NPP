import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7591

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_7591

theorem PEqualNP.Outside.L_meta_7591 : ∀ (x1 x2 x3 : ℕ) (x4 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))), (0 : ℕ) < x1 → (∀ (x6 : Fin x2), x4 ↑x6 = {x7 : (Fin x2 → Bool) × (Fin x2 → Bool) | x7.1 x6 = Bool.true} ∧ x4 (x2 + ↑x6) = {x7 : (Fin x2 → Bool) × (Fin x2 → Bool) | x7.2 x6 = Bool.true}) → (∀ x7 < x3, ∃ (x9 : ℕ) (x10 : ℕ), Max.max x9 x10 < x2 + x2 + x7 ∧ x4 (x2 + x2 + x7) ∈ [x4 x9 ∪ x4 x10, x4 x9, ∅, x4 x9 ∩ x4 x10]) → ∃ (x8 : ℕ → Set (Finset (Fin x2) × Finset (Fin x2))), (∀ (x9 : Fin x2), x8 ↑x9 = {({x9}, ∅)} ∧ x8 (x2 + ↑x9) = {(∅, {x9})}) ∧ (∀ x9 < x3, ∃ (x11 : ℕ) (x12 : ℕ), Max.max x11 x12 < x2 + x2 + x9 ∧ x8 (x2 + x2 + x9) ∈ [x8 x11 ∪ x8 x12, x8 x11, ∅, {x13 : Finset (Fin x2) × Finset (Fin x2) | x13 ∈ Set.image2 (fun (x14 x15 : Finset (Fin x2) × Finset (Fin x2)) => x14 ⊔ x15) (x8 x11) (x8 x12) ∧ x13.2.card ≤ x1}]) ∧ ∀ x9 < x2 + x2 + x3, ∀ (x11 x12 : Fin x2 → Bool), Fintype.card { x13 : Fin x2 // x12 x13 = Bool.true } ≤ x1 → ((x11, x12) ∈ x4 x9 ↔ ∃ x14 ∈ x8 x9, (∀ x15 ∈ x14.1, x11 x15 = Bool.true) ∧ ∀ x15 ∈ x14.2, x12 x15 = Bool.true) := by
  intro q n k V hq hin hg
  classical
  have key : ∀ i ≤ k, ∃ W : ℕ → Set (Finset (Fin n) × Finset (Fin n)), (∀ p : Fin n, W p = {({p}, ∅)} ∧ W (n + p) = {(∅, {p})}) ∧
      (∀ j < i, ∃ a b : ℕ, max a b < n + n + j ∧ W (n + n + j) ∈ [W a ∪ W b, W a, ∅, {s | s ∈ Set.image2 (fun u v : Finset (Fin n) × Finset (Fin n) => u ⊔ v) (W a) (W b) ∧ s.2.card ≤ q}]) ∧
      ∀ w < n + n + i, ∀ x y : Fin n → Bool, Fintype.card {l : Fin n // y l = true} ≤ q →
        ((x, y) ∈ V w ↔ ∃ s ∈ W w, (∀ p ∈ s.1, x p = true) ∧ ∀ l ∈ s.2, y l = true) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨fun w => if h : w < n then {({⟨w, h⟩}, ∅)} else if h2 : w - n < n then {(∅, {⟨w - n, h2⟩})} else ∅, fun p => ⟨?_, ?_⟩, fun j hj => by omega, ?_⟩
      · simp only [p.isLt, dite_true, Fin.eta]
      · have h1 : ¬ (n + (p : ℕ) < n) := by omega
        have h2 : n + (p : ℕ) - n < n := by have := p.isLt; omega
        simp only [h1, dite_false, h2, dite_true, Nat.add_sub_cancel_left, Fin.eta]
        simp [p.isLt]
      · intro w hw x y _
        by_cases h : w < n
        · have e := (hin ⟨w, h⟩).1
          simp only at e
          rw [e]
          simp [h]
        · have h2 : w - n < n := by omega
          have e := (hin ⟨w - n, h2⟩).2
          simp only [show n + (w - n) = w by omega] at e
          rw [e]
          simp [h, h2]
    | succ i ih =>
      intro hi
      obtain ⟨W, w1, w2, w3⟩ := ih (by omega)
      obtain ⟨a, b, hab, hval⟩ := hg i (by omega)
      have ha : a < n + n + i := lt_of_le_of_lt (le_max_left _ _) hab
      have hb : b < n + n + i := lt_of_le_of_lt (le_max_right _ _) hab
      have fin : ∀ Z : Set (Finset (Fin n) × Finset (Fin n)), Z ∈ [W a ∪ W b, W a, ∅, {s | s ∈ Set.image2 (fun u v : Finset (Fin n) × Finset (Fin n) => u ⊔ v) (W a) (W b) ∧ s.2.card ≤ q}] →
          (∀ x y : Fin n → Bool, Fintype.card {l : Fin n // y l = true} ≤ q → ((x, y) ∈ V (n + n + i) ↔ ∃ s ∈ Z, (∀ p ∈ s.1, x p = true) ∧ ∀ l ∈ s.2, y l = true)) →
          ∃ W : ℕ → Set (Finset (Fin n) × Finset (Fin n)), (∀ p : Fin n, W p = {({p}, ∅)} ∧ W (n + p) = {(∅, {p})}) ∧
      (∀ j < i + 1, ∃ a b : ℕ, max a b < n + n + j ∧ W (n + n + j) ∈ [W a ∪ W b, W a, ∅, {s | s ∈ Set.image2 (fun u v : Finset (Fin n) × Finset (Fin n) => u ⊔ v) (W a) (W b) ∧ s.2.card ≤ q}]) ∧
      ∀ w < n + n + (i + 1), ∀ x y : Fin n → Bool, Fintype.card {l : Fin n // y l = true} ≤ q →
        ((x, y) ∈ V w ↔ ∃ s ∈ W w, (∀ p ∈ s.1, x p = true) ∧ ∀ l ∈ s.2, y l = true) := by
        intro Z hZ hsem
        have upd : ∀ w < n + n + i, Function.update W (n + n + i) Z w = W w := fun w hw => Function.update_of_ne (by omega) _ _
        refine ⟨Function.update W (n + n + i) Z, fun p => ?_, ?_, ?_⟩
        · have := p.isLt
          rw [upd _ (by omega), upd _ (by omega)]
          exact w1 p
        · intro j hj
          by_cases hje : j = i
          · subst hje
            refine ⟨a, b, hab, ?_⟩
            rw [Function.update_self, upd a ha, upd b hb]
            exact hZ
          · obtain ⟨c, d, hcd, h⟩ := w2 j (by omega)
            have hc := lt_of_le_of_lt (le_max_left c d) hcd
            have hd := lt_of_le_of_lt (le_max_right c d) hcd
            refine ⟨c, d, hcd, ?_⟩
            rw [upd (n + n + j) (by omega), upd c (by omega), upd d (by omega)]
            exact h
        · intro w hw x y hy
          by_cases hwe : w = n + n + i
          · subst hwe; rw [Function.update_self]; exact hsem x y hy
          · rw [upd w (by omega)]; exact w3 w (by omega) x y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hval
      rcases hval with hval | hval | hval | hval
      · refine fin (W a ∪ W b) (by simp) fun x y hy => ?_
        rw [hval, Set.mem_union, w3 a ha x y hy, w3 b hb x y hy]
        constructor
        · rintro (⟨s, hs, h⟩ | ⟨s, hs, h⟩)
          · exact ⟨s, Or.inl hs, h⟩
          · exact ⟨s, Or.inr hs, h⟩
        · rintro ⟨s, hs | hs, h⟩
          · exact Or.inl ⟨s, hs, h⟩
          · exact Or.inr ⟨s, hs, h⟩
      · refine fin (W a) (by simp) fun x y hy => ?_
        rw [hval]; exact w3 a ha x y hy
      · refine fin ∅ (by simp) fun x y hy => ?_
        rw [hval]; simp
      · refine fin {s | s ∈ Set.image2 (fun u v : Finset (Fin n) × Finset (Fin n) => u ⊔ v) (W a) (W b) ∧ s.2.card ≤ q} (by simp) fun x y hy => ?_
        rw [hval, Set.mem_inter_iff, w3 a ha x y hy, w3 b hb x y hy]
        constructor
        · rintro ⟨⟨s, hs, s1, s2⟩, ⟨u, hu, u1, u2⟩⟩
          have y2 : ∀ l ∈ (s ⊔ u).2, y l = true := by
            intro l hl
            rw [Prod.snd_sup, Finset.sup_eq_union, Finset.mem_union] at hl
            exact hl.elim (s2 l) (u2 l)
          refine ⟨s ⊔ u, ⟨⟨s, hs, u, hu, rfl⟩, ?_⟩, ?_, y2⟩
          · refine le_trans ?_ hy
            rw [Fintype.card_subtype]
            exact Finset.card_le_card fun l hl => by simpa using y2 l hl
          · intro p hp
            rw [Prod.fst_sup, Finset.sup_eq_union, Finset.mem_union] at hp
            exact hp.elim (s1 p) (u1 p)
        · rintro ⟨_, ⟨⟨s, hs, u, hu, rfl⟩, _⟩, h1, h2⟩
          refine ⟨⟨s, hs, fun p hp => h1 p ?_, fun l hl => h2 l ?_⟩, ⟨u, hu, fun p hp => h1 p ?_, fun l hl => h2 l ?_⟩⟩
          · exact Finset.mem_union_left _ hp
          · exact Finset.mem_union_left _ hl
          · exact Finset.mem_union_right _ hp
          · exact Finset.mem_union_right _ hl
  exact key k le_rfl
