import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3765

-- kind 0: union of the two operands (an AND, or a copy when both operands agree);
-- kind 1: the empty set (a constant); any other kind: the operand picked by the choice bit.
def val (n m : ℕ) (kind a b : ℕ → ℕ) (c : Fin m → Bool) (w : ℕ) : Finset ℕ :=
  if w < n then {w}
  else if hk : w - n < m then
    if kind (w - n) = 0 then
      (if h1 : a (w - n) < w then val n m kind a b c (a (w - n)) else ∅) ∪
        (if h2 : b (w - n) < w then val n m kind a b c (b (w - n)) else ∅)
    else if kind (w - n) = 1 then ∅
    else if c ⟨w - n, hk⟩ = true then
      (if h1 : a (w - n) < w then val n m kind a b c (a (w - n)) else ∅)
    else (if h2 : b (w - n) < w then val n m kind a b c (b (w - n)) else ∅)
  else ∅
termination_by w

theorem val_input (n m : ℕ) (kind a b : ℕ → ℕ) (c : Fin m → Bool) (w : ℕ) (hw : w < n) :
    val n m kind a b c w = {w} := by
  rw [val, if_pos hw]

theorem val_and (n m : ℕ) (kind a b : ℕ → ℕ) (c : Fin m → Bool) (k : ℕ) (hk : k < m)
    (hkind : kind k = 0) (ha : a k < n + k) (hb : b k < n + k) :
    val n m kind a b c (n + k) = val n m kind a b c (a k) ∪ val n m kind a b c (b k) := by
  rw [val]
  have e : n + k - n = k := by omega
  have hn : ¬ n + k < n := by omega
  simp only [hn, if_false, e, hk, dif_pos, hkind, if_true, ha, hb]

theorem val_const (n m : ℕ) (kind a b : ℕ → ℕ) (c : Fin m → Bool) (k : ℕ) (hk : k < m)
    (hkind : kind k = 1) :
    val n m kind a b c (n + k) = ∅ := by
  rw [val]
  have e : n + k - n = k := by omega
  have hn : ¬ n + k < n := by omega
  simp only [hn, if_false, e, hk, dif_pos, hkind]
  simp

theorem val_or (n m : ℕ) (kind a b : ℕ → ℕ) (c : Fin m → Bool) (k : ℕ) (hk : k < m)
    (h0 : kind k ≠ 0) (h1 : kind k ≠ 1) (ha : a k < n + k) (hb : b k < n + k) :
    val n m kind a b c (n + k) =
      if c ⟨k, hk⟩ = true then val n m kind a b c (a k) else val n m kind a b c (b k) := by
  rw [val]
  have e : n + k - n = k := by omega
  have hn : ¬ n + k < n := by omega
  simp only [hn, if_false, e, hk, dif_pos, h0, h1, ha, hb]

-- The shape each gate has, with the chosen kind and second operand.
def Spec (n : ℕ) (S : ℕ → Set (Finset ℕ)) (kind a b : ℕ → ℕ) (k : ℕ) : Prop :=
  a k < n + k ∧ b k < n + k ∧
    ((kind k = 0 ∧ (S (n + k) = Set.image2 (fun s t : Finset ℕ => s ∪ t) (S (a k)) (S (b k)) ∨
        (S (n + k) = S (a k) ∧ b k = a k))) ∨
      (kind k = 1 ∧ S (n + k) = {∅}) ∨
      (kind k = 2 ∧ S (n + k) = S (a k) ∪ S (b k)))

theorem mem_all (n m : ℕ) (S : ℕ → Set (Finset ℕ)) (kind a b : ℕ → ℕ)
    (hin : ∀ i < n, S i = {{i}}) (hspec : ∀ k < m, Spec n S kind a b k) (c : Fin m → Bool) :
    ∀ w, w < n + m → val n m kind a b c w ∈ S w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [val_input n m kind a b c w hlt, hin w hlt]
      exact Set.mem_singleton _
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < m := by omega
      obtain ⟨ha, hb, hcase⟩ := hspec k hk
      rcases hcase with ⟨h0, hS | ⟨hS, hba⟩⟩ | ⟨h1, hS⟩ | ⟨h2, hS⟩
      · rw [val_and n m kind a b c k hk h0 ha hb, hS]
        exact Set.mem_image2_of_mem (ih _ ha (by omega)) (ih _ hb (by omega))
      · rw [val_and n m kind a b c k hk h0 ha hb, hS, hba, Finset.union_self]
        exact ih _ ha (by omega)
      · rw [val_const n m kind a b c k hk h1, hS]
        exact Set.mem_singleton _
      · rw [val_or n m kind a b c k hk (by omega) (by omega) ha hb, hS]
        split
        · exact Or.inl (ih _ ha (by omega))
        · exact Or.inr (ih _ hb (by omega))

open Classical in
theorem sub_all (n m : ℕ) (S : ℕ → Set (Finset ℕ)) (kind a b : ℕ → ℕ)
    (hin : ∀ i < n, S i = {{i}}) (hspec : ∀ k < m, Spec n S kind a b k) (M : Finset ℕ) :
    ∀ w, w < n + m → (∃ s ∈ S w, s ⊆ M) →
      val n m kind a b (fun k => decide (∃ s ∈ S (a k), s ⊆ M)) w ⊆ M := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hs
    obtain ⟨s, hsS, hsM⟩ := hs
    by_cases hlt : w < n
    · rw [val_input _ _ _ _ _ _ w hlt]
      rw [hin w hlt] at hsS
      rw [Set.mem_singleton_iff] at hsS
      rw [hsS] at hsM
      exact hsM
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < m := by omega
      obtain ⟨ha, hb, hcase⟩ := hspec k hk
      rcases hcase with ⟨h0, hS | ⟨hS, hba⟩⟩ | ⟨h1, hS⟩ | ⟨h2, hS⟩
      · rw [val_and _ _ _ _ _ _ k hk h0 ha hb]
        rw [hS] at hsS
        obtain ⟨s1, hs1, s2, hs2, rfl⟩ := hsS
        exact Finset.union_subset
          (ih _ ha (by omega) ⟨s1, hs1, (Finset.subset_union_left).trans hsM⟩)
          (ih _ hb (by omega) ⟨s2, hs2, (Finset.subset_union_right).trans hsM⟩)
      · rw [val_and _ _ _ _ _ _ k hk h0 ha hb, hba, Finset.union_self]
        rw [hS] at hsS
        exact ih _ ha (by omega) ⟨s, hsS, hsM⟩
      · rw [val_const _ _ _ _ _ _ k hk h1]
        exact Finset.empty_subset _
      · rw [val_or _ _ _ _ _ _ k hk (by omega) (by omega) ha hb]
        rw [hS] at hsS
        by_cases hA : ∃ s ∈ S (a k), s ⊆ M
        · have hd : decide (∃ s ∈ S (a k), s ⊆ M) = true := decide_eq_true hA
          simp only [hd, if_true]
          exact ih _ ha (by omega) hA
        · have hd : decide (∃ s ∈ S (a k), s ⊆ M) = false := decide_eq_false hA
          simp only [hd, Bool.false_eq_true, if_false]
          rcases hsS with hsA | hsB
          · exact absurd ⟨s, hsA, hsM⟩ hA
          · exact ih _ hb (by omega) ⟨s, hsB, hsM⟩

end PEqualNP.Outside.L_meta_3765

open PEqualNP.Outside.L_meta_3765

theorem PEqualNP.Outside.L_meta_3765 : ∀ (x1 x2 x3 : ℕ) (x4 : ℕ → Set (Finset ℕ)), x3 < x1 + x2 → (∀ x6 < x1, x4 x6 = {{x6}}) → (∀ x7 < x2, ∃ x9 < x1 + x7, ∃ x10 < x1 + x7, x4 (x1 + x7) = Set.image2 (fun (x11 x12 : Finset ℕ) => x11 ∪ x12) (x4 x9) (x4 x10) ∨ x4 (x1 + x7) = x4 x9 ∨ x4 (x1 + x7) = {∅} ∨ x4 (x1 + x7) = x4 x9 ∪ x4 x10) → ∃ (x8 : (Fin x2 → Bool) → ℕ → Finset ℕ), (∀ (x9 : Fin x2 → Bool), ∀ x10 < x1, x8 x9 x10 = {x10}) ∧ (∀ (x9 : Fin x2), ∃ x10 < x1 + ↑x9, ∃ x11 < x1 + ↑x9, (∀ (x12 : Fin x2 → Bool), x8 x12 (x1 + ↑x9) = x8 x12 x10 ∪ x8 x12 x11) ∨ (∀ (x12 : Fin x2 → Bool), x8 x12 (x1 + ↑x9) = if x12 x9 = Bool.true then x8 x12 x10 else x8 x12 x11) ∨ ∀ (x12 : Fin x2 → Bool), x8 x12 (x1 + ↑x9) = ∅) ∧ (∀ (x9 : Fin x2 → Bool), x8 x9 x3 ∈ x4 x3) ∧ ∀ x9 ∈ x4 x3, ∃ (x11 : Fin x2 → Bool), x8 x11 x3 ⊆ x9 := by
  intro x1 x2 x3 x4 hx3 hin hgate
  classical
  have hex : ∀ k, ∃ p : ℕ × ℕ × ℕ, k < x2 →
      Spec x1 x4 (fun _ => p.1) (fun _ => p.2.1) (fun _ => p.2.2) k := by
    intro k
    by_cases hk : k < x2
    · obtain ⟨A, hA, B, hB, hcase⟩ := hgate k hk
      rcases hcase with h | h | h | h
      · exact ⟨(0, A, B), fun _ => ⟨hA, hB, Or.inl ⟨rfl, Or.inl h⟩⟩⟩
      · exact ⟨(0, A, A), fun _ => ⟨hA, hA, Or.inl ⟨rfl, Or.inr ⟨h, rfl⟩⟩⟩⟩
      · exact ⟨(1, A, B), fun _ => ⟨hA, hB, Or.inr (Or.inl ⟨rfl, h⟩)⟩⟩
      · exact ⟨(2, A, B), fun _ => ⟨hA, hB, Or.inr (Or.inr ⟨rfl, h⟩)⟩⟩
    · exact ⟨(0, 0, 0), fun h => absurd h hk⟩
  choose f hf using hex
  let kind : ℕ → ℕ := fun k => (f k).1
  let a : ℕ → ℕ := fun k => (f k).2.1
  let b : ℕ → ℕ := fun k => (f k).2.2
  have hspec : ∀ k < x2, Spec x1 x4 kind a b k := fun k hk => hf k hk
  refine ⟨fun c w => val x1 x2 kind a b c w, ?_, ?_, ?_, ?_⟩
  · intro c w hw
    exact val_input x1 x2 kind a b c w hw
  · intro k
    obtain ⟨ha, hb, hcase⟩ := hspec k k.isLt
    refine ⟨a k, ha, b k, hb, ?_⟩
    rcases hcase with ⟨h0, _⟩ | ⟨h1, _⟩ | ⟨h2, _⟩
    · exact Or.inl fun c => val_and x1 x2 kind a b c k k.isLt h0 ha hb
    · exact Or.inr (Or.inr fun c => val_const x1 x2 kind a b c k k.isLt h1)
    · refine Or.inr (Or.inl fun c => ?_)
      show val x1 x2 kind a b c (x1 + ↑k) =
        if c k = true then val x1 x2 kind a b c (a k) else val x1 x2 kind a b c (b k)
      rw [val_or x1 x2 kind a b c k k.isLt (by omega) (by omega) ha hb]
  · intro c
    exact mem_all x1 x2 x4 kind a b hin hspec c x3 hx3
  · intro M hM
    exact ⟨_, sub_all x1 x2 x4 kind a b hin hspec M x3 hx3 ⟨M, hM, subset_refl M⟩⟩
