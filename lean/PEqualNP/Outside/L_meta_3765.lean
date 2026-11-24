import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3765

abbrev Nodes := Set (Finset Nat)

def source (m : Fin 3) (a b : Nodes) : Nodes :=
  if m = 0 then Set.image2 (fun x y => x ∪ y) a b else if m = 1 then a ∪ b else {∅}

def pick (m : Fin 3) (bit : Bool) (a b : Finset Nat) : Finset Nat :=
  if m = 0 then a ∪ b else if m = 1 then (if bit then a else b) else ∅

def value {n k : Nat} (a b : (j : Fin k) → Fin (n + j.val))
    (m : Fin k → Fin 3) (bits : Fin k → Bool) (i : Nat) : Finset Nat :=
  if h : i < n then {i}
  else if hk : i - n < k then
    let j : Fin k := ⟨i - n, hk⟩
    pick (m j) (bits j) (value a b m bits (a j).val) (value a b m bits (b j).val)
  else ∅
termination_by i
decreasing_by all_goals apply Nat.lt_of_lt_of_le (Fin.isLt _); omega

lemma input {n k : Nat} (a b : (j : Fin k) → Fin (n + j.val))
    (m : Fin k → Fin 3) (bits : Fin k → Bool) {i : Nat} (hi : i < n) :
    value a b m bits i = {i} := by rw [value]; simp [hi]

lemma gate {n k : Nat} (a b : (j : Fin k) → Fin (n + j.val))
    (m : Fin k → Fin 3) (bits : Fin k → Bool) (j : Fin k) :
    value a b m bits (n + j.val) = pick (m j) (bits j)
      (value a b m bits (a j).val) (value a b m bits (b j).val) := by
  rw [value]
  split
  · omega
  · split
    next hk =>
      have he : (⟨n + j.val - n, hk⟩ : Fin k) = j := Fin.ext (by simp)
      have ha := congrArg (fun x : Fin k => (a x).val) he
      have hb := congrArg (fun x : Fin k => (b x).val) he
      dsimp only at ha hb
      simp only [he, ha, hb]
    next hk => simp at hk

lemma good {A B : Nodes} {m : Fin 3} {a b : Finset Nat} (bit : Bool)
    (ha : a ∈ A) (hb : b ∈ B) : pick m bit a b ∈ source m A B := by
  fin_cases m <;> cases bit <;> simp_all [pick, source, Set.mem_image2] <;> exact ⟨a, ha, b, hb, rfl⟩

def fits (A : Nodes) (T : Finset Nat) : Prop := ∃ s ∈ A, s ⊆ T

lemma small {A B : Nodes} {T a b : Finset Nat} {m : Fin 3}
    (ha : fits A T → a ⊆ T) (hb : fits B T → b ⊆ T) :
    ∀ bit : Bool, (bit = true ↔ fits A T) → fits (source m A B) T →
      pick m bit a b ⊆ T := by
  intro bit hbit hs
  fin_cases m
  · obtain ⟨s, hs, ht⟩ := hs
    change s ∈ Set.image2 (fun x y : Finset Nat => x ∪ y) A B at hs
    obtain ⟨x, hx, y, hy, rfl⟩ := hs
    have hxy := Finset.union_subset_iff.mp ht
    exact Finset.union_subset (ha ⟨x, hx, hxy.1⟩) (hb ⟨y, hy, hxy.2⟩)
  · obtain ⟨s, hs, ht⟩ := hs
    change s ∈ A ∪ B at hs
    cases bit
    · apply hb
      rcases hs with hs | hs
      · exact False.elim (Bool.false_ne_true (hbit.2 ⟨s,hs,ht⟩))
      · exact ⟨s,hs,ht⟩
    · exact ha (hbit.1 rfl)
  · exact Finset.empty_subset _

end PEqualNP.Outside.L_meta_3765

open PEqualNP.Outside.L_meta_3765

theorem PEqualNP.Outside.L_meta_3765 : ∀ (x1 x2 x3 : ℕ) (x4 : ℕ → Set (Finset ℕ)), x3 < x1 + x2 → (∀ x6 < x1, x4 x6 = {{x6}}) → (∀ x7 < x2, ∃ x9 < x1 + x7, ∃ x10 < x1 + x7, x4 (x1 + x7) = Set.image2 (fun (x11 x12 : Finset ℕ) => x11 ∪ x12) (x4 x9) (x4 x10) ∨ x4 (x1 + x7) = x4 x9 ∨ x4 (x1 + x7) = {∅} ∨ x4 (x1 + x7) = x4 x9 ∪ x4 x10) → ∃ (x8 : (Fin x2 → Bool) → ℕ → Finset ℕ), (∀ (x9 : Fin x2 → Bool), ∀ x10 < x1, x8 x9 x10 = {x10}) ∧ (∀ (x9 : Fin x2), ∃ x10 < x1 + ↑x9, ∃ x11 < x1 + ↑x9, (∀ (x12 : Fin x2 → Bool), x8 x12 (x1 + ↑x9) = x8 x12 x10 ∪ x8 x12 x11) ∨ (∀ (x12 : Fin x2 → Bool), x8 x12 (x1 + ↑x9) = if x12 x9 = Bool.true then x8 x12 x10 else x8 x12 x11) ∨ ∀ (x12 : Fin x2 → Bool), x8 x12 (x1 + ↑x9) = ∅) ∧ (∀ (x9 : Fin x2 → Bool), x8 x9 x3 ∈ x4 x3) ∧ ∀ x9 ∈ x4 x3, ∃ (x11 : Fin x2 → Bool), x8 x11 x3 ⊆ x9 := by
  classical
  intro n k o S ho inputs gates
  have parents (j : Fin k) : ∃ (a b : Fin (n+j.val)) (m : Fin 3),
      S (n+j.val) = source m (S a.val) (S b.val) := by
    obtain ⟨a, ha, b, hb, h | h | h | h⟩ := gates j.val j.isLt
    · exact ⟨⟨a,ha⟩,⟨b,hb⟩,0,h⟩
    · exact ⟨⟨a,ha⟩,⟨a,ha⟩,1,by simpa [source] using h⟩
    · exact ⟨⟨a,ha⟩,⟨b,hb⟩,2,h⟩
    · exact ⟨⟨a,ha⟩,⟨b,hb⟩,1,h⟩
  choose a b m spec using parents
  refine ⟨value a b m, fun bits i hi => input a b m bits hi, ?_, ?_, ?_⟩
  · intro j
    refine ⟨(a j).val,(a j).isLt,(b j).val,(b j).isLt,?_⟩
    by_cases h : m j = 0
    · exact Or.inl (fun bits => by rw [gate]; simp [pick,h])
    · by_cases h' : m j = 1
      · exact Or.inr (Or.inl (fun bits => by rw [gate]; simp [pick,h,h']))
      · exact Or.inr (Or.inr (fun bits => by rw [gate]; simp [pick,h,h']))
  · intro bits
    suffices hall : ∀ i < n+k, value a b m bits i ∈ S i by exact hall o ho
    intro i hi
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      by_cases h : i < n
      · rw [input a b m bits h, inputs i h]; simp
      · let j : Fin k := ⟨i-n,by omega⟩
        have eqn : n + j.val = i := by dsimp [j]; omega
        rw [← eqn, gate, spec]
        exact good _ (ih _ (eqn ▸ (a j).isLt) (by have := (a j).isLt; omega))
          (ih _ (eqn ▸ (b j).isLt) (by have := (b j).isLt; omega))
  · intro T ht
    let bits := fun j : Fin k => decide (fits (S (a j).val) T)
    refine ⟨bits, ?_⟩
    suffices hall : ∀ i < n+k, fits (S i) T → value a b m bits i ⊆ T by
      exact hall o ho ⟨T,ht,Finset.Subset.rfl⟩
    intro i hi
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      by_cases h : i < n
      · rw [input a b m bits h, inputs i h]
        rintro ⟨s,hs,ht⟩
        simpa [Set.mem_singleton_iff.mp hs] using ht
      · let j : Fin k := ⟨i-n,by omega⟩
        have eqn : n + j.val = i := by dsimp [j]; omega
        rw [← eqn, gate, spec]
        exact small (ih _ (eqn ▸ (a j).isLt) (by have := (a j).isLt; omega))
          (ih _ (eqn ▸ (b j).isLt) (by have := (b j).isLt; omega))
          _ (by simp [bits])
