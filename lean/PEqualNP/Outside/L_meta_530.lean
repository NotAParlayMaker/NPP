import Mathlib
import PEqualNP.Defs

private abbrev Input530 (n : ℕ) := Fin n → Bool

private def Rect530 {n : ℕ} (L : ℕ) (X Y : Finset (Input530 n)) : Prop :=
  ∃ (k : ℕ) (A B : Fin k → Finset (Input530 n)) (t : Fin k → Fin n),
    k ≤ L ∧ (∀ i, A i ⊆ X) ∧ (∀ i, B i ⊆ Y) ∧
    (∀ i, ∀ x ∈ A i, x (t i) = true) ∧ (∀ i, ∀ y ∈ B i, y (t i) = false) ∧
    ∀ x ∈ X, ∀ y ∈ Y, ∃! i : Fin k, x ∈ A i ∧ y ∈ B i

private lemma uniqueAppend530 {k l : ℕ} (P : Fin k → Prop) (Q : Fin l → Prop)
    (R : Fin (k + l) → Prop)
    (hl : ∀ i, R (Fin.castAdd l i) ↔ P i)
    (hr : ∀ i, R (Fin.natAdd k i) ↔ Q i)
    (h : ((∃! i, P i) ∧ (∀ j, ¬ Q j)) ∨ ((∀ i, ¬ P i) ∧ ∃! j, Q j)) :
    ∃! i, R i := by
  rcases h with ⟨⟨i, hi, huniq⟩, hnone⟩ | ⟨hnone, ⟨j, hj, huniq⟩⟩
  · refine ⟨i.castAdd l, (hl i).2 hi, ?_⟩
    intro z hz
    induction z using Fin.addCases with
    | left z => exact congrArg (Fin.castAdd l) (huniq z ((hl z).1 hz))
    | right z => exact (hnone z ((hr z).1 hz)).elim
  · refine ⟨j.natAdd k, (hr j).2 hj, ?_⟩
    intro z hz
    induction z using Fin.addCases with
    | left z => exact (hnone z ((hl z).1 hz)).elim
    | right z => exact congrArg (Fin.natAdd k) (huniq z ((hr z).1 hz))

private lemma combine530 {n l r : ℕ} {X Y X₁ Y₁ X₂ Y₂ : Finset (Input530 n)}
    (left : Rect530 l X₁ Y₁) (right : Rect530 r X₂ Y₂)
    (hx₁ : X₁ ⊆ X) (hy₁ : Y₁ ⊆ Y) (hx₂ : X₂ ⊆ X) (hy₂ : Y₂ ⊆ Y)
    (cover : ∀ x ∈ X, ∀ y ∈ Y, (x ∈ X₁ ∧ y ∈ Y₁) ∨ (x ∈ X₂ ∧ y ∈ Y₂))
    (disj : ∀ x ∈ X₁, ∀ y ∈ Y₁, ¬ (x ∈ X₂ ∧ y ∈ Y₂)) :
    Rect530 (l + r) X Y := by
  obtain ⟨k, A, B, t, hk, hA, hB, ht, hf, hu⟩ := left
  obtain ⟨j, C, D, s, hj, hC, hD, hs, hg, hv⟩ := right
  refine ⟨k + j, Fin.append A C, Fin.append B D, Fin.append t s, Nat.add_le_add hk hj,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left i => simpa using Finset.Subset.trans (hA i) hx₁
    | right i => simpa using Finset.Subset.trans (hC i) hx₂
  · intro i
    induction i using Fin.addCases with
    | left i => simpa using Finset.Subset.trans (hB i) hy₁
    | right i => simpa using Finset.Subset.trans (hD i) hy₂
  · intro i
    induction i using Fin.addCases with
    | left i => simpa using ht i
    | right i => simpa using hs i
  · intro i
    induction i using Fin.addCases with
    | left i => simpa using hf i
    | right i => simpa using hg i
  · intro x hx y hy
    apply uniqueAppend530 (fun i => x ∈ A i ∧ y ∈ B i) (fun i => x ∈ C i ∧ y ∈ D i)
      (fun i => x ∈ Fin.append A C i ∧ y ∈ Fin.append B D i)
      (by intro i; simp) (by intro i; simp)
    rcases cover x hx y hy with ⟨ha, hb⟩ | ⟨hc, hd⟩
    · exact Or.inl ⟨hu x ha y hb, fun i hi => disj x ha y hb ⟨hC i hi.1, hD i hi.2⟩⟩
    · exact Or.inr ⟨fun i hi => disj x (hA i hi.1) y (hB i hi.2) ⟨hc, hd⟩, hv x hc y hd⟩

private def Positive530 {n : ℕ} (φ : PEqualNP.MetaComplexity.DMFormula n) : Prop :=
  PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop)
    (fun _ c => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ

private lemma partition530 {n : ℕ} (φ : PEqualNP.MetaComplexity.DMFormula n)
    (pos : Positive530 φ) (X Y : Finset (Input530 n))
    (good : ∀ x ∈ X, φ.eval x = true) (bad : ∀ y ∈ Y, φ.eval y = false) :
    Rect530 φ.leaves X Y := by
  classical
  induction φ generalizing X Y with
  | lit i c =>
    change c = true at pos
    subst c
    refine ⟨1, fun _ => X, fun _ => Y, fun _ => i, le_rfl,
      fun _ => Finset.Subset.rfl, fun _ => Finset.Subset.rfl, ?_, ?_, ?_⟩
    · exact fun _ => good
    · exact fun _ => bad
    · intro x hx y hy
      exact ⟨0, ⟨hx, hy⟩, fun j _ => Subsingleton.elim j 0⟩
  | and f g ihf ihg =>
    let Y₁ := Y.filter (fun y => f.eval y = false)
    let Y₂ := Y.filter (fun y => f.eval y = true)
    have left := ihf pos.1 X Y₁ (fun x hx => (Bool.and_eq_true_iff.mp (good x hx)).1)
      (fun y hy => (Finset.mem_filter.mp hy).2)
    have right := ihg pos.2 X Y₂ (fun x hx => (Bool.and_eq_true_iff.mp (good x hx)).2) (by
      intro y hy
      obtain ⟨hy', hf⟩ := Finset.mem_filter.mp hy
      have h := bad y hy'
      simpa [PEqualNP.MetaComplexity.DMFormula.eval, hf] using h)
    apply combine530 left right Finset.Subset.rfl (Finset.filter_subset _ _)
      Finset.Subset.rfl (Finset.filter_subset _ _)
    · intro x hx y hy
      cases he : f.eval y with
      | false => exact Or.inl ⟨hx, Finset.mem_filter.mpr ⟨hy, he⟩⟩
      | true => exact Or.inr ⟨hx, Finset.mem_filter.mpr ⟨hy, he⟩⟩
    · intro x hx y hy h
      have hf : f.eval y = false := (Finset.mem_filter.mp hy).2
      have ht : f.eval y = true := (Finset.mem_filter.mp h.2).2
      simp [hf] at ht
  | or f g ihf ihg =>
    let X₁ := X.filter (fun x => f.eval x = true)
    let X₂ := X.filter (fun x => f.eval x = false)
    have left := ihf pos.1 X₁ Y (fun x hx => (Finset.mem_filter.mp hx).2)
      (fun y hy => (Bool.or_eq_false_iff.mp (bad y hy)).1)
    have right := ihg pos.2 X₂ Y (by
      intro x hx
      obtain ⟨hx', hf⟩ := Finset.mem_filter.mp hx
      have h := good x hx'
      simpa [PEqualNP.MetaComplexity.DMFormula.eval, hf] using h)
      (fun y hy => (Bool.or_eq_false_iff.mp (bad y hy)).2)
    apply combine530 left right (Finset.filter_subset _ _) Finset.Subset.rfl
      (Finset.filter_subset _ _) Finset.Subset.rfl
    · intro x hx y hy
      cases he : f.eval x with
      | false => exact Or.inr ⟨Finset.mem_filter.mpr ⟨hx, he⟩, hy⟩
      | true => exact Or.inl ⟨Finset.mem_filter.mpr ⟨hx, he⟩, hy⟩
    · intro x hx y hy h
      have ht : f.eval x = true := (Finset.mem_filter.mp hx).2
      have hf : f.eval x = false := (Finset.mem_filter.mp h.1).2
      simp [hf] at ht

theorem PEqualNP.Outside.L_meta_530 : ∀ (n : ℕ) (φ : PEqualNP.MetaComplexity.DMFormula n), PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop) (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ → ∀ (X Y : Finset (Fin n → Bool)), (∀ x ∈ X, φ.eval x = true) → (∀ y ∈ Y, φ.eval y = false) → ∃ (k : ℕ) (A B : Fin k → Finset (Fin n → Bool)) (t : Fin k → Fin n), k ≤ φ.leaves ∧ (∀ i : Fin k, ∀ x ∈ A i, x (t i) = true) ∧ (∀ i : Fin k, ∀ y ∈ B i, y (t i) = false) ∧ ∀ x ∈ X, ∀ y ∈ Y, ∃! i : Fin k, x ∈ A i ∧ y ∈ B i := by
  intro n φ pos X Y good bad
  obtain ⟨k, A, B, t, hle, _, _, hA, hB, unique⟩ := partition530 φ pos X Y good bad
  exact ⟨k, A, B, t, hle, hA, hB, unique⟩
