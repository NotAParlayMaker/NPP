import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8421_aux

def D : List ℕ := [0, 5, 7, 17, 20]

def bad (f : Fin 42 → Bool) : Prop :=
  ∃ (a : Fin 42) (b : Fin 42), (a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ D) ∧
    f a = true ∧ f b = true

theorem md (l p : ℕ) (hp : p < 21) : (l + 21 + 21 - p) % 21 = (l + 21 - p) % 21 := by
  omega

theorem upd (f : Fin 42 → Bool) (i : Fin 42)
    (hf : ∀ g : Fin 42 → Bool, (∀ k, f k = true → g k = true) → ¬ bad g → g = f)
    (hg : ¬ bad (Function.update f i true)) : f i = true := by
  have h := hf (Function.update f i true) (by
    intro k hk
    by_cases h : k = i
    · subst h; simp
    · rw [Function.update_of_ne h]; exact hk) hg
  have h2 := congrFun h i
  simp at h2
  simpa using h2.symm

theorem main (S : Fin 21 → Finset (Fin 21))
    (hS : ∀ l p : Fin 21, p ∈ S l ↔ (l.val + 21 - p.val) % 21 ∈ D)
    (f : Fin 42 → Bool) (hnb : ¬ bad f)
    (hf : ∀ g : Fin 42 → Bool, (∀ k, f k = true → g k = true) → ¬ bad g → g = f) :
    ∃ X : Finset (Fin 21),
      PEqualNP.GenericRejection.zeroSet S (PEqualNP.HeptadCover.missLines S X) = X ∧
      List.ofFn f = PEqualNP.GenericRejection.incidenceInput X (PEqualNP.HeptadCover.missLines S X) := by
  let X : Finset (Fin 21) := Finset.univ.filter fun p => f ⟨p.val, by omega⟩ = true
  let Y : Finset (Fin 21) := Finset.univ.filter fun l => f ⟨l.val + 21, by omega⟩ = true
  have c1 : ∀ l p : Fin 21, f ⟨l.val + 21, by omega⟩ = true → f ⟨p.val, by omega⟩ = true →
      p ∉ S l := by
    intro l p hl hp hin
    apply hnb
    refine ⟨⟨p.val, by omega⟩, ⟨l.val + 21, by omega⟩, ⟨by simp, by simp, ?_⟩, hp, hl⟩
    rw [hS] at hin
    simp only
    rw [md _ _ p.isLt]
    exact hin
  have hY : PEqualNP.HeptadCover.missLines S X = Y := by
    ext l
    simp only [PEqualNP.HeptadCover.missLines, Finset.mem_filter, Finset.mem_univ, true_and, Y]
    constructor
    · intro hd
      apply upd f ⟨l.val + 21, by omega⟩ hf
      rintro ⟨a, b, ⟨ha, hb, hab⟩, h1, h2⟩
      have hne : a ≠ ⟨l.val + 21, by omega⟩ := by
        intro h; rw [h] at ha; simp at ha
      rw [Function.update_of_ne hne] at h1
      by_cases hbb : b = ⟨l.val + 21, by omega⟩
      · rw [hbb] at hab
        have hpin : (⟨a.val, ha⟩ : Fin 21) ∈ S l := by
          rw [hS]; simp only at hab; rw [md _ _ ha] at hab; exact hab
        have hpX : (⟨a.val, ha⟩ : Fin 21) ∈ X := by
          simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]; exact h1
        exact Finset.disjoint_left.mp hd hpin hpX
      · rw [Function.update_of_ne hbb] at h2
        exact hnb ⟨a, b, ⟨ha, hb, hab⟩, h1, h2⟩
    · intro hl
      rw [Finset.disjoint_left]
      intro p hp hpX
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at hpX
      exact c1 l p hl hpX hp
  refine ⟨X, ?_, ?_⟩
  · rw [hY]
    ext p
    simp only [PEqualNP.GenericRejection.zeroSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hall
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
      apply upd f ⟨p.val, by omega⟩ hf
      rintro ⟨a, b, ⟨ha, hb, hab⟩, h1, h2⟩
      have hne : b ≠ ⟨p.val, by omega⟩ := by
        intro h; rw [h] at hb; simp at hb; omega
      rw [Function.update_of_ne hne] at h2
      by_cases haa : a = ⟨p.val, by omega⟩
      · rw [haa] at hab
        have hl : (⟨b.val - 21, by omega⟩ : Fin 21) ∈ Y := by
          simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and]
          have : (⟨b.val - 21 + 21, by omega⟩ : Fin 42) = b := by ext; simp; omega
          rw [this]; exact h2
        apply hall _ hl
        rw [hS]
        simp only at hab ⊢
        have : b.val - 21 + 21 = b.val := by omega
        have e : (b.val - 21 + 21 - p.val) % 21 = (b.val + 21 - p.val) % 21 := by omega
        rw [e]; exact hab
      · rw [Function.update_of_ne haa] at h1
        exact hnb ⟨a, b, ⟨ha, hb, hab⟩, h1, h2⟩
    · intro hpX l hl
      simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and] at hl
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at hpX
      exact c1 l p hl hpX
  · rw [hY]
    simp only [PEqualNP.GenericRejection.incidenceInput]
    have e := List.ofFn_add (m := 21) (n := 21) (f := f)
    rw [e]
    congr 1
    · congr 1
      funext p
      simp [X]
      rfl
    · congr 1
      funext l
      simp [Y]
      rfl

end PEqualNP.Outside.L_meta_8421_aux

theorem PEqualNP.Outside.L_meta_8421 : let x1 : Type := Fin (21 : ℕ); have x2 : x1 → Finset x1 := fun (x2 : x1) => {x3 : x1 | (↑x2 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]}; have x3 : (Fin (42 : ℕ) → Bool) → Prop := fun (x3 : Fin (42 : ℕ) → Bool) => ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true; ∀ (x4 : Fin (42 : ℕ) → Bool),   ¬x3 x4 →     (∀ (x6 : Fin (42 : ℕ) → Bool), (∀ (x7 : Fin (42 : ℕ)), x4 x7 = Bool.true → x6 x7 = Bool.true) → ¬x3 x6 → x6 = x4) →       ∃ (x7 : Finset x1),         have x8 : Finset (Fin (21 : ℕ)) := PEqualNP.HeptadCover.missLines x2 x7;         PEqualNP.GenericRejection.zeroSet x2 x8 = x7 ∧ List.ofFn x4 = PEqualNP.GenericRejection.incidenceInput x7 x8 := by
  intro x1 x2 x3 x4 h1 h2
  exact PEqualNP.Outside.L_meta_8421_aux.main x2 (fun l p => by simp [x2, PEqualNP.Outside.L_meta_8421_aux.D]) x4 h1 h2
