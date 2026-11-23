import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1463 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (A : Finset (Fin n)),
    A.card = 7 → (∀ i : Fin m, (S i ∩ A).card ≤ 2) →
    ∃ (r : Fin n → Fin n → Prop) (f : Fin m → Fin n), (∀ a b : Fin n, r a b → ¬ r b a) ∧
      ∀ i : Fin m, f i ∈ A ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ A, r (f i) y := by
  intro n m S A hA hS
  classical
  have e : A ≃ Fin 7 := Finset.equivFinOfCardEq hA
  have anti : ∀ x y : Fin 7, (y - x = 1 ∨ y - x = 2 ∨ y - x = 4) → ¬ (x - y = 1 ∨ x - y = 2 ∨ x - y = 4) := by
    decide
  have dom : ∀ T : Finset (Fin 7), T.card ≤ 2 → ∃ w : Fin 7, ∀ y ∈ T, (y - w = 1 ∨ y - w = 2 ∨ y - w = 4) := by
    decide +kernel
  have hT : ∀ i : Fin m, (Finset.univ.filter (fun k : Fin 7 => (e.symm k).val ∈ S i)).card ≤ 2 := by
    intro i
    refine le_trans ?_ (hS i)
    apply Finset.card_le_card_of_injOn (fun k => (e.symm k).val)
    · intro k hk
      exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hk).2, (e.symm k).2⟩
    · intro k1 _ k2 _ h
      exact e.symm.injective (Subtype.ext h)
  choose w hw using fun i : Fin m => dom _ (hT i)
  have key : ∀ i : Fin m, ∀ y ∈ S i ∩ A, ∃ (ha : (e.symm (w i)).val ∈ A) (hb : y ∈ A),
      (e ⟨y, hb⟩ - e ⟨(e.symm (w i)).val, ha⟩ = 1 ∨ e ⟨y, hb⟩ - e ⟨(e.symm (w i)).val, ha⟩ = 2 ∨
        e ⟨y, hb⟩ - e ⟨(e.symm (w i)).val, ha⟩ = 4) := by
    intro i y hy
    have hyA := (Finset.mem_inter.mp hy).2
    refine ⟨(e.symm (w i)).2, hyA, ?_⟩
    have h1 : e ⟨(e.symm (w i)).val, (e.symm (w i)).2⟩ = w i := by simp
    rw [h1]
    apply hw i
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact (Finset.mem_inter.mp hy).1
  refine ⟨fun a b => ∃ (ha : a ∈ A) (hb : b ∈ A),
    (e ⟨b, hb⟩ - e ⟨a, ha⟩ = 1 ∨ e ⟨b, hb⟩ - e ⟨a, ha⟩ = 2 ∨ e ⟨b, hb⟩ - e ⟨a, ha⟩ = 4),
    fun i => (e.symm (w i)).val, ?_, ?_⟩
  · rintro a b ⟨ha, hb, h⟩ ⟨hb', ha', h'⟩
    exact anti _ _ h h'
  · intro i
    refine ⟨(e.symm (w i)).2, ?_, key i⟩
    intro hin
    obtain ⟨ha, hb, h⟩ := key i _ (Finset.mem_inter.mpr ⟨hin, (e.symm (w i)).2⟩)
    exact anti _ _ h h
