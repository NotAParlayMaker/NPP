import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1463

def P (i j : Fin 7) : Prop := j = i + 1 ∨ j = i + 2 ∨ j = i + 4

lemma P_asymm : ∀ i j : Fin 7, P i j → ¬ P j i := by
  unfold P; decide

lemma P_dom : ∀ x y : Fin 7, ∃ z : Fin 7, P z x ∧ P z y := by
  unfold P; decide

lemma cover {n : ℕ} (T : Finset (Fin n)) (d : Fin n) (h : T.card ≤ 2) :
    ∃ x y : Fin n, (x ∈ T ∨ x = d) ∧ (y ∈ T ∨ y = d) ∧ ∀ z ∈ T, z = x ∨ z = y := by
  rcases Nat.lt_or_ge T.card 1 with h0 | h1
  · have : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    exact ⟨d, d, Or.inr rfl, Or.inr rfl, by simp⟩
  rcases Nat.lt_or_ge T.card 2 with h2 | h2
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (show T.card = 1 by omega)
    exact ⟨a, a, by simp, by simp, by simp⟩
  · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp (show T.card = 2 by omega)
    exact ⟨a, b, by simp, by simp, by simp⟩

end PEqualNP.Outside.L_meta_1463

theorem PEqualNP.Outside.L_meta_1463 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (A : Finset (Fin n)),
    A.card = 7 → (∀ i : Fin m, (S i ∩ A).card ≤ 2) →
    ∃ (r : Fin n → Fin n → Prop) (f : Fin m → Fin n), (∀ a b : Fin n, r a b → ¬ r b a) ∧
      ∀ i : Fin m, f i ∈ A ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ A, r (f i) y := by
  intro n m S A hA hS
  let e := A.equivFinOfCardEq hA
  let r : Fin n → Fin n → Prop := fun a b =>
    ∃ (ha : a ∈ A) (hb : b ∈ A), PEqualNP.Outside.L_meta_1463.P (e ⟨a, ha⟩) (e ⟨b, hb⟩)
  have hr : ∀ a b : Fin n, r a b → ¬ r b a := by
    rintro a b ⟨ha, hb, h⟩ ⟨_, _, h'⟩
    exact PEqualNP.Outside.L_meta_1463.P_asymm _ _ h h'
  have hd : ∃ d, d ∈ A := Finset.card_pos.mp (by omega)
  obtain ⟨d, hd⟩ := hd
  have key : ∀ i : Fin m, ∃ z : Fin n, z ∈ A ∧ z ∉ S i ∧ ∀ y ∈ S i ∩ A, r z y := by
    intro i
    obtain ⟨x, y, hx, hy, hc⟩ := PEqualNP.Outside.L_meta_1463.cover (S i ∩ A) d (hS i)
    have hxA : x ∈ A := by
      rcases hx with hx | rfl
      · exact (Finset.mem_inter.mp hx).2
      · exact hd
    have hyA : y ∈ A := by
      rcases hy with hy | rfl
      · exact (Finset.mem_inter.mp hy).2
      · exact hd
    obtain ⟨z, hzx, hzy⟩ := PEqualNP.Outside.L_meta_1463.P_dom (e ⟨x, hxA⟩) (e ⟨y, hyA⟩)
    have hdom : ∀ w ∈ S i ∩ A, r (e.symm z : Fin n) w := by
      intro w hw
      rcases hc w hw with rfl | rfl
      · exact ⟨(e.symm z).2, hxA, by simpa using hzx⟩
      · exact ⟨(e.symm z).2, hyA, by simpa using hzy⟩
    refine ⟨e.symm z, (e.symm z).2, fun hs => ?_, hdom⟩
    have h := hdom _ (Finset.mem_inter.mpr ⟨hs, (e.symm z).2⟩)
    exact hr _ _ h h
  choose f hf using key
  exact ⟨r, f, hr, hf⟩
