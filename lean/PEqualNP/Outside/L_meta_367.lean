import Mathlib
import PEqualNP.Defs

namespace Gap367A

abbrev D := Fin 6 × Fin 6
abbrev E : List D := [(0,1),(1,2),(2,3),(3,4),(4,5),(0,5)]
def J : Fin 5 → Finset (Fin 6) := ![{0,2,4},{1,3,5},{0,3},{1,4},{2,5}]

lemma indep : ∀ i, ∀ f ∈ E, ¬ (f.1 ∈ J i ∧ f.2 ∈ J i) := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
lemma distinguish : ∀ i j, (∀ f ∈ E, ¬ ((f.1 ∈ J i ∨ f.1 ∈ J j) ∧
    (f.2 ∈ J i ∨ f.2 ∈ J j))) → i = j := by decide

lemma cover : PEqualNP.MetaComplexity.SingleLevel.vc E ≤ 3 := by
  apply Nat.sInf_le
  exact ⟨J 0, by decide, by decide⟩

end Gap367A

open Gap367A

theorem PEqualNP.Outside.L_meta_367 : ∀ E : List (Fin 6 × Fin 6), E = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)] → ∀ O : Finset (Fin 6) → Finset (Fin 6 × Fin 6), (∀ J : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) → (∀ d ∈ O J, d ∈ E ∨ (d.2, d.1) ∈ E) ∧ (∀ e ∈ E, (e ∈ O J ∨ (e.2, e.1) ∈ O J) ∧ ¬ (e ∈ O J ∧ (e.2, e.1) ∈ O J)) ∧ (∀ d ∈ O J, d.2 ∉ J)) → PEqualNP.MetaComplexity.SingleLevel.vc E ≤ Module.finrank (ZMod 2) (vectorSpan (ZMod 2) {w : Fin 6 × Fin 6 → ZMod 2 | ∃ J : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) ∧ w = fun d => if d ∈ O J then 1 else 0}) := by
  intro _ rfl O h
  let w (i : Fin 5) : D → ZMod 2 := fun d => if d ∈ O (J i) then 1 else 0
  let S : Set (D → ZMod 2) := {v | ∃ T : Finset (Fin 6),
    (∀ f ∈ Gap367A.E, ¬ (f.1 ∈ T ∧ f.2 ∈ T)) ∧
      v = fun d => if d ∈ O T then 1 else 0}
  have hw (i) : w i ∈ S := ⟨J i, indep i, rfl⟩
  have winj : Function.Injective w := by
    intro i j hij
    have eqO : O (J i) = O (J j) := by
      ext d
      have hd := congrFun hij d
      by_cases hi : d ∈ O (J i) <;> by_cases hj : d ∈ O (J j) <;>
        simp_all only [w, ite_true, ite_false, iff_self, one_ne_zero, zero_ne_one]
    apply distinguish i j
    intro f hf hp
    have noIn (d : D) (hd : d ∈ O (J i)) : ¬ (d.2 ∈ J i ∨ d.2 ∈ J j) :=
      not_or_intro ((h _ (indep i)).2.2 _ hd) ((h _ (indep j)).2.2 _ (eqO ▸ hd))
    rcases ((h _ (indep i)).2.1 f hf).1 with hd | hd
    · exact noIn _ hd hp.2
    · exact noIn _ hd hp.1
  let V := vectorSpan (ZMod 2) S
  let g (i : Fin 5) : V := ⟨w i - w 0, vsub_mem_vectorSpan (ZMod 2) (hw i) (hw 0)⟩
  have hg : Function.Injective g := by
    intro i j heq
    apply winj
    have hsub : w i - w 0 = w j - w 0 := congrArg Subtype.val heq
    simpa using congrArg (fun a => a + w 0) hsub
  classical
  let : Fintype V := Fintype.ofFinite _
  have hc := Fintype.card_le_of_injective g hg
  rw [Fintype.card_fin, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card] at hc
  apply cover.trans
  change 3 ≤ Module.finrank (ZMod 2) V
  by_contra! hlt
  have hle : Module.finrank (ZMod 2) V ≤ 2 := by omega
  have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hle
  omega
