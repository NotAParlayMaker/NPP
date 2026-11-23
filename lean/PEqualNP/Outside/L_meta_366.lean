import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_366

def edges : List (Fin 5 × Fin 5) := [(0,1),(1,2),(2,3),(3,4),(0,4)]

def pair (i : Fin 5) : Finset (Fin 5) := {i, i + 2}

theorem independentPair : ∀ i : Fin 5, ∀ e ∈ edges,
    ¬ (e.1 ∈ pair i ∧ e.2 ∈ pair i) := by decide

theorem joinedPair : ∀ i j : Fin 5, i ≠ j → ∃ e ∈ edges,
    e.1 ∈ pair i ∪ pair j ∧ e.2 ∈ pair i ∪ pair j := by decide

end PEqualNP.Outside.L_meta_366

open PEqualNP.Outside

theorem PEqualNP.Outside.L_meta_366 :
    ∀ E : List (Fin 5 × Fin 5), E = [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)] →
    ∀ O : Finset (Fin 5) → Finset (Fin 5 × Fin 5),
    (∀ J : Finset (Fin 5), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) →
      (∀ d ∈ O J, d ∈ E ∨ (d.2, d.1) ∈ E) ∧
      (∀ e ∈ E, (e ∈ O J ∨ (e.2, e.1) ∈ O J) ∧ ¬ (e ∈ O J ∧ (e.2, e.1) ∈ O J)) ∧
      (∀ d ∈ O J, d.2 ∉ J)) →
    PEqualNP.MetaComplexity.SingleLevel.vc E ≤ Module.finrank (ZMod 2)
      (vectorSpan (ZMod 2) {w : Fin 5 × Fin 5 → ZMod 2 | ∃ J : Finset (Fin 5),
        (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) ∧ w = fun d => if d ∈ O J then 1 else 0}) := by
  classical
  intro E hE O hO
  subst E
  let S : Set (Fin 5 × Fin 5 → ZMod 2) := {w | ∃ J : Finset (Fin 5),
    (∀ f ∈ L_meta_366.edges, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) ∧
    w = fun d => if d ∈ O J then 1 else 0}
  let v (i : Fin 5) : Fin 5 × Fin 5 → ZMod 2 := fun d =>
    if d ∈ O (L_meta_366.pair i) then 1 else 0
  have hv (i : Fin 5) : v i ∈ S :=
    ⟨L_meta_366.pair i, L_meta_366.independentPair i, rfl⟩
  have inj : Function.Injective v := by
    intro i j heq
    by_contra hij
    obtain ⟨e, he, ha, hb⟩ := L_meta_366.joinedPair i j hij
    have hi := hO _ (L_meta_366.independentPair i)
    have hj := hO _ (L_meta_366.independentPair j)
    have avoid (d : Fin 5 × Fin 5) (hd : d ∈ O (L_meta_366.pair i)) :
        d.2 ∉ L_meta_366.pair i ∪ L_meta_366.pair j := by
      have hdj : d ∈ O (L_meta_366.pair j) := by
        by_contra hn
        have := congrFun heq d
        simp [v, hd, hn] at this
      exact fun hm => (Finset.mem_union.mp hm).elim (hi.2.2 d hd) (hj.2.2 d hdj)
    rcases (hi.2.1 e he).1 with h | h
    · exact avoid e h hb
    · exact avoid (e.2,e.1) h ha
  let V := vectorSpan (ZMod 2) S
  let f (i : Fin 5) : V := ⟨v i -ᵥ v 0, vsub_mem_vectorSpan (ZMod 2) (hv i) (hv 0)⟩
  have hf : Function.Injective f := by
    intro i j h
    apply inj
    have eqv : v i - v 0 = v j - v 0 := congrArg Subtype.val h
    calc
      v i = (v i - v 0) + v 0 := (sub_add_cancel _ _).symm
      _ = (v j - v 0) + v 0 := congrArg (fun t => t + v 0) eqv
      _ = v j := sub_add_cancel _ _
  have hcard := Fintype.card_le_of_injective f hf
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := ↥V), ZMod.card, Fintype.card_fin] at hcard
  have lb : 3 ≤ Module.finrank (ZMod 2) V := by
    by_contra! small
    have upper := Nat.pow_le_pow_right (by decide : 0 < 2) (show Module.finrank (ZMod 2) V ≤ 2 by omega)
    omega
  apply le_trans _ lb
  apply Nat.sInf_le
  exact ⟨({0,2,4} : Finset (Fin 5)), by decide, by decide⟩
