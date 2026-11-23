import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_367

private abbrev V := Fin 6
private abbrev Dart := V × V
private def cycle : List Dart := [(0,1), (1,2), (2,3), (3,4), (4,5), (0,5)]
private def sets : Fin 5 → Finset V := ![{0,2,4}, {1,3,5}, {0,3}, {1,4}, {2,5}]

private theorem independent : ∀ i, ∀ f ∈ cycle, ¬ (f.1 ∈ sets i ∧ f.2 ∈ sets i) := by decide

-- Each two of the five independent sets force opposite directions on a shared edge.
set_option synthInstance.maxSize 10000 in
private theorem conflict : ∀ i j, i ≠ j → ∃ a b : V, a ∈ sets i ∧ b ∈ sets j ∧
    ((a,b) ∈ cycle ∨ (b,a) ∈ cycle) := by decide

end PEqualNP.Outside.L_meta_367

open PEqualNP.Outside.L_meta_367 in
theorem PEqualNP.Outside.L_meta_367 : ∀ E : List (Fin 6 × Fin 6), E = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)] → ∀ O : Finset (Fin 6) → Finset (Fin 6 × Fin 6), (∀ J : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) → (∀ d ∈ O J, d ∈ E ∨ (d.2, d.1) ∈ E) ∧ (∀ e ∈ E, (e ∈ O J ∨ (e.2, e.1) ∈ O J) ∧ ¬ (e ∈ O J ∧ (e.2, e.1) ∈ O J)) ∧ (∀ d ∈ O J, d.2 ∉ J)) → PEqualNP.MetaComplexity.SingleLevel.vc E ≤ Module.finrank (ZMod 2) (vectorSpan (ZMod 2) {w : Fin 6 × Fin 6 → ZMod 2 | ∃ J : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) ∧ w = fun d => if d ∈ O J then 1 else 0}) := by
  classical
  rintro E rfl O hO
  let W : Fin 5 → Dart → ZMod 2 := fun i d => if d ∈ O (sets i) then 1 else 0
  let S : Set (Dart → ZMod 2) := {w | ∃ J : Finset V,
    (∀ f ∈ cycle, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) ∧ w = fun d => if d ∈ O J then 1 else 0}
  let U := vectorSpan (ZMod 2) S
  have mem (i : Fin 5) : W i ∈ S := ⟨sets i, independent i, rfl⟩
  have inj : Function.Injective W := by
    intro i j h
    by_contra hij
    obtain ⟨a,b,ha,hb,he⟩ := conflict i j hij
    have hi := hO (sets i) (independent i)
    have hj := hO (sets j) (independent j)
    have hn : (b,a) ∉ O (sets i) := fun hm => hi.2.2 _ hm ha
    have hp : (a,b) ∈ O (sets i) := by
      rcases he with he | he
      · exact ((hi.2.1 (a,b) he).1).resolve_right hn
      · exact ((hi.2.1 (b,a) he).1).resolve_left hn
    have hq : (a,b) ∉ O (sets j) := fun hm => hj.2.2 _ hm hb
    simpa [W, hp, hq] using congrFun h (a,b)
  let into (i : Fin 5) : U := ⟨W i - W 0, vsub_mem_vectorSpan (ZMod 2) (mem i) (mem 0)⟩
  have hi : Function.Injective into := by
    intro i j h
    exact inj (sub_left_inj.mp (congrArg Subtype.val h : W i - W 0 = W j - W 0))
  have count := Nat.card_le_card_of_injective into hi
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥U), Nat.card_zmod, Nat.card_fin] at count
  have lower : 3 ≤ Module.finrank (ZMod 2) U := by
    by_contra! h
    have h' : 2 ^ Module.finrank (ZMod 2) U ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  apply le_trans _ lower
  exact Nat.sInf_le (show ∃ T : Finset V, PEqualNP.MetaComplexity.SingleLevel.IsCover cycle T ∧ T.card = 3 from
    ⟨{0,2,4}, by decide, by decide⟩)
