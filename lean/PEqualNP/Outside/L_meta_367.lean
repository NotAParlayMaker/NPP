import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_367

private abbrev Edge := Fin 6 × Fin 6

private def edges : List Edge := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)]

private def sets : Fin 5 → Finset (Fin 6) :=
  ![{0, 2, 4}, {1, 3, 5}, {0, 3}, {1, 4}, {2, 5}]

private theorem independent : ∀ i, ∀ e ∈ edges, ¬ (e.1 ∈ sets i ∧ e.2 ∈ sets i) := by
  decide

private theorem incompatible : ∀ i j, i ≠ j → ∃ e ∈ edges,
    e.1 ∈ sets i ∪ sets j ∧ e.2 ∈ sets i ∪ sets j := by
  decide

end PEqualNP.Outside.L_meta_367

open PEqualNP.Outside.L_meta_367

theorem PEqualNP.Outside.L_meta_367 : ∀ E : List (Fin 6 × Fin 6), E = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)] → ∀ O : Finset (Fin 6) → Finset (Fin 6 × Fin 6), (∀ J : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) → (∀ d ∈ O J, d ∈ E ∨ (d.2, d.1) ∈ E) ∧ (∀ e ∈ E, (e ∈ O J ∨ (e.2, e.1) ∈ O J) ∧ ¬ (e ∈ O J ∧ (e.2, e.1) ∈ O J)) ∧ (∀ d ∈ O J, d.2 ∉ J)) → PEqualNP.MetaComplexity.SingleLevel.vc E ≤ Module.finrank (ZMod 2) (vectorSpan (ZMod 2) {w : Fin 6 × Fin 6 → ZMod 2 | ∃ J : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) ∧ w = fun d => if d ∈ O J then 1 else 0}) := by
  intro E hE O hO
  subst E
  let w (i : Fin 5) (d : Edge) : ZMod 2 := if d ∈ O (sets i) then 1 else 0
  -- An orientation cannot avoid pointing into both sets of any distinct pair.
  have hw : Function.Injective w := by
    intro i j h
    by_contra hij
    obtain ⟨e, he, ha, hb⟩ := incompatible i j hij
    have hi := hO (sets i) (independent i)
    have hj := hO (sets j) (independent j)
    have transfer (d : Edge) (hd : d ∈ O (sets i)) : d ∈ O (sets j) := by
      by_contra hn
      have eq := congrFun h d
      simp [w, hd, hn] at eq
    have excludes (d : Edge) (hd : d ∈ O (sets i)) : d.2 ∉ sets i ∪ sets j := by
      simpa only [Finset.mem_union, not_or] using And.intro (hi.2.2 d hd) (hj.2.2 d (transfer d hd))
    rcases (hi.2.1 e he).1 with hf | hr
    · exact excludes e hf hb
    · exact excludes (e.2, e.1) hr ha
  let S : Set (Edge → ZMod 2) := {v | ∃ J : Finset (Fin 6),
    (∀ e ∈ edges, ¬ (e.1 ∈ J ∧ e.2 ∈ J)) ∧ v = fun d => if d ∈ O J then 1 else 0}
  let V := vectorSpan (ZMod 2) S
  have hmem (i : Fin 5) : w i ∈ S := ⟨sets i, independent i, rfl⟩
  -- Translation by one fixed point puts the five distinct points in the direction space.
  let f (i : Fin 5) : V := ⟨w i - w 0, vsub_mem_vectorSpan (ZMod 2) (hmem i) (hmem 0)⟩
  have hf : Function.Injective f := fun i j e => hw (sub_left_inj.mp (congrArg Subtype.val e))
  classical
  let _ := Fintype.ofFinite V
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card] at hcard
  have hdim : 3 ≤ Module.finrank (ZMod 2) V := by
    by_contra! hsmall
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show Module.finrank (ZMod 2) V ≤ 2 by omega)
    omega
  have hcover : PEqualNP.MetaComplexity.SingleLevel.vc edges ≤ 3 := by
    apply Nat.sInf_le
    exact ⟨{0, 2, 4}, by decide, by decide⟩
  exact hcover.trans hdim
