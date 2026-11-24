import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3245

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

private def bipartOk (x1 x4 : ℕ) (own : List (ℕ × List ℕ)) : Prop :=
  ∀ p ∈ own, p.2 ≠ [] ∧
    ((p.1 < x1 ∧ ∀ v ∈ p.2, x1 ≤ v ∧ v < x4) ∨
     (x1 ≤ p.1 ∧ p.1 < x4 ∧ ∀ v ∈ p.2, v < x1))

private def x8Gates (x1 B : ℕ) (lead : Bool) (a : ℕ) : List (ℕ × List ℕ) → Finset ℕ
  | [] => ∅
  | (_, []) :: os => x8Gates x1 B lead a os
  | (t, v1 :: rest) :: os =>
      let len := (blockGates B a t v1 rest lead).length
      (if x1 ≤ t then (Finset.range rest.length).image (fun i => B + i) else ∅) ∪
        x8Gates x1 (B + len) false (B + len - 1) os

private def x9Gates (x1 B : ℕ) (lead : Bool) (a : ℕ) : List (ℕ × List ℕ) → Finset ℕ
  | [] => ∅
  | (_, []) :: os => x9Gates x1 B lead a os
  | (t, v1 :: rest) :: os =>
      let len := (blockGates B a t v1 rest lead).length
      (if t < x1 then (Finset.range rest.length).image (fun i => B + i) else ∅) ∪
        x9Gates x1 (B + len) false (B + len - 1) os

private lemma blockGates_len (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v1 rest lead).length = rest.length + 1 + (if lead then 0 else 1) := by
  unfold blockGates
  cases lead <;> simp [Nat.add_assoc]

private lemma blockGates_andOr (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    ∀ g ∈ blockGates B a t v1 rest lead, g.op = GateOp.or ∨ g.op = GateOp.and := by
  intro g hg
  unfold blockGates at hg
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons] at hg
  rcases hg with ⟨i, _, rfl⟩ | rfl | htail
  · exact Or.inl rfl
  · exact Or.inr rfl
  · cases lead <;> simp at htail
    rcases htail with rfl
    exact Or.inl rfl

private lemma coverGatesB_andOr (B : ℕ) (lead : Bool) (a : ℕ) (own : List (ℕ × List ℕ)) :
    ∀ g ∈ coverGatesB B lead a own, g.op = GateOp.or ∨ g.op = GateOp.and := by
  induction own generalizing B lead a with
  | nil => simp [coverGatesB]
  | cons p os ih =>
    rcases p with ⟨t, L⟩
    rcases L with _ | ⟨v1, rest⟩
    · simp only [coverGatesB]
      exact ih B lead a
    · simp only [coverGatesB, List.mem_append]
      intro g hg
      rcases hg with hg | hg
      · exact blockGates_andOr B a t v1 rest lead g hg
      · exact ih _ false _ g hg

private lemma blockGates_len2 (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    ∀ g ∈ blockGates B a t v1 rest lead, g.inputs.length = 2 := by
  intro g hg
  unfold blockGates at hg
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons] at hg
  rcases hg with ⟨i, _, rfl⟩ | rfl | htail
  · rfl
  · rfl
  · cases lead <;> simp at htail
    rcases htail with rfl
    rfl

private lemma coverGatesB_len2 (B : ℕ) (lead : Bool) (a : ℕ) (own : List (ℕ × List ℕ)) :
    ∀ g ∈ coverGatesB B lead a own, g.inputs.length = 2 := by
  induction own generalizing B lead a with
  | nil => simp [coverGatesB]
  | cons p os ih =>
    rcases p with ⟨t, L⟩
    rcases L with _ | ⟨v1, rest⟩
    · simp only [coverGatesB]
      exact ih B lead a
    · simp only [coverGatesB, List.mem_append]
      intro g hg
      rcases hg with hg | hg
      · exact blockGates_len2 B a t v1 rest lead g hg
      · exact ih _ false _ g hg

private lemma getD_chain_lt (v1 : ℕ) (B m i : ℕ) (hv1 : v1 < B) (hi : i ≤ m) :
    (v1 :: (List.range m).map (fun j => B + j)).getD i 0 < B + i := by
  rcases i with _ | i
  · simp [hv1]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_map,
      List.getElem?_range (by omega : i < m), Option.map_some, Option.getD_some]
    omega

private lemma blockGates_readsBack (x4 B : ℕ) (lead : Bool) (a t v1 : ℕ) (rest : List ℕ)
    (hB : x4 ≤ B) (ha : lead = false → a < B) (ht : t < x4) (hv1 : v1 < x4)
    (hrest : ∀ v ∈ rest, v < x4) :
    ∀ j < (blockGates B a t v1 rest lead).length,
      ∀ u ∈ ((blockGates B a t v1 rest lead).getD j ⟨GateOp.or, []⟩).inputs, u < B + j := by
  intro j hj u hu
  rw [blockGates_len] at hj
  have hlt : j < rest.length ∨ j = rest.length ∨ (lead = false ∧ j = rest.length + 1) := by
    cases lead
    · have hle : j ≤ rest.length + 1 := by simpa using hj
      rcases Nat.lt_or_eq_of_le hle with hlt1 | heq1
      · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt1) with hlt2 | rfl
        · exact Or.inl hlt2
        · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨rfl, heq1⟩)
    · have hle : j ≤ rest.length := by simpa using hj
      rcases Nat.lt_or_eq_of_le hle with hlt1 | rfl
      · exact Or.inl hlt1
      · exact Or.inr (Or.inl rfl)
  unfold blockGates at hu
  rcases hlt with hj1 | rfl | ⟨hlead, rfl⟩
  · have hget : ((List.range rest.length).map (fun i =>
        Gate.mk GateOp.or [(v1 :: (List.range rest.length).map (fun k => B + k)).getD i 0, rest.getD i 0]) ++
        Gate.mk GateOp.and [t, (v1 :: (List.range rest.length).map (fun k => B + k)).getD rest.length 0] ::
        (if lead then [] else [Gate.mk GateOp.or [a, B + rest.length]])).getD j ⟨GateOp.or, []⟩ =
        Gate.mk GateOp.or [(v1 :: (List.range rest.length).map (fun k => B + k)).getD j 0, rest.getD j 0] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hj1])]
      simp only [List.getElem?_map, List.getElem?_range hj1, Option.map_some, Option.getD_some]
    rw [hget] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact getD_chain_lt v1 B rest.length j (by omega) (by omega)
    · have := hrest (rest.getD j 0) (by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_getElem hj1, Option.getD_some]
        exact List.getElem_mem hj1)
      omega
  · have hget : ((List.range rest.length).map (fun i =>
        Gate.mk GateOp.or [(v1 :: (List.range rest.length).map (fun k => B + k)).getD i 0, rest.getD i 0]) ++
        Gate.mk GateOp.and [t, (v1 :: (List.range rest.length).map (fun k => B + k)).getD rest.length 0] ::
        (if lead then [] else [Gate.mk GateOp.or [a, B + rest.length]])).getD rest.length ⟨GateOp.or, []⟩ =
        Gate.mk GateOp.and [t, (v1 :: (List.range rest.length).map (fun k => B + k)).getD rest.length 0] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
      simp only [List.length_map, List.length_range, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    rw [hget] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · omega
    · exact getD_chain_lt v1 B rest.length rest.length (by omega) (le_refl _)
  · subst hlead
    have hget : ((List.range rest.length).map (fun i =>
        Gate.mk GateOp.or [(v1 :: (List.range rest.length).map (fun k => B + k)).getD i 0, rest.getD i 0]) ++
        Gate.mk GateOp.and [t, (v1 :: (List.range rest.length).map (fun k => B + k)).getD rest.length 0] ::
        [Gate.mk GateOp.or [a, B + rest.length]]).getD (rest.length + 1) ⟨GateOp.or, []⟩ =
        Gate.mk GateOp.or [a, B + rest.length] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
      simp only [List.length_map, List.length_range, Nat.add_sub_cancel_left,
        List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    simp only [Bool.false_eq_true, ↓reduceIte] at hu
    rw [hget] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · have := ha rfl; omega
    · omega

private lemma coverGatesB_readsBack (x4 B : ℕ) (lead : Bool) (a : ℕ) (own : List (ℕ × List ℕ))
    (hB : x4 ≤ B) (ha : lead = false → a < B)
    (hown : ∀ p ∈ own, p.1 < x4 ∧ ∀ v ∈ p.2, v < x4) :
    ∀ j < (coverGatesB B lead a own).length,
      ∀ u ∈ ((coverGatesB B lead a own).getD j ⟨GateOp.or, []⟩).inputs, u < B + j := by
  induction own generalizing B lead a with
  | nil => simp [coverGatesB]
  | cons p os ih =>
    rcases p with ⟨t, L⟩
    rcases L with _ | ⟨v1, rest⟩
    · simp only [coverGatesB]
      exact ih B lead a hB ha (fun q hq => hown q (by simp [hq]))
    · simp only [coverGatesB, List.length_append]
      intro j hj u hu
      have hp := hown (t, v1 :: rest) (by simp)
      have ht : t < x4 := hp.1
      have hv1 : v1 < x4 := hp.2 v1 (by simp)
      have hrest : ∀ v ∈ rest, v < x4 := fun v hv => hp.2 v (by simp [hv])
      by_cases hj_blk : j < (blockGates B a t v1 rest lead).length
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj_blk] at hu
        exact blockGates_readsBack x4 B lead a t v1 rest hB ha ht hv1 hrest j hj_blk u hu
      · have hj_ge : (blockGates B a t v1 rest lead).length ≤ j := by omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hj_ge] at hu
        have hlen_pos : 0 < (blockGates B a t v1 rest lead).length := by
          rw [blockGates_len]; omega
        have := ih (B + (blockGates B a t v1 rest lead).length) false
          (B + (blockGates B a t v1 rest lead).length - 1) (by omega)
          (fun _ => by omega) (fun q hq => hown q (by simp [hq]))
          (j - (blockGates B a t v1 rest lead).length) (by omega) u hu
        omega

private lemma x8Gates_spec (x1 x2 : ℕ) (B : ℕ) (lead : Bool) (a : ℕ) (own : List (ℕ × List ℕ))
    (hB : x1 + x2 ≤ B) (hown : bipartOk x1 (x1 + x2) own) :
    ∀ w ∈ x8Gates x1 B lead a own,
      ∃ j < (coverGatesB B lead a own).length,
        w = B + j ∧
        ((coverGatesB B lead a own).getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∀ u ∈ ((coverGatesB B lead a own).getD j ⟨GateOp.or, []⟩).inputs,
          u ∈ Finset.range x1 ∪ x8Gates x1 B lead a own := by
  induction own generalizing B lead a with
  | nil => simp [x8Gates]
  | cons p os ih =>
    rcases p with ⟨t, L⟩
    rcases L with _ | ⟨v1, rest⟩
    · simp only [x8Gates, coverGatesB]
      exact ih B lead a hB (fun q hq => hown q (by simp [hq]))
    · simp only [x8Gates, coverGatesB, Finset.mem_union]
      intro w hw
      have hbip := hown (t, v1 :: rest) (by simp)
      rcases hw with hw_blk | hw_os
      · split_ifs at hw_blk with ht
        · simp only [Finset.mem_image, Finset.mem_range] at hw_blk
          rcases hw_blk with ⟨i, hi, rfl⟩
          have hj_lt : i < (blockGates B a t v1 rest lead).length := by
            rw [blockGates_len]; omega
          refine ⟨i, by simp; omega, rfl, ?_, ?_⟩
          · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj_lt]
            unfold blockGates
            simp only [List.getElem?_append_left (by simp [hi] : i < ((List.range rest.length).map _).length),
              List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some]
          · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj_lt]
            unfold blockGates
            simp only [List.getElem?_append_left (by simp [hi] : i < ((List.range rest.length).map _).length),
              List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some,
              List.mem_cons, List.not_mem_nil, or_false]
            have hL : v1 < x1 ∧ ∀ v ∈ rest, v < x1 := by
              rcases hbip.2 with ⟨hlt, _⟩ | ⟨_, _, hv⟩
              · omega
              · exact ⟨hv v1 (by simp), fun v hv' => hv v (by simp [hv'])⟩
            intro u hu
            simp only [Finset.mem_union, Finset.mem_range]
            rcases hu with rfl | rfl
            · rcases i with _ | i
              · exact Or.inl hL.1
              · simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_map,
                  List.getElem?_range (by omega : i < rest.length), Option.map_some, Option.getD_some]
                refine Or.inr (Or.inl ?_)
                rw [if_pos ht]
                exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
            · have hv_lt : rest.getD i 0 < x1 := hL.2 (rest.getD i 0) (by
                simp only [List.getD_eq_getElem?_getD]
                rw [List.getElem?_eq_getElem hi, Option.getD_some]
                exact List.getElem_mem hi)
              exact Or.inl hv_lt
        · simp at hw_blk
      · obtain ⟨j, hj, rfl, hop, hin⟩ := ih (B + (blockGates B a t v1 rest lead).length) false
          (B + (blockGates B a t v1 rest lead).length - 1) (by omega)
          (fun q hq => hown q (by simp [hq])) w hw_os
        have hle : (blockGates B a t v1 rest lead).length ≤ (blockGates B a t v1 rest lead).length + j :=
          Nat.le_add_right _ _
        refine ⟨(blockGates B a t v1 rest lead).length + j, by simp; omega, by omega, ?_, ?_⟩
        · simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right hle, Nat.add_sub_cancel_left]
          exact hop
        · simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right hle, Nat.add_sub_cancel_left]
          intro u hu
          have hu' := hin u hu
          simp only [Finset.mem_union] at hu' ⊢
          rcases hu' with hu' | hu'
          · exact Or.inl hu'
          · exact Or.inr (Or.inr hu')

private lemma x9Gates_spec (x1 x2 : ℕ) (B : ℕ) (lead : Bool) (a : ℕ) (own : List (ℕ × List ℕ))
    (hB : x1 + x2 ≤ B) (hown : bipartOk x1 (x1 + x2) own) :
    ∀ w ∈ x9Gates x1 B lead a own,
      ∃ j < (coverGatesB B lead a own).length,
        w = B + j ∧
        ((coverGatesB B lead a own).getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∀ u ∈ ((coverGatesB B lead a own).getD j ⟨GateOp.or, []⟩).inputs,
          u ∈ (Finset.range x2).image (fun i => x1 + i) ∪ x9Gates x1 B lead a own := by
  induction own generalizing B lead a with
  | nil => simp [x9Gates]
  | cons p os ih =>
    rcases p with ⟨t, L⟩
    rcases L with _ | ⟨v1, rest⟩
    · simp only [x9Gates, coverGatesB]
      exact ih B lead a hB (fun q hq => hown q (by simp [hq]))
    · simp only [x9Gates, coverGatesB, Finset.mem_union]
      intro w hw
      have hbip := hown (t, v1 :: rest) (by simp)
      rcases hw with hw_blk | hw_os
      · split_ifs at hw_blk with ht
        · simp only [Finset.mem_image, Finset.mem_range] at hw_blk
          rcases hw_blk with ⟨i, hi, rfl⟩
          have hj_lt : i < (blockGates B a t v1 rest lead).length := by
            rw [blockGates_len]; omega
          refine ⟨i, by simp; omega, rfl, ?_, ?_⟩
          · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj_lt]
            unfold blockGates
            simp only [List.getElem?_append_left (by simp [hi] : i < ((List.range rest.length).map _).length),
              List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some]
          · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj_lt]
            unfold blockGates
            simp only [List.getElem?_append_left (by simp [hi] : i < ((List.range rest.length).map _).length),
              List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some,
              List.mem_cons, List.not_mem_nil, or_false]
            have hL : (x1 ≤ v1 ∧ v1 < x1 + x2) ∧ ∀ v ∈ rest, x1 ≤ v ∧ v < x1 + x2 := by
              rcases hbip.2 with ⟨_, hv⟩ | ⟨hge, _, _⟩
              · exact ⟨hv v1 (by simp), fun v hv' => hv v (by simp [hv'])⟩
              · omega
            rcases hL with ⟨⟨hv1_ge, hv1_lt⟩, hrest_mem⟩
            intro u hu
            simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
            rcases hu with rfl | rfl
            · rcases i with _ | i
              · simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some]
                exact Or.inl ⟨v1 - x1, by omega, by omega⟩
              · simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_map,
                  List.getElem?_range (by omega : i < rest.length), Option.map_some, Option.getD_some]
                refine Or.inr (Or.inl ?_)
                rw [if_pos ht]
                exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
            · have hv_mem := hrest_mem (rest.getD i 0) (by
                simp only [List.getD_eq_getElem?_getD]
                rw [List.getElem?_eq_getElem hi, Option.getD_some]
                exact List.getElem_mem hi)
              exact Or.inl ⟨rest.getD i 0 - x1, by omega, by omega⟩
        · simp at hw_blk
      · obtain ⟨j, hj, rfl, hop, hin⟩ := ih (B + (blockGates B a t v1 rest lead).length) false
          (B + (blockGates B a t v1 rest lead).length - 1) (by omega)
          (fun q hq => hown q (by simp [hq])) w hw_os
        have hle : (blockGates B a t v1 rest lead).length ≤ (blockGates B a t v1 rest lead).length + j :=
          Nat.le_add_right _ _
        refine ⟨(blockGates B a t v1 rest lead).length + j, by simp; omega, by omega, ?_, ?_⟩
        · simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right hle, Nat.add_sub_cancel_left]
          exact hop
        · simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right hle, Nat.add_sub_cancel_left]
          intro u hu
          have hu' := hin u hu
          simp only [Finset.mem_union] at hu' ⊢
          rcases hu' with hu' | hu'
          · exact Or.inl hu'
          · exact Or.inr (Or.inr hu')

private lemma coverGatesB_and_spec (x1 x2 : ℕ) (B : ℕ) (lead : Bool) (a : ℕ) (own : List (ℕ × List ℕ))
    (hB : x1 + x2 ≤ B) (hown : bipartOk x1 (x1 + x2) own) :
    ∀ j < (coverGatesB B lead a own).length,
      ((coverGatesB B lead a own).getD j ⟨GateOp.or, []⟩).op = GateOp.and →
      ∃ c d, ((coverGatesB B lead a own).getD j ⟨GateOp.or, []⟩).inputs = [c, d] ∧
        ((c ∈ Finset.range x1 ∪ x8Gates x1 B lead a own ∧ d ∈ (Finset.range x2).image (fun i => x1 + i) ∪ x9Gates x1 B lead a own) ∨
         (c ∈ (Finset.range x2).image (fun i => x1 + i) ∪ x9Gates x1 B lead a own ∧ d ∈ Finset.range x1 ∪ x8Gates x1 B lead a own)) := by
  induction own generalizing B lead a with
  | nil => simp [coverGatesB]
  | cons p os ih =>
    rcases p with ⟨t, L⟩
    rcases L with _ | ⟨v1, rest⟩
    · simp only [coverGatesB, x8Gates, x9Gates]
      exact ih B lead a hB (fun q hq => hown q (by simp [hq]))
    · intro j hj hop
      have hbip := hown (t, v1 :: rest) (by simp)
      simp only [coverGatesB, List.length_append] at hj hop ⊢
      by_cases hj_blk : j < (blockGates B a t v1 rest lead).length
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj_blk] at hop ⊢
        have hlen_blk := blockGates_len B a t v1 rest lead
        have hj_eq : j = rest.length := by
          have : j < rest.length ∨ j = rest.length ∨ (lead = false ∧ j = rest.length + 1) := by
            rw [hlen_blk] at hj_blk
            cases lead
            · have hle : j ≤ rest.length + 1 := by simpa using hj_blk
              rcases Nat.lt_or_eq_of_le hle with hlt1 | heq1
              · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt1) with hlt2 | rfl
                · exact Or.inl hlt2
                · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr ⟨rfl, heq1⟩)
            · have hle : j ≤ rest.length := by simpa using hj_blk
              rcases Nat.lt_or_eq_of_le hle with hlt1 | rfl
              · exact Or.inl hlt1
              · exact Or.inr (Or.inl rfl)
          rcases this with hj1 | rfl | ⟨hlead, rfl⟩
          · unfold blockGates at hop
            rw [List.getElem?_append_left (by simp [hj1] : j < ((List.range rest.length).map _).length),
              List.getElem?_map, List.getElem?_range hj1, Option.map_some, Option.getD_some] at hop
            cases hop
          · rfl
          · subst hlead
            unfold blockGates at hop
            rw [List.getElem?_append_right (by simp)] at hop
            simp only [List.length_map, List.length_range, Nat.add_sub_cancel_left,
              List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] at hop
            cases hop
        subst hj_eq
        have hget : (blockGates B a t v1 rest lead)[rest.length]?.getD ⟨GateOp.or, []⟩ =
            ⟨GateOp.and, [t, (v1 :: (List.range rest.length).map (fun k => B + k)).getD rest.length 0]⟩ := by
          unfold blockGates
          rw [List.getElem?_append_right (by simp)]
          simp only [List.length_map, List.length_range, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [hget]
        refine ⟨t, (v1 :: (List.range rest.length).map (fun k => B + k)).getD rest.length 0, rfl, ?_⟩
        rcases hbip.2 with ⟨ht, hv⟩ | ⟨ht1, ht2, hv⟩
        · refine Or.inl ⟨Finset.mem_union_left _ (Finset.mem_range.mpr ht), ?_⟩
          rcases hrest : rest with _ | ⟨v2, rest'⟩
          · simp only [List.length_nil, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some]
            have hv1 := hv v1 (by simp)
            exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v1 - x1, Finset.mem_range.mpr (by omega), by omega⟩)
          · simp only [List.length_cons, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
              List.getElem?_map, List.getElem?_range (by omega : rest'.length < rest'.length + 1),
              Option.map_some, Option.getD_some]
            refine Finset.mem_union_right _ (Finset.mem_union_left _ ?_)
            simp only [x9Gates, if_pos ht, Finset.mem_image, Finset.mem_range, List.length_cons]
            exact ⟨rest'.length, by omega, rfl⟩
        · refine Or.inr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t - x1, Finset.mem_range.mpr (by omega), by omega⟩), ?_⟩
          rcases hrest : rest with _ | ⟨v2, rest'⟩
          · simp only [List.length_nil, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some]
            exact Finset.mem_union_left _ (Finset.mem_range.mpr (hv v1 (by simp)))
          · simp only [List.length_cons, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
              List.getElem?_map, List.getElem?_range (by omega : rest'.length < rest'.length + 1),
              Option.map_some, Option.getD_some]
            refine Finset.mem_union_right _ (Finset.mem_union_left _ ?_)
            simp only [x8Gates, if_pos ht1, Finset.mem_image, Finset.mem_range, List.length_cons]
            exact ⟨rest'.length, by omega, rfl⟩
      · have hj_ge : (blockGates B a t v1 rest lead).length ≤ j := by omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hj_ge] at hop ⊢
        obtain ⟨c, d, hcd, hmem⟩ := ih (B + (blockGates B a t v1 rest lead).length) false
          (B + (blockGates B a t v1 rest lead).length - 1) (by omega)
          (fun q hq => hown q (by simp [hq])) (j - (blockGates B a t v1 rest lead).length) (by omega) hop
        refine ⟨c, d, hcd, ?_⟩
        simp only [x8Gates, x9Gates, Finset.mem_union] at hmem ⊢
        tauto

theorem main :
    ∀ (x1 x2 : ℕ) (x3 : List (ℕ × List ℕ)), have x4 : ℕ := x1 + x2; (∀ x5 ∈ x3, x5.2 ≠ [] ∧ ((x5.1 < x1 ∧ ∀ x7 ∈ x5.2, x1 ≤ x7 ∧ x7 < x4) ∨ x1 ≤ x5.1 ∧ x5.1 < x4 ∧ ∀ x7 ∈ x5.2, x7 < x1)) → have x6 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x4 x3; have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x6; ∃ (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 x4 x6 ∧ (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x8) ∧ (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x4 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x9) ∧ ∀ x10 < x6.gates.length, (x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (x7 x10).inputs = [x13, x14] ∧ (x13 ∈ x8 ∧ x14 ∈ x9 ∨ x13 ∈ x9 ∧ x14 ∈ x8) := by
  intro x1 x2 x3 x4 hown x6 x7
  have hbip : bipartOk x1 x4 x3 := hown
  have hflat : ∀ p ∈ x3, p.1 < x4 ∧ ∀ v ∈ p.2, v < x4 := by
    intro p hp
    rcases (hown p hp).2 with ⟨h1, h2⟩ | ⟨_, h2, h3⟩
    · exact ⟨by omega, fun v hv => (h2 v hv).2⟩
    · exact ⟨h2, fun v hv => by have := h3 v hv; omega⟩
  have hgates : x6.gates = coverGatesB x4 true 0 x3 := by
    dsimp only [x6, coverCircuitB]
    split_ifs with h
    · exact h.symm
    · rfl
  refine ⟨Finset.range x1 ∪ x8Gates x1 x4 true 0 x3,
    (Finset.range x2).image (fun i => x1 + i) ∪ x9Gates x1 x4 true 0 x3, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rw [hgates] at hg
      exact (coverGatesB_andOr x4 true 0 x3 g hg).symm
    · intro j hj u hu
      dsimp only [gateAt] at hu
      rw [hgates] at hj hu
      exact coverGatesB_readsBack x4 x4 true 0 x3 (le_refl _) (fun h => by cases h) hflat j hj u hu
    · intro g hg
      rw [hgates] at hg
      exact coverGatesB_len2 x4 true 0 x3 g hg
  · intro w hw
    simp only [Finset.mem_union, Finset.mem_range] at hw
    rcases hw with hw | hw
    · exact Or.inl hw
    · obtain ⟨j, hj, rfl, hop, hin⟩ := x8Gates_spec x1 x2 x4 true 0 x3 (le_refl _) hbip w hw
      refine Or.inr ⟨j, by rw [hgates]; exact hj, rfl, ?_, ?_⟩
      · dsimp only [x7, gateAt]; rw [hgates]; exact hop
      · dsimp only [x7, gateAt]; rw [hgates]; exact hin
  · intro w hw
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range] at hw
    rcases hw with ⟨i, hi, rfl⟩ | hw
    · exact Or.inl ⟨by omega, by omega⟩
    · obtain ⟨j, hj, rfl, hop, hin⟩ := x9Gates_spec x1 x2 x4 true 0 x3 (le_refl _) hbip w hw
      refine Or.inr ⟨j, by rw [hgates]; exact hj, rfl, ?_, ?_⟩
      · dsimp only [x7, gateAt]; rw [hgates]; exact hop
      · dsimp only [x7, gateAt]; rw [hgates]; exact hin
  · intro j hj hop
    dsimp only [x7, gateAt] at hj hop ⊢
    rw [hgates] at hj hop ⊢
    exact coverGatesB_and_spec x1 x2 x4 true 0 x3 (le_refl _) hbip j hj hop

end PEqualNP.Outside.L_meta_3245
