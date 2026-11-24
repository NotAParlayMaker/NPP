import Mathlib
import PEqualNP.Defs

-- The cover circuit of a bipartite incidence is two-level.
--
-- coverCircuitB puts, for every owner, a chain of ORs over its list, then the AND of the owner
-- with the end of the chain, and joins the blocks with one OR per block after the first.
--
-- When the owners are the points and the lines of a bipartite incidence (points are the wires
-- below Np, lines the wires from Np to Np + Nl), the list of a point owner holds lines and the
-- list of a line owner holds points. So the chain of a point owner is a chain of ORs over lines,
-- the chain of a line owner is a chain of ORs over points, and each AND gate reads its owner on
-- one side and the end of its chain on the other side. That is the two-level form.
--
-- This file proves it for the concrete circuit coverCircuitB, with the shape IsAO2 and the
-- read-back property, so every AND gate of the circuit reads one wire from each side.

namespace PEqualNP.Outside.L_meta_3245

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- The fallback gate of gateAt.
abbrev dflt : Gate := ⟨GateOp.or, []⟩

-- The wires of the point side.
def Pt (Np : ℕ) : Finset ℕ := Finset.range Np

-- The wires of the line side.
def Ln (Np Nl : ℕ) : Finset ℕ := Finset.Ico Np (Np + Nl)

-- The number of gates of one block with remainder list rest and lead flag lead.
def blen (rest : List ℕ) (lead : Bool) : ℕ := rest.length + 1 + (if lead then 0 else 1)

-- The chain gate of index k of the block with first member v1, the block starting at wire B.
def chainGate (B v1 k : ℕ) (rest : List ℕ) : Gate :=
  ⟨GateOp.or, [(v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0, rest.getD k 0]⟩

-- The OR chain of the block with first member v1, the block starting at wire B.
def chainOf (B v1 : ℕ) (rest : List ℕ) : List Gate :=
  (List.range rest.length).map (fun k => chainGate B v1 k rest)

-- The wire the AND gate of a block reads for the end of the chain.
def andWire (B v1 : ℕ) (rest : List ℕ) : ℕ :=
  (v1 :: (List.range rest.length).map (fun j => B + j)).getD rest.length 0

-- The point side of the cover circuit of the owner list own, placed from wire B.
def clsP (Np Nl : ℕ) (B : ℕ) (lead : Bool) (own : List (ℕ × List ℕ)) : Finset ℕ :=
  match own with
  | [] => Pt Np
  | (_, []) :: os => clsP Np Nl B lead os
  | (t, _ :: rest) :: os =>
      if t < Np then clsP Np Nl (B + blen rest lead) false os
      else clsP Np Nl (B + blen rest lead) false os ∪
        (Finset.range rest.length).image (fun k => B + k)

-- The line side of the cover circuit of the owner list own, placed from wire B.
def clsL (Np Nl : ℕ) (B : ℕ) (lead : Bool) (own : List (ℕ × List ℕ)) : Finset ℕ :=
  match own with
  | [] => Ln Np Nl
  | (_, []) :: os => clsL Np Nl B lead os
  | (t, _ :: rest) :: os =>
      if t < Np then clsL Np Nl (B + blen rest lead) false os ∪
        (Finset.range rest.length).image (fun k => B + k)
      else clsL Np Nl (B + blen rest lead) false os

theorem getD_map_range (B m n : ℕ) (hm : m < n) :
    ((List.range n).map (fun j => B + j)).getD m 0 = B + m := by
  rw [List.getD_eq_getElem _ 0 (n := m) (by simpa using hm)]
  simp

theorem getD_mem {l : List ℕ} {k : ℕ} (hk : k < l.length) : l.getD k 0 ∈ l := by
  rw [List.getD_eq_getElem l 0 hk]
  simp

theorem blockGates_eq (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    blockGates B a t v1 rest lead =
      chainOf B v1 rest ++ (⟨GateOp.and, [t, andWire B v1 rest]⟩ ::
        (if lead then [] else [⟨GateOp.or, [a, B + rest.length]⟩])) := by
  simp only [blockGates, chainOf, chainGate, andWire]

theorem blockGates_length (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v1 rest lead).length = blen rest lead := by
  rw [blockGates_eq]
  cases lead <;> simp [blen, chainOf]

theorem getD_chain (B a t v1 k : ℕ) (rest : List ℕ) (lead : Bool) (hk : k < rest.length) :
    (blockGates B a t v1 rest lead).getD k dflt = chainGate B v1 k rest := by
  rw [blockGates_eq]
  rw [List.getD_append (chainOf B v1 rest) _ dflt k (by simp [chainOf]; omega)]
  rw [List.getD_eq_getElem _ dflt (n := k) (by simp [chainOf]; omega)]
  simp [chainOf]

theorem getD_tail (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) (j : ℕ) :
    (blockGates B a t v1 rest lead).getD (rest.length + j) dflt =
      (⟨GateOp.and, [t, andWire B v1 rest]⟩ ::
        (if lead then [] else [⟨GateOp.or, [a, B + rest.length]⟩])).getD j dflt := by
  rw [blockGates_eq]
  rw [List.getD_append_right (chainOf B v1 rest) _ dflt (rest.length + j) (by simp [chainOf])]
  congr 1
  simp [chainOf]

theorem blockGates_and_gate (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v1 rest lead).getD rest.length dflt
      = ⟨GateOp.and, [t, andWire B v1 rest]⟩ := by
  have h := getD_tail B a t v1 rest lead 0
  simpa using h

theorem blockGates_join_gate (B a t v1 : ℕ) (rest : List ℕ) :
    (blockGates B a t v1 rest false).getD (rest.length + 1) dflt
      = ⟨GateOp.or, [a, B + rest.length]⟩ := by
  have h := getD_tail B a t v1 rest false 1
  simpa using h

theorem chainGate_inputs (B v1 k : ℕ) (rest : List ℕ) (hk : k < rest.length) :
    ∀ i ∈ (chainGate B v1 k rest).inputs, i = v1 ∨ i ∈ rest ∨ ∃ k' < k, i = B + k' := by
  intro i hi
  simp only [chainGate, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi
  · rcases Nat.eq_zero_or_pos k with h0 | hp
    · left
      rw [h0] at hi
      simpa using hi
    · right; right
      obtain ⟨m, hk'⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      refine ⟨m, by omega, ?_⟩
      rw [hk'] at hi
      rw [List.getD_cons_succ] at hi
      rw [getD_map_range B m rest.length (by omega)] at hi
      exact hi
  · right; left
    rw [hi]
    exact getD_mem hk

theorem andWire_spec (B v1 : ℕ) (rest : List ℕ) :
    andWire B v1 rest = v1 ∨ ∃ k' < rest.length, andWire B v1 rest = B + k' := by
  rcases rest with _ | ⟨a, rs⟩
  · left; simp [andWire]
  · right
    refine ⟨rs.length, by simp, ?_⟩
    simp only [andWire, List.length_cons]
    rw [List.getD_cons_succ]
    rw [getD_map_range B rs.length (rs.length + 1) (by omega)]

theorem blockGates_reads (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool)
    (ha : a < B) (ht : t < B) (hv1 : v1 < B) (hrest : ∀ u ∈ rest, u < B) :
    ∀ k < (blockGates B a t v1 rest lead).length,
      ∀ i ∈ ((blockGates B a t v1 rest lead).getD k dflt).inputs, i < B + k := by
  intro k hk i hi
  rcases lt_or_ge k rest.length with hlt | hge
  · rw [getD_chain B a t v1 k rest lead hlt] at hi
    rcases chainGate_inputs B v1 k rest hlt i hi with h | h | ⟨k', hk', h⟩
    · rw [h]; omega
    · exact lt_of_lt_of_le (hrest i h) (Nat.le_add_right B k)
    · rw [h]; omega
  · have hb : 1 ≤ blen rest lead := by cases lead <;> simp [blen]
    cases lead
    · have hlen : (blockGates B a t v1 rest false).length = rest.length + 2 := by
        rw [blockGates_length]; simp [blen]
      have hcases : k = rest.length ∨ k = rest.length + 1 := by omega
      rcases hcases with rfl | rfl
      · have hi2 : i = t ∨ i = andWire B v1 rest := by
          rw [blockGates_and_gate] at hi
          simpa using hi
        rcases hi2 with rfl | rfl
        · omega
        · rcases andWire_spec B v1 rest with h | ⟨k', hk', h⟩
          · rw [h]; omega
          · rw [h]; omega
      · have hi2 : i = a ∨ i = B + rest.length := by
          rw [blockGates_join_gate B a t v1 rest] at hi
          simpa using hi
        rcases hi2 with rfl | rfl <;> omega
    · have hlen : (blockGates B a t v1 rest true).length = rest.length + 1 := by
        rw [blockGates_length]; simp [blen]
      have hk0 : k = rest.length := by omega
      subst hk0
      have hi2 : i = t ∨ i = andWire B v1 rest := by
        rw [blockGates_and_gate] at hi
        simpa using hi
      rcases hi2 with rfl | rfl
      · omega
      · rcases andWire_spec B v1 rest with h | ⟨k', hk', h⟩
        · rw [h]; omega
        · rw [h]; omega

theorem Pt_subset_clsP (Np Nl B : ℕ) (lead : Bool) (own : List (ℕ × List ℕ)) :
    ∀ w ∈ Pt Np, w ∈ clsP Np Nl B lead own := by
  induction own generalizing B lead with
  | nil => exact fun w hw => hw
  | cons tx os ih =>
      obtain ⟨t, l⟩ := tx
      cases l with
      | nil =>
          intro w hw
          simp only [clsP]
          exact ih B lead w hw
      | cons v1 rest =>
          intro w hw
          simp only [clsP]
          split_ifs with htp
          · exact ih (B + blen rest lead) false w hw
          · exact Finset.mem_union_left _ (ih (B + blen rest lead) false w hw)

theorem Ln_subset_clsL (Np Nl B : ℕ) (lead : Bool) (own : List (ℕ × List ℕ)) :
    ∀ w ∈ Ln Np Nl, w ∈ clsL Np Nl B lead own := by
  induction own generalizing B lead with
  | nil => exact fun w hw => hw
  | cons tx os ih =>
      obtain ⟨t, l⟩ := tx
      cases l with
      | nil =>
          intro w hw
          simp only [clsL]
          exact ih B lead w hw
      | cons v1 rest =>
          intro w hw
          simp only [clsL]
          split_ifs with htp
          · exact Finset.mem_union_left _ (ih (B + blen rest lead) false w hw)
          · exact ih (B + blen rest lead) false w hw

theorem blockGates_shape (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    ∀ g ∈ blockGates B a t v1 rest lead,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  cases lead <;> simp [blockGates] at hg <;> rcases hg with ⟨i, _, rfl⟩ | rfl | rfl <;> simp

theorem coverGates_shape : ∀ (own : List (ℕ × List ℕ)) (B a : ℕ) (lead : Bool),
    ∀ g ∈ coverGatesB B lead a own,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  | [], _, _, _ => by intro g hg; simp [coverGatesB] at hg
  | (t, []) :: os, B, a, lead => by
      intro g hg
      simp only [coverGatesB] at hg
      exact coverGates_shape os B a lead g hg
  | (t, v1 :: rest) :: os, B, a, lead => by
      intro g hg
      simp only [coverGatesB, List.mem_append] at hg
      rcases hg with hg | hg
      · exact blockGates_shape B a t v1 rest lead g hg
      · exact coverGates_shape os _ _ false g hg

end PEqualNP.Outside.L_meta_3245

namespace PEqualNP.Outside.L_meta_3245

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- A chain wire belongs to the image of its block.
theorem mem_chain_image {B k : ℕ} {rest : List ℕ} (hk : k < rest.length) :
    B + k ∈ (Finset.range rest.length).image (fun j => B + j) :=
  Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩

-- The only gates of a block after its OR chain are its AND gate and, when the block does not
-- lead, its joining OR gate.
theorem blockGates_tail_cases (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) (j : ℕ)
    (hj : j < 1 + (if lead then 0 else 1)) : j = 0 ∨ (j = 1 ∧ lead = false) := by
  cases lead
  · have hj2 : j < 2 := by simpa only [Bool.false_eq_true, ite_false] using hj
    rcases Nat.eq_zero_or_pos j with h0 | hp
    · exact Or.inl h0
    · exact Or.inr ⟨by omega, rfl⟩
  · have hj1 : j < 1 := by simpa only [ite_true, Nat.add_zero] using hj
    exact Or.inl (by omega)

-- The main bookkeeping, for a suffix of the owner list placed from wire B: every gate reads back,
-- both sides are closed under their own OR gates, and every AND gate reads one wire of each side.
theorem shape_aux (Np Nl : ℕ) : ∀ (own : List (ℕ × List ℕ)) (B a : ℕ) (lead : Bool),
    Np + Nl ≤ B → a < B →
    (∀ tx ∈ own, tx.2 ≠ [] ∧
      ((tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < Np + Nl) ∨
       (Np ≤ tx.1 ∧ tx.1 < Np + Nl ∧ ∀ u ∈ tx.2, u < Np))) →
    (∀ k < (coverGatesB B lead a own).length,
      ∀ i ∈ ((coverGatesB B lead a own).getD k dflt).inputs, i < B + k) ∧
    (∀ w ∈ clsP Np Nl B lead own, w < Np ∨
      ∃ k < (coverGatesB B lead a own).length, w = B + k ∧
        ((coverGatesB B lead a own).getD k dflt).op = GateOp.or ∧
        ∀ i ∈ ((coverGatesB B lead a own).getD k dflt).inputs, i ∈ clsP Np Nl B lead own) ∧
    (∀ w ∈ clsL Np Nl B lead own, (Np ≤ w ∧ w < Np + Nl) ∨
      ∃ k < (coverGatesB B lead a own).length, w = B + k ∧
        ((coverGatesB B lead a own).getD k dflt).op = GateOp.or ∧
        ∀ i ∈ ((coverGatesB B lead a own).getD k dflt).inputs, i ∈ clsL Np Nl B lead own) ∧
    (∀ k < (coverGatesB B lead a own).length,
      ((coverGatesB B lead a own).getD k dflt).op = GateOp.and →
      ∃ x y, ((coverGatesB B lead a own).getD k dflt).inputs = [x, y] ∧
        ((x ∈ clsP Np Nl B lead own ∧ y ∈ clsL Np Nl B lead own) ∨
         (x ∈ clsL Np Nl B lead own ∧ y ∈ clsP Np Nl B lead own))) := by
  intro own
  induction own with
  | nil =>
      intro B a lead hB ha hown
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro k hk
        simp [coverGatesB] at hk
      · intro w hw
        exact Or.inl (by simpa [clsP, Pt] using hw)
      · intro w hw
        exact Or.inl (by simpa [clsL, Ln] using hw)
      · intro k hk
        simp [coverGatesB] at hk
  | cons tx os ih =>
      obtain ⟨t, l⟩ := tx
      cases l with
      | nil =>
          intro B a lead hB ha hown
          simp only [coverGatesB, clsP, clsL]
          exact ih B a lead hB ha (fun tx htx => hown tx (List.mem_cons_of_mem _ htx))
      | cons v1 rest =>
          intro B a lead hB ha hown
          obtain ⟨hne, hside⟩ := hown (t, v1 :: rest) (by simp)
          have htail : ∀ tx ∈ os, tx.2 ≠ [] ∧
              ((tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < Np + Nl) ∨
               (Np ≤ tx.1 ∧ tx.1 < Np + Nl ∧ ∀ u ∈ tx.2, u < Np)) :=
            fun tx htx => hown tx (List.mem_cons_of_mem _ htx)
          have hmem : ∀ u ∈ v1 :: rest, u < Np + Nl := by
            rcases hside with ⟨_, hu⟩ | ⟨_, _, hu⟩
            · exact fun u hu' => (hu u hu').2
            · exact fun u hu' => by have h := hu u hu'; omega
          have htB : t < B := by
            rcases hside with ⟨h, _⟩ | ⟨_, h, _⟩ <;> omega
          have hv1B : v1 < B := by have := hmem v1 (by simp); omega
          have hrestB : ∀ u ∈ rest, u < B := by
            intro u hu
            have := hmem u (List.mem_cons_of_mem _ hu)
            omega
          have ha' : B + blen rest lead - 1 < B + blen rest lead := by
            have : 1 ≤ blen rest lead := by cases lead <;> simp [blen]
            omega
          have hB' : Np + Nl ≤ B + blen rest lead := by omega
          simp only [coverGatesB, blockGates_length, clsP, clsL]
          set g₁ := blockGates B a t v1 rest lead with hg₁
          set g₂ := coverGatesB (B + blen rest lead) false (B + blen rest lead - 1) os with hg₂
          have hlen₁ : g₁.length = blen rest lead := by
            rw [hg₁]
            exact blockGates_length B a t v1 rest lead
          have hlen₂ : g₁.length = rest.length + 1 + (if lead then 0 else 1) := by
            rw [hlen₁]
            rfl
          have hlen₃ : rest.length < g₁.length := by omega
          obtain ⟨ih1, ih2, ih3, ih4⟩ :=
            ih (B + blen rest lead) (B + blen rest lead - 1) false hB' ha' htail
          have ih1' : ∀ k < g₂.length, ∀ i ∈ (g₂.getD k dflt).inputs,
              i < (B + blen rest lead) + k := ih1
          have ih2' : ∀ w ∈ clsP Np Nl (B + blen rest lead) false os, w < Np ∨
              ∃ k < g₂.length, w = (B + blen rest lead) + k ∧
                (g₂.getD k dflt).op = GateOp.or ∧
                ∀ i ∈ (g₂.getD k dflt).inputs, i ∈ clsP Np Nl (B + blen rest lead) false os :=
            ih2
          have ih3' : ∀ w ∈ clsL Np Nl (B + blen rest lead) false os,
              (Np ≤ w ∧ w < Np + Nl) ∨
              ∃ k < g₂.length, w = (B + blen rest lead) + k ∧
                (g₂.getD k dflt).op = GateOp.or ∧
                ∀ i ∈ (g₂.getD k dflt).inputs, i ∈ clsL Np Nl (B + blen rest lead) false os :=
            ih3
          have ih4' : ∀ k < g₂.length, (g₂.getD k dflt).op = GateOp.and →
              ∃ x y, (g₂.getD k dflt).inputs = [x, y] ∧
                ((x ∈ clsP Np Nl (B + blen rest lead) false os ∧
                    y ∈ clsL Np Nl (B + blen rest lead) false os) ∨
                 (x ∈ clsL Np Nl (B + blen rest lead) false os ∧
                    y ∈ clsP Np Nl (B + blen rest lead) false os)) := ih4
          by_cases htp : t < Np
          · have hleaves : ∀ u ∈ v1 :: rest, Np ≤ u ∧ u < Np + Nl := by
              rcases hside with ⟨_, hu⟩ | ⟨h1, _, _⟩
              · exact hu
              · exact absurd h1 (by omega)
            simp only [ite_eq_left htp]
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro k hk i hi
              simp only [List.length_append] at hk
              rcases lt_or_ge k g₁.length with hlt | hge
              · rw [List.getD_append g₁ g₂ dflt k hlt] at hi
                exact blockGates_reads B a t v1 rest lead ha htB hv1B hrestB k hlt i hi
              · rw [List.getD_append_right g₁ g₂ dflt k hge] at hi
                have := ih1' (k - g₁.length) (by omega) i hi
                omega
            · intro w hw
              rcases ih2' w hw with h | ⟨k, hk, hwk, hop, hin⟩
              · exact Or.inl h
              · refine Or.inr ⟨g₁.length + k, ?_, ?_, ?_, ?_⟩
                · rw [List.length_append]; omega
                · omega
                · rw [List.getD_append_right g₁ g₂ dflt (g₁.length + k) (by omega),
                    show g₁.length + k - g₁.length = k from by omega]
                  exact hop
                · intro i hi
                  rw [List.getD_append_right g₁ g₂ dflt (g₁.length + k) (by omega),
                    show g₁.length + k - g₁.length = k from by omega] at hi
                  exact hin i hi
            · intro w hw
              rcases Finset.mem_union.mp hw with hw | hw
              · rcases ih3' w hw with h | ⟨k, hk, hwk, hop, hin⟩
                · exact Or.inl h
                · refine Or.inr ⟨g₁.length + k, ?_, ?_, ?_, ?_⟩
                  · rw [List.length_append]; omega
                  · omega
                  · rw [List.getD_append_right g₁ g₂ dflt (g₁.length + k) (by omega),
                      show g₁.length + k - g₁.length = k from by omega]
                    exact hop
                  · intro i hi
                    rw [List.getD_append_right g₁ g₂ dflt (g₁.length + k) (by omega),
                      show g₁.length + k - g₁.length = k from by omega] at hi
                    exact Finset.mem_union_left _ (hin i hi)
              · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
                have hkr : k < rest.length := Finset.mem_range.mp hk
                refine Or.inr ⟨k, ?_, rfl, ?_, ?_⟩
                · rw [List.length_append]; omega
                · rw [List.getD_append g₁ g₂ dflt k (by omega), hg₁,
                    getD_chain B a t v1 k rest lead hkr]
                  rfl
                · intro i hi
                  rw [List.getD_append g₁ g₂ dflt k (by omega), hg₁,
                    getD_chain B a t v1 k rest lead hkr] at hi
                  rcases chainGate_inputs B v1 k rest hkr i hi with h | h | ⟨k', hk', h⟩
                  · rw [h]
                    exact Finset.mem_union_left _
                      (Ln_subset_clsL Np Nl (B + blen rest lead) false os v1
                            (Finset.mem_Ico.mpr (hleaves v1 (by simp))))
                  · exact Finset.mem_union_left _
                      (Ln_subset_clsL Np Nl (B + blen rest lead) false os i (Finset.mem_Ico.mpr (hleaves i (List.mem_cons_of_mem _ h))))
                  · rw [h]
                    exact Finset.mem_union_right _ (mem_chain_image (by omega))
            · intro k hk hop
              simp only [List.length_append] at hk
              rcases lt_or_ge k g₁.length with hlt | hge
              · have hkge : rest.length ≤ k := by
                  by_contra hcon
                  have hlt' : k < rest.length := by omega
                  have hor : (g₁.getD k dflt).op = GateOp.or := by
                    rw [hg₁, getD_chain B a t v1 k rest lead hlt']
                    rfl
                  rw [List.getD_append g₁ g₂ dflt k hlt, hor] at hop
                  exact absurd hop (by simp)
                obtain ⟨j, hk'⟩ : ∃ j, k = rest.length + j := ⟨k - rest.length, by omega⟩
                have hj : j < 1 + (if lead then 0 else 1) := by
                  rw [hk'] at hlt
                  omega
                rw [hk'] at hop ⊢
                rcases blockGates_tail_cases B a t v1 rest lead j hj with rfl | ⟨rfl, rfl⟩
                · refine ⟨t, andWire B v1 rest, ?_, Or.inl ⟨?_, ?_⟩⟩
                  · rw [List.getD_append g₁ g₂ dflt (rest.length + 0) (by omega),
                      show rest.length + 0 = rest.length from by omega, hg₁,
                      blockGates_and_gate]
                  · exact Pt_subset_clsP Np Nl (B + blen rest lead) false os t
                      (by simpa [Pt] using htp)
                  · rcases andWire_spec B v1 rest with h | ⟨k', hk', h⟩
                    · rw [h]
                      exact Finset.mem_union_left _
                        (Ln_subset_clsL Np Nl (B + blen rest lead) false os v1
                            (Finset.mem_Ico.mpr (hleaves v1 (by simp))))
                    · rw [h]
                      exact Finset.mem_union_right _ (mem_chain_image (by omega))
                · have hor : (g₁.getD (rest.length + 1) dflt).op = GateOp.or := by
                    rw [hg₁, blockGates_join_gate B a t v1 rest]
                  rw [List.getD_append g₁ g₂ dflt (rest.length + 1) (by omega), hor] at hop
                  exact absurd hop (by simp)
              · rw [List.getD_append_right g₁ g₂ dflt k hge] at hop ⊢
                obtain ⟨x, y, hxy, hm | hm⟩ := ih4' (k - g₁.length) (by omega) hop
                · exact ⟨x, y, hxy, Or.inl ⟨hm.1, Finset.mem_union_left _ hm.2⟩⟩
                · exact ⟨x, y, hxy, Or.inr ⟨Finset.mem_union_left _ hm.1, hm.2⟩⟩
          · have htL : Np ≤ t ∧ t < Np + Nl := by
              rcases hside with ⟨h1, _⟩ | ⟨h1, h2, _⟩
              · exact absurd h1 htp
              · exact ⟨h1, h2⟩
            have hleaves : ∀ u ∈ v1 :: rest, u < Np := by
              rcases hside with ⟨h1, _⟩ | ⟨_, _, hu⟩
              · exact absurd h1 htp
              · exact hu
            simp only [ite_eq_right (show ¬ (t < Np) from htp)]
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro k hk i hi
              simp only [List.length_append] at hk
              rcases lt_or_ge k g₁.length with hlt | hge
              · rw [List.getD_append g₁ g₂ dflt k hlt] at hi
                exact blockGates_reads B a t v1 rest lead ha htB hv1B hrestB k hlt i hi
              · rw [List.getD_append_right g₁ g₂ dflt k hge] at hi
                have := ih1' (k - g₁.length) (by omega) i hi
                omega
            · intro w hw
              rcases Finset.mem_union.mp hw with hw | hw
              · rcases ih2' w hw with h | ⟨k, hk, hwk, hop, hin⟩
                · exact Or.inl h
                · refine Or.inr ⟨g₁.length + k, ?_, ?_, ?_, ?_⟩
                  · rw [List.length_append]; omega
                  · omega
                  · rw [List.getD_append_right g₁ g₂ dflt (g₁.length + k) (by omega),
                      show g₁.length + k - g₁.length = k from by omega]
                    exact hop
                  · intro i hi
                    rw [List.getD_append_right g₁ g₂ dflt (g₁.length + k) (by omega),
                      show g₁.length + k - g₁.length = k from by omega] at hi
                    exact Finset.mem_union_left _ (hin i hi)
              · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
                have hkr : k < rest.length := Finset.mem_range.mp hk
                refine Or.inr ⟨k, ?_, rfl, ?_, ?_⟩
                · rw [List.length_append]; omega
                · rw [List.getD_append g₁ g₂ dflt k (by omega), hg₁,
                    getD_chain B a t v1 k rest lead hkr]
                  rfl
                · intro i hi
                  rw [List.getD_append g₁ g₂ dflt k (by omega), hg₁,
                    getD_chain B a t v1 k rest lead hkr] at hi
                  rcases chainGate_inputs B v1 k rest hkr i hi with h | h | ⟨k', hk', h⟩
                  · rw [h]
                    exact Finset.mem_union_left _
                      (Pt_subset_clsP Np Nl (B + blen rest lead) false os v1
                        (by simpa [Pt] using hleaves v1 (by simp)))
                  · exact Finset.mem_union_left _
                      (Pt_subset_clsP Np Nl (B + blen rest lead) false os i
                        (by simpa [Pt] using hleaves i (List.mem_cons_of_mem _ h)))
                  · rw [h]
                    exact Finset.mem_union_right _ (mem_chain_image (by omega))
            · intro w hw
              rcases ih3' w hw with h | ⟨k, hk, hwk, hop, hin⟩
              · exact Or.inl h
              · refine Or.inr ⟨g₁.length + k, ?_, ?_, ?_, ?_⟩
                · rw [List.length_append]; omega
                · omega
                · rw [List.getD_append_right g₁ g₂ dflt (g₁.length + k) (by omega),
                    show g₁.length + k - g₁.length = k from by omega]
                  exact hop
                · intro i hi
                  rw [List.getD_append_right g₁ g₂ dflt (g₁.length + k) (by omega),
                    show g₁.length + k - g₁.length = k from by omega] at hi
                  exact hin i hi
            · intro k hk hop
              simp only [List.length_append] at hk
              rcases lt_or_ge k g₁.length with hlt | hge
              · have hkge : rest.length ≤ k := by
                  by_contra hcon
                  have hlt' : k < rest.length := by omega
                  have hor : (g₁.getD k dflt).op = GateOp.or := by
                    rw [hg₁, getD_chain B a t v1 k rest lead hlt']
                    rfl
                  rw [List.getD_append g₁ g₂ dflt k hlt, hor] at hop
                  exact absurd hop (by simp)
                obtain ⟨j, hk'⟩ : ∃ j, k = rest.length + j := ⟨k - rest.length, by omega⟩
                have hj : j < 1 + (if lead then 0 else 1) := by
                  rw [hk'] at hlt
                  omega
                rw [hk'] at hop ⊢
                rcases blockGates_tail_cases B a t v1 rest lead j hj with rfl | ⟨rfl, rfl⟩
                · refine ⟨t, andWire B v1 rest, ?_, Or.inr ⟨?_, ?_⟩⟩
                  · rw [List.getD_append g₁ g₂ dflt (rest.length + 0) (by omega),
                      show rest.length + 0 = rest.length from by omega, hg₁,
                      blockGates_and_gate]
                  · exact Ln_subset_clsL Np Nl (B + blen rest lead) false os t (Finset.mem_Ico.mpr htL)
                  · rcases andWire_spec B v1 rest with h | ⟨k', hk', h⟩
                    · rw [h]
                      exact Finset.mem_union_left _
                        (Pt_subset_clsP Np Nl (B + blen rest lead) false os v1
                          (by simpa [Pt] using hleaves v1 (by simp)))
                    · rw [h]
                      exact Finset.mem_union_right _ (mem_chain_image (by omega))
                · have hor : (g₁.getD (rest.length + 1) dflt).op = GateOp.or := by
                    rw [hg₁, blockGates_join_gate B a t v1 rest]
                  rw [List.getD_append g₁ g₂ dflt (rest.length + 1) (by omega), hor] at hop
                  exact absurd hop (by simp)
              · rw [List.getD_append_right g₁ g₂ dflt k hge] at hop ⊢
                obtain ⟨x, y, hxy, hm | hm⟩ := ih4' (k - g₁.length) (by omega) hop
                · exact ⟨x, y, hxy, Or.inl ⟨Finset.mem_union_left _ hm.1, hm.2⟩⟩
                · exact ⟨x, y, hxy, Or.inr ⟨hm.1, Finset.mem_union_left _ hm.2⟩⟩

end PEqualNP.Outside.L_meta_3245

theorem PEqualNP.Outside.L_meta_3245 : ∀ (x1 x2 : ℕ) (x3 : List (ℕ × List ℕ)),   have x4 : ℕ := x1 + x2;   (∀ x5 ∈ x3, x5.2 ≠ [] ∧ ((x5.1 < x1 ∧ ∀ x7 ∈ x5.2, x1 ≤ x7 ∧ x7 < x4) ∨ x1 ≤ x5.1 ∧ x5.1 < x4 ∧ ∀ x7 ∈ x5.2, x7 < x1)) →     have x6 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x4 x3;     have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x6;     ∃ (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 x4 x6 ∧ (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x8) ∧ (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x4 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x9) ∧ ∀ x10 < x6.gates.length, (x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (x7 x10).inputs = [x13, x14] ∧ (x13 ∈ x8 ∧ x14 ∈ x9 ∨ x13 ∈ x9 ∧ x14 ∈ x8) := by
  intro Np Nl own
  dsimp only
  intro h
  classical
  by_cases hgs : PEqualNP.MetaComplexity.coverGatesB (Np + Nl) true 0 own = []
  · refine ⟨PEqualNP.Outside.L_meta_3245.Pt Np, PEqualNP.Outside.L_meta_3245.Ln Np Nl, ?_, ?_, ?_, ?_⟩
    · simp [PEqualNP.TopForm.IsAO2, PEqualNP.EdgeOwnership.AndOrOnly,
        PEqualNP.MetaComplexity.NestedCover.ReadsBack, PEqualNP.MetaComplexity.coverCircuitB, hgs]
    · intro w hw
      exact Or.inl (by simpa [PEqualNP.Outside.L_meta_3245.Pt] using hw)
    · intro w hw
      exact Or.inl (by simpa [PEqualNP.Outside.L_meta_3245.Ln] using hw)
    · intro k hk
      simp [PEqualNP.MetaComplexity.coverCircuitB, hgs] at hk
  · have hone : own ≠ [] := by
      intro h0
      exact hgs (by rw [h0]; simp [PEqualNP.MetaComplexity.coverGatesB])
    obtain ⟨tx0, htx0⟩ := List.exists_mem_of_ne_nil own hone
    obtain ⟨t0, l0⟩ := tx0
    have hl0 : l0 ≠ [] := (h (t0, l0) htx0).1
    obtain ⟨v0, r0, rfl⟩ := List.exists_cons_of_ne_nil hl0
    have hside0 := (h (t0, v0 :: r0) htx0).2
    have hnpos : 0 < Np + Nl := by
      rcases hside0 with ⟨-, hu⟩ | ⟨-, h2, -⟩
      · have hv := (hu v0 (by simp)).2
        omega
      · omega
    have hD : PEqualNP.MetaComplexity.coverCircuitB (Np + Nl) own
        = ⟨PEqualNP.MetaComplexity.coverGatesB (Np + Nl) true 0 own,
            Np + Nl + (PEqualNP.MetaComplexity.coverGatesB (Np + Nl) true 0 own).length - 1⟩ := by
      simp only [PEqualNP.MetaComplexity.coverCircuitB, if_neg hgs]
    rw [hD]
    obtain ⟨s1, s2, s3, s4⟩ :=
      PEqualNP.Outside.L_meta_3245.shape_aux Np Nl own (Np + Nl) 0 true (Nat.le_refl _) hnpos h
    refine ⟨PEqualNP.Outside.L_meta_3245.clsP Np Nl (Np + Nl) true own,
      PEqualNP.Outside.L_meta_3245.clsL Np Nl (Np + Nl) true own, ?_, ?_, ?_, ?_⟩
    · exact ⟨fun g hg => (PEqualNP.Outside.L_meta_3245.coverGates_shape own (Np + Nl) 0 true g hg).1,
        fun j hj i hi => s1 j hj i hi,
        fun g hg => (PEqualNP.Outside.L_meta_3245.coverGates_shape own (Np + Nl) 0 true g hg).2⟩
    · intro w hw
      exact s2 w hw
    · intro w hw
      exact s3 w hw
    · intro k hk
      exact s4 k hk
