import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3245

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def dg : Gate := ⟨GateOp.or, []⟩

def ChainOK (P N B : ℕ) (gs : List Gate) (i : ℕ) (s : Prop) (w : ℕ) : Prop :=
  (w < N ∧ (w < P ↔ s)) ∨
  (0 < i ∧ w = B + (i - 1) ∧ (gs.getD (i - 1) dg).op = GateOp.or ∧
    ∃ w' u', (gs.getD (i - 1) dg).inputs = [w', u'] ∧ u' < N ∧ (u' < P ↔ s))

def GoodAt (P N B : ℕ) (gs : List Gate) (i : ℕ) : Prop :=
  (∀ x ∈ (gs.getD i dg).inputs, x < B + i) ∧
  ∃ w u, (gs.getD i dg).inputs = [w, u] ∧
    (((gs.getD i dg).op = GateOp.or ∧ u < N ∧ ChainOK P N B gs i (u < P) w) ∨
     ((gs.getD i dg).op = GateOp.or ∧ N ≤ u) ∨
     ((gs.getD i dg).op = GateOp.and ∧ w < N ∧ ChainOK P N B gs i (¬ w < P) u))

def Good (P N B : ℕ) (gs : List Gate) : Prop := ∀ i < gs.length, GoodAt P N B gs i

theorem get_left (g1 g2 : List Gate) (j : ℕ) (h : j < g1.length) :
    (g1 ++ g2).getD j dg = g1.getD j dg := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem get_right (g1 g2 : List Gate) (j : ℕ) :
    (g1 ++ g2).getD (g1.length + j) dg = g2.getD j dg := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  simp

theorem chain_left (P N B : ℕ) (g1 g2 : List Gate) (i : ℕ) (s : Prop) (w : ℕ)
    (hi : i < g1.length) (h : ChainOK P N B g1 i s w) : ChainOK P N B (g1 ++ g2) i s w := by
  unfold ChainOK at h ⊢
  rw [get_left g1 g2 (i - 1) (by omega)]
  exact h

theorem chain_right (P N B : ℕ) (g1 g2 : List Gate) (k : ℕ) (s : Prop) (w : ℕ)
    (h : ChainOK P N (B + g1.length) g2 k s w) :
    ChainOK P N B (g1 ++ g2) (g1.length + k) s w := by
  rcases h with h | ⟨hk, hw, hop, w', u', hin, hu, hs⟩
  · exact Or.inl h
  · right
    have e : (g1 ++ g2).getD (g1.length + k - 1) dg = g2.getD (k - 1) dg := by
      have : g1.length + k - 1 = g1.length + (k - 1) := by omega
      rw [this, get_right]
    refine ⟨by omega, by omega, ?_, w', u', ?_, hu, hs⟩
    · rw [e]; exact hop
    · rw [e]; exact hin

theorem good_append (P N B : ℕ) (g1 g2 : List Gate) (h1 : Good P N B g1)
    (h2 : Good P N (B + g1.length) g2) : Good P N B (g1 ++ g2) := by
  intro i hi
  by_cases hl : i < g1.length
  · obtain ⟨hr, w, u, hin, hk⟩ := h1 i hl
    have e := get_left g1 g2 i hl
    refine ⟨?_, w, u, ?_, ?_⟩
    · rw [e]; exact hr
    · rw [e]; exact hin
    · rw [e]
      rcases hk with ⟨a, b, c⟩ | hk | ⟨a, b, c⟩
      · exact Or.inl ⟨a, b, chain_left P N B g1 g2 i _ w hl c⟩
      · exact Or.inr (Or.inl hk)
      · exact Or.inr (Or.inr ⟨a, b, chain_left P N B g1 g2 i _ u hl c⟩)
  · obtain ⟨k, rfl⟩ : ∃ k, i = g1.length + k := ⟨i - g1.length, by omega⟩
    have hk2 : k < g2.length := by simp at hi; omega
    obtain ⟨hr, w, u, hin, hk⟩ := h2 k hk2
    have e := get_right g1 g2 k
    refine ⟨?_, w, u, ?_, ?_⟩
    · rw [e]; intro x hx; have := hr x hx; omega
    · rw [e]; exact hin
    · rw [e]
      rcases hk with ⟨a, b, c⟩ | hk | ⟨a, b, c⟩
      · exact Or.inl ⟨a, b, chain_right P N B g1 g2 k _ w c⟩
      · exact Or.inr (Or.inl hk)
      · exact Or.inr (Or.inr ⟨a, b, chain_right P N B g1 g2 k _ u c⟩)

theorem ch_get (B v1 : ℕ) (r i : ℕ) (hi : i ≤ r) :
    (v1 :: (List.range r).map (fun j => B + j)).getD i 0 = if i = 0 then v1 else B + (i - 1) := by
  cases i with
  | zero => simp
  | succ i =>
    rw [List.getD_cons_succ, List.getD_eq_getElem?_getD]
    simp [List.getElem?_range (by omega : i < r)]

theorem block_get_chain (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) (i : ℕ)
    (hi : i < rest.length) :
    (blockGates B a t v1 rest lead).getD i dg =
      ⟨GateOp.or, [(v1 :: (List.range rest.length).map (fun j => B + j)).getD i 0,
        rest.getD i 0]⟩ := by
  unfold blockGates
  rw [get_left _ _ i (by simp [hi]), List.getD_eq_getElem?_getD]
  simp [List.getElem?_range hi]

theorem block_get_and (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v1 rest lead).getD rest.length dg =
      ⟨GateOp.and, [t, (v1 :: (List.range rest.length).map (fun j => B + j)).getD rest.length 0]⟩ := by
  unfold blockGates
  have := get_right ((List.range rest.length).map (fun i =>
      (⟨GateOp.or, [(v1 :: (List.range rest.length).map (fun j => B + j)).getD i 0,
        rest.getD i 0]⟩ : Gate)))
    (⟨GateOp.and, [t, (v1 :: (List.range rest.length).map (fun j => B + j)).getD rest.length 0]⟩ ::
      (if lead then [] else [⟨GateOp.or, [a, B + rest.length]⟩])) 0
  simpa using this

theorem block_get_join (B a t v1 : ℕ) (rest : List ℕ) :
    (blockGates B a t v1 rest false).getD (rest.length + 1) dg =
      ⟨GateOp.or, [a, B + rest.length]⟩ := by
  unfold blockGates
  have := get_right ((List.range rest.length).map (fun i =>
      (⟨GateOp.or, [(v1 :: (List.range rest.length).map (fun j => B + j)).getD i 0,
        rest.getD i 0]⟩ : Gate)))
    (⟨GateOp.and, [t, (v1 :: (List.range rest.length).map (fun j => B + j)).getD rest.length 0]⟩ ::
      (if false = true then [] else [⟨GateOp.or, [a, B + rest.length]⟩])) 1
  simpa using this

theorem block_length (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v1 rest lead).length = rest.length + 1 + (if lead then 0 else 1) := by
  cases lead <;> simp [blockGates]

theorem good_block (P N B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) (s : Prop)
    (hB : N ≤ B) (ha : lead = false → a < B) (ht : t < N ∧ (t < P ↔ ¬ s))
    (hv : ∀ v ∈ v1 :: rest, v < N ∧ (v < P ↔ s)) :
    Good P N B (blockGates B a t v1 rest lead) := by
  have hv1 := hv v1 (by simp)
  have hrest : ∀ i < rest.length, rest.getD i 0 < N ∧ (rest.getD i 0 < P ↔ s) := by
    intro i hi
    rw [List.getD_eq_getElem _ _ hi]
    exact hv _ (List.mem_cons_of_mem _ (List.getElem_mem hi))
  intro i hi
  rw [block_length] at hi
  rcases lt_trichotomy i rest.length with hlt | heq | hgt
  · rw [GoodAt, block_get_chain B a t v1 rest lead i hlt, ch_get B v1 rest.length i hlt.le]
    obtain ⟨hu1, hu2⟩ := hrest i hlt
    refine ⟨?_, _, _, rfl, Or.inl ⟨rfl, hu1, ?_⟩⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · split_ifs <;> omega
      · omega
    · unfold ChainOK
      by_cases h0 : i = 0
      · left
        rw [if_pos h0]
        exact ⟨hv1.1, by rw [hv1.2, hu2]⟩
      · right
        rw [if_neg h0, block_get_chain B a t v1 rest lead (i - 1) (by omega)]
        obtain ⟨hp1, hp2⟩ := hrest (i - 1) (by omega)
        exact ⟨by omega, rfl, rfl, _, _, rfl, hp1, by rw [hp2, hu2]⟩
  · subst heq
    rw [GoodAt, block_get_and, ch_get B v1 rest.length rest.length le_rfl]
    refine ⟨?_, _, _, rfl, Or.inr (Or.inr ⟨rfl, ht.1, ?_⟩)⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · omega
      · split_ifs <;> omega
    · unfold ChainOK
      by_cases h0 : rest.length = 0
      · left
        rw [if_pos h0]
        refine ⟨hv1.1, ?_⟩
        rw [hv1.2, ht.2]; tauto
      · right
        rw [if_neg h0, block_get_chain B a t v1 rest lead (rest.length - 1) (by omega)]
        obtain ⟨hp1, hp2⟩ := hrest (rest.length - 1) (by omega)
        refine ⟨by omega, rfl, rfl, _, _, rfl, hp1, ?_⟩
        rw [hp2, ht.2]; tauto
  · cases lead with
    | true => simp at hi; omega
    | false =>
      have hi' : i = rest.length + 1 := by simp at hi; omega
      subst hi'
      have ha' := ha rfl
      rw [GoodAt, block_get_join]
      refine ⟨?_, _, _, rfl, Or.inr (Or.inl ⟨rfl, by omega⟩)⟩
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> omega

theorem good_cover (P N : ℕ) : ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ),
    N ≤ B → (lead = false → a < B) →
    (∀ x ∈ own, x.2 ≠ [] → ∃ s : Prop, x.1 < N ∧ (x.1 < P ↔ ¬ s) ∧
      ∀ v ∈ x.2, v < N ∧ (v < P ↔ s)) →
    Good P N B (coverGatesB B lead a own)
  | [], _, _, _ => by
      intro _ _ _ i hi
      simp [coverGatesB] at hi
  | (t, []) :: os, B, lead, a => by
      intro hB ha h
      simp only [coverGatesB]
      exact good_cover P N os B lead a hB ha (fun x hx => h x (List.mem_cons_of_mem _ hx))
  | (t, v1 :: rest) :: os, B, lead, a => by
      intro hB ha h
      simp only [coverGatesB]
      obtain ⟨s, ht1, ht2, hv⟩ := h (t, v1 :: rest) (by simp) (by simp)
      apply good_append
      · exact good_block P N B a t v1 rest lead s hB ha ⟨ht1, ht2⟩ hv
      · apply good_cover P N os
        · omega
        · intro _
          have := block_length B a t v1 rest lead
          omega
        · exact fun x hx => h x (List.mem_cons_of_mem _ hx)

end PEqualNP.Outside.L_meta_3245

open PEqualNP.Outside.L_meta_3245 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_3245 : ∀ (x1 x2 : ℕ) (x3 : List (ℕ × List ℕ)),   have x4 : ℕ := x1 + x2;   (∀ x5 ∈ x3, x5.2 ≠ [] ∧ ((x5.1 < x1 ∧ ∀ x7 ∈ x5.2, x1 ≤ x7 ∧ x7 < x4) ∨ x1 ≤ x5.1 ∧ x5.1 < x4 ∧ ∀ x7 ∈ x5.2, x7 < x1)) →     have x6 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x4 x3;     have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x6;     ∃ (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 x4 x6 ∧ (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x8) ∧ (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x4 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x9) ∧ ∀ x10 < x6.gates.length, (x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (x7 x10).inputs = [x13, x14] ∧ (x13 ∈ x8 ∧ x14 ∈ x9 ∨ x13 ∈ x9 ∧ x14 ∈ x8) := by
  intro x1 x2 x3
  dsimp only
  intro hx
  classical
  set N := x1 + x2 with hN
  set gs := coverGatesB N true 0 x3 with hgs
  have hC : (coverCircuitB N x3).gates = gs := by
    unfold coverCircuitB
    split_ifs with h
    · simp [h, hgs]
    · rfl
  have hG : ∀ j, NestedCover.gateAt (coverCircuitB N x3) j = gs.getD j dg := by
    intro j
    unfold NestedCover.gateAt
    rw [hC]
    rfl
  have good : Good x1 N N gs := by
    apply good_cover x1 N x3 N true 0 le_rfl (by simp)
    intro x hxm _
    rcases (hx x hxm).2 with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact ⟨False, by omega, by simp [h1], fun v hv => ⟨(h2 v hv).2, by
        have := (h2 v hv).1; simp; omega⟩⟩
    · exact ⟨True, h2, by simp; omega, fun v hv => ⟨by have := h3 v hv; omega, by
        simp [h3 v hv]⟩⟩
  have hor : GateOp.or ≠ GateOp.and := by intro h; cases h
  refine ⟨Finset.range x1 ∪ ((Finset.range gs.length).filter (fun j =>
      (gs.getD j dg).op = GateOp.or ∧ (gs.getD j dg).inputs.getD 1 0 < x1)).image (fun j => N + j),
    (Finset.range N).filter (fun v => x1 ≤ v) ∪ ((Finset.range gs.length).filter (fun j =>
      (gs.getD j dg).op = GateOp.or ∧ x1 ≤ (gs.getD j dg).inputs.getD 1 0 ∧
        (gs.getD j dg).inputs.getD 1 0 < N)).image (fun j => N + j), ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rw [hC] at hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      obtain ⟨_, w, u, _, hk⟩ := good j hj
      rw [← List.getD_eq_getElem _ dg hj]
      rcases hk with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inr h
      · exact Or.inr h
      · exact Or.inl h
    · intro j hj i hi
      rw [hC] at hj
      rw [hG] at hi
      exact (good j hj).1 i hi
    · intro g hg
      rw [hC] at hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      obtain ⟨_, w, u, hin, _⟩ := good j hj
      rw [← List.getD_eq_getElem _ dg hj, hin]
      rfl
  · intro v hv
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_image, Finset.mem_filter] at hv
    rcases hv with hv | ⟨j, ⟨hj, hop, hu⟩, rfl⟩
    · exact Or.inl hv
    · right
      rw [hC]
      refine ⟨j, hj, rfl, by rw [hG]; exact hop, ?_⟩
      rw [hG]
      obtain ⟨_, w, u, hin, hk⟩ := good j hj
      rw [hin] at hu ⊢
      simp only [List.getD_cons_succ, List.getD_cons_zero] at hu
      rcases hk with ⟨_, hu1, hc⟩ | ⟨_, h2⟩ | ⟨h3, _⟩
      · intro x hxm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxm
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_image, Finset.mem_filter]
        rcases hxm with rfl | rfl
        · rcases hc with ⟨hw1, hw2⟩ | ⟨hpos, hw, hop', w', u', hin', hu', hs'⟩
          · left; exact hw2.2 hu
          · right
            refine ⟨j - 1, ⟨by omega, hop', ?_⟩, by omega⟩
            rw [hin']
            exact hs'.2 hu
        · left; exact hu
      · omega
      · rw [h3] at hop; exact absurd hop (by intro h; cases h)
  · intro v hv
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_image, Finset.mem_filter] at hv
    rcases hv with ⟨hv1, hv2⟩ | ⟨j, ⟨hj, hop, hu1, hu2⟩, rfl⟩
    · exact Or.inl ⟨hv2, hv1⟩
    · right
      rw [hC]
      refine ⟨j, hj, rfl, by rw [hG]; exact hop, ?_⟩
      rw [hG]
      obtain ⟨_, w, u, hin, hk⟩ := good j hj
      rw [hin] at hu1 hu2 ⊢
      simp only [List.getD_cons_succ, List.getD_cons_zero] at hu1 hu2
      rcases hk with ⟨_, _, hc⟩ | ⟨_, h2⟩ | ⟨h3, _⟩
      · intro x hxm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxm
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_image, Finset.mem_filter]
        rcases hxm with rfl | rfl
        · rcases hc with ⟨hw1, hw2⟩ | ⟨hpos, hw, hop', w', u', hin', hu', hs'⟩
          · left
            refine ⟨hw1, ?_⟩
            by_contra hlt
            push_neg at hlt
            exact (Nat.not_lt.mpr hu1) (hw2.1 hlt)
          · right
            refine ⟨j - 1, ⟨by omega, hop', ?_⟩, by omega⟩
            rw [hin']
            simp only [List.getD_cons_succ, List.getD_cons_zero]
            refine ⟨?_, hu'⟩
            by_contra hlt
            push_neg at hlt
            exact (Nat.not_lt.mpr hu1) (hs'.1 hlt)
        · left; exact ⟨hu2, hu1⟩
      · omega
      · rw [h3] at hop; exact absurd hop (by intro h; cases h)
  · intro j hj hand
    rw [hC] at hj
    rw [hG] at hand ⊢
    obtain ⟨_, w, u, hin, hk⟩ := good j hj
    refine ⟨w, u, hin, ?_⟩
    rcases hk with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, hw, hc⟩
    · rw [h1] at hand; exact absurd hand (by intro h; cases h)
    · rw [h1] at hand; exact absurd hand (by intro h; cases h)
    · simp only [Finset.mem_union, Finset.mem_range, Finset.mem_image, Finset.mem_filter]
      by_cases hwp : w < x1
      · left
        refine ⟨Or.inl hwp, ?_⟩
        rcases hc with ⟨hu1, hu2⟩ | ⟨hpos, hu, hop', w', u', hin', hu', hs'⟩
        · left
          refine ⟨hu1, ?_⟩
          by_contra hlt
          push_neg at hlt
          exact (hu2.1 hlt) hwp
        · right
          refine ⟨j - 1, ⟨by omega, hop', ?_⟩, by omega⟩
          rw [hin']
          simp only [List.getD_cons_succ, List.getD_cons_zero]
          refine ⟨?_, hu'⟩
          by_contra hlt
          push_neg at hlt
          exact (hs'.1 hlt) hwp
      · right
        refine ⟨Or.inl ⟨hw, by omega⟩, ?_⟩
        rcases hc with ⟨hu1, hu2⟩ | ⟨hpos, hu, hop', w', u', hin', hu', hs'⟩
        · left
          exact hu2.2 hwp
        · right
          refine ⟨j - 1, ⟨by omega, hop', ?_⟩, by omega⟩
          rw [hin']
          simp only [List.getD_cons_succ, List.getD_cons_zero]
          exact hs'.2 hwp
