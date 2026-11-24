import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3245
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def dflt : Gate := ⟨GateOp.or, []⟩

def accw (B v1 i : ℕ) : ℕ := if i = 0 then v1 else B + (i - 1)

def bg (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) (j : ℕ) : Gate :=
  if j < rest.length then ⟨GateOp.or, [accw B v1 j, rest.getD j 0]⟩
  else if j = rest.length then ⟨GateOp.and, [t, accw B v1 rest.length]⟩
  else if lead = false ∧ j = rest.length + 1 then ⟨GateOp.or, [a, B + rest.length]⟩
  else dflt

theorem accw_list (B v1 r i : ℕ) (hi : i ≤ r) :
    (v1 :: (List.range r).map (fun j => B + j)).getD i 0 = accw B v1 i := by
  rcases i with _ | i
  · simp [accw]
  · have : i < r := by omega
    simp [accw, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range this]

theorem block_len (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v1 rest lead).length = rest.length + 1 + (if lead = true then 0 else 1) := by
  unfold blockGates
  by_cases h : lead = true <;> simp [h]

def orPart (B v1 : ℕ) (rest : List ℕ) : List Gate :=
  (List.range rest.length).map (fun i =>
    (⟨GateOp.or, [(v1 :: (List.range rest.length).map (fun j => B + j)).getD i 0, rest.getD i 0]⟩ : Gate))

theorem orPart_len (B v1 : ℕ) (rest : List ℕ) : (orPart B v1 rest).length = rest.length := by
  simp [orPart]

theorem orPart_get (B v1 : ℕ) (rest : List ℕ) (j : ℕ) (hj : j < rest.length) :
    (orPart B v1 rest).getD j dflt = ⟨GateOp.or, [accw B v1 j, rest.getD j 0]⟩ := by
  rw [List.getD_eq_getElem _ _ (by rw [orPart_len]; exact hj)]
  simp only [orPart, List.getElem_map, List.getElem_range]
  rw [accw_list B v1 rest.length j (by omega)]

theorem block_get (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) (j : ℕ)
    (hj : j < (blockGates B a t v1 rest lead).length) :
    (blockGates B a t v1 rest lead).getD j dflt = bg B a t v1 rest lead j := by
  rw [block_len] at hj
  have hb : blockGates B a t v1 rest lead =
      orPart B v1 rest ++ (⟨GateOp.and, [t, accw B v1 rest.length]⟩ ::
        (if lead = true then [] else [⟨GateOp.or, [a, B + rest.length]⟩])) := by
    unfold blockGates orPart
    rw [accw_list B v1 rest.length rest.length (le_refl _)]
  rw [hb]
  unfold bg
  by_cases hjr : j < rest.length
  · rw [if_pos hjr, List.getD_append _ _ _ _ (by rw [orPart_len]; exact hjr)]
    exact orPart_get B v1 rest j hjr
  · by_cases hjr2 : j = rest.length
    · subst hjr2
      rw [if_neg hjr, if_pos rfl, List.getD_append_right _ _ _ _ (by rw [orPart_len])]
      rw [orPart_len, Nat.sub_self]
      simp
    · have hj2 : j = rest.length + 1 := by
        by_cases hl : lead = true
        · simp [hl] at hj; omega
        · simp [hl] at hj; omega
      subst hj2
      have hl : lead = false := by
        by_cases hl : lead = true
        · simp [hl] at hj
        · simpa using hl
      subst hl
      rw [if_neg hjr, if_neg hjr2, if_pos (show (false = false ∧ rest.length + 1 = rest.length + 1) from ⟨rfl, rfl⟩)]
      rw [List.getD_append_right _ _ _ _ (by rw [orPart_len]; omega), orPart_len]
      simp


def Good (P0 L0 : Finset ℕ) (B : ℕ) (gs : List Gate) (P L : Finset ℕ) : Prop :=
  (∀ j < gs.length, ((gs.getD j dflt).op = GateOp.and ∨ (gs.getD j dflt).op = GateOp.or) ∧
      (gs.getD j dflt).inputs.length = 2 ∧ ∀ i ∈ (gs.getD j dflt).inputs, i < B + j) ∧
  (∀ w ∈ P, w ∈ P0 ∨ ∃ j < gs.length, w = B + j ∧ (gs.getD j dflt).op = GateOp.or ∧
      ∀ u ∈ (gs.getD j dflt).inputs, u ∈ P) ∧
  (∀ w ∈ L, w ∈ L0 ∨ ∃ j < gs.length, w = B + j ∧ (gs.getD j dflt).op = GateOp.or ∧
      ∀ u ∈ (gs.getD j dflt).inputs, u ∈ L) ∧
  (∀ j < gs.length, (gs.getD j dflt).op = GateOp.and → ∃ p q, (gs.getD j dflt).inputs = [p, q] ∧
      ((p ∈ P ∧ q ∈ L) ∨ (p ∈ L ∧ q ∈ P))) ∧
  P0 ⊆ P ∧ L0 ⊆ L

theorem good_nil (P0 L0 : Finset ℕ) (B : ℕ) : Good P0 L0 B [] P0 L0 := by
  refine ⟨by simp, ?_, ?_, by simp, subset_rfl, subset_rfl⟩
  · intro w hw; exact Or.inl hw
  · intro w hw; exact Or.inl hw

theorem good_swap (P0 L0 : Finset ℕ) (B : ℕ) (gs : List Gate) (P L : Finset ℕ)
    (h : Good P0 L0 B gs P L) : Good L0 P0 B gs L P := by
  obtain ⟨a, b, c, d, e, f⟩ := h
  refine ⟨a, c, b, ?_, f, e⟩
  intro j hj hand
  obtain ⟨p, q, hpq, hpl⟩ := d j hj hand
  exact ⟨p, q, hpq, hpl.symm⟩

theorem good_append (P0 L0 : Finset ℕ) (B : ℕ) (gs1 gs2 : List Gate) (P1 L1 P2 L2 : Finset ℕ)
    (h1 : Good P0 L0 B gs1 P1 L1) (h2 : Good P0 L0 (B + gs1.length) gs2 P2 L2) :
    Good P0 L0 B (gs1 ++ gs2) (P1 ∪ P2) (L1 ∪ L2) := by
  obtain ⟨a1, b1, c1, d1, e1, f1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2⟩ := h2
  have gl : ∀ j, j < gs1.length → (gs1 ++ gs2).getD j dflt = gs1.getD j dflt :=
    fun j hj => List.getD_append _ _ _ _ hj
  have gr : ∀ j, (gs1 ++ gs2).getD (gs1.length + j) dflt = gs2.getD j dflt := by
    intro j
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simp only [List.length_append] at hj
    by_cases hj1 : j < gs1.length
    · rw [gl j hj1]; exact a1 j hj1
    · obtain ⟨k, rfl⟩ : ∃ k, j = gs1.length + k := ⟨j - gs1.length, by omega⟩
      rw [gr k]
      obtain ⟨x, y, z⟩ := a2 k (by omega)
      refine ⟨x, y, fun i hi => ?_⟩
      have := z i hi
      omega
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · rcases b1 w hw with h | ⟨j, hj, hwj, hop, hin⟩
      · exact Or.inl h
      · right
        refine ⟨j, by simp only [List.length_append]; omega, hwj, ?_, ?_⟩
        · rw [gl j hj]; exact hop
        · intro u hu; rw [gl j hj] at hu; exact Finset.mem_union_left _ (hin u hu)
    · rcases b2 w hw with h | ⟨j, hj, hwj, hop, hin⟩
      · exact Or.inl h
      · right
        refine ⟨gs1.length + j, by simp only [List.length_append]; omega, by omega, ?_, ?_⟩
        · rw [gr j]; exact hop
        · intro u hu; rw [gr j] at hu; exact Finset.mem_union_right _ (hin u hu)
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · rcases c1 w hw with h | ⟨j, hj, hwj, hop, hin⟩
      · exact Or.inl h
      · right
        refine ⟨j, by simp only [List.length_append]; omega, hwj, ?_, ?_⟩
        · rw [gl j hj]; exact hop
        · intro u hu; rw [gl j hj] at hu; exact Finset.mem_union_left _ (hin u hu)
    · rcases c2 w hw with h | ⟨j, hj, hwj, hop, hin⟩
      · exact Or.inl h
      · right
        refine ⟨gs1.length + j, by simp only [List.length_append]; omega, by omega, ?_, ?_⟩
        · rw [gr j]; exact hop
        · intro u hu; rw [gr j] at hu; exact Finset.mem_union_right _ (hin u hu)
  · intro j hj hand
    simp only [List.length_append] at hj
    by_cases hj1 : j < gs1.length
    · rw [gl j hj1] at hand ⊢
      obtain ⟨p, q, hpq, hpl⟩ := d1 j hj1 hand
      refine ⟨p, q, hpq, ?_⟩
      rcases hpl with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · exact Or.inl ⟨Finset.mem_union_left _ hp, Finset.mem_union_left _ hq⟩
      · exact Or.inr ⟨Finset.mem_union_left _ hp, Finset.mem_union_left _ hq⟩
    · obtain ⟨k, rfl⟩ : ∃ k, j = gs1.length + k := ⟨j - gs1.length, by omega⟩
      rw [gr k] at hand ⊢
      obtain ⟨p, q, hpq, hpl⟩ := d2 k (by omega) hand
      refine ⟨p, q, hpq, ?_⟩
      rcases hpl with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · exact Or.inl ⟨Finset.mem_union_right _ hp, Finset.mem_union_right _ hq⟩
      · exact Or.inr ⟨Finset.mem_union_right _ hp, Finset.mem_union_right _ hq⟩
  · exact e1.trans Finset.subset_union_left
  · exact f1.trans Finset.subset_union_left


theorem bg_lt (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) (j : ℕ) (h : j < rest.length) :
    bg B a t v1 rest lead j = ⟨GateOp.or, [accw B v1 j, rest.getD j 0]⟩ := by
  unfold bg; rw [if_pos h]

theorem bg_eq (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    bg B a t v1 rest lead rest.length = ⟨GateOp.and, [t, accw B v1 rest.length]⟩ := by
  unfold bg; rw [if_neg (lt_irrefl _), if_pos rfl]

theorem bg_join (B a t v1 : ℕ) (rest : List ℕ) :
    bg B a t v1 rest false (rest.length + 1) = ⟨GateOp.or, [a, B + rest.length]⟩ := by
  unfold bg
  rw [if_neg (by omega), if_neg (by omega), if_pos (show (false = false ∧ rest.length + 1 = rest.length + 1) from ⟨rfl, rfl⟩)]

theorem cases3 (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) (j : ℕ)
    (hj : j < (blockGates B a t v1 rest lead).length) :
    j < rest.length ∨ j = rest.length ∨ (lead = false ∧ j = rest.length + 1) := by
  rw [block_len] at hj
  by_cases hl : lead = true
  · simp [hl] at hj; omega
  · have : lead = false := by simpa using hl
    subst this
    simp at hj
    by_cases h1 : j < rest.length
    · exact Or.inl h1
    · by_cases h2 : j = rest.length
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨rfl, by omega⟩)

theorem good_block (P0 L0 : Finset ℕ) (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool)
    (hP0 : ∀ w ∈ P0, w < B) (hL0 : ∀ w ∈ L0, w < B) (ha : lead = false → a < B)
    (ht : t ∈ P0) (hv : ∀ v ∈ v1 :: rest, v ∈ L0) :
    ∃ P L, Good P0 L0 B (blockGates B a t v1 rest lead) P L := by
  let acc : Finset ℕ := (Finset.range rest.length).image (fun i => B + i)
  have hv1 : v1 ∈ L0 := hv v1 (by simp)
  have hrest : ∀ j < rest.length, rest.getD j 0 ∈ L0 := by
    intro j hj
    rw [List.getD_eq_getElem _ _ hj]
    exact hv _ (List.mem_cons_of_mem _ (List.getElem_mem hj))
  have haccw : ∀ i ≤ rest.length, accw B v1 i ∈ L0 ∪ acc := by
    intro i hi
    unfold accw
    split_ifs with h
    · exact Finset.mem_union_left _ hv1
    · apply Finset.mem_union_right
      simp only [acc, Finset.mem_image, Finset.mem_range]
      exact ⟨i - 1, by omega, rfl⟩
  have haccw_lt : ∀ i ≤ rest.length, accw B v1 i < B + i := by
    intro i hi
    unfold accw
    split_ifs with h
    · have := hL0 v1 hv1; omega
    · omega
  refine ⟨P0, L0 ∪ acc, ?_, ?_, ?_, ?_, subset_rfl, Finset.subset_union_left⟩
  · intro j hj
    have hg := block_get B a t v1 rest lead j hj
    rw [hg]
    rcases cases3 B a t v1 rest lead j hj with h | h | ⟨hl, h⟩
    · rw [bg_lt B a t v1 rest lead j h]
      refine ⟨Or.inr rfl, rfl, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact haccw_lt j h.le
      · have := hL0 _ (hrest j h); omega
    · subst h
      rw [bg_eq]
      refine ⟨Or.inl rfl, rfl, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · have := hP0 _ ht; omega
      · exact haccw_lt _ (le_refl _)
    · subst h; subst hl
      rw [bg_join]
      refine ⟨Or.inr rfl, rfl, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · have := ha rfl; omega
      · omega
  · intro w hw; exact Or.inl hw
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Or.inl hw
    · right
      simp only [acc, Finset.mem_image, Finset.mem_range] at hw
      obtain ⟨i, hi, rfl⟩ := hw
      have hj : i < (blockGates B a t v1 rest lead).length := by
        rw [block_len]; split_ifs <;> omega
      refine ⟨i, hj, rfl, ?_, ?_⟩
      · rw [block_get B a t v1 rest lead i hj, bg_lt B a t v1 rest lead i hi]
      · intro u hu
        rw [block_get B a t v1 rest lead i hj, bg_lt B a t v1 rest lead i hi] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact haccw i hi.le
        · exact Finset.mem_union_left _ (hrest i hi)
  · intro j hj hand
    have hg := block_get B a t v1 rest lead j hj
    rw [hg] at hand ⊢
    rcases cases3 B a t v1 rest lead j hj with h | h | ⟨hl, h⟩
    · rw [bg_lt B a t v1 rest lead j h] at hand
      exact absurd hand (by intro e; cases e)
    · subst h
      rw [bg_eq] at hand ⊢
      exact ⟨t, accw B v1 rest.length, rfl, Or.inl ⟨ht, haccw _ (le_refl _)⟩⟩
    · subst h; subst hl
      rw [bg_join] at hand
      exact absurd hand (by intro e; cases e)


theorem good_cover (P0 L0 : Finset ℕ) : ∀ (own : List (ℕ × List ℕ)),
    (∀ o ∈ own, o.2 ≠ [] ∧ ((o.1 ∈ P0 ∧ ∀ v ∈ o.2, v ∈ L0) ∨ (o.1 ∈ L0 ∧ ∀ v ∈ o.2, v ∈ P0))) →
    ∀ (B a : ℕ) (lead : Bool), (∀ w ∈ P0, w < B) → (∀ w ∈ L0, w < B) → (lead = false → a < B) →
      ∃ P L, Good P0 L0 B (coverGatesB B lead a own) P L := by
  intro own
  induction own with
  | nil =>
    intro _ B a lead _ _ _
    exact ⟨P0, L0, by simpa [coverGatesB] using good_nil P0 L0 B⟩
  | cons o os ih =>
    intro hwf B a lead hP hL ha
    obtain ⟨t, l⟩ := o
    have hhead := hwf (t, l) (by simp)
    have htail : ∀ o' ∈ os, o'.2 ≠ [] ∧ ((o'.1 ∈ P0 ∧ ∀ v ∈ o'.2, v ∈ L0) ∨
        (o'.1 ∈ L0 ∧ ∀ v ∈ o'.2, v ∈ P0)) := fun o' h => hwf o' (by simp [h])
    rcases l with _ | ⟨v1, rest⟩
    · exact absurd rfl hhead.1
    · have hcov : coverGatesB B lead a ((t, v1 :: rest) :: os) =
          blockGates B a t v1 rest lead ++
            coverGatesB (B + (blockGates B a t v1 rest lead).length) false
              (B + (blockGates B a t v1 rest lead).length - 1) os := by
        simp [coverGatesB]
      have hblk : ∃ P1 L1, Good P0 L0 B (blockGates B a t v1 rest lead) P1 L1 := by
        rcases hhead.2 with ⟨ht, hv⟩ | ⟨ht, hv⟩
        · exact good_block P0 L0 B a t v1 rest lead hP hL ha ht hv
        · obtain ⟨P', L', h⟩ := good_block L0 P0 B a t v1 rest lead hL hP ha ht hv
          exact ⟨L', P', good_swap _ _ _ _ _ _ h⟩
      obtain ⟨P1, L1, h1⟩ := hblk
      have hlen : 1 ≤ (blockGates B a t v1 rest lead).length := by
        rw [block_len]; omega
      obtain ⟨P2, L2, h2⟩ := ih htail (B + (blockGates B a t v1 rest lead).length)
        (B + (blockGates B a t v1 rest lead).length - 1) false
        (fun w hw => by have := hP w hw; omega) (fun w hw => by have := hL w hw; omega)
        (fun _ => by omega)
      rw [hcov]
      exact ⟨P1 ∪ P2, L1 ∪ L2, good_append P0 L0 B _ _ P1 L1 P2 L2 h1 h2⟩

theorem cc_gates (n : ℕ) (own : List (ℕ × List ℕ)) :
    (coverCircuitB n own).gates = coverGatesB n true 0 own := by
  unfold coverCircuitB
  by_cases h : coverGatesB n true 0 own = []
  · simp [h]
  · simp [h]

end PEqualNP.Outside.L_meta_3245

theorem PEqualNP.Outside.L_meta_3245 : ∀ (x1 x2 : ℕ) (x3 : List (ℕ × List ℕ)),   have x4 : ℕ := x1 + x2;   (∀ x5 ∈ x3, x5.2 ≠ [] ∧ ((x5.1 < x1 ∧ ∀ x7 ∈ x5.2, x1 ≤ x7 ∧ x7 < x4) ∨ x1 ≤ x5.1 ∧ x5.1 < x4 ∧ ∀ x7 ∈ x5.2, x7 < x1)) →     have x6 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x4 x3;     have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x6;     ∃ (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 x4 x6 ∧ (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x8) ∧ (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x4 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x9) ∧ ∀ x10 < x6.gates.length, (x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (x7 x10).inputs = [x13, x14] ∧ (x13 ∈ x8 ∧ x14 ∈ x9 ∨ x13 ∈ x9 ∧ x14 ∈ x8) := by
  intro x1 x2 x3
  dsimp only
  intro hwf
  have hP0 : ∀ w ∈ Finset.range x1, w < x1 + x2 := by
    intro w hw; simp at hw; omega
  have hL0 : ∀ w ∈ Finset.Ico x1 (x1 + x2), w < x1 + x2 := by
    intro w hw; simp at hw; omega
  have hwf' : ∀ o ∈ x3, o.2 ≠ [] ∧
      ((o.1 ∈ Finset.range x1 ∧ ∀ v ∈ o.2, v ∈ Finset.Ico x1 (x1 + x2)) ∨
        (o.1 ∈ Finset.Ico x1 (x1 + x2) ∧ ∀ v ∈ o.2, v ∈ Finset.range x1)) := by
    intro o ho
    obtain ⟨h1, h2⟩ := hwf o ho
    refine ⟨h1, ?_⟩
    rcases h2 with ⟨a, b⟩ | ⟨a, b, c⟩
    · left
      refine ⟨by simpa using a, fun v hv => ?_⟩
      have := b v hv; simp; omega
    · right
      refine ⟨by simp; omega, fun v hv => ?_⟩
      have := c v hv; simpa using this
  obtain ⟨P, L, hgood⟩ := PEqualNP.Outside.L_meta_3245.good_cover (Finset.range x1)
    (Finset.Ico x1 (x1 + x2)) x3 hwf' (x1 + x2) 0 true hP0 hL0 (by simp)
  have hg := PEqualNP.Outside.L_meta_3245.cc_gates (x1 + x2) x3
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hgood
  have gat : ∀ j, PEqualNP.MetaComplexity.NestedCover.gateAt
      (PEqualNP.MetaComplexity.coverCircuitB (x1 + x2) x3) j =
        (PEqualNP.MetaComplexity.coverGatesB (x1 + x2) true 0 x3).getD j
          PEqualNP.Outside.L_meta_3245.dflt := by
    intro j
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [hg]; rfl
  refine ⟨P, L, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g hg'
    rw [hg] at hg'
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg'
    have := (g1 j hj).1
    rwa [List.getD_eq_getElem _ _ hj] at this
  · intro j hj
    rw [hg] at hj
    intro i hi
    rw [gat j] at hi
    exact (g1 j hj).2.2 i hi
  · intro g hg'
    rw [hg] at hg'
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg'
    have := (g1 j hj).2.1
    rwa [List.getD_eq_getElem _ _ hj] at this
  · intro w hw
    rcases g2 w hw with h | ⟨j, hj, hwj, hop, hin⟩
    · left; simpa using h
    · right
      refine ⟨j, by rw [hg]; exact hj, hwj, by rw [gat j]; exact hop, ?_⟩
      intro u hu; rw [gat j] at hu; exact hin u hu
  · intro w hw
    rcases g3 w hw with h | ⟨j, hj, hwj, hop, hin⟩
    · left; simpa using h
    · right
      refine ⟨j, by rw [hg]; exact hj, hwj, by rw [gat j]; exact hop, ?_⟩
      intro u hu; rw [gat j] at hu; exact hin u hu
  · intro j hj hand
    rw [hg] at hj
    rw [gat j] at hand ⊢
    exact g4 j hj hand
