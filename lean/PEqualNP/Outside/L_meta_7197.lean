import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7197

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


attribute [local instance] lineDegreeGateOpDecEq

def ld (gs : List Gate) (d : List ℕ) : List ℕ := gs.foldl (fun d g => d ++ [g.lineDegree d]) d

theorem ld_snoc (gs : List Gate) (g : Gate) (d : List ℕ) : ld (gs ++ [g]) d = ld gs d ++ [g.lineDegree (ld gs d)] := by
  simp [ld, List.foldl_append]

theorem ld_length (gs : List Gate) (d : List ℕ) : (ld gs d).length = d.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [ld]
  | append_singleton gs g ih => rw [ld_snoc]; simp [ih]; omega

theorem ld_prefix (gs hs : List Gate) (d : List ℕ) (i : ℕ) (hi : i < d.length + gs.length) :
    (ld (gs ++ hs) d).getD i 0 = (ld gs d).getD i 0 := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, ld_snoc, ← ih]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [ld_length]; simp; omega)]

theorem ld_gate (gs : List Gate) (d : List ℕ) (j : ℕ) (hj : j < gs.length) (a b : ℕ) (h : gs[j].inputs = [a, b])
    (ha : a < d.length + j) (hb : b < d.length + j) :
    (ld gs d).getD (d.length + j) 0 = if gs[j].op = GateOp.and then (ld gs d).getD a 0 + (ld gs d).getD b 0
      else max ((ld gs d).getD a 0) ((ld gs d).getD b 0) := by
  have e : gs = gs.take j ++ ([gs[j]] ++ gs.drop (j + 1)) := by simp
  have hl : (gs.take j).length = j := by rw [List.length_take]; omega
  have pa : ∀ w, w < d.length + j → (ld gs d).getD w 0 = (ld (gs.take j) d).getD w 0 := by
    intro w hw
    conv_lhs => rw [e]
    exact ld_prefix _ _ _ _ (by omega)
  have pg : (ld gs d).getD (d.length + j) 0 = (ld (gs.take j ++ [gs[j]]) d).getD (d.length + j) 0 := by
    conv_lhs => rw [e, ← List.append_assoc]
    exact ld_prefix _ _ _ _ (by simp; omega)
  rw [pg, pa a ha, pa b hb, ld_snoc]
  have l1 : d.length + j = (ld (gs.take j) d).length := by rw [ld_length, hl]
  rw [l1]
  have : (ld (gs.take j) d ++ [gs[j].lineDegree (ld (gs.take j) d)]).getD (ld (gs.take j) d).length 0 = gs[j].lineDegree (ld (gs.take j) d) := by
    simp [List.getD_eq_getElem?_getD]
  rw [this, Gate.lineDegree, h]
  simp

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_7197

theorem PEqualNP.Outside.L_meta_7197 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x3 → (∀ x5 < x1 + x2 + x3.size, (x3.lineDegrees (x1 + x2) (Finset.range x1)).getD x5 (0 : ℕ) ≤ (1 : ℕ) ∧ (x3.lineDegrees (x1 + x2) (Finset.Ico x1 (x1 + x2))).getD x5 (0 : ℕ) ≤ (1 : ℕ)) → ∃ (x6 : Finset ℕ) (x7 : Finset ℕ), (∀ x8 ∈ x6, x8 < x1 ∨ ∃ x10 < x3.size, x8 = x1 + x2 + x10 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).inputs, x11 ∈ x6) ∧ (∀ x8 ∈ x7, x1 ≤ x8 ∧ x8 < x1 + x2 ∨ ∃ x10 < x3.size, x8 = x1 + x2 + x10 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).inputs, x11 ∈ x7) ∧ ∀ x8 < x3.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x8).inputs = [x11, x12] ∧ (x11 ∈ x6 ∧ x12 ∈ x7 ∨ x11 ∈ x7 ∧ x12 ∈ x6) := by
  intro n m C hC hd
  classical
  let dL := C.lineDegrees (n + m) (Finset.range n)
  let dR := C.lineDegrees (n + m) (Finset.Ico n (n + m))
  have hlen : ∀ M : Finset ℕ, ((List.range (n + m)).map fun i => if i ∈ M then 1 else 0).length = n + m := by intro M; simp
  have inp : ∀ (M : Finset ℕ) (w : ℕ), w < n + m → (C.lineDegrees (n + m) M).getD w 0 = if w ∈ M then 1 else 0 := by
    intro M w hw
    have h := PEqualNP.Outside.L_meta_7197.ld_prefix [] C.gates ((List.range (n + m)).map fun i => if i ∈ M then 1 else 0) w (by simpa using hw)
    rw [List.nil_append] at h
    refine h.trans ?_
    simp [PEqualNP.Outside.L_meta_7197.ld, List.getD_eq_getElem?_getD, hw]
  have g2 : ∀ j < C.size, ∃ a b, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, b] ∧ a < n + m + j ∧ b < n + m + j ∧
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      ∀ M : Finset ℕ, (C.lineDegrees (n + m) M).getD (n + m + j) 0 = if (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and then (C.lineDegrees (n + m) M).getD a 0 + (C.lineDegrees (n + m) M).getD b 0
        else max ((C.lineDegrees (n + m) M).getD a 0) ((C.lineDegrees (n + m) M).getD b 0) := by
    intro j hj
    have hj' : j < C.gates.length := hj
    have e : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj'
    have h2 := hC.2.2 _ (List.getElem_mem hj')
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 h2
    have h3 := hC.2.1 j hj'
    rw [e, hab] at h3
    refine ⟨a, b, by rw [e, hab], h3 a (by simp), h3 b (by simp), by rw [e]; exact hC.1 _ (List.getElem_mem hj'), fun M => ?_⟩
    rw [e]
    have := PEqualNP.Outside.L_meta_7197.ld_gate C.gates ((List.range (n + m)).map fun i => if i ∈ M then 1 else 0) j hj' a b hab (by rw [hlen]; exact h3 a (by simp)) (by rw [hlen]; exact h3 b (by simp))
    rw [hlen] at this
    refine Eq.trans this ?_
    by_cases hh : C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.and
    · rw [if_pos hh, if_pos hh]; rfl
    · rw [if_neg hh, if_neg hh]; rfl
  have pos : ∀ w, w < n + m + C.size → 1 ≤ dL.getD w 0 + dR.getD w 0 := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases h : w < n + m
      · simp only [dL, dR, inp _ w h, Finset.mem_range, Finset.mem_Ico]
        split_ifs <;> omega
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + m + j := ⟨w - (n + m), by omega⟩
        obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := g2 j (by omega)
        have ia := ih a (by omega) (by omega)
        simp only [dL, dR] at ia ⊢
        rw [h5, h5]
        split_ifs <;> omega
  have bd : ∀ w, w < n + m + C.size → dL.getD w 0 ≤ 1 ∧ dR.getD w 0 ≤ 1 := hd
  refine ⟨(Finset.range (n + m + C.size)).filter fun w => dR.getD w 0 = 0, (Finset.range (n + m + C.size)).filter fun w => dL.getD w 0 = 0, ?_, ?_, ?_⟩
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨hw1, hw2⟩ := hw
    by_cases h : w < n + m
    · left
      simp only [dR, inp _ w h, Finset.mem_Ico] at hw2
      split_ifs at hw2 <;> omega
    · right
      obtain ⟨j, rfl⟩ : ∃ j, w = n + m + j := ⟨w - (n + m), by omega⟩
      obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := g2 j (by omega)
      have pa := pos a (by omega)
      have pb := pos b (by omega)
      have bw := (bd (n + m + j) hw1).1
      simp only [dL, dR] at pa pb bw hw2 ⊢
      rw [h5] at bw hw2
      refine ⟨j, by omega, rfl, ?_, ?_⟩
      · rcases h4 with h4 | h4
        · rw [if_pos h4] at bw hw2; omega
        · exact h4
      · intro x hx
        rw [h1] at hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        simp only [Finset.mem_filter, Finset.mem_range]
        rcases hx with rfl | rfl
        · refine ⟨by omega, ?_⟩
          split_ifs at hw2 <;> omega
        · refine ⟨by omega, ?_⟩
          split_ifs at hw2 <;> omega
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨hw1, hw2⟩ := hw
    by_cases h : w < n + m
    · left
      simp only [dL, inp _ w h, Finset.mem_range] at hw2
      split_ifs at hw2 <;> omega
    · right
      obtain ⟨j, rfl⟩ : ∃ j, w = n + m + j := ⟨w - (n + m), by omega⟩
      obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := g2 j (by omega)
      have pa := pos a (by omega)
      have pb := pos b (by omega)
      have bw := (bd (n + m + j) hw1).2
      simp only [dL, dR] at pa pb bw hw2 ⊢
      rw [h5] at bw hw2
      refine ⟨j, by omega, rfl, ?_, ?_⟩
      · rcases h4 with h4 | h4
        · rw [if_pos h4] at bw hw2; omega
        · exact h4
      · intro x hx
        rw [h1] at hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        simp only [Finset.mem_filter, Finset.mem_range]
        rcases hx with rfl | rfl
        · refine ⟨by omega, ?_⟩
          split_ifs at hw2 <;> omega
        · refine ⟨by omega, ?_⟩
          split_ifs at hw2 <;> omega
  · intro j hj hop
    obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := g2 j hj
    refine ⟨a, b, h1, ?_⟩
    have pa := pos a (by omega)
    have pb := pos b (by omega)
    have bw := bd (n + m + j) (by omega)
    simp only [dL, dR] at pa pb bw ⊢
    rw [h5, h5, if_pos hop, if_pos hop] at bw
    simp only [Finset.mem_filter, Finset.mem_range]
    have ha : a < n + m + C.size := by omega
    have hb : b < n + m + C.size := by omega
    simp only [ha, hb, true_and]
    omega
