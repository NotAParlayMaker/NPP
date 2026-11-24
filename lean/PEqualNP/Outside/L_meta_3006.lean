import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3006

open PEqualNP.CircuitLowerBounds

private lemma build_gates (x1 x2 : List ℕ)
    (hstep : ∀ (j : Fin x2.length),
      ∃ a ∈ x1 ++ List.take j.val x2, ∃ b ∈ x1 ++ List.take j.val x2,
        x2.get j = a &&& b ∨ x2.get j = a ||| b) :
    ∃ gs : List Gate,
      gs.length = x2.length ∧
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      ∀ k : ℕ,
        gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (x1.map fun v => v.testBit k) =
        (x1 ++ x2).map fun v => v.testBit k := by
  induction x2 using List.reverseRecOn with
  | nil =>
    refine ⟨[], rfl, by simp, ?_⟩
    intro k
    simp
  | append_singleton ys y ih =>
    have hys : ∀ (j : Fin ys.length),
        ∃ a ∈ x1 ++ List.take j.val ys, ∃ b ∈ x1 ++ List.take j.val ys,
          ys.get j = a &&& b ∨ ys.get j = a ||| b := by
      intro j
      have hjlt : j.val < (ys ++ [y]).length := by simp
      have h := hstep ⟨j.val, hjlt⟩
      have htake : List.take j.val (ys ++ [y]) = List.take j.val ys := by
        rw [List.take_append_of_le_length (le_of_lt j.isLt)]
      have hget : (ys ++ [y]).get ⟨j.val, hjlt⟩ = ys.get j := by
        simp [List.getElem_append_left j.isLt]
      simpa only [htake, hget] using h
    obtain ⟨gs, hglen, hgmono, hgwires⟩ := ih hys
    have hlast_lt : ys.length < (ys ++ [y]).length := by simp
    have hlast := hstep ⟨ys.length, hlast_lt⟩
    have htake_last : List.take ys.length (ys ++ [y]) = ys := by
      rw [List.take_append_of_le_length (le_refl _), List.take_length]
    have hget_last : (ys ++ [y]).get ⟨ys.length, hlast_lt⟩ = y := by
      simp
    simp only [htake_last, hget_last] at hlast
    obtain ⟨a, ha, b, hb, hab⟩ := hlast
    obtain ⟨ia, hia_lt, hia_eq⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨ib, hib_lt, hib_eq⟩ := List.mem_iff_getElem.mp hb
    have hget_bit : ∀ (k : ℕ) (i : ℕ) (hi : i < (x1 ++ ys).length),
        ((x1 ++ ys).map fun v => v.testBit k).getD i false = ((x1 ++ ys)[i]'hi).testBit k := by
      intro k i hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
      rfl
    rcases hab with hy_and | hy_or
    · let g : Gate := ⟨GateOp.and, [ia, ib]⟩
      refine ⟨gs ++ [g], by simp [hglen], ?_, ?_⟩
      · intro g' hg'
        simp only [List.mem_append, List.mem_singleton] at hg'
        rcases hg' with hg' | rfl
        · exact hgmono g' hg'
        · exact ⟨Or.inl rfl, by simp [g]⟩
      · intro k
        rw [List.foldl_append, hgwires k]
        simp only [List.foldl_cons, List.foldl_nil, g, GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, Bool.and_true, id_eq]
        rw [hget_bit k ia hia_lt, hget_bit k ib hib_lt, hia_eq, hib_eq, ← Nat.testBit_and, ← hy_and]
        simp [List.append_assoc]
    · let g : Gate := ⟨GateOp.or, [ia, ib]⟩
      refine ⟨gs ++ [g], by simp [hglen], ?_, ?_⟩
      · intro g' hg'
        simp only [List.mem_append, List.mem_singleton] at hg'
        rcases hg' with hg' | rfl
        · exact hgmono g' hg'
        · exact ⟨Or.inr rfl, by simp [g]⟩
      · intro k
        rw [List.foldl_append, hgwires k]
        simp only [List.foldl_cons, List.foldl_nil, g, GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, Bool.or_false, id_eq]
        rw [hget_bit k ia hia_lt, hget_bit k ib hib_lt, hia_eq, hib_eq, ← Nat.testBit_or, ← hy_or]
        simp [List.append_assoc]

private lemma main_proof (x1 x2 : List ℕ) (x3 : ℕ)
    (hstep : ∀ (x4 : Fin x2.length),
      ∃ x5 ∈ x1 ++ List.take (↑x4) x2, ∃ x6 ∈ x1 ++ List.take (↑x4) x2,
        x2.get x4 = x5 &&& x6 ∨ x2.get x4 = x5 ||| x6)
    (hx3 : x3 ∈ x2) :
    ∃ (x6 : Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x2.length ∧
      ∀ (x7 : ℕ), x6.eval (List.map (fun (x8 : ℕ) => x8.testBit x7) x1) = x3.testBit x7 := by
  obtain ⟨gs, hglen, hgmono, hgwires⟩ := build_gates x1 x2 hstep
  have hx3' : x3 ∈ x1 ++ x2 := List.mem_append_right x1 hx3
  obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.mem_iff_getElem.mp hx3'
  refine ⟨⟨gs, idx⟩, hgmono, ?_, ?_⟩
  · change gs.length ≤ x2.length
    omega
  · intro k
    change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (x1.map fun v => v.testBit k)).getD idx false = x3.testBit k
    rw [hgwires k, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hidx_lt]
    simp [hidx_eq]

end PEqualNP.Outside.L_meta_3006

theorem PEqualNP.Outside.L_meta_3006 : ∀ (x1 x2 : List ℕ) (x3 : ℕ), (∀ (x4 : Fin x2.length), ∃ x5 ∈ x1 ++ List.take (↑x4) x2, ∃ x6 ∈ x1 ++ List.take (↑x4) x2, x2.get x4 = x5 &&& x6 ∨ x2.get x4 = x5 ||| x6) → x3 ∈ x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x2.length ∧ ∀ (x7 : ℕ), x6.eval (List.map (fun (x8 : ℕ) => x8.testBit x7) x1) = x3.testBit x7 :=
  PEqualNP.Outside.L_meta_3006.main_proof
