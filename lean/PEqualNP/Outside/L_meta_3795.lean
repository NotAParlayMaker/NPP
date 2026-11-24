import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3795

open PEqualNP.CircuitLowerBounds

/-- Degrees of the 14 input wires: the marked wire `x2` has degree 1, the rest 0. -/
def initDeg (x2 : ℕ) : List ℕ :=
  (List.range 14).map fun i => if i ∈ ({x2} : Finset ℕ) then 1 else 0

/-- Degrees of all wires after processing the gates in `L`. -/
def degList (x2 : ℕ) (L : List Gate) : List ℕ :=
  L.foldl (fun d g => d ++ [g.lineDegree d]) (initDeg x2)

/-- Wires read by the gates in `L`. -/
def readWires (L : List Gate) : List ℕ := List.flatMap Gate.inputs L

/-- A gate of fan-in two has degree at most the sum of its two input degrees
(both for AND, where it is the sum, and for OR, where it is the max). -/
theorem gateDeg_le (g : Gate) (d : List ℕ) (a b : ℕ) (h : g.inputs = [a, b]) :
    g.lineDegree d ≤ d.getD a 0 + d.getD b 0 := by
  unfold Gate.lineDegree
  rw [h]
  split_ifs
  · simp
  · simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    omega

/-- Reading a degree out of a list extended by one entry. -/
theorem getD_append_single (D : List ℕ) (x w : ℕ) :
    (D ++ [x]).getD w 0 = if w < D.length then D.getD w 0 else if w = D.length then x else 0 := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    simp
  · apply List.getD_eq_default
    simp
    omega

/-- Pointwise bound on a sum, with two entries moved out and one added. -/
theorem sum_step (N a b k : ℕ) (f f' : ℕ → ℕ) (fa fb c : ℕ) (ha : a < N) (hb : b < N)
    (hk : k < N)
    (h : ∀ w, f' w + (if w = a then fa else 0) + (if w = b then fb else 0)
      ≤ f w + (if w = k then c else 0)) :
    ∑ w ∈ Finset.range N, f' w + fa + fb ≤ ∑ w ∈ Finset.range N, f w + c := by
  have hs := Finset.sum_le_sum (s := Finset.range N) (fun w _ => h w)
  simpa [Finset.sum_add_distrib, ha, hb, hk] using hs

/-- The sum invariant: the degrees of the gate wires not yet read are bounded by
the number of times the marked wire `x2` is read. Each fresh gate can add at most
the degrees of its two inputs, and those inputs stop being unread once read, so the
total only grows when `x2` itself is read. -/
theorem inv (x2 N : ℕ) (_hx : x2 < 14) : ∀ L : List Gate, 14 + L.length ≤ N →
    (∀ (i : ℕ) (g : Gate), L[i]? = some g →
      ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + i ∧ b < 14 + i) →
    ((readWires L).filter (fun w => decide (14 ≤ w))).Nodup →
    (degList x2 L).length = 14 + L.length ∧
    (∀ w < 14, (degList x2 L).getD w 0 = if w = x2 then 1 else 0) ∧
    ∑ w ∈ Finset.range N, (if 14 ≤ w ∧ w ∉ readWires L then (degList x2 L).getD w 0 else 0)
      ≤ List.count x2 (readWires L) := by
  intro L
  induction L using List.reverseRecOn with
  | nil =>
    intro _ _ _
    refine ⟨by simp [degList, initDeg], ?_, ?_⟩
    · intro w hw
      simp [degList, initDeg, List.getD_eq_getElem?_getD, hw]
    · have hz : ∀ w, 14 ≤ w → (initDeg x2).getD w 0 = 0 := fun w hw =>
        List.getD_eq_default _ _ (by simpa [initDeg] using hw)
      have hzero : ∑ w ∈ Finset.range N,
          (if 14 ≤ w ∧ w ∉ readWires [] then (degList x2 []).getD w 0 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro w _
        split_ifs with h
        · exact hz w h.1
        · rfl
      rw [hzero]
      exact Nat.zero_le _
  | append_singleton L g ih =>
    intro hN hg hnd
    have hU : readWires (L ++ [g]) = readWires L ++ g.inputs := by simp [readWires]
    have hD : degList x2 (L ++ [g]) = degList x2 L ++ [g.lineDegree (degList x2 L)] := by
      simp [degList]
    obtain ⟨a, b, hab, hne, ha, hb⟩ := hg L.length g (by simp)
    rw [hU, hab, List.filter_append] at hnd
    have hnd1 := (List.nodup_append.mp hnd).1
    have hdis := (List.nodup_append.mp hnd).2.2
    have hLen : (L ++ [g]).length = L.length + 1 := by simp
    rw [hLen] at hN
    obtain ⟨hlen, hlow, hsum⟩ := ih (by omega)
      (fun i g' h => hg i g' (by
        have hi : i < L.length := by
          by_contra hc
          rw [List.getElem?_eq_none (by omega)] at h
          cases h
        rw [List.getElem?_append_left hi]
        exact h)) hnd1
    have haU : 14 ≤ a → a ∉ readWires L := by
      intro h14 hm
      exact hdis a (by simp [List.mem_filter, hm, h14]) a (by simp [List.mem_filter, h14]) rfl
    have hbU : 14 ≤ b → b ∉ readWires L := by
      intro h14 hm
      exact hdis b (by simp [List.mem_filter, hm, h14]) b (by simp [List.mem_filter, h14]) rfl
    have hgl := gateDeg_le g (degList x2 L) a b hab
    have hz : (degList x2 L).getD (14 + L.length) 0 = 0 :=
      List.getD_eq_default _ _ (by omega)
    refine ⟨by simp [hD, hlen]; omega, ?_, ?_⟩
    · intro w hw
      rw [hD, getD_append_single, ite_eq_left (by omega)]
      exact hlow w hw
    · rw [hU, hab, hD]
      have hc : List.count x2 (readWires L ++ [a, b])
          = List.count x2 (readWires L) + ((if a = x2 then 1 else 0) + (if b = x2 then 1 else 0)) := by
        simp [List.count_cons]
        omega
      have hfa : (degList x2 L).getD a 0 ≤
          (if 14 ≤ a ∧ a ∉ readWires L then (degList x2 L).getD a 0 else 0) + (if a = x2 then 1 else 0) := by
        by_cases h14 : 14 ≤ a
        · rw [ite_eq_left ⟨h14, haU h14⟩]
          omega
        · rw [hlow a (by omega)]
          omega
      have hfb : (degList x2 L).getD b 0 ≤
          (if 14 ≤ b ∧ b ∉ readWires L then (degList x2 L).getD b 0 else 0) + (if b = x2 then 1 else 0) := by
        by_cases h14 : 14 ≤ b
        · rw [ite_eq_left ⟨h14, hbU h14⟩]
          omega
        · rw [hlow b (by omega)]
          omega
      have hst := sum_step N a b (14 + L.length)
        (fun w => if 14 ≤ w ∧ w ∉ readWires L then (degList x2 L).getD w 0 else 0)
        (fun w => if 14 ≤ w ∧ w ∉ readWires L ++ [a, b] then
          (degList x2 L ++ [g.lineDegree (degList x2 L)]).getD w 0 else 0)
        (if 14 ≤ a ∧ a ∉ readWires L then (degList x2 L).getD a 0 else 0)
        (if 14 ≤ b ∧ b ∉ readWires L then (degList x2 L).getD b 0 else 0)
        ((degList x2 L).getD a 0 + (degList x2 L).getD b 0)
        (by omega) (by omega) (by omega) (by
          intro w
          simp only [getD_append_single, hlen, List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false, not_or]
          by_cases hwa : w = a
          · subst hwa
            simp [hne]
          · by_cases hwb : w = b
            · subst hwb
              simp [hwa]
            · by_cases hwk : w = 14 + L.length
              · subst hwk
                have h1 : ¬ (14 + L.length < 14 + L.length) := by omega
                simp only [hz, h1, ite_false, ite_true, hwa, hwb]
                split_ifs <;> omega
              · simp only [hwa, hwb, hwk, ite_false]
                split_ifs <;> first | omega | tauto)
      omega

end PEqualNP.Outside.L_meta_3795

theorem PEqualNP.Outside.L_meta_3795 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x2 < (14 : ℕ), (∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 → (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x7 : ℕ) (x8 : ℕ), x5.inputs = [x7, x8] ∧ x7 ≠ x8 ∧ x7 < (14 : ℕ) + x4 ∧ x8 < (14 : ℕ) + x4) → (List.filter (fun (x5 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x5)) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates)).Nodup → List.count x2 (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates) ≤ (1 : ℕ) → PEqualNP.CircuitLowerBounds.HasLineDegree (14 : ℕ) {x2} x1 (1 : ℕ) := by
  intro C x2 hx hg hnd hc
  have hnd' : ((PEqualNP.Outside.L_meta_3795.readWires C.gates).filter
      (fun w => decide (14 ≤ w))).Nodup := by
    rw [List.filter_cons] at hnd
    split_ifs at hnd
    · exact (List.nodup_cons.mp hnd).2
    · exact hnd
  have h := PEqualNP.Outside.L_meta_3795.inv x2 (14 + C.gates.length) hx C.gates le_rfl
    (fun i g h => (hg i g h).2) hnd'
  change (PEqualNP.Outside.L_meta_3795.degList x2 C.gates).getD C.output 0 ≤ 1
  by_cases ho : C.output < 14
  · rw [h.2.1 _ ho]
    split_ifs <;> omega
  · by_cases hN : C.output < 14 + C.gates.length
    · have hnot : C.output ∉ PEqualNP.Outside.L_meta_3795.readWires C.gates := by
        intro hm
        rw [List.filter_cons_of_pos (by simpa using ho)] at hnd
        exact (List.nodup_cons.mp hnd).1 (List.mem_filter.mpr ⟨hm, by simpa using ho⟩)
      have hs := Finset.single_le_sum
        (f := fun w => if 14 ≤ w ∧ w ∉ PEqualNP.Outside.L_meta_3795.readWires C.gates then
          (PEqualNP.Outside.L_meta_3795.degList x2 C.gates).getD w 0 else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hN)
      rw [ite_eq_left ⟨by omega, hnot⟩] at hs
      have h3 := h.2.2
      unfold PEqualNP.Outside.L_meta_3795.readWires at h3 hs
      omega
    · rw [List.getD_eq_default _ _ (by rw [h.1]; omega)]
      omega
