import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5028

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl F w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [F]
    omega

theorem pre_fold (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl F w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih (F w g) (by simp [F]; omega)]
    simp only [F]
    rw [List.getD_append _ _ _ _ hi]

theorem gate_val (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (hin : ∀ i ∈ (gs[j]'hj).inputs, i < w.length + j) :
    (gs.foldl F w).getD (w.length + j) false =
      (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i => (gs.foldl F w).getD i false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero] at hin ⊢
      rw [pre_fold gs (F w g) _ (by simp [F])]
      simp only [F, Nat.add_zero]
      rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
      simp only [List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i hi
      have h1 := hin i hi
      rw [pre_fold gs _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
    | succ k =>
      simp only [List.getElem_cons_succ] at hin ⊢
      have hl : (F w g).length = w.length + 1 := by simp [F]
      have := ih (F w g) k (by simp at hj; omega) (by intro i hi; have := hin i hi; omega)
      rw [hl] at this
      rw [show w.length + (k + 1) = w.length + 1 + k by omega]
      exact this

def isOr (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

def lv (C : Circuit) (n : ℕ) : ℕ → ℕ → Finset ℕ
  | 0, w => {w}
  | d + 1, w =>
    if n ≤ w ∧ w < n + C.gates.length ∧ isOr (gateAt C (w - n)) = true then
      (gateAt C (w - n)).inputs.toFinset.biUnion (lv C n d)
    else {w}

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem isOr_iff (g : Gate) : isOr g = true ↔ g.op = GateOp.or := by
  unfold isOr
  split <;> simp_all

theorem wv_gate (n : ℕ) (C : Circuit) (hr : ReadsBack n C) (xs : List Bool) (hx : xs.length = n)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires xs).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires xs).getD i false) := by
  have h := gate_val C.gates xs j hj (by
    intro i hi
    have := hr j hj i (by rw [gateAt_eq C j hj]; exact hi)
    omega)
  rw [gateAt_eq C j hj]
  rw [hx] at h
  exact h

theorem lv_val (n : ℕ) (C : Circuit) (hr : ReadsBack n C) (xs : List Bool) (hx : xs.length = n) :
    ∀ d w, (C.wires xs).getD w false = true ↔ ∃ x ∈ lv C n d w, (C.wires xs).getD x false = true := by
  intro d
  induction d with
  | zero => intro w; simp [lv]
  | succ d ih =>
    intro w
    simp only [lv]
    split
    · rename_i h
      obtain ⟨h1, h2, h3⟩ := h
      rw [isOr_iff] at h3
      have hw : w = n + (w - n) := by omega
      rw [hw, wv_gate n C hr xs hx (w - n) (by omega), h3]
      rw [← hw]
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
      constructor
      · rintro ⟨i, hi, hv⟩
        obtain ⟨x, hx1, hx2⟩ := (ih i).1 hv
        exact ⟨x, Finset.mem_biUnion.2 ⟨i, List.mem_toFinset.2 hi, hx1⟩, hx2⟩
      · rintro ⟨x, hxm, hv⟩
        obtain ⟨i, hi, hx1⟩ := Finset.mem_biUnion.1 hxm
        exact ⟨i, List.mem_toFinset.1 hi, (ih i).2 ⟨x, hx1, hv⟩⟩
    · simp

theorem lv_leaf (n : ℕ) (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C) (hr : ReadsBack n C) :
    ∀ d w, w < d → w < n + C.gates.length → ∀ x ∈ lv C n d w,
      x ≤ w ∧ (x < n ∨ (gateAt C (x - n)).op = GateOp.and) := by
  intro d
  induction d with
  | zero => intro w hw; omega
  | succ d ih =>
    intro w hwd hwl x hx
    simp only [lv] at hx
    split at hx
    · rename_i h
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨i, hi, hx1⟩ := Finset.mem_biUnion.1 hx
      have hi' := hr (w - n) (by omega) i (List.mem_toFinset.1 hi)
      have := ih i (by omega) (by omega) x hx1
      exact ⟨by omega, this.2⟩
    · rename_i h
      simp only [Finset.mem_singleton] at hx
      subst hx
      refine ⟨le_refl _, ?_⟩
      by_cases hn : x < n
      · exact Or.inl hn
      · right
        have hj : x - n < C.gates.length := by omega
        have hmem : gateAt C (x - n) ∈ C.gates := by rw [gateAt_eq C _ hj]; exact List.getElem_mem hj
        have hop := (hm _ hmem).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · exact hop
        · exfalso; apply h; refine ⟨by omega, by omega, ?_⟩; rw [isOr_iff]; exact hop

end PEqualNP.Outside.L_meta_5028

theorem PEqualNP.Outside.L_meta_5028 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x1 ≤ x2.output → x2.output < x1 + x2.size → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x2.output - x1)).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∃ (x8 : Finset ℕ), (∀ x9 ∈ x8, x9 < x2.output ∧ (x9 < x1 ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x9 - x1)).op = PEqualNP.CircuitLowerBounds.GateOp.and)) ∧ ∀ (x9 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x9 = Bool.true ↔ ∃ x10 ∈ x8, PEqualNP.CircuitLowerBounds.wireValue x2 (List.ofFn x9) x10 = Bool.true := by
  intro n C hm hr hlo hhi hor
  refine ⟨PEqualNP.Outside.L_meta_5028.lv C n (C.output + 1) C.output, ?_, ?_⟩
  · intro x hx
    simp only [PEqualNP.Outside.L_meta_5028.lv] at hx
    rw [if_pos (c := _) ⟨hlo, by unfold PEqualNP.CircuitLowerBounds.Circuit.size at hhi; omega, by rw [PEqualNP.Outside.L_meta_5028.isOr_iff]; exact hor⟩] at hx
    obtain ⟨i, hi, hx1⟩ := Finset.mem_biUnion.1 hx
    have hi' := hr (C.output - n) (by unfold PEqualNP.CircuitLowerBounds.Circuit.size at hhi; omega) i (List.mem_toFinset.1 hi)
    have := PEqualNP.Outside.L_meta_5028.lv_leaf n C hm hr C.output i (by omega) (by unfold PEqualNP.CircuitLowerBounds.Circuit.size at hhi; omega) x hx1
    exact ⟨by omega, this.2⟩
  · intro x
    exact PEqualNP.Outside.L_meta_5028.lv_val n C hr (List.ofFn x) (by simp) (C.output + 1) C.output
