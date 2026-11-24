import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3012

open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem op_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem wf_mono (gs : List Gate) (hleg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := hleg g (by simp)
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact op_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : x ≤ y)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · have e1 : (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
      simp [List.getD_eq_getElem?_getD, hw]
    have e2 : (List.ofFn y).getD w false = y ⟨w, hw⟩ := by
      simp [List.getD_eq_getElem?_getD, hw]
    rw [e1, e2]
    have hle := hxy ⟨w, hw⟩
    revert hle
    cases x ⟨w, hw⟩ <;> cases y ⟨w, hw⟩ <;> simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem circ_mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : Fin n → Bool) (hab : a ≤ b) :
    C.eval (List.ofFn a) = true → C.eval (List.ofFn b) = true :=
  wf_mono C.gates hC (List.ofFn a) (List.ofFn b) (by simp) (ofFn_mono n a b hab) C.output

end PEqualNP.Outside.L_meta_3012

theorem PEqualNP.Outside.L_meta_3012 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : (Fin x1 → Bool) → Bool), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ (x5 : Fin x1 → Bool), x3 x5 = Bool.true → (∀ x7 ≤ x5, x3 x7 = Bool.true → x7 = x5) → x2.eval (List.ofFn x5) = Bool.true) → (∀ (x6 : Fin x1 → Bool), x3 x6 = Bool.false → (∀ (x8 : Fin x1 → Bool), x6 ≤ x8 → x3 x8 = Bool.false → x8 = x6) → x2.eval (List.ofFn x6) = Bool.false) → ∀ (x7 : Fin x1 → Bool), x2.eval (List.ofFn x7) = x3 x7 := by
  intro n C f hC hmin hmax x
  have hAO : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := hC.1
  cases hfx : f x with
  | true =>
    obtain ⟨m, hmx, hm⟩ := Finset.exists_le_minimal (Finset.univ.filter fun y => f y = true)
      (Finset.mem_filter.2 ⟨Finset.mem_univ x, hfx⟩)
    have hmf : f m = true := (Finset.mem_filter.1 hm.1).2
    have hCm := hmin m hmf (fun y hy hfy =>
      le_antisymm hy (hm.2 (Finset.mem_filter.2 ⟨Finset.mem_univ y, hfy⟩) hy))
    exact PEqualNP.Outside.L_meta_3012.circ_mono C hAO m x hmx hCm
  | false =>
    obtain ⟨M, hxM, hM⟩ := Finset.exists_le_maximal (Finset.univ.filter fun y => f y = false)
      (Finset.mem_filter.2 ⟨Finset.mem_univ x, hfx⟩)
    have hMf : f M = false := (Finset.mem_filter.1 hM.1).2
    have hCM := hmax M hMf (fun y hy hfy =>
      le_antisymm (hM.2 (Finset.mem_filter.2 ⟨Finset.mem_univ y, hfy⟩) hy) hy)
    cases hCx : C.eval (List.ofFn x) with
    | false => rfl
    | true =>
      have := PEqualNP.Outside.L_meta_3012.circ_mono C hAO x M hxM hCx
      rw [hCM] at this
      exact absurd this (by simp)
