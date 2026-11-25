import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8849
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

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
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
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem cmono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (n : ℕ)
    (x y : Fin n → Bool) (hxy : x ≤ y) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  intro h
  have h' : (wf C.gates (List.ofFn x)).getD C.output false = true := h
  exact mono2 C.gates (fun g hg => ⟨by
      rcases (hC g hg).1 with h | h
      · exact Or.inl h
      · exact Or.inr h, (hC g hg).2⟩) (List.ofFn x) (List.ofFn y) (by simp)
    (fun i => ofFn_mono n x y (fun v hv => by
      have := hxy v
      rw [Bool.le_iff_imp] at this
      exact this hv) i) C.output h'

theorem inc_eq (n : ℕ) (X Y : Finset (Fin n)) :
    PEqualNP.GenericRejection.incidenceInput X Y
      = List.ofFn (Fin.append (fun p : Fin n => decide (p ∈ X)) (fun l : Fin n => decide (l ∈ Y))) := by
  unfold PEqualNP.GenericRejection.incidenceInput
  rw [List.ofFn_fin_append]

theorem inc_mono (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (X X' Y Y' : Finset (Fin n)) (hX : X ⊆ X') (hY : Y ⊆ Y')
    (h : C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = true) :
    C.eval (PEqualNP.GenericRejection.incidenceInput X' Y') = true := by
  rw [inc_eq] at h ⊢
  refine cmono C hC (n + n) _ _ ?_ h
  intro w hw
  induction w using Fin.addCases with
  | left p =>
    rw [Fin.append_left] at hw ⊢
    simpa using hX (by simpa using hw)
  | right l =>
    rw [Fin.append_right] at hw ⊢
    simpa using hY (by simpa using hw)

end PEqualNP.Outside.L_meta_8849

open PEqualNP.Outside.L_meta_8849 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8849 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x1) x2 → ∀ (x4 x5 x6 x7 : Finset (Fin x1)), x4 ⊆ x6 → x5 ⊆ x7 → x2.eval (PEqualNP.GenericRejection.incidenceInput x4 x5) = Bool.true → x2.eval (PEqualNP.GenericRejection.incidenceInput x6 x7) = Bool.true := by
  intro n C hAO X Y X' Y' hX hY h
  have hm : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    refine ⟨?_, le_of_eq (hAO.2.2 g hg)⟩
    have := hAO.1 g hg
    simpa using this
  exact inc_mono n C hm X X' Y Y' hX hY h
