import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8744_aux
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
    (hleg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
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
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem app_mono (A A' B B' : List Bool) (hl : A.length = A'.length)
    (hA : ∀ i, A.getD i false = true → A'.getD i false = true)
    (hB : ∀ i, B.getD i false = true → B'.getD i false = true) :
    ∀ i, (A ++ B).getD i false = true → (A' ++ B').getD i false = true := by
  intro i
  by_cases hi : i < A.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega)]; exact hA i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), ← hl]
    exact hB _

theorem inc_mono (n : ℕ) (C : Circuit) (hC : PEqualNP.EdgeOwnership.AndOrOnly C)
    (X X' Y Y' : Finset (Fin n)) (hX : X ⊆ X') (hY : Y ⊆ Y')
    (h : C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = true) :
    C.eval (PEqualNP.GenericRejection.incidenceInput X' Y') = true := by
  unfold Circuit.eval Circuit.wires at *
  refine mono2 C.gates hC _ _ (by simp [PEqualNP.GenericRejection.incidenceInput]) ?_ C.output h
  unfold PEqualNP.GenericRejection.incidenceInput
  apply app_mono _ _ _ _ (by simp)
  · apply ofFn_mono; intro v hv; simp at hv ⊢; exact hX hv
  · apply ofFn_mono; intro v hv; simp at hv ⊢; exact hY hv

theorem descent (n : ℕ) (C : Circuit) : ∀ k, ∀ X Y : Finset (Fin n), X.card + Y.card = k →
    C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = true →
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, C.eval (PEqualNP.GenericRejection.incidenceInput X' Y') = true ∧
      (∀ x ∈ X', C.eval (PEqualNP.GenericRejection.incidenceInput (X'.erase x) Y') = false) ∧
      (∀ y ∈ Y', C.eval (PEqualNP.GenericRejection.incidenceInput X' (Y'.erase y)) = false) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro X Y hk h
    by_cases h1 : ∃ x ∈ X, C.eval (PEqualNP.GenericRejection.incidenceInput (X.erase x) Y) = true
    · obtain ⟨x, hx, hx2⟩ := h1
      have hc := Finset.card_erase_lt_of_mem hx
      obtain ⟨X', hX', Y', hY', r⟩ := ih _ (by omega) _ _ rfl hx2
      exact ⟨X', hX'.trans (Finset.erase_subset _ _), Y', hY', r⟩
    by_cases h2 : ∃ y ∈ Y, C.eval (PEqualNP.GenericRejection.incidenceInput X (Y.erase y)) = true
    · obtain ⟨y, hy, hy2⟩ := h2
      have hc := Finset.card_erase_lt_of_mem hy
      obtain ⟨X', hX', Y', hY', r⟩ := ih _ (by omega) _ _ rfl hy2
      exact ⟨X', hX', Y', hY'.trans (Finset.erase_subset _ _), r⟩
    push_neg at h1 h2
    exact ⟨X, subset_rfl, Y, subset_rfl, h, fun x hx => by simpa using h1 x hx,
      fun y hy => by simpa using h2 y hy⟩

end PEqualNP.Outside.L_meta_8744_aux

open PEqualNP.Outside.L_meta_8744_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8744 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (x1 + x1) x2 →     (∀ (x4 x5 : Finset (Fin x1)), x2.eval (PEqualNP.GenericRejection.incidenceInput x4 x5) = Bool.true → (∀ x7 ∈ x4, x2.eval (PEqualNP.GenericRejection.incidenceInput (x4.erase x7) x5) = Bool.false) → (∀ x8 ∈ x5, x2.eval (PEqualNP.GenericRejection.incidenceInput x4 (x5.erase x8)) = Bool.false) → x4.card = (1 : ℕ) ∧ x5.card = (1 : ℕ)) →       have x5 : Fin x1 → Finset (Fin x1) := fun (x5 : Fin x1) => {x6 : Fin x1 | x2.eval (PEqualNP.GenericRejection.incidenceInput {x6} {x5}) = Bool.true};       PEqualNP.GenericRejection.ComputesIncidence x5 x2 := by
  intro n C hC hmin S X Y
  have hAO := hC.1
  unfold PEqualNP.GenericRejection.incidenceFun
  cases hv : C.eval (PEqualNP.GenericRejection.incidenceInput X Y)
  · symm; rw [decide_eq_false_iff_not]
    rintro ⟨p, hp, l, hl, hpl⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hpl
    have := inc_mono n C hAO {p} X {l} Y (by simpa using hp) (by simpa using hl) hpl
    rw [hv] at this; exact absurd this (by simp)
  · symm; rw [decide_eq_true_iff]
    obtain ⟨X', hX', Y', hY', ht, hx, hy⟩ := descent n C _ X Y rfl hv
    obtain ⟨c1, c2⟩ := hmin X' Y' ht hx hy
    obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp c1
    obtain ⟨l, rfl⟩ := Finset.card_eq_one.mp c2
    refine ⟨p, hX' (by simp), l, hY' (by simp), ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ht
