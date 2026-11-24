import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_4651

private def wireLE (a b : Bool) : Prop := a = true → b = true

private def gateValue (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def gateLE (g h : Gate) : Prop :=
  ∀ u v : List Bool, List.Forall₂ wireLE u v → wireLE (gateValue g u) (gateValue h v)

private theorem readLE {u v : List Bool} (huv : List.Forall₂ wireLE u v) (j : ℕ) :
    wireLE (u.getD j false) (v.getD j false) := by
  by_cases hj : j < u.length
  · have hk : j < v.length := huv.length_eq ▸ hj
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hk]
    exact huv.get hj hk
  · have hk : v.length ≤ j := by have := huv.length_eq; omega
    rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hj), List.getD_eq_default _ _ hk]
    exact fun h => h

private theorem sameGate (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    gateLE g g := by
  intro u v h hv
  rcases hg with ha | ho
  · have hs : ∀ i ∈ g.inputs, u.getD i false = true := by
      simpa [gateValue, ha, GateOp.eval, List.all_map, Function.comp_def] using hv
    simpa [gateValue, ha, GateOp.eval, List.all_map, Function.comp_def] using
      (show ∀ i ∈ g.inputs, v.getD i false = true from fun i hi => readLE h i (hs i hi))
  · have hs : ∃ i ∈ g.inputs, u.getD i false = true := by
      simpa [gateValue, ho, GateOp.eval, List.any_map, Function.comp_def] using hv
    obtain ⟨i,hi,hu⟩ := hs
    simpa [gateValue, ho, GateOp.eval, List.any_map, Function.comp_def] using
      (show ∃ j ∈ g.inputs, v.getD j false = true from ⟨i,hi,readLE h i hu⟩)

private theorem bypassGate (g : Gate) (k : ℕ) (hg : g.op = GateOp.or) (hk : k ∈ g.inputs) :
    gateLE ⟨GateOp.and,[k]⟩ g := by
  intro u v h hv
  have hu : u.getD k false = true := by simpa [gateValue, GateOp.eval] using hv
  simpa [gateValue, hg, GateOp.eval, List.any_map, Function.comp_def] using
    (show ∃ j ∈ g.inputs, v.getD j false = true from ⟨k,hk,readLE h k hu⟩)

private theorem foldLE {as bs : List Gate} (hg : List.Forall₂ gateLE as bs)
    {u v : List Bool} (hw : List.Forall₂ wireLE u v) :
    List.Forall₂ wireLE (as.foldl (fun w g => w ++ [gateValue g w]) u)
      (bs.foldl (fun w g => w ++ [gateValue g w]) v) := by
  induction hg generalizing u v with
  | nil => exact hw
  | cons h _ ih => exact ih (List.rel_append hw (.cons (h u v hw) .nil))

private theorem monoOp {C : Circuit} (h : PEqualNP.MetaComplexity.Monotone2 C)
    (g : Gate) (hg : g ∈ C.gates) : g.op = GateOp.and ∨ g.op = GateOp.or :=
  (h g hg).1

private theorem countAs (gs : List Gate) {n : ℕ} (hl : gs.length = n) :
    {i : Fin gs.length | (gs.get i).op = GateOp.or}.ncard =
    {i : Fin n | (gs[i.val]'(hl.symm ▸ i.isLt)).op = GateOp.or}.ncard := by
  subst n
  rfl

private theorem countFalls (gs : List Gate) (i : Fin gs.length) (k : ℕ)
    (ho : (gs.get i).op = GateOp.or) :
    {j : Fin (gs.set i.val ⟨GateOp.and,[k]⟩).length |
      ((gs.set i.val ⟨GateOp.and,[k]⟩).get j).op = GateOp.or}.ncard <
    {j : Fin gs.length | (gs.get j).op = GateOp.or}.ncard := by
  rw [countAs _ (List.length_set ..)]
  refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
  constructor
  · intro j hj
    change ((gs.set i.val ⟨GateOp.and,[k]⟩)[j.val]'_).op = GateOp.or at hj
    rw [List.getElem_set] at hj
    by_cases he : i.val = j.val
    · simp [he] at hj
    · simpa [he] using hj
  · intro h
    have hf := h (show i ∈ {j : Fin gs.length | (gs.get j).op = GateOp.or} from ho)
    change ((gs.set i.val ⟨GateOp.and,[k]⟩)[i.val]'_).op = GateOp.or at hf
    simp at hf

end PEqualNP.Outside.L_meta_4651

open PEqualNP.Outside.L_meta_4651

theorem PEqualNP.Outside.L_meta_4651 :
    have x1 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => {x2 : Fin x1.gates.length | (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard; have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) => { gates := x2.gates.set x3 { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4] : PEqualNP.CircuitLowerBounds.Gate }, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit }; ∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin x4.gates.length) (x6 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x4 →     (x4.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or →       x6 ∈ (x4.gates.get x5).inputs →         have x10 : PEqualNP.CircuitLowerBounds.Circuit := x2 x4 (↑x5) x6;         PEqualNP.MetaComplexity.Monotone2 x10 ∧ x1 x10 < x1 x4 ∧ (∀ (x11 : Fin x3 → Bool), x10.eval (List.ofFn x11) = Bool.true → x4.eval (List.ofFn x11) = Bool.true) ∧ ∀ (x11 x12 : Fin x3 → Bool), (∀ (x13 : Fin x3), x11 x13 = Bool.true → x12 x13 = Bool.true) → x10.eval (List.ofFn x11) = Bool.true → x10.eval (List.ofFn x12) = Bool.true := by
  dsimp only
  intro n C j k hm ho hk
  let copy : Gate := ⟨GateOp.and,[k]⟩
  let D : Circuit := ⟨C.gates.set j.val copy, C.output⟩
  have hD : PEqualNP.MetaComplexity.Monotone2 D := by
    intro g hg
    change g ∈ C.gates.set j.val copy at hg
    obtain ⟨i,hi,hg'⟩ := List.getElem_of_mem hg
    rw [List.getElem_set] at hg'
    by_cases he : j.val = i
    · simp [he] at hg'
      subst g
      simp [copy]
    · simp [he] at hg'
      exact hm _ (hg' ▸ List.getElem_mem _)
  refine ⟨hD, countFalls C.gates j k ho, ?_, ?_⟩
  · intro x
    have rel : List.Forall₂ gateLE D.gates C.gates := by
      apply List.forall₂_iff_get.mpr
      refine ⟨List.length_set .., ?_⟩
      intro i hi ht
      change gateLE ((C.gates.set j.val copy)[i]'hi) (C.gates[i]'ht)
      rw [List.getElem_set]
      by_cases he : j.val = i
      · subst i
        rw [if_pos rfl]
        exact bypassGate _ k ho hk
      · rw [if_neg he]
        exact sameGate _ (monoOp hm _ (List.getElem_mem ht))
    have hx : List.Forall₂ wireLE (List.ofFn x) (List.ofFn x) :=
      List.forall₂_iff_get.mpr ⟨rfl,fun _ _ _ h => h⟩
    exact readLE (foldLE rel hx) C.output
  · intro x y hxy
    have rel : List.Forall₂ gateLE D.gates D.gates :=
      List.forall₂_iff_get.mpr ⟨rfl, fun i hi _ => sameGate _ (monoOp hD _ (List.getElem_mem hi))⟩
    have hx : List.Forall₂ wireLE (List.ofFn x) (List.ofFn y) := by
      apply List.forall₂_iff_get.mpr
      refine ⟨by simp, ?_⟩
      intro i hi hj
      simpa [wireLE, List.get_eq_getElem, List.getElem_ofFn] using hxy ⟨i, by simpa using hi⟩
    exact readLE (foldLE rel hx) D.output
