import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_736

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

lemma pi_exists (n n' : ℕ) (O : Finset (Fin n)) (e : Fin n' → Fin n)
    (hO : ∀ k : Fin n, k ∉ O ↔ ∃ j : Fin n', e j = k) :
    ∃ π : Fin n → Fin (n' + 1), ∀ k : Fin n,
      (k ∈ O ∧ π k = Fin.last n') ∨ (∃ j : Fin n', e j = k ∧ π k = j.castSucc) := by
  classical
  refine ⟨fun k => if h : ∃ j : Fin n', e j = k then (Classical.choose h).castSucc
    else Fin.last n', ?_⟩
  intro k
  by_cases h : ∃ j : Fin n', e j = k
  · right
    exact ⟨Classical.choose h, Classical.choose_spec h, by simp [h]⟩
  · left
    refine ⟨?_, by simp [h]⟩
    by_contra hn
    exact h ((hO k).1 hn)

lemma main : ∀ (n n' : ℕ) (O : Finset (Fin n)) (e : Fin n' → Fin n), StrictMono e →
  (∀ k : Fin n, k ∉ O ↔ ∃ j : Fin n', e j = k) → n' + O.card = n →
  ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
  ∃ psi : ℕ → ℕ, ∀ x x' : List Bool, x.length = n → x'.length = n' →
    (∀ k ∈ O, x.getD (k : ℕ) false = true) →
    (∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) →
    (∀ i : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := 0 } x').getD (psi i) false
      = (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := gates, output := 0 } x).getD i false) ∧
    (∀ o : ℕ, PEqualNP.CircuitLowerBounds.Circuit.eval
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := psi o } x'
      = PEqualNP.CircuitLowerBounds.Circuit.eval { gates := gates, output := o } x) := by
  intro n n' O e _ hO _ gates
  obtain ⟨π, hπ⟩ := pi_exists n n' O e hO
  refine ⟨wmap n (n' + 1) π, ?_⟩
  intro x x' hx hx' hOt hej
  have hinit : Rel n (n' + 1) π x (x' ++ [true]) := by
    refine ⟨by omega, by simp; omega, ?_⟩
    intro w
    unfold wmap
    split
    · rename_i hw
      rcases hπ ⟨w, hw⟩ with ⟨hk, hl⟩ | ⟨j, hj, hl⟩
      · rw [hl, Fin.val_last, ← hx', getD_snoc_eq]
        exact (hOt _ hk).symm
      · rw [hl, Fin.coe_castSucc, List.getD_append _ _ _ _ (by rw [hx']; exact j.isLt)]
        rw [← hej j, hj]
    · rename_i hw
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have hfold := rel_fold n (n' + 1) π gates x (x' ++ [true]) hinit
  have hw1 : ∀ i : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map (wmap n (n' + 1) π) }),
          output := 0 } x').getD (wmap n (n' + 1) π i) false
      = (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := gates, output := 0 } x).getD i false := by
    intro i
    exact hfold.2.2 i
  refine ⟨hw1, ?_⟩
  intro o
  exact hw1 o

end PEqualNP.Outside.L_meta_736

theorem PEqualNP.Outside.L_meta_736 : ∀ (n n' : ℕ) (O : Finset (Fin n)) (e : Fin n' → Fin n), StrictMono e →
  (∀ k : Fin n, k ∉ O ↔ ∃ j : Fin n', e j = k) → n' + O.card = n →
  ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
  ∃ psi : ℕ → ℕ, ∀ x x' : List Bool, x.length = n → x'.length = n' →
    (∀ k ∈ O, x.getD (k : ℕ) false = true) →
    (∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) →
    (∀ i : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := 0 } x').getD (psi i) false
      = (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := gates, output := 0 } x).getD i false) ∧
    (∀ o : ℕ, PEqualNP.CircuitLowerBounds.Circuit.eval
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := psi o } x'
      = PEqualNP.CircuitLowerBounds.Circuit.eval { gates := gates, output := o } x) := by
  exact PEqualNP.Outside.L_meta_736.main
