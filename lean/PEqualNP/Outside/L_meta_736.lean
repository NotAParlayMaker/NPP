import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_736_aux

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma main (psi : ℕ → ℕ) (a b G : ℕ) (hpsi : ∀ i t, t < G → (psi i = b + t ↔ i = a + t)) :
    ∀ (gs : List Gate) (W W' : List Bool) (t : ℕ), W.length = a + t → W'.length = b + t →
    t + gs.length = G → (∀ i, W'.getD (psi i) false = W.getD i false) →
    ∀ i, ((gs.map (fun g => ({ op := g.op, inputs := g.inputs.map psi } : Gate))).foldl step W').getD (psi i) false
      = (gs.foldl step W).getD i false := by
  intro gs
  induction gs with
  | nil => intro W W' t _ _ _ h i; exact h i
  | cons g gs ih =>
    intro W W' t hW hW' hG h
    simp only [List.map_cons, List.foldl_cons]
    apply ih _ _ (t + 1) (by simp [step]; omega) (by simp [step]; omega) (by simp at hG; omega)
    intro i
    have hv : g.op.eval ((g.inputs.map psi).map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro k _
      exact h k
    have hk := hpsi i t (by simp at hG; omega)
    simp only [step]
    rw [getD_snoc, getD_snoc, hW, hW', hv]
    by_cases hi : i = a + t
    · rw [if_pos (hk.2 hi), if_pos hi]
    · rw [if_neg (fun h' => hi (hk.1 h')), if_neg hi, h i]

end PEqualNP.Outside.L_meta_736_aux

open PEqualNP.Outside.L_meta_736_aux in
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
  intro n n' O e _ hO _ gates
  refine ⟨fun i => if h : i < n then (if hk : (⟨i, h⟩ : Fin n) ∉ O then
      (((hO ⟨i, h⟩).1 hk).choose : ℕ) else n') else
      if i < n + gates.length then n' + 1 + (i - n) else n' + 1 + gates.length, ?_⟩
  intro x x' hx hx' hxO hxe
  have hw : ∀ i : ℕ, (Circuit.wires
        { gates := { op := GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map (fun i => if h : i < n then (if hk : (⟨i, h⟩ : Fin n) ∉ O then
      (((hO ⟨i, h⟩).1 hk).choose : ℕ) else n') else
      if i < n + gates.length then n' + 1 + (i - n) else n' + 1 + gates.length) }), output := 0 } x').getD
        ((fun i => if h : i < n then (if hk : (⟨i, h⟩ : Fin n) ∉ O then
      (((hO ⟨i, h⟩).1 hk).choose : ℕ) else n') else
      if i < n + gates.length then n' + 1 + (i - n) else n' + 1 + gates.length) i) false
      = (Circuit.wires { gates := gates, output := 0 } x).getD i false := by
    intro i
    show ((gates.map _).foldl step (step x' { op := GateOp.and, inputs := [] })).getD _ false
      = (gates.foldl step x).getD i false
    apply main _ n (n' + 1) gates.length _ gates x _ 0 (by omega) (by simp [step, hx']) (by omega)
    · intro k
      have hs : step x' { op := GateOp.and, inputs := [] } = x' ++ [true] := by
        simp [step, GateOp.eval]
      rw [hs, getD_snoc, hx']
      by_cases hkn : k < n
      · simp only [dif_pos hkn]
        by_cases hkO : (⟨k, hkn⟩ : Fin n) ∉ O
        · rw [dif_pos hkO]
          have hc := ((hO ⟨k, hkn⟩).1 hkO).choose_spec
          have hlt := (((hO ⟨k, hkn⟩).1 hkO).choose).isLt
          rw [if_neg (by omega), hxe _ |>.symm, hc]
        · rw [dif_neg hkO, if_pos rfl]
          have := hxO _ (not_not.mp hkO)
          exact this.symm
      · simp only [dif_neg hkn]
        rw [List.getD_eq_default x _ (by omega)]
        split_ifs <;> first | rfl | omega | (rw [List.getD_eq_default _ _ (by omega)])
    · intro k t ht
      by_cases hkn : k < n
      · simp only [dif_pos hkn]
        split_ifs with hm
        · first | omega | (have hlt := (((hO ⟨k, hkn⟩).1 hm).choose).isLt; omega)
        · first | omega | (have hlt := (((hO ⟨k, hkn⟩).1 hm).choose).isLt; omega)
      · simp only [dif_neg hkn]
        split_ifs <;> omega
  refine ⟨hw, ?_⟩
  intro o
  exact hw o
