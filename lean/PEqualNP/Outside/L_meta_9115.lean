import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9115

open PEqualNP.CircuitLowerBounds

def stepGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_stepGate_len (gs : List Gate) (init : List Bool) :
    (gs.foldl stepGate init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g tl ih => simp [List.foldl, stepGate, ih]; omega

def cl (n a : ℕ) : Fin (n + 1) := ⟨min a n, by omega⟩

def desc (n : ℕ) : Gate → Fin (n + 1) ⊕ Bool × Fin (n + 1) × Fin (n + 1)
  | ⟨GateOp.not, l⟩ => Sum.inl (cl n (l.headD n))
  | ⟨GateOp.and, []⟩ => Sum.inl (cl n n)
  | ⟨GateOp.and, a :: l⟩ => Sum.inr (false, cl n a, cl n (l.headD a))
  | ⟨GateOp.or, l⟩ => Sum.inr (true, cl n (l.headD n), cl n (l.tail.headD (l.headD n)))
  | ⟨_, _⟩ => Sum.inl (cl n n)

noncomputable def toGate (n : ℕ) (d : Fin (n + 1) ⊕ Bool × Fin (n + 1) × Fin (n + 1)) : Gate :=
  Sum.elim (fun (x7 : Fin (n + 1)) => ({ op := GateOp.not, inputs := [↑x7] } : Gate))
    (fun (x7 : Bool × Fin (n + 1) × Fin (n + 1)) =>
      ({ op := Bool.rec GateOp.and GateOp.or x7.1, inputs := [↑x7.2.1, ↑x7.2.2] } : Gate)) d

lemma toGate_inl (n : ℕ) (a : Fin (n + 1)) :
    toGate n (Sum.inl a) = { op := GateOp.not, inputs := [(a : ℕ)] } := rfl

lemma toGate_inr_false (n : ℕ) (a b : Fin (n + 1)) :
    toGate n (Sum.inr (false, a, b)) = { op := GateOp.and, inputs := [(a : ℕ), (b : ℕ)] } := rfl

lemma toGate_inr_true (n : ℕ) (a b : Fin (n + 1)) :
    toGate n (Sum.inr (true, a, b)) = { op := GateOp.or, inputs := [(a : ℕ), (b : ℕ)] } := rfl

lemma get_cl (w : List Bool) (n a : ℕ) (hw : w.length = n) : w[min a n]? = w[a]? := by
  rcases Nat.lt_or_ge a n with h | h
  · rw [Nat.min_eq_left h.le]
  · rw [Nat.min_eq_right h, List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

lemma step_eq (n : ℕ) (op : GateOp) (l : List ℕ) (w : List Bool) (hw : w.length = n)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (h2 : l.length ≤ 2) :
    stepGate w (toGate n (desc n ⟨op, l⟩)) = stepGate w ⟨op, l⟩ := by
  have e1 : ∀ a, w[min a n]? = w[a]? := fun a => get_cl w n a hw
  have e2 : w[n]? = none := List.getElem?_eq_none (by omega)
  rcases hop with rfl | rfl | rfl <;> rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    first
    | (exfalso; simp only [List.length_cons] at h2; omega)
    | simp [stepGate, toGate_inl, toGate_inr_false, toGate_inr_true, desc, cl, GateOp.eval,
        List.getD_eq_getElem?_getD, e1, e2]

lemma fold_congr (gs : List Gate) : ∀ (L : List Gate) (n : ℕ) (init : List Bool),
    init.length = n → L.length = gs.length →
    (∀ (i : ℕ) (h1 : i < L.length) (h2 : i < gs.length) (w : List Bool),
      w.length = n + i → stepGate w L[i] = stepGate w gs[i]) →
    L.foldl stepGate init = gs.foldl stepGate init := by
  induction gs with
  | nil =>
    intro L n init _ hL _
    have hnil : L = [] := List.eq_nil_of_length_eq_zero hL
    subst hnil
    rfl
  | cons g tl ih =>
    intro L n init hi hL h
    cases L with
    | nil => simp at hL
    | cons g' tl' =>
      have h0 : stepGate init g' = stepGate init g :=
        h 0 (by simp) (by simp) init (by omega)
      simp only [List.foldl_cons]
      rw [h0]
      refine ih tl' (n + 1) (stepGate init g) (by simp [stepGate, hi]) (by simpa using hL) ?_
      intro i h1 h2 w hw
      exact h (i + 1) (by simp only [List.length_cons]; omega)
        (by simp only [List.length_cons]; omega) w (by omega)

lemma main (x1 : ℕ) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) :
    ∀ (x : List Bool), x.length = x1 → C.eval x = Circuit.eval
      { gates := List.ofFn fun (i : Fin C.size) =>
          toGate (x1 + i.val) (desc (x1 + i.val) (C.gates[i.val]'i.isLt)),
        output := ((cl (x1 + C.size) C.output : Fin (x1 + C.size + 1)) : ℕ) } x := by
  intro x hx
  have hw : Circuit.wires
      { gates := List.ofFn fun (i : Fin C.size) =>
          toGate (x1 + i.val) (desc (x1 + i.val) (C.gates[i.val]'i.isLt)),
        output := ((cl (x1 + C.size) C.output : Fin (x1 + C.size + 1)) : ℕ) } x = C.wires x := by
    show List.foldl stepGate x (List.ofFn fun (i : Fin C.size) =>
          toGate (x1 + i.val) (desc (x1 + i.val) (C.gates[i.val]'i.isLt))) =
        List.foldl stepGate x C.gates
    refine fold_congr C.gates _ x1 x hx ?_ ?_
    · simp [Circuit.size]
    · intro i h1 h2 w hw
      rw [List.getElem_ofFn]
      obtain ⟨hop, hl⟩ := h _ (List.getElem_mem h2)
      exact step_eq (x1 + i) (C.gates[i]).op (C.gates[i]).inputs w hw (by simpa using hop) hl
  have hlen : (C.wires x).length = x1 + C.size := by
    show (C.gates.foldl stepGate x).length = x1 + C.gates.length
    rw [foldl_stepGate_len, hx]
  calc C.eval x = (C.wires x).getD C.output false := rfl
    _ = (C.wires x).getD (min C.output (x1 + C.size)) false := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, get_cl _ _ _ hlen]
    _ = _ := (congrArg (fun l => l.getD (min C.output (x1 + C.size)) false) hw).symm

end PEqualNP.Outside.L_meta_9115

theorem PEqualNP.Outside.L_meta_9115 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     ∃ (x4 : (x4 : Fin x2.size) → Fin (x1 + ↑x4 + (1 : ℕ)) ⊕ Bool × Fin (x1 + ↑x4 + (1 : ℕ)) × Fin (x1 + ↑x4 + (1 : ℕ))) (x5 : Fin (x1 + x2.size + (1 : ℕ))),       have x6 : List PEqualNP.CircuitLowerBounds.Gate := List.ofFn fun (x6 : Fin x2.size) => Sum.elim (fun (x7 : Fin (x1 + ↑x6 + (1 : ℕ))) => { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [↑x7] : PEqualNP.CircuitLowerBounds.Gate }) (fun (x7 : Bool × Fin (x1 + ↑x6 + (1 : ℕ)) × Fin (x1 + ↑x6 + (1 : ℕ))) => { op := Bool.rec PEqualNP.CircuitLowerBounds.GateOp.and PEqualNP.CircuitLowerBounds.GateOp.or x7.1, inputs := [↑x7.2.1, ↑x7.2.2] : PEqualNP.CircuitLowerBounds.Gate }) (x4 x6);       ∀ (x7 : List Bool), x7.length = x1 → x2.eval x7 = { gates := x6, output := ↑x5 : PEqualNP.CircuitLowerBounds.Circuit }.eval x7 := by
  intro x1 x2 h
  exact ⟨fun i => PEqualNP.Outside.L_meta_9115.desc (x1 + i.val) (x2.gates[i.val]'i.isLt),
    PEqualNP.Outside.L_meta_9115.cl (x1 + x2.size) x2.output,
    PEqualNP.Outside.L_meta_9115.main x1 x2 h⟩
