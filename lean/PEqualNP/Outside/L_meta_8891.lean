import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8891
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

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem set_mono (g' : Gate) (hg' : (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2) :
    ∀ (gs : List Gate) (m : ℕ) (g : Gate),
    (∀ h ∈ gs, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) → gs[m]? = some g →
    (∀ U V : List Bool, (∀ i, U.getD i false = true → V.getD i false = true) →
      g.op.eval (g.inputs.map fun i => U.getD i false) = true →
      g'.op.eval (g'.inputs.map fun i => V.getD i false) = true) →
    ∀ U V : List Bool, U.length = V.length → (∀ i, U.getD i false = true → V.getD i false = true) →
    ∀ i, (wf gs U).getD i false = true → (wf (gs.set m g') V).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro m g _ hm; simp at hm
  | cons h t ih =>
    intro m g hleg hm hdom U V hlen hUV i
    have hsn : ∀ (a b : Bool), (a = true → b = true) → ∀ j, (U ++ [a]).getD j false = true →
        (V ++ [b]).getD j false = true := by
      intro a b hab j hj
      rcases Nat.lt_trichotomy j U.length with hj' | hj' | hj'
      · rw [getD_snoc_lt _ _ _ hj'] at hj
        rw [getD_snoc_lt _ _ _ (by omega)]
        exact hUV j hj
      · rw [hj', getD_snoc_eq] at hj
        rw [hj', hlen, getD_snoc_eq]
        exact hab hj
      · rw [getD_snoc_gt _ _ _ hj'] at hj
        exact absurd hj (by simp)
    cases m with
    | zero =>
      have hg : h = g := by simpa using hm
      subst hg
      rw [List.set_cons_zero, wf_cons, wf_cons]
      exact mono2 t (fun h' hh' => hleg h' (List.mem_cons_of_mem _ hh')) _ _ (by simp [hlen])
        (hsn _ _ (hdom U V hUV)) i
    | succ m =>
      rw [List.set_cons_succ, wf_cons, wf_cons]
      exact ih m g (fun h' hh' => hleg h' (List.mem_cons_of_mem _ hh')) (by simpa using hm) hdom _ _
        (by simp [hlen])
        (hsn _ _ (eval_mono h.op (hleg h (List.mem_cons_self ..)).1 h.inputs U V hUV)) i

theorem cset (p : Gate → Bool) (g' : Gate) (hp' : p g' = false) : ∀ (gs : List Gate) (m : ℕ) (g : Gate),
    gs[m]? = some g → p g = true → (gs.set m g').countP p + 1 = gs.countP p := by
  intro gs
  induction gs with
  | nil => intro m g hm; simp at hm
  | cons h t ih =>
    intro m g hm hp
    cases m with
    | zero =>
      have hg : h = g := by simpa using hm
      subst hg
      rw [List.set_cons_zero, List.countP_cons, List.countP_cons, hp, hp']
      simp
    | succ m =>
      rw [List.set_cons_succ, List.countP_cons, List.countP_cons, ← ih m g (by simpa using hm) hp]
      omega

end PEqualNP.Outside.L_meta_8891

open PEqualNP.Outside.L_meta_8891 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8891 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 x4 x5 : ℕ),   x1.gates[x2]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate } →     x5 = x3 ∨ x5 = x4 →       have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1.gates.set x2 { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5] : PEqualNP.CircuitLowerBounds.Gate }, output := x1.output : PEqualNP.CircuitLowerBounds.Circuit };       PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size = x1.size ∧ List.countP (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => x10.inputs.length == (2 : ℕ)) x8.gates < List.countP (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => x10.inputs.length == (2 : ℕ)) x1.gates ∧ ∀ (x10 : List Bool), x1.eval x10 = Bool.true → x8.eval x10 = Bool.true := by
  intro C m a b c hm hc
  dsimp only
  intro hmono
  have hleg : ∀ h ∈ C.gates, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2 := fun h hh =>
    ⟨by simpa using (hmono h hh).1, (hmono h hh).2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_or_eq_of_mem_set hg with h | h
    · exact hmono g h
    · rw [h]; simp
  · show (C.gates.set m _).length = C.gates.length
    simp
  · have := cset (fun g : Gate => g.inputs.length == 2) ⟨GateOp.and, [c]⟩ (by simp) C.gates m _ hm (by simp)
    show List.countP (fun g : Gate => g.inputs.length == 2) (C.gates.set m ⟨GateOp.and, [c]⟩)
      < List.countP (fun g : Gate => g.inputs.length == 2) C.gates
    omega
  · intro x hx
    have hx' : (wf C.gates x).getD C.output false = true := hx
    exact set_mono ⟨GateOp.and, [c]⟩ ⟨Or.inl rfl, by simp⟩ C.gates m _ hleg hm (fun U V hUV h => by
      have hall : ([U.getD a false, U.getD b false]).all id = true := h
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, id] at hall
      show ([V.getD c false]).all id = true
      simp only [List.all_cons, List.all_nil, Bool.and_true, id]
      rcases hc with rfl | rfl
      · exact hUV _ hall.1
      · exact hUV _ hall.2) x x rfl (fun i hi => hi) C.output hx'
