import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1354

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi


def deps (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.head?.toList
  | _ => g.inputs

theorem eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ i ∈ deps g, f i = f' i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  obtain ⟨op, l⟩ := g
  cases op with
  | not =>
    cases l with
    | nil => rfl
    | cons a l =>
      simp only [deps, List.head?_cons, Option.toList_some, List.mem_singleton, forall_eq] at h
      simp [GateOp.eval, h]
  | _ =>
    simp only [deps] at h
    rw [List.map_congr_left h]

theorem getD_eraseIdx_lt (l : List Bool) (p i : ℕ) (hi : i < p) :
    (l.eraseIdx p).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_lt hi]

theorem getD_eraseIdx_ge (l : List Bool) (p i : ℕ) (hi : p ≤ i) :
    (l.eraseIdx p).getD i false = l.getD (i + 1) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_ge hi]


def ren (p r i : ℕ) : ℕ := if i < p then i else if i = p then r else i - 1

def renG (p r : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren p r)⟩


theorem del_foldl_aux (W : List Bool) (p r : ℕ) (hr : r < p ∨ W.length ≤ r) :
    ∀ (L : List Gate) (v : List Bool), L.foldl step v = W → p < v.length →
      (∀ g ∈ L, p ∈ deps g → W.getD p false = W.getD r false) →
      (L.map (renG p r)).foldl step (v.eraseIdx p) = W.eraseIdx p := by
  intro L
  induction L with
  | nil =>
    intro v hW _ _
    simp only [List.foldl_nil] at hW
    subst hW
    rfl
  | cons g L ih =>
    intro v hW hp hv
    rw [List.foldl_cons] at hW
    rw [List.map_cons, List.foldl_cons]
    have hvW : ∀ i, i < v.length → v.getD i false = W.getD i false := fun i hi => by
      rw [← hW, foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton]; omega)]
      exact (getD_append_lt _ _ _ hi).symm
    have hWlen : v.length + 1 + L.length = W.length := by
      have := congrArg List.length hW
      rw [foldl_step_length] at this
      simp only [step, List.length_append, List.length_singleton] at this
      omega
    have hstep : step (v.eraseIdx p) (renG p r g) = (step v g).eraseIdx p := by
      simp only [step, renG, List.map_map]
      rw [List.eraseIdx_append_of_lt_length hp]
      congr 2
      apply eval_congr
      intro i hi
      simp only [Function.comp, ren]
      split_ifs with h1 h2
      · exact getD_eraseIdx_lt _ _ _ h1
      · subst h2
        rcases hr with hr | hr
        · rw [getD_eraseIdx_lt _ _ _ hr, hvW _ (by omega), hvW _ hp]
          exact (hv g (by simp) hi).symm
        · rw [getD_of_length_le _ _ (by rw [List.length_eraseIdx_of_lt hp]; omega), hvW _ hp,
            hv g (by simp) hi, getD_of_length_le _ _ hr]
      · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]
    rw [hstep]
    exact ih _ hW (by simp only [step, List.length_append, List.length_singleton]; omega)
      (fun g' hg' => hv g' (List.mem_cons_of_mem _ hg'))

end PEqualNP.Outside.L_meta_1354

theorem PEqualNP.Outside.L_meta_1354 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.map PEqualNP.CircuitLowerBounds.Gate.op = gates.map PEqualNP.CircuitLowerBounds.Gate.op ∧ gates'.map (fun g => g.inputs.length) = gates.map (fun g => g.inputs.length) ∧ ∀ (j : ℕ) (x : Fin n → Bool), j < gates.length → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + 1 + j⟩ (List.ofFn x ++ [false]) := by
  intro n gates
  refine ⟨gates.map (PEqualNP.Outside.L_meta_1354.renG n (n + 1 + gates.length)), ?_, ?_, ?_⟩
  · simp [List.map_map, PEqualNP.Outside.L_meta_1354.renG, Function.comp_def]
  · simp [List.map_map, PEqualNP.Outside.L_meta_1354.renG, Function.comp_def]
  · intro j x hj
    let v : List Bool := List.ofFn x ++ [false]
    let W : List Bool := gates.foldl PEqualNP.Outside.L_meta_1354.step v
    have hvlen : v.length = n + 1 := by simp [v]
    have hWlen : W.length = n + 1 + gates.length := by
      simp only [W, PEqualNP.Outside.L_meta_1354.foldl_step_length, hvlen]
    have hfalse : W.getD n false = false := by
      rw [show W = gates.foldl PEqualNP.Outside.L_meta_1354.step v from rfl,
        PEqualNP.Outside.L_meta_1354.foldl_step_getD _ _ _ (by omega)]
      change (List.ofFn x ++ [false]).getD n false = false
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp
    have herase : v.eraseIdx n = List.ofFn x := by
      change (List.ofFn x ++ [false]).eraseIdx n = List.ofFn x
      rw [List.eraseIdx_append_of_length_le (by simp)]
      simp
    have heq := PEqualNP.Outside.L_meta_1354.del_foldl_aux W n (n + 1 + gates.length)
      (Or.inr hWlen.le) gates v rfl (by omega)
      (fun g hg hp => by
        rw [hfalse, PEqualNP.Outside.L_meta_1354.getD_of_length_le _ _ hWlen.le])
    rw [herase] at heq
    change ((gates.map (PEqualNP.Outside.L_meta_1354.renG n (n + 1 + gates.length))).foldl
      PEqualNP.Outside.L_meta_1354.step (List.ofFn x)).getD (n + j) false =
      W.getD (n + 1 + j) false
    rw [heq, PEqualNP.Outside.L_meta_1354.getD_eraseIdx_ge _ _ _ (by omega)]
    congr 1
    omega
