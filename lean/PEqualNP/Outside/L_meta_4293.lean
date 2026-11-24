import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

namespace PEqualNP.Outside.L_meta_4293

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [wiresFrom_cons, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem sim (n m p : ℕ) (B : List Gate) : ∀ U V : List Bool, U.length = V.length + 1 →
    n + m < U.length → p < V.length →
    (∀ i, U.getD i false = V.getD (eraseRedirect n m p i) false) →
    ∀ i, (wiresFrom B U).getD i false =
      (wiresFrom (B.map (fun g => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate))) V).getD
        (eraseRedirect n m p i) false := by
  induction B with
  | nil => intro U V _ _ _ hUV i; exact hUV i
  | cons g B ih =>
    intro U V hl hN hp hUV
    have hval : g.op.eval (g.inputs.map fun i => U.getD i false) =
        g.op.eval ((g.inputs.map (eraseRedirect n m p)).map fun i => V.getD i false) := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact hUV i
    refine ih (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval ((g.inputs.map (eraseRedirect n m p)).map fun i => V.getD i false)])
      (by simp [hl]) (by simp; omega) (by simp; omega) ?_
    intro i
    rcases Nat.lt_trichotomy i U.length with hi | hi | hi
    · have hri : eraseRedirect n m p i < V.length := by
        unfold eraseRedirect; split_ifs <;> omega
      rw [getD_snoc_ne U _ false i (by omega), getD_snoc_ne V _ false (eraseRedirect n m p i) (by omega)]
      exact hUV i
    · have hri : eraseRedirect n m p i = V.length := by
        unfold eraseRedirect; split_ifs <;> omega
      rw [hri, hi, getD_snoc_eq, getD_snoc_eq]
      exact hval
    · have hri : V.length + 1 < eraseRedirect n m p i + 1 := by
        unfold eraseRedirect; split_ifs <;> omega
      rw [List.getD_eq_default (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)]) false
          (by simp; omega),
        List.getD_eq_default (V ++ [g.op.eval ((g.inputs.map (eraseRedirect n m p)).map
          fun i => V.getD i false)]) false (by simp; omega)]

theorem redirect_lt (n m p i k : ℕ) (hp : p < n + m) (hk : m ≤ k) (hi : i < n + k + 1) :
    eraseRedirect n m p i < n + k := by
  unfold eraseRedirect; split_ifs <;> omega

theorem main (n : ℕ) (C C' : Circuit) (hC : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hL : Lift n C C') : IsAO2 n C' ∧ C'.output < n + C'.gates.length ∧ C'.size = C.size ∧
      circuitFun n C' = circuitFun n C := by
  obtain ⟨m, hm, p, hp, h, hh, hnh, hg, hbelow, rfl⟩ := hL
  obtain ⟨hAO, hRB, h2⟩ := hC
  obtain ⟨Eg, hEg⟩ : ∃ Eg : List Gate, Eg = C.gates.take m ++ (C.gates.drop (m + 1)).map
      (fun g => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate)) := ⟨_, rfl⟩
  have hEgates : (eraseGate n C m p).gates = Eg := by
    simp [eraseGate, hm, hEg]
  have hEout : (eraseGate n C m p).output = eraseRedirect n m p C.output := by
    simp [eraseGate, hm]
  have hEgl : Eg.length = C.gates.length - 1 := by rw [hEg]; simp; omega
  have hgm : C.gates[m] = ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m] = ⟨GateOp.or, [h, p]⟩ := by
    rcases hg with hg | hg
    · left; rw [List.getElem?_eq_getElem hm] at hg; exact Option.some.inj hg
    · right; rw [List.getElem?_eq_getElem hm] at hg; exact Option.some.inj hg
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
  have hLift : liftAt n C m p h =
      Circuit.mk (Eg ++ [⟨GateOp.or, [eraseRedirect n m p C.output, h]⟩]) (n + Eg.length) := by
    unfold liftAt; rw [hEgates, hEout]
  rw [hLift]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g hg'
    simp only [hEg, List.mem_append, List.mem_map, List.mem_singleton] at hg'
    rcases hg' with (hg' | ⟨g0, hg0, rfl⟩) | rfl
    · exact hAO g (List.mem_of_mem_take hg')
    · exact hAO g0 (List.mem_of_mem_drop hg0)
    · right; rfl
  · intro j hj i hi
    unfold gateAt at hi
    simp only at hj hi
    rw [List.getD_eq_getElem _ _ hj] at hi
    rcases lt_or_ge j Eg.length with hj1 | hj1
    · rw [List.getElem_append_left hj1] at hi
      have hj1' := hj1
      rw [hEgl] at hj1'
      subst hEg
      have htl : (List.take m C.gates).length = m := by simp; omega
      rcases lt_or_ge j m with hjm | hjm
      · rw [List.getElem_append_left (by omega), List.getElem_take] at hi
        exact hRB j (by omega) i (by unfold gateAt; rw [List.getD_eq_getElem _ _ (by omega)]; exact hi)
      · rw [List.getElem_append_right (by omega), List.getElem_map, List.getElem_drop] at hi
        simp only [List.mem_map] at hi
        obtain ⟨i0, hi0, rfl⟩ := hi
        have hk : m + 1 + (j - (List.take m C.gates).length) < C.gates.length := by
          rw [htl]; omega
        have hlt := hRB _ hk i0 (by unfold gateAt; rw [List.getD_eq_getElem _ _ hk]; exact hi0)
        rw [htl] at hlt
        apply redirect_lt n m p i0 j hp hjm
        omega
    · have hj2 : j = Eg.length := by simp at hj; omega
      subst hj2
      rw [List.getElem_append_right (le_refl _)] at hi
      simp at hi
      rcases hi with rfl | rfl
      · apply redirect_lt n m p C.output (Eg.length) hp (by omega); omega
      · omega
  · intro g hg'
    simp only [hEg, List.mem_append, List.mem_map, List.mem_singleton] at hg'
    rcases hg' with (hg' | ⟨g0, hg0, rfl⟩) | rfl
    · exact h2 g (List.mem_of_mem_take hg')
    · simp; exact h2 g0 (List.mem_of_mem_drop hg0)
    · rfl
  · simp
  · unfold Circuit.size; simp; omega
  · funext x
    unfold circuitFun Circuit.eval
    rw [wires_eq, wires_eq]
    simp only
    have hxl : (List.ofFn x).length = n := by simp
    obtain ⟨w0, hw0⟩ : ∃ w0 : List Bool, w0 = wiresFrom (C.gates.take m) (List.ofFn x) :=
      ⟨_, rfl⟩
    have hw0l : w0.length = n + m := by rw [hw0, length_wiresFrom]; simp; omega
    have hCw : wiresFrom C.gates (List.ofFn x) =
        wiresFrom (C.gates.drop (m + 1)) (w0 ++ [w0.getD p false || w0.getD h false]) := by
      conv_lhs => rw [hsplit]
      rw [wiresFrom_append, wiresFrom_cons, ← hw0]
      rcases hgm with hgm | hgm <;> rw [hgm] <;> simp [GateOp.eval, Bool.or_comm]
    have hEw : wiresFrom Eg (List.ofFn x) = wiresFrom ((C.gates.drop (m + 1)).map
        (fun g => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate))) w0 := by
      rw [hEg, wiresFrom_append, ← hw0]
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : n + Eg.length = (wiresFrom Eg (List.ofFn x)).length := by
      rw [length_wiresFrom]; omega
    rw [hlen, getD_snoc_eq]
    have hEh : (wiresFrom Eg (List.ofFn x)).getD h false = w0.getD h false := by
      rw [hEw, getD_wiresFrom _ w0 h (by omega)]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id,
      Bool.or_false]
    rw [hEh]
    cases hhv : w0.getD h false
    · simp only [Bool.or_false]
      rw [hCw, hEw, hhv, Bool.or_false]
      symm
      apply sim n m p _ (w0 ++ [w0.getD p false]) w0 (by simp) (by simp; omega) (by omega)
      intro i
      rcases Nat.lt_trichotomy i (n + m) with hi | hi | hi
      · rw [getD_snoc_ne w0 (w0.getD p false) false i (by omega)]
        have : eraseRedirect n m p i = i := by unfold eraseRedirect; split_ifs <;> omega
        rw [this]
      · have : eraseRedirect n m p i = p := by unfold eraseRedirect; split_ifs; omega
        rw [this, hi, ← hw0l, getD_snoc_eq]
      · have : n + m ≤ eraseRedirect n m p i := by unfold eraseRedirect; split_ifs <;> omega
        rw [List.getD_eq_default (w0 ++ [w0.getD p false]) false (by simp; omega),
          List.getD_eq_default w0 false (by omega)]
    · simp only [Bool.or_true]
      symm
      have hb := hbelow x
      unfold Circuit.eval at hb
      rw [wires_eq] at hb
      apply hb
      rw [hCw, getD_wiresFrom (C.gates.drop (m + 1))
        (w0 ++ [w0.getD p false || w0.getD h false]) h (by simp; omega),
        List.getD_append w0 _ false h (by omega)]
      exact hhv

end PEqualNP.Outside.L_meta_4293

theorem PEqualNP.Outside.L_meta_4293 : ∀ (x1 : ℕ) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.gates.length → PEqualNP.CircuitMoves.Lift x1 x2 x3 → PEqualNP.TopForm.IsAO2 x1 x3 ∧ x3.output < x1 + x3.gates.length ∧ x3.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x3 = PEqualNP.MetaComplexity.circuitFun x1 x2 := by
  intro x1 x2 x3 h1 h2 h3
  exact PEqualNP.Outside.L_meta_4293.main x1 x2 x3 h1 h2 h3
