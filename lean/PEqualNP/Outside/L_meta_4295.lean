import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4295

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves

def wst (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wst x := rfl

theorem foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl wst w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, wst]; omega

theorem getD_app_lt (l l' : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_last (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl wst w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [wst]; omega)]
    exact getD_app_lt _ _ _ h

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f g : ℕ → Bool) (h : ∀ i ∈ l, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
    intro hf i hi
    exact h i hi (hf i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    rintro ⟨i, hi, hf⟩
    exact ⟨i, hi, h i hi hf⟩

def ren (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩

theorem suffix_le (n m p : ℕ) (hp : p < n + m) (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (k : ℕ) (N O : List Bool), N.length = n + m + k → O.length = n + m + 1 + k →
    (∀ i, N.getD (eraseRedirect n m p i) false = true → O.getD i false = true) →
    ∀ i, ((gs.map (ren n m p)).foldl wst N).getD (eraseRedirect n m p i) false = true →
      (gs.foldl wst O).getD i false = true := by
  induction gs with
  | nil => intro k N O _ _ hrel; simpa using hrel
  | cons g gs ih =>
    intro k N O hN hO hrel
    simp only [List.map_cons, List.foldl_cons]
    apply ih (fun g' hg' => hop g' (List.mem_cons_of_mem g hg')) (k + 1) _ _
      (by simp [wst, hN]; omega) (by simp [wst, hO]; omega)
    intro i hi
    rcases lt_trichotomy i O.length with h | h | h
    · have hr : eraseRedirect n m p i < N.length := by
        unfold eraseRedirect; split_ifs <;> omega
      rw [show wst N (ren n m p g) = N ++ _ from rfl, getD_app_lt _ _ _ hr] at hi
      rw [show wst O g = O ++ _ from rfl, getD_app_lt _ _ _ h]
      exact hrel i hi
    · subst h
      have hr : eraseRedirect n m p O.length = N.length := by
        unfold eraseRedirect; split_ifs <;> omega
      rw [hr, show wst N (ren n m p g) = N ++ _ from rfl, getD_last] at hi
      rw [show wst O g = O ++ _ from rfl, getD_last]
      simp only [ren, List.map_map] at hi
      exact eval_mono g.op (hop g (List.mem_cons_self ..)) g.inputs _ _ (fun i _ => hrel i) hi
    · have hr : N.length + 1 ≤ eraseRedirect n m p i := by
        unfold eraseRedirect; split_ifs <;> omega
      rw [getD_ge _ _ (by simp [wst]; omega)] at hi
      cases hi

theorem suffix_ge (n m p : ℕ) (hp : p < n + m) (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (k : ℕ) (N O : List Bool), N.length = n + m + k → O.length = n + m + 1 + k →
    (∀ i, O.getD i false = true → N.getD (eraseRedirect n m p i) false = true) →
    ∀ i, (gs.foldl wst O).getD i false = true →
      ((gs.map (ren n m p)).foldl wst N).getD (eraseRedirect n m p i) false = true := by
  induction gs with
  | nil => intro k N O _ _ hrel; simpa using hrel
  | cons g gs ih =>
    intro k N O hN hO hrel
    simp only [List.map_cons, List.foldl_cons]
    apply ih (fun g' hg' => hop g' (List.mem_cons_of_mem g hg')) (k + 1) _ _
      (by simp [wst, hN]; omega) (by simp [wst, hO]; omega)
    intro i hi
    rcases lt_trichotomy i O.length with h | h | h
    · have hr : eraseRedirect n m p i < N.length := by
        unfold eraseRedirect; split_ifs <;> omega
      rw [show wst N (ren n m p g) = N ++ _ from rfl, getD_app_lt _ _ _ hr]
      rw [show wst O g = O ++ _ from rfl, getD_app_lt _ _ _ h] at hi
      exact hrel i hi
    · subst h
      have hr : eraseRedirect n m p O.length = N.length := by
        unfold eraseRedirect; split_ifs <;> omega
      rw [hr, show wst N (ren n m p g) = N ++ _ from rfl, getD_last]
      rw [show wst O g = O ++ _ from rfl, getD_last] at hi
      simp only [ren, List.map_map]
      exact eval_mono g.op (hop g (List.mem_cons_self ..)) g.inputs _ _ (fun i _ => hrel i) hi
    · rw [getD_ge _ _ (by simp [wst]; omega)] at hi
      cases hi

theorem gates_split (C : Circuit) (m : ℕ) (gm : Gate) (hm : C.gates[m]? = some gm) :
    C.gates = C.gates.take m ++ gm :: C.gates.drop (m + 1) := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hm
  conv_lhs => rw [← List.take_append_drop m C.gates, List.drop_eq_getElem_cons hlt, hget]

theorem erase_eq (n : ℕ) (C : Circuit) (m p : ℕ) (hlt : m < C.gates.length) :
    eraseGate n C m p = ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (ren n m p),
      eraseRedirect n m p C.output⟩ := by
  unfold eraseGate
  rw [if_pos hlt]
  rfl

theorem erase_len (n : ℕ) (C : Circuit) (m p : ℕ) (hlt : m < C.gates.length) :
    (eraseGate n C m p).gates.length = C.gates.length - 1 := by
  rw [erase_eq n C m p hlt]
  simp
  omega

theorem lift_wires (n : ℕ) (C : Circuit) (m p h : ℕ) (x : List Bool) :
    (liftAt n C m p h).wires x = (eraseGate n C m p).wires x ++
      [GateOp.or.eval [((eraseGate n C m p).wires x).getD (eraseGate n C m p).output false,
        ((eraseGate n C m p).wires x).getD h false]] := by
  simp [liftAt, wires_eq, List.foldl_append, wst]

-- the facts about one erasure, for one input list
theorem facts (n : ℕ) (C : Circuit) (m p h : ℕ) (gm : Gate) (hm : C.gates[m]? = some gm)
    (hgo : gm.op = GateOp.or) (hgi : gm.inputs = [p, h] ∨ gm.inputs = [h, p])
    (hp : p < n + m) (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : List Bool) (hx : x.length = n) :
    (∀ i, ((eraseGate n C m p).wires x).getD (eraseRedirect n m p i) false = true →
        (C.wires x).getD i false = true) ∧
    (((C.gates.take m).foldl wst x).getD h false = false → ∀ i,
        (C.wires x).getD i false = true →
        ((eraseGate n C m p).wires x).getD (eraseRedirect n m p i) false = true) ∧
    (∀ i < n + m, ((eraseGate n C m p).wires x).getD i false =
        ((C.gates.take m).foldl wst x).getD i false ∧
      (C.wires x).getD i false = ((C.gates.take m).foldl wst x).getD i false) ∧
    (C.wires x).getD (n + m) false = (((C.gates.take m).foldl wst x).getD p false ||
        ((C.gates.take m).foldl wst x).getD h false) ∧
    ((eraseGate n C m p).wires x).length = n + (C.gates.length - 1) := by
  have hlt := (List.getElem?_eq_some_iff.mp hm).1
  set A := (C.gates.take m).foldl wst x with hAdef
  have hA : A.length = n + m := by
    rw [hAdef, foldl_len, hx, List.length_take]; omega
  set vm := gm.op.eval (gm.inputs.map fun i => A.getD i false) with hvm
  have hvm' : vm = (A.getD p false || A.getD h false) := by
    rw [hvm, hgo]
    rcases hgi with hgi | hgi <;> rw [hgi] <;> simp [GateOp.eval, Bool.or_comm]
  have hOw : C.wires x = (C.gates.drop (m + 1)).foldl wst (A ++ [vm]) := by
    rw [wires_eq]
    nth_rewrite 1 [gates_split C m gm hm]
    rw [List.foldl_append, List.foldl_cons]
    rfl
  have hEw : (eraseGate n C m p).wires x = ((C.gates.drop (m + 1)).map (ren n m p)).foldl wst A := by
    rw [erase_eq n C m p hlt, wires_eq, List.foldl_append]
  have hop' : ∀ g ∈ C.gates.drop (m + 1), g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => hAO g (List.mem_of_mem_drop hg)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hOw, hEw]
    apply suffix_le n m p hp _ hop' 0 A (A ++ [vm]) (by simpa using hA) (by simp [hA])
    intro i hi
    unfold eraseRedirect at hi
    split_ifs at hi with h1 h2
    · subst h1
      rw [← hA, getD_last, hvm', hi]
      rfl
    · rw [getD_ge _ _ (by omega)] at hi
      cases hi
    · rw [getD_app_lt _ _ _ (by omega)]
      exact hi
  · intro hhf
    rw [hOw, hEw]
    apply suffix_ge n m p hp _ hop' 0 A (A ++ [vm]) (by simpa using hA) (by simp [hA])
    intro i hi
    unfold eraseRedirect
    split_ifs with h1 h2
    · subst h1
      rw [← hA, getD_last, hvm', hhf, Bool.or_false] at hi
      exact hi
    · rw [getD_ge _ _ (by simp [hA]; omega)] at hi
      cases hi
    · rw [getD_app_lt _ _ _ (by omega)] at hi
      exact hi
  · intro i hi
    constructor
    · rw [hEw, foldl_getD_lt _ _ _ (by omega)]
    · rw [hOw, foldl_getD_lt _ _ _ (by simp [hA]; omega), getD_app_lt _ _ _ (by omega)]
  · rw [hOw, foldl_getD_lt _ _ _ (by simp [hA]), ← hA, getD_last, hvm']
  · rw [hEw, foldl_len, hA]
    simp
    omega

theorem lift_eval (n : ℕ) (C : Circuit) (m p h : ℕ) (gm : Gate) (hm : C.gates[m]? = some gm)
    (hgo : gm.op = GateOp.or) (hgi : gm.inputs = [p, h] ∨ gm.inputs = [h, p])
    (hp : p < n + m) (hh : h < n + m) (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hW : WireBelowOutput n C h) (x : Fin n → Bool) :
    (liftAt n C m p h).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hlt := (List.getElem?_eq_some_iff.mp hm).1
  obtain ⟨F1, F2, F3, _, F5⟩ := facts n C m p h gm hm hgo hgi hp hAO (List.ofFn x) (by simp)
  have hev : (liftAt n C m p h).eval (List.ofFn x) =
      (((eraseGate n C m p).wires (List.ofFn x)).getD (eraseRedirect n m p C.output) false ||
        ((eraseGate n C m p).wires (List.ofFn x)).getD h false) := by
    unfold Circuit.eval
    rw [lift_wires]
    have : (liftAt n C m p h).output = ((eraseGate n C m p).wires (List.ofFn x)).length := by
      rw [F5]; simp [liftAt, erase_len n C m p hlt]
    rw [this, getD_last, erase_eq n C m p hlt]
    simp [GateOp.eval]
  have hhe : ((eraseGate n C m p).wires (List.ofFn x)).getD h false =
      (C.wires (List.ofFn x)).getD h false := by
    rw [(F3 h hh).1, (F3 h hh).2]
  rw [hev, hhe]
  cases hF : C.eval (List.ofFn x)
  · have h1 : ((eraseGate n C m p).wires (List.ofFn x)).getD (eraseRedirect n m p C.output) false = false := by
      cases e : ((eraseGate n C m p).wires (List.ofFn x)).getD (eraseRedirect n m p C.output) false
      · rfl
      · have := F1 _ e
        unfold Circuit.eval at hF
        rw [hF] at this; cases this
    have h2 : (C.wires (List.ofFn x)).getD h false = false := by
      cases e : (C.wires (List.ofFn x)).getD h false
      · rfl
      · have := hW x e
        rw [hF] at this; cases this
    rw [h1, h2]; rfl
  · cases e : (C.wires (List.ofFn x)).getD h false
    · have hA : ((C.gates.take m).foldl wst (List.ofFn x)).getD h false = false := by
        rw [← (F3 h hh).2]; exact e
      unfold Circuit.eval at hF
      rw [F2 hA _ hF]; rfl
    · simp

def Bc (n : ℕ) (C : Circuit) (j : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Bool =>
    (C.wires (List.ofFn x)).getD (n + j) false = true ∧ C.eval (List.ofFn x) = false).card

def Phi (n : ℕ) (C : Circuit) : ℕ := ∑ j ∈ Finset.range C.gates.length, Bc n C j

theorem lift_phi (n : ℕ) (C : Circuit) (m p h : ℕ) (gm : Gate) (hm : C.gates[m]? = some gm)
    (hgo : gm.op = GateOp.or) (hgi : gm.inputs = [p, h] ∨ gm.inputs = [h, p])
    (hp : p < n + m) (hh : h < n + m) (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hW : WireBelowOutput n C h) (hP : ¬ WireBelowOutput n C p) :
    Phi n (liftAt n C m p h) < Phi n C := by
  have hlt := (List.getElem?_eq_some_iff.mp hm).1
  have hE := lift_eval n C m p h gm hm hgo hgi hp hh hAO hW
  obtain ⟨k, hk⟩ : ∃ k, C.gates.length = m + 1 + k := ⟨C.gates.length - m - 1, by omega⟩
  have hL1 : (liftAt n C m p h).gates.length = m + k + 1 := by
    simp [liftAt, erase_len n C m p hlt]; omega
  -- wires of the lifted circuit against the old ones
  have hw1 : ∀ x : Fin n → Bool, ∀ j < m, ((liftAt n C m p h).wires (List.ofFn x)).getD (n + j) false =
      (C.wires (List.ofFn x)).getD (n + j) false := by
    intro x j hj
    obtain ⟨_, _, F3, _, F5⟩ := facts n C m p h gm hm hgo hgi hp hAO (List.ofFn x) (by simp)
    rw [lift_wires, getD_app_lt _ _ _ (by rw [F5]; omega), (F3 _ (by omega)).1, (F3 _ (by omega)).2]
  have hw2 : ∀ x : Fin n → Bool, ∀ i < k,
      ((liftAt n C m p h).wires (List.ofFn x)).getD (n + (m + i)) false = true →
      (C.wires (List.ofFn x)).getD (n + (m + 1 + i)) false = true := by
    intro x i hi hw
    obtain ⟨F1, _, _, _, F5⟩ := facts n C m p h gm hm hgo hgi hp hAO (List.ofFn x) (by simp)
    rw [lift_wires, getD_app_lt _ _ _ (by rw [F5]; omega)] at hw
    apply F1
    have : eraseRedirect n m p (n + (m + 1 + i)) = n + (m + i) := by
      unfold eraseRedirect; split_ifs <;> omega
    rw [this]; exact hw
  have hlast : Bc n (liftAt n C m p h) (m + k) = 0 := by
    rw [Bc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨hw, he⟩
    have : (liftAt n C m p h).output = n + (m + k) := by
      simp [liftAt, erase_len n C m p hlt]; omega
    unfold Circuit.eval at he
    rw [this, hw] at he
    cases he
  have hmid : 1 ≤ Bc n C m := by
    unfold WireBelowOutput at hP
    push Not at hP
    obtain ⟨x, hxp, hxe⟩ := hP
    obtain ⟨_, _, F3, F4, _⟩ := facts n C m p h gm hm hgo hgi hp hAO (List.ofFn x) (by simp)
    apply Finset.card_pos.mpr
    refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, by simpa using hxe⟩⟩
    rw [F4, ← (F3 p hp).2, hxp]; rfl
  unfold Phi
  rw [hL1, hk, Finset.sum_range_succ, Finset.sum_range_add, Finset.sum_range_add,
    Finset.sum_range_succ]
  have s1 : ∑ j ∈ Finset.range m, Bc n (liftAt n C m p h) j = ∑ j ∈ Finset.range m, Bc n C j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    unfold Bc
    congr 1
    apply Finset.filter_congr
    intro x _
    rw [hw1 x j hj, hE x]
  have s2 : ∑ i ∈ Finset.range k, Bc n (liftAt n C m p h) (m + i) ≤
      ∑ i ∈ Finset.range k, Bc n C (m + 1 + i) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    apply Finset.card_le_card
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨hw, he⟩
    exact ⟨hw2 x i hi hw, by rw [← hE x]; exact he⟩
  rw [s1, hlast]
  omega

-- the gates of the lifted circuit
theorem gateAt_eq (C : Circuit) (j : ℕ) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j = (C.gates[j]?).getD ⟨GateOp.or, []⟩ := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD]

theorem lift_get_lt (n : ℕ) (C : Circuit) (m p h j : ℕ) (hlt : m < C.gates.length) (hj : j < m) :
    (liftAt n C m p h).gates[j]? = C.gates[j]? := by
  rw [show (liftAt n C m p h).gates = (eraseGate n C m p).gates ++ _ from rfl,
    List.getElem?_append_left (by rw [erase_len n C m p hlt]; omega), erase_eq n C m p hlt]
  simp only
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hj]

theorem lift_get_mid (n : ℕ) (C : Circuit) (m p h j : ℕ) (hlt : m < C.gates.length) (hj : m ≤ j)
    (hj2 : j + 1 < C.gates.length) :
    (liftAt n C m p h).gates[j]? = (C.gates[j + 1]?).map (ren n m p) := by
  rw [show (liftAt n C m p h).gates = (eraseGate n C m p).gates ++ _ from rfl,
    List.getElem?_append_left (by rw [erase_len n C m p hlt]; omega), erase_eq n C m p hlt]
  simp only
  rw [List.getElem?_append_right (by simp; omega), List.getElem?_map, List.getElem?_drop]
  simp only [List.length_take, min_eq_left hlt.le]
  congr 2
  omega

theorem lift_get_last (n : ℕ) (C : Circuit) (m p h : ℕ) (hlt : m < C.gates.length) :
    (liftAt n C m p h).gates[C.gates.length - 1]? =
      some ⟨GateOp.or, [eraseRedirect n m p C.output, h]⟩ := by
  rw [show (liftAt n C m p h).gates = (eraseGate n C m p).gates ++ _ from rfl,
    List.getElem?_append_right (by rw [erase_len n C m p hlt])]
  rw [erase_len n C m p hlt, Nat.sub_self]
  rw [erase_eq n C m p hlt]
  rfl

theorem lift_mem (n : ℕ) (C : Circuit) (m p h : ℕ) (hlt : m < C.gates.length) (g : Gate)
    (hg : g ∈ (liftAt n C m p h).gates) :
    g ∈ C.gates ∨ (∃ g' ∈ C.gates, g = ren n m p g') ∨
      g = ⟨GateOp.or, [eraseRedirect n m p C.output, h]⟩ := by
  rw [show (liftAt n C m p h).gates = (eraseGate n C m p).gates ++ _ from rfl,
    erase_eq n C m p hlt] at hg
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
  rcases hg with (hg | ⟨g', hg', rfl⟩) | hg
  · exact Or.inl (List.mem_of_mem_take hg)
  · exact Or.inr (Or.inl ⟨g', List.mem_of_mem_drop hg', rfl⟩)
  · exact Or.inr (Or.inr hg)

theorem lift_ao2 (n : ℕ) (C : Circuit) (m p h : ℕ) (gm : Gate) (hm : C.gates[m]? = some gm)
    (hp : p < n + m) (hh : h < n + m)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hout : C.output < n + C.gates.length) :
    PEqualNP.TopForm.IsAO2 n (liftAt n C m p h) ∧
      (liftAt n C m p h).output < n + (liftAt n C m p h).gates.length := by
  have hlt := (List.getElem?_eq_some_iff.mp hm).1
  obtain ⟨hAO, hRB, h2⟩ := hC
  have hL1 : (liftAt n C m p h).gates.length = C.gates.length := by
    simp [liftAt, erase_len n C m p hlt]; omega
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro g hg
    rcases lift_mem n C m p h hlt g hg with hg | ⟨g', hg', rfl⟩ | rfl
    · exact hAO g hg
    · exact hAO g' hg'
    · exact Or.inr rfl
  · intro j hj i hi
    rw [hL1] at hj
    rw [gateAt_eq] at hi
    by_cases hjm : j < m
    · rw [lift_get_lt n C m p h j hlt hjm] at hi
      have := hRB j (by omega) i (by rw [gateAt_eq]; exact hi)
      exact this
    · by_cases hj2 : j + 1 < C.gates.length
      · rw [lift_get_mid n C m p h j hlt (by omega) hj2] at hi
        obtain ⟨g', hg'⟩ : ∃ g', C.gates[j + 1]? = some g' := by
          exact ⟨_, List.getElem?_eq_getElem hj2⟩
        rw [hg'] at hi
        simp only [Option.map_some, Option.getD_some, ren, List.mem_map] at hi
        obtain ⟨i', hi', rfl⟩ := hi
        have := hRB (j + 1) hj2 i' (by rw [gateAt_eq, hg']; exact hi')
        unfold eraseRedirect; split_ifs <;> omega
      · have hjl : j = C.gates.length - 1 := by omega
        rw [hjl, lift_get_last n C m p h hlt] at hi
        simp only [Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · unfold eraseRedirect; split_ifs <;> omega
        · omega
  · intro g hg
    rcases lift_mem n C m p h hlt g hg with hg | ⟨g', hg', rfl⟩ | rfl
    · exact h2 g hg
    · simp [ren, h2 g' hg']
    · rfl
  · rw [hL1]
    simp [liftAt, erase_len n C m p hlt]
    omega

def Good (n : ℕ) (C : Circuit) : Prop :=
  ∀ x6 < C.gates.length, ∀ (x8 x9 : ℕ),
    C.gates[x6]? = some { op := GateOp.or, inputs := [x8, x9] : Gate } →
    (n ≤ x9 → WireBelowOutput n C x9 → WireBelowOutput n C x8) ∧
      (n ≤ x8 → WireBelowOutput n C x8 → WireBelowOutput n C x9)

theorem lift_step (n : ℕ) (C : Circuit) (m p h : ℕ) (hlt : m < C.gates.length)
    (hg : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (hnh : n ≤ h) (hW : WireBelowOutput n C h) (hP : ¬ WireBelowOutput n C p)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hout : C.output < n + C.gates.length) :
    Lift n C (liftAt n C m p h) ∧ PEqualNP.TopForm.IsAO2 n (liftAt n C m p h) ∧
      (liftAt n C m p h).output < n + (liftAt n C m p h).gates.length ∧
      Phi n (liftAt n C m p h) < Phi n C := by
  obtain ⟨gm, hm, hgo, hgi⟩ : ∃ gm, C.gates[m]? = some gm ∧ gm.op = GateOp.or ∧
      (gm.inputs = [p, h] ∨ gm.inputs = [h, p]) := by
    rcases hg with hg | hg
    · exact ⟨_, hg, rfl, Or.inl rfl⟩
    · exact ⟨_, hg, rfl, Or.inr rfl⟩
  have hRB := hC.2.1
  have hin : ∀ i ∈ gm.inputs, i < n + m := by
    intro i hi
    have := hRB m hlt i (by rw [gateAt_eq, hm]; exact hi)
    exact this
  have hp : p < n + m := hin p (by rcases hgi with e | e <;> rw [e] <;> simp)
  have hh : h < n + m := hin h (by rcases hgi with e | e <;> rw [e] <;> simp)
  have hAO := hC.1
  obtain ⟨h1, h2⟩ := lift_ao2 n C m p h gm hm hp hh hC hout
  refine ⟨⟨m, hlt, p, hp, h, hh, hnh, hg, hW, rfl⟩, h1, h2, ?_⟩
  exact lift_phi n C m p h gm hm hgo hgi hp hh hAO hW hP

theorem main (n : ℕ) : ∀ k, ∀ C : Circuit, Phi n C = k → PEqualNP.TopForm.IsAO2 n C →
    C.output < n + C.gates.length →
    ∃ C', Relation.ReflTransGen (Lift n) C C' ∧ Good n C' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hk hC hout
    by_cases hG : Good n C
    · exact ⟨C, Relation.ReflTransGen.refl, hG⟩
    · unfold Good at hG
      push Not at hG
      obtain ⟨m, hlt, x8, x9, hm, hbad⟩ := hG
      have key : ∃ p h, (C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨
          C.gates[m]? = some ⟨GateOp.or, [h, p]⟩) ∧ n ≤ h ∧ WireBelowOutput n C h ∧
          ¬ WireBelowOutput n C p := by
        by_cases h1 : n ≤ x9 → WireBelowOutput n C x9 → WireBelowOutput n C x8
        · obtain ⟨a, b, c⟩ := hbad h1
          exact ⟨x9, x8, Or.inr hm, a, b, c⟩
        · push Not at h1
          obtain ⟨a, b, c⟩ := h1
          exact ⟨x8, x9, Or.inl hm, a, b, c⟩
      obtain ⟨p, h, hg, hnh, hW, hP⟩ := key
      obtain ⟨hL, hC1, hout1, hphi⟩ := lift_step n C m p h hlt hg hnh hW hP hC hout
      obtain ⟨C', hC', hG'⟩ := ih _ (by rw [← hk]; exact hphi) (liftAt n C m p h) rfl hC1 hout1
      exact ⟨C', Relation.ReflTransGen.head hL hC', hG'⟩

end PEqualNP.Outside.L_meta_4295

theorem PEqualNP.Outside.L_meta_4295 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.gates.length → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), Relation.ReflTransGen (PEqualNP.CircuitMoves.Lift x1) x2 x5 ∧ ∀ x6 < x5.gates.length, ∀ (x8 x9 : ℕ), x5.gates[x6]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x8, x9] : PEqualNP.CircuitLowerBounds.Gate } → (x1 ≤ x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8) ∧ (x1 ≤ x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9) := by
  intro x1 x2 hC hout
  exact PEqualNP.Outside.L_meta_4295.main x1 _ x2 rfl hC hout
