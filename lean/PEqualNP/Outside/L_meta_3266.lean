import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3266

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The wires a gate really reads: a NOT gate reads its first input only.
def rel (g : Gate) : List ℕ := if g.op.eval [false] = true then g.inputs.take 1 else g.inputs

-- The inputs that the wires in O can depend on, through the first k gates of gs. The last wire
-- n + k is replaced by the wires its gate reads below it.
def dep (n : ℕ) (gs : List Gate) : ℕ → Finset ℕ → Finset ℕ
  | 0, O => O.filter (· < n)
  | k + 1, O => dep n gs k (O.erase (n + k) ∪
      (if n + k ∈ O then ((rel (gs.getD k ⟨GateOp.or, []⟩)).toFinset.filter (· < n + k)) else ∅))

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

-- The wires after the first k gates.
def W (gs : List Gate) (k : ℕ) (x : List Bool) : List Bool := (gs.take k).foldl stepF x

theorem W_zero (gs : List Gate) (x : List Bool) : W gs 0 x = x := by
  simp [W]

theorem W_succ (gs : List Gate) (k : ℕ) (hk : k < gs.length) (x : List Bool) :
    W gs (k + 1) x = stepF (W gs k x) gs[k] := by
  unfold W
  rw [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
  rfl

theorem W_length (gs : List Gate) (k : ℕ) (hk : k ≤ gs.length) (x : List Bool) :
    (W gs k x).length = x.length + k := by
  induction k with
  | zero => simp [W_zero]
  | succ k ih =>
    rw [W_succ gs k (by omega), stepF, List.length_append, ih (by omega)]
    simp
    omega

theorem countP_take_succ (gs : List Gate) (k : ℕ) (hk : k < gs.length) (p : Gate → Bool) :
    (gs.take (k + 1)).countP p = (gs.take k).countP p + (if p gs[k] then 1 else 0) := by
  rw [List.take_succ, List.getElem?_eq_getElem hk, List.countP_append]
  simp [List.countP_cons]

theorem rel_card (g : Gate) (hg : g.inputs.length ≤ 2) :
    (rel g).toFinset.card ≤ 1 + (if (!g.op.eval [false]) = true then 1 else 0) := by
  refine (List.toFinset_card_le _).trans ?_
  unfold rel
  by_cases h : g.op.eval [false] = true
  · simp [h]
  · simp only [h, if_false]
    simp at h
    simp [h]
    omega

theorem dep_card (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ k, k ≤ gs.length → ∀ O : Finset ℕ,
      (dep n gs k O).card ≤ O.card + (gs.take k).countP (fun g => !g.op.eval [false]) := by
  intro k
  induction k with
  | zero =>
    intro _ O
    simp only [dep, List.take_zero, List.countP_nil, add_zero]
    exact Finset.card_filter_le _ _
  | succ k ih =>
    intro hk O
    have hk' : k < gs.length := by omega
    have hget : gs.getD k ⟨GateOp.or, []⟩ = gs[k] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
    simp only [dep, hget]
    rw [countP_take_succ gs k hk']
    set L := n + k
    set X : Finset ℕ := if L ∈ O then ((rel gs[k]).toFinset.filter (· < L)) else ∅
    have hrel := rel_card gs[k] (hgs _ (List.getElem_mem hk'))
    have hO' : (O.erase L ∪ X).card ≤ O.card + (if (!gs[k].op.eval [false]) = true then 1 else 0) := by
      refine (Finset.card_union_le _ _).trans ?_
      by_cases hL : L ∈ O
      · have h1 := Finset.card_erase_of_mem hL
        have h2 : X.card ≤ (rel gs[k]).toFinset.card := by
          simp only [X, hL, if_true]
          exact Finset.card_filter_le _ _
        have h3 := Finset.card_pos.mpr ⟨L, hL⟩
        omega
      · have h1 : O.erase L = O := Finset.erase_eq_of_notMem hL
        have h2 : X = ∅ := by simp [X, hL]
        rw [h1, h2]
        simp
    have := ih (by omega) (O.erase L ∪ X)
    omega

theorem eval_congr (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (f h : ℕ → Bool) (hfh : ∀ i ∈ rel g, f i = h i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map h) := by
  rcases hop with hop | hop | hop
  · have hr : rel g = g.inputs := by simp [rel, hop, GateOp.eval]
    rw [hr] at hfh
    rw [List.map_congr_left hfh]
  · have hr : rel g = g.inputs := by simp [rel, hop, GateOp.eval]
    rw [hr] at hfh
    rw [List.map_congr_left hfh]
  · have hr : rel g = g.inputs.take 1 := by simp [rel, hop, GateOp.eval]
    rw [hr] at hfh
    rw [hop]
    cases hin : g.inputs with
    | nil => rfl
    | cons i tl =>
      rw [hin] at hfh
      have := hfh i (by simp)
      simp [GateOp.eval, this]

theorem dep_agree (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    ∀ k, k ≤ gs.length → ∀ (O : Finset ℕ) (x y : List Bool), x.length = n → y.length = n →
      (∀ i ∈ dep n gs k O, x.getD i false = y.getD i false) →
      ∀ w ∈ O, (W gs k x).getD w false = (W gs k y).getD w false := by
  intro k
  induction k with
  | zero =>
    intro _ O x y hx hy hag w hw
    rw [W_zero, W_zero]
    by_cases hwn : w < n
    · exact hag w (by simp [dep, hw, hwn])
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | succ k ih =>
    intro hk O x y hx hy hag w hw
    have hk' : k < gs.length := by omega
    have hget : gs.getD k ⟨GateOp.or, []⟩ = gs[k] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
    set L := n + k with hL
    set O' : Finset ℕ := O.erase L ∪
      (if L ∈ O then ((rel gs[k]).toFinset.filter (· < L)) else ∅) with hO'
    have hdep : dep n gs (k + 1) O = dep n gs k O' := by
      simp only [dep, hget, hO', hL]
    rw [hdep] at hag
    have IH := ih (by omega) O' x y hx hy hag
    have lx : (W gs k x).length = L := by rw [W_length gs k (by omega), hx]
    have ly : (W gs k y).length = L := by rw [W_length gs k (by omega), hy]
    rw [W_succ gs k hk', W_succ gs k hk', stepF, stepF]
    rcases lt_trichotomy w L with hwL | hwL | hwL
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact IH w (by simp [hO', hw, Nat.ne_of_lt hwL])
    · subst hwL
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [lx, ly, Nat.sub_self, List.getD_cons_zero]
      apply eval_congr gs[k] (hgs _ (List.getElem_mem hk'))
      intro i hi
      by_cases hiL : i < n + k
      · exact IH i (by simp [hO', hw, hi]; right; omega)
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_3266

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3266

theorem PEqualNP.Outside.L_meta_3266 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x4 : Finset ℕ), x4.card ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => !x5.op.eval [Bool.false]) x2.gates + (1 : ℕ) ∧ ∀ (x5 x6 : List Bool), x5.length = x1 → x6.length = x1 → (∀ x9 ∈ x4, x5.getD x9 Bool.false = x6.getD x9 Bool.false) → x2.eval x5 = x2.eval x6 := by
  intro n C hfan
  refine ⟨dep n C.gates C.gates.length {C.output}, ?_, ?_⟩
  · have := dep_card n C.gates (fun g hg => (hfan g hg).2) C.gates.length le_rfl {C.output}
    rw [List.take_length] at this
    simp at this
    omega
  · intro x y hx hy hag
    have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
      intro g hg
      have := (hfan g hg).1
      simpa using this
    have := dep_agree n C.gates hop C.gates.length le_rfl {C.output} x y hx hy hag C.output (by simp)
    have hw : ∀ z : List Bool, W C.gates C.gates.length z = C.wires z := by
      intro z
      unfold W Circuit.wires
      rw [List.take_length]
      rfl
    rw [hw, hw] at this
    exact this
