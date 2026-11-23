import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1105_aux

open PEqualNP.CircuitLowerBounds

attribute [local instance] PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq

/-- One evaluation step of a gate list, as in Circuit.wires. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem length_step (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem getD_of_le (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem length_foldl (G : List Gate) : ∀ w : List Bool,
    (G.foldl step w).length = w.length + G.length := by
  induction G with
  | nil => intro w; simp
  | cons g G ih => intro w; rw [List.foldl_cons, ih, length_step]; simp; omega

theorem foldl_take_succ (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.take (t + 1)).foldl step w = step ((G.take t).foldl step w) G[t] := by
  rw [List.take_succ_eq_append_getElem ht, List.foldl_append]
  rfl

/-- Wire indices after inserting one new input wire at position 
. -/
def sh (n i : ℕ) : ℕ := if i < n then i else i + 1

/-- The gate of D: a NOT gate becomes a copy of the new input wire 
; any other gate reads
the shifted wires. -/
def fix (n : ℕ) (g : Gate) : Gate :=
  if g.op = GateOp.not then ⟨GateOp.and, [n]⟩ else ⟨g.op, g.inputs.map (sh n)⟩

theorem main (n : ℕ) (C : Circuit) (j : ℕ)
    (hC : ∀ i (g : Gate), C.gates[i]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ (i = j ∧ g.op = GateOp.not))) :
    ∃ (D H : Circuit), IsMonotoneCircuit D ∧ IsMonotoneCircuit H ∧ D.size ≤ C.size ∧
      H.size ≤ C.size ∧ ∀ x : List Bool, x.length = n → C.eval x = D.eval (x ++ [!(H.eval x)]) := by
  let a : ℕ := match C.gates[j]? with
    | some g => g.inputs.headD (n + j)
    | none => 0
  let D : Circuit := ⟨C.gates.map (fix n), sh n C.output⟩
  let H : Circuit := ⟨C.gates.take j, a⟩
  refine ⟨D, H, ?_, ?_, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hg
    unfold fix
    by_cases hnot : g.op = GateOp.not
    · rw [if_pos hnot]; left; rfl
    · rw [if_neg hnot]
      rcases hC i g hi with h | h | h
      · left; exact h
      · right; exact h
      · exact absurd h.2 hnot
  · intro g hg
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hg
    rw [List.getElem?_take] at hi
    split_ifs at hi with hij
    rcases hC i g hi with h | h | h
    · left; exact h
    · right; exact h
    · omega
  · simp [D, Circuit.size]
  · simp [H, Circuit.size]
  · intro x hx
    set b := !(H.eval x) with hb
    let W : ℕ → List Bool := fun t => (C.gates.take t).foldl step x
    let W' : ℕ → List Bool := fun t => ((C.gates.map (fix n)).take t).foldl step (x ++ [b])
    have hlenW : ∀ t, t ≤ C.gates.length → (W t).length = n + t := by
      intro t ht
      simp only [W]
      rw [length_foldl, List.length_take, hx]
      omega
    have hlenW' : ∀ t, t ≤ C.gates.length → (W' t).length = n + 1 + t := by
      intro t ht
      simp only [W']
      rw [length_foldl, List.length_take, List.length_map]
      simp [hx]
      omega
    have key : ∀ t, t ≤ C.gates.length → (W' t).getD n false = b ∧
        ∀ i, (W' t).getD (sh n i) false = (W t).getD i false := by
      intro t
      induction t with
      | zero =>
        intro _
        simp only [W, W', List.take_zero, List.foldl_nil]
        refine ⟨?_, fun i => ?_⟩
        · rw [List.getD_append_right _ _ _ _ (by omega), hx]; simp
        · unfold sh
          split_ifs with hi
          · rw [List.getD_append _ _ _ _ (by omega)]
          · rw [getD_of_le _ _ (by simp [hx]; omega), getD_of_le _ _ (by omega)]
      | succ t ih =>
        intro ht
        have ht' : t < C.gates.length := by omega
        obtain ⟨ihb, ihw⟩ := ih (by omega)
        have hW : W (t + 1) = step (W t) C.gates[t] := foldl_take_succ _ _ _ ht'
        have hW' : W' (t + 1) = step (W' t) (fix n C.gates[t]) := by
          simp only [W']
          rw [foldl_take_succ _ _ _ (by simpa using ht'), List.getElem_map]
        have lt := hlenW t (by omega)
        have lt' := hlenW' t (by omega)
        -- the new gate has the same value in both lists
        have hv : (fix n C.gates[t]).op.eval ((fix n C.gates[t]).inputs.map
              fun i => (W' t).getD i false) =
            C.gates[t].op.eval (C.gates[t].inputs.map fun i => (W t).getD i false) := by
          by_cases hnot : C.gates[t].op = GateOp.not
          · have htj : t = j := by
              rcases hC t C.gates[t] (List.getElem?_eq_getElem ht') with h | h | h
              · rw [h] at hnot; exact absurd hnot (by intro e; cases e)
              · rw [h] at hnot; exact absurd hnot (by intro e; cases e)
              · exact h.1
            subst htj
            simp only [fix, if_pos hnot, GateOp.eval, List.map_cons, List.map_nil,
              List.all_cons, List.all_nil, id, Bool.and_true]
            rw [ihb, hnot, hb]
            simp only [GateOp.eval]
            have ha : a = C.gates[t].inputs.headD (n + t) := by
              simp only [a, List.getElem?_eq_getElem ht']
            have hH : H.eval x = (W t).getD a false := rfl
            rw [hH, ha]
            congr 1
            rcases hin : C.gates[t].inputs with _ | ⟨c, rest⟩
            · simp only [List.headD_nil, List.map_nil]
              exact getD_of_le _ _ (by omega)
            · simp
          · simp only [fix, if_neg hnot, List.map_map]
            congr 1
            apply List.map_congr_left
            intro i _
            exact ihw i
        rw [hW, hW']
        refine ⟨?_, fun i => ?_⟩
        · simp only [step]
          rw [List.getD_append _ _ _ _ (by omega)]
          exact ihb
        · simp only [step]
          rcases lt_trichotomy i (n + t) with hi | hi | hi
          · have hs : sh n i < (W' t).length := by unfold sh; split_ifs <;> omega
            rw [List.getD_append _ _ _ _ hs, List.getD_append _ _ _ _ (by omega)]
            exact ihw i
          · have hs : sh n i = (W' t).length := by unfold sh; split_ifs <;> omega
            rw [hs, List.getD_append_right _ _ _ _ le_rfl,
              List.getD_append_right _ _ _ _ (by omega)]
            simp only [Nat.sub_self, lt, hi, Nat.sub_self]
            simpa using hv
          · have hs : (W' t).length + 1 ≤ sh n i := by unfold sh; split_ifs <;> omega
            rw [getD_of_le _ _ (by simp; omega), getD_of_le _ _ (by simp; omega)]
    have hall := key C.gates.length le_rfl
    show (C.wires x).getD C.output false = (D.wires (x ++ [b])).getD (sh n C.output) false
    have e1 : C.wires x = W C.gates.length := by
      simp only [W, List.take_length]; rfl
    have e2 : D.wires (x ++ [b]) = W' C.gates.length := by
      simp only [W', D]
      rw [show C.gates.length = (C.gates.map (fix n)).length by simp, List.take_length]
      rfl
    rw [e1, e2, hall.2]

end PEqualNP.Outside.L_meta_1105_aux

theorem PEqualNP.Outside.L_meta_1105 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ), (∀ i (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[i]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ (i = j ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not))) → ∃ (D H : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D ∧ PEqualNP.CircuitLowerBounds.IsMonotoneCircuit H ∧ D.size ≤ C.size ∧ H.size ≤ C.size ∧ ∀ x : List Bool, x.length = n → C.eval x = D.eval (x ++ [!(H.eval x)]) :=
  PEqualNP.Outside.L_meta_1105_aux.main
