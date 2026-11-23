import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_196

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool := Circuit.wires ⟨gs, 0⟩ x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, Circuit.wires, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W, Circuit.wires]
  | append_singleton gs g ih =>
    rw [W_snoc, List.length_append, ih]
    simp
    omega

theorem W_append (l1 l2 : List Gate) (x : List Bool) : ∃ t, W (l1 ++ l2) x = W l1 x ++ t := by
  induction l2 using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton l2 g ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t ++ [g.op.eval (g.inputs.map fun i => (W (l1 ++ l2) x).getD i false)], ?_⟩
    rw [← List.append_assoc, W_snoc, ht, List.append_assoc]

theorem W_getD_prefix (gs : List Gate) (k i : ℕ) (x : List Bool) (hi : i < x.length + k)
    (hk : k ≤ gs.length) : (W gs x).getD i false = (W (gs.take k) x).getD i false := by
  obtain ⟨t, ht⟩ := W_append (gs.take k) (gs.drop k) x
  rw [List.take_append_drop] at ht
  have hl : i < (W (gs.take k) x).length := by
    rw [W_length, List.length_take]
    omega
  rw [ht, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hl]

theorem take_succ_of {α : Type} (l : List α) (k : ℕ) (a : α) (h : l[k]? = some a) :
    l.take (k + 1) = l.take k ++ [a] := by
  rw [List.take_add_one, h]
  rfl

theorem same_wires (gs : List Gate) (j a h : ℕ) (x : List Bool)
    (hj : gs[j]? = some ⟨GateOp.or, [a, h]⟩) (hh : h < x.length + j)
    (hb : (W gs x).getD h false = false) :
    ∀ k, k ≤ gs.length → W ((gs.set j ⟨GateOp.or, [a]⟩).take k) x = W (gs.take k) x := by
  have hjl : j < gs.length := (List.getElem?_eq_some_iff.mp hj).1
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hkl : k < gs.length := by omega
    have hc : gs[k]? = some gs[k] := List.getElem?_eq_getElem hkl
    by_cases hkj : k = j
    · subst hkj
      have hc' : (gs.set k ⟨GateOp.or, [a]⟩)[k]? = some ⟨GateOp.or, [a]⟩ := by
        rw [List.getElem?_set_self hkl]
      rw [take_succ_of _ k _ hc', take_succ_of _ k _ hj, W_snoc, W_snoc, ih (by omega)]
      have hw : (W (gs.take k) x).getD h false = false := by
        rw [← W_getD_prefix gs k h x hh (by omega)]
        exact hb
      simp only [GateOp.eval, List.map_cons, List.map_nil, hw]
      cases (W (gs.take k) x).getD a false <;> rfl
    · have hc' : (gs.set j ⟨GateOp.or, [a]⟩)[k]? = some gs[k] := by
        rw [List.getElem?_set_ne (Ne.symm hkj), hc]
      rw [take_succ_of _ k _ hc', take_succ_of _ k _ hc, W_snoc, W_snoc, ih (by omega)]

end PEqualNP.Outside.L_meta_196

open PEqualNP.Outside.L_meta_196 in
theorem PEqualNP.Outside.L_meta_196 : ∀ (n j a h : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool), C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩ → h < n + j → ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } x ≠ f x → PEqualNP.MetaComplexity.circuitFun n C x ≠ f x ∨ ((C.wires (List.ofFn x)).getD h false = true ∧ f x = false) := by
  intro n j a h C f hj hh x hne
  have hjl : j < C.gates.length := (List.getElem?_eq_some_iff.mp hj).1
  have hxl : (List.ofFn x).length = n := List.length_ofFn
  have hev : PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } x =
      ((W (C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩) (List.ofFn x)).getD C.output false ||
        (W (C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩) (List.ofFn x)).getD h false) := by
    show (W (C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩]) (List.ofFn x)).getD (n + C.size) false = _
    rw [W_snoc]
    have hl : (W (C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩) (List.ofFn x)).length = n + C.size := by
      rw [W_length, List.length_set, hxl]
      rfl
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl, Nat.sub_self]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  have hC : PEqualNP.MetaComplexity.circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl
  cases hb : (W C.gates (List.ofFn x)).getD h false
  · left
    have hs := same_wires C.gates j a h (List.ofFn x) hj (by rw [hxl]; exact hh) hb C.gates.length le_rfl
    rw [List.take_of_length_le (by rw [List.length_set]), List.take_length] at hs
    rw [hev, hs] at hne
    have hz : (W C.gates (List.ofFn x)).getD h false = false := hb
    rw [hz, Bool.or_false] at hne
    rw [hC]
    exact hne
  · right
    refine ⟨hb, ?_⟩
    have h1 : (W (C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩) (List.ofFn x)).getD h false = true := by
      rw [W_getD_prefix _ j h _ (by rw [hxl]; exact hh) (by rw [List.length_set]; omega),
        List.take_set_of_le (le_refl j), ← W_getD_prefix _ j h _ (by rw [hxl]; exact hh) (le_of_lt hjl)]
      exact hb
    rw [hev, h1, Bool.or_true] at hne
    cases hf : f x
    · rfl
    · rw [hf] at hne
      exact absurd rfl hne
