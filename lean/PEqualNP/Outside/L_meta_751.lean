import Mathlib.Logic.Relation
import Mathlib.Tactic.SplitIfs
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_751

open PEqualNP.CircuitLowerBounds

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def runWires (gs : List Gate) (init : List Bool) : List Bool :=
  gs.foldl stepWire init

private lemma getD_append_singleton (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then b
      else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : i < w.length
  · rw [ite_eq_left h1, List.getElem?_append_left h1]
  · rw [ite_eq_right h1]
    by_cases h2 : i = w.length
    · subst h2
      rw [ite_eq_left rfl, List.getElem?_append_right (le_refl _)]
      simp
    · rw [ite_eq_right h2, List.getElem?_eq_none]
      · rfl
      · simp only [List.length_append, List.length_singleton]
        omega

private lemma getD_of_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) :
    w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

private lemma runWires_getD_prefix (gs : List Gate) (init : List Bool) (i : ℕ)
    (hi : i < init.length) :
    (runWires gs init).getD i false = init.getD i false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    change (runWires gs (stepWire init g)).getD i false = init.getD i false
    have hlt : i < (stepWire init g).length := by
      simp only [stepWire, List.length_append, List.length_singleton]
      omega
    rw [ih (stepWire init g) hlt, stepWire, getD_append_singleton, ite_eq_left hi]

private lemma runWires_getD_gate (gs : List Gate) (init : List Bool) (j : ℕ)
    (hj : j < gs.length) :
    (runWires gs init).getD (init.length + j) false =
      (gs[j]).op.eval
        ((gs[j]).inputs.map fun i =>
          if i < init.length + j then (runWires gs init).getD i false else false) := by
  induction gs generalizing init j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      change (runWires gs (stepWire init g)).getD (init.length + 0) false =
        g.op.eval (g.inputs.map fun i =>
          if i < init.length + 0 then (runWires gs (stepWire init g)).getD i false else false)
      have hlen : init.length < (stepWire init g).length := by
        simp only [stepWire, List.length_append, List.length_singleton]
        omega
      rw [Nat.add_zero, runWires_getD_prefix gs (stepWire init g) init.length hlen]
      have hhead : (stepWire init g).getD init.length false =
          g.op.eval (g.inputs.map fun i => init.getD i false) := by
        rw [stepWire, getD_append_singleton, ite_eq_right (lt_irrefl _), ite_eq_left rfl]
      rw [hhead]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < init.length
      · rw [ite_eq_left hi]
        have hi' : i < (stepWire init g).length := by
          simp only [stepWire, List.length_append, List.length_singleton]
          omega
        rw [runWires_getD_prefix gs (stepWire init g) i hi', stepWire,
          getD_append_singleton, ite_eq_left hi]
      · rw [ite_eq_right hi, getD_of_ge init i (not_lt.mp hi)]
    | succ k =>
      have hk : k < gs.length := by simpa using hj
      have hidx : init.length + (k + 1) = (stepWire init g).length + k := by
        simp only [stepWire, List.length_append, List.length_singleton]
        omega
      change (runWires gs (stepWire init g)).getD (init.length + (k + 1)) false =
        (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
          if i < init.length + (k + 1) then (runWires gs (stepWire init g)).getD i false else false)
      rw [hidx]
      exact ih (stepWire init g) k hk

private lemma runWires_length (gs : List Gate) (w : List Bool) :
    (runWires gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [runWires]
  | cons g gs ih =>
    change (runWires gs (stepWire w g)).length = _
    rw [ih]
    simp [stepWire, Nat.add_comm, Nat.add_left_comm]

private lemma inputValue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  change (runWires C.gates (List.ofFn x)).getD i false = _
  rw [runWires_getD_prefix _ _ _ (by simpa)]
  simp [List.getD_eq_getElem?_getD, hi]

private lemma gateValue (n j : ℕ) (C : Circuit) (g : Gate)
    (hg : C.gates[j]? = some g) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun b =>
        if b < n + j then (C.wires (List.ofFn x)).getD b false else false) := by
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp hg
  have h := runWires_getD_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn, hget] at h
  exact h

private def reads (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  ∃ (k : ℕ) (e : Gate), a = n + k ∧ C.gates[k]? = some e ∧ b ∈ e.inputs ∧ b < a

private lemma monotoneWire (n : ℕ) (C : Circuit) (i : ℕ)
    (hc : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      Relation.ReflTransGen (reads n C) i (n + j) →
      g.op = GateOp.and ∨ g.op = GateOp.or)
    (x x' : Fin n → Bool) (hxx : ∀ q, x q = true → x' q = true)
    (a : ℕ) (ha : Relation.ReflTransGen (reads n C) i a) :
    (C.wires (List.ofFn x)).getD a false = true →
      (C.wires (List.ofFn x')).getD a false = true := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    by_cases hinput : a < n
    · rw [inputValue C x a hinput, inputValue C x' a hinput]
      exact hxx _
    · let j := a - n
      have eq : a = n + j := by dsimp [j]; omega
      cases hg : C.gates[j]? with
      | none =>
        intro hv
        have hj := List.getElem?_eq_none_iff.mp hg
        change (runWires C.gates (List.ofFn x)).getD a false = true at hv
        rw [getD_of_ge _ _ (by rw [runWires_length, List.length_ofFn]; omega)] at hv
        cases hv
      | some g =>
        have hmono (b : ℕ) (hb : b ∈ g.inputs) :
            (if b < n + j then (C.wires (List.ofFn x)).getD b false else false) = true →
            (if b < n + j then (C.wires (List.ofFn x')).getD b false else false) = true := by
          split_ifs with hba
          · exact ih b (by omega) (ha.tail ⟨j, g, eq, hg, hb, by omega⟩)
          · simp
        have hop := hc j g hg (eq ▸ ha)
        rw [eq, gateValue n j C g hg x, gateValue n j C g hg x']
        rcases hop with hop | hop
        · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map]
          intro hv b hb
          obtain ⟨w, hw, rfl⟩ := hb
          exact hmono w hw (hv _ ⟨w, hw, rfl⟩)
        · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map]
          rintro ⟨_, ⟨w, hw, rfl⟩, hv⟩
          exact ⟨_, ⟨w, hw, rfl⟩, hmono w hw hv⟩

end PEqualNP.Outside.L_meta_751

theorem PEqualNP.Outside.L_meta_751 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (i : ℕ), (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → Relation.ReflTransGen (fun a b : ℕ => ∃ (k : ℕ) (e : PEqualNP.CircuitLowerBounds.Gate), a = n + k ∧ C.gates[k]? = some e ∧ b ∈ e.inputs ∧ b < a) i (n + j) → g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ x x' : Fin n → Bool, (∀ q : Fin n, x q = true → x' q = true) → (PEqualNP.CircuitLowerBounds.Circuit.wires C (List.ofFn x)).getD i false = true → (PEqualNP.CircuitLowerBounds.Circuit.wires C (List.ofFn x')).getD i false = true := by
  intro n C i hc x x' hxx
  exact PEqualNP.Outside.L_meta_751.monotoneWire n C i hc x x' hxx i .refl
