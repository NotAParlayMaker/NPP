import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3434_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def remapGate (f : ℕ → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map f⟩

lemma foldl_step_length (gs : List Gate) (init : List Bool) :
    (gs.foldl step init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

lemma foldl_step_preserved (gs : List Gate) (init : List Bool) (k : ℕ) (hk : k < init.length) :
    (gs.foldl step init).getD k false = init.getD k false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step init g) (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma getD_eq_false_of_le {l : List Bool} {k : ℕ} (hk : l.length ≤ k) :
    l.getD k false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk, Option.getD_none]

lemma remap_wires_take (f : ℕ → ℕ) (C : Circuit) (x3 x4 : List Bool)
    (hlen : x3.length = x4.length)
    (hfix : ∀ k, x3.length ≤ k → f k = k)
    (hdisj : ∀ k < x3.length, f k < x3.length ∨ x3.length + C.size ≤ f k)
    (hinit : ∀ k, x4.getD (f k) false = x3.getD k false) :
    ∀ j ≤ C.gates.length, ∀ w : ℕ,
      (((C.gates.take j).map (remapGate f)).foldl step x4).getD (f w) false =
      ((C.gates.take j).foldl step x3).getD w false := by
  intro j
  induction j with
  | zero =>
    intro _ w
    simp only [List.take_zero, List.map_nil, List.foldl_nil]
    exact hinit w
  | succ j ih =>
    intro hj_le w
    have hj : j < C.gates.length := by omega
    have htake : C.gates.take (j + 1) = C.gates.take j ++ [C.gates[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
    rw [htake, List.map_append, List.map_singleton, List.foldl_append, List.foldl_append,
      List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
    set w1 := (C.gates.take j).foldl step x3
    set w2 := ((C.gates.take j).map (remapGate f)).foldl step x4
    have hlen1 : w1.length = x3.length + j := by
      simp [w1, foldl_step_length, Nat.le_of_lt hj]
    have hlen2 : w2.length = x3.length + j := by
      simp [w2, foldl_step_length, hlen, Nat.le_of_lt hj]
    by_cases hw_lt_in : w < x3.length
    · have h_w1 : (step w1 C.gates[j]).getD w false = x3.getD w false := by
        have h1 : (step w1 C.gates[j]).getD w false = w1.getD w false := by
          simp only [step, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by omega : w < w1.length)]
        have h2 : w1.getD w false = x3.getD w false :=
          foldl_step_preserved (C.gates.take j) x3 w hw_lt_in
        exact h1.trans h2
      rcases hdisj w hw_lt_in with hf_lt | hf_ge
      · have h_w2 : (step w2 (remapGate f C.gates[j])).getD (f w) false = x4.getD (f w) false := by
          have h1 : (step w2 (remapGate f C.gates[j])).getD (f w) false = w2.getD (f w) false := by
            simp only [step, List.getD_eq_getElem?_getD,
              List.getElem?_append_left (by omega : f w < w2.length)]
          have h2 : w2.getD (f w) false = x4.getD (f w) false :=
            foldl_step_preserved ((C.gates.take j).map (remapGate f)) x4 (f w) (by omega)
          exact h1.trans h2
        rw [h_w2, h_w1, hinit w]
      · have hlen_step2 : (step w2 (remapGate f C.gates[j])).length = x3.length + j + 1 := by
          simp [step, hlen2]
        have hf_ge1 : (step w2 (remapGate f C.gates[j])).length ≤ f w := by
          have : C.gates.length = C.size := rfl
          omega
        have hf_ge2 : x4.length ≤ f w := by
          have : C.gates.length = C.size := rfl
          omega
        rw [getD_eq_false_of_le hf_ge1, h_w1, ← hinit w, getD_eq_false_of_le hf_ge2]
    · have hfw : f w = w := hfix w (by omega)
      rw [hfw]
      by_cases hw_lt_j : w < x3.length + j
      · simp only [step, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega : w < w2.length),
          List.getElem?_append_left (by omega : w < w1.length)]
        have ih_w := ih (Nat.le_of_lt hj) w
        rwa [hfw] at ih_w
      · by_cases hw_eq : w = x3.length + j
        · subst hw_eq
          have h1 : (step w1 C.gates[j]).getD (x3.length + j) false =
              C.gates[j].op.eval (C.gates[j].inputs.map fun i => w1.getD i false) := by
            simp [step, hlen1]
          have h2 : (step w2 (remapGate f C.gates[j])).getD (x3.length + j) false =
              C.gates[j].op.eval ((C.gates[j].inputs.map f).map fun i => w2.getD i false) := by
            simp [step, hlen2, remapGate]
          rw [h2, h1, List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact ih (Nat.le_of_lt hj) i
        · have hlen_s1 : (step w1 C.gates[j]).length ≤ w := by simp [step, hlen1]; omega
          have hlen_s2 : (step w2 (remapGate f C.gates[j])).length ≤ w := by simp [step, hlen2]; omega
          rw [getD_eq_false_of_le hlen_s2, getD_eq_false_of_le hlen_s1]

end PEqualNP.Outside.L_meta_3434_aux

theorem PEqualNP.Outside.L_meta_3434 : ∀ (x1 : ℕ → ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : List Bool), x3.length = x4.length → (∀ (x6 : ℕ), x3.length ≤ x6 → x1 x6 = x6) → (∀ x7 < x3.length, x1 x7 < x3.length ∨ x3.length + x2.size ≤ x1 x7) → (∀ (x8 : ℕ), x4.getD (x1 x8) Bool.false = x3.getD x8 Bool.false) → { gates := List.map (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => { op := x9.op, inputs := List.map x1 x9.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates, output := x1 x2.output : PEqualNP.CircuitLowerBounds.Circuit }.eval x4 = x2.eval x3 := by
  intro x1 x2 x3 x4 hlen hfix hdisj hinit
  have h := PEqualNP.Outside.L_meta_3434_aux.remap_wires_take x1 x2 x3 x4 hlen hfix hdisj hinit
    x2.gates.length (le_refl _) x2.output
  rw [List.take_length] at h
  exact h
