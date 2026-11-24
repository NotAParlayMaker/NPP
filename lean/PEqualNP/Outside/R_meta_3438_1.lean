import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_3438_1

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def targetFun (x3 : Fin 9 → Bool) : Bool :=
  x3 0 && x3 1 || x3 1 && x3 2 || x3 2 && x3 3 || x3 3 && x3 4 || x3 4 && x3 0 ||
    x3 0 && x3 5 || x3 1 && x3 6 || x3 2 && x3 7 || x3 3 && x3 8 ||
    x3 5 && x3 7 || x3 6 && x3 8 || x3 8 && x3 5

private lemma wires_length (gs : List Gate) (init : List Bool) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map (fun i => acc[i]?.getD false))]) init).length =
      init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

private lemma wires_getD_lt (gs : List Gate) (init : List Bool)
    (i : ℕ) (hi : i < init.length) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map (fun j => acc.getD j false))]) init).getD i false =
      init.getD i false := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (init ++ [_]) (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem main
    (h_not : ∀ (x1 : Circuit), FanInTwo x1 →
      (∀ (x3 : Fin 9 → Bool), x1.eval (List.ofFn x3) = targetFun x3) →
      9 ≤ x1.output →
      x1.output < 9 + x1.gates.length →
      ∀ (gout : Gate), x1.gates[x1.output - 9]? = some gout →
      gout.op = GateOp.not →
      13 ≤ List.countP (fun x4 => GateOp.rec Bool.true Bool.true Bool.false (fun _ => Bool.true) Bool.true x4.op) x1.gates)
    (h_ao : ∀ (x1 : Circuit), FanInTwo x1 →
      (∀ (x3 : Fin 9 → Bool), x1.eval (List.ofFn x3) = targetFun x3) →
      9 ≤ x1.output →
      x1.output < 9 + x1.gates.length →
      ∀ (gout : Gate), x1.gates[x1.output - 9]? = some gout →
      (gout.op = GateOp.and ∨ gout.op = GateOp.or) →
      13 ≤ List.countP (fun x4 => GateOp.rec Bool.true Bool.true Bool.false (fun _ => Bool.true) Bool.true x4.op) x1.gates) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) x1.gates := by
  intro x1 hfan heval
  have heval' : ∀ (x3 : Fin 9 → Bool), x1.eval (List.ofFn x3) = targetFun x3 := heval
  by_cases hout9 : x1.output < 9
  · exfalso
    by_cases h12 : x1.output = 1 ∨ x1.output = 2
    · rcases h12 with h1 | h2
      · let y : Fin 9 → Bool := fun v => decide (v = 2 ∨ v = 3)
        have hy := heval' y
        simp only [Circuit.eval, Circuit.wires] at hy
        rw [wires_getD_lt x1.gates _ x1.output (by simp [hout9]), h1] at hy
        simp [List.getD_eq_getElem?_getD, y, targetFun] at hy
      · let y : Fin 9 → Bool := fun v => decide (v = 0 ∨ v = 1)
        have hy := heval' y
        simp only [Circuit.eval, Circuit.wires] at hy
        rw [wires_getD_lt x1.gates _ x1.output (by simp [hout9]), h2] at hy
        simp [List.getD_eq_getElem?_getD, y, targetFun] at hy
    · let y : Fin 9 → Bool := fun v => decide (v ≠ ⟨x1.output, hout9⟩)
      have hy := heval' y
      simp only [Circuit.eval, Circuit.wires] at hy
      rw [wires_getD_lt x1.gates _ x1.output (by simp [hout9])] at hy
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hout9, Option.getD_some] at hy
      have hy1 : y 1 = Bool.true := by
        simp only [y, decide_eq_true_eq, ne_eq, Fin.ext_iff]; omega
      have hy2 : y 2 = Bool.true := by
        simp only [y, decide_eq_true_eq, ne_eq, Fin.ext_iff]; omega
      have htf : targetFun y = Bool.true := by simp [targetFun, hy1, hy2]
      have hy_out : y ⟨x1.output, hout9⟩ = Bool.false := by simp [y]
      rw [hy_out, htf] at hy
      cases hy
  · by_cases hout_hi : 9 + x1.gates.length ≤ x1.output
    · exfalso
      have hy := heval' (fun _ => Bool.true)
      simp only [Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD] at hy
      rw [List.getElem?_eq_none] at hy
      · simp [targetFun] at hy
      · rw [wires_length]
        simp only [List.length_ofFn]
        omega
    · have hout_ge : 9 ≤ x1.output := by omega
      have hout_lt : x1.output < 9 + x1.gates.length := by omega
      rcases hget : x1.gates[x1.output - 9]? with _ | gout
      · exfalso
        have : x1.output - 9 < x1.gates.length := by omega
        simp [List.getElem?_eq_getElem this] at hget
      · have hmem : gout ∈ x1.gates := List.mem_of_getElem? hget
        rcases (hfan gout hmem).1 with h_and | h_or | h_not_op
        · exact h_ao x1 hfan heval' hout_ge hout_lt gout hget (Or.inl h_and)
        · exact h_ao x1 hfan heval' hout_ge hout_lt gout hget (Or.inr h_or)
        · exact h_not x1 hfan heval' hout_ge hout_lt gout hget h_not_op

end PEqualNP.Outside.R_meta_3438_1
