import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2746

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]
    simp
    omega

lemma run_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false = _
    rw [ih _ (by simp; omega)]
    simp [List.getD, List.getElem?_append_left hi]

def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

lemma singleton_false : ∀ i : Fin 9, target (fun j => decide (j = i)) = false := by
  decide +kernel

end PEqualNP.Outside.L_meta_2746

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2746
theorem PEqualNP.Outside.L_meta_2746 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → (¬∃ (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x5) → (16 : ℕ) ≤ x1.size := by
  intro C _ hfirst hfun hnone
  have hlen : C.gates.length ≤ 1 := by
    cases hgs : C.gates with
    | nil => simp
    | cons a gs =>
      cases gs with
      | nil => simp
      | cons b rest =>
        exact False.elim (hnone ⟨b, by simp [hgs]⟩)
  have computes (x : Fin 9 → Bool) : C.eval (List.ofFn x) = target x :=
    congrFun hfun x
  exfalso
  by_cases hi : C.output < 9
  · let i : Fin 9 := ⟨C.output, hi⟩
    let x : Fin 9 → Bool := fun j => decide (j = i)
    have hinput : C.eval (List.ofFn x) = true := by
      change (run C.gates (List.ofFn x)).getD C.output false = true
      rw [run_input _ _ _ (by simpa using hi)]
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
      simp [x, i]
    have hz := singleton_false i
    have hc := computes x
    rw [hinput] at hc
    exact Bool.false_ne_true (hc.trans hz).symm
  · by_cases hout : C.output = 9
    · let x : Fin 9 → Bool := fun j => decide (j = 4)
      have hv : C.eval (List.ofFn x) = true := by
        change (C.wires (List.ofFn x)).getD C.output false = true
        rw [hout, hfirst]
        decide +kernel
      have hc := computes x
      rw [hv] at hc
      exact Bool.false_ne_true (hc.trans (singleton_false 4)).symm
    · let x : Fin 9 → Bool := fun j => decide (j = 0 ∨ j = 1)
      have hlength : (C.wires (List.ofFn x)).length ≤ 10 := by
        change (run C.gates (List.ofFn x)).length ≤ 10
        rw [run_length]
        simp only [List.length_ofFn]
        omega
      have hv : C.eval (List.ofFn x) = false :=
        List.getD_eq_default _ _ (by omega)
      have ht : target x = true := by decide +kernel
      have hc := computes x
      rw [hv, ht] at hc
      exact Bool.false_ne_true hc