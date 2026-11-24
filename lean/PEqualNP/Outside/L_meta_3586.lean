import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3586

open PEqualNP.CircuitLowerBounds

lemma getD_foldl_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_min (w : List Bool) (hw : w.length = 10) (a : ℕ) :
    w.getD (min a 10) false = w.getD a false := by
  rcases Nat.lt_or_ge a 10 with h | h
  · rw [Nat.min_eq_left (Nat.le_of_lt h)]
  · rw [Nat.min_eq_right h, List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by omega)]

lemma min_lt (a : ℕ) : min a 10 < 11 := Nat.lt_succ_of_le (Nat.min_le_right a 10)

lemma getD_min' (w : List Bool) (hw : w.length = 10) (a : ℕ) :
    w[min a 10]?.getD false = w[a]?.getD false := by
  simpa [List.getD_eq_getElem?_getD] using getD_min w hw a

lemma or_inputs (l : List ℕ) (hl : l.length ≤ 2) :
    ∃ a b : Fin 11, ∀ w : List Bool, w.length = 10 →
      (w.getD (↑a) false || w.getD (↑b) false)
        = GateOp.or.eval (l.map fun i => w.getD i false) := by
  match l, hl with
  | [], _ =>
    refine ⟨⟨10, by omega⟩, ⟨10, by omega⟩, fun w hw => ?_⟩
    simp [GateOp.eval, List.getElem?_eq_none (Nat.le_of_eq hw)]
  | [a], _ =>
    refine ⟨⟨min a 10, min_lt a⟩, ⟨min a 10, min_lt a⟩, fun w hw => ?_⟩
    simp [GateOp.eval, getD_min' w hw]
  | [a, b], _ =>
    refine ⟨⟨min a 10, min_lt a⟩, ⟨min b 10, min_lt b⟩, fun w hw => ?_⟩
    simp [GateOp.eval, getD_min' w hw]
  | _ :: _ :: _ :: _, h => exact absurd h (by simp)

end PEqualNP.Outside.L_meta_3586

theorem PEqualNP.Outside.L_meta_3586 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) →       Option.map PEqualNP.CircuitLowerBounds.Gate.op x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or →         ∃ (x5 : Fin (11 : ℕ)) (x6 : Fin (11 : ℕ)) (x7 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x7 ∧             x7.size + (2 : ℕ) = x1.size ∧               ∀ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))];                 x7.eval (x9 ++ [x9.getD (↑x5) Bool.false || x9.getD (↑x6) Bool.false]) = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 x8 := by
  intro x1 hF h9 h1
  obtain ⟨gates, out⟩ := x1
  match gates, hF, h9, h1 with
  | [], _, _, h1 => simp at h1
  | [_], _, _, h1 => simp at h1
  | g0 :: g1 :: rest, hF, h9, h1 =>
    have hop : g1.op = PEqualNP.CircuitLowerBounds.GateOp.or := by simpa using h1
    have hlen : g1.inputs.length ≤ 2 := (hF g1 (by simp)).2
    obtain ⟨a, b, hab⟩ := PEqualNP.Outside.L_meta_3586.or_inputs g1.inputs hlen
    have hv0 : ∀ x : Fin 9 → Bool,
        g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 4) := by
      intro x
      have h := h9 x
      simp only [PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons] at h
      rw [PEqualNP.Outside.L_meta_3586.getD_foldl_prefix _ _ 9 (by simp)] at h
      simpa [List.getD_eq_getElem?_getD] using h
    refine ⟨a, b, ⟨rest, out⟩, ?_, ?_, ?_⟩
    · intro g hg
      exact hF g (by simp [hg])
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    · intro x8
      show PEqualNP.CircuitLowerBounds.Circuit.eval ⟨rest, out⟩
          ((List.ofFn x8 ++ [x8 0 || x8 4]) ++
            [(List.ofFn x8 ++ [x8 0 || x8 4]).getD (↑a) false ||
              (List.ofFn x8 ++ [x8 0 || x8 4]).getD (↑b) false])
          = PEqualNP.MetaComplexity.circuitFun 9 ⟨g0 :: g1 :: rest, out⟩ x8
      simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons]
      rw [hv0 x8, hop, hab _ (by simp)]
