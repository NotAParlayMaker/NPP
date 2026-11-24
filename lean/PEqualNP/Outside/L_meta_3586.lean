import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3586
open PEqualNP.CircuitLowerBounds

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

def fl (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [F w g]) w

theorem fl_cons (F : List Bool → Gate → Bool) (g : Gate) (gs : List Gate) (w : List Bool) :
    fl F (g :: gs) w = fl F gs (w ++ [F w g]) := rfl

theorem fl_keep (F : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (fl F gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [fl_cons, ih _ _ (by simp; omega), List.getD_append _ _ _ _ hi]

def EV (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem clip (l : List Bool) (hl : l.length = 10) (a : ℕ) :
    l.getD (min a 10) false = l.getD a false := by
  by_cases h : a < 10
  · rw [Nat.min_eq_left (le_of_lt h)]
  · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by omega)]

theorem or2 (ins : List ℕ) (h : ins.length ≤ 2) :
    ∃ p q : Fin 11, ∀ l : List Bool, l.length = 10 →
      GateOp.or.eval (ins.map fun i => l.getD i false) = (l.getD p.1 false || l.getD q.1 false) := by
  match ins, h with
  | [], _ =>
    refine ⟨⟨10, by omega⟩, ⟨10, by omega⟩, ?_⟩
    intro l hl
    have h10 : l.getD 10 false = false := List.getD_eq_default _ _ (by omega)
    show GateOp.or.eval [] = (l.getD 10 false || l.getD 10 false)
    rw [h10]; rfl
  | [a], _ =>
    refine ⟨⟨min a 10, by omega⟩, ⟨min a 10, by omega⟩, ?_⟩
    intro l hl
    show GateOp.or.eval [l.getD a false] = (l.getD (min a 10) false || l.getD (min a 10) false)
    rw [clip l hl a]
    simp [GateOp.eval]
  | [a, b], _ =>
    refine ⟨⟨min a 10, by omega⟩, ⟨min b 10, by omega⟩, ?_⟩
    intro l hl
    show GateOp.or.eval [l.getD a false, l.getD b false]
      = (l.getD (min a 10) false || l.getD (min b 10) false)
    rw [clip l hl a, clip l hl b]
    simp [GateOp.eval]
  | _ :: _ :: _ :: _, h => exact absurd h (by simp)

theorem snoc9 (X : List Bool) (v : Bool) (h : X.length = 9) : (X ++ [v]).getD 9 false = v := by
  rw [← h]; exact getD_snoc_eq X v

end PEqualNP.Outside.L_meta_3586

open PEqualNP.Outside.L_meta_3586 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3586 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) →       Option.map PEqualNP.CircuitLowerBounds.Gate.op x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or →         ∃ (x5 : Fin (11 : ℕ)) (x6 : Fin (11 : ℕ)) (x7 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x7 ∧             x7.size + (2 : ℕ) = x1.size ∧               ∀ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))];                 x7.eval (x9 ++ [x9.getD (↑x5) Bool.false || x9.getD (↑x6) Bool.false]) = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 x8 := by
  intro C hF h9 h1
  rcases hg : C.gates with _ | ⟨g0, _ | ⟨g1, rest⟩⟩
  · rw [hg] at h1; simp at h1
  · rw [hg] at h1; simp at h1
  · rw [hg] at h1
    have hop : g1.op = GateOp.or := by simpa using h1
    have hlen : g1.inputs.length ≤ 2 := (hF g1 (by rw [hg]; simp)).2
    obtain ⟨p, q, hpq⟩ := or2 g1.inputs hlen
    refine ⟨p, q, ⟨rest, C.output⟩, ?_, ?_, ?_⟩
    · intro g hg'
      exact hF g (by rw [hg]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg'))
    · show rest.length + 2 = C.gates.length
      rw [hg]; rfl
    · intro x
      have hX : (List.ofFn x).length = 9 := by simp
      have e0 : EV (List.ofFn x) g0 = (x 0 || x 4) := by
        have h := h9 x
        change (fl EV C.gates (List.ofFn x)).getD 9 false = _ at h
        rw [hg, fl_cons, fl_keep _ _ _ _ (by simp), snoc9 _ _ hX] at h
        exact h
      have e1 : EV (List.ofFn x ++ [x 0 || x 4]) g1
          = ((List.ofFn x ++ [x 0 || x 4]).getD p.1 false || (List.ofFn x ++ [x 0 || x 4]).getD q.1 false) := by
        unfold EV
        rw [hop]
        exact hpq _ (by simp)
      show (fl EV rest (_ ++ [_])).getD C.output false = (fl EV C.gates (List.ofFn x)).getD C.output false
      rw [hg, fl_cons, fl_cons, e0, e1]
