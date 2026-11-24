import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3586_aux

def boundedPin (i : ℕ) : Fin 11 := ⟨min i 10, by omega⟩

lemma readPin (w : List Bool) (len : w.length = 10) (i : ℕ) :
    w.getD (boundedPin i).val false = w.getD i false := by
  by_cases hi : i ≤ 10
  · simp [boundedPin, Nat.min_eq_left hi]
  · simp only [boundedPin, Nat.min_eq_right (by omega : 10 ≤ i)]
    rw [List.getD_eq_default _ _ (by omega : w.length ≤ 10),
        List.getD_eq_default _ _ (by omega : w.length ≤ i)]

lemma twoPins (ins : List ℕ) (h : ins.length ≤ 2) :
    ∃ a b : Fin 11, ∀ w : List Bool, w.length = 10 →
      GateOp.or.eval (ins.map fun i => w.getD i false) =
        (w.getD a.val false || w.getD b.val false) := by
  cases ins with
  | nil =>
    refine ⟨10, 10, ?_⟩
    intro w hw
    have off : w.getD 10 false = false := List.getD_eq_default _ _ (by omega)
    change false = (w.getD 10 false || w.getD 10 false)
    rw [off]
    rfl
  | cons i more =>
    cases more with
    | nil =>
      refine ⟨boundedPin i, boundedPin i, ?_⟩
      intro w hw
      rw [readPin w hw]
      simp [GateOp.eval]
    | cons j rest =>
      have hempty : rest = [] := by simpa using h
      subst rest
      refine ⟨boundedPin i, boundedPin j, ?_⟩
      intro w hw
      rw [readPin w hw, readPin w hw]
      simp [GateOp.eval]

def pushGate (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma stable (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl pushGate w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g rest ih =>
    rw [List.foldl_cons, ih]
    · simp [pushGate, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    · simp [pushGate]
      omega

end PEqualNP.Outside.L_meta_3586_aux

open PEqualNP.Outside.L_meta_3586_aux

-- The argument for the first two gates follows the checked reduction R_meta_2527_513.
theorem PEqualNP.Outside.L_meta_3586 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) →       Option.map PEqualNP.CircuitLowerBounds.Gate.op x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or →         ∃ (x5 : Fin (11 : ℕ)) (x6 : Fin (11 : ℕ)) (x7 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x7 ∧             x7.size + (2 : ℕ) = x1.size ∧               ∀ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))];                 x7.eval (x9 ++ [x9.getD (↑x5) Bool.false || x9.getD (↑x6) Bool.false]) = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 x8 := by
  rintro ⟨gates, output⟩ fan first second
  rcases gates with _ | ⟨g, _ | ⟨h, tail⟩⟩
  · cases second
  · cases second
  have hop : h.op = GateOp.or := Option.some.inj second
  obtain ⟨a,b,pins⟩ := twoPins h.inputs (fan h (by simp)).2
  refine ⟨a, b, ⟨tail, output⟩, ?_, ?_, ?_⟩
  · intro gate member
    exact fan gate (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  · simp [Circuit.size]
  · intro x
    let w := List.ofFn x ++ [x 0 || x 4]
    have aligned : pushGate (List.ofFn x) g = w := by
      have e := first x
      change ((h :: tail).foldl pushGate (pushGate (List.ofFn x) g)).getD 9 false = _ at e
      rw [stable _ _ _ (by simp [pushGate])] at e
      change (List.ofFn x ++ [_]).getD 9 false = _ at e
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)] at e
      simpa [w, pushGate] using congrArg (fun v => List.ofFn x ++ [v]) e
    change (tail.foldl pushGate (w ++ [_])).getD output false =
      (tail.foldl pushGate (pushGate (pushGate (List.ofFn x) g) h)).getD output false
    rw [aligned]
    simp only [pushGate, hop, pins w (by simp [w])]
    rfl

