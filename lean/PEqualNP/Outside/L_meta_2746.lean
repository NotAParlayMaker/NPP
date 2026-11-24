import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2746

open PEqualNP.CircuitLowerBounds

-- The wire-list invariant is adapted from this project's Shannon helper.

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

def edge : (Fin 9 → Bool) → Bool :=
  fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))

def singleton (i : Fin 9) (x : Fin 9) : Bool := decide (x = i)

def pair01 (x : Fin 9) : Bool := decide (x = 0 ∨ x = 1)

lemma edge_single (i : Fin 9) : edge (singleton i) = false := by
  fin_cases i <;> decide

lemma edge_pair : edge pair01 = true := by decide

lemma no_second (C : Circuit)
    (h : ¬∃ g : Gate, C.gates[1]? = some g) : C.gates.length ≤ 1 := by
  by_contra! hl
  exact h ⟨C.gates[1], List.getElem?_eq_getElem hl⟩

lemma impossible (C : Circuit)
    (hfirst : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6))
    (hev : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edge x)
    (hno : ¬∃ g : Gate, C.gates[1]? = some g) : False := by
  have hsmall := no_second C hno
  rcases Nat.lt_trichotomy C.output 9 with h | h | h
  · let i : Fin 9 := ⟨C.output, h⟩
    have e := hev (singleton i)
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix C.gates (List.ofFn (singleton i))
    change (C.wires (List.ofFn (singleton i))).getD C.output false = edge (singleton i) at e
    rw [wires_eq, ht, List.getD_append _ _ _ _ (by simpa using h), edge_single] at e
    rw [List.getD_eq_getElem _ _ (by simpa using h)] at e
    rw [List.getElem_ofFn] at e
    change singleton i i = false at e
    simp [singleton] at e
  · have e := hev (singleton 4)
    change (C.wires (List.ofFn (singleton 4))).getD C.output false = edge (singleton 4) at e
    rw [h, hfirst, edge_single] at e
    simp [singleton] at e
  · have e := hev pair01
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix C.gates (List.ofFn pair01)
    change (C.wires (List.ofFn pair01)).getD C.output false = edge pair01 at e
    rw [wires_eq, ht, List.getD_eq_default _ _ (by simp [htl]; omega), edge_pair] at e
    cases e

end PEqualNP.Outside.L_meta_2746

theorem PEqualNP.Outside.L_meta_2746 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 →
    (∀ (x3 : Fin (9 : ℕ) →
    Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) →
    (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) →
    Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → (¬∃ (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x5) → (16 : ℕ) ≤ x1.size := by
  intro C _ hfirst heval hno
  exact (PEqualNP.Outside.L_meta_2746.impossible C hfirst (congrFun heval) hno).elim
