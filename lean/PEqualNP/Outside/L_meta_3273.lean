import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_2756
import PEqualNP.Outside.L_meta_2913

namespace PEqualNP.Outside.L_meta_3273

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The Petersen graph minus a vertex, as an edge function on nine bits.
-- Step via the proved OR-pin lemma (L_meta_2756): a fan-in-two circuit of at most
-- thirteen gates never computes the edge function when the last input wire is an
-- OR of at most one wire of w.
theorem or_step (pins : List ℕ) (hp : pins.length ≤ 1) (C : Circuit)
    (hf : FanInTwo C) (hs : C.size ≤ 13) :
    ∃ x : Fin (9 : ℕ) → Bool,
      have w : List Bool := List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]
      C.eval (w ++ [GateOp.or.eval (List.map (fun j => w.getD j Bool.false) pins)]) ≠
        (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))) :=
  PEqualNP.Outside.L_meta_2756 pins (by omega) (Or.inl hp) C hf hs

-- Step via the proved NOT-pin lemma (L_meta_2913): same, with the last wire a NOT
-- of no wires, that is the constant true.
theorem not_step (C : Circuit) (hf : FanInTwo C) (hs : C.size ≤ 13) :
    ∃ x : Fin (9 : ℕ) → Bool,
      have w : List Bool := List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]
      C.eval (w ++ [GateOp.not.eval (List.map (fun j => w.getD j Bool.false) [])]) ≠
        (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))) :=
  PEqualNP.Outside.L_meta_2913 [] (by simp) (Or.inl rfl) C hf hs

-- Bridge: rewrite the literal last wire t ab.1 && t ab.2 into the OR of pins.
theorem apply_or (ab : Fin (12 : ℕ) × Fin (12 : ℕ)) (pins : List ℕ) (hp : pins.length ≤ 1)
    (hlast : ∀ x : Fin (9 : ℕ) → Bool,
      ((if ab.1 = (11 : Fin (12 : ℕ)) then Bool.true else (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD (↑ab.1) Bool.false) &&
      (if ab.2 = (11 : Fin (12 : ℕ)) then Bool.true else (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD (↑ab.2) Bool.false)) =
      GateOp.or.eval (List.map (fun j => (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD j Bool.false) pins))
    (C : Circuit) (hf : FanInTwo C) (hs : C.size ≤ 13) :
    ∃ x : Fin (9 : ℕ) → Bool,
      C.eval ((List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]) ++ [((if ab.1 = (11 : Fin (12 : ℕ)) then Bool.true else (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD (↑ab.1) Bool.false) &&
      (if ab.2 = (11 : Fin (12 : ℕ)) then Bool.true else (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD (↑ab.2) Bool.false))]) ≠
        (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))) := by
  obtain ⟨x, hx⟩ := or_step pins hp C hf hs
  exact ⟨x, by rw [hlast x]; exact hx⟩

-- Bridge: rewrite the literal last wire into the NOT of no wires.
theorem apply_not (ab : Fin (12 : ℕ) × Fin (12 : ℕ))
    (hlast : ∀ x : Fin (9 : ℕ) → Bool,
      ((if ab.1 = (11 : Fin (12 : ℕ)) then Bool.true else (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD (↑ab.1) Bool.false) &&
      (if ab.2 = (11 : Fin (12 : ℕ)) then Bool.true else (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD (↑ab.2) Bool.false)) =
      GateOp.not.eval (List.map (fun j => (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD j Bool.false) []))
    (C : Circuit) (hf : FanInTwo C) (hs : C.size ≤ 13) :
    ∃ x : Fin (9 : ℕ) → Bool,
      C.eval ((List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]) ++ [((if ab.1 = (11 : Fin (12 : ℕ)) then Bool.true else (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD (↑ab.1) Bool.false) &&
      (if ab.2 = (11 : Fin (12 : ℕ)) then Bool.true else (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD (↑ab.2) Bool.false))]) ≠
        (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))) := by
  obtain ⟨x, hx⟩ := not_step C hf hs
  exact ⟨x, by rw [hlast x]; exact hx⟩

-- The last wire for a literal self-pair at i ≠ 11 is the wire value itself.
theorem hlast_or (i : Fin (12 : ℕ)) (hne : i ≠ (11 : Fin (12 : ℕ))) (x : Fin (9 : ℕ) → Bool) :
    ((if i = (11 : Fin (12 : ℕ)) then Bool.true else (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD (↑i) Bool.false) &&
     (if i = (11 : Fin (12 : ℕ)) then Bool.true else (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD (↑i) Bool.false)) =
    GateOp.or.eval (List.map (fun j => (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD j Bool.false) [↑i]) := by
  rw [ite_eq_right hne]
  simp [GateOp.eval]

-- The last wire for the self-pair at 10 is false, the OR of no wires.
theorem hlast_ten (x : Fin (9 : ℕ) → Bool) :
    ((if (10 : Fin (12 : ℕ)) = (11 : Fin (12 : ℕ)) then Bool.true else (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD (↑(10 : Fin (12 : ℕ))) Bool.false) &&
     (if (10 : Fin (12 : ℕ)) = (11 : Fin (12 : ℕ)) then Bool.true else (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD (↑(10 : Fin (12 : ℕ))) Bool.false)) =
    GateOp.or.eval (List.map (fun j => (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD j Bool.false) []) := by
  have hne : (10 : Fin (12 : ℕ)) ≠ (11 : Fin (12 : ℕ)) := by decide
  rw [ite_eq_right hne]
  show ((List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD 10 Bool.false && (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD 10 Bool.false) = Bool.false
  have hA : (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD 10 Bool.false = Bool.false := List.getD_eq_default _ _ (by simp)
  rw [hA]
  rfl

-- The last wire for the self-pair at 11 is true, the NOT of no wires.
theorem hlast_eleven (x : Fin (9 : ℕ) → Bool) :
    ((if (11 : Fin (12 : ℕ)) = (11 : Fin (12 : ℕ)) then Bool.true else (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD (↑(11 : Fin (12 : ℕ))) Bool.false) &&
     (if (11 : Fin (12 : ℕ)) = (11 : Fin (12 : ℕ)) then Bool.true else (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD (↑(11 : Fin (12 : ℕ))) Bool.false)) =
    GateOp.not.eval (List.map (fun j => (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD j Bool.false) []) := by
  rw [ite_eq_left rfl]
  rfl

end PEqualNP.Outside.L_meta_3273

theorem PEqualNP.Outside.L_meta_3273 : ∀ x1 ∈ [((0 : Fin (12 : ℕ)), (0 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (1 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (2 : Fin (12 : ℕ))), ((3 : Fin (12 : ℕ)), (3 : Fin (12 : ℕ))), ((4 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((6 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((9 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((10 : Fin (12 : ℕ)), (10 : Fin (12 : ℕ))), ((11 : Fin (12 : ℕ)), (11 : Fin (12 : ℕ)))],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];           have x8 : Fin (12 : ℕ) → Bool := fun (x8 : Fin (12 : ℕ)) => if x8 = (11 : Fin (12 : ℕ)) then Bool.true else x7.getD (↑x8) Bool.false;           x3.eval (x7 ++ [x8 x1.1 && x8 x1.2]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 hx1 x3 hfan hsize
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx1
  rcases hx1 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact PEqualNP.Outside.L_meta_3273.apply_or ((0 : Fin (12 : ℕ)), (0 : Fin (12 : ℕ))) [0] (by simp) (fun x => PEqualNP.Outside.L_meta_3273.hlast_or 0 (by decide) x) x3 hfan hsize
  · exact PEqualNP.Outside.L_meta_3273.apply_or ((1 : Fin (12 : ℕ)), (1 : Fin (12 : ℕ))) [1] (by simp) (fun x => PEqualNP.Outside.L_meta_3273.hlast_or 1 (by decide) x) x3 hfan hsize
  · exact PEqualNP.Outside.L_meta_3273.apply_or ((2 : Fin (12 : ℕ)), (2 : Fin (12 : ℕ))) [2] (by simp) (fun x => PEqualNP.Outside.L_meta_3273.hlast_or 2 (by decide) x) x3 hfan hsize
  · exact PEqualNP.Outside.L_meta_3273.apply_or ((3 : Fin (12 : ℕ)), (3 : Fin (12 : ℕ))) [3] (by simp) (fun x => PEqualNP.Outside.L_meta_3273.hlast_or 3 (by decide) x) x3 hfan hsize
  · exact PEqualNP.Outside.L_meta_3273.apply_or ((4 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))) [4] (by simp) (fun x => PEqualNP.Outside.L_meta_3273.hlast_or 4 (by decide) x) x3 hfan hsize
  · exact PEqualNP.Outside.L_meta_3273.apply_or ((6 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))) [6] (by simp) (fun x => PEqualNP.Outside.L_meta_3273.hlast_or 6 (by decide) x) x3 hfan hsize
  · exact PEqualNP.Outside.L_meta_3273.apply_or ((9 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))) [9] (by simp) (fun x => PEqualNP.Outside.L_meta_3273.hlast_or 9 (by decide) x) x3 hfan hsize
  · exact PEqualNP.Outside.L_meta_3273.apply_or ((10 : Fin (12 : ℕ)), (10 : Fin (12 : ℕ))) [] (by simp) PEqualNP.Outside.L_meta_3273.hlast_ten x3 hfan hsize
  · exact PEqualNP.Outside.L_meta_3273.apply_not ((11 : Fin (12 : ℕ)), (11 : Fin (12 : ℕ))) PEqualNP.Outside.L_meta_3273.hlast_eleven x3 hfan hsize
