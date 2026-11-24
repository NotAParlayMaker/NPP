import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4015

-- the edge function of the Petersen graph, as in the statement
def F (x7 : Fin 10 → Bool) : Bool :=
  x7 0 && x7 1 || x7 1 && x7 2 || x7 2 && x7 3 || x7 3 && x7 4 || x7 4 && x7 0 ||
  x7 0 && x7 5 || x7 1 && x7 6 || x7 2 && x7 7 || x7 3 && x7 8 || x7 4 && x7 9 ||
  x7 5 && x7 7 || x7 7 && x7 9 || x7 9 && x7 6 || x7 6 && x7 8 || x7 8 && x7 5

-- a small set that, together with v, holds one edge, and without v holds none
def S (v : Fin 10) : List (Fin 10) :=
  match v with
  | 0 => [2, 5]
  | 1 => [0]
  | 2 => [0, 7]
  | 3 => [4]
  | 4 => [3]
  | 5 => [7]
  | 6 => [1]
  | 7 => [9]
  | 8 => [3]
  | 9 => [4]

def a (v : Fin 10) (i : Fin 10) : Bool := decide (i = v) || decide (i ∈ S v)

def b (v : Fin 10) (i : Fin 10) : Bool := decide (i ∈ S v)

theorem sep : ∀ v : Fin 10, F (a v) ≠ F (b v) ∧ (a v 0 || a v 2) = (b v 0 || b v 2) := by
  decide

theorem agree (v i : Fin 10) (h : i ≠ v) : a v i = b v i := by
  simp [a, b, h]

end PEqualNP.Outside.L_meta_4015

theorem PEqualNP.Outside.L_meta_4015 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ¬Function.Surjective x2 → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C p _ _ hns
  -- some vertex v is never read: the circuit cannot tell a v from b v
  obtain ⟨v, hv⟩ : ∃ v, ∀ i, p i ≠ v := by
    by_contra h
    exact hns fun v => by_contra fun hv => h ⟨v, fun i hi => hv ⟨i, hi⟩⟩
  have hin : List.ofFn (PEqualNP.Outside.L_meta_4015.a v ∘ p) ++ [PEqualNP.Outside.L_meta_4015.a v 0 || PEqualNP.Outside.L_meta_4015.a v 2] = List.ofFn (PEqualNP.Outside.L_meta_4015.b v ∘ p) ++ [PEqualNP.Outside.L_meta_4015.b v 0 || PEqualNP.Outside.L_meta_4015.b v 2] := by
    have hf : PEqualNP.Outside.L_meta_4015.a v ∘ p = PEqualNP.Outside.L_meta_4015.b v ∘ p := funext fun i => PEqualNP.Outside.L_meta_4015.agree v (p i) (hv i)
    rw [hf, (PEqualNP.Outside.L_meta_4015.sep v).2]
  by_cases ha : C.eval (List.ofFn (PEqualNP.Outside.L_meta_4015.a v ∘ p) ++ [PEqualNP.Outside.L_meta_4015.a v 0 || PEqualNP.Outside.L_meta_4015.a v 2]) = PEqualNP.Outside.L_meta_4015.F (PEqualNP.Outside.L_meta_4015.a v)
  · refine ⟨PEqualNP.Outside.L_meta_4015.b v, ?_⟩
    show C.eval (List.ofFn (PEqualNP.Outside.L_meta_4015.b v ∘ p) ++ [PEqualNP.Outside.L_meta_4015.b v 0 || PEqualNP.Outside.L_meta_4015.b v 2]) ≠ PEqualNP.Outside.L_meta_4015.F (PEqualNP.Outside.L_meta_4015.b v)
    rw [← hin, ha]
    exact (PEqualNP.Outside.L_meta_4015.sep v).1
  · exact ⟨PEqualNP.Outside.L_meta_4015.a v, ha⟩
