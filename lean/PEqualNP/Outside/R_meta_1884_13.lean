import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1884_13
 (h1 :
  let F := fun x : Fin 10 → Bool => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
  ∀ (C : Circuit) (σ : Fin 10 → Fin 10) (f : Bool → Bool), FanInTwo C →
  (∀ x, C.eval (List.ofFn (x ∘ σ) ++ [f (x 0)]) = F x) → 13 ≤ C.gates.countP (fun g => !(g.op.eval [false]) && decide (1 < g.inputs.toFinset.card)))
 (h2 :
  let F := fun x : Fin 10 → Bool => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
  ∀ (C : Circuit) (σ : Fin 10 → Fin 10) (f : Bool → Bool), FanInTwo C →
  C.size ≤ 18 → 13 ≤ C.gates.countP (fun g => !(g.op.eval [false]) && decide (1 < g.inputs.toFinset.card)) → ∃ x, C.eval (List.ofFn (x ∘ σ) ++ [f (x 0)]) ≠ F x) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Bool → Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x3 (x6 (0 : Fin (10 : ℕ)))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C σ f hC hsize
  by_contra h
  push Not at h
  let F := fun x : Fin 10 → Bool => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
  have agree (x : Fin 10 → Bool) : C.eval (List.ofFn (x ∘ σ) ++ [f (x 0)])=F x := by
    have he := h x
    simp only [F,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] at he ⊢
    convert he using 1
  obtain ⟨x,hx⟩ := h2 C σ f hC hsize (h1 C σ f hC agree)
  exact hx (agree x)
