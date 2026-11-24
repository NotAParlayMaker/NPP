import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_1890_302
    (h1 : let F := fun x : Fin 10 → Bool => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any (fun e => x (Fin.ofNat 10 (e/10)) && x (Fin.ofNat 10 (e%10)));
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin 10 → Fin 10), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 18 →
      (∀ x, C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) = F x) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ 18 ∧ (∀ r : Fin 10, r=0 ∨ r=2 → (D.gates.filter fun g => g.inputs.any (fun i => ((i == r.val) || (i == 10)) && (g.op.eval [true] || (g.inputs.head? == some i)))).length ≤ 3) ∧
      ∀ x, D.eval (List.ofFn x ++ [x 0 && x 2]) = F x)
    (h2 : let F := fun x : Fin 10 → Bool => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any (fun e => x (Fin.ofNat 10 (e/10)) && x (Fin.ofNat 10 (e%10)));
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 18 → (∀ r : Fin 10, r=0 ∨ r=2 → (D.gates.filter fun g => g.inputs.any (fun i => ((i == r.val) || (i == 10)) && (g.op.eval [true] || (g.inputs.head? == some i)))).length ≤ 3) →
      ∃ x, D.eval (List.ofFn x ++ [x 0 && x 2]) ≠ F x) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  intro C p hf hs
  by_contra! h
  let F := fun x : Fin 10 → Bool => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any (fun e => x (Fin.ofNat 10 (e/10)) && x (Fin.ofNat 10 (e%10)));
  have correct : ∀ x : Fin 10 → Bool, (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x = F x := by decide +kernel
  obtain ⟨D, hd, hl, hr, he⟩ := h1 C p hf hs (fun x => (h x).trans (correct x))
  obtain ⟨x,hx⟩ := h2 D hd hl hr
  exact hx (he x)
