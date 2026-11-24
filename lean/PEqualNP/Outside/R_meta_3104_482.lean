import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_3104_482
    (saving :
      let uses := fun (C : Circuit) (k : Nat) => (C.gates.filter (fun g =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
          (fun j => decide (j=8 ∨ j=k)))).length
      let h := fun x : Fin 8 → Bool => x 0 || x 3 ||
        (x 1 && x 2) || (x 2 && x 6) || (x 6 && x 4) || (x 4 && x 7) || (x 7 && x 5) || (x 5 && x 1)
      ∀ A B : Circuit, FanInTwo A → FanInTwo B →
        (∀ x, B.eval (A.wires (List.ofFn x ++ [true]) ++ [true]) = h x) →
        10 + uses A 8 + uses B (9+A.size) ≤ A.size+B.size)
    (remaining :
      let uses := fun (C : Circuit) (k : Nat) => (C.gates.filter (fun g =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
          (fun j => decide (j=8 ∨ j=k)))).length
      let f := fun x : Fin 8 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
        (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
      ∀ (A B : Circuit) (k : Nat), FanInTwo A → FanInTwo B → A.size+B.size ≤ 13 →
        uses A 8 + uses B (9+A.size) ≤ 3 →
        let w := fun (b : Bool) (x : Fin 8 → Bool) => A.wires (List.ofFn x ++ [x 1 || b])
        (∀ x, x 1 = true → f x = false → x 3 = true → (w false x).getD k false = false) →
        (∀ x, B.eval (w false x ++ [(w false x).getD k false]) = f x) →
        ∃ x, B.eval (w true x ++ [true]) ≠ (f x || x 0 || x 3)) :
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x2.size + x3.size ≤ (13 : ℕ) →         have x8 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x8 : Bool) (x9 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x9 ++ [x9 (1 : Fin (8 : ℕ)) || x8]);         (∀ (x9 : Fin (8 : ℕ) → Bool), x3.eval (x8 Bool.false x9 ++ [(x8 Bool.false x9).getD x4 Bool.false]) = x1 x9) → ∃ (x10 : Fin (8 : ℕ) → Bool), x3.eval (x8 Bool.true x10 ++ [Bool.true]) ≠ (x1 x10 || x10 (0 : Fin (8 : ℕ)) || x10 (3 : Fin (8 : ℕ))) := by
  let uses := fun (C : Circuit) (k : Nat) => (C.gates.filter (fun g =>
    (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
      (fun j => decide (j=8 ∨ j=k)))).length
  let f := fun x : Fin 8 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
    (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
  let h := fun x : Fin 8 → Bool => x 0 || x 3 ||
    (x 1 && x 2) || (x 2 && x 6) || (x 6 && x 4) || (x 4 && x 7) || (x 7 && x 5) || (x 5 && x 1)
  dsimp only
  intro A B k ha hb size low
  by_contra! high
  let w := fun (b : Bool) (x : Fin 8 → Bool) => A.wires (List.ofFn x ++ [x 1 || b])
  have identityH : ∀ x : Fin 8 → Bool, (f x || x 0 || x 3) = h x := by decide +kernel
  have counted := saving A B ha hb (fun x => by
    have hx := (high x).trans (identityH x)
    simpa only [Bool.or_true] using hx)
  change 10 + uses A 8 + uses B (9+A.size) ≤ A.size+B.size at counted
  have cap : uses A 8 + uses B (9+A.size) ≤ 3 := by omega
  have dead (x : Fin 8 → Bool) (h1 : x 1 = true) (hf : f x = false) (h3 : x 3 = true) :
      (w false x).getD k false = false := by
    have he : w true x = w false x := by simp [w,h1]
    have hlo := low x
    have hhi := high x
    change B.eval (w false x ++ [(w false x).getD k false]) = f x at hlo
    change B.eval (w true x ++ [true]) = (f x || x 0 || x 3) at hhi
    rw [he,hf,h3,Bool.or_true] at hhi
    cases hk : (w false x).getD k false with
    | false => rfl
    | true => rw [hk,hf] at hlo; exact Bool.noConfusion (hlo.symm.trans hhi)
  obtain ⟨x,hx⟩ := remaining A B k ha hb size cap dead low
  exact hx (high x)
