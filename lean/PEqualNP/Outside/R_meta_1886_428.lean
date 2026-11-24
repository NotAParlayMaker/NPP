import PEqualNP.Defs

-- SPDX-License-Identifier: Apache-2.0
-- Author: WH3EL5
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1886_428
    (minor : let ev := fun (es : List ℕ) (x : ℕ → Bool) => es.any (fun e => x (e / 10) && x (e % 10))
let cost := fun (D : Circuit) => D.gates.countP (fun g => !(g.op.eval [false]))
∀ (C : Circuit) (σ : Fin 10 → Fin 10) (b : Bool), FanInTwo C →
let readers := fun (v : Fin 10) => C.gates.countP (fun g =>
        (if g.op.eval [false] then g.inputs.take 1 else g.inputs).any (fun i =>
          (decide (i<10) && decide (σ (Fin.ofNat 10 i)=v)) || (b && decide (i=10))))
(∀ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ σ) ++ [if b=true then x 0 && x 1 else x 0 || x 1]) = ev [1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] (x ∘ Fin.ofNat 10)) → ∀ v : Fin 10,v.val≤1 → ∃ D : Circuit, FanInTwo D ∧ (∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = ev [1,12,23,34,40,5,16,27,38,57,68,85] (y ∘ Fin.ofNat 9)) ∧ D.size+max 1 (readers v) ≤ C.size ∧ cost D < cost C)
    (baseline : let ev := fun (es : List ℕ) (x : ℕ → Bool) => es.any (fun e => x (e / 10) && x (e % 10))
∀ D : Circuit,FanInTwo D → (∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = ev [1,12,23,34,40,5,16,27,38,57,68,85] (y ∘ Fin.ofNat 9)) → 15 ≤ D.size)
    (binary : let ev := fun (es : List ℕ) (x : ℕ → Bool) => es.any (fun e => x (e / 10) && x (e % 10))
let cost := fun (D : Circuit) => D.gates.countP (fun g => !(g.op.eval [false]))
∀ D : Circuit,FanInTwo D → (∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = ev [1,12,23,34,40,5,16,27,38,57,68,85] (y ∘ Fin.ofNat 9)) → 13 ≤ cost D)
    (residual : let ev := fun (es : List ℕ) (x : ℕ → Bool) => es.any (fun e => x (e / 10) && x (e % 10))
let cost := fun (D : Circuit) => D.gates.countP (fun g => !(g.op.eval [false]))
∀ (C : Circuit) (σ : Fin 10 → Fin 10) (b : Bool), FanInTwo C →
let readers := fun (v : Fin 10) => C.gates.countP (fun g =>
        (if g.op.eval [false] then g.inputs.take 1 else g.inputs).any (fun i =>
          (decide (i<10) && decide (σ (Fin.ofNat 10 i)=v)) || (b && decide (i=10))))
16 ≤ C.size → C.size ≤ 18 → 14 ≤ cost C → (∀ v : Fin 10,v.val≤1 → 15 + readers v ≤ C.size) → ¬ (∀ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ σ) ++ [if b=true then x 0 && x 1 else x 0 || x 1]) = ev [1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] (x ∘ Fin.ofNat 10)))
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [if x3 = Bool.true then x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) else x6 (0 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C σ b fan hs
  by_contra! agrees
  let ev := fun (es : List ℕ) (x : ℕ → Bool) => es.any (fun e => x (e / 10) && x (e % 10))
  have same : ∀ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ σ) ++ [if b=true then x 0 && x 1 else x 0 || x 1]) = ev [1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] (x ∘ Fin.ofNat 10) := by
    intro x
    apply (agrees x).trans
    simp only [ev,List.any_cons,List.any_nil,Bool.or_false,Function.comp_apply,Bool.or_assoc]
    rfl
  let use := fun (v : Fin 10) => C.gates.countP (fun g =>
    (if g.op.eval [false] then g.inputs.take 1 else g.inputs).any (fun i =>
      (decide (i<10) && decide (σ (Fin.ofNat 10 i)=v)) || (b && decide (i=10))))
  have bound (v : Fin 10) (small : v.val≤1) :
      15 + max 1 (use v) ≤ C.size ∧ 14 ≤ C.gates.countP (fun g => !(g.op.eval [false])) := by
    obtain ⟨D,fd,yd,sd,cd⟩ := minor C σ b fan same v small
    have total := baseline D fd yd
    have gates := binary D fd yd
    change D.size+max 1 (use v)≤C.size at sd
    dsimp only at gates cd
    exact ⟨by omega,by omega⟩
  have h := bound 0 (by decide)
  apply residual C σ b fan (by omega) hs h.2 _ same
  intro v hv
  exact le_trans (Nat.add_le_add_left (Nat.le_max_right _ _) _) (bound v hv).1
