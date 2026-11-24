import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3225_67
    (cut : let r (g : Gate) := (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun i => decide (i=6)); let p (v b : Bool) (x : Fin 8 → Bool) := [x 1,x 0,x 4,x 7,x 5,x 2,v,x 6,x 3,x 1 || b]; ∀ C : Circuit, FanInTwo C → C.size=14 → C.gates.countP r ≤ 1 →
       (∃ g ∈ C.gates, g.op=.or ∧ 6 ∈ g.inputs) → C.output ≠ 6 →
       ∃ (A B : Circuit) (k : Nat), FanInTwo A ∧ FanInTwo B ∧ A.size+B.size=13 ∧
       ∀ (b : Bool) x, let v := A.wires (p false b x)
       C.eval (p b b x) = B.eval (v ++ [b || v.getD k false]))
    (partner : let f (x : Fin 8 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4); let w (A : Circuit) (b : Bool) (x : Fin 8 → Bool) := A.wires [x 1,x 0,x 4,x 7,x 5,x 2,false,x 6,x 3,x 1 || b]; ∀ (A B : Circuit) (k : Nat), FanInTwo A → FanInTwo B → A.size+B.size=13 → (∀ x, B.eval (w A false x ++ [(w A false x).getD k false]) = f x) → (∀ x, B.eval (w A true x ++ [true]) = (f x || x 0 || x 3)) → (∃ x, (w A false x).getD k false = true) ∧ (∀ r ∈ [10,26,74], (w A false (fun i => Nat.testBit r i.val)).getD k false = false) ∧ (k ∈ [1,3,4,5] ∨ (10 ≤ k ∧ k < 10 + A.size)))
    (core : let f (x : Fin 8 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4); let w (A : Circuit) (b : Bool) (x : Fin 8 → Bool) := A.wires [x 1,x 0,x 4,x 7,x 5,x 2,false,x 6,x 3,x 1 || b]; ∀ (A B : Circuit) (k : Nat), FanInTwo A → FanInTwo B → A.size+B.size=13 → (∃ x, (w A false x).getD k false = true) → (∀ r ∈ [10,26,74], (w A false (fun i => Nat.testBit r i.val)).getD k false = false) → (k ∈ [1,3,4,5] ∨ (10 ≤ k ∧ k < 10 + A.size)) → (∀ x, B.eval (w A false x ++ [(w A false x).getD k false]) = f x) → ∃ x, B.eval (w A true x ++ [true]) ≠ (f x || x 0 || x 3))
    : have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (14 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∃ x8 ∈ x4.gates, x8.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (6 : ℕ) ∈ x8.inputs) → (∀ (x9 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x9) = x3 x9) → ∃ (x10 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x10) ≠ (x3 x10 || x10 (0 : Fin (8 : ℕ)) || x10 (3 : Fin (8 : ℕ))) := by
  intro r p f C hf size readers has low
  by_contra! high
  have keep (gs : List Gate) (v : List Bool) (j : Nat) (hj : j < v.length) :
      (gs.foldl (fun u (g : Gate) => u ++ [g.op.eval (g.inputs.map (fun i => u.getD i false))]) v).getD j false = v.getD j false := by
    induction gs generalizing v with
    | nil => rfl
    | cons g gs ih => rw [List.foldl_cons,ih _ (by simp;omega), List.getD_append _ _ _ _ hj]
  have out : C.output ≠ 6 := by
    intro e; let x : Fin 8 → Bool := fun _ => true
    have h := low x
    change (C.gates.foldl _ (p false x)).getD C.output false = _ at h
    rw [e,keep _ _ _ (by decide : 6 < (p false x).length)] at h
    exact (by decide : (p false x).getD 6 false ≠ f x) h
  obtain ⟨A,B,k,ha,hb,sz,agree⟩ := cut C hf size readers has out
  let w (b : Bool) (x : Fin 8 → Bool) := A.wires [x 1,x 0,x 4,x 7,x 5,x 2,false,x 6,x 3,x 1 || b]
  have lo (x : Fin 8 → Bool) : B.eval (w false x ++ [(w false x).getD k false]) = f x := (agree false x).symm.trans (low x)
  have hi (x : Fin 8 → Bool) : B.eval (w true x ++ [true]) = (f x || x 0 || x 3) := (agree true x).symm.trans (high x)
  obtain ⟨yes,no,pos⟩ := partner A B k ha hb sz lo hi
  obtain ⟨x,hx⟩ := core A B k ha hb sz yes no pos lo
  exact hx (hi x)
