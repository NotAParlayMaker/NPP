import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem PEqualNP.Outside.R_meta_4817_327
  (rep : let F := fun (x : Fin 10 → Bool) => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))
    let B := fun (r : Fin 12) (x : Fin 10 → Bool) => let v := List.ofFn x ++ [x 0 && x 2]; v ++ [!v.getD r.val false]
    ∀ t∈([0,1,3,6,8,10] : List (Fin 12)), ∀ D : Circuit, FanInTwo D → D.size≤17 → ∃ x, D.eval (B t x) ≠ F x)
  (geo : let F := fun (x : Fin 10 → Bool) => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))
    let B := fun (r : Fin 12) (x : Fin 10 → Bool) => let v := List.ofFn x ++ [x 0 && x 2]; v ++ [!v.getD r.val false]
    ∀ r : Fin 12, ∃ t∈([0,1,3,6,8,10] : List (Fin 12)), ∃ (f : Fin 10 → Fin 10) (I : List Nat), (∀ i∈I,i≤12) ∧ ∀ x, F (x ∘ f) = F x ∧ B r (x ∘ f) = I.map (fun i => if i=12 then true else (B t x).getD i false))
  (route : ∀ (I : List Nat) (C : Circuit), (∀ i∈I,i≤12) → FanInTwo C →
    ∃ (b : Option Bool) (D : Circuit), FanInTwo D ∧ D.size≤C.size ∧ ∀ w : List Bool, w.length=12 →
      b.getD (D.eval w) = C.eval (I.map (fun i => if i=12 then true else w.getD i false))) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (12 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       ∃ (x5 : Fin (10 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))];         x1.eval (x6 ++ [!x6.getD (↑x2) Bool.false]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x5 := by
  classical
  let F := fun (x : Fin 10 → Bool) => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))
  let B := fun (r : Fin 12) (x : Fin 10 → Bool) => let v := List.ofFn x ++ [x 0 && x 2]; v ++ [!v.getD r.val false]
  have low : F (fun _ => false) = false := by decide
  have high : F (fun _ => true) = true := by decide
  intro C r legal cap
  by_contra no
  push_neg at no
  have computes (x : Fin 10 → Bool) : C.eval (B r x) = F x := by
    have e := not_not.mp (no x)
    apply e.trans
    change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 4 && x 9) || ((x 5 && x 7) || ((x 7 && x 9) || ((x 9 && x 6) || ((x 6 && x 8) || ((x 8 && x 5) || false)))))))))))))))
    simp only [Bool.or_false,Bool.or_assoc]
  obtain ⟨t,tok,f,I,small,perm⟩ := geo r
  obtain ⟨o,D,good,bound,eval⟩ := route I C small legal
  have matchF (x : Fin 10 → Bool) : o.getD (D.eval (B t x)) = F x := by
    have he := perm x
    change F (x ∘ f)=F x ∧ B r (x ∘ f) = _ at he
    rw [eval _ (by simp [B]),←he.2,computes,he.1]
  cases o with
  | none =>
    obtain ⟨x,bad⟩ := rep t tok D good (bound.trans cap)
    exact bad (matchF x)
  | some b =>
    have h0 := matchF (fun _ => false)
    have h1 := matchF (fun _ => true)
    rw [low] at h0
    rw [high] at h1
    exact Bool.noConfusion (h0.symm.trans h1)
