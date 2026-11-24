import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_3590_427
    (pin : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (a : Fin 11) (f : (Fin 9 → Bool) → Bool), PEqualNP.MetaComplexity.FanInTwo D →
      (∀ x : Fin 9 → Bool, let w := List.ofFn x ++ [x 0 || x 4]
        D.eval (w ++ [w.getD a false]) = f x) →
      (∃ x : Fin 9 → Bool, x 0 = true ∧ x 4 = false ∧ f x ≠ f (Function.update x 4 true)) →
      let g := fun y : Fin 8 → Bool => f ![y 0,y 1,y 2,y 3,false,y 4,y 5,y 6,y 7]
      (∃ y z, g y ≠ g z) → PEqualNP.MetaComplexity.HasCircuitSize 8 g (D.size-1))
    (minorFour : ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (remaining : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin 10), PEqualNP.MetaComplexity.FanInTwo D → a < b →
      ¬ (a = 0 ∧ b = 4) → ¬ ((a = 0 ∨ a = 4) ∧ b = 9) →
      (a = 4 → b = 5 ∨ b = 9) → (b = 4 → a = 1) →
      (∀ x : Fin 9 → Bool, let w := List.ofFn x ++ [x 0 || x 4]
        D.eval (w ++ [w.getD a false || w.getD b false]) = (fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) x) → 14 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (10 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2 < x3 →       ¬(x2 = (0 : Fin (10 : ℕ)) ∧ x3 = (4 : Fin (10 : ℕ))) →         ¬((x2 = (0 : Fin (10 : ℕ)) ∨ x2 = (4 : Fin (10 : ℕ))) ∧ x3 = (9 : Fin (10 : ℕ))) →           (∀ (x8 : Fin (9 : ℕ) → Bool),               have x9 : List Bool := List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))];               x1.eval (x9 ++ [x9.getD (↑x2) Bool.false || x9.getD (↑x3) Bool.false]) = (fun (x10 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x11 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x10 x11.1 && x10 x11.2) x8) →             (14 : ℕ) ≤ x1.size := by
  intro D a b fan order distinct absorbed computes
  let F : (Fin 9 → Bool) → Bool := (fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2)
  have closePair (j : Fin 9) (hj : j ∈ ({2,3,6,7,8} : Finset (Fin 9)))
      (comp : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4] ++ [x 4 || x j]) = F x) : 14 ≤ D.size := by
    let f := fun x : Fin 9 → Bool => D.eval (List.ofFn x ++ [x 0 || x 4] ++ [x j])
    have readj (x : Fin 9 → Bool) : (List.ofFn x ++ [x 0 || x 4]).getD j.val false = x j := by
      rw [List.getD_append _ _ _ _ (by simpa using j.isLt)]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos j.isLt]
      rfl
    have witness : ∀ j : Fin 9, j ∈ ({2,3,6,7,8} : Finset (Fin 9)) →
        let x : Fin 9 → Bool := fun i => decide (i=0 ∨ i=j)
        x 0=true ∧ x 4=false ∧ x j=true ∧ (Function.update x 4 true) j=true ∧ F x ≠ F (Function.update x 4 true) := by
      dsimp only [F]
      decide +kernel
    obtain ⟨h0,h4,hj',hju,hd⟩ := witness j hj
    let x : Fin 9 → Bool := fun i => decide (i=0 ∨ i=j)
    have agree (x : Fin 9 → Bool) (ht : x j=true) : f x=F x := by
      simpa only [f,ht,Bool.or_true] using comp x
    have restricted (y : Fin 8 → Bool) : f ![y 0,y 1,y 2,y 3,false,y 4,y 5,y 6,y 7] = F ![y 0,y 1,y 2,y 3,false,y 4,y 5,y 6,y 7] := by
      have h := comp ![y 0,y 1,y 2,y 3,false,y 4,y 5,y 6,y 7]
      change D.eval (_ ++ [false || _]) = _ at h
      simpa only [Bool.false_or] using h
    obtain ⟨E,ef,es,ee⟩ := pin D ⟨j.val,by omega⟩ f fan (by
      intro x
      dsimp only
      rw [readj])
      ⟨x,h0,h4,by rw [agree x hj',agree _ hju]; exact hd⟩
      ⟨fun _ => false,![true,true,false,false,false,false,false,false],by
        change f ![false,false,false,false,false,false,false,false,false] ≠ f ![true,true,false,false,false,false,false,false,false]
        have r0 := restricted (fun _ => false)
        have r1 := restricted ![true,true,false,false,false,false,false,false]
        change f ![false,false,false,false,false,false,false,false,false] = F ![false,false,false,false,false,false,false,false,false] at r0
        change f ![true,true,false,false,false,false,false,false,false] = F ![true,true,false,false,false,false,false,false,false] at r1
        rw [r0,r1]
        dsimp only [F]
        decide +kernel⟩
    by_contra! small
    apply minorFour
    refine ⟨E,ef,by omega,?_⟩
    intro y
    have h := (ee y).trans (restricted y)
    have eqF : ∀ y : Fin 8 → Bool, F ![y 0,y 1,y 2,y 3,false,y 4,y 5,y 6,y 7] =
        ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 0 && y 4) || (y 1 && y 5) || (y 2 && y 6) || (y 3 && y 7) || (y 4 && y 6) || (y 5 && y 7) || (y 7 && y 4)) := by
      dsimp only [F]
      decide +kernel
    exact h.trans (eqF y)
  by_cases hard : (a=4 → b=5 ∨ b=9) ∧ (b=4 → a=1)
  · exact remaining D a b fan order distinct absorbed hard.1 hard.2 computes
  · have pick : ∀ a b : Fin 10, a<b → ¬(a=0 ∧ b=4) →
        ¬((a=4 → b=5 ∨ b=9) ∧ (b=4 → a=1)) →
        (a=4 ∧ b.val<9 ∧ Fin.ofNat 9 b.val ∈ ({2,3,6,7,8} : Finset (Fin 9))) ∨
        (b=4 ∧ a.val<9 ∧ Fin.ofNat 9 a.val ∈ ({2,3,6,7,8} : Finset (Fin 9))) := by decide +kernel
    rcases pick a b order distinct hard with ⟨rfl,hb,hj⟩|⟨rfl,ha,hj⟩
    · apply closePair (Fin.ofNat 9 b.val) hj
      intro x
      have h := computes x
      have rb : (List.ofFn x ++ [x 0 || x 4]).getD b.val false = x (Fin.ofNat 9 b.val) := by
        rw [List.getD_append _ _ _ _ (by simpa using hb)]
        simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
        rw [dif_pos hb]
        change x ⟨b.val,hb⟩ = x (Fin.ofNat 9 b.val)
        congr 1
        apply Fin.ext
        exact (Nat.mod_eq_of_lt hb).symm
      change D.eval (List.ofFn x ++ [x 0 || x 4] ++ [(List.ofFn x ++ [x 0 || x 4]).getD 4 false || (List.ofFn x ++ [x 0 || x 4]).getD b.val false]) = F x at h
      rw [rb,show (List.ofFn x ++ [x 0 || x 4]).getD 4 false=x 4 from by simp] at h
      exact h
    · apply closePair (Fin.ofNat 9 a.val) hj
      intro x
      have h := computes x
      have ra : (List.ofFn x ++ [x 0 || x 4]).getD a.val false = x (Fin.ofNat 9 a.val) := by
        rw [List.getD_append _ _ _ _ (by simpa using ha)]
        simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
        rw [dif_pos ha]
        change x ⟨a.val,ha⟩ = x (Fin.ofNat 9 a.val)
        congr 1
        apply Fin.ext
        exact (Nat.mod_eq_of_lt ha).symm
      change D.eval (List.ofFn x ++ [x 0 || x 4] ++ [(List.ofFn x ++ [x 0 || x 4]).getD a.val false || (List.ofFn x ++ [x 0 || x 4]).getD 4 false]) = F x at h
      rw [ra,show (List.ofFn x ++ [x 0 || x 4]).getD 4 false=x 4 from by simp] at h
      simpa only [Bool.or_comm] using h
