import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3202_91
    (width : let f (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
     ∀ C : Circuit, FanInTwo C → C.size ≤ 15 → (∀ x, C.eval (List.ofFn x) = f x) → C.size = 15 ∧ C.output = 23)
    (raw : let f (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
     ∀ D : Circuit, FanInTwo D → D.size ≤ 14 → (∃ a b : Fin 9, a ≠ b ∧ (⟨.and,[a.val,b.val]⟩ : Gate) ∈ D.gates) → ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) ≠ f x)
    (rest : let f (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
     ∀ D : Circuit, FanInTwo D → D.size = 14 → D.output = 23 → ¬ (∃ a b : Fin 9, a ≠ b ∧ (⟨.and,[a.val,b.val]⟩ : Gate) ∈ D.gates) → (∃ i j : Fin D.gates.length, i < j ∧ i.val = 6 ∧ (D.gates.get i).op = .not ∧ (D.gates.get j).op = .not ∧ ∀ k : Fin D.gates.length, (D.gates.get k).op = .not → k = i ∨ k = j) → ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) ≠ f x)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 = (7 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  have keep3200 (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
      (gs.foldl (fun v (g : Gate) => v ++ [g.op.eval (g.inputs.map (fun j => v.getD j false))]) w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih _ (by simp;omega),List.getD_append _ _ _ _ hi]
  rintro ⟨gates,out⟩ hf ⟨i,j,ij,ii,ni,nj,only⟩ seed ok
  by_contra! small
  cases gates with
  | nil => exact Fin.elim0 i
  | cons first tail =>
    let D : Circuit := ⟨tail,out⟩
    have df : FanInTwo D := fun g hg => hf _ (List.mem_cons_of_mem _ hg)
    have ds : D.size ≤ 14 := by
      change tail.length ≤ 14
      change tail.length + 1 < 16 at small
      omega
    have seedVal (x : Fin 9 → Bool) :
        first.op.eval (first.inputs.map (fun j => (List.ofFn x).getD j false)) = (x 0 || x 2) := by
      have ss := seed x
      change (tail.foldl _ (List.ofFn x ++ [_])).getD 9 false = _ at ss
      rw [keep3200 _ _ _ (by simp),List.getD_append_right _ _ _ _ (by simp)] at ss
      simpa using ss
    have hit (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 0 || x 2]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
      have hx := congrFun ok x
      change D.eval (List.ofFn x ++ [first.op.eval (first.inputs.map (fun j => (List.ofFn x).getD j false))]) = _ at hx
      rwa [seedVal] at hx
    have widthC := width ⟨first::tail,out⟩ hf (by change (first::tail).length ≤ 15; change (first::tail).length < 16 at small; omega) (fun x => congrFun ok x)
    have exactSize : D.size = 14 := by
      have t := widthC.1
      change tail.length+1=15 at t
      change tail.length=14
      omega
    by_cases ex : (∃ a b : Fin 9, a ≠ b ∧ (⟨.and,[a.val,b.val]⟩ : Gate) ∈ D.gates)
    · obtain ⟨x,hx⟩ := raw D df ds ex
      exact hx (hit x)
    · have il : i.val < tail.length + 1 := i.isLt
      have jl : j.val < tail.length + 1 := j.isLt
      have lt : i.val < j.val := ij
      let u : Fin tail.length := ⟨i.val-1,by omega⟩
      let v : Fin tail.length := ⟨j.val-1,by omega⟩
      have ui : u.succ = i := by apply Fin.ext; change i.val-1+1=i.val; omega
      have vj : v.succ = j := by apply Fin.ext; change j.val-1+1=j.val; omega
      have du : (tail.get u).op = .not := by change ((first :: tail).get u.succ).op = .not; rwa [ui]
      have dv : (tail.get v).op = .not := by change ((first :: tail).get v.succ).op = .not; rwa [vj]
      have dr : (∃ i j : Fin D.gates.length, i < j ∧ i.val = 6 ∧ (D.gates.get i).op = .not ∧ (D.gates.get j).op = .not ∧ ∀ k : Fin D.gates.length, (D.gates.get k).op = .not → k = i ∨ k = j) := by
        refine ⟨u,v,?_,?_,du,dv,?_⟩
        · change i.val-1<j.val-1; omega
        · change i.val-1=6; omega
        · intro k hk
          have h := only k.succ (by simpa using hk)
          rcases h with h|h
          · left; exact Fin.succ_inj.mp (h.trans ui.symm)
          · right; exact Fin.succ_inj.mp (h.trans vj.symm)
      obtain ⟨x,hx⟩ := rest D df exactSize widthC.2 ex dr
      exact hx (hit x)
