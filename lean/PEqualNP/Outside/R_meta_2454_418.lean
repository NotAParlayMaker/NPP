import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2454_418
    (suffix : ∃ (a b : Fin 10) (D : PEqualNP.CircuitLowerBounds.Circuit),
      ((a=0 ∧ 1≤b ∧ b≤6) ∨ (a=2 ∧ 3≤b ∧ b≤6) ∨ (a=4 ∧ 5≤b ∧ b≤9) ∨ (a=5 ∧ b=8)) ∧
      PEqualNP.MetaComplexity.FanInTwo D ∧ D.size≤13 ∧
      (∀ u : Fin 2, ∃ g∈D.gates, u.val∈g.inputs) ∧
      (let t := Equiv.swap (0 : Fin 10) a
       let e := (Equiv.swap (1 : Fin 10) (t b)).trans t
       ∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 || x 1]) =
         ([(0,2),(2,3),(3,1),(0,4),(4,5),(5,6),(6,1),(0,7),(7,8),(8,9),(9,1)] : List (Fin 10 × Fin 10)).any
           (fun z => x (e.symm z.1) && x (e.symm z.2))))
    (relocate : ∀ (n : ℕ) (a b : Fin n) (e : Equiv.Perm (Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo D →
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = D.size+1 ∧
        C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or,[(e a).val,(e b).val]⟩ ∧
        ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
          D.eval (List.ofFn (fun i => x (e i)) ++ [x (e a) || x (e b)])) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 ∧ x1.size ≤ (14 : ℕ) ∧ (∀ (x2 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x2) = [((0 : Fin (10 : ℕ)), (2 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (3 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (1 : Fin (10 : ℕ))), ((0 : Fin (10 : ℕ)), (4 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ))), ((5 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((6 : Fin (10 : ℕ)), (1 : Fin (10 : ℕ))), ((0 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((7 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((8 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((9 : Fin (10 : ℕ)), (1 : Fin (10 : ℕ)))].any fun (x3 : Fin (10 : ℕ) × Fin (10 : ℕ)) => x2 x3.1 && x2 x3.2) ∧ ∃ (x2 : PEqualNP.CircuitLowerBounds.Gate), x1.gates.head? = Option.some x2 ∧ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
  obtain ⟨a,b,D,_,fd,sz,_,table⟩ := suffix
  let t := Equiv.swap (0 : Fin 10) a
  let e := (Equiv.swap (1 : Fin 10) (t b)).trans t
  obtain ⟨C,fc,count,head,ev⟩ := relocate 10 0 1 e D fd
  refine ⟨C,fc,by omega,?_,⟨_,head,rfl⟩⟩
  intro x
  rw [ev]
  have h := table (fun i => x (e i))
  change _ = List.any _ (fun z : Fin 10 × Fin 10 => x (e (e.symm z.1)) && x (e (e.symm z.2))) at h
  simpa only [Equiv.apply_symm_apply] using h
