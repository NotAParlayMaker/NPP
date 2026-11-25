import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3273_418
    (normalize :
    ∀ (n : Nat) (port : Sum (Fin n) Bool) (C : Circuit), FanInTwo C →
      ∃ D : Circuit, FanInTwo D ∧ D.size ≤ max 1 C.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          C.eval (List.ofFn x ++ [port.elim x id]))
    (remaining :
    ∀ D : Circuit, FanInTwo D → D.size ≤ 13 → ∃ x : Fin 9 → Bool,
      D.eval (List.ofFn x ++ [!x 0]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ x1 ∈ [((0 : Fin (12 : ℕ)), (0 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (1 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (2 : Fin (12 : ℕ))), ((3 : Fin (12 : ℕ)), (3 : Fin (12 : ℕ))), ((4 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((6 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((9 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((10 : Fin (12 : ℕ)), (10 : Fin (12 : ℕ))), ((11 : Fin (12 : ℕ)), (11 : Fin (12 : ℕ)))],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];           have x8 : Fin (12 : ℕ) → Bool := fun (x8 : Fin (12 : ℕ)) => if x8 = (11 : Fin (12 : ℕ)) then Bool.true else x7.getD (↑x8) Bool.false;           x3.eval (x7 ++ [x8 x1.1 && x8 x1.2]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  let tags : List (Fin 12 × Fin 12) := [(0,0),(1,1),(2,2),(3,3),(4,4),(6,6),(9,9),(10,10),(11,11)]
  let port (i : Fin 12) : Sum (Fin 10) Bool :=
    if h : i.val < 10 then Sum.inl ⟨i.val,h⟩ else Sum.inr (decide (i.val=11))
  let y (x : Fin 9 → Bool) : Fin 10 → Bool := Fin.snoc x (!x 0)
  have appendBit (n : Nat) (x : Fin n → Bool) (b : Bool) :
      List.ofFn (Fin.snoc x b : Fin (n+1) → Bool) = List.ofFn x ++ [b] := by
    rw [List.ofFn_succ']; simp
  have snoc (x : Fin 9 → Bool) : List.ofFn (y x) = List.ofFn x ++ [!x 0] := appendBit 9 x (!x 0)
  have diag : tags.all (fun t => t.1==t.2) = true := by decide
  intro t ht C fan lim
  have diagonal : t.1=t.2 := eq_of_beq (List.all_eq_true.mp diag t ht)
  obtain ⟨D,fd,sd,run⟩ := normalize 10 (port t.1) C fan
  obtain ⟨x,bad⟩ := remaining D fd (by omega)
  refine ⟨x,?_⟩
  dsimp only
  rw [← diagonal,Bool.and_self]
  rw [← snoc] at bad ⊢
  rw [run] at bad
  convert bad using 1
  congr 3
  by_cases h : t.1.val<10
  · have ne : t.1≠11 := fun e => by rw [e] at h; contradiction
    simp only [port,dite_eq_left h,Sum.elim_inl,ite_eq_right ne]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h)]
    simp only [List.getElem_ofFn]
  · have z : (List.ofFn (y x)).getD t.1.val false=false :=
      List.getD_eq_default _ _ (by simp only [List.length_ofFn];omega)
    simp only [port,dite_eq_right h,Sum.elim_inr,id_eq,z]
    by_cases hi : t.1=11
    · simp [hi]
    · have nv : t.1.val≠11 := fun e => hi (Fin.ext e)
      simp [hi,nv]
