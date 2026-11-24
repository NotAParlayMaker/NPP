import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Compiling the two free wires costs two gates. A surviving signed
-- monotone computation loses both polarities on the zero slice.
theorem PEqualNP.Outside.R_meta_3885_714
    (raw : ∀ D : Circuit, FanInTwo D → circuitFun 9 D = (fun x => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → 15 ≤ D.size)
    (twoNeg : ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
      2 ≤ D.gates.countP (fun g => g.op.eval [false]) →
      ¬ ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2))
    (project : ∀ (b : Fin 9) (F : (Fin 9 → Bool) → Bool) (C : Circuit), Monotone2 C →
      (∀ x, C.eval (List.ofFn x ++ [x 0 || x 2, !(x b)]) = F x) →
      (∃ u v : Fin 9 → Bool, F u = true ∧ F v = false ∧
        (∀ i, i ≠ b → u i ≤ v i) ∧ (u 0 || u 2) ≤ (v 0 || v 2) ∧ v b ≤ u b) →
      (∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size + 1 ∧ circuitFun 9 D = F) ∨
      (∃ D : Circuit, FanInTwo D ∧ D.size + 2 ≤ C.size ∧
        ∀ y : Fin 9 → Bool, let x := Function.update y b false
          D.eval (List.ofFn x ++ [x 0 || x 2, false, true]) = F x))
    (minor : ∀ (b : Fin 9), b ∈ ([0,3,4] : List (Fin 9)) → ∀ D : Circuit,
      FanInTwo D → D.size ≤ 11 → ∃ y : Fin 9 → Bool, let x := Function.update y b false
        D.eval (List.ofFn x ++ [x 0 || x 2, false, true]) ≠ ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2))
    : ∀ (x1 : Fin (11 : ℕ)),   x1 = (0 : Fin (11 : ℕ)) ∨ x1 = (3 : Fin (11 : ℕ)) ∨ x1 = (4 : Fin (11 : ℕ)) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [!x7.getD (↑x1) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x8.1 && x6 x8.2 := by
  let F (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let atRow (r : Nat) (i : Fin 9) := r.testBit i.val
  have rowTest : ∀ b ∈ ([0,3,4] : List (Fin 9)),
      let u := atRow (if b = 0 then 17 else if b = 3 then 12 else 24)
      let v := atRow (if b = 0 then 20 else if b = 3 then 4 else 8)
      F u = true ∧ F v = false ∧ (∀ i, i ≠ b → u i ≤ v i) ∧
        (u 0 || u 2) ≤ (v 0 || v 2) ∧ v b ≤ u b := by decide +kernel
  intro j hj C fan size
  let b : Fin 9 := Fin.ofNat 9 j.val
  have bm : b ∈ ([0,3,4] : List (Fin 9)) := by
    rcases hj with h | h | h <;> subst j <;> decide
  by_contra! agree
  have ev : ∀ x, C.eval (List.ofFn x ++ [x 0 || x 2, !(x b)]) = F x := by
    intro x
    have h := agree x
    rcases hj with e | e | e <;> subst j <;> simpa [b,List.getD,F] using h
  have mono : Monotone2 C := by
    intro g hg
    refine ⟨?_,(fan g hg).2⟩
    rcases (fan g hg).1 with z | z | z
    · exact Or.inl z
    · exact Or.inr z
    · exfalso
      let n : Gate := ⟨.not,[b.val]⟩
      let D : Circuit := ⟨n::C.gates,C.output⟩
      have fd : FanInTwo D := by
        intro a ha
        rcases List.mem_cons.mp ha with rfl | hm
        · simp [n]
        · exact fan a hm
      have sd : D.size ≤ 14 := by change C.gates.length + 1 ≤ 14; change C.gates.length ≤ 13 at size; omega
      have pos : 0 < C.gates.countP (fun g => g.op.eval [false]) :=
        List.countP_pos_iff.mpr ⟨g,hg,by rw [z]; rfl⟩
      have count : 2 ≤ D.gates.countP (fun g => g.op.eval [false]) := by
        change 2 ≤ (n::C.gates).countP _
        simp only [List.countP_cons]
        change 2 ≤ C.gates.countP _ + 1
        omega
      apply twoNeg D fd sd count
      intro x
      change C.eval ((List.ofFn x ++ [x 0 || x 2]) ++ [_]) = _
      have hb : (List.ofFn x ++ [x 0 || x 2]).getD b.val false = x b := by
        rw [List.getD_append _ _ _ _ (by simpa using b.isLt)]
        rcases hj with h | h | h <;> subst j <;> rfl
      change C.eval ((List.ofFn x ++ [x 0 || x 2]) ++ [!((List.ofFn x ++ [x 0 || x 2]).getD b.val false)]) = _
      rw [hb, List.append_assoc]
      exact ev x
  rcases project b F C mono ev ⟨_,_,rowTest b bm⟩ with ⟨D,fd,sd,hd⟩ | ⟨D,fd,sd,hd⟩
  · have lo := raw D fd hd
    omega
  · obtain ⟨y,hy⟩ := minor b bm D fd (by omega)
    exact hy (hd y)
