import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Remove the sole consumer of the extra input. Its two cofactors are a constant
-- and a value on an earlier wire. Both endpoint orientations must reach the output.
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_3089_644
    (cut : ∀ (n : ℕ) (C : Circuit), FanInTwo C → C.output ≠ n →
      (C.output :: C.gates.flatMap Gate.inputs).count n = 1 →
      (∃ x : Fin n → Bool, C.eval (List.ofFn x ++ [false]) ≠ C.eval (List.ofFn x ++ [true])) →
      ∃ (P Q : Circuit) (a c : Bool) (j : ℕ),
        FanInTwo P ∧ FanInTwo Q ∧ P.size + Q.size + 1 = C.size ∧
        (a = c ∨ j = 0) ∧ j ≤ 2 + n + P.size ∧
        ∀ (x : Fin n → Bool) (b : Bool),
          let w := P.wires (List.ofFn x ++ [false])
          C.eval (List.ofFn x ++ [b]) =
            Q.eval (w ++ [if b = a then c else (true :: w).getD j false]))
    (residual : let edge := (fun x : Fin 9 → Bool =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
      let seed := fun x : Fin 9 → Bool => x 0 || x 3
      ∀ (P Q : Circuit) (a c : Bool) (j : ℕ), FanInTwo P → FanInTwo Q →
        P.size + Q.size = 13 → 0 < Q.size → (a = c ∨ j = 0) → j ≤ 11 + P.size →
        let w := fun x : Fin 9 → Bool => P.wires (List.ofFn x ++ [false])
        let tap := fun x => (true :: w x).getD j false
        let run := fun x (b : Bool) => Q.eval (w x ++ [b])
        (∀ d : Bool, ∃ x, x 0 = d ∧ x 3 = !d ∧ tap x ≠ c ∧ run x false ≠ run x true) →
        (∀ x, seed x = a → run x c = edge x) →
        ∃ x, seed x ≠ a ∧ run x (tap x) ≠ edge x) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (14 : ℕ) → (x2.output ≤ (10 : ℕ) + x2.size ∧ ∀ x5 ∈ x2.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (10 : ℕ) + x2.size) → (∀ x6 < (10 : ℕ) + x2.size, x6 ∈ x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) → (9 : ℕ) + (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false] && !x7.op.eval [Bool.true]) x2.gates).length + ∑ x7 ∈ Finset.range ((10 : ℕ) + x2.size), (List.count x7 (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) - (1 : ℕ)) ≤ x2.size → List.count (9 : ℕ) (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) = (1 : ℕ) → (∀ (x9 : Fin (9 : ℕ)), ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 x9]) ≠ x1 x10) → ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]) ≠ x1 x10 := by
  intro target C fan size _ _ _ once copies
  let seed := fun x : Fin 9 → Bool => x 0 || x 3
  let raw := fun (x : Fin 9 → Bool) (b : Bool) => C.eval (List.ofFn x ++ [b])
  by_contra! correct
  have ok (x : Fin 9 → Bool) : raw x (seed x) = target x := correct x
  have varied : ∀ a c : Bool, ∃ x : Fin 9 → Bool, seed x = a ∧ target x ≠ c := by
    decide +kernel
  have stable (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      ((Circuit.mk gs 0).wires w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change ((Circuit.mk gs 0).wires (w ++ [_])).getD i false = _
      rw [ih _ (by simp; omega)]
      exact List.getD_append _ _ _ _ hi
  have out : C.output ≠ 9 := by
    intro eq
    obtain ⟨x, hx, bad⟩ := varied true true
    apply bad
    have h := ok x
    change ((Circuit.mk C.gates 0).wires (List.ofFn x ++ [seed x])).getD C.output false = _ at h
    rw [eq, stable _ _ _ (by simp)] at h
    simpa [hx, List.getD_eq_getElem?_getD] using h.symm
  have sensitive : ∀ d : Bool, ∃ x : Fin 9 → Bool,
      x 0 = d ∧ x 3 = !d ∧ raw x false ≠ raw x true := by
    intro d
    let p : Fin 9 := if d then 3 else 0
    obtain ⟨x, bad⟩ := copies p
    change raw x (x p) ≠ target x at bad
    rw [← ok x] at bad
    have different : x p ≠ seed x := fun e => bad (congrArg (raw x) e)
    cases d <;> cases h0 : x 0 <;> cases h3 : x 3 <;>
      simp [p, seed, h0, h3] at different bad <;> exact ⟨x, h0, h3, bad⟩
  obtain ⟨_, _, _, hs⟩ := sensitive false
  obtain ⟨P,Q,a,c,j,hp,hq,hsize,hmode,hj,rep⟩ := cut 9 C fan out once ⟨_, hs⟩
  let w := fun x : Fin 9 → Bool => P.wires (List.ofFn x ++ [false])
  let tap := fun x => (true :: w x).getD j false
  let run := fun x (b : Bool) => Q.eval (w x ++ [b])
  have factor (x : Fin 9 → Bool) (b : Bool) :
      raw x b = run x (if b = a then c else tap x) := rep x b
  have cross (d : Bool) : ∃ x : Fin 9 → Bool,
      x 0 = d ∧ x 3 = !d ∧ tap x ≠ c ∧ run x false ≠ run x true := by
    obtain ⟨x,h0,h3,ne⟩ := sensitive d
    rw [factor x false, factor x true] at ne
    refine ⟨x,h0,h3,fun same => ?_, ?_⟩
    · simp [same] at ne
    · intro eq
      have constant (b : Bool) : run x b = run x true := by cases b <;> simp [eq]
      exact ne ((constant _).trans (constant _).symm)
  have on (x : Fin 9 → Bool) (h : seed x = a) : run x c = target x := by
    simpa only [factor, h, ite_true, eq_self] using ok x
  have positive : 0 < Q.size := by
    by_contra! empty
    have hn : Q.gates = [] := List.length_eq_zero_iff.mp (by change Q.size = 0; omega)
    have length (gs : List Gate) (v : List Bool) :
        ((Circuit.mk gs 0).wires v).length = v.length + gs.length := by
      induction gs generalizing v with
      | nil => rfl
      | cons g gs ih =>
        change ((Circuit.mk gs 0).wires (v ++ [_])).length = _
        rw [ih]
        simp
        omega
    have wl (x : Fin 9 → Bool) : (w x).length = 10 + P.size := by
      change ((Circuit.mk P.gates 0).wires _).length = _
      rw [length]
      change (List.ofFn x ++ [false]).length + P.gates.length = 10 + P.gates.length
      simp
    have read (x : Fin 9 → Bool) (b : Bool) :
        run x b = (w x ++ [b]).getD Q.output false := by
      change (Q.gates.foldl _ (w x ++ [b])).getD Q.output false = _
      rw [hn]
      rfl
    obtain ⟨x,_,_,_,ne⟩ := cross false
    have output : Q.output = 10 + P.size := by
      by_contra h
      rw [read,read] at ne
      by_cases lt : Q.output < (w x).length
      · exact ne ((List.getD_append _ _ _ _ lt).trans (List.getD_append _ _ _ _ lt).symm)
      · have past : (w x).length + 1 ≤ Q.output := by rw [wl] at lt ⊢; omega
        apply ne
        exact (List.getD_eq_default (w x ++ [false]) false (by simpa using past)).trans
          (List.getD_eq_default (w x ++ [true]) false (by simpa using past)).symm
    obtain ⟨y,hy,bad⟩ := varied a c
    apply bad
    have h := (on y hy).symm
    rw [read, output, ← wl y] at h
    simpa [List.getD_eq_getElem?_getD] using h
  let edge := (fun x : Fin 9 → Bool =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
  have graphEq : target = edge := by decide +kernel
  obtain ⟨x,hx,bad⟩ := residual P Q a c j hp hq (by omega) positive hmode (by omega)
    cross (by
      intro y ey
      exact (on y ey).trans (congrFun graphEq y))
  apply bad
  change seed x ≠ a at hx
  change run x (tap x) = edge x
  have eq := (ok x).trans (congrFun graphEq x)
  rwa [factor, ite_eq_right hx] at eq
