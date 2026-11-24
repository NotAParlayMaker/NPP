import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3020_67
    (transport : let f := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5); ∀ (a b : Fin 9), a ≠ b → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
        (∀ x, C.eval (List.ofFn x ++ [x 0 || x 2, x a && x b]) = f x) →
        ∃ (u v : Fin 9) (D : PEqualNP.CircuitLowerBounds.Circuit), 10 * min u.val v.val + max u.val v.val ∈ ([1,2,3,4,6,46] : List Nat) ∧ PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ 15 ∧
        (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = (x u && x v)) ∧
        ∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = f x)
    (firstAnd : let f := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5); ∀ (u v : Fin 9), 10 * min u.val v.val + max u.val v.val ∈ ([1,2,3,4,6,46] : List Nat) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
        (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = (x u && x v)) →
        (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = f x) → 16 ≤ D.size)
    (aliases : let f := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5); ∀ (j : Fin 11) (c : Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
        ∃ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [x 0 || x 2]) ++ [c || (List.ofFn x ++ [x 0 || x 2]).getD j.val false]) ≠ f x)
    (mixed : let f := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5); ∀ k ∈ ([1,3,4,5,6,7,8] : List (Fin 9)), ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
        ∃ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [x 0 || x 2]) ++ [(x 0 || x 2) && x k]) ≠ f x) : ∀ (x1 : List (Fin (11 : ℕ))),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro pins hlen C hf hs
  let sig := fun (x : Fin 9 → Bool) (i : Fin 11) => (List.ofFn x ++ [x 0 || x 2]).getD i.val false
  let mode (i j : Fin 11) : Fin 11 ⊕ ((Fin 9 × Fin 9) ⊕ Fin 9) :=
    if i.val=10 ∨ j.val=10 then .inl 10 else if i=j then .inl i
    else if i.val<9 ∧ j.val<9 then .inr (.inl (Fin.ofNat 9 i.val, Fin.ofNat 9 j.val))
    else let r := if i.val=9 then j else i
         if r.val=0 ∨ r.val=2 then .inl r else .inr (.inr (Fin.ofNat 9 r.val))
  let pass (i j : Fin 11) := (mode i j).elim
    (fun k => decide (∀ x, (sig x i && sig x j) = sig x k))
    (fun t => t.elim
      (fun ab => decide (ab.1 ≠ ab.2 ∧ ∀ x, (sig x i && sig x j) = (x ab.1 && x ab.2)))
      (fun k => decide (k ∈ ([1,3,4,5,6,7,8] : List (Fin 9)) ∧
        ∀ x, (sig x i && sig x j) = ((x 0 || x 2) && x k))))
  have correct : ∀ i j : Fin 11, pass i j = true := by decide +kernel
  by_contra! agree
  have hit (x : Fin 9 → Bool) := Classical.not_not.mp (agree x)
  cases pins with
  | nil =>
    obtain ⟨x,hx⟩ := aliases 10 true C hf hs
    exact hx (hit x)
  | cons i is =>
    cases is with
    | nil =>
      obtain ⟨x,hx⟩ := aliases i false C hf hs
      have eqn := hit x
      change C.eval ((List.ofFn x ++ [x 0 || x 2]) ++ [sig x i && true]) = _ at eqn
      exact hx (by simpa only [Bool.and_true,Bool.false_or] using eqn)
    | cons j js =>
      have emp : js = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at hlen
        omega
      subst js
      have ev (x : Fin 9 → Bool) : C.eval ((List.ofFn x ++ [x 0 || x 2]) ++ [sig x i && sig x j]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
        have eqn := hit x
        change C.eval ((List.ofFn x ++ [x 0 || x 2]) ++ [sig x i && (sig x j && true)]) = _ at eqn
        simpa only [Bool.and_true] using eqn
      have spec := correct i j
      cases hm : mode i j with
      | inl k =>
        simp only [pass,hm,Sum.elim_inl,Sum.elim_inr,decide_eq_true_eq] at spec
        obtain ⟨x,hx⟩ := aliases k false C hf hs
        have e := ev x; rw [spec x] at e
        exact hx (by simpa only [Bool.false_or] using e)
      | inr t =>
        simp only [pass,hm,Sum.elim_inl,Sum.elim_inr,decide_eq_true_eq] at spec
        rcases t with ⟨a,b⟩ | k
        · simp only [Sum.elim_inl,decide_eq_true_eq] at spec
          obtain ⟨ne,h⟩ := spec
          obtain ⟨u,v,D,rep,df,ds,seed,ok⟩ := transport a b ne C hf hs (by
            intro x; have e := ev x; rw [h x,List.append_assoc] at e; exact e)
          have lb := firstAnd u v rep D df seed ok
          omega
        · simp only [Sum.elim_inr,decide_eq_true_eq] at spec
          obtain ⟨hk,h⟩ := spec
          obtain ⟨x,hx⟩ := mixed k hk C hf hs
          have e := ev x; rw [h x] at e
          exact hx e
