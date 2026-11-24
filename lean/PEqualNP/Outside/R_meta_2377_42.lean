import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Delete one point at a time, retaining all its five lines for the other points.
-- At the last point, its five incident lines give five independent ways
-- to change one rejecting input into an accepting input.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3500000 in
theorem PEqualNP.Outside.R_meta_2377_42
    (singleton : ∀ (n : Nat) (C : Circuit) (x : Fin n → Bool) (v : Fin 5 → Fin n),
      Monotone2 C → Function.Injective v → C.eval (List.ofFn x) = false →
      (∀ t, C.eval (List.ofFn (Function.update x (v t) true)) = true) →
      4 ≤ {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard)
    (deletion :
      let adj := fun p l : Fin 21 => ([(p.val+20)%21,p.val,(p.val+5)%21,(p.val+7)%21,(p.val+17)%21] : List Nat).contains l.val
      let game := fun (S : Finset (Fin 21)) (x : Fin 42 → Bool) =>
        ∃ p ∈ S, ∃ l : Fin 21, adj p l = true ∧ x (Fin.castAdd 21 p) = true ∧ x (Fin.natAdd 21 l) = true
      let cost := fun C : Circuit => {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard
      ∀ (S : Finset (Fin 21)) (C : Circuit), 2 ≤ S.card → Monotone2 C →
      (∀ x, C.eval (List.ofFn x) = true ↔ game S x) →
      ∃ p ∈ S, ∃ D : Circuit, Monotone2 D ∧ cost D + 5 ≤ cost C ∧
        ∀ x, D.eval (List.ofFn x) = true ↔ game (S.erase p) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (104 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  intro C mono computes
  let adj := fun p l : Fin 21 => ([(p.val+20)%21,p.val,(p.val+5)%21,(p.val+7)%21,(p.val+17)%21] : List Nat).contains l.val
  let game := fun (S : Finset (Fin 21)) (x : Fin 42 → Bool) =>
        ∃ p ∈ S, ∃ l : Fin 21, adj p l = true ∧ x (Fin.castAdd 21 p) = true ∧ x (Fin.natAdd 21 l) = true
  let cost := fun C : Circuit => {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard
  let line := fun (p : Fin 21) (t : Fin 5) => Fin.ofNat 21
      (([(p.val+20)%21,p.val,(p.val+5)%21,(p.val+7)%21,(p.val+17)%21] : List Nat).getD t.val 0)
  have distinct : ∀ p, Function.Injective (line p) := by unfold Function.Injective; decide
  have incident : ∀ p t, adj p (line p t) = true := by decide
  have separated : ∀ p l : Fin 21, Fin.castAdd 21 p ≠ Fin.natAdd 21 l := by decide
  have inject : Function.Injective (Fin.natAdd 21 : Fin 21 → Fin 42) := by unfold Function.Injective; decide
  have one (p : Fin 21) (D : Circuit) (hD : Monotone2 D)
      (ok : ∀ x, D.eval (List.ofFn x) = true ↔ game {p} x) : 4 ≤ cost D := by
    let x := fun j : Fin 42 => decide (j = Fin.castAdd 21 p)
    let v := fun t => Fin.natAdd 21 (line p t)
    apply singleton 42 D x v hD (inject.comp (distinct p))
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨q,_,l,_,_,hl⟩ := (ok x).1 h
      exact separated p l (of_decide_eq_true hl).symm
    · intro t
      apply (ok _).2
      refine ⟨p,by simp,line p t,incident p t,?_,?_⟩
      · rw [Function.update_of_ne (separated p (line p t))]
        simp [x]
      · exact Function.update_self .. 
  have bound (k : Nat) : ∀ (S : Finset (Fin 21)) (D : Circuit), S.card = k →
      1 ≤ k → Monotone2 D → (∀ x, D.eval (List.ofFn x) = true ↔ game S x) →
      5*k ≤ cost D + 1 := by
    induction k with
    | zero => intro S D card pos; omega
    | succ k ih =>
      intro S D card pos basis ok
      by_cases empty : k = 0
      · have unit : S.card = 1 := by omega
        obtain ⟨p,rfl⟩ := Finset.card_eq_one.mp unit
        have b := one p D basis ok
        omega
      · obtain ⟨p,hp,B,hB,save,eval⟩ := deletion S D (by omega) basis ok
        change cost B + 5 ≤ cost D at save
        have card' : (S.erase p).card = k := by rw [Finset.card_erase_of_mem hp,card]; omega
        have b := ih _ B card' (by omega) hB eval
        omega
  let edges := (List.range 21).flatMap fun p =>
    [(p,21+(p+20)%21),(p,21+p),(p,21+(p+5)%21),(p,21+(p+7)%21),(p,21+(p+17)%21)]
  have sides : ∀ u v : Fin 42, (u.val,v.val) ∈ edges → u.val < 21 ∧ 21 ≤ v.val := by decide
  have check : ∀ p l : Fin 21, (p.val,21+l.val) ∈ edges ↔ adj p l = true := by decide
  have indices (u v : Fin 42) : (u.val,v.val) ∈ edges ↔
      ∃ p l : Fin 21, adj p l = true ∧ u = Fin.castAdd 21 p ∧ v = Fin.natAdd 21 l := by
    constructor
    · intro e
      obtain ⟨hu,hv⟩ := sides u v e
      let p : Fin 21 := ⟨u.val,hu⟩
      let l : Fin 21 := ⟨v.val-21,by omega⟩
      have ev : 21+l.val = v.val := by dsimp [l]; omega
      exact ⟨p,l,(check p l).1 (by rw [ev]; exact e),Fin.ext rfl,Fin.ext ev.symm⟩
    · rintro ⟨p,l,h,rfl,rfl⟩
      exact (check p l).2 h
  have full (x) : C.eval (List.ofFn x) = true ↔ game Finset.univ x := by
    rw [computes]
    constructor
    · rintro ⟨u,v,e,hu,hv⟩
      obtain ⟨p,l,h,rfl,rfl⟩ := (indices u v).1 e
      exact ⟨p,Finset.mem_univ _,l,h,hu,hv⟩
    · rintro ⟨p,_,l,h,hu,hv⟩
      exact ⟨_,_,(indices _ _).2 ⟨p,l,h,rfl,rfl⟩,hu,hv⟩
  have finalBound := bound 21 Finset.univ C (by decide) (by decide) mono full
  change 104 ≤ cost C
  omega


