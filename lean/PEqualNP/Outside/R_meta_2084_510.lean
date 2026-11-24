import PEqualNP.Defs

open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2084_510
    (restrict : ∀ (n : ℕ) (f : (Fin (n+1) → Bool) → Bool) (p : Fin (n+1)) (b : Bool) (s : ℕ),
      (∃ x : Fin (n+1) → Bool, f (Function.update x p (!x p)) ≠ f x) →
      (∃ x y : Fin (n+1) → Bool, f (Function.update x p b) ≠ f (Function.update y p b)) →
      HasCircuitSize (n+1) f (s+1) →
      HasCircuitSize (n+1) (fun x => f (Function.update x p b)) s)
    (core : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (f : (Fin n → Bool) → Bool),
      (∀ v : Fin n, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∃ i j : Fin n, G.Adj i j) →
      (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
      (∀ x : Fin n → Bool, f x = true ↔ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) →
      ∀ s : ℕ, HasCircuitSize n f s → G.edgeSet.ncard + k ≤ s + 1) :
∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool), (∀ x6 ∉ x4, (x3.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x3.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x3.Adj x8 x9 → x8 ∉ x4) → (∃ (x9 : Fin x1) (x10 : Fin x1), x3.Adj x9 x10) → (∀ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x3.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) → x2 ≤ x10.card) → (∀ (x11 : Fin x1 → Bool), x5 x11 = Bool.true ↔ (∃ x12 ∈ x4, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → ∀ (x12 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x12 → x4.card + x3.edgeSet.ncard + x2 ≤ x12 + (1 : ℕ) := by
  classical
  intro n k G A f degree girth isolated edges cover computes s has
  cases n with
  | zero =>
    obtain ⟨i, _, _⟩ := edges
    exact Fin.elim0 i
  | succ n =>
    have cubic (v : Fin (n+1)) :
        (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3 := by
      by_cases h : v ∈ A
      · left
        have empty : G.neighborSet v = ∅ := Set.eq_empty_iff_forall_notMem.mpr
          (fun w hw => isolated v w hw h)
        simp [empty]
      · exact Or.inr (degree v h)
    have strip (S : Finset (Fin (n+1))) : S ⊆ A →
        ∀ (F : (Fin (n+1) → Bool) → Bool) (t : ℕ),
        (∀ x : Fin (n+1) → Bool, F x = true ↔
          (∃ a ∈ S, x a = true) ∨ ∃ i j : Fin (n+1), G.Adj i j ∧ x i = true ∧ x j = true) →
        HasCircuitSize (n+1) F t → S.card + G.edgeSet.ncard + k ≤ t + 1 := by
      induction S using Finset.induction_on with
      | empty =>
        intro _ F t hF hsize
        have bound := core (n+1) k G F cubic girth edges cover
          (fun x => by simpa using hF x) t hsize
        simpa using bound
      | @insert p S hp ih =>
        intro sub F t hF hsize
        have pA : p ∈ A := sub (Finset.mem_insert_self p S)
        have sA : S ⊆ A := fun q hq => sub (Finset.mem_insert_of_mem hq)
        let Z : Fin (n+1) → Bool := fun _ => false
        let O : Fin (n+1) → Bool := fun _ => true
        have zero : F Z = false := by
          cases h : F Z with
          | false => rfl
          | true => exact False.elim (by simpa [Z] using (hF Z).mp h)
        have one : F (Function.update Z p (!Z p)) = true := by
          apply (hF _).mpr
          exact Or.inl ⟨p, Finset.mem_insert_self p S, by simp [Z]⟩
        have zeroUpdate : Function.update Z p false = Z := by
          funext i
          by_cases h : i = p <;> simp [Function.update, h, Z]
        obtain ⟨i,j,hij⟩ := edges
        have hip : i ≠ p := fun e => isolated i j hij (e ▸ pA)
        have hjp : j ≠ p := fun e => isolated j i hij.symm (e ▸ pA)
        have oneUpdate : F (Function.update O p false) = true := by
          apply (hF _).mpr
          exact Or.inr ⟨i, j, hij, by simp [Function.update_of_ne hip, O],
            by simp [Function.update_of_ne hjp, O]⟩
        have tpos : 0 < t := by
          obtain ⟨C, fan, small, eval⟩ := hsize
          by_contra hn
          have nil : C.gates = [] := List.eq_nil_of_length_eq_zero (by
            change C.gates.length ≤ t at small
            omega)
          have read (x : Fin (n+1) → Bool) :
              F x = (List.ofFn x).getD C.output false := by
            rw [← eval x]
            change (C.gates.foldl (fun w g =>
              w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])
              (List.ofFn x)).getD C.output false = _
            rw [nil]
            rfl
          have out : C.output = p.val := by
            have h := read (Function.update Z p (!Z p))
            rw [one] at h
            by_cases hlt : C.output < n+1
            · have hx : (⟨C.output,hlt⟩ : Fin (n+1)) = p := by
                by_contra hne
                have hd : (List.ofFn (Function.update Z p (!Z p))).getD C.output false =
                    false := by
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hlt)]
                  simp only [Option.getD_some, List.getElem_ofFn]
                  exact Function.update_of_ne (show (⟨C.output,hlt⟩ : Fin (n+1)) ≠ p from hne) _ _
                rw [hd] at h
                contradiction
              exact congrArg Fin.val hx
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hlt)] at h
              contradiction
          have h := read (Function.update O p false)
          rw [oneUpdate, out, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (by simpa using p.isLt)] at h
          simp only [Option.getD_some, List.getElem_ofFn, Fin.eta, Function.update_self] at h
          exact Bool.noConfusion h
        obtain ⟨u,rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
        have smaller := restrict n F p false u ⟨Z, by simp [one, zero]⟩
          ⟨Z, O, by rw [zeroUpdate, zero, oneUpdate]; decide⟩ hsize
        have hsmall (x : Fin (n+1) → Bool) :
            F (Function.update x p false) = true ↔ (∃ a ∈ S, x a = true) ∨
              ∃ i j : Fin (n+1), G.Adj i j ∧ x i = true ∧ x j = true := by
          rw [hF]
          constructor
          · rintro (⟨a, ha, hax⟩ | ⟨v,w,hvw,hvx,hwx⟩)
            · rcases Finset.mem_insert.mp ha with rfl | ha
              · simp at hax
              · have hap : a ≠ p := fun e => hp (e ▸ ha)
                exact Or.inl ⟨a,ha,by simpa [Function.update_of_ne hap] using hax⟩
            · have hvp : v ≠ p := fun e => isolated v w hvw (e ▸ pA)
              have hwp : w ≠ p := fun e => isolated w v hvw.symm (e ▸ pA)
              exact Or.inr ⟨v,w,hvw,by simpa [Function.update_of_ne hvp] using hvx,
                by simpa [Function.update_of_ne hwp] using hwx⟩
          · rintro (⟨a,ha,hax⟩ | ⟨v,w,hvw,hvx,hwx⟩)
            · have hap : a ≠ p := fun e => hp (e ▸ ha)
              exact Or.inl ⟨a,Finset.mem_insert_of_mem ha,by simpa [Function.update_of_ne hap] using hax⟩
            · have hvp : v ≠ p := fun e => isolated v w hvw (e ▸ pA)
              have hwp : w ≠ p := fun e => isolated w v hvw.symm (e ▸ pA)
              exact Or.inr ⟨v,w,hvw,by simpa [Function.update_of_ne hvp] using hvx,
                by simpa [Function.update_of_ne hwp] using hwx⟩
        have bound := ih sA _ u hsmall smaller
        rw [Finset.card_insert_of_notMem hp]
        omega
    exact strip A (fun _ h => h) f s computes has
