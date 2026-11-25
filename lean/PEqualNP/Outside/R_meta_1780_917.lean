import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.CrossAnd

/- Charge the incident singleton pairs lost at a rewrite to the decrease in cross gates.
The subsequent circuit may compute only a subset of the original incident pairs. For every
set of lines Y we still test the input containing all points that those lines miss.
The zero-cross base uses the sound-wire covering argument of L_meta_4592. In a C4-free
plane each of its gate labels can account for at most two surviving incident pairs. -/
theorem PEqualNP.Outside.R_meta_1780_917
    (base : ∀ (N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      (∀ l m, l ≠ m → (S l ∩ S m).card ≤ 1) → Monotone2 C →
      (∀ Y : Finset (Fin N), C.eval (incidenceInput (Finset.univ.filter fun p => ∀ l ∈ Y, p ∉ S l) Y) = false) →
      crossCount (N+N) (Finset.univ.map (Fin.natAddEmb N)) C = 0 →
      ∑ l : Fin N, ((S l).filter fun p => C.eval (incidenceInput {p} {l}) = true).card ≤ 2*C.size)
    (peel : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      199 ≤ q → N=q^2+q+1 → (∀ l, (S l).card=q+1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) → Monotone2 C →
      let M : Finset (Fin (N+N)) := Finset.univ.map (Fin.natAddEmb N)
      let K := crossCount (N+N) M
      let H := fun D : Circuit => ∑ l : Fin N, ((S l).filter fun p => D.eval (incidenceInput {p} {l}) = true).card
      let Z := fun D : Circuit => ∀ Y : Finset (Fin N),
        D.eval (incidenceInput (Finset.univ.filter fun p => ∀ l ∈ Y, p ∉ S l) Y) = false
      Z C → 2*C.size < H C → 0 < K C →
      ∃ j : Fin C.size, IsCrossAnd (N+N) M C j ∧ ∃ ws : List ℕ, ws.length ≤ 2 ∧
        let D : Circuit := ⟨C.gates.set j ⟨.or,ws⟩, C.output⟩
        Z D ∧ K D < K C ∧ H C + 98*K D ≤ H D + 98*K C) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (199 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  classical
  intro q N I _ C hq hN reg plane mono accept sound
  let S := fun l : Fin N => Finset.univ.filter (fun p => I p l)
  have mem (p l : Fin N) : p ∈ S l ↔ I p l := by simp [S]
  have r (l : Fin N) : (S l).card=q+1 := by simpa only [S,Fintype.card_subtype] using reg l
  have uni : ∀ p t : Fin N, p ≠ t → ∃! l, p ∈ S l ∧ t ∈ S l := by simpa only [mem] using plane
  have thin (l m : Fin N) (ne : l ≠ m) : (S l ∩ S m).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp t ht
    by_contra diff
    obtain ⟨k,_,one⟩ := uni p t diff
    obtain ⟨pl,pm⟩ := Finset.mem_inter.mp hp
    obtain ⟨tl,tm⟩ := Finset.mem_inter.mp ht
    exact ne ((one l ⟨pl,tl⟩).trans (one m ⟨pm,tm⟩).symm)
  let M : Finset (Fin (N+N)) := Finset.univ.map (Fin.natAddEmb N)
  let K := crossCount (N+N) M
  let H := fun D : Circuit => ∑ l : Fin N, ((S l).filter fun p => D.eval (incidenceInput {p} {l}) = true).card
  let Z := fun D : Circuit => ∀ Y : Finset (Fin N),
    D.eval (incidenceInput (Finset.univ.filter fun p => ∀ l ∈ Y, p ∉ S l) Y) = false
  have bound : ∀ k D, K D=k → Monotone2 D → Z D → H D ≤ 2*D.size+98*k := by
    intro k; induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro D kval md zd
      by_cases small : H D ≤ 2*D.size
      · omega
      by_cases zero : K D=0
      · have := base N S D thin md zd zero
        change H D ≤ 2*D.size at this
        omega
      obtain ⟨j,_,ws,arity,good,dec,charge⟩ := peel q N S D hq hN r uni md zd (Nat.lt_of_not_ge small) (Nat.pos_of_ne_zero zero)
      let B : Circuit := ⟨D.gates.set j ⟨.or,ws⟩,D.output⟩
      have mb : Monotone2 B := by
        intro g hg
        rcases List.mem_or_eq_of_mem_set hg with old | rfl
        · exact md g old
        · exact ⟨by simp,arity⟩
      have same : B.size=D.size := by
        change (D.gates.set j ⟨.or,ws⟩).length = D.gates.length
        simp
      change Z B at good
      change K B < K D at dec
      change H D + 98*K B ≤ H B + 98*K D at charge
      have tail := ih (K B) (by omega) B rfl mb good
      omega
  have listInput (X Y : Finset (Fin N)) : List.ofFn
      (Fin.append (fun p => decide (p∈X)) (fun l => decide (l∈Y))) = incidenceInput X Y := by
    change List.ofFn _ = List.ofFn (fun p : Fin N => decide (p∈X)) ++ List.ofFn (fun l : Fin N => decide (l∈Y))
    rw [List.ofFn_add]; simp only [Fin.append_left',Fin.append_right]
  have safe : Z C := by
    intro Y
    let X := Finset.univ.filter fun p => ∀ l∈Y, p∉S l
    let x := Fin.append (fun p => decide (p∈X)) (fun l => decide (l∈Y))
    have no : ¬∃ p l, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true := by
      rintro ⟨p,l,inc,hp,hl⟩
      have a : p∈X := by simpa [x,Fin.append_left] using hp
      have b : l∈Y := by simpa only [x,Fin.append_right,decide_eq_true_eq] using hl
      exact (Finset.mem_filter.mp a).2 l b ((mem p l).mpr inc)
    have proof := sound x no
    change C.eval (List.ofFn x)=false at proof
    simpa only [x,listInput] using proof
  have sided (a b : Fin N) : Fin.castAdd N a ≠ Fin.natAdd N b := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castAdd,Fin.val_natAdd] at h'
    omega
  have lit (p l : Fin N) (inc : p ∈ S l) : C.eval (incidenceInput {p} {l})=true := by
    rw [←listInput]
    have eq : Fin.append (fun u : Fin N => decide (u ∈ ({p} : Finset (Fin N))))
        (fun v : Fin N => decide (v ∈ ({l} : Finset (Fin N)))) =
        (fun k => decide (k=Fin.castAdd N p ∨ k=Fin.natAdd N l)) := by
      funext i
      refine Fin.addCases (motive := fun i : Fin (N+N) => _ = decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l)) ?_ ?_ i
      · intro u
        simp only [Fin.append_left,Finset.mem_singleton,Fin.castAdd_inj,sided,or_false]
      · intro v
        simp only [Fin.append_right,Finset.mem_singleton,Fin.natAdd_inj,(sided p v).symm,false_or]
    rw [eq]; exact accept p l ((mem p l).mp inc)
  have sum : H C=N*(q+1) := by
    change (∑ l : Fin N, ((S l).filter _).card)=_
    trans ∑ l : Fin N, (S l).card
    · apply Finset.sum_congr rfl
      intro l _
      rw [Finset.filter_true_of_mem (lit · l ·)]
    · simp [r]
  have cost : K C≤C.size := by
    change ((Finset.range C.gates.length).filter _).card ≤ C.gates.length
    simpa using Finset.card_le_card (Finset.filter_subset _ (Finset.range C.gates.length))
  have priced := bound (K C) C rfl mono safe
  have le : N*q≤N*(q+1) := Nat.mul_le_mul_left N (Nat.le_succ q)
  omega
