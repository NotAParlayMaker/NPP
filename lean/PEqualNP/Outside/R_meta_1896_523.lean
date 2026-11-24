import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.HeptadCover in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_1896_523
    (normalize :
      ∀ (n : ℕ) (C : Circuit), Monotone2 C →
      ∃ (r : List (List ℕ × List ℕ)) (z : List ℕ),
        r.length ≤ {g : Fin C.gates.length | (C.gates.get g).op = GateOp.or}.ncard ∧
        ∀ x : List Bool, x.length = n →
          C.eval x = z.all (fun i => (r.foldl
            (fun b a => b ++ [a.1.all (fun j => b.getD j false) ||
              a.2.all (fun j => b.getD j false)]) (false :: x)).getD i false))
    (bounded :
      let S (l : Fin 13) : Finset (Fin 13) := {l,l+1,l+3,l+9}
      ∀ (r : List (List ℕ × List ℕ)) (z : List ℕ),
      let f := fun x : List Bool => z.all (fun i => (r.foldl
        (fun b a => b ++ [a.1.all (fun j => b.getD j false) ||
          a.2.all (fun j => b.getD j false)]) (false :: x)).getD i false)
      (∀ l p, p ∈ S l → f (incidenceInput {p} {l}) = true) →
      (∀ X : Finset (Fin 13),
        let Y := missLines S X
        zeroSet S Y = X → InNoLine S X → InNoPencil S Y →
        X.card = 3 ∨ Y.card = 3 → f (incidenceInput X Y) = false) →
      51 ≤ r.length) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → (51 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  classical
  intro C mono yes no
  let S (l : Fin 13) : Finset (Fin 13) := {l,l+1,l+3,l+9}
  have incident (p l : Fin 13) : p ∈ S l ↔
      p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9 := by
    simp only [S,Finset.mem_insert,Finset.mem_singleton]
  obtain ⟨r,z,cost,normalized⟩ := normalize 26 C mono
  let eval (x : List Bool) := z.all (fun i => (r.foldl
    (fun b a => b ++ [a.1.all (fun j => b.getD j false) ||
      a.2.all (fun j => b.getD j false)]) (false::x)).getD i false)
  have agrees (X Y : Finset (Fin 13)) : C.eval (incidenceInput X Y) = eval (incidenceInput X Y) :=
    normalized _ (by change (List.ofFn _ ++ List.ofFn _).length = _; simp)
  let vec (X Y : Finset (Fin 13)) : Fin (13+13) → Bool :=
    Fin.append (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
  have read (X Y : Finset (Fin 13)) : List.ofFn (vec X Y) = incidenceInput X Y :=
    List.ofFn_fin_append _ _
  have separate (p l : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
    intro eq
    have h := congrArg Fin.val eq
    simp only [Fin.val_castAdd,Fin.val_natAdd] at h
    have lt := p.isLt
    omega
  have vp (X Y : Finset (Fin 13)) (p : Fin 13) : vec X Y (Fin.castAdd 13 p) = decide (p ∈ X) :=
    Fin.append_left ..
  have vl (X Y : Finset (Fin 13)) (l : Fin 13) : vec X Y (Fin.natAdd 13 l) = decide (l ∈ Y) :=
    Fin.append_right ..
  have correct (l p : Fin 13) (h : p ∈ S l) : eval (incidenceInput {p} {l}) = true := by
    rw [← agrees,← read]
    have pair : vec {p} {l} = fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l) := by
      funext i
      refine Fin.addCases (motive := fun i => vec {p} {l} i =
        decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) ?_ ?_ i
      · intro a
        rw [vp]
        simp only [Finset.mem_singleton,Fin.castAdd_inj,separate a l,or_false]
      · intro b
        rw [vl]
        simp only [Finset.mem_singleton,Fin.natAdd_inj,Ne.symm (separate p b),false_or]
    rw [pair]
    exact yes p l ((incident p l).mp h)
  have safe (X : Finset (Fin 13)) (closed : zeroSet S (missLines S X) = X)
      (noLine : InNoLine S X) (noPencil : InNoPencil S (missLines S X))
      (_ : X.card = 3 ∨ (missLines S X).card = 3) : eval (incidenceInput X (missLines S X)) = false := by
    let Y := missLines S X
    have lineMem (l : Fin 13) : l ∈ Y ↔ ∀ p ∈ X, ¬p ∈ S l := by
      change l ∈ Finset.univ.filter (fun l => Disjoint (S l) X) ↔ _
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left]
      exact ⟨fun h p pX pL => h pL pX,fun h p pL pX => h p pX pL⟩
    have close (p : Fin 13) (hp : p ∉ X) :
        ∃ l : Fin 13, (∀ a ∈ X, ¬(a = l ∨ a = l+1 ∨ a = l+3 ∨ a = l+9)) ∧
          (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) := by
      have missing : p ∉ zeroSet S Y := by rw [show zeroSet S Y = X from closed]; exact hp
      have witness : ∃ l ∈ Y, p ∈ S l := by
        by_contra! empty
        apply missing
        change p ∈ Finset.univ.filter (fun a => ∀ l ∈ Y, a ∉ S l)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, empty⟩
      obtain ⟨l,hl,inc⟩ := witness
      exact ⟨l,fun a ha => fun h => (lineMem l).mp hl a ha ((incident a l).mpr h),(incident p l).mp inc⟩
    have generic :
        (¬ ∃ l : Fin 13, ∀ p ∈ X, p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧
        ¬ ∃ p : Fin 13, ∀ l : Fin 13,
          (∀ a ∈ X, ¬(a = l ∨ a = l+1 ∨ a = l+3 ∨ a = l+9)) →
          p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9 := by
      refine ⟨?_,?_⟩
      · rintro ⟨l,all⟩
        exact noLine l (fun p hp => (incident p l).mpr (all p hp))
      · rintro ⟨p,all⟩
        exact noPencil p (fun l hl => (incident p l).mpr (all l (fun a ha inc =>
          (lineMem l).mp hl a ha ((incident a l).mpr inc))))
    let recorded (i : Fin (13+13)) := decide
      ((∃ p ∈ X, i = Fin.castAdd 13 p) ∨ ∃ l : Fin 13,
        i = Fin.natAdd 13 l ∧ ∀ p ∈ X, ¬(p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9))
    have vector : vec X Y = recorded := by
      funext i
      refine Fin.addCases (motive := fun i => vec X Y i = recorded i) ?_ ?_ i
      · intro p
        rw [vp]
        simp only [recorded,Fin.castAdd_inj,separate,false_and,exists_false,or_false]
        rw [Bool.eq_iff_iff]
        simp only [decide_eq_true_eq]
        constructor
        · intro hp
          exact ⟨p,hp,rfl⟩
        · rintro ⟨q,hq,rfl⟩
          exact hq
      · intro l
        rw [vl]
        have lbl : l ∈ Y ↔ ∀ p ∈ X, ¬(p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) := by
          simp only [lineMem,incident]
        simp only [recorded,lbl,Ne.symm (separate _ _),and_false,exists_false,false_or,Fin.natAdd_inj]
        rw [Bool.eq_iff_iff]
        simp only [decide_eq_true_eq]
        constructor
        · intro h
          exact ⟨l,rfl,h⟩
        · rintro ⟨k,rfl,h⟩
          exact h
    rw [← agrees,← read]
    change C.eval (List.ofFn (vec X Y)) = false
    rw [vector]
    exact no X close generic
  exact (bounded r z correct safe).trans cost
