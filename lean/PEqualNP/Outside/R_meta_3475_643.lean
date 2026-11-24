import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_3475_643
    (narrow : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
        (E : Finset (Fin N × Fin N)),
      1 ≤ q → (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (N+N) C →
      (∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N+N) C z = false) →
      (∀ e ∈ E, I e.1 e.2 ∧ circuitFun (N+N) C
        (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true) →
      (C.size ≤ 4400 ∨ min (E.image Prod.fst).card (E.image Prod.snd).card ≤ 2200) →
      E.card ≤ 24*C.size)
    (trim : ∀ (n : ℕ) (C : Circuit), IsAO2 n C →
      (∀ u : Fin n, circuitFun n C (fun v => decide (v=u)) = false) →
      (∃ x, circuitFun n C x = true) → ∃ D : Circuit,
      IsAO2 n D ∧ D.size ≤ C.size ∧ D.output+1 = n+D.size ∧
      (∀ x, circuitFun n D x = circuitFun n C x) ∧
      (∀ color p l, lineSingle D n color p l = lineSingle C n color p l))
    (wide : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : Circuit) (E : Finset (Fin N × Fin N)),
      87 ≤ q → N = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (N+N) C →
      (∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N+N) C z = false) →
      let hits := fun (i : Fin (N+N)) (e : Fin N × Fin N) =>
        i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2
      (∀ e ∈ E, I e.1 e.2 ∧ circuitFun (N+N) C (fun i => decide (hits i e)) = true ∧
        lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val) = false ∧
        lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val) = false) →
      (∀ e ∈ E, ∀ i, hits i e → 24 < (E.filter (hits i)).card) →
      4400 < C.size → 2200 < min (E.image Prod.fst).card (E.image Prod.snd).card →
      C.output+1 = N+N+C.size → E.card ≤ 24*C.size) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)),   (87 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →             (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →               let x13 : Fin (x2 + x2) → Fin x2 × Fin x2 → Prop := fun (x13 : Fin (x2 + x2)) (x14 : Fin x2 × Fin x2) => x13 = Fin.castAdd x2 x14.1 ∨ x13 = Fin.natAdd x2 x14.2;               (∀ x14 ∈ x6, x3 x14.1 x14.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x13 x16 x14)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x16 : ℕ) => Decidable.decide (x2 ≤ x16)) (↑x14.1) (x2 + ↑x14.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x16 : ℕ) => Decidable.decide (x16 < x2)) (↑x14.1) (x2 + ↑x14.2) = Bool.false) → (∀ x15 ∈ x6, ∀ (x17 : Fin (x2 + x2)), x13 x17 x15 → (24 : ℕ) < (Finset.filter (x13 x17) x6).card) → x6.card ≤ (24 : ℕ) * x5.size := by
  intro q N I _ C E hq hN cols unique ao sound hits accepted dense
  by_cases empty : E = ∅
  · simp [empty]
  have single (v : Fin (N+N)) : circuitFun (N+N) C (fun i => decide (i=v)) = false := by
    apply sound
    · have one : Subsingleton {l : Fin N // (decide (Fin.natAdd N l = v) : Bool) = true} := by
        constructor
        intro a b
        apply Subtype.ext
        exact (Fin.natAdd_injective N N) ((of_decide_eq_true a.property).trans (of_decide_eq_true b.property).symm)
      exact (Fintype.card_le_one_iff_subsingleton.mpr one).trans (by omega)
    · rintro ⟨p,l,_,hp,hl⟩
      have eq := (of_decide_eq_true hp).trans (of_decide_eq_true hl).symm
      have h : p.val = N+l.val := congrArg (fun i : Fin (N+N) => i.val) eq
      have hn := p.isLt
      omega
  obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  obtain ⟨D,hD,size,last,eval,linear⟩ := trim (N+N) C ao single ⟨_,(accepted e he).2.1⟩
  have soundD x hb hn : circuitFun (N+N) D x = false := (eval x).trans (sound x hb hn)
  have acceptedD (e : Fin N × Fin N) (he : e ∈ E) :
      I e.1 e.2 ∧ circuitFun (N+N) D (fun i => decide (hits i e)) = true ∧
      lineSingle D (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val) = false ∧
      lineSingle D (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val) = false := by
    simpa only [eval,linear] using accepted e he
  have smaller : E.card ≤ 24*D.size := by
    by_cases small : D.size ≤ 4400 ∨ min (E.image Prod.fst).card (E.image Prod.snd).card ≤ 2200
    · exact narrow q N I D E (by omega) unique hD soundD (fun e he => ⟨(acceptedD e he).1,(acceptedD e he).2.1⟩) small
    · exact wide q N I D E hq hN cols unique hD soundD acceptedD dense (by omega) (by omega) last
  exact smaller.trans (Nat.mul_le_mul_left 24 size)
