import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Values on a set of wires can distinguish the witnesses if that set
-- meets the operands of every binary gate of the indicated type.
theorem PEqualNP.Outside.R_meta_4578_392
    (bound : ∀ (n m : ℕ) (C : Circuit) (side : Bool) (S : Finset ℕ) (w : Fin m → Fin n → Bool),
      Monotone2 C → (∀ g∈C.gates, g.op=(if side then GateOp.or else GateOp.and) → g.inputs.length=2 → ∃ i∈g.inputs,i∈S) →
      (∀ a, circuitFun n C (w a)=side) →
      (∀ a b, a≠b → ∃ z : Fin n → Bool, (∀ i, w a i=side → w b i=side → z i=side) ∧ circuitFun n C z≠side) →
      m ≤ 2^S.card)
    (geometry : let I := fun (p l : Fin 13) => p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
      (∃ P L : Fin 704 → Finset (Fin 13),
        (∀ a, ∀ p∈P a, ∀ l∈L a, ¬I p l) ∧
        ∀ a b, a≠b → ∃ p∈P a ∪ P b, ∃ l∈L a ∪ L b, I p l) ∧
      (∃ e : Fin 52 → Fin 13 × Fin 13, Function.Injective e ∧ ∀ a,I (e a).1 (e a).2))
    (remaining : let I := fun (p l : Fin 13) => p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
      let inp := fun (P L : Finset (Fin 13)) (i : Fin 26) => Fin.addCases (fun p : Fin 13 => decide (p∈P)) (fun l : Fin 13 => decide (l∈L)) i
      let cover := fun (op : GateOp) (C : Circuit) (S : Finset ℕ) => ∀ g∈C.gates, g.op=op → g.inputs.length=2 → ∃ i∈g.inputs, i∈S
      ∀ C : Circuit, Monotone2 C → (∀ p l, I p l → circuitFun 26 C (inp {p} {l})=true) →
      (∀ P L, circuitFun 26 C (inp P L)=true → ∃ p∈P,∃ l∈L,I p l) →
      ¬HasLineDegree 26 (Finset.range 13) C 1 → ¬HasLineDegree 26 (Finset.Ico 13 26) C 1 →
      (∀ S,cover .and C S → 10≤S.card) → (∀ S,cover .or C S → 6≤S.card) → 64≤C.size) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset (Fin (13 : ℕ))) => PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x5 : Fin (26 : ℕ)) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x4)) x5; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Prop := fun (x3 x4 : Finset (Fin (13 : ℕ))) => ∃ x5 ∈ x3, ∃ x6 ∈ x4, x1 x5 x6; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 x7 : Fin (13 : ℕ)), x1 x6 x7 → x2 x4 {x6} {x7} = Bool.true) → (∀ (x7 x8 : Finset (Fin (13 : ℕ))), x2 x4 x7 x8 = Bool.true → x3 x7 x8) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x4 (1 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x4 (1 : ℕ) → (64 : ℕ) ≤ x4.size := by
  intro I eval hit C mono pos sound dp dl
  let inp : Finset (Fin 13) → Finset (Fin 13) → Fin 26 → Bool := fun (P L : Finset (Fin 13)) (i : Fin 26) => Fin.addCases (fun p : Fin 13 => decide (p∈P)) (fun l : Fin 13 => decide (l∈L)) i
  obtain ⟨⟨P,L,empty,join⟩,⟨e,inj,flag⟩⟩ := geometry
  apply remaining C mono pos sound dp dl
  · intro S covered
    let w := fun a => inp (P a) (L a)
    have neg (a : Fin 704) : circuitFun 26 C (w a)=false := by
      cases h : circuitFun 26 C (w a) with
      | false => rfl
      | true =>
        obtain ⟨p,hp,l,hl,edge⟩ := sound (P a) (L a) h
        exact (empty a p hp l hl edge).elim
    have sep (a b : Fin 704) (ne : a≠b) :
        ∃ z : Fin 26 → Bool, (∀ i,w a i=false → w b i=false → z i=false) ∧ circuitFun 26 C z≠false := by
      obtain ⟨p,hp,l,hl,edge⟩ := join a b ne
      refine ⟨inp {p} {l},?_,by rw [show circuitFun 26 C (inp {p} {l})=true from pos p l edge]; decide⟩
      intro i
      induction i using Fin.addCases (m:=13) (n:=13) with
      | left j =>
        simp only [w,inp,Fin.addCases_left,decide_eq_false_iff_not,Finset.mem_singleton]
        intro aoff boff eq
        subst j
        exact (Finset.mem_union.mp hp).elim aoff boff
      | right j =>
        simp only [w,inp,Fin.addCases_right,decide_eq_false_iff_not,Finset.mem_singleton]
        intro aoff boff eq
        subst j
        exact (Finset.mem_union.mp hl).elim aoff boff
    have h := bound 26 704 C false S w mono covered neg sep
    by_contra small
    have le : S.card ≤ 9 := by omega
    have pow := Nat.pow_le_pow_right (by decide : 0<2) le
    omega
  · intro S covered
    let w := fun a => inp {(e a).1} {(e a).2}
    have yes (a : Fin 52) : circuitFun 26 C (w a)=true := pos _ _ (flag a)
    have sep (a b : Fin 52) (ne : a≠b) :
        ∃ z : Fin 26 → Bool, (∀ i,w a i=true → w b i=true → z i=true) ∧ circuitFun 26 C z≠true := by
      let A : Finset (Fin 13) := {(e a).1} ∩ {(e b).1}
      let B : Finset (Fin 13) := {(e a).2} ∩ {(e b).2}
      refine ⟨inp A B,?_,?_⟩
      · intro i
        induction i using Fin.addCases (m:=13) (n:=13) with
        | left j =>
          simp only [w,inp,Fin.addCases_left,decide_eq_true_eq]
          exact fun u v => Finset.mem_inter.mpr ⟨u,v⟩
        | right j =>
          simp only [w,inp,Fin.addCases_right,decide_eq_true_eq]
          exact fun u v => Finset.mem_inter.mpr ⟨u,v⟩
      · intro h
        obtain ⟨p,hp,l,hl,_⟩ := sound A B h
        simp [A] at hp
        simp [B] at hl
        exact ne (inj (Prod.ext (hp.1.symm.trans hp.2) (hl.1.symm.trans hl.2)))
    have h := bound 26 52 C true S w mono covered yes sep
    by_contra small
    have le : S.card ≤ 5 := by omega
    have pow := Nat.pow_le_pow_right (by decide : 0<2) le
    omega
