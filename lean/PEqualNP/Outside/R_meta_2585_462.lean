import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK PEqualNP.ReadTwo

-- Delete one nonisolated copy; the pin saves the gate needed to restore both labels.
theorem PEqualNP.Outside.R_meta_2585_462
  (pin : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : Circuit) (a : Fin (P+L)),
    IsAO2 (P+L) C → circuitFun (P+L) C = fpl P I →
    (∃ p l, I p l ∧ (Fin.castAdd L p = a ∨ Fin.natAdd P l = a)) →
    (∃ p l, I p l ∧ Fin.castAdd L p ≠ a ∧ Fin.natAdd P l ≠ a) →
    ∃ D : Circuit, IsAO2 (P+L) D ∧ D.size < C.size ∧
      circuitFun (P+L) D = fpl P (fun p l => I p l ∧ Fin.castAdd L p ≠ a ∧ Fin.natAdd P l ≠ a))
  (row : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (a b : Fin P) (D : Circuit),
    a ≠ b → (∀ l, I a l ↔ I b l) → IsAO2 (P+L) D → IsReadK (P+L) D 1 →
    circuitFun (P+L) D = fpl P (fun p l => I p l ∧ p ≠ a) →
    ∃ C : Circuit, IsAO2 (P+L) C ∧ IsReadK (P+L) C 1 ∧ circuitFun (P+L) C = fpl P I ∧ C.size ≤ D.size+1)
  (col : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (a b : Fin L) (D : Circuit),
    a ≠ b → (∀ p, I p a ↔ I p b) → IsAO2 (P+L) D → IsReadK (P+L) D 1 →
    circuitFun (P+L) D = fpl P (fun p l => I p l ∧ l ≠ a) →
    ∃ C : Circuit, IsAO2 (P+L) C ∧ IsReadK (P+L) C 1 ∧ circuitFun (P+L) C = fpl P I ∧ C.size ≤ D.size+1)
  (distinct : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : Circuit), Lin I →
    (∀ a b, (∃ l, I a l) → (∀ l, I a l ↔ I b l) → a=b) →
    (∀ a b, (∃ p, I p a) → (∀ p, I p a ↔ I p b) → a=b) →
    IsAO2 (P+L) C → circuitFun (P+L) C = fpl P I →
    ∃ D : Circuit, IsAO2 (P+L) D ∧ IsReadK (P+L) D 1 ∧ circuitFun (P+L) D = fpl P I ∧ D.size ≤ C.size) :
  ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (P + L) C → (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧ (∀ y : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D y = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 1 := by
  intro P L I dec C sq ao correct
  classical
  have sep (p : Fin P) (l : Fin L) : Fin.castAdd L p ≠ Fin.natAdd P l := by
    intro h; have e := congrArg Fin.val h; change p.val=P+l.val at e; omega
  have solve (s : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : Circuit) (sz : C.size=s)
      (lin : Lin I) (ao : IsAO2 (P+L) C) (hf : circuitFun (P+L) C = fpl P I) :
      ∃ D : Circuit, IsAO2 (P+L) D ∧ IsReadK (P+L) D 1 ∧ circuitFun (P+L) D = fpl P I ∧ D.size ≤ C.size := by
    induction s using Nat.strong_induction_on generalizing I C with
    | ind s ih =>
      have cut (v : Fin (P+L)) (hit : ∃ p l, I p l ∧ (Fin.castAdd L p = v ∨ Fin.natAdd P l = v))
          (miss : ∃ p l, I p l ∧ Fin.castAdd L p ≠ v ∧ Fin.natAdd P l ≠ v) :
          ∃ D : Circuit, IsAO2 (P+L) D ∧ IsReadK (P+L) D 1 ∧
            circuitFun (P+L) D = fpl P (fun p l => I p l ∧ Fin.castAdd L p ≠ v ∧ Fin.natAdd P l ≠ v) ∧ D.size < C.size := by
        let J := fun p l => I p l ∧ Fin.castAdd L p ≠ v ∧ Fin.natAdd P l ≠ v
        have hJ : Lin J := by
          intro p q l k n m bad; exact lin p q l k n m ⟨bad.1.1,bad.2.1.1,bad.2.2.1.1,bad.2.2.2.1⟩
        obtain ⟨B,hB,lt,hfB⟩ := pin P L I C v ao hf hit miss
        obtain ⟨D,hD,hr,hd,le⟩ := ih B.size (lt.trans_eq sz) J B rfl hJ hB hfB
        exact ⟨D,hD,hr,hd,le.trans_lt lt⟩
      by_cases rows : ∃ a b : Fin P, a≠b ∧ (∃ l,I a l) ∧ ∀ l,I a l ↔ I b l
      · obtain ⟨a,b,ne,⟨l,hit⟩,tw⟩ := rows
        obtain ⟨D,ad,rd,ed,lt⟩ := cut (Fin.castAdd L a) ⟨a,l,hit,Or.inl rfl⟩
          ⟨b,l,(tw l).mp hit,fun h => ne (Fin.castAdd_inj.mp h).symm,(sep a l).symm⟩
        have hd : circuitFun (P+L) D = fpl P (fun p l => I p l ∧ p≠a) := by
          rw [ed]; funext z; apply decide_eq_decide.mpr; simp [fun l => (sep a l).symm]
        obtain ⟨E,ae,re,ee,le⟩ := row P L I a b D ne tw ad rd hd
        exact ⟨E,ae,re,ee,by omega⟩
      by_cases cols : ∃ a b : Fin L, a≠b ∧ (∃ p,I p a) ∧ ∀ p,I p a ↔ I p b
      · obtain ⟨a,b,ne,⟨p,hit⟩,tw⟩ := cols
        obtain ⟨D,ad,rd,ed,lt⟩ := cut (Fin.natAdd P a) ⟨p,a,hit,Or.inr rfl⟩
          ⟨p,b,(tw p).mp hit,sep p a,by simpa using ne.symm⟩
        have hd : circuitFun (P+L) D = fpl P (fun p l => I p l ∧ l≠a) := by
          rw [ed]; funext z; apply decide_eq_decide.mpr; simp [fun p => sep p a]
        obtain ⟨E,ae,re,ee,le⟩ := col P L I a b D ne tw ad rd hd
        exact ⟨E,ae,re,ee,by omega⟩
      exact distinct P L I C lin (fun a b hit tw => by_contra fun ne => rows ⟨a,b,ne,hit,tw⟩)
        (fun a b hit tw => by_contra fun ne => cols ⟨a,b,ne,hit,tw⟩) ao hf
  obtain ⟨D,ad,rd,ed,le⟩ := solve C.size I C rfl (fun p q l k n m bad => sq p q l k n m ⟨bad.1,bad.2.2.1,bad.2.1,bad.2.2.2⟩) ao (funext correct)
  exact ⟨D,ad,congrFun ed,le,rd⟩
