import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_3051_694
    (extract :
      ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit),
      let reads := fun (D : Circuit) (u : Fin (n+n+D.size)) (b : Bool) =>
        (D.gates.getD (u.val-(n+n)) ⟨.and,[]⟩).inputs.getD (if b then 1 else 0) 0
      let hard := fun (D : Circuit) (w : ℕ) =>
        ∀ T : List (List (Fin (n+n))), (T.map List.length).sum ≤ 99 →
          ∃ x : Fin (n+n) → Bool, T.any (fun a => a.all x) ≠ (D.wires (List.ofFn x)).getD w false
      300 ≤ q → n = q^2+q+1 →
      (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → Monotone2 C →
      (∀ p l, I p l → C.eval (incidenceInput {p} {l}) = true) →
      (∀ X Y : Finset (Fin n), Y.card ≤ q → (∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) →
        C.eval (incidenceInput X Y) = false) →
      100*C.size < n*q →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧
        (∀ x, circuitFun (n+n) D x = circuitFun (n+n) C x) ∧
      ∃ w : ℕ, n+n ≤ w ∧ hard D w ∧
      ∃ (u v : Fin (n+n+D.size)) (b c : Bool), n+n ≤ u.val ∧ n+n ≤ v.val ∧
        (u,b) ≠ (v,c) ∧ reads D u b = w ∧ reads D v c = w)
    (restricted :
      ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit),
      let reads := fun (D : Circuit) (u : Fin (n+n+D.size)) (b : Bool) =>
        (D.gates.getD (u.val-(n+n)) ⟨.and,[]⟩).inputs.getD (if b then 1 else 0) 0
      let hard := fun (D : Circuit) (w : ℕ) =>
        ∀ T : List (List (Fin (n+n))), (T.map List.length).sum ≤ 99 →
          ∃ x : Fin (n+n) → Bool, T.any (fun a => a.all x) ≠ (D.wires (List.ofFn x)).getD w false
      300 ≤ q → n = q^2+q+1 →
      (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → Monotone2 C →
      (∀ p l, I p l → C.eval (incidenceInput {p} {l}) = true) →
      (∀ X Y : Finset (Fin n), Y.card ≤ q → (∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) →
        C.eval (incidenceInput X Y) = false) →
      (∃ w : ℕ, n+n ≤ w ∧ hard C w ∧
      ∃ (u v : Fin (n+n+C.size)) (b c : Bool), n+n ≤ u.val ∧ n+n ≤ v.val ∧
        (u,b) ≠ (v,c) ∧ reads C u b = w ∧ reads C v c = w) → n*q ≤ 100*C.size) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q n I inst C big geom line unique mono allPos allNeg
  classical
  let input (X Y : Finset (Fin n)) : Fin (n+n) → Bool :=
    Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
  have translated (D : Circuit) (X Y : Finset (Fin n)) :
      D.eval (incidenceInput X Y) = circuitFun (n+n) D (input X Y) :=
    congrArg D.eval (List.ofFn_fin_append _ _).symm
  have pos (p l : Fin n) (hit : I p l) : C.eval (incidenceInput {p} {l}) = true := by
    rw [translated]
    convert allPos p l hit using 2
    funext i
    have sep (a z : Fin n) : Fin.castAdd n a ≠ Fin.natAdd n z := by
      intro e
      have v := congrArg Fin.val e
      change a.val = n + z.val at v
      omega
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simp only [input,Fin.addCases_left,Finset.mem_singleton,Fin.castAdd_inj,sep,or_false]
    · simp only [input,Fin.addCases_right,Finset.mem_singleton,Fin.natAdd_inj,
        Ne.symm (sep _ _),false_or]
  have neg (X Y : Finset (Fin n)) (small : Y.card ≤ q)
      (free : ∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) : C.eval (incidenceInput X Y) = false := by
    rw [translated]
    apply allNeg
    · simpa only [input,Fin.addCases_right,decide_eq_true_eq,Fintype.card_coe] using small
    · rintro ⟨p,l,hit,onP,onL⟩
      exact free p (by simpa [input] using onP) l (of_decide_eq_true (by simpa only [input,Fin.addCases_right] using onL)) hit
  by_contra! small
  obtain ⟨D,hD,sz,eq,hard⟩ := extract q n I C big geom line unique mono pos neg small
  have eqSets (X Y : Finset (Fin n)) : D.eval (incidenceInput X Y) = C.eval (incidenceInput X Y) := by
    rw [translated,translated,eq]
  have low := restricted q n I D big geom line unique hD
    (fun p l hi => (eqSets {p} {l}).trans (pos p l hi))
    (fun X Y hY hfree => (eqSets X Y).trans (neg X Y hY hfree)) hard
  omega
