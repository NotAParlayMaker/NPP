import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Probe 10 turns off all outside inputs. Each other probe turns on at most one.
-- The edge function of an inside assignment on these eleven probes must be recoverable
-- from the boundary wires evaluated with all outside inputs off.
theorem PEqualNP.Outside.R_meta_4085_11
    (separate :
    let inputs := fun x : Fin 10 → Bool => List.ofFn x ++ [!x 0]
    let splice := fun (S : Finset (Fin 10)) (a z : Fin 10 → Bool) (i : Fin 10) =>
      if i ∈ S then a i else z i
    ∀ (C : Circuit) (S : Finset (Fin 10)) (A B : Finset ℕ),
      (∀ i : Fin 10, i.val ∈ A ↔ i ∈ S) →
      (10 ∈ A ↔ (0 : Fin 10) ∈ S) →
      (∀ t : Fin C.size, ∀ i ∈ (C.gates.get t).inputs,
        (11+t.val ∈ A → i ∈ A) ∧ (11+t.val ∉ A → i ∈ A → i ∈ B)) →
      (C.output ∈ A → C.output ∈ B) →
      ∀ a b z : Fin 10 → Bool,
      (∀ i ∈ B, (C.wires (inputs (splice S a (fun _ => false)))).getD i false =
        (C.wires (inputs (splice S b (fun _ => false)))).getD i false) →
      C.eval (inputs (splice S a z)) = C.eval (inputs (splice S b z)))
    (search :
    let rows : List ℕ := [50,69,138,276,521,385,770,548,104,208]
    let edge := fun x : Fin 10 → Bool => decide
      (∃ a b : Fin 10, x a = true ∧ x b = true ∧ (rows.getD a.val 0).testBit b.val = true)
    let inputs := fun x : Fin 10 → Bool => List.ofFn x ++ [!x 0]
    let probe := fun (S : Finset (Fin 10)) (a : Fin 10 → Bool) (j : Fin 11) (i : Fin 10) =>
      if i ∈ S then a i else decide (i.castSucc = j)
    ∀ C : Circuit, FanInTwo C → C.size ≤ 18 →
      (∀ (S : Finset (Fin 10)) (A B : Finset ℕ),
      (∀ i : Fin 10, i.val ∈ A ↔ i ∈ S) →
      (10 ∈ A ↔ (0 : Fin 10) ∈ S) →
      (∀ t : Fin C.size, ∀ i ∈ (C.gates.get t).inputs,
        (11+t.val ∈ A → i ∈ A) ∧ (11+t.val ∉ A → i ∈ A → i ∈ B)) →
      (C.output ∈ A → C.output ∈ B) →
      (Finset.univ.image (fun a : Fin 10 → Bool => fun j : Fin 11 => edge (probe S a j))).card ≤
        (Finset.univ.image (fun a : Fin 10 → Bool => fun w : ↥B =>
          (C.wires (inputs (probe S a 10))).getD w.val false)).card) →
      ∃ x : Fin 10 → Bool, C.eval (inputs x) ≠ edge x)
    : ∀ C : Circuit, FanInTwo C → C.size ≤ 18 →
      (∀ (S : Finset (Fin 10)) (A B : Finset ℕ),
        (∀ i : Fin 10, i.val ∈ A ↔ i ∈ S) →
        (10 ∈ A ↔ (0 : Fin 10) ∈ S) →
        (∀ t : Fin C.size, ∀ i ∈ (C.gates.get t).inputs,
          (11+t.val ∈ A → i ∈ A) ∧ (11+t.val ∉ A → i ∈ A → i ∈ B)) →
        (C.output ∈ A → C.output ∈ B) →
        ([1,2,4,6,9,12,9,9,5,3,2] : List ℕ).getD S.card 0 ≤
          (Finset.univ.image (fun (x : Fin 10 → Bool) (w : ↥B) =>
            (C.wires (List.ofFn x ++ [!x 0])).getD w.val false)).card) →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) ≠ (fun y : Fin 10 → Bool =>
        decide (∃ a b : Fin 10, y a = true ∧ y b = true ∧
          (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD a.val 0).testBit b.val = true)) x := by
  classical
  let rows : List ℕ := [50,69,138,276,521,385,770,548,104,208]
  let edge := fun x : Fin 10 → Bool => decide
    (∃ a b : Fin 10, x a = true ∧ x b = true ∧ (rows.getD a.val 0).testBit b.val = true)
  let inputs := fun x : Fin 10 → Bool => List.ofFn x ++ [!x 0]
  let splice (S : Finset (Fin 10)) (a z : Fin 10 → Bool) (i : Fin 10) :=
    if i ∈ S then a i else z i
  let probe (S : Finset (Fin 10)) (a : Fin 10 → Bool) (j : Fin 11) (i : Fin 10) :=
    if i ∈ S then a i else decide (i.castSucc = j)
  intro C fan budget _
  change ∃ x : Fin 10 → Bool, C.eval (inputs x) ≠ edge x
  by_contra! correct
  apply (search C fan budget ?_).elim
  · intro x hx
    exact hx (correct x)
  · intro S A B side negSide gates out
    let trace (a : Fin 10 → Bool) (w : ↥B) :=
      (C.wires (inputs (probe S a 10))).getD w.val false
    let behavior (a : Fin 10 → Bool) (j : Fin 11) := edge (probe S a j)
    have off (a : Fin 10 → Bool) : probe S a 10 = splice S a (fun _ => false) := by
      funext i
      have hi : i.castSucc ≠ (10 : Fin 11) := fun h => (Nat.ne_of_lt i.isLt) (congrArg Fin.val h)
      simp [probe,splice,hi]
    have same (a b : Fin 10 → Bool) (eq : trace a = trace b) : behavior a = behavior b := by
      funext j
      have boundary (i : ℕ) (hi : i ∈ B) := congrFun eq ⟨i,hi⟩
      have compare := separate C S A B side negSide gates out a b
        (fun (i : Fin 10) => decide (i.castSucc = j)) (by
          intro i hi
          simpa only [trace,off] using boundary i hi)
      change C.eval (inputs (probe S a j)) = C.eval (inputs (probe S b j)) at compare
      exact (correct _).symm.trans (compare.trans (correct _))
    let traces := Finset.univ.image trace
    let profiles := Finset.univ.image behavior
    have witness (v : ↥profiles) : ∃ a, behavior a = v.val := by
      obtain ⟨a,_,h⟩ := Finset.mem_image.mp v.property
      exact ⟨a,h⟩
    let rep (v : ↥profiles) := Classical.choose (witness v)
    have represents (v : ↥profiles) : behavior (rep v) = v.val := Classical.choose_spec (witness v)
    let encode (v : ↥profiles) : ↥traces :=
      ⟨trace (rep v),Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩⟩
    have inj : Function.Injective encode := by
      intro u v eq
      have tracesEq : trace (rep u) = trace (rep v) := congrArg Subtype.val eq
      exact Subtype.ext ((represents u).symm.trans ((same _ _ tracesEq).trans (represents v)))
    change profiles.card ≤ traces.card
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective encode inj
