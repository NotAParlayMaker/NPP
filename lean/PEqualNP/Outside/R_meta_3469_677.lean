
import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.GenericRejection

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_3469_677
    (orCase :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ g : PEqualNP.CircuitLowerBounds.Gate, x4.gates[x4.output - (x2 + x2)]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size)
    (firstAnd :
      ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit), 200 ≤ q →
      N = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (N+N) C → N+N ≤ C.output → C.output < N+N+C.size →
      (∃ g : Gate, C.gates[C.output-(N+N)]? = some g ∧ g.op = GateOp.and) →
      RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      (let bad (X Y : Finset (Fin N)) := Y.card ≤ q ∧ IsFalseInput S X Y
       let v (w : ℕ) (X Y : Finset (Fin N)) := wireValue C (incidenceInput X Y) w
       ∀ w < C.output, RightOnIncidentPairs S (⟨C.gates,w⟩ : Circuit) →
         ∃ X Y, bad X Y ∧ v w X Y = true ∧
           ∀ U V, bad U V → U.card+V.card < X.card+Y.card → v w U V = false) →
      N*q ≤ 100*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q N S C hq hn hdegree hunique hAO _ hbound _ accept reject
  classical
  let reroot (w : ℕ) : Circuit := ⟨C.gates,w⟩
  let good (w : ℕ) : Prop :=
    RightOnIncidentPairs S (reroot w) ∧
    ∀ X Y, Y.card ≤ q → IsFalseInput S X Y → (reroot w).eval (incidenceInput X Y) = false
  have has : ∃ w, good w := ⟨C.output,accept,reject⟩
  let w := Nat.find has
  have satisfies : good w := Nat.find_spec has
  have earlier : ∀ v < w, ¬ good v := fun v h => Nat.find_min has h
  have wle : w ≤ C.output := Nat.find_min' has ⟨accept,reject⟩
  have valid : w < N+N+C.size := lt_of_le_of_lt wle hbound
  have viewAO : IsAO2 (N+N) (reroot w) := hAO
  have hN : 2 ≤ N := by omega
  have suffix (gs : List Gate) (xs : List Bool) :
      ∃ t, gs.foldl (fun b g => b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]) xs =
        xs ++ t := by
    induction gs generalizing xs with
    | nil => exact ⟨[],by simp⟩
    | cons g gs ih =>
      obtain ⟨t,ht⟩ := ih (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)])
      refine ⟨[g.op.eval (g.inputs.map fun i => xs.getD i false)] ++ t, ?_⟩
      rw [List.foldl_cons, ht, List.append_assoc]
  have eval_raw (j : ℕ) (xs : List Bool) (hj : j < xs.length) :
      (reroot j).eval xs = xs.getD j false := by
    obtain ⟨t, ht⟩ := suffix C.gates xs
    change (C.gates.foldl (fun b g => b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]) xs).getD j false = _
    rw [ht, List.getD_append _ _ _ _ hj]
  have inputLength (X Y : Finset (Fin N)) : (incidenceInput X Y).length = N+N := by
    change (List.ofFn (fun i : Fin N => decide (i ∈ X)) ++
      List.ofFn (fun i : Fin N => decide (i ∈ Y))).length = _
    simp
  have notRaw : N+N ≤ w := by
    by_contra! h
    have pos : RightOnIncidentPairs S (reroot w) := satisfies.1
    by_cases wp : w < N
    · let p : Fin N := ⟨w,wp⟩
      let l : Fin N := ⟨0,by omega⟩
      have other : ∃ x ∈ S l, x ≠ p := by
        by_contra! all
        have sub : S l ⊆ {p} := fun x hx => Finset.mem_singleton.mpr (all x hx)
        have cnt := Finset.card_le_card sub
        rw [hdegree l, Finset.card_singleton] at cnt
        omega
      obtain ⟨x,hx,hxp⟩ := other
      have ev := pos l x hx
      rw [eval_raw _ _ (by rw [inputLength]; omega)] at ev
      change (List.ofFn (fun i : Fin N => decide (i ∈ ({x} : Finset (Fin N)))) ++
        List.ofFn (fun i : Fin N => decide (i ∈ ({l} : Finset (Fin N))))).getD w false = true at ev
      rw [List.getD_append _ _ _ _ (by simpa using wp)] at ev
      simp [wp, p, Ne.symm hxp] at ev
    · let l : Fin N := ⟨w-N,by omega⟩
      obtain ⟨k,hkl⟩ : ∃ k : Fin N, k ≠ l := by
        by_cases v : w-N = 0
        · refine ⟨⟨1,by omega⟩,fun e => ?_⟩
          have eq := congrArg Fin.val e
          change 1 = w-N at eq
          omega
        · refine ⟨⟨0,by omega⟩,fun e => ?_⟩
          have eq := congrArg Fin.val e
          change 0 = w-N at eq
          omega
      obtain ⟨x,hx⟩ : (S k).Nonempty := Finset.card_pos.mp (by rw [hdegree k]; omega)
      have ev := pos k x hx
      rw [eval_raw _ _ (by rw [inputLength]; omega)] at ev
      change (List.ofFn (fun i : Fin N => decide (i ∈ ({x} : Finset (Fin N)))) ++
        List.ofFn (fun i : Fin N => decide (i ∈ ({k} : Finset (Fin N))))).getD w false = true at ev
      rw [List.getD_append_right _ _ _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt wp)] at ev
      have hw : w-N < N := by omega
      simp [hw, l, Ne.symm hkl] at ev
  have gateIndex : w-(N+N) < C.gates.length := by
    change w-(N+N) < C.size
    omega
  let g := C.gates[w-(N+N)]
  have getGate : C.gates[w-(N+N)]? = some g := getElem?_pos C.gates _ gateIndex
  rcases hAO.1 g (List.mem_of_getElem? getGate) with isAnd | isOr
  · apply firstAnd q N S (reroot w) hq hn hdegree hunique viewAO notRaw valid
      ⟨g,getGate,isAnd⟩ satisfies.1 satisfies.2
    dsimp only
    intro j hj positive
    let bad (X Y : Finset (Fin N)) : Prop := Y.card ≤ q ∧ IsFalseInput S X Y
    let f (X Y : Finset (Fin N)) : Bool := (reroot j).eval (incidenceInput X Y)
    have incorrect : ∃ X Y, bad X Y ∧ f X Y = true := by
      by_contra no
      apply earlier j hj
      refine ⟨positive,fun X Y hY hf => ?_⟩
      change f X Y = false
      cases v : f X Y with
      | false => rfl
      | true => exact (no ⟨X,Y,⟨hY,hf⟩,v⟩).elim
    have threshold : ∃ m, ∃ X Y, bad X Y ∧ f X Y = true ∧ X.card+Y.card=m := by
      obtain ⟨X,Y,hb,hy⟩ := incorrect
      exact ⟨_,X,Y,hb,hy,rfl⟩
    obtain ⟨X,Y,hb,hy,hm⟩ := Nat.find_spec threshold
    refine ⟨X,Y,hb,hy,fun U V bu small => ?_⟩
    change f U V = false
    cases v : f U V with
    | false => rfl
    | true =>
      have smaller : U.card+V.card < Nat.find threshold := small.trans_le (le_of_eq hm)
      exact (Nat.find_min threshold smaller ⟨U,V,bu,v,rfl⟩).elim
  · exact orCase q N S (reroot w) hq hn hdegree hunique viewAO notRaw valid
      ⟨g,getGate,isOr⟩ satisfies.1 satisfies.2
