import Mathlib
import PEqualNP.Defs

-- A minimum circuit below the target must put two marked AND gates on a dependency path.
-- At all other AND gates a point-only and a line-only witness can be combined without
-- increasing either count. The evaluator, input support and read vectors follow L_meta_1942.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.ReadK PEqualNP.GenericRejection in
set_option maxRecDepth 6000 in
set_option maxHeartbeats 4800000 in
theorem PEqualNP.Outside.R_meta_2870_751
    (coneRule : ∀ (n : ℕ) (C : Circuit) (i j : ℕ), j < C.gates.length →
      (InCone n C i j ↔ ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n+j ∧
        (i = w-n ∨ InCone n C i (w-n))))
    (readLower : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * q ≤ 100 * C.size)
    (nestedMinimum : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)), 200 ≤ q → n = q^2+q+1 →
    (∀ l, (S l).card = q+1) →
    (∀ p p' : Fin n, p ≠ p' → ∃! l : Fin n, p ∈ S l ∧ p' ∈ S l) →
    let admissible := fun (C : Circuit) => IsAO2 (n+n) C ∧ RightOnIncidentPairs S C ∧
      ∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false
    ∀ C : Circuit, admissible C → (∀ D : Circuit, admissible D → C.size ≤ D.size) →
      let test := fun (X : Fin n → Bool) (side bit : Bool) => if side then
        List.replicate n bit ++ List.ofFn X else List.ofFn X ++ List.replicate n bit
      let mark := fun (j : ℕ) => (gateAt C j).op = .and ∧ ∃ s : Bool, ∀ w ∈ (gateAt C j).inputs,
        ∃ X : Fin n → Bool, wireValue C (test X s false) w ≠ wireValue C (test X s true) w
      (∃ i j : Fin C.size, InCone (n+n) C i j ∧ mark i ∧ mark j) → n*q ≤ 100*C.size)
    : have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → ∀ x16 ⊆ Finset.range x6.size, (1 : ℕ) ≤ x16.card → (∀ (x19 : ℕ) (x20 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x19]? = Option.some x20 → (x19 ∈ x16 ↔ x1 x3 x6 x20)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size := by
  classical
  have eval_and (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have eval_or (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have size_eq (c : Circuit) : c.size = c.gates.length := rfl
  have cap2 (u v : List ℕ) : capAdd 2 u v =
      List.zipWith (fun a b => min (a+b) 3) u v := rfl
  have and2 (A B : List (List ℕ)) : andStep 2 A B =
      (A.flatMap fun u => B.map fun v => capAdd 2 u v).foldl insertNew [] := rfl
  have leaf2 (S : List ℕ) (i : ℕ) : leafVectors S 2 i =
      (if i ∈ S then [S.map fun j => if j = i then min 1 (2+1) else 0] else []) := rfl
  let evalFrom {α : Type} (d : α) (op : GateOp → List α → α) (gates : List Gate) (xs : List α) :
      List α :=
    gates.foldl (fun u g => u ++ [op g.op (g.inputs.map fun i => u.getD i d)]) xs

  have evalFrom_cons {α : Type} (d : α) (op : GateOp → List α → α) (g : Gate) (gs : List Gate)
      (xs : List α) :
      evalFrom d op (g :: gs) xs = evalFrom d op gs
        (xs ++ [op g.op (g.inputs.map fun i => xs.getD i d)]) := rfl

  have evalFrom_length {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
      (xs : List α) : (evalFrom d op gs xs).length = xs.length + gs.length := by
    induction gs generalizing xs with
    | nil => simp [evalFrom]
    | cons g gs ih => rw [evalFrom_cons, ih]; simp; omega

  have evalFrom_input {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
      (xs : List α) (i : ℕ) (hi : i < xs.length) :
      (evalFrom d op gs xs).getD i d = xs.getD i d := by
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      rw [evalFrom_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

  let row (C : Circuit) (k : Fin C.size) : Gate := C.gates[k.val]'k.isLt

  let operand (C : Circuit) (k : Fin C.size) (b : Fin 2) : ℕ :=
    (row C k).inputs.getD b.val 0

  let outWire (n : ℕ) {s : ℕ} (k : Fin s) : ℕ := n + k.val

  have inputs_two {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
      (row C k).inputs = [operand C k 0, operand C k 1] := by
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h.2.2 (row C k) (List.getElem_mem _))
    simp [operand, hab]

  have op_kind {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
      (row C k).op = GateOp.and ∨ (row C k).op = GateOp.or :=
    h.1 (row C k) (List.getElem_mem _)

  have earlier {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
      (k : Fin C.size) (b : Fin 2) : operand C k b < outWire n k := by
    have he : gateAt C k.val = row C k := List.getD_eq_getElem _ _ k.isLt
    have hm : operand C k b ∈ (row C k).inputs := by
      rw [inputs_two h k]
      fin_cases b <;> simp
    exact h.2.1 k.val k.isLt (operand C k b) (by simpa only [he] using hm)

  have evalFrom_gate {α : Type} (d : α) (op : GateOp → List α → α) {n : ℕ}
      {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (xs : List α) (hx : xs.length = n)
      (k : Fin C.size) :
      (evalFrom d op C.gates xs).getD (outWire n k) d =
        op (row C k).op ([(evalFrom d op C.gates xs).getD (operand C k 0) d,
          (evalFrom d op C.gates xs).getD (operand C k 1) d]) := by
    let front := evalFrom d op (C.gates.take k.val) xs
    have hf : front.length = outWire n k := by
      have hk : k.val ≤ C.gates.length := k.isLt.le
      simp [front, evalFrom_length, hx, outWire, Nat.min_eq_left hk]
    have hsplit : evalFrom d op C.gates xs =
        evalFrom d op (row C k :: C.gates.drop (k.val + 1)) front := by
      simp only [front, row, evalFrom, ← List.foldl_append, ← List.drop_eq_getElem_cons k.isLt,
        List.take_append_drop]
    have hread (i : ℕ) (hi : i < outWire n k) :
        (evalFrom d op C.gates xs).getD i d = front.getD i d := by
      rw [hsplit, evalFrom_input _ _ _ _ _ (by simpa only [hf] using hi)]
    change (evalFrom d op C.gates xs).getD (outWire n k) d = _
    rw [hread _ (earlier h k 0), hread _ (earlier h k 1), hsplit, evalFrom_cons]
    rw [evalFrom_input _ _ _ _ _ (by simp; omega)]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hf, inputs_two h k]

  have wire_cases (n s w : ℕ) :
      w < n ∨ (∃ k : Fin s, w = outWire n k) ∨ n + s ≤ w := by
    by_cases hb : w < n
    · exact Or.inl hb
    by_cases he : w < n + s
    · exact Or.inr (Or.inl ⟨⟨w - n, by omega⟩, by simp [outWire]; omega⟩)
    · exact Or.inr (Or.inr (by omega))

  let wordOp (o : GateOp) (xs : List (Set (List ℕ))) : Set (List ℕ) :=
    GateOp.rec (motive := fun _ => Set (List ℕ))
      {t | ∃ u ∈ xs.getD 0 ∅, ∃ v ∈ xs.getD 1 ∅, t = u ++ v}
      (xs.getD 0 ∅ ∪ xs.getD 1 ∅) ∅ (fun _ => ∅) ∅ o
  have wordAnd (A B : Set (List ℕ)) : wordOp .and [A,B] =
      {t | ∃ u ∈ A, ∃ v ∈ B, t = u++v} := rfl
  have wordOr (A B : Set (List ℕ)) : wordOp .or [A,B] = A ∪ B := rfl

  let wordList (n : ℕ) (C : Circuit) : List (Set (List ℕ)) :=
    evalFrom ∅ wordOp C.gates (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ))))

  let words (n : ℕ) (C : Circuit) (w : ℕ) : Set (List ℕ) :=
    (wordList n C).getD w ∅

  have words_input {n : ℕ} (C : Circuit) {w : ℕ} (hw : w < n) :
      words n C w = {[w]} := by
    unfold words wordList
    have hi : w < (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ)))).length := by
      simpa using hw
    rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
    simp

  have words_missing (n : ℕ) (C : Circuit) {w : ℕ} (hw : n + C.size ≤ w) :
      words n C w = ∅ :=
    List.getD_eq_default _ _ (by simpa [wordList, evalFrom_length, size_eq] using hw)

  have words_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
      words n C (outWire n k) =
        wordOp (row C k).op [words n C (operand C k 0), words n C (operand C k 1)] :=
    evalFrom_gate _ _ h _ List.length_ofFn k

  let circuitValue {n : ℕ} (C : Circuit) (z : Fin n → Bool) (w : ℕ) : Bool :=
    (evalFrom false GateOp.eval C.gates (List.ofFn z)).getD w false

  have value_input {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ} (hw : w < n) :
      circuitValue C z w = z ⟨w, hw⟩ := by
    have hi : w < (List.ofFn z).length := by simpa using hw
    unfold circuitValue
    rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
    simp

  have value_missing {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ}
      (hw : n + C.size ≤ w) : circuitValue C z w = false :=
    List.getD_eq_default _ _ (by simpa [evalFrom_length, size_eq] using hw)

  have value_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
      (z : Fin n → Bool) (k : Fin C.size) :
      circuitValue C z (outWire n k) = (row C k).op.eval
        [circuitValue C z (operand C k 0), circuitValue C z (operand C k 1)] :=
    evalFrom_gate _ _ h _ List.length_ofFn k

  have value_eq_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
      (z : Fin n → Bool) (w : ℕ) :
      circuitValue C z w = true ↔
        ∃ t ∈ words n C w, ∀ i ∈ t, ∃ a : Fin n, a.val = i ∧ z a = true := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
      · rw [value_input C z hb, words_input C hb]
        constructor
        · intro ht
          exact ⟨[w], rfl, fun i hi => ⟨⟨w, hb⟩, by simpa only [List.mem_singleton, eq_comm] using hi, ht⟩⟩
        · rintro ⟨t, ht, hp⟩
          have ht' : t = [w] := ht
          obtain ⟨a, ha, hz⟩ := hp w (by simp [ht'])
          exact (Fin.ext ha : a = ⟨w, hb⟩) ▸ hz
      · have h1 := ih _ (earlier h k 0)
        have h2 := ih _ (earlier h k 1)
        rw [value_gate h z k, words_gate h k]
        rcases op_kind h k with ho | ho
        · rw [ho]
          simp only [eval_and, List.all_cons, List.all_nil, id_eq, Bool.and_true,
            Bool.and_eq_true, wordAnd, Set.mem_ofPred_eq, h1, h2]
          constructor
          · rintro ⟨⟨t, ht, htz⟩, ⟨u, hu, huz⟩⟩
            exact ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, fun i hi =>
              (List.mem_append.mp hi).elim (htz i) (huz i)⟩
          · rintro ⟨_, ⟨t, ht, u, hu, rfl⟩, hh⟩
            exact ⟨⟨t, ht, fun i hi => hh i (List.mem_append_left _ hi)⟩,
              ⟨u, hu, fun i hi => hh i (List.mem_append_right _ hi)⟩⟩
        · rw [ho]
          simp only [eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false,
            Bool.or_eq_true, wordOr, Set.mem_union, h1, h2]
          constructor
          · rintro (⟨t, ht, ha⟩ | ⟨t, ht, ha⟩)
            · exact ⟨t, Or.inl ht, ha⟩
            · exact ⟨t, Or.inr ht, ha⟩
          · rintro ⟨t, ht | ht, ha⟩
            · exact Or.inl ⟨t, ht, ha⟩
            · exact Or.inr ⟨t, ht, ha⟩
      · simp [value_missing C z hb, words_missing n C hb]


  have mem_insertNew (a v : List ℕ) (A : List (List ℕ)) :
      v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
    unfold insertNew
    by_cases ha : a ∈ A
    · simp [ha, or_iff_left_of_imp (fun (e : v = a) => e.symm ▸ ha)]
    · simp [ha]

  have mem_fold_insertNew (v : List ℕ) (B A : List (List ℕ)) :
      v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
    induction B generalizing A with
    | nil => simp
    | cons b B ih => simp [ih, mem_insertNew, or_assoc]

  have mem_andStep_two (v : List ℕ) (A B : List (List ℕ)) :
      v ∈ andStep 2 A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd 2 u w := by
    simp [and2, mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]

  let encode (S t : List ℕ) : List ℕ :=
    S.map fun j => min (t.count j) 3

  have encode_nil (S : List ℕ) : encode S [] = S.map (fun _ => 0) := by
    simp [encode]

  have encode_append (S t u : List ℕ) :
      capAdd 2 (encode S t) (encode S u) = encode S (t ++ u) := by
    induction S with
    | nil => rfl
    | cons a S ih =>
      simp only [encode, cap2, List.map_cons, List.zipWith_cons_cons, List.count_append] at ih ⊢
      rw [ih]
      congr 1
      omega

  let readOp (S : List ℕ) (o : GateOp) (ins : List (List (List ℕ))) : List (List ℕ) :=
    GateOp.rec (motive := fun _ => List (List ℕ))
      (ins.foldl (andStep 2) [S.map fun _ => 0])
      (ins.foldl (fun acc A => A.foldl insertNew acc) []) [] (fun _ => []) [] o

  let vecs (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) : List (List ℕ) :=
    ((readVectors C n S 2).getD w [])

  have vec_eval (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) :
      vecs n C S w =
        (evalFrom [] (readOp S) C.gates ((List.range n).map (leafVectors S 2))).getD w [] :=
    by
      apply congrArg (fun R : List (List (List ℕ)) => R.getD w [])
      apply congrArg (fun f => C.gates.foldl f ((List.range n).map (leafVectors S 2)))
      funext R g
      obtain ⟨o,ins⟩ := g
      cases o <;> rfl

  -- A supported proof word also produces the corresponding capped read vector.
  have word_to_vector {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
      (S : List ℕ) (w : ℕ) (t : List ℕ) (ht : t ∈ words n C w)
      (hs : ∀ i ∈ t, i ∈ S) : encode S t ∈ vecs n C S w := by
    induction w using Nat.strong_induction_on generalizing t with
    | ind w ih =>
      rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
      · rw [words_input C hb] at ht
        obtain rfl : t = [w] := ht
        have hws := hs w (by simp)
        have hi : w < ((List.range n).map (leafVectors S 2)).length := by simpa using hb
        rw [vec_eval, evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
        simp only [List.getElem_map, List.getElem_range, leaf2, hws, ite_true, List.mem_singleton]
        unfold encode
        apply List.map_congr_left
        intro a _
        by_cases he : a = w
        · simp [he]
        · simp [he, Ne.symm he]
      · have hlen : ((List.range n).map (leafVectors S 2)).length = n := by simp
        have hvec := evalFrom_gate ([] : List (List ℕ)) (readOp S) h _ hlen k
        rw [← vec_eval, ← vec_eval, ← vec_eval] at hvec
        rw [hvec]
        rw [words_gate h k] at ht
        rcases op_kind h k with ho | ho
        · rw [ho] at ht ⊢
          obtain ⟨u, hu, v, hv, rfl⟩ := ht
          have h₁ := ih _ (earlier h k 0) u hu (fun i hi => hs i (List.mem_append_left v hi))
          have h₂ := ih _ (earlier h k 1) v hv (fun i hi => hs i (List.mem_append_right u hi))
          apply (mem_andStep_two _ _ _).mpr
          refine ⟨encode S u, ?_, encode S v, h₂, (encode_append S u v).symm⟩
          apply (mem_andStep_two _ _ _).mpr
          refine ⟨encode S [], by simp [encode_nil], encode S u, h₁, ?_⟩
          simp [encode_append]
        · rw [ho] at ht ⊢
          change _ ∈ (vecs n C S (operand C k 1)).foldl insertNew
            ((vecs n C S (operand C k 0)).foldl insertNew [])
          rw [mem_fold_insertNew, mem_fold_insertNew]
          rcases ht with ht | ht
          · exact Or.inl (Or.inr (ih _ (earlier h k 0) t ht hs))
          · exact Or.inr (ih _ (earlier h k 1) t ht hs)
      · rw [words_missing n C hb] at ht
        exact False.elim ht

  let value {N : ℕ} (C : Circuit) (w : ℕ) (X Y : Fin N → Bool) : Bool :=
    circuitValue C (Fin.append X Y) w

  let lineSensitive {N : ℕ} (C : Circuit) (w : ℕ) : Prop :=
    ∃ X : Fin N → Bool, value C w X (fun _ => false) ≠ value C w X (fun _ => true)

  let pointSensitive {N : ℕ} (C : Circuit) (w : ℕ) : Prop :=
    ∃ Y : Fin N → Bool, value C w (fun _ => false) Y ≠ value C w (fun _ => true) Y

  let overlap (N : ℕ) (C : Circuit) (k : Fin C.size) : Prop :=
    (lineSensitive (N := N) C (operand C k 0) ∧ lineSensitive (N := N) C (operand C k 1)) ∨
    (pointSensitive (N := N) C (operand C k 0) ∧ pointSensitive (N := N) C (operand C k 1))

  let Supported {N : ℕ} (X Y : Fin N → Bool) (t : List ℕ) : Prop :=
    ∀ i ∈ t, ∃ a : Fin (N+N), a.val = i ∧ Fin.append X Y a = true

  let pts (N : ℕ) (t : List ℕ) := t.filter (fun i => decide (i < N))
  let lns (N : ℕ) (t : List ℕ) := t.filter (fun i => decide (N ≤ i))

  have pts_append (N : ℕ) (u v : List ℕ) : pts N (u++v) = pts N u ++ pts N v := List.filter_append u v
  have lns_append (N : ℕ) (u v : List ℕ) : lns N (u++v) = lns N u ++ lns N v := List.filter_append u v

  have support_mono {N : ℕ} {X Y X' Y' : Fin N → Bool} {t : List ℕ}
      (hx : ∀ i, X i = true → X' i = true) (hy : ∀ i, Y i = true → Y' i = true)
      (ht : Supported X Y t) : Supported X' Y' t := by
    intro i hi
    obtain ⟨a, ha, hv⟩ := ht i hi
    refine ⟨a, ha, ?_⟩
    induction a using Fin.addCases with
    | left p => simpa using hx p (by simpa using hv)
    | right l => simpa only [Fin.append_right] using hy l (by simpa only [Fin.append_right] using hv)

  have value_mono {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N+N) C)
      (w : ℕ) {X Y X' Y' : Fin N → Bool}
      (hx : ∀ i, X i = true → X' i = true) (hy : ∀ i, Y i = true → Y' i = true)
      (hv : value C w X Y = true) : value C w X' Y' = true := by
    obtain ⟨t, ht, hs⟩ := (value_eq_terms h _ w).mp hv
    exact (value_eq_terms h _ w).mpr ⟨t, ht, support_mono hx hy hs⟩

  have extreme {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
      (b : Bool) (w : ℕ) (hw : w < n + C.size) : circuitValue C (fun _ : Fin n => b) w = b := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
      · exact value_input C _ hb
      · have ha := earlier h k 0
        have hb := earlier h k 1
        rw [value_gate h _ k, ih _ ha (by omega), ih _ hb (by omega)]
        rcases op_kind h k with ho | ho <;> rw [ho] <;> cases b <;> rfl
      · omega

  have append_const {N : ℕ} (b : Bool) :
      Fin.append (fun _ : Fin N => b) (fun _ : Fin N => b) = fun _ => b := by
    funext a
    induction a using Fin.addCases <;> simp only [Fin.append_left, Fin.append_right]

  have some_sensitivity {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N+N) C)
      {w : ℕ} (hw : w < N+N+C.size) : pointSensitive (N := N) C w ∨ lineSensitive (N := N) C w := by
    by_cases hp : pointSensitive (N := N) C w
    · exact Or.inl hp
    · right
      refine ⟨fun _ => true, ?_⟩
      have he : value C w (fun _ : Fin N => false) (fun _ => false) =
          value C w (fun _ => true) (fun _ => false) :=
        of_not_not (fun hn => hp ⟨_, hn⟩)
      rw [← he]
      simp only [value, append_const, extreme h _ _ hw]
      decide

  have mono_point_pure {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N+N) C)
      {w : ℕ} (hl : ¬lineSensitive (N := N) C w) (X Y : Fin N → Bool)
      (hv : value C w X Y = true) : value C w X (fun _ => false) = true := by
    have he : value C w X (fun _ => false) = value C w X (fun _ => true) :=
      of_not_not (fun hn => hl ⟨X, hn⟩)
    exact he.trans (value_mono h w (fun _ => id) (fun _ _ => rfl) hv)

  have mono_line_pure {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N+N) C)
      {w : ℕ} (hp : ¬pointSensitive (N := N) C w) (X Y : Fin N → Bool)
      (hv : value C w X Y = true) : value C w (fun _ => false) Y = true := by
    have he : value C w (fun _ => false) Y = value C w (fun _ => true) Y :=
      of_not_not (fun hn => hp ⟨Y, hn⟩)
    exact he.trans (value_mono h w (fun _ _ => rfl) (fun _ => id) hv)

  have support_no_lines {N : ℕ} {X : Fin N → Bool} {t : List ℕ}
      (hs : Supported X (fun _ => false) t) : lns N t = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro i hi
    obtain ⟨a, rfl, ha⟩ := hs i hi
    induction a using Fin.addCases with
    | left p => simp [Fin.val_castAdd, p.isLt]
    | right l => simp only [Fin.append_right, Bool.false_eq_true] at ha

  have support_no_points {N : ℕ} {Y : Fin N → Bool} {t : List ℕ}
      (hs : Supported (fun _ => false) Y t) : pts N t = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro i hi
    obtain ⟨a, rfl, ha⟩ := hs i hi
    induction a using Fin.addCases with
    | left p => simp at ha
    | right l => simp

  let Bounded {N : ℕ} (C : Circuit) (w d : ℕ) (X Y : Fin N → Bool) : Prop :=
    ∃ t ∈ words (N+N) C w, Supported X Y t ∧ (pts N t).length ≤ d ∧ (lns N t).length ≤ d

  have comb {N : ℕ} {X Y : Fin N → Bool} {u v : List ℕ}
      (hu : Supported X Y u) (hv : Supported X Y v) : Supported X Y (u++v) :=
    fun i hi => (List.mem_append.mp hi).elim (hu i) (hv i)

  have bounded_words {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N+N) C)
      (d : ℕ → ℕ) (hpos : ∀ w, 1 ≤ d w)
      (hedge : ∀ k b, d (operand C k b) ≤ d (outWire (N+N) k))
      (hbad : ∀ k, (row C k).op = .and → overlap N C k →
        d (operand C k 0) + d (operand C k 1) ≤ d (outWire (N+N) k))
      (w : ℕ) (X Y : Fin N → Bool) (hv : value C w X Y = true) : Bounded C w (d w) X Y := by
    classical
    induction w using Nat.strong_induction_on generalizing X Y with
    | ind w ih =>
      rcases wire_cases (N+N) C.size w with hb | ⟨k, rfl⟩ | hb
      · refine ⟨[w], ?_, ?_, ?_, ?_⟩
        · rw [words_input C hb]; rfl
        · intro i hi
          have eq : i = w := by simpa using hi
          subst i
          exact ⟨⟨w,hb⟩, rfl, (value_input C _ hb).symm.trans hv⟩
        · exact (List.length_filter_le ..).trans (hpos w)
        · exact (List.length_filter_le ..).trans (hpos w)
      · have ha := earlier h k 0
        have hb := earlier h k 1
        change circuitValue C (Fin.append X Y) (outWire (N+N) k) = true at hv
        rw [value_gate h _ k] at hv
        have H₁ := hedge k 0
        have H₂ := hedge k 1
        rcases op_kind h k with ho | ho
        · rw [ho] at hv
          have hab : value C (operand C k 0) X Y = true ∧ value C (operand C k 1) X Y = true := by
            simpa [value, eval_and, eval_or] using hv
          have join (u v : List ℕ) (hu : u ∈ words (N+N) C (operand C k 0))
              (hv' : v ∈ words (N+N) C (operand C k 1)) :
              u++v ∈ words (N+N) C (outWire (N+N) k) := by
            rw [words_gate h k, ho]; exact ⟨u, hu, v, hv', rfl⟩
          by_cases hconf : overlap N C k
          · obtain ⟨u,hu,su,pu,lu⟩ := ih _ ha X Y hab.1
            obtain ⟨v,hv',sv,pv,lv⟩ := ih _ hb X Y hab.2
            have H := hbad k ho hconf
            refine ⟨u++v, join u v hu hv', comb su sv, ?_, ?_⟩
            · simpa [pts] using (le_trans (Nat.add_le_add pu pv) H)
            · simpa [lns] using (le_trans (Nat.add_le_add lu lv) H)
          · have ha' : operand C k 0 < N+N+C.size := by unfold outWire at ha; have := k.isLt; omega
            have hb' : operand C k 1 < N+N+C.size := by unfold outWire at hb; have := k.isLt; omega
            have sa := some_sensitivity h ha'
            have sb := some_sensitivity h hb'
            unfold overlap at hconf
            rcases sa with sa | sa
            · have ap : ¬pointSensitive (N := N) C (operand C k 1) := fun sp => hconf (Or.inr ⟨sa,sp⟩)
              have bl := sb.resolve_left ap
              have al : ¬lineSensitive (N := N) C (operand C k 0) := fun sl => hconf (Or.inl ⟨sl,bl⟩)
              obtain ⟨u,hu,su,pu,_⟩ := ih _ ha X _ (mono_point_pure h al X Y hab.1)
              obtain ⟨v,hv',sv,_,lv⟩ := ih _ hb _ Y (mono_line_pure h ap X Y hab.2)
              have u0 := support_no_lines su
              have v0 := support_no_points sv
              refine ⟨u++v, join u v hu hv', comb (support_mono (fun _ => id) (by simp) su)
                (support_mono (by simp) (fun _ => id) sv), ?_, ?_⟩
              · simpa [pts_append, v0] using pu.trans H₁
              · simpa [lns_append, u0] using lv.trans H₂
            · have bl : ¬lineSensitive (N := N) C (operand C k 1) := fun sl => hconf (Or.inl ⟨sa,sl⟩)
              have bp := sb.resolve_right bl
              have ap : ¬pointSensitive (N := N) C (operand C k 0) := fun sp => hconf (Or.inr ⟨sp,bp⟩)
              obtain ⟨u,hu,su,_,lu⟩ := ih _ ha _ Y (mono_line_pure h ap X Y hab.1)
              obtain ⟨v,hv',sv,pv,_⟩ := ih _ hb X _ (mono_point_pure h bl X Y hab.2)
              have u0 := support_no_points su
              have v0 := support_no_lines sv
              refine ⟨u++v, join u v hu hv', comb (support_mono (by simp) (fun _ => id) su)
                (support_mono (fun _ => id) (by simp) sv), ?_, ?_⟩
              · simpa [pts_append, u0] using pv.trans H₂
              · simpa [lns_append, v0] using lu.trans H₁
        · rw [ho] at hv
          have hor : value C (operand C k 0) X Y = true ∨ value C (operand C k 1) X Y = true := by
            simpa [value, eval_and, eval_or] using hv
          rcases hor with za | zb
          · obtain ⟨t,ht,hs,hp,hl⟩ := ih _ ha X Y za
            refine ⟨t, ?_, hs, hp.trans H₁, hl.trans H₁⟩
            rw [words_gate h k, ho]; exact Or.inl ht
          · obtain ⟨t,ht,hs,hp,hl⟩ := ih _ hb X Y zb
            refine ⟨t, ?_, hs, hp.trans H₂, hl.trans H₂⟩
            rw [words_gate h k, ho]; exact Or.inr ht
      · have he := value_missing C (Fin.append X Y) hb
        exact False.elim (Bool.false_ne_true (he.symm.trans hv))

  have count_bound {N b : ℕ} {t : List ℕ} (hp : (pts N t).length ≤ b)
      (hl : (lns N t).length ≤ b) (i : ℕ) : t.count i ≤ b := by
    by_cases hi : i < N
    · have he : (pts N t).count i = t.count i := List.count_filter (by simpa using hi)
      exact he ▸ List.count_le_length.trans hp
    · have he : (lns N t).count i = t.count i := List.count_filter (by simp [Nat.le_of_not_gt hi])
      exact he ▸ List.count_le_length.trans hl

  let lineSet (N : ℕ) (t : List ℕ) : Finset (Fin N) :=
    Finset.univ.filter (fun l => N+l.val ∈ t)

  have lineSet_card (N : ℕ) (t : List ℕ) :
      (lineSet N t).card ≤ (lns N t).length := by
    let f : Fin N → ℕ := fun l => N+l.val
    have inj : Function.Injective f := by intro a b he; apply Fin.ext; exact Nat.add_left_cancel he
    have sub : (lineSet N t).image f ⊆ (lns N t).toFinset := by
      intro i hi
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hi
      have hm : N+l.val ∈ t := (Finset.mem_filter.mp hl).2
      simp [f, lns, hm]
    rw [← Finset.card_image_of_injective (lineSet N t) inj]
    exact (Finset.card_le_card sub).trans (List.toFinset_card_le _)

  have support_lineSet {N : ℕ} {X Y : Fin N → Bool} {t : List ℕ} (ht : Supported X Y t) :
      Supported X (fun l => decide (l ∈ lineSet N t)) t := by
    intro i hi
    obtain ⟨a, ha, hv⟩ := ht i hi
    refine ⟨a, ha, ?_⟩
    induction a using Fin.addCases with
    | left p => simpa using hv
    | right l =>
      have hm : N+l.val ∈ t := by simpa only [← ha, Fin.val_natAdd] using hi
      simp only [Fin.append_right, lineSet, Finset.mem_filter, Finset.mem_univ, true_and, hm, decide_true]

  have selected_line {N : ℕ} {X Y : Fin N → Bool} {t : List ℕ} (ht : Supported X Y t)
      (l : Fin N) (hm : l ∈ lineSet N t) : Y l = true := by
    obtain ⟨a, ha, hv⟩ := ht _ (Finset.mem_filter.mp hm).2
    obtain rfl : a = Fin.natAdd N l := Fin.ext ha
    simpa only [Fin.append_right] using hv

  have raw_mono {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
      {z z' : Fin n → Bool} (hz : ∀ i, z i = true → z' i = true)
      (hc : circuitFun n C z = true) : circuitFun n C z' = true := by
    obtain ⟨t, ht, hs⟩ := (value_eq_terms h z C.output).mp hc
    apply (value_eq_terms h z' C.output).mpr
    refine ⟨t, ht, fun i hi => ?_⟩
    obtain ⟨a, ha, hv⟩ := hs i hi
    exact ⟨a, ha, hz a hv⟩

  have exact_read_two {N q : ℕ} {C : Circuit} (I : Fin N → Fin N → Prop) [DecidableRel I]
      (h : PEqualNP.TopForm.IsAO2 (N+N) C) (hq : 2 ≤ q)
      (accept : ∀ p l, I p l → circuitFun (N+N) C (fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l)) = true)
      (reject : ∀ z : Fin (N+N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬∃ p l, I p l ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N l)=true) →
        circuitFun (N+N) C z = false)
      (bounded : ∀ X Y : Fin N → Bool, value C C.output X Y = true → Bounded C C.output 2 X Y) :
      (∀ z, circuitFun (N+N) C z = decide (∃ p l, I p l ∧ z (Fin.castAdd N p)=true ∧
        z (Fin.natAdd N l)=true)) ∧ IsReadK (N+N) C 2 := by
    classical
    constructor
    · intro z
      by_cases e : ∃ p l, I p l ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N l)=true
      · rw [decide_eq_true e]
        obtain ⟨p,l,hi,hp,hl⟩ := e
        apply raw_mono h _ (accept p l hi)
        intro i hit
        rcases of_decide_eq_true hit with rfl | rfl
        · exact hp
        · exact hl
      · rw [decide_eq_false e]
        apply Bool.eq_false_iff.mpr
        intro hz
        let X (p : Fin N) := z (Fin.castAdd N p)
        let Y (l : Fin N) := z (Fin.natAdd N l)
        have hz' : value C C.output X Y = true := by
          unfold value
          rw [show Fin.append X Y = z from Fin.append_castAdd_natAdd]
          exact hz
        obtain ⟨t, ht, hs, _, hl⟩ := bounded X Y hz'
        let Y' (l : Fin N) := decide (l ∈ lineSet N t)
        have small : Fintype.card {l : Fin N // Fin.append X Y' (Fin.natAdd N l) = true} =
            (lineSet N t).card := by
          rw [← Fintype.card_coe]
          apply Fintype.card_congr
          exact Equiv.subtypeEquivRight (fun l => by simp only [Fin.append_right, Y', decide_eq_true_eq])
        have miss : ¬∃ p l, I p l ∧ Fin.append X Y' (Fin.castAdd N p)=true ∧
            Fin.append X Y' (Fin.natAdd N l)=true := by
          rintro ⟨p,l,hi,hp,hmem⟩
          have mem : l ∈ lineSet N t := by simpa only [Fin.append_right, Y', decide_eq_true_eq] using hmem
          exact e ⟨p,l,hi,by simpa [X] using hp,selected_line hs l mem⟩
        have no := reject (Fin.append X Y') (small.trans_le ((lineSet_card N t).trans (hl.trans hq))) miss
        have yes := (value_eq_terms h (Fin.append X Y') C.output).mpr ⟨t, ht, support_lineSet hs⟩
        exact Bool.false_ne_true (no.symm.trans yes)
    · intro S hS
      let z := @setInput (N+N) S
      let X (p : Fin N) := z (Fin.castAdd N p)
      let Y (l : Fin N) := z (Fin.natAdd N l)
      have he : Fin.append X Y = z := Fin.append_castAdd_natAdd
      have hv : value C C.output X Y = true := by unfold value; rw [he]; exact hS.1
      obtain ⟨t, ht, hs, hp, hl⟩ := bounded X Y hv
      have hsub (i : ℕ) (hi : i ∈ t) : i ∈ setList S := by
        obtain ⟨a, rfl, hz⟩ := hs i hi
        rw [he] at hz
        exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_finRange a, hz⟩, rfl⟩
      apply List.any_eq_true.mpr
      refine ⟨encode (setList S) t, word_to_vector h _ _ _ ht hsub, List.all_eq_true.mpr ?_⟩
      intro a ha
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      exact decide_eq_true (min_le_of_left_le (count_bound hp hl i))


  -- This is the marked-gate predicate in the desk statement, on its original input lists.
  let OverlapGate (N : ℕ) (C : Circuit) (g : Gate) : Prop :=
    g.op = .and ∧
      ((∀ w ∈ g.inputs, ∃ X : Fin N → Bool,
         (C.wires (List.ofFn X ++ List.replicate N false)).getD w false ≠
         (C.wires (List.ofFn X ++ List.replicate N true)).getD w false) ∨
       (∀ w ∈ g.inputs, ∃ Y : Fin N → Bool,
         (C.wires (List.replicate N false ++ List.ofFn Y)).getD w false ≠
         (C.wires (List.replicate N true ++ List.ofFn Y)).getD w false))

  have marked_iff {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N+N) C)
      (k : Fin C.size) : OverlapGate N C (row C k) ↔ (row C k).op = .and ∧ overlap N C k := by
    have mix (w : ℕ) (X Y : Fin N → Bool) : value C w X Y =
        (C.wires (List.ofFn X ++ List.ofFn Y)).getD w false := by
      unfold value circuitValue
      rw [List.ofFn_fin_append]
      rfl
    simp [OverlapGate, inputs_two h k, overlap, lineSensitive, pointSensitive, mix, List.ofFn_const]

  have small_words_of_antichain {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N+N) C)
      (U : Finset ℕ) (mark : ∀ k : Fin C.size, OverlapGate N C (row C k) → k.val ∈ U)
      (anti : ∀ i ∈ U, ∀ j ∈ U, ¬InCone (N+N) C i j) :
      ∀ X Y : Fin N → Bool, value C C.output X Y = true → Bounded C C.output 2 X Y := by
    classical
    let n := N+N
    let after (w : ℕ) := n ≤ w ∧ ∃ i ∈ U, i = w-n ∨ InCone n C i (w-n)
    let d (w : ℕ) := if after w then 2 else 1
    have relay (k : Fin C.size) (b : Fin 2) (ha : after (operand C k b)) :
        ∃ i ∈ U, InCone n C i k.val := by
      obtain ⟨hn,i,hi,ha⟩ := ha
      have mem : operand C k b ∈ (gateAt C k.val).inputs := by
        rw [show gateAt C k.val = row C k from List.getD_eq_getElem _ _ k.isLt, inputs_two h k]
        fin_cases b <;> simp
      exact ⟨i,hi,(coneRule n C i k.val k.isLt).mpr
        ⟨operand C k b, mem, hn, earlier h k b, ha⟩⟩
    have up (k : Fin C.size) (b : Fin 2) : d (operand C k b) ≤ d (outWire n k) := by
      by_cases ha : after (operand C k b)
      · obtain ⟨i, hi, hc⟩ := relay k b ha
        have hk : after (outWire n k) := by
          refine ⟨by simp [outWire], i, hi, Or.inr ?_⟩
          simpa [outWire] using hc
        simp [d,ha,hk]
      · rw [show d (operand C k b) = 1 by simp [d,ha]]
        unfold d
        split <;> decide
    have marked (k : Fin C.size) (hand : (row C k).op = .and) (hc : overlap N C k) :
        d (operand C k 0) + d (operand C k 1) ≤ d (outWire n k) := by
      have hu := mark k ((marked_iff h k).mpr ⟨hand,hc⟩)
      have clear (b : Fin 2) : ¬after (operand C k b) := by
        intro ha
        obtain ⟨i, hi, hc⟩ := relay k b ha
        exact anti i hi k.val hu hc
      have here : after (outWire n k) := by
        refine ⟨by simp [outWire], k.val, hu, Or.inl ?_⟩
        simp [outWire]
      simp [d,clear,here]
    intro X Y ht
    have hp (w : ℕ) : 1 ≤ d w := by unfold d; split <;> decide
    obtain ⟨t,hw,hs,h₁,h₂⟩ := bounded_words h d hp up marked C.output X Y ht
    have le : d C.output ≤ 2 := by unfold d; split <;> decide
    exact ⟨t,hw,hs,h₁.trans le,h₂.trans le⟩


  let run (gs : List Gate) (xs : List Bool) : List Bool :=
    evalFrom false GateOp.eval gs xs

  have run_snoc (gs : List Gate) (g : Gate) (xs : List Bool) :
      run (gs ++ [g]) xs = run gs xs ++ [g.op.eval (g.inputs.map fun i => (run gs xs).getD i false)] := by
    simp [run, evalFrom, List.foldl_append]

  have run_length (gs : List Gate) (xs : List Bool) :
      (run gs xs).length = xs.length + gs.length :=
    evalFrom_length false GateOp.eval gs xs

  have supports (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
      (F : Finset ℕ) :
      ∃ S : Finset ℕ, S.card ≤ F.card + gs.length ∧
        ∀ (x y : List Bool), x.length = n → y.length = n →
          (∀ i ∈ S, x.getD i false = y.getD i false) →
          ∀ i ∈ F, (run gs x).getD i false = (run gs y).getD i false := by
    induction gs using List.reverseRecOn generalizing F with
    | nil => exact ⟨F, by simp, fun _ _ _ _ ha => ha⟩
    | append_singleton gs g ih =>
      let j := n + gs.length
      let B := if j ∈ F then F.erase j ∪ g.inputs.toFinset else F
      have hb : B.card ≤ F.card + 1 := by
        by_cases hj : j ∈ F
        · have hu := Finset.card_union_le (F.erase j) g.inputs.toFinset
          have he := Finset.card_erase_add_one hj
          have hd := (List.toFinset_card_le g.inputs).trans (hg g (by simp))
          simp only [B, ite_eq_left hj]
          omega
        · simp [B, hj]
      obtain ⟨S, hS, hs⟩ := ih (fun a ha => hg a (List.mem_append_left _ ha)) B
      refine ⟨S, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      intro x y hx hy ha i hi
      have ex : (run gs x).length = j := by simp [run_length, hx, j]
      have ey : (run gs y).length = j := by simp [run_length, hy, j]
      rw [run_snoc, run_snoc]
      rcases lt_trichotomy i j with hij | rfl | hij
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        apply hs x y hx hy ha i
        by_cases hj : j ∈ F
        · simpa [B, hj] using Finset.mem_union_left g.inputs.toFinset (Finset.mem_erase.mpr ⟨hij.ne, hi⟩)
        · simpa [B, hj] using hi
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        simp only [ex, ey, Nat.sub_self, List.getD_cons_zero]
        congr 1
        apply List.map_congr_left
        intro k hk
        apply hs x y hx hy ha k
        simpa [B, hi] using Finset.mem_union_right (F.erase j) (List.mem_toFinset.mpr hk)
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

  have essential_bound {n : ℕ} (C : Circuit)
      (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
      (he : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
        circuitFun n C x ≠ circuitFun n C y) :
      n ≤ C.size + 1 := by
    obtain ⟨S, hS, hs⟩ := supports n C.gates hg {C.output}
    suffices hh : Finset.range n ⊆ S by
      have := Finset.card_le_card hh
      simp only [Finset.card_range] at this
      simp only [Finset.card_singleton] at hS
      unfold Circuit.size
      omega
    intro i hi
    by_contra hni
    let a : Fin n := ⟨i, Finset.mem_range.mp hi⟩
    obtain ⟨x, y, hxy, hne⟩ := he a
    apply hne
    apply hs (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
    intro j hj
    by_cases hjn : j < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hjn),
        List.getD_eq_getElem _ _ (by simpa using hjn)]
      simp only [List.getElem_ofFn]
      apply hxy
      intro e
      have he : j = i := congrArg Fin.val e
      exact hni (he ▸ hj)
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn)]

  dsimp only
  intro q n R dec C qLarge geom lines connects basis output order accept reject U urange unonempty exactU few
  let S (l : Fin n) := Finset.univ.filter fun p => R p l
  have incident (p l : Fin n) : p ∈ S l ↔ R p l := by simp [S]
  have lineSize (l : Fin n) : (S l).card = q+1 := by
    rw [← Fintype.card_coe]
    exact (Fintype.card_congr (Equiv.subtypeEquivRight (fun p => incident p l))).trans (lines l)
  have through (p p' : Fin n) (h : p ≠ p') :
      ∃! l : Fin n, p ∈ S l ∧ p' ∈ S l := by simpa only [incident] using connects p p' h
  have model : IsAO2 (n+n) C := by
    refine ⟨fun g hg => (basis g hg).1, ?_, ?_⟩
    · intro j hj i hi
      have get : C.gates[j]? = some (gateAt C j) := by
        rw [List.getElem?_eq_getElem hj, show gateAt C j = C.gates[j] from List.getD_eq_getElem _ _ hj]
      obtain ⟨a,b,eq,lt,back⟩ := order j _ get
      rw [eq, List.mem_cons, List.mem_singleton] at hi
      rcases hi with rfl | rfl <;> omega
    · intro g hg
      obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hg
      obtain ⟨a,b,ab,_,_⟩ := order j g (by rw [List.getElem?_eq_getElem hj, eq])
      simp [ab]
  let vector (X Y : Finset (Fin n)) := Fin.append (fun p : Fin n => decide (p ∈ X))
    (fun l : Fin n => decide (l ∈ Y))
  have listForm (X Y : Finset (Fin n)) : List.ofFn (vector X Y) = incidenceInput X Y :=
    List.ofFn_fin_append _ _
  have vp (X Y : Finset (Fin n)) (p : Fin n) : vector X Y (Fin.castAdd n p) = decide (p ∈ X) :=
    Fin.append_left _ _ _
  have vl (X Y : Finset (Fin n)) (l : Fin n) : vector X Y (Fin.natAdd n l) = decide (l ∈ Y) :=
    Fin.append_right _ _ _
  have diff (p l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd n l := by
    intro e
    have he := congrArg Fin.val e
    simp only [Fin.val_castAdd, Fin.val_natAdd] at he
    have := p.isLt
    omega
  have pair (p l : Fin n) :
      vector {p} {l} = fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l) := by
    funext i
    induction i using Fin.addCases with
    | left a => simp only [vp, Finset.mem_singleton, Fin.castAdd_inj, diff a l, or_false]
    | right b => simp only [vl, Finset.mem_singleton, Ne.symm (diff p b), false_or,
        Fin.natAdd_inj]
  have count (X Y : Finset (Fin n)) :
      Fintype.card {l : Fin n // vector X Y (Fin.natAdd n l) = true} = Y.card := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun l => by simp only [vl, decide_eq_true_eq]))
  let admissible (E : Circuit) := IsAO2 (n+n) E ∧ RightOnIncidentPairs S E ∧
    ∀ X Y, Y.card ≤ q → IsFalseInput S X Y → E.eval (incidenceInput X Y) = false
  have cOK : admissible C := by
    refine ⟨model, ?_, ?_⟩
    · intro l p hi
      change C.eval (incidenceInput {p} {l}) = true
      rw [← listForm, pair]
      exact accept p l ((incident p l).mp hi)
    · intro X Y bud he
      rw [← listForm]
      apply reject (vector X Y) ((count X Y).trans_le bud)
      rintro ⟨p,l,hi,hp,hl⟩
      exact Finset.disjoint_left.mp (he l (of_decide_eq_true ((vl X Y l).symm.trans hl)))
        ((incident p l).mpr hi) (of_decide_eq_true ((vp X Y p).symm.trans hp))
  have sourceSize : n+n ≤ C.size+1 := by
    apply essential_bound C (fun g hg => (model.2.2 g hg).le)
    have sizeN : 2 ≤ n := by nlinarith
    have val (A B : Finset (Fin n)) : circuitFun (n+n) C (vector A B) =
        C.eval (incidenceInput A B) := congrArg C.eval (listForm A B)
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro p
      have other : ∃ p' : Fin n, p ≠ p' := by
        by_cases zero : p.val = 0
        · exact ⟨⟨1, by omega⟩, fun e => by have hh := congrArg Fin.val e; simp at hh; omega⟩
        · exact ⟨⟨0, by omega⟩, fun e => zero (congrArg Fin.val e)⟩
      obtain ⟨p', ne⟩ := other
      obtain ⟨l, hpl, _⟩ := through p p' ne
      have on := cOK.2.1 l p hpl.1
      have bound : ({l} : Finset (Fin n)).card ≤ q := by simpa using (show 1 ≤ q by omega)
      have off := cOK.2.2 ∅ {l} bound (fun _ _ => by simp)
      refine ⟨vector {p} {l}, vector ∅ {l}, ?_, ?_⟩
      · intro j hj
        induction j using Fin.addCases with
        | left a =>
          have neq : a ≠ p := fun h => hj (congrArg (Fin.castAdd n) h)
          simp only [vp, Finset.mem_singleton, neq, Finset.notMem_empty]
        | right b => simp only [vl]
      · rw [val,val,on,off]; decide
    · intro l
      obtain ⟨p,pl⟩ := Finset.card_pos.mp (show 0 < (S l).card by rw [lineSize]; omega)
      have on := cOK.2.1 l p pl
      have off := cOK.2.2 {p} ∅ (by simp) (fun _ h => False.elim (Finset.notMem_empty _ h))
      refine ⟨vector {p} {l}, vector {p} ∅, ?_, ?_⟩
      · intro j hj
        induction j using Fin.addCases with
        | left a => simp only [vp]
        | right b =>
          have neq : b ≠ l := fun h => hj (congrArg (Fin.natAdd n) h)
          simp only [vl, Finset.mem_singleton, neq, Finset.notMem_empty]
      · rw [val,val,on,off]; decide
  by_cases large : 200 ≤ q
  swap
  · have above : 100 ≤ n := by nlinarith
    have times := Nat.mul_le_mul_left n (show q ≤ 199 by omega)
    omega
  have existsSize : ∃ s, ∃ E : Circuit, admissible E ∧ E.size = s := ⟨C.size,C,cOK,rfl⟩
  obtain ⟨E,hE,sz⟩ := Nat.find_spec existsSize
  have least (D : Circuit) (hd : admissible D) : E.size ≤ D.size := by
    rw [sz]; exact Nat.find_min' existsSize ⟨D,hd,rfl⟩
  have compare := Nat.mul_le_mul_left 100 (least C cOK)
  apply le_trans _ compare
  let test (X : Fin n → Bool) (side bit : Bool) := if side then
    List.replicate n bit ++ List.ofFn X else List.ofFn X ++ List.replicate n bit
  let mark (j : ℕ) := (gateAt E j).op = .and ∧ ∃ s : Bool, ∀ w ∈ (gateAt E j).inputs,
    ∃ X : Fin n → Bool, wireValue E (test X s false) w ≠ wireValue E (test X s true) w
  by_cases nested : ∃ i j : Fin E.size, InCone (n+n) E i j ∧ mark i ∧ mark j
  · exact nestedMinimum q n S large geom lineSize through E hE least nested
  let marks := (Finset.range E.size).filter mark
  have cover (k : Fin E.size) (hm : OverlapGate n E (row E k)) : k.val ∈ marks := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr k.isLt, ?_⟩
    have eq : gateAt E k.val = row E k := List.getD_eq_getElem _ _ k.isLt
    rcases hm with ⟨ho, h | h⟩
    · exact ⟨eq ▸ ho, false, by rw [eq]; exact h⟩
    · exact ⟨eq ▸ ho, true, by rw [eq]; exact h⟩
  have anti (i : ℕ) (hi : i ∈ marks) (j : ℕ) (hj : j ∈ marks) (hc : InCone (n+n) E i j) : False := by
    obtain ⟨a,b⟩ := Finset.mem_filter.mp hi
    obtain ⟨c,d⟩ := Finset.mem_filter.mp hj
    exact nested ⟨⟨i,Finset.mem_range.mp a⟩,⟨j,Finset.mem_range.mp c⟩,hc,b,d⟩
  have hit (p l : Fin n) (hi : R p l) : circuitFun (n+n) E
      (fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) = true := by
    change E.eval (List.ofFn _) = _
    rw [← pair, listForm]
    exact hE.2.1 l p ((incident p l).mpr hi)
  have miss (z : Fin (n+n) → Bool)
      (budget : Fintype.card {l : Fin n // z (Fin.natAdd n l) = true} ≤ q)
      (ne : ¬∃ p l : Fin n, R p l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true) :
      circuitFun (n+n) E z = false := by
    let X := Finset.univ.filter (fun p : Fin n => z (Fin.castAdd n p) = true)
    let Y := Finset.univ.filter (fun l : Fin n => z (Fin.natAdd n l) = true)
    have same : vector X Y = z := by
      funext i
      induction i using Fin.addCases with
      | left p => rw [vp]; simp [X]
      | right l => rw [vl]; simp [Y]
    have sizeY := count X Y
    rw [same] at sizeY
    change E.eval (List.ofFn z) = false
    rw [← same, listForm]
    apply hE.2.2 X Y (sizeY.symm.trans_le budget)
    intro l hl
    apply Finset.disjoint_left.mpr
    intro p hi hp
    exact ne ⟨p,l,(incident p l).mp hi,(Finset.mem_filter.mp hp).2,(Finset.mem_filter.mp hl).2⟩
  obtain ⟨correct,reads⟩ := exact_read_two R hE.1 (by omega : 2 ≤ q) hit miss
    (small_words_of_antichain hE.1 marks cover anti)
  exact readLower q n R E (by omega) geom lines connects hE.1 correct reads
