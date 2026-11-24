import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3708

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

section Circuit
private def evalFrom {α : Type} (d : α) (op : GateOp → List α → α) (gates : List Gate) (xs : List α) :
    List α :=
  gates.foldl (fun u g => u ++ [op g.op (g.inputs.map fun i => u.getD i d)]) xs

private lemma evalFrom_cons {α : Type} (d : α) (op : GateOp → List α → α) (g : Gate) (gs : List Gate)
    (xs : List α) :
    evalFrom d op (g :: gs) xs = evalFrom d op gs
      (xs ++ [op g.op (g.inputs.map fun i => xs.getD i d)]) := rfl

private lemma evalFrom_length {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) : (evalFrom d op gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalFrom]
  | cons g gs ih => rw [evalFrom_cons, ih]; simp; omega

private lemma evalFrom_input {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (evalFrom d op gs xs).getD i d = xs.getD i d := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [evalFrom_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

private def row (C : Circuit) (k : Fin C.size) : Gate := C.gates[k.val]'k.isLt

private def operand (C : Circuit) (k : Fin C.size) (b : Fin 2) : ℕ :=
  (row C k).inputs.getD b.val 0

private def outWire (n : ℕ) {s : ℕ} (k : Fin s) : ℕ := n + k.val

private lemma inputs_two {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).inputs = [operand C k 0, operand C k 1] := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h.2.2 (row C k) (List.getElem_mem _))
  simp [operand, hab]

private lemma op_kind {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).op = GateOp.and ∨ (row C k).op = GateOp.or :=
  h.1 (row C k) (List.getElem_mem _)

private lemma earlier {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (k : Fin C.size) (b : Fin 2) : operand C k b < outWire n k := by
  have he : gateAt C k.val = row C k := List.getD_eq_getElem _ _ k.isLt
  have hm : operand C k b ∈ (row C k).inputs := by
    rw [inputs_two h k]
    fin_cases b <;> simp
  exact h.2.1 k.val k.isLt (operand C k b) (by simpa only [he] using hm)

private lemma evalFrom_gate {α : Type} (d : α) (op : GateOp → List α → α) {n : ℕ}
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

private lemma wire_cases (n s w : ℕ) :
    w < n ∨ (∃ k : Fin s, w = outWire n k) ∨ n + s ≤ w := by
  by_cases hb : w < n
  · exact Or.inl hb
  by_cases he : w < n + s
  · exact Or.inr (Or.inl ⟨⟨w - n, by omega⟩, by simp [outWire]; omega⟩)
  · exact Or.inr (Or.inr (by omega))

private def wordOp : GateOp → List (Set (List ℕ)) → Set (List ℕ)
  | .or, [a, b] => a ∪ b
  | .and, [a, b] => {t | ∃ u ∈ a, ∃ v ∈ b, t = u ++ v}
  | _, _ => ∅

private def wordList (n : ℕ) (C : Circuit) : List (Set (List ℕ)) :=
  evalFrom ∅ wordOp C.gates (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ))))

private def words (n : ℕ) (C : Circuit) (w : ℕ) : Set (List ℕ) :=
  (wordList n C).getD w ∅

private lemma words_input {n : ℕ} (C : Circuit) {w : ℕ} (hw : w < n) :
    words n C w = {[w]} := by
  unfold words wordList
  have hi : w < (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ)))).length := by
    simpa using hw
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

private lemma words_missing (n : ℕ) (C : Circuit) {w : ℕ} (hw : n + C.size ≤ w) :
    words n C w = ∅ :=
  List.getD_eq_default _ _ (by simpa [wordList, evalFrom_length, Circuit.size] using hw)

private lemma words_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    words n C (outWire n k) =
      wordOp (row C k).op [words n C (operand C k 0), words n C (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

private def circuitValue {n : ℕ} (C : Circuit) (z : Fin n → Bool) (w : ℕ) : Bool :=
  (evalFrom false GateOp.eval C.gates (List.ofFn z)).getD w false

private lemma value_input {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ} (hw : w < n) :
    circuitValue C z w = z ⟨w, hw⟩ := by
  have hi : w < (List.ofFn z).length := by simpa using hw
  unfold circuitValue
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

private lemma value_missing {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ}
    (hw : n + C.size ≤ w) : circuitValue C z w = false :=
  List.getD_eq_default _ _ (by simpa [evalFrom_length, Circuit.size] using hw)

private lemma value_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (z : Fin n → Bool) (k : Fin C.size) :
    circuitValue C z (outWire n k) = (row C k).op.eval
      [circuitValue C z (operand C k 0), circuitValue C z (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

private lemma value_eq_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
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
        simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
          Bool.and_eq_true, wordOp, Set.mem_ofPred_eq, h1, h2]
        constructor
        · rintro ⟨⟨t, ht, htz⟩, ⟨u, hu, huz⟩⟩
          exact ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, fun i hi =>
            (List.mem_append.mp hi).elim (htz i) (huz i)⟩
        · rintro ⟨_, ⟨t, ht, u, hu, rfl⟩, hh⟩
          exact ⟨⟨t, ht, fun i hi => hh i (List.mem_append_left _ hi)⟩,
            ⟨u, hu, fun i hi => hh i (List.mem_append_right _ hi)⟩⟩
      · rw [ho]
        simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
          Bool.or_eq_true, wordOp, Set.mem_union, h1, h2]
        exact ⟨fun h => h.elim (fun ⟨t, ht, ha⟩ => ⟨t, Or.inl ht, ha⟩)
          (fun ⟨t, ht, ha⟩ => ⟨t, Or.inr ht, ha⟩),
          fun ⟨t, ht, ha⟩ => ht.elim (fun h => Or.inl ⟨t, h, ha⟩) (fun h => Or.inr ⟨t, h, ha⟩)⟩
    · simp [value_missing C z hb, words_missing n C hb]

private lemma words_nonempty {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {w : ℕ} {t : List ℕ} (ht : t ∈ words n C w) : t ≠ [] := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb] at ht
      have ht' : t = [w] := ht
      simp [ht']
    · rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · rw [ho] at ht
        obtain ⟨u, hu, v, _, rfl⟩ := ht
        exact fun hh => ih _ (earlier h k 0) hu (List.append_eq_nil_iff.mp hh).1
      · rw [ho] at ht
        exact ht.elim (ih _ (earlier h k 0)) (ih _ (earlier h k 1))
    · simp [words_missing n C hb] at ht

end Circuit

section ReadWitness

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

private lemma mem_insertNew (a v : List ℕ) (A : List (List ℕ)) :
    v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
  unfold insertNew
  by_cases ha : a ∈ A
  · simp [ha, or_iff_left_of_imp (fun (e : v = a) => e.symm ▸ ha)]
  · simp [ha]

private lemma mem_fold_insertNew (v : List ℕ) (B A : List (List ℕ)) :
    v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons b B ih => simp [ih, mem_insertNew, or_assoc]

private lemma mem_andStep_one (v : List ℕ) (A B : List (List ℕ)) :
    v ∈ andStep 1 A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd 1 u w := by
  simp [andStep, mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]

private def encode (S t : List ℕ) : List ℕ :=
  S.map fun j => min (t.count j) 2

private lemma encode_nil (S : List ℕ) : encode S [] = S.map (fun _ => 0) := by
  simp [encode]

private lemma encode_append (S t u : List ℕ) :
    capAdd 1 (encode S t) (encode S u) = encode S (t ++ u) := by
  induction S with
  | nil => rfl
  | cons a S ih =>
    simp only [encode, capAdd, List.map_cons, List.zipWith_cons_cons, List.count_append] at ih ⊢
    rw [ih]
    congr 1
    omega

private def readOp (S : List ℕ) (o : GateOp) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match o with
  | .or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | .and => ins.foldl (andStep 1) [S.map fun _ => 0]
  | _ => []

private def vecs (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) : List (List ℕ) :=
  ((readVectors C n S 1).getD w [])

private lemma vec_eval (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) :
    vecs n C S w =
      (evalFrom [] (readOp S) C.gates ((List.range n).map (leafVectors S 1))).getD w [] :=
  rfl

private lemma leaf_encode (S : List ℕ) (w : ℕ) :
    S.map (fun j => if j = w then min 1 (1 + 1) else 0) = encode S [w] := by
  unfold encode
  apply List.map_congr_left
  intro a _
  by_cases hea : a = w
  · simp [hea]
  · simp [hea, Ne.symm hea]

private lemma encode_witness {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (w : ℕ) (v : List ℕ) (hv : v ∈ vecs n C S w) :
    ∃ t ∈ words n C w, v = encode S t ∧ ∀ i ∈ t, i ∈ S := by
  induction w using Nat.strong_induction_on generalizing v with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · have hi : w < ((List.range n).map (leafVectors S 1)).length := by simpa using hb
      rw [vec_eval, evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi] at hv
      simp only [List.getElem_map, List.getElem_range] at hv
      rw [words_input C hb]
      by_cases hs : w ∈ S
      · refine ⟨[w], rfl, ?_, by simpa using hs⟩
        have hvec : v = S.map (fun j => if j = w then min 1 (1 + 1) else 0) := by
          simpa only [leafVectors, hs, ite_true, List.mem_singleton] using hv
        rw [hvec, leaf_encode]
      · simp [leafVectors, hs] at hv
    · have hlen : ((List.range n).map (leafVectors S 1)).length = n := by simp
      have hvec := evalFrom_gate ([] : List (List ℕ)) (readOp S) h _ hlen k
      rw [← vec_eval, ← vec_eval, ← vec_eval] at hvec
      rw [hvec] at hv
      rw [words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho] at hv ⊢
        change v ∈ andStep 1 (andStep 1 [S.map (fun _ => 0)] (vecs n C S (operand C k 0)))
          (vecs n C S (operand C k 1)) at hv
        obtain ⟨x, hx, y, hy, rfl⟩ := (mem_andStep_one _ _ _).mp hv
        obtain ⟨z, hz, x', hx', rfl⟩ := (mem_andStep_one _ _ _).mp hx
        obtain ⟨t, ht, rfl, hts⟩ := ih _ (earlier h k 0) _ hx'
        obtain ⟨u, hu, rfl, hus⟩ := ih _ (earlier h k 1) _ hy
        refine ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, ?_, fun i hi =>
          (List.mem_append.mp hi).elim (hts i) (hus i)⟩
        have hz' : z = encode S [] := by simpa [encode_nil] using hz
        rw [hz', encode_append, List.nil_append, encode_append]
      · rw [ho] at hv ⊢
        change v ∈ (vecs n C S (operand C k 1)).foldl insertNew
          ((vecs n C S (operand C k 0)).foldl insertNew []) at hv
        rw [mem_fold_insertNew, mem_fold_insertNew] at hv
        simp only [List.not_mem_nil, false_or] at hv
        rcases hv with hp | hp
        · obtain ⟨t, ht, he, hs⟩ := ih _ (earlier h k 0) _ hp
          exact ⟨t, Or.inl ht, he, hs⟩
        · obtain ⟨t, ht, he, hs⟩ := ih _ (earlier h k 1) _ hp
          exact ⟨t, Or.inr ht, he, hs⟩
    · rw [vec_eval, List.getD_eq_default _ _ (by
        simpa [evalFrom_length, Circuit.size] using hb)] at hv
      simp at hv

private lemma encode_complete {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (w : ℕ) (t : List ℕ) (ht : t ∈ words n C w) (hs : ∀ i ∈ t, i ∈ S) :
    encode S t ∈ vecs n C S w := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · have hi : w < ((List.range n).map (leafVectors S 1)).length := by simpa using hb
      rw [vec_eval, evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
      simp only [List.getElem_map, List.getElem_range]
      rw [words_input C hb] at ht
      have ht' : t = [w] := ht
      subst ht'
      have hw : w ∈ S := hs w (by simp)
      simp only [leafVectors, hw, ite_true, List.mem_singleton]
      exact (leaf_encode S w).symm
    · have hlen : ((List.range n).map (leafVectors S 1)).length = n := by simp
      have hvec := evalFrom_gate ([] : List (List ℕ)) (readOp S) h _ hlen k
      rw [← vec_eval, ← vec_eval, ← vec_eval] at hvec
      rw [hvec]
      rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · rw [ho] at ht ⊢
        change encode S t ∈ andStep 1 (andStep 1 [S.map (fun _ => 0)]
          (vecs n C S (operand C k 0))) (vecs n C S (operand C k 1))
        obtain ⟨t1, ht1, t2, ht2, rfl⟩ := ht
        have h1 := ih _ (earlier h k 0) t1 ht1 (fun i hi => hs i (List.mem_append_left _ hi))
        have h2 := ih _ (earlier h k 1) t2 ht2 (fun i hi => hs i (List.mem_append_right _ hi))
        refine (mem_andStep_one _ _ _).mpr ⟨encode S t1, ?_, encode S t2, h2,
          (encode_append S t1 t2).symm⟩
        refine (mem_andStep_one _ _ _).mpr ⟨encode S [], by simp [encode_nil], encode S t1, h1, ?_⟩
        rw [encode_append, List.nil_append]
      · rw [ho] at ht ⊢
        change encode S t ∈ (vecs n C S (operand C k 1)).foldl insertNew
          ((vecs n C S (operand C k 0)).foldl insertNew [])
        rw [mem_fold_insertNew, mem_fold_insertNew]
        rcases ht with ht | ht
        · exact Or.inl (Or.inr (ih _ (earlier h k 0) t ht hs))
        · exact Or.inr (ih _ (earlier h k 1) t ht hs)
    · rw [words_missing n C hb] at ht
      exact absurd ht (Set.notMem_empty t)

private lemma read_iff {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (S : List ℕ) :
    readsAtMost C n S 1 = true ↔
      ∃ t ∈ words n C C.output, (∀ i ∈ t, i ∈ S) ∧ ∀ i ∈ S, t.count i ≤ 1 := by
  constructor
  · intro r
    obtain ⟨v, hv, ha⟩ := List.any_eq_true.mp r
    obtain ⟨t, ht, rfl, hts⟩ := encode_witness h S C.output v hv
    refine ⟨t, ht, hts, fun i hi => ?_⟩
    have hv : min (t.count i) 2 ∈ encode S t := List.mem_map.mpr ⟨i, hi, rfl⟩
    have hb := of_decide_eq_true ((List.all_eq_true.mp ha) _ hv)
    omega
  · rintro ⟨t, ht, hts, hc⟩
    refine List.any_eq_true.mpr ⟨encode S t, encode_complete h S _ t ht hts, ?_⟩
    refine List.all_eq_true.mpr fun a ha => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    have := hc j hj
    exact decide_eq_true (by omega)

end ReadWitness

section OrReach

open PEqualNP.CleanedNonEdge

private lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

private lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

private lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

private lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

private lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

private lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

private lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by simp [orStep, hl0])]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by simp [orStep, hl0]; omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩

private lemma row_eq (C : Circuit) (k : Fin C.size) : gateAt C k.val = row C k :=
  List.getD_eq_getElem _ _ k.isLt

private lemma opnd_eq (C : Circuit) (k : Fin C.size) (b : Fin 2) :
    PEqualNP.TopForm.opnd C k.val b = operand C k b := by
  simp only [PEqualNP.TopForm.opnd, operand, row_eq]

private lemma orR_input {n : ℕ} (C : Circuit) {w g : ℕ} (hw : w < n) : ¬ OrReaches n C w g :=
  fun h => absurd h.1 (by omega)

private lemma orR_missing {n : ℕ} (C : Circuit) {w g : ℕ} (hw : n + C.size ≤ w) :
    ¬ OrReaches n C w g := by
  rintro ⟨_, hm⟩
  have hlen : (orSets n C).length = C.gates.length := by simp [orSets, orFold_length]
  rw [List.getD_eq_default _ _ (by simp [Circuit.size] at hw; omega)] at hm
  simp at hm

private lemma orR_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size)
    (g : ℕ) :
    OrReaches n C (outWire n k) g ↔ g = k.val ∨ ((row C k).op = GateOp.or ∧
      (OrReaches n C (operand C k 0) g ∨ OrReaches n C (operand C k 1) g)) := by
  unfold OrReaches
  have hsub : outWire n k - n = k.val := by simp [outWire]
  rw [hsub, orSets_mem_iff n C k.val g k.isLt, row_eq, inputs_two h k]
  have e0 := earlier h k 0
  have e1 := earlier h k 1
  simp only [outWire] at e0 e1
  simp only [outWire, le_add_iff_nonneg_right, zero_le, true_and, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro (h1 | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h1
    · rcases hw with rfl | rfl
      · exact Or.inr ⟨hop, Or.inl ⟨hn, hx⟩⟩
      · exact Or.inr ⟨hop, Or.inr ⟨hn, hx⟩⟩
  · rintro (h1 | ⟨hop, ⟨hn, hx⟩ | ⟨hn, hx⟩⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨hop, _, Or.inl rfl, hn, e0, hx⟩
    · exact Or.inr ⟨hop, _, Or.inr rfl, hn, e1, hx⟩

end OrReach

section Words

open PEqualNP.CleanedNonEdge

private lemma single_iff {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (p : ℕ)
    (hp : p < n) (w : ℕ) :
    [p] ∈ words n C w ↔ p = w ∨ ∃ k < C.gates.length, OrReaches n C w k ∧
      (gateAt C k).op = GateOp.or ∧ p ∈ (gateAt C k).inputs := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb]
      constructor
      · intro hm
        have : [p] = [w] := hm
        exact Or.inl (List.singleton_inj.mp this)
      · rintro (rfl | ⟨k, _, hr, _⟩)
        · rfl
        · exact absurd hr (orR_input C hb)
    · have hpw : p ≠ outWire n k := by simp [outWire]; omega
      rw [words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho]
        constructor
        · rintro ⟨t, ht, u, hu, he⟩
          have h1 := words_nonempty h ht
          have h2 := words_nonempty h hu
          have hl := congrArg List.length he
          simp only [List.length_singleton, List.length_append] at hl
          have := List.length_pos_of_ne_nil h1
          have := List.length_pos_of_ne_nil h2
          omega
        · rintro (he | ⟨k', _, hr, hop, _⟩)
          · exact absurd he hpw
          · rcases (orR_gate h k k').mp hr with rfl | ⟨hop', _⟩
            · rw [row_eq, ho] at hop; nomatch hop
            · rw [ho] at hop'; nomatch hop'
      · rw [ho]
        simp only [wordOp, Set.mem_union]
        rw [ih _ (earlier h k 0), ih _ (earlier h k 1)]
        constructor
        · rintro ((he | ⟨k', hk', hr, hop, hin⟩) | (he | ⟨k', hk', hr, hop, hin⟩))
          · refine Or.inr ⟨k.val, k.isLt, (orR_gate h k _).mpr (Or.inl rfl), by rw [row_eq, ho],
              by rw [row_eq, inputs_two h k, he]; simp⟩
          · exact Or.inr ⟨k', hk', (orR_gate h k _).mpr (Or.inr ⟨ho, Or.inl hr⟩), hop, hin⟩
          · refine Or.inr ⟨k.val, k.isLt, (orR_gate h k _).mpr (Or.inl rfl), by rw [row_eq, ho],
              by rw [row_eq, inputs_two h k, he]; simp⟩
          · exact Or.inr ⟨k', hk', (orR_gate h k _).mpr (Or.inr ⟨ho, Or.inr hr⟩), hop, hin⟩
        · rintro (he | ⟨k', hk', hr, hop, hin⟩)
          · exact absurd he hpw
          · rcases (orR_gate h k k').mp hr with rfl | ⟨_, hr' | hr'⟩
            · rw [row_eq, inputs_two h k] at hin
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
              rcases hin with hin | hin
              · exact Or.inl (Or.inl hin)
              · exact Or.inr (Or.inl hin)
            · exact Or.inl (Or.inr ⟨k', hk', hr', hop, hin⟩)
            · exact Or.inr (Or.inr ⟨k', hk', hr', hop, hin⟩)
    · rw [words_missing n C hb]
      constructor
      · intro hm; exact absurd hm (Set.notMem_empty _)
      · rintro (he | ⟨k, _, hr, _⟩)
        · simp [Circuit.size] at hb; omega
        · exact absurd hr (orR_missing C hb)

private lemma pair_iff {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (p q : ℕ) (w : ℕ) :
    [p, q] ∈ words n C w ↔ ∃ a < C.gates.length, OrReaches n C w a ∧
      (gateAt C a).op = GateOp.and ∧ [p] ∈ words n C (PEqualNP.TopForm.opnd C a 0) ∧
        [q] ∈ words n C (PEqualNP.TopForm.opnd C a 1) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb]
      constructor
      · intro hm
        have : [p, q] = [w] := hm
        simp at this
      · rintro ⟨a, _, hr, _⟩
        exact absurd hr (orR_input C hb)
    · rw [words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho]
        constructor
        · rintro ⟨t, ht, u, hu, he⟩
          have h1 := words_nonempty h ht
          have h2 := words_nonempty h hu
          obtain ⟨t0, ts, rfl⟩ := List.exists_cons_of_ne_nil h1
          obtain ⟨u0, us, rfl⟩ := List.exists_cons_of_ne_nil h2
          have hts : ts = [] := by
            rcases ts with _ | ⟨_, _⟩
            · rfl
            · simp at he
          subst hts
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          refine ⟨k.val, k.isLt, (orR_gate h k _).mpr (Or.inl rfl), by rw [row_eq, ho], ?_, ?_⟩
          · rw [opnd_eq]; exact ht
          · rw [opnd_eq]; exact hu
        · rintro ⟨a, _, hr, hop, h0, h1⟩
          rcases (orR_gate h k a).mp hr with rfl | ⟨hop', _⟩
          · rw [opnd_eq] at h0 h1
            exact ⟨[p], h0, [q], h1, rfl⟩
          · rw [ho] at hop'; nomatch hop'
      · rw [ho]
        simp only [wordOp, Set.mem_union]
        rw [ih _ (earlier h k 0), ih _ (earlier h k 1)]
        constructor
        · rintro (⟨a, ha, hr, hrest⟩ | ⟨a, ha, hr, hrest⟩)
          · exact ⟨a, ha, (orR_gate h k _).mpr (Or.inr ⟨ho, Or.inl hr⟩), hrest⟩
          · exact ⟨a, ha, (orR_gate h k _).mpr (Or.inr ⟨ho, Or.inr hr⟩), hrest⟩
        · rintro ⟨a, ha, hr, hop, hrest⟩
          rcases (orR_gate h k a).mp hr with rfl | ⟨_, hr' | hr'⟩
          · rw [row_eq, ho] at hop; nomatch hop
          · exact Or.inl ⟨a, ha, hr', hop, hrest⟩
          · exact Or.inr ⟨a, ha, hr', hop, hrest⟩
    · rw [words_missing n C hb]
      constructor
      · intro hm; exact absurd hm (Set.notMem_empty _)
      · rintro ⟨a, _, hr, _⟩
        exact absurd hr (orR_missing C hb)

private lemma single_orIn {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (i : Fin n)
    (w : ℕ) : [i.val] ∈ words n C w ↔ i ∈ PEqualNP.TopForm.orIn n C w := by
  rw [single_iff h i.val i.isLt w]
  simp [PEqualNP.TopForm.orIn]

end Words

open PEqualNP.CleanedNonEdge in
theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (u v : Fin n) (huv : G.Adj u v) :
    (¬ PEqualNP.Core.ReadTwiceAt n C (C.output - n) u v ↔
      ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧
        OrToOutput n C a ∧
        ((u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) ∧
            v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1)) ∨
          (v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) ∧
            u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1)))) := by
  have hne : u ≠ v := G.ne_of_adj huv
  have hne' : u.val ≠ v.val := fun e => hne (Fin.ext e)
  -- no proof tree with a single leaf at the output
  have noSingle : ∀ i : Fin n, [i.val] ∉ words n C C.output := by
    intro i hi
    have hv : circuitValue C (fun a : Fin n => decide (a = i)) C.output = true :=
      (value_eq_terms hAO _ _).mpr ⟨[i.val], hi, fun j hj => ⟨i, (List.mem_singleton.mp hj).symm, by simp⟩⟩
    have hv' : circuitFun n C (fun a : Fin n => decide (a = i)) = true := hv
    rw [hF] at hv'
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq, decide_eq_true_eq] at hv'
    obtain ⟨a, b, hab, rfl, rfl⟩ := hv'
    exact G.ne_of_adj hab rfl
  have hout : n ≤ C.output := by
    by_contra hlt
    push Not at hlt
    apply noSingle ⟨C.output, hlt⟩
    rw [words_input C hlt]
    rfl
  have hat : PEqualNP.Core.atGate n C (C.output - n) = C := by
    cases C with
    | mk gs o =>
      simp only [PEqualNP.Core.atGate]
      simp only at hout
      congr 1
      omega
  unfold PEqualNP.Core.ReadTwiceAt
  rw [hat, Bool.not_eq_false, read_iff hAO]
  constructor
  · rintro ⟨t, ht, hts, hc⟩
    have hnd : t.Nodup := by
      refine List.nodup_iff_count_le_one.mpr fun a => ?_
      by_cases ha : a ∈ [u.val, v.val]
      · exact hc a ha
      · have : a ∉ t := fun h' => ha (hts a h')
        rw [List.count_eq_zero_of_not_mem this]
        omega
    have hlen : t.length ≤ 2 := by
      have := (List.Nodup.subperm hnd (fun a ha => hts a ha)).length_le
      simpa using this
    have hmem : ∀ a ∈ t, a = u.val ∨ a = v.val := by
      intro a ha; simpa using hts a ha
    match t, ht, hlen, hnd, hmem with
    | [], ht, _, _, _ => exact absurd rfl (words_nonempty hAO ht)
    | [a], ht, _, _, hmem =>
      rcases hmem a (by simp) with rfl | rfl
      · exact absurd ht (noSingle u)
      · exact absurd ht (noSingle v)
    | [a, b], ht, _, hnd, hmem =>
      have hab : a ≠ b := by simpa using hnd
      obtain ⟨g, hg, hr, hop, h0, h1⟩ := (pair_iff hAO a b C.output).mp ht
      refine ⟨g, hg, hop, hr, ?_⟩
      rcases hmem a (by simp) with rfl | rfl <;> rcases hmem b (by simp) with rfl | rfl
      · exact absurd rfl hab
      · exact Or.inl ⟨(single_orIn hAO u _).mp h0, (single_orIn hAO v _).mp h1⟩
      · exact Or.inr ⟨(single_orIn hAO v _).mp h0, (single_orIn hAO u _).mp h1⟩
      · exact absurd rfl hab
    | _ :: _ :: _ :: _, _, hlen, _, _ => simp at hlen
  · rintro ⟨a, ha, hop, hr, hside⟩
    rcases hside with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · have hw : [u.val, v.val] ∈ words n C C.output :=
        (pair_iff hAO _ _ _).mpr ⟨a, ha, hr, hop, (single_orIn hAO u _).mpr h0,
          (single_orIn hAO v _).mpr h1⟩
      refine ⟨_, hw, fun i hi => hi, fun i _ => ?_⟩
      exact List.nodup_iff_count_le_one.mp (by simpa using hne') i
    · have hw : [v.val, u.val] ∈ words n C C.output :=
        (pair_iff hAO _ _ _).mpr ⟨a, ha, hr, hop, (single_orIn hAO v _).mpr h0,
          (single_orIn hAO u _).mpr h1⟩
      refine ⟨_, hw, fun i hi => by simp at hi ⊢ <;> tauto, fun i _ => ?_⟩
      exact List.nodup_iff_count_le_one.mp (by simpa using hne'.symm) i

end PEqualNP.Outside.L_meta_3708

theorem PEqualNP.Outside.L_meta_3708 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  ∀ u v : Fin n, G.Adj u v →
    (¬ PEqualNP.Core.ReadTwiceAt n C (C.output - n) u v ↔
      ∃ a < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.CleanedNonEdge.OrToOutput n C a ∧
        ((u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) ∧ v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1)) ∨ (v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) ∧ u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1)))) := by
  intro n G _ C _ hAO hF u v huv
  exact PEqualNP.Outside.L_meta_3708.main n G C hAO hF u v huv
