import Mathlib.Data.List.Nodup
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2230

-- The word semantics specialize the accounting in L-meta-2466 to read-once trees.
-- The OR closure recurrence follows L-meta-1502.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


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


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadK PEqualNP.CleanedNonEdge PEqualNP.TopForm
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

private lemma mem_andStep_two (v : List ℕ) (A B : List (List ℕ)) :
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
        rw [hvec]
        unfold encode
        apply List.map_congr_left
        intro a _
        by_cases hea : a = w
        · simp [hea]
        · simp [hea, Ne.symm hea]
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
        obtain ⟨x, hx, y, hy, rfl⟩ := (mem_andStep_two _ _ _).mp hv
        obtain ⟨z, hz, x', hx', rfl⟩ := (mem_andStep_two _ _ _).mp hx
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

private lemma read_to_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (r : readsAtMost C n S 1 = true) :
    ∃ t ∈ words n C C.output, (∀ i ∈ t, i ∈ S) ∧ ∀ i ∈ S, t.count i ≤ 1 := by
  obtain ⟨v, hv, ha⟩ := List.any_eq_true.mp r
  obtain ⟨t, ht, rfl, hts⟩ := encode_witness h S C.output v hv
  refine ⟨t, ht, hts, fun i hi => ?_⟩
  have hv : min (t.count i) 2 ∈ encode S t := List.mem_map.mpr ⟨i, hi, rfl⟩
  have hb := of_decide_eq_true ((List.all_eq_true.mp ha) _ hv)
  omega


private lemma orSets_spec (n : ℕ) (gs : List Gate) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length ∧
    ∀ k < gs.length, ∀ g, g ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] ↔
      g = k ∨ ((gs.getD k ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + k ∧
          g ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g0 ih =>
    obtain ⟨hl, hs⟩ := ih
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize gs.foldl (PEqualNP.CleanedNonEdge.orStep n) [] = S at hl hs
    have hpre : ∀ i < gs.length,
        (PEqualNP.CleanedNonEdge.orStep n S g0).getD i [] = S.getD i [] := by
      intro i hi
      unfold PEqualNP.CleanedNonEdge.orStep
      exact List.getD_append _ _ _ _ (by omega)
    have hlast : ∀ g, g ∈ (PEqualNP.CleanedNonEdge.orStep n S g0).getD gs.length [] ↔
        g = gs.length ∨ (g0.op = GateOp.or ∧ ∃ w ∈ g0.inputs, n ≤ w ∧ w < n + gs.length ∧
          g ∈ S.getD (w - n) []) := by
      intro g
      unfold PEqualNP.CleanedNonEdge.orStep
      rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
      by_cases hop : g0.op = GateOp.or
      · simp [hop, and_assoc]
      · simp [hop]
    refine ⟨by simp [PEqualNP.CleanedNonEdge.orStep, hl], ?_⟩
    intro k hk g
    rw [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
    · rw [hpre k hk', List.getD_append _ _ _ _ hk', hs k hk' g]
      constructor
      · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hop, w, hw, h1, h2, by rwa [hpre _ (by omega)]⟩
      · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hop, w, hw, h1, h2, by rwa [hpre _ (by omega)] at h3⟩
    · rw [hlast g, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
      simp only [List.getD_cons_zero]
      constructor
      · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hop, w, hw, h1, h2, by rwa [hpre _ (by omega)]⟩
      · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hop, w, hw, h1, h2, by rwa [hpre _ (by omega)] at h3⟩

private lemma orReaches_def (n : ℕ) (C : Circuit) (w g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C w g ↔
      n ≤ w ∧ g ∈ (C.gates.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [] :=
  Iff.rfl

private lemma orReaches_iff (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) (g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        PEqualNP.CleanedNonEdge.OrReaches n C w g) := by
  rw [orReaches_def, Nat.add_sub_cancel_left, (orSets_spec n C.gates).2 k hk g]
  constructor
  · rintro ⟨_, h | ⟨hop, w, hw, h1, h2, h3⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, h1, h2, (orReaches_def n C w g).2 ⟨h1, h3⟩⟩
  · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
    · exact ⟨by omega, Or.inl h⟩
    · exact ⟨by omega, Or.inr ⟨hop, w, hw, h1, h2, ((orReaches_def n C w g).1 h3).2⟩⟩

private lemma row_eq (C : Circuit) (k : Fin C.size) : gateAt C k.val = row C k :=
  List.getD_eq_getElem _ _ k.isLt

private lemma operand_eq (C : Circuit) (k : Fin C.size) (p : Fin 2) :
    opnd C k.val p = operand C k p := by simp [opnd, operand, row_eq]

private lemma operand_mem {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    (k : Fin C.size) (p : Fin 2) : operand C k p ∈ (gateAt C k.val).inputs := by
  rw [row_eq, inputs_two h k]
  fin_cases p <;> simp

private lemma lift_reach {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    (k : Fin C.size) (p : Fin 2) (ho : (row C k).op = GateOp.or) {j : ℕ}
    (hr : OrReaches n C (operand C k p) j) : OrReaches n C (outWire n k) j :=
  (orReaches_iff n C k.val k.isLt j).2 (Or.inr ⟨(row_eq C k).symm ▸ ho,
    operand C k p, operand_mem h k p, hr.1, earlier h k p, hr⟩)

private lemma lift_input {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    (k : Fin C.size) (p : Fin 2) (ho : (row C k).op = GateOp.or) {a : Fin n}
    (ha : a ∈ orIn n C (operand C k p)) : a ∈ orIn n C (outWire n k) := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  apply Or.inr
  rcases ha with he | ⟨j, hj, hr, hor, hm⟩
  · exact ⟨k.val, k.isLt, (orReaches_iff n C k.val k.isLt _).2 (Or.inl rfl),
      (row_eq C k).symm ▸ ho, he.symm ▸ operand_mem h k p⟩
  · exact ⟨j, hj, lift_reach h k p ho hr, hor, hm⟩

private lemma singleton_input {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    (a : Fin n) (w : ℕ) (ht : [a.val] ∈ words n C w) : a ∈ orIn n C w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb] at ht
      have he : [a.val] = [w] := ht
      simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl (List.cons.inj he).1
    · rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · rw [ho] at ht
        obtain ⟨u, hu, v, hv, he⟩ := ht
        have h1 := List.length_pos_iff.mpr (words_nonempty h hu)
        have h2 := List.length_pos_iff.mpr (words_nonempty h hv)
        have hl := congrArg List.length he
        simp only [List.length_cons, List.length_nil, List.length_append] at hl
        omega
      · rw [ho] at ht
        exact ht.elim (fun hx => lift_input h k 0 ho (ih _ (earlier h k 0) hx))
          (fun hx => lift_input h k 1 ho (ih _ (earlier h k 1) hx))
    · simp [words_missing n C hb] at ht

private lemma pair_gate {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    (a b : Fin n) (w : ℕ) (ht : [a.val, b.val] ∈ words n C w) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ OrReaches n C w j ∧
      a ∈ side C j 0 ∧ b ∈ side C j 1 := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb] at ht
      have he : [a.val, b.val] = [w] := ht
      simp at he
    · rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · rw [ho] at ht
        obtain ⟨u, hu, v, hv, he⟩ := ht
        have h1 := List.length_pos_iff.mpr (words_nonempty h hu)
        have h2 := List.length_pos_iff.mpr (words_nonempty h hv)
        have hl := congrArg List.length he
        simp only [List.length_cons, List.length_nil, List.length_append] at hl
        obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp (show u.length = 1 by omega)
        obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp (show v.length = 1 by omega)
        change [a.val, b.val] = [x, y] at he
        cases he
        exact ⟨k.val, k.isLt, (row_eq C k).symm ▸ ho,
          (orReaches_iff n C k.val k.isLt _).2 (Or.inl rfl),
          by simpa only [side, operand_eq] using singleton_input h a _ hu,
          by simpa only [side, operand_eq] using singleton_input h b _ hv⟩
      · rw [ho] at ht
        have up (p : Fin 2) (hp : [a.val, b.val] ∈ words n C (operand C k p)) :
            ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
              OrReaches n C (outWire n k) j ∧ a ∈ side C j 0 ∧ b ∈ side C j 1 := by
          obtain ⟨j, hj, hop, hr, hs⟩ := ih _ (earlier h k p) hp
          exact ⟨j, hj, hop, lift_reach h k p ho hr, hs⟩
        exact ht.elim (up 0) (up 1)
    · simp [words_missing n C hb] at ht

end PEqualNP.Outside.L_meta_2230

open PEqualNP.Outside.L_meta_2230
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

theorem PEqualNP.Outside.L_meta_2230 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin n), PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → a < b → PEqualNP.ReadK.readsAtMost C n [a.val, b.val] 1 = true → ∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j ∧ ((a ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ b ∈ PEqualNP.TopForm.side (n := n) C j 1) ∨ (b ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ a ∈ PEqualNP.TopForm.side (n := n) C j 1)) := by
  intro n C a b h hz hab hread
  obtain ⟨t, ht, hs, hc⟩ := read_to_terms h [a.val, b.val] hread
  have hn : t.Nodup := List.nodup_iff_count_le_one.mpr (fun i => by
    by_cases hi : i ∈ t
    · exact hc i (hs i hi)
    · simp [List.count_eq_zero_of_not_mem hi])
  have hl := hn.length_le_of_subset (show t ⊆ [a.val, b.val] from fun _ hi => hs _ hi)
  have both (x y : Fin n) (hxy : ∀ i ∈ t, i = x.val ∨ i = y.val) : x.val ∈ t := by
    by_contra hx
    have hv : circuitValue C (fun k => decide (k = y)) C.output = true := by
      apply (value_eq_terms h _ _).2
      refine ⟨t, ht, fun i hi => ?_⟩
      rcases hxy i hi with he | he
      · exact False.elim (hx (he ▸ hi))
      · exact ⟨y, he.symm, by simp⟩
    change circuitFun n C (fun k => decide (k = y)) = true at hv
    simp [hz] at hv
  have hs' (i : ℕ) (hi : i ∈ t) : i = a.val ∨ i = b.val := by simpa using hs i hi
  have ha := both a b hs'
  have hb := both b a (fun i hi => (hs' i hi).symm)
  have hne : a.val ≠ b.val := Nat.ne_of_lt hab
  have hlo := (show [a.val, b.val].Nodup by simp [hne]).length_le_of_subset
    (show [a.val, b.val] ⊆ t by simpa using And.intro ha hb)
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp (show t.length = 2 by simpa using Nat.le_antisymm hl hlo)
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact False.elim (hne (ha.trans hb.symm))
  · obtain ⟨j, hj, hop, hr, hsides⟩ := pair_gate h a b C.output (by simpa only [ha, hb] using ht)
    exact ⟨j, hj, hop, hr, Or.inl hsides⟩
  · obtain ⟨j, hj, hop, hr, hsides⟩ := pair_gate h b a C.output (by simpa only [ha, hb] using ht)
    exact ⟨j, hj, hop, hr, Or.inr hsides⟩
  · exact False.elim (hne (ha.trans hb.symm))
