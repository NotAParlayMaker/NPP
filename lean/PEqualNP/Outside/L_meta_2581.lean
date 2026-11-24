import Mathlib

import PEqualNP.Defs



/-!
A proof tree for an incident pair has at most six leaves. Removing that incidence makes
its word independent. Each wire retains a bounded family of independent words that
represents all queries from the rest of the tree of combined length at most six. A gate charges the
exceptional incidences for which deleting the edge can change this representation.

The read-vector and word interpretation in Base adapts the checked L_meta_1942 proof.
-/
namespace PEqualNP.Outside.L_meta_2581
namespace Base


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

section Circuit

def evalFrom {α : Type} (d : α) (op : GateOp → List α → α) (gates : List Gate) (xs : List α) :
    List α :=
  gates.foldl (fun u g => u ++ [op g.op (g.inputs.map fun i => u.getD i d)]) xs

lemma evalFrom_cons {α : Type} (d : α) (op : GateOp → List α → α) (g : Gate) (gs : List Gate)
    (xs : List α) :
    evalFrom d op (g :: gs) xs = evalFrom d op gs
      (xs ++ [op g.op (g.inputs.map fun i => xs.getD i d)]) := rfl

lemma evalFrom_length {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) : (evalFrom d op gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalFrom]
  | cons g gs ih => rw [evalFrom_cons, ih]; simp; omega

lemma evalFrom_input {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (evalFrom d op gs xs).getD i d = xs.getD i d := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [evalFrom_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

def row (C : Circuit) (k : Fin C.size) : Gate := C.gates[k.val]'k.isLt

def operand (C : Circuit) (k : Fin C.size) (b : Fin 2) : ℕ :=
  (row C k).inputs.getD b.val 0

def outWire (n : ℕ) {s : ℕ} (k : Fin s) : ℕ := n + k.val

lemma inputs_two {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).inputs = [operand C k 0, operand C k 1] := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h.2.2 (row C k) (List.getElem_mem _))
  simp [operand, hab]

lemma op_kind {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).op = GateOp.and ∨ (row C k).op = GateOp.or :=
  h.1 (row C k) (List.getElem_mem _)

lemma earlier {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (k : Fin C.size) (b : Fin 2) : operand C k b < outWire n k := by
  have he : gateAt C k.val = row C k := List.getD_eq_getElem _ _ k.isLt
  have hm : operand C k b ∈ (row C k).inputs := by
    rw [inputs_two h k]
    fin_cases b <;> simp
  exact h.2.1 k.val k.isLt (operand C k b) (by simpa only [he] using hm)

lemma evalFrom_gate {α : Type} (d : α) (op : GateOp → List α → α) {n : ℕ}
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

lemma wire_cases (n s w : ℕ) :
    w < n ∨ (∃ k : Fin s, w = outWire n k) ∨ n + s ≤ w := by
  by_cases hb : w < n
  · exact Or.inl hb
  by_cases he : w < n + s
  · exact Or.inr (Or.inl ⟨⟨w - n, by omega⟩, by simp [outWire]; omega⟩)
  · exact Or.inr (Or.inr (by omega))

def wordOp : GateOp → List (Set (List ℕ)) → Set (List ℕ)
  | .or, [a, b] => a ∪ b
  | .and, [a, b] => {t | ∃ u ∈ a, ∃ v ∈ b, t = u ++ v}
  | _, _ => ∅

def wordList (n : ℕ) (C : Circuit) : List (Set (List ℕ)) :=
  evalFrom ∅ wordOp C.gates (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ))))

def words (n : ℕ) (C : Circuit) (w : ℕ) : Set (List ℕ) :=
  (wordList n C).getD w ∅

lemma words_input {n : ℕ} (C : Circuit) {w : ℕ} (hw : w < n) :
    words n C w = {[w]} := by
  unfold words wordList
  have hi : w < (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ)))).length := by
    simpa using hw
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

lemma words_missing (n : ℕ) (C : Circuit) {w : ℕ} (hw : n + C.size ≤ w) :
    words n C w = ∅ :=
  List.getD_eq_default _ _ (by simpa [wordList, evalFrom_length, Circuit.size] using hw)

lemma words_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    words n C (outWire n k) =
      wordOp (row C k).op [words n C (operand C k 0), words n C (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

def circuitValue {n : ℕ} (C : Circuit) (z : Fin n → Bool) (w : ℕ) : Bool :=
  (evalFrom false GateOp.eval C.gates (List.ofFn z)).getD w false

lemma value_input {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ} (hw : w < n) :
    circuitValue C z w = z ⟨w, hw⟩ := by
  have hi : w < (List.ofFn z).length := by simpa using hw
  unfold circuitValue
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

lemma value_missing {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ}
    (hw : n + C.size ≤ w) : circuitValue C z w = false :=
  List.getD_eq_default _ _ (by simpa [evalFrom_length, Circuit.size] using hw)

lemma value_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (z : Fin n → Bool) (k : Fin C.size) :
    circuitValue C z (outWire n k) = (row C k).op.eval
      [circuitValue C z (operand C k 0), circuitValue C z (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

lemma value_eq_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
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

end Circuit


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma cast_ne_nat {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have he := congrArg Fin.val h
  change p.val = N + l.val at he
  omega

section ReadWitness

-- Decode capped multiplicities into actual words of input leaves.

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

lemma mem_insertNew (a v : List ℕ) (A : List (List ℕ)) :
    v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
  unfold insertNew
  by_cases ha : a ∈ A
  · simp [ha, or_iff_left_of_imp (fun (e : v = a) => e.symm ▸ ha)]
  · simp [ha]

lemma mem_fold_insertNew (v : List ℕ) (B A : List (List ℕ)) :
    v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons b B ih => simp [ih, mem_insertNew, or_assoc]

lemma mem_andStep_two (v : List ℕ) (A B : List (List ℕ)) :
    v ∈ andStep 3 A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd 3 u w := by
  simp [andStep, mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]

def encode (S t : List ℕ) : List ℕ :=
  S.map fun j => min (t.count j) 4

lemma encode_nil (S : List ℕ) : encode S [] = S.map (fun _ => 0) := by
  simp [encode]

lemma encode_append (S t u : List ℕ) :
    capAdd 3 (encode S t) (encode S u) = encode S (t ++ u) := by
  induction S with
  | nil => rfl
  | cons a S ih =>
    simp only [encode, capAdd, List.map_cons, List.zipWith_cons_cons, List.count_append] at ih ⊢
    rw [ih]
    congr 1
    omega

def readOp (S : List ℕ) (o : GateOp) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match o with
  | .or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | .and => ins.foldl (andStep 3) [S.map fun _ => 0]
  | _ => []

def vecs (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) : List (List ℕ) :=
  ((readVectors C n S 3).getD w [])

lemma vec_eval (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) :
    vecs n C S w =
      (evalFrom [] (readOp S) C.gates ((List.range n).map (leafVectors S 3))).getD w [] :=
  rfl

lemma encode_witness {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (w : ℕ) (v : List ℕ) (hv : v ∈ vecs n C S w) :
    ∃ t ∈ words n C w, v = encode S t ∧ ∀ i ∈ t, i ∈ S := by
  induction w using Nat.strong_induction_on generalizing v with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · have hi : w < ((List.range n).map (leafVectors S 3)).length := by simpa using hb
      rw [vec_eval, evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi] at hv
      simp only [List.getElem_map, List.getElem_range] at hv
      rw [words_input C hb]
      by_cases hs : w ∈ S
      · refine ⟨[w], rfl, ?_, by simpa using hs⟩
        have hvec : v = S.map (fun j => if j = w then min 1 (3 + 1) else 0) := by
          simpa only [leafVectors, hs, ite_true, List.mem_singleton] using hv
        rw [hvec]
        unfold encode
        apply List.map_congr_left
        intro a _
        by_cases hea : a = w
        · simp [hea]
        · simp [hea, Ne.symm hea]
      · simp [leafVectors, hs] at hv
    · have hlen : ((List.range n).map (leafVectors S 3)).length = n := by simp
      have hvec := evalFrom_gate ([] : List (List ℕ)) (readOp S) h _ hlen k
      rw [← vec_eval, ← vec_eval, ← vec_eval] at hvec
      rw [hvec] at hv
      rw [words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho] at hv ⊢
        change v ∈ andStep 3 (andStep 3 [S.map (fun _ => 0)] (vecs n C S (operand C k 0)))
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

lemma read_to_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (r : readsAtMost C n S 3 = true) :
    ∃ t ∈ words n C C.output, (∀ i ∈ t, i ∈ S) ∧ ∀ i ∈ S, t.count i ≤ 3 := by
  obtain ⟨v, hv, ha⟩ := List.any_eq_true.mp r
  obtain ⟨t, ht, rfl, hts⟩ := encode_witness h S C.output v hv
  refine ⟨t, ht, hts, fun i hi => ?_⟩
  have hv : min (t.count i) 4 ∈ encode S t := List.mem_map.mpr ⟨i, hi, rfl⟩
  have hb := of_decide_eq_true ((List.all_eq_true.mp ha) _ hv)
  omega

end ReadWitness


section Degrees

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def on (N : ℕ) (X Y : Set (Fin N)) (w : ℕ) : Prop :=
  (∃ p ∈ X, (p : ℕ) = w) ∨ ∃ l ∈ Y, N + (l : ℕ) = w

lemma on_point {N : ℕ} (X Y : Set (Fin N)) (p : Fin N) :
    on N X Y p.val ↔ p ∈ X := by
  constructor
  · rintro (⟨q, hq, hv⟩ | ⟨l, _, hv⟩)
    · exact (Fin.ext hv : q = p) ▸ hq
    · omega
  · exact fun hp => Or.inl ⟨p, hp, rfl⟩

lemma on_line {N : ℕ} (X Y : Set (Fin N)) (l : Fin N) :
    on N X Y (N + l.val) ↔ l ∈ Y := by
  constructor
  · rintro (⟨p, _, hv⟩ | ⟨l', hl', hv⟩)
    · omega
    · exact (Fin.ext (Nat.add_left_cancel hv) : l' = l) ▸ hl'
  · exact fun hl => Or.inr ⟨l, hl, rfl⟩

noncomputable def bits {N : ℕ} (X Y : Set (Fin N)) (i : Fin (N + N)) : Bool := by
  classical
  exact decide (on N X Y i.val)

lemma bits_true {N : ℕ} (X Y : Set (Fin N)) (i : Fin (N + N)) :
    bits X Y i = true ↔ on N X Y i.val := by
  classical
  simp [bits]

def pcount (N : ℕ) (t : List ℕ) : ℕ := (t.filter fun w => decide (w < N)).length
def lcount (N : ℕ) (t : List ℕ) : ℕ := (t.filter fun w => decide (N ≤ w)).length

lemma sum_counts (N : ℕ) (t : List ℕ) : pcount N t + lcount N t = t.length := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    by_cases h : a < N
    · have hn : ¬ N ≤ a := by omega
      simp [pcount, lcount, h, hn] at ih ⊢
      omega
    · have hn : N ≤ a := by omega
      simp [pcount, lcount, h, hn] at ih ⊢
      omega

def Hom (N : ℕ) (C : Circuit) (w a b : ℕ) (X Y : Set (Fin N)) : Prop :=
  ∃ t ∈ words (N + N) C w, pcount N t = a ∧ lcount N t = b ∧ ∀ j ∈ t, on N X Y j

lemma hom_mono {N : ℕ} {C : Circuit} {w a b : ℕ} {X X' Y Y' : Set (Fin N)}
    (hx : X ⊆ X') (hy : Y ⊆ Y') (h : Hom N C w a b X Y) : Hom N C w a b X' Y' := by
  obtain ⟨t, ht, ha, hb, hxy⟩ := h
  exact ⟨t, ht, ha, hb, fun j hj => (hxy j hj).imp
    (fun ⟨p, hp, he⟩ => ⟨p, hx hp, he⟩) (fun ⟨l, hl, he⟩ => ⟨l, hy hl, he⟩)⟩

lemma hom_pure_x {N : ℕ} {C : Circuit} {w a : ℕ} {X Y : Set (Fin N)} :
    Hom N C w a 0 X Y ↔ Hom N C w a 0 X ∅ := by
  refine ⟨?_, hom_mono (fun _ h => h) (Set.empty_subset _)⟩
  rintro ⟨t, ht, ha, hb, hxy⟩
  refine ⟨t, ht, ha, hb, fun j hj => ?_⟩
  rcases hxy j hj with hp | ⟨l, _, hl⟩
  · exact Or.inl hp
  · have hn : N ≤ j := by omega
    have hmem : j ∈ t.filter (fun w => decide (N ≤ w)) := List.mem_filter.mpr ⟨hj, by simp [hn]⟩
    unfold lcount at hb
    rw [List.length_eq_zero_iff.mp hb] at hmem
    simp at hmem

lemma hom_pure_y {N : ℕ} {C : Circuit} {w b : ℕ} {X Y : Set (Fin N)} :
    Hom N C w 0 b X Y ↔ Hom N C w 0 b ∅ Y := by
  refine ⟨?_, hom_mono (Set.empty_subset _) (fun _ h => h)⟩
  rintro ⟨t, ht, ha, hb, hxy⟩
  refine ⟨t, ht, ha, hb, fun j hj => ?_⟩
  rcases hxy j hj with ⟨p, _, hp⟩ | hl
  · have hn : j < N := hp ▸ p.isLt
    have hmem : j ∈ t.filter (fun w => decide (w < N)) := List.mem_filter.mpr ⟨hj, by simp [hn]⟩
    unfold pcount at ha
    rw [List.length_eq_zero_iff.mp ha] at hmem
    simp at hmem
  · exact Or.inr hl

lemma hom_sound {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w a b : ℕ} {X Y : Set (Fin N)} (hh : Hom N C w a b X Y) :
    circuitValue C (bits X Y) w = true := by
  obtain ⟨t, ht, _, _, hxy⟩ := hh
  apply (value_eq_terms h _ _).mpr
  refine ⟨t, ht, fun j hj => ?_⟩
  rcases hxy j hj with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
  · exact ⟨Fin.castAdd N p, rfl, (bits_true _ _ _).mpr ((on_point X Y p).mpr hp)⟩
  · exact ⟨Fin.natAdd N l, rfl, (bits_true _ _ _).mpr ((on_line X Y l).mpr hl)⟩

lemma hom_output_safe {N : ℕ} {C : Circuit} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {a b : ℕ} {X Y : Set (Fin N)} (hh : Hom N C C.output a b X Y) :
    ∃ p ∈ X, ∃ l ∈ Y, I p l := by
  have hv := hom_sound h hh
  change circuitFun (N + N) C (bits X Y) = true at hv
  rw [hC, decide_eq_true_eq] at hv
  obtain ⟨p, l, hi, hp, hl⟩ := hv
  exact ⟨p, (on_point X Y p).mp ((bits_true _ _ _).mp hp),
    l, (on_line X Y l).mp ((bits_true _ _ _).mp hl), hi⟩

end Degrees


open Finset

section Plane

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

variable {N : ℕ} {C : Circuit}
variable (I : Fin N → Fin N → Prop) [DecidableRel I]

lemma pair_prime
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p l : Fin N} (hi : I p l) :
    IsPrimeImplicant (N + N) C {Fin.castAdd N p, Fin.natAdd N l} := by
  classical
  constructor
  · rw [hC, decide_eq_true_eq]
    exact ⟨p, l, hi, by simp [setInput], by simp [setInput]⟩
  · intro T hT
    have hT' := Finset.mem_ssubsets.mp hT
    rw [hC, decide_eq_false_iff_not]
    rintro ⟨p', l', _, hp, hl⟩
    have hp' : Fin.castAdd N p' ∈ T := of_decide_eq_true hp
    have hl' : Fin.natAdd N l' ∈ T := of_decide_eq_true hl
    have pe : Fin.castAdd N p' = Fin.castAdd N p := by
      have := Finset.mem_insert.mp (hT'.subset hp')
      exact this.resolve_right (fun hm => cast_ne_nat p' l (Finset.mem_singleton.mp hm))
    have le : Fin.natAdd N l' = Fin.natAdd N l := by
      have := Finset.mem_insert.mp (hT'.subset hl')
      exact Finset.mem_singleton.mp (this.resolve_left (fun e => cast_ne_nat p l' e.symm))
    exact hT'.not_ge (by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · simpa only [pe] using hp'
      · rw [Finset.mem_singleton.mp hw, ← le]
        exact hl')

lemma setList_pair {p l : Fin N} (j : ℕ) :
    j ∈ setList ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) ↔
      j = p.val ∨ j = N + l.val := by
  simp only [setList, List.mem_map, List.mem_filter, decide_eq_true_eq, List.mem_finRange,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Fin.castAdd N p, Or.inl rfl, rfl⟩
    · exact ⟨Fin.natAdd N l, Or.inr rfl, rfl⟩

lemma pair_counts {p l : Fin N} (t : List ℕ)
    (ht : ∀ a ∈ t, a = p.val ∨ a = N + l.val) :
    pcount N t = t.count p.val ∧ lcount N t = t.count (N + l.val) := by
  have hp : p.val < N := p.isLt
  have hne : p.val ≠ N + l.val := by omega
  have hl : ¬ N + l.val < N := by omega
  induction t with
  | nil => simp [pcount, lcount]
  | cons j t ih =>
    obtain ⟨h1, h2⟩ := ih (fun a ha => ht a (List.mem_cons_of_mem _ ha))
    change (t.filter _).length = _ at h1 h2
    rcases ht j (by simp) with rfl | rfl
    · have hpn : ¬ N ≤ p.val := by omega
      simp [pcount, lcount, hp, hpn, hne, h1, h2]
    · simp [pcount, lcount, hl, Ne.symm hne, h1, h2]

lemma plane_read_cover
    (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (hr : IsReadK (N + N) C 3) {p l : Fin N} (hi : I p l) :
    ∃ a b : ℕ, 1 ≤ a ∧ a ≤ 3 ∧ 1 ≤ b ∧ b ≤ 3 ∧ Hom N C C.output a b {p} {l} := by
  obtain ⟨t, ht, hs, hu⟩ := read_to_terms h _
    (hr {Fin.castAdd N p, Fin.natAdd N l} (pair_prime I hC hi))
  obtain ⟨hp, hl⟩ := pair_counts (p := p) (l := l) t
    (fun j hj => (setList_pair j).mp (hs j hj))
  have hh : Hom N C C.output (pcount N t) (lcount N t) {p} {l} := by
    refine ⟨t, ht, rfl, rfl, fun j hj => ?_⟩
    rcases (setList_pair j).mp (hs j hj) with rfl | rfl
    · exact (on_point _ _ p).mpr (by simp)
    · exact (on_line _ _ l).mpr (by simp)
  have hp1 : 1 ≤ pcount N t := by
    by_contra! hn
    have he : pcount N t = 0 := by omega
    rw [he] at hh
    obtain ⟨a, ha, _⟩ := hom_output_safe I h hC (hom_pure_y.mp hh)
    exact ha
  have hl1 : 1 ≤ lcount N t := by
    by_contra! hn
    have he : lcount N t = 0 := by omega
    rw [he] at hh
    obtain ⟨_, _, b, hb, _⟩ := hom_output_safe I h hC (hom_pure_x.mp hh)
    exact hb
  exact ⟨_, _, hp1, hp ▸ hu _ ((setList_pair _).mpr (Or.inl rfl)),
    hl1, hl ▸ hu _ ((setList_pair _).mpr (Or.inr rfl)), hh⟩

noncomputable def allEdges : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2)

lemma allEdges_card (q : ℕ)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    (allEdges I).card = N * (q + 1) := by
  classical
  let F (l : Fin N) : Finset (Fin N × Fin N) :=
    (Finset.univ.filter (fun p => I p l)).map ⟨fun p => (p, l), fun _ _ h => congrArg Prod.fst h⟩
  have hF (l : Fin N) (e : Fin N × Fin N) : e ∈ F l ↔ I e.1 l ∧ e.2 = l := by
    constructor
    · intro he
      obtain ⟨p, hp, ht⟩ := Finset.mem_map.mp he
      change (p, l) = e at ht
      rw [← ht]
      exact ⟨(Finset.mem_filter.mp hp).2, rfl⟩
    · rintro ⟨hi, hh⟩
      refine Finset.mem_map.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
      exact Prod.ext rfl hh.symm
  have heq : allEdges I = Finset.univ.biUnion F := by
    ext e
    simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, hF]
    exact ⟨fun h => ⟨e.2, h, rfl⟩, fun ⟨l, hi, he⟩ => he ▸ hi⟩
  rw [heq, Finset.card_biUnion]
  · simp [F, hL]
  · intro l _ l' _ hne
    refine Finset.disjoint_left.mpr ?_
    intro e he he'
    exact hne (((hF l e).mp he).2.symm.trans ((hF l' e).mp he').2)

end Plane
end Base
end PEqualNP.Outside.L_meta_2581

namespace PEqualNP.Outside.L_meta_2581
namespace Small
open Finset
def tower (c : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => c * tower c n + 1

private lemma canon {K : Type*} [Fintype K] [Nonempty K] (f : Nat → Nat → K) (n : Nat)
    (S : Finset Nat) (hs : tower (Fintype.card K) n ≤ S.card) :
    ∃ T ⊆ S, n ≤ T.card ∧ ∀ x ∈ T, ∃ c, ∀ y ∈ T, x < y → f x y = c := by
  classical
  induction n generalizing S with
  | zero => exact ⟨∅,empty_subset _,by simp,by simp⟩
  | succ n ih =>
    have hne : S.Nonempty := card_pos.mp (by simp only [tower] at hs; omega)
    let x := S.min' hne
    have hx : x ∈ S := S.min'_mem hne
    have htail : Fintype.card K * tower (Fintype.card K) n ≤ (S.erase x).card := by
      rw [card_erase_of_mem hx]
      simp only [tower] at hs
      omega
    obtain ⟨c,_,hc⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s:=S.erase x) (t:=(univ : Finset K)) (f:=f x) (fun y _ => mem_univ _)
      univ_nonempty (by simpa using htail)
    obtain ⟨T,hT,ht,hmono⟩ := ih _ hc
    have inS {y} (hy : y ∈ T) : y ∈ S := mem_of_mem_erase (mem_filter.mp (hT hy)).1
    have gt {y} (hy : y ∈ T) : x < y := by
      have ne := (mem_erase.mp (mem_filter.mp (hT hy)).1).1
      exact lt_of_le_of_ne (S.min'_le y (inS hy)) (Ne.symm ne)
    have hnx : x ∉ T := fun h => (Nat.lt_irrefl _ (gt h))
    refine ⟨insert x T, insert_subset hx (fun _ h => inS h),by rw [card_insert_of_notMem hnx]; omega,?_⟩
    intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · refine ⟨c,fun y hy hxy => ?_⟩
      exact (mem_filter.mp (hT ((mem_insert.mp hy).resolve_left (Ne.symm (Nat.ne_of_lt hxy))))).2
    · obtain ⟨c',hh⟩ := hmono _ ha
      refine ⟨c',fun y hy hxy => ?_⟩
      rcases mem_insert.mp hy with rfl | hy
      · exact (lt_asymm hxy (gt ha)).elim
      · exact hh _ hy hxy

def limit (c : Nat) := tower c (4*c)

theorem four {K : Type*} [Fintype K] [Nonempty K] (f : Nat → Nat → K) (m : Nat)
    (hm : limit (Fintype.card K) ≤ m) :
    ∃ a b c d : Nat, a < b ∧ b < c ∧ c < d ∧ d < m ∧
      f a b = f a c ∧ f a b = f a d ∧ f a b = f b c ∧ f a b = f b d ∧ f a b = f c d := by
  classical
  obtain ⟨T,hT,ht,hf⟩ := canon f (4*Fintype.card K) (range m) (by simpa [limit] using hm)
  let col (x : Nat) : K := if h : x ∈ T then Classical.choose (hf x h) else Classical.choice inferInstance
  have spec {x y} (hx : x ∈ T) (hy : y ∈ T) (hxy : x < y) : f x y = col x := by
    rw [show col x = _ from dite_eq_left hx]
    exact Classical.choose_spec (hf x hx) _ hy hxy
  obtain ⟨v,_,hv⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to (s:=T) (t:=(univ : Finset K))
    (f:=col) (n:=4) (fun x _ => mem_univ _) univ_nonempty (by simpa [Nat.mul_comm] using ht)
  let D := T.filter fun x => col x = v
  have hcard : 4 ≤ D.card := hv
  let emb := D.orderEmbOfFin rfl
  let a := emb ⟨0,by omega⟩
  let b := emb ⟨1,by omega⟩
  let c := emb ⟨2,by omega⟩
  let d := emb ⟨3,by omega⟩
  have hab : a < b := emb.strictMono (show (0 : Nat) < 1 by decide)
  have hbc : b < c := emb.strictMono (show (1 : Nat) < 2 by decide)
  have hcd : c < d := emb.strictMono (show (2 : Nat) < 3 by decide)
  have ha : a ∈ D := orderEmbOfFin_mem _ _ _
  have hb : b ∈ D := orderEmbOfFin_mem _ _ _
  have hc : c ∈ D := orderEmbOfFin_mem _ _ _
  have hd : d ∈ D := orderEmbOfFin_mem _ _ _
  have hcolor {x y} (hx : x ∈ D) (hy : y ∈ D) (hxy : x < y) : f x y = v :=
    (spec (mem_filter.mp hx).1 (mem_filter.mp hy).1 hxy).trans (mem_filter.mp hx).2
  have vab := hcolor ha hb hab
  exact ⟨a,b,c,d,hab,hbc,hcd,mem_range.mp (hT (mem_filter.mp hd).1),
    vab.trans (hcolor ha hc (hab.trans hbc)).symm,vab.trans (hcolor ha hd (hab.trans (hbc.trans hcd))).symm,
    vab.trans (hcolor hb hc hbc).symm,vab.trans (hcolor hb hd (hbc.trans hcd)).symm,vab.trans (hcolor hc hd hcd).symm⟩
end Small
end PEqualNP.Outside.L_meta_2581

namespace PEqualNP.Outside.L_meta_2581
namespace Small
open Finset

abbrev Word := List Nat
abbrev Col := Fin 6 × Fin 6
def rankBound := limit (Fintype.card Col)
def sparse (R : Nat → Nat → Prop) := ∀ x z y u, x ≠ z → y ≠ u → R x y → R x u → R z y → ¬R z u
def avoids (R : Nat → Nat → Prop) (t c : Word) := ∀ x ∈ t, ∀ y ∈ c, ¬ R x y
def represents (R : Nat → Nat → Prop) (F D : Finset Word) :=
  ∀ t ∈ F, ∀ c : Word, c.length ≤ 6 → avoids R t c → ∃ u ∈ D, avoids R u c

theorem representatives (R : Nat → Nat → Prop) (hR : sparse R)
    (F : Finset Word) (hF : ∀ w ∈ F, w.length ≤ 6) :
    ∃ D ⊆ F, represents R F D ∧ D.card ≤ rankBound := by
  classical
  have ex : ∃ n, ∃ D ⊆ F, represents R F D ∧ D.card=n :=
    ⟨F.card,F,Subset.rfl,fun t ht _ _ hh => ⟨t,ht,hh⟩,rfl⟩
  obtain ⟨D,sub,rep,eq⟩ := Nat.find_spec ex
  refine ⟨D,sub,rep,?_⟩
  by_contra! big
  have priv (w : Word) (hw : w ∈ D) : ∃ c : Word, c.length ≤ 6 ∧ avoids R w c ∧
      ∀ u ∈ D, u ≠ w → ¬avoids R u c := by
    have fail : ¬represents R F (D.erase w) := by
      intro yes
      have small := Nat.find_min' ex ⟨D.erase w,(erase_subset _ _).trans sub,yes,rfl⟩
      have less := card_erase_lt_of_mem hw
      omega
    unfold represents at fail
    push Not at fail
    obtain ⟨t,ht,c,hc,good,bad⟩ := fail
    obtain ⟨u,hu,huc⟩ := rep t ht c hc good
    have he : u=w := by
      by_contra ne
      exact bad u (mem_erase.mpr ⟨ne,hu⟩) huc
    refine ⟨c,hc,he ▸ huc,?_⟩
    intro z hz hzw
    exact bad z (mem_erase.mpr ⟨hzw,hz⟩)
  let emb := D.orderEmbOfFin rfl
  let word (i : Nat) := if h : i < D.card then emb ⟨i,h⟩ else []
  have word_mem (i : Nat) (hi : i < D.card) : word i ∈ D := by
    simp only [word,dite_eq_left hi]; exact orderEmbOfFin_mem _ _ _
  let qry (i : Nat) := if h : i < D.card then Classical.choose (priv (word i) (word_mem i h)) else []
  have spec (i : Nat) (hi : i < D.card) : (qry i).length ≤ 6 ∧ avoids R (word i) (qry i) ∧
      ∀ u ∈ D, u ≠ word i → ¬avoids R u (qry i) := by
    simpa only [qry,dite_eq_left hi] using Classical.choose_spec (priv (word i) (word_mem i hi))
  let works (i j : Nat) (z : Col) :=
    (word i).getD z.1.val 0 ∈ word i ∧ (qry j).getD z.2.val 0 ∈ qry j ∧
      R ((word i).getD z.1.val 0) ((qry j).getD z.2.val 0)
  have chooseCol {i j : Nat} (hij : i<j) (hj : j<D.card) : ∃ z, works i j z := by
    have hi := hij.trans hj
    have hne : word i ≠ word j := by
      intro e
      have hh : (⟨i,hi⟩ : Fin D.card) = ⟨j,hj⟩ := emb.injective (by simpa only [word,dite_eq_left hi,dite_eq_left hj] using e)
      exact Nat.ne_of_lt hij (congrArg Fin.val hh)
    have hbad := (spec j hj).2.2 (word i) (word_mem i hi) hne
    unfold avoids at hbad
    push Not at hbad
    obtain ⟨x,hx,y,hy,hxy⟩ := hbad
    obtain ⟨a,ha,eqA⟩ := List.getElem_of_mem hx
    obtain ⟨b,hb,eqB⟩ := List.getElem_of_mem hy
    have wa := hF _ (sub (word_mem i hi))
    have wb := (spec j hj).1
    refine ⟨(⟨a,by omega⟩,⟨b,by omega⟩),?_⟩
    change (word i).getD a 0 ∈ _ ∧ (qry j).getD b 0 ∈ _ ∧ _
    simpa only [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb, eqA, eqB] using And.intro hx (And.intro hy hxy)
  let color (i j : Nat) : Col := if h : ∃ z, works i j z then Classical.choose h else (0,0)
  have hwc (i j : Nat) (h : i<j) (hj : j<D.card) : works i j (color i j) := by
    have ⟨z,hz⟩ := chooseCol h hj
    have existsZ : ∃ z, works i j z := ⟨z,hz⟩
    simpa only [color,dite_eq_left existsZ] using Classical.choose_spec existsZ
  obtain ⟨a,b,c,d,ab,bc,cd,dh,eac,ead,ebc,ebd,ecd⟩ := four color D.card (le_of_lt big)
  let z := color a b
  have hab : works a b z := hwc _ _ ab (by omega)
  have hac : works a c z := by dsimp only [z]; rw [eac]; exact hwc _ _ (by omega) (by omega)
  have had : works a d z := by dsimp only [z]; rw [ead]; exact hwc _ _ (by omega) dh
  have hbc : works b c z := by dsimp only [z]; rw [ebc]; exact hwc _ _ bc (by omega)
  have hbd : works b d z := by dsimp only [z]; rw [ebd]; exact hwc _ _ (by omega) dh
  have hcd : works c d z := by dsimp only [z]; rw [ecd]; exact hwc _ _ cd dh
  have nx : (word a).getD z.1.val 0 ≠ (word b).getD z.1.val 0 := by
    intro eq
    exact (spec b (by omega)).2.1 _ hbc.1 _ hab.2.1 (eq ▸ hab.2.2)
  have ny : (qry c).getD z.2.val 0 ≠ (qry d).getD z.2.val 0 := by
    intro eq
    exact (spec c (by omega)).2.1 _ hcd.1 _ hac.2.1 (eq.symm ▸ hcd.2.2)
  exact hR _ _ _ _ nx ny hac.2.2 had.2.2 hbc.2.2 hbd.2.2

end Small
end PEqualNP.Outside.L_meta_2581

namespace PEqualNP.Outside.L_meta_2581
namespace Small
open Finset
abbrev Edge := Nat × Nat
def omitEdge (R : Nat → Nat → Prop) (e : Edge) (x y : Nat) :=
  R x y ∧ (x,y) ≠ e ∧ (y,x) ≠ e
def fits (R : Nat → Nat → Prop) (e : Edge) (t c : Word) :=
  avoids (omitEdge R e) t t ∧ avoids (omitEdge R e) t c
noncomputable def common (R : Nat → Nat → Prop) (v : Nat × Nat) : Nat := by
  classical exact if h : ∃ x, R v.1 x ∧ R v.2 x then Classical.choose h else 0
noncomputable def hull (R : Nat → Nat → Prop) (P : Finset Nat) := P ∪ (P ×ˢ P).image (common R)
noncomputable def charge (R : Nat → Nat → Prop) (P : Finset Nat) := hull R P ×ˢ hull R P

lemma mem_hull {R P x} (h : x ∈ P) : x ∈ hull R P := mem_union_left _ h
lemma common_mem {R P a b y} (hR : sparse R) (ha : a∈P) (hb : b∈P)
    (ne : a≠b) (hy : R a y) (hz : R b y) : y ∈ hull R P := by
  classical
  have existsY : ∃ z, R a z ∧ R b z := ⟨y,hy,hz⟩
  have hc : R a (common R (a,b)) ∧ R b (common R (a,b)) := by
    simpa only [common,dite_eq_left existsY] using Classical.choose_spec existsY
  have eq : common R (a,b) = y := by by_contra hn; exact hR _ _ _ _ ne hn hc.1 hy hc.2 hz
  exact mem_union_right _ (mem_image.mpr ⟨(a,b),mem_product.mpr ⟨ha,hb⟩,eq⟩)

def aligned (e : Edge) (x y : Nat) := (x,y)=e ∨ (y,x)=e
lemma align_paid {R P e x y} (hx : x∈hull R P) (hy : y∈hull R P) (a : aligned e x y) :
    e ∈ charge R P := by
  rcases a with rfl | rfl
  · exact mem_product.mpr ⟨hx,hy⟩
  · exact mem_product.mpr ⟨hy,hx⟩

noncomputable def restrictQuery (P : Finset Nat) (e : Edge) (c : Word) : Word := by
  classical exact c.filter (fun y => decide (∀ x ∈ P, ¬ aligned e x y))

lemma query_iff {R P e t c} (hR : sparse R) (sym : ∀ {x y}, R x y → R y x) (he : R e.1 e.2)
    (paid : e ∉ charge R P) (inside : ∀ x∈t, x∈P) :
    avoids (omitEdge R e) t c ↔ avoids R t (restrictQuery P e c) := by
  classical
  constructor
  · intro good x hx y hy hxy
    have hmem := List.mem_filter.mp hy
    have havoid := of_decide_eq_true hmem.2 x (inside _ hx)
    exact good _ hx _ hmem.1 ⟨hxy, fun eq => havoid (Or.inl eq), fun eq => havoid (Or.inr eq)⟩
  · intro good x hx y hy hxy
    by_cases hkeep : ∀ z ∈ P, ¬ aligned e z y
    · exact good _ hx _ (List.mem_filter.mpr ⟨hy,decide_eq_true hkeep⟩) hxy.1
    push Not at hkeep
    obtain ⟨z,hz,hit⟩ := hkeep
    have hzy : R z y := by rcases hit with rfl | rfl; exact he; exact sym he
    have xz : x ≠ z := by
      intro eq
      rcases eq ▸ hit with eq' | eq'
      · exact hxy.2.1 eq'
      · exact hxy.2.2 eq'
    exact paid (align_paid (mem_hull hz) (common_mem hR (inside _ hx) hz xz hxy.1 hzy) hit)

def volume (S : Finset Word) : Finset Nat := S.biUnion List.toFinset
lemma in_volume {S t x} (ht : t∈S) (hx : x∈t) : x∈volume S := mem_biUnion.mpr ⟨t,ht,List.mem_toFinset.mpr hx⟩

noncomputable def grade (R : Nat → Nat → Prop) (S : Finset Word) (d : Fin 7) : Finset Word := by
  classical exact S.filter fun w => w.length=d.val ∧ avoids R w w

private lemma grade_bound (R S d) : ∀ w ∈ grade R S d, w.length ≤ 6 := by
  classical
  intro w hw
  have eq := (mem_filter.mp hw).2.1
  have := d.isLt
  omega

noncomputable def chooseGrade (R) (hR : sparse R) (S : Finset Word) (d : Fin 7) :=
  Classical.choose (representatives R hR (grade R S d) (grade_bound R S d))
lemma grade_spec (R) (hR : sparse R) (S : Finset Word) (d : Fin 7) :
    chooseGrade R hR S d ⊆ grade R S d ∧ represents R (grade R S d) (chooseGrade R hR S d) ∧
      (chooseGrade R hR S d).card ≤ rankBound :=
  Classical.choose_spec (representatives R hR (grade R S d) (grade_bound R S d))

noncomputable def compress (R) (hR : sparse R) (S : Finset Word) :=
  (univ : Finset (Fin 7)).biUnion (chooseGrade R hR S)
lemma in_compress {R} {hR : sparse R} {S t} (ht : t ∈ compress R hR S) :
    t ∈ S ∧ avoids R t t ∧ t.length ≤ 6 := by
  classical
  obtain ⟨d,_,hd⟩ := mem_biUnion.mp ht
  have hh := (mem_filter.mp ((grade_spec R hR S d).1 hd))
  exact ⟨hh.1,hh.2.2,by have := d.isLt; omega⟩

def budget := 7*rankBound
lemma compact_card (R) (hR : sparse R) (S) : (compress R hR S).card ≤ budget := calc
  _ ≤ ∑ d : Fin 7, (chooseGrade R hR S d).card := card_biUnion_le
  _ ≤ ∑ _d : Fin 7, rankBound := sum_le_sum fun d _ => (grade_spec R hR S d).2.2
  _ = _ := by simp [budget]

lemma preserve {R} (hR : sparse R) (sym : ∀ {x y}, R x y → R y x) {S e} (he : R e.1 e.2)
    (paid : e ∉ charge R (volume S)) {t c : Word} (ht : t∈S) (hlen : t.length≤6)
    (clen : c.length≤6) (good : fits R e t c) :
    ∃ u ∈ compress R hR S, u.length=t.length ∧ fits R e u c := by
  classical
  have intrinsic : avoids R t t := by
    intro x hx y hy hxy
    have nothit := fun h => paid (align_paid (mem_hull (in_volume ht hx)) (mem_hull (in_volume ht hy)) h)
    exact good.1 _ hx _ hy ⟨hxy, fun h => nothit (Or.inl h), fun h => nothit (Or.inr h)⟩
  let d : Fin 7 := ⟨t.length,by omega⟩
  have hgrade : t∈grade R S d := mem_filter.mpr ⟨ht,rfl,intrinsic⟩
  let c' := restrictQuery (volume S) e c
  have hc' : c'.length≤6 := (List.length_filter_le _ _).trans clen
  have compat := (query_iff hR sym he paid (fun _ h => in_volume ht h) (c:=c)).mp good.2
  obtain ⟨u,hu,huc⟩ := (grade_spec R hR S d).2.1 _ hgrade _ hc' compat
  have desc := (mem_filter.mp ((grade_spec R hR S d).1 hu))
  exact ⟨u,mem_biUnion.mpr ⟨d,mem_univ _,hu⟩,desc.2.1,
    fun x hx y hy hd => desc.2.2 _ hx _ hy hd.1,
    (query_iff hR sym he paid (fun _ h => in_volume desc.1 h)).mpr huc⟩

end Small
end PEqualNP.Outside.L_meta_2581

namespace PEqualNP.Outside.L_meta_2581
namespace Small
open Finset PEqualNP.CircuitLowerBounds Base
def cap := budget+1
def room := 12*(2*cap+cap*cap)
def gateCost := (room+room*room)*(room+room*room)

structure Box where
  vals : Finset Word
  paid : Finset Edge
  len : ∀ w∈vals, w.length≤6
  short : vals.card ≤ cap
  cheap : paid.card ≤ gateCost

def emptyBox : Box := ⟨∅,∅,by simp,by simp,by simp⟩
def leafBox (i : Nat) : Box := ⟨{[i]},∅,by simp,by simp [cap],by simp⟩

noncomputable def pool (o : GateOp) (a b : Box) : Finset Word := by
  classical exact if o = .and then (a.vals ×ˢ b.vals).image fun z => z.1 ++ z.2 else a.vals ∪ b.vals

lemma pool_size (o : GateOp) (a b : Box) : (pool o a b).card ≤ 2*cap+cap*cap := by
  classical
  by_cases ho : o = .and
  · simp only [pool,ho,ite_true]
    have hh := card_image_le (s:=a.vals ×ˢ b.vals) (f:=fun z => z.1++z.2)
    rw [card_product] at hh
    have hmul := Nat.mul_le_mul a.short b.short
    omega
  · simp only [pool,ho,ite_false]
    have h := card_union_le a.vals b.vals
    have h1 := a.short
    have h2 := b.short
    omega

lemma pool_length (o : GateOp) (a b : Box) {w} (hw : w∈pool o a b) : w.length≤12 := by
  classical
  by_cases ho : o = .and
  · simp only [pool,ho,ite_true,mem_image,mem_product] at hw
    obtain ⟨⟨u,v⟩,⟨hu,hv⟩,rfl⟩ := hw
    change (u++v).length ≤ 12
    rw [List.length_append]
    have := a.len u hu; have := b.len v hv; omega
  · simp only [pool,ho,ite_false,mem_union] at hw
    exact hw.elim (fun h => (a.len _ h).trans (by decide)) (fun h => (b.len _ h).trans (by decide))

lemma charge_size (R o) (a b : Box) : (charge R (volume (pool o a b))).card ≤ gateCost := by
  classical
  let S := pool o a b
  have hvol : (volume S).card ≤ room := calc
    _ ≤ ∑ w ∈ S, w.toFinset.card := card_biUnion_le
    _ ≤ ∑ _w ∈ S, 12 := sum_le_sum fun w hw => (List.toFinset_card_le _).trans (pool_length o a b hw)
    _ = 12*S.card := by simp [Nat.mul_comm]
    _ ≤ room := Nat.mul_le_mul_left _ (pool_size o a b)
  have hh : (hull R (volume S)).card ≤ room+room*room := calc
    _ ≤ (volume S).card + (((volume S) ×ˢ (volume S)).image (common R)).card := card_union_le _ _
    _ ≤ (volume S).card + ((volume S) ×ˢ (volume S)).card := Nat.add_le_add_left card_image_le _
    _ ≤ room+room*room := by rw [card_product]; exact Nat.add_le_add hvol (Nat.mul_le_mul hvol hvol)
  exact (le_of_eq (card_product _ _)).trans (Nat.mul_le_mul hh hh)

noncomputable def merged (R) (hR : sparse R) (o : GateOp) (a b : Box) : Box where
  vals := compress R hR (pool o a b)
  paid := charge R (volume (pool o a b))
  len := fun _ hw => (in_compress hw).2.2
  short := (compact_card _ _ _).trans (by unfold cap; omega)
  cheap := charge_size _ _ _ _

noncomputable def step (R) (hR : sparse R) (o : GateOp) : List Box → Box
  | [a,b] => merged R hR o a b
  | _ => emptyBox

noncomputable def boxAt (R) (hR : sparse R) (n : Nat) (C : Circuit) (w : Nat) : Box :=
  (evalFrom emptyBox (step R hR) C.gates (List.ofFn fun i : Fin n => leafBox i.val)).getD w emptyBox

lemma box_input {R hR n C w} (hw : w<n) : boxAt R hR n C w = leafBox w := by
  unfold boxAt
  have hl : w<(List.ofFn fun i : Fin n => leafBox i.val).length := by simpa using hw
  rw [evalFrom_input _ _ _ _ _ hl, List.getD_eq_getElem _ _ hl,List.getElem_ofFn]
lemma box_gate {R hR n C} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    boxAt R hR n C (outWire n k) = merged R hR (row C k).op (boxAt R hR n C (operand C k 0)) (boxAt R hR n C (operand C k 1)) := by
  exact evalFrom_gate _ _ h _ List.length_ofFn k
lemma box_missing {R hR n C w} (hw : n+C.size≤w) : boxAt R hR n C w = emptyBox := by
  apply List.getD_eq_default
  simpa [evalFrom_length,Circuit.size] using hw

noncomputable def allPaid (R) (hR : sparse R) (n : Nat) (C : Circuit) :=
  (univ : Finset (Fin C.size)).biUnion fun k => (boxAt R hR n C (outWire n k)).paid

lemma total_cost (R hR n C) : (allPaid R hR n C).card ≤ C.size*gateCost := calc
  _ ≤ ∑ k : Fin C.size, (boxAt R hR n C (outWire n k)).paid.card := card_biUnion_le
  _ ≤ ∑ _k : Fin C.size, gateCost := sum_le_sum fun k _ => (boxAt R hR _ _ _).cheap
  _ = _ := by simp

lemma soundBox {R hR n C} (h : PEqualNP.TopForm.IsAO2 n C) (irr : ∀ i, ¬R i i) {w t} (ht : t∈(boxAt R hR n C w).vals) :
    t∈words n C w ∧ avoids R t t := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hw | ⟨k,rfl⟩ | hw
    · rw [box_input hw] at ht
      have eq : t=[w] := mem_singleton.mp ht
      subst t
      refine ⟨by rw [words_input C hw]; rfl,?_⟩
      intro x hx y hy
      simpa only [List.mem_singleton.mp hx,List.mem_singleton.mp hy] using irr w
    · rw [box_gate h k] at ht
      have spec := in_compress ht
      refine ⟨?_, spec.2.1⟩
      rw [words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho]
        have hm := spec.1
        simp only [pool,ho,ite_true,mem_image,mem_product] at hm
        obtain ⟨⟨u,v⟩,⟨hu,hv⟩,rfl⟩ := hm
        exact ⟨u,(ih _ (earlier h k 0) hu).1,v,(ih _ (earlier h k 1) hv).1,rfl⟩
      · rw [ho]
        have hm := spec.1
        simp only [pool,ho,reduceCtorEq,ite_false,mem_union] at hm
        exact hm.imp (fun hu => (ih _ (earlier h k 0) hu).1) (fun hv => (ih _ (earlier h k 1) hv).1)
    · rw [box_missing hw] at ht
      exact (notMem_empty _ ht).elim
end Small
end PEqualNP.Outside.L_meta_2581

namespace PEqualNP.Outside.L_meta_2581
namespace Small
open Finset Base PEqualNP.CircuitLowerBounds

lemma avoid_left (G) (u v c : Word) : avoids G (u++v) c ↔ avoids G u c ∧ avoids G v c := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (List.mem_append_left _ hx),fun x hx => h x (List.mem_append_right _ hx)⟩
  · rintro ⟨hu,hv⟩ x hx
    exact (List.mem_append.mp hx).elim (hu x) (hv x)
lemma avoid_right (G) (u v c : Word) : avoids G u (v++c) ↔ avoids G u v ∧ avoids G u c := by
  constructor
  · intro h
    exact ⟨fun x hx y hy => h x hx y (List.mem_append_left _ hy),fun x hx y hy => h x hx y (List.mem_append_right _ hy)⟩
  · rintro ⟨hv,hc⟩ x hx y hy
    exact (List.mem_append.mp hy).elim (hv x hx y) (hc x hx y)

lemma omit_flip {R e u v} (sym : ∀ {x y}, R x y → R y x)
    (h : avoids (omitEdge R e) u v) : avoids (omitEdge R e) v u := by
  intro x hx y hy hh
  exact h y hy x hx ⟨sym hh.1,hh.2.2,hh.2.1⟩

lemma fits_join {R e u v c} (sym : ∀ {x y}, R x y → R y x) :
    fits R e (u++v) c ↔ fits R e u c ∧ fits R e v c ∧ avoids (omitEdge R e) u v := by
  unfold fits
  simp only [avoid_left,avoid_right]
  constructor
  · rintro ⟨⟨⟨hu,_⟩,⟨huv,hv⟩⟩,huc,hvc⟩
    exact ⟨⟨hu,huc⟩,⟨hv,hvc⟩,huv⟩
  · rintro ⟨⟨hu,huc⟩,⟨hv,hvc⟩,huv⟩
    exact ⟨⟨⟨hu,omit_flip sym huv⟩,huv,hv⟩,huc,hvc⟩

theorem completeBox {R hR n C e} (sym : ∀ {x y}, R x y → R y x) (he : R e.1 e.2)
    (unpaid : e ∉ allPaid R hR n C) (h : PEqualNP.TopForm.IsAO2 n C)
    {w t c} (ht : t∈words n C w) (hl : t.length+c.length≤6) (hg : fits R e t c) :
    ∃ r∈(boxAt R hR n C w).vals, r.length=t.length ∧ fits R e r c := by
  induction w using Nat.strong_induction_on generalizing t c with
  | ind w ih =>
    rcases wire_cases n C.size w with hw | ⟨k,rfl⟩ | hw
    · rw [words_input C hw] at ht
      have eq : t=[w] := ht
      subst t; rw [box_input hw]; exact ⟨[w],mem_singleton_self _,rfl,hg⟩
    · let a := boxAt R hR n C (operand C k 0)
      let b := boxAt R hR n C (operand C k 1)
      have un : e ∉ charge R (volume (pool (row C k).op a b)) := by
        intro hmem
        apply unpaid
        exact mem_biUnion.mpr ⟨k,mem_univ _,by rw [box_gate h k]; exact hmem⟩
      have proceed {v} (hv : v ∈ pool (row C k).op a b) (len : v.length=t.length) (ok : fits R e v c) :
          ∃ r∈(boxAt R hR n C (outWire n k)).vals, r.length=t.length ∧ fits R e r c := by
        obtain ⟨r,hr,hlen,hgood⟩ := preserve hR sym he un hv (by omega) (by omega) ok
        exact ⟨r,by rw [box_gate h k]; exact hr,hlen.trans len,hgood⟩
      rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · rw [ho] at ht
        obtain ⟨u,hu,v,hv,rfl⟩ := ht
        have hparts := (fits_join sym).mp hg
        rw [List.length_append] at hl
        have huc : fits R e u (v++c) :=
          ⟨hparts.1.1,(avoid_right _ _ _ _).mpr ⟨hparts.2.2,hparts.1.2⟩⟩
        obtain ⟨u',hu',eu,hu'c⟩ := ih _ (earlier h k 0) hu (c:=v++c) (by rw [List.length_append]; omega) huc
        have hu'v := (avoid_right _ _ _ _).mp hu'c.2
        have hvc : fits R e v (u'++c) :=
          ⟨hparts.2.1.1,(avoid_right _ _ _ _).mpr ⟨omit_flip sym hu'v.1,hparts.2.1.2⟩⟩
        obtain ⟨v',hv',ev,hv'c⟩ := ih _ (earlier h k 1) hv (c:=u'++c) (by rw [List.length_append]; omega) hvc
        have hv'u := (avoid_right _ _ _ _).mp hv'c.2
        apply proceed (v:=u'++v')
        · simp only [pool,ho,ite_true,mem_image,mem_product]
          exact ⟨(u',v'),⟨hu',hv'⟩,rfl⟩
        · simp only [List.length_append,eu,ev]
        · exact (fits_join sym).mpr ⟨⟨hu'c.1,hu'v.2⟩,⟨hv'c.1,hv'u.2⟩,omit_flip sym hv'u.1⟩
      · rw [ho] at ht
        rcases ht with hu | hv
        · obtain ⟨u,hu,eu,huc⟩ := ih _ (earlier h k 0) hu hl hg
          apply proceed (v:=u) _ eu huc
          simpa only [pool,ho,reduceCtorEq,ite_false] using (mem_union_left b.vals hu)
        · obtain ⟨v,hv,ev,hvc⟩ := ih _ (earlier h k 1) hv hl hg
          apply proceed (v:=v) _ ev hvc
          simpa only [pool,ho,reduceCtorEq,ite_false] using (mem_union_right a.vals hv)
    · simp [words_missing n C hw] at ht

end Small
end PEqualNP.Outside.L_meta_2581

namespace PEqualNP.Outside.L_meta_2581
namespace Small
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Base

def forward {N} (I : Fin N → Fin N → Prop) (x y : Nat) :=
  ∃ p l, I p l ∧ x=p.val ∧ y=N+l.val
def graph {N} (I : Fin N → Fin N → Prop) (x y : Nat) := forward I x y ∨ forward I y x
lemma forward_side {N} {I : Fin N → Fin N → Prop} {x y} (h : forward I x y) : x<N ∧ N≤y := by
  obtain ⟨p,l,_,rfl,rfl⟩ := h
  exact ⟨p.isLt,Nat.le_add_right _ _⟩
lemma graph_sym {N} {I : Fin N → Fin N → Prop} {x y} (h : graph I x y) : graph I y x := h.symm
lemma graph_irr {N} {I : Fin N → Fin N → Prop} (x) : ¬ graph I x x := by
  intro hh
  have h : forward I x x := hh.elim id id
  have := forward_side h
  omega

lemma forward_sparse {N} (I : Fin N → Fin N → Prop)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) : sparse (forward I) := by
  rintro x z y u nx ny ⟨p,l,hpl,rfl,rfl⟩ ⟨p',l',hpl',e1,rfl⟩ ⟨z,l2,hzl,rfl,e2⟩ ⟨z',l3,hzl',e3,e4⟩
  have ep : p'=p := Fin.ext e1.symm
  have el : l2=l := Fin.ext (Nat.add_left_cancel e2.symm)
  have ez : z'=z := Fin.ext e3.symm
  have eul : l3=l' := Fin.ext (Nat.add_left_cancel e4.symm)
  subst p'; subst l2; subst z'; subst l3
  have hne : p≠z := fun h => nx (congrArg Fin.val h)
  have eq := (hU p z hne).unique ⟨hpl,hzl⟩ ⟨hpl',hzl'⟩
  exact ny (congrArg (fun a : Fin N => N+a.val) eq)

lemma graph_sparse {N} (I : Fin N → Fin N → Prop)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) : sparse (graph I) := by
  have s := forward_sparse I hU
  have left {x y} (hx : x<N) (h : graph I x y) : forward I x y :=
    h.resolve_right (fun b => Nat.not_le_of_gt hx (forward_side b).2)
  have right {x y} (hy : N≤y) (h : graph I x y) : forward I x y :=
    h.resolve_right (fun b => Nat.not_lt_of_ge hy (forward_side b).1)
  intro x z y u nx ny hxy hxu hzy hzu
  rcases hxy with h | h
  · obtain ⟨hx,hy⟩ := forward_side h
    have fzy := right hy hzy
    exact s _ _ _ _ nx ny h (left hx hxu) fzy (left (forward_side fzy).1 hzu)
  · obtain ⟨hy,hx⟩ := forward_side h
    have fux := right hx (graph_sym hxu)
    exact s _ _ _ _ ny nx h (left hy (graph_sym hzy)) fux (left (forward_side fux).1 (graph_sym hzu))

lemma letters_lt {n C} (h : PEqualNP.TopForm.IsAO2 n C) {w t} (ht : t∈words n C w) :
    ∀ x∈t, x<n := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hw | ⟨k,rfl⟩ | hw
    · have eq : t=[w] := by rwa [words_input C hw] at ht
      simpa [eq] using hw
    · rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · rw [ho] at ht
        obtain ⟨u,hu,v,hv,rfl⟩ := ht
        intro x hx
        exact (List.mem_append.mp hx).elim (ih _ (earlier h k 0) hu x) (ih _ (earlier h k 1) hv x)
      · rw [ho] at ht
        exact ht.elim (ih _ (earlier h k 0)) (ih _ (earlier h k 1))
    · simp [words_missing n C hw] at ht

lemma word_has_edge {N C} (I : Fin N → Fin N → Prop) [DecidableRel I] (h : PEqualNP.TopForm.IsAO2 (N+N) C)
    (hc : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {t} (ht : t∈words (N+N) C C.output) : ¬avoids (graph I) t t := by
  classical
  let z (i : Fin (N+N)) := decide (i.val∈t)
  have out := (value_eq_terms h z C.output).mpr ⟨t,ht,fun x hx =>
    ⟨⟨x,letters_lt h ht x hx⟩,rfl,decide_eq_true hx⟩⟩
  change circuitFun (N+N) C z = true at out
  rw [hc,decide_eq_true_eq] at out
  obtain ⟨p,l,hi,hp,hl⟩ := out
  intro no
  exact no _ (of_decide_eq_true hp) _ (of_decide_eq_true hl) (Or.inl ⟨p,l,hi,rfl,rfl⟩)

theorem plane {N C} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (h : PEqualNP.TopForm.IsAO2 (N+N) C)
    (hc : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (hr : PEqualNP.ReadK.IsReadK (N+N) C 3) : (allEdges I).card ≤ C.size*gateCost := by
  classical
  let R := graph I
  let hR : sparse R := graph_sparse I hU
  let E := allPaid R hR (N+N) C
  let enc (v : Fin N × Fin N) : Edge := (v.1.val,N+v.2.val)
  have inject : Function.Injective enc := by
    intro a b eq
    exact Prod.ext (Fin.ext (congrArg Prod.fst eq)) (Fin.ext (Nat.add_left_cancel (congrArg Prod.snd eq)))
  have mapped : Set.MapsTo enc (allEdges I) E := by
    rintro ⟨p,l⟩ hm
    have hi : I p l := (mem_filter.mp hm).2
    let e := enc (p,l)
    by_contra unpaid
    obtain ⟨a,b,_,ha,_,hb,t,ht,ea,eb,hs⟩ := plane_read_cover I h hc hr hi
    have lens : t.length≤6 := by have hh := sum_counts N t; omega
    have members (x : Nat) (hx : x∈t) : x=p.val ∨ x=N+l.val := by
      rcases hs x hx with ⟨q,hq,rfl⟩ | ⟨m,hm,rfl⟩
      · obtain rfl : q=p := hq
        exact Or.inl rfl
      · obtain rfl : m=l := hm
        exact Or.inr rfl
    have good : fits R e t [] := by
      refine ⟨?_,fun _ _ _ hy => False.elim (List.not_mem_nil hy)⟩
      intro x hx y hy has
      rcases members _ hx with rfl | rfl <;> rcases members _ hy with rfl | rfl
      · exact graph_irr _ has.1
      · exact has.2.1 rfl
      · exact has.2.2 rfl
      · exact graph_irr _ has.1
    have actual : R e.1 e.2 := Or.inl ⟨p,l,hi,rfl,rfl⟩
    obtain ⟨r,mem,_,_⟩ := completeBox (hR:=hR) (fun q => graph_sym q) actual unpaid h ht (c:=[]) (by simpa using lens) good
    have ds := soundBox h (fun x => graph_irr x) mem
    exact word_has_edge I h hc ds.1 ds.2
  exact (card_le_card_of_injOn enc mapped inject.injOn).trans (total_cost R hR (N+N) C)

end Small
end PEqualNP.Outside.L_meta_2581

open PEqualNP.Outside.L_meta_2581

theorem PEqualNP.Outside.L_meta_2581 : ∃ c : ℕ, ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 3 → N * q ≤ c * C.size := by
  refine ⟨Small.gateCost,?_⟩
  intro q N I inst C _hq _hN hL hU h hc hr
  have hbound := Small.plane I hU h hc hr
  rw [Base.allEdges_card I q hL] at hbound
  calc
    N*q ≤ N*(q+1) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ C.size*Small.gateCost := hbound
    _ = Small.gateCost*C.size := Nat.mul_comm _ _
