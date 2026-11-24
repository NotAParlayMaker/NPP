import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4990



private theorem dagLeafBound {α : Type*} [DecidableEq α]
    (support : ℕ → Finset α) (internal roots : Finset ℕ)
    (split : ∀ w ∈ internal, ∃ u v : ℕ, u < w ∧ v < w ∧
      support w ⊆ support u ∪ support v ∧
      (1 < (support u).card → u ∈ internal) ∧
      (1 < (support v).card → v ∈ internal))
    (rootMem : ∀ w ∈ roots, 1 < (support w).card → w ∈ internal) :
    (roots.biUnion support).card ≤ internal.card + roots.card := by
  classical
  induction internal using Finset.induction_on_max generalizing roots with
  | empty =>
    have h := Finset.card_biUnion_le_card_mul roots support 1 (by
      intro w hw
      by_contra! h
      simpa using rootMem w hw h)
    simpa using h
  | insert w rest hmax ih =>
    have fresh : w ∉ rest := fun h => (Nat.lt_irrefl w) (hmax w h)
    rw [Finset.card_insert_of_notMem fresh]
    have drop {x : ℕ} (hlt : x < w) (hx : x ∈ insert w rest) : x ∈ rest :=
      (Finset.mem_insert.mp hx).resolve_left (Nat.ne_of_lt hlt)
    have smaller : ∀ x ∈ rest, ∃ u v : ℕ, u < x ∧ v < x ∧
        support x ⊆ support u ∪ support v ∧
        (1 < (support u).card → u ∈ rest) ∧
        (1 < (support v).card → v ∈ rest) := by
      intro x hx
      obtain ⟨u,v,hu,hv,hs,hU,hV⟩ := split x (Finset.mem_insert_of_mem hx)
      exact ⟨u,v,hu,hv,hs,fun h => drop (lt_trans hu (hmax x hx)) (hU h),
        fun h => drop (lt_trans hv (hmax x hx)) (hV h)⟩
    by_cases hw : w ∈ roots
    · obtain ⟨u,v,hu,hv,hs,hU,hV⟩ := split w (Finset.mem_insert_self ..)
      let frontier := insert u (insert v (roots.erase w))
      have hfront : ∀ x ∈ frontier, 1 < (support x).card → x ∈ rest := by
        intro x hx h
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact drop hu (hU h)
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact drop hv (hV h)
        exact (Finset.mem_insert.mp (rootMem x (Finset.mem_of_mem_erase hx) h)).resolve_left
          (Finset.ne_of_mem_erase hx)
      have sub : roots.biUnion support ⊆ frontier.biUnion support := by
        intro a ha
        obtain ⟨x,hx,hax⟩ := Finset.mem_biUnion.mp ha
        by_cases eq : x = w
        · subst x
          rcases Finset.mem_union.mp (hs hax) with h | h
          · exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_insert_self .., h⟩
          · exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_self ..), h⟩
        · exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨eq,hx⟩)), hax⟩
      have bound := (Finset.card_le_card sub).trans (ih frontier smaller hfront)
      have one := Finset.card_insert_le u (insert v (roots.erase w))
      have two := Finset.card_insert_le v (roots.erase w)
      have erased := Finset.card_erase_add_one hw
      dsimp [frontier] at bound
      omega
    · have bound := ih roots smaller (fun x hx h =>
        (Finset.mem_insert.mp (rootMem x hx h)).resolve_left (fun e => hw (e ▸ hx)))
      omega



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

private lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

private lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

private lemma emptyIncidenceCover {N M : ℕ} (I : Fin N → Fin M → Prop)
    (C : Circuit) (he : ¬ ∃ p l, I p l) :
    ∃ S : Finset (Fin (N + M)), (∀ p l, I p l → Fin.castAdd M p ∈ S ∨ Fin.natAdd N l ∈ S) ∧
      (PEqualNP.ReadTwo.incid I).card + S.card ≤ C.size + 1 := by
  classical
  have h : PEqualNP.ReadTwo.incid I = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e h
    exact he ⟨e.1, e.2, (Finset.mem_filter.mp h).2⟩
  exact ⟨∅, fun p l hp => (he ⟨p,l,hp⟩).elim, by simp [h]⟩

private lemma incidenceOutputGate {N M : ℕ} (I : Fin N → Fin M → Prop) [DecidableRel I]
    (C : Circuit) (he : ∃ p l, I p l)
    (hc : ∀ x : Fin (N + M) → Bool, circuitFun (N + M) C x =
      decide (∃ p l, I p l ∧ x (Fin.castAdd M p) = true ∧ x (Fin.natAdd N l) = true)) :
    ∃ j < C.gates.length, C.output = N + M + j := by
  have upper : C.output < N + M + C.gates.length := by
    by_contra! h
    let x : Fin (N + M) → Bool := fun _ => true
    have hf := getD_ge_length (C.wires (List.ofFn x)) C.output (by rwa [wires_length])
    change circuitFun _ C x = false at hf
    obtain ⟨p,l,hpl⟩ := he
    have ht := (hc x).trans (decide_eq_true ⟨p,l,hpl,rfl,rfl⟩)
    simp [hf] at ht
  have lower : N + M ≤ C.output := by
    by_contra! h
    let x : Fin (N + M) → Bool := fun i => decide (i.val = C.output)
    have ht : circuitFun _ C x = true := by
      change (C.wires (List.ofFn x)).getD C.output false = true
      rw [wires_eq_foldl, foldl_stepWire_getD_lt _ _ _ (by simpa using h)]
      simp [List.getD_eq_getElem?_getD, h, x]
    obtain ⟨p,l,_,hp,hl⟩ := of_decide_eq_true ((hc x).symm.trans ht)
    have hp' : p.val = C.output := of_decide_eq_true hp
    have hl' : N + l.val = C.output := of_decide_eq_true hl
    omega
  exact ⟨C.output - (N + M), by omega, by omega⟩



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
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

private def PureSide (n : ℕ) (C : Circuit) (S : Finset ℕ) (P : ℕ → Prop) :=
  ∀ w ∈ S, (w < n ∧ P w) ∨ ∃ k < C.gates.length, w = n + k ∧
    (gateAt C k).op = GateOp.or ∧ ∀ v ∈ (gateAt C k).inputs, v ∈ S

private lemma pureWord {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {S : Finset ℕ} {P : ℕ → Prop} (hp : PureSide n C S P)
    {w : ℕ} (hw : w ∈ S) {t : List ℕ} (ht : t ∈ words n C w) :
    ∃ v, t = [v] ∧ P v := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hp w hw with ⟨hi,hP⟩ | ⟨j,hj,rfl,ho,hs⟩
    · rw [words_input C hi] at ht
      exact ⟨w, ht, hP⟩
    · let k : Fin C.size := ⟨j,hj⟩
      change t ∈ words n C (outWire n k) at ht
      have he := row_eq C k
      change gateAt C j = row C k at he
      rw [he] at ho hs
      rw [words_gate h k, ho] at ht
      rw [inputs_two h k] at hs
      rcases ht with ht | ht
      · exact ih _ (earlier h k 0) (hs _ (by simp)) ht
      · exact ih _ (earlier h k 1) (hs _ (by simp)) ht

private lemma outputWordShape {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {P Q : ℕ → Prop} {A B : Finset ℕ}
    (ha : PureSide n C A P) (hb : PureSide n C B Q)
    (hg : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∃ a b, (gateAt C j).inputs = [a,b] ∧ a ∈ A ∧ b ∈ B)
    {w : ℕ} {t : List ℕ} (ht : t ∈ words n C w) :
    (∃ i, t = [i]) ∨ ∃ a b, t = [a,b] ∧ P a ∧ Q b := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases wire_cases n C.size w with hi | ⟨k,rfl⟩ | hm
    · rw [words_input C hi] at ht
      exact Or.inl ⟨w, ht⟩
    · rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · obtain ⟨a,b,hab,ha',hb'⟩ := hg k k.isLt (by rwa [row_eq])
        rw [row_eq, inputs_two h k] at hab
        obtain ⟨rfl,rfl⟩ := List.cons.inj hab |>.imp_right (fun e => (List.cons.inj e).1)
        rw [ho] at ht
        obtain ⟨u,hu,v,hv,rfl⟩ := ht
        obtain ⟨x,rfl,hx⟩ := pureWord h ha ha' hu
        obtain ⟨y,rfl,hy⟩ := pureWord h hb hb' hv
        exact Or.inr ⟨x,y,rfl,hx,hy⟩
      · rw [ho] at ht
        exact ht.elim (ih _ (earlier h k 0)) (ih _ (earlier h k 1))
    · simp [words_missing n C hm] at ht

private lemma incidenceFrontier {m l : ℕ} {R : Fin m → Fin l → Prop} [DecidableRel R]
    {C : Circuit} (h : IsAO2 (m+l) C)
    (hf : ∀ z, circuitFun (m+l) C z = decide (∃ p q, R p q ∧
      z (Fin.castAdd l p) = true ∧ z (Fin.natAdd m q) = true))
    {A B : Finset ℕ}
    (ha : PureSide (m+l) C A (fun v => m ≤ v ∧ v < m+l))
    (hb : PureSide (m+l) C B (fun v => v < m))
    (hg : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∃ a b, (gateAt C j).inputs = [a,b] ∧ a ∈ A ∧ b ∈ B)
    (p : Fin m) (q : Fin l) :
    R p q ↔ ∃ j < C.gates.length, OrReaches (m+l) C C.output j ∧
      (gateAt C j).op = GateOp.and ∧
      Fin.natAdd m q ∈ orIn (m+l) C (opnd C j 0) ∧
      Fin.castAdd l p ∈ orIn (m+l) C (opnd C j 1) := by
  simp only [← single_orIn h, ← pair_iff h]
  let z : Fin (m+l) → Bool := fun i => decide (i = Fin.castAdd l p ∨ i = Fin.natAdd m q)
  have sep (a : Fin m) (b : Fin l) : Fin.castAdd l a ≠ Fin.natAdd m b := by
    intro e
    have := congrArg Fin.val e
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  have zP (a : Fin m) : z (Fin.castAdd l a) = true ↔ a = p := by
    simp [z, sep]
  have zQ (b : Fin l) : z (Fin.natAdd m b) = true ↔ b = q := by
    simp [z, Ne.symm (sep p b)]
  have hz : circuitValue C z C.output = true ↔ R p q := by
    change circuitFun (m+l) C z = true ↔ _
    simp [hf, zP, zQ]
  constructor
  · intro he
    obtain ⟨t,ht,hw⟩ := (value_eq_terms h z _).mp (hz.mpr he)
    rcases outputWordShape h ha hb hg ht with ⟨i,rfl⟩ | ⟨a,b,rfl,ha',hb'⟩
    · obtain ⟨k,hk,_⟩ := hw i (by simp)
      let s : Fin (m+l) → Bool := fun v => decide (v = k)
      have hs : circuitFun (m+l) C s = true :=
        (value_eq_terms h s _).mpr ⟨[i],ht,by
          intro v hv
          obtain rfl := List.mem_singleton.mp hv
          exact ⟨k,hk,by simp [s]⟩⟩
      rw [hf, decide_eq_true_eq] at hs
      obtain ⟨u,v,_,hu,hv⟩ := hs
      simp only [s,decide_eq_true_eq] at hu hv
      exact False.elim (sep u v (hu.trans hv.symm))
    · obtain ⟨i,hi,zi⟩ := hw a (by simp)
      obtain ⟨j,hj,zj⟩ := hw b (by simp)
      simp only [z,decide_eq_true_eq] at zi zj
      rcases zi with rfl | rfl <;> rcases zj with rfl | rfl <;>
        simp only [Fin.val_natAdd, Fin.val_castAdd] at * <;> first | omega | simpa [hi,hj] using ht
  · intro ht
    apply hz.mp
    apply (value_eq_terms h z _).mpr
    refine ⟨_,ht,?_⟩
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨_,rfl,(zQ q).mpr rfl⟩
    · exact ⟨_,rfl,(zP p).mpr rfl⟩




open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

private noncomputable def topGates (n : ℕ) (C : Circuit) (w : ℕ) (op : GateOp) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter fun j => OrReaches n C w j ∧ (gateAt C j).op = op

private lemma memTop {n w j : ℕ} {C : Circuit} {op : GateOp} :
    j ∈ topGates n C w op ↔ j < C.size ∧ OrReaches n C w j ∧ (gateAt C j).op = op := by
  classical
  simp [topGates]

private lemma topTrans {n : ℕ} {C : Circuit} (h : IsAO2 n C) (w : ℕ) (k : Fin C.size)
    (j : ℕ) (hr : OrReaches n C w k.val) (hj : OrReaches n C (outWire n k) j) :
    OrReaches n C w j := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases wire_cases n C.size w with hi | ⟨a,rfl⟩ | hm
    · exact False.elim (orR_input C hi hr)
    · rcases (orR_gate h a _).mp hr with he | ⟨ho,hl | hl⟩
      · exact (Fin.ext he : k = a) ▸ hj
      · exact (orR_gate h a _).mpr (Or.inr ⟨ho,Or.inl (ih _ (earlier h a 0) hl)⟩)
      · exact (orR_gate h a _).mpr (Or.inr ⟨ho,Or.inr (ih _ (earlier h a 1) hl)⟩)
    · exact False.elim (orR_missing C hm hr)

private lemma topCount {n : ℕ} {C : Circuit} (h : IsAO2 n C) (root : ℕ) :
    (topGates n C root .and).card ≤ (topGates n C root .or).card + 1 := by
  classical
  let support := fun w => topGates n C w .and
  let internal := (topGates n C root .or).image (fun j => n+j)
  have large (w : ℕ) (reach : ∀ j, OrReaches n C w j → OrReaches n C root j)
      (hc : 1 < (support w).card) : w ∈ internal := by
    rcases wire_cases n C.size w with hi | ⟨k,rfl⟩ | hm
    · have he : support w = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
        (fun j hj => orR_input C hi (memTop.mp hj).2.1)
      simp [he] at hc
    · rcases op_kind h k with ho | ho
      · have sub : support (outWire n k) ⊆ {k.val} := by
          intro j hj
          rcases (orR_gate h k _).mp (memTop.mp hj).2.1 with he | ⟨bad,_⟩
          · simpa using he
          · rw [ho] at bad; contradiction
        have := Finset.card_le_card sub
        simp at this
        omega
      · exact Finset.mem_image.mpr ⟨k.val,memTop.mpr ⟨k.isLt,
          reach _ ((orR_gate h k _).mpr (Or.inl rfl)), by rwa [row_eq]⟩,rfl⟩
    · have he : support w = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
        (fun j hj => orR_missing C hm (memTop.mp hj).2.1)
      simp [he] at hc
  have bound := dagLeafBound support internal {root} (by
    intro w hw
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨ha,hr,ho⟩ := memTop.mp ha
    let k : Fin C.size := ⟨a,ha⟩
    have hop : (row C k).op = GateOp.or := by rwa [← row_eq]
    have child (b : Fin 2) (j : ℕ) (hj : OrReaches n C (operand C k b) j) :
        OrReaches n C root j := by
      apply topTrans h root k j hr
      apply (orR_gate h k j).mpr
      right
      refine ⟨hop,?_⟩
      fin_cases b <;> tauto
    refine ⟨_,_,earlier h k 0,earlier h k 1,?_,large _ (child 0),large _ (child 1)⟩
    intro j hj
    obtain ⟨hlt,hrj,hjop⟩ := memTop.mp hj
    rcases (orR_gate h k j).mp hrj with he | ⟨_,hl | hl⟩
    · change j = a at he
      subst j
      rw [ho] at hjop
      contradiction
    · exact Finset.mem_union_left _ (memTop.mpr ⟨hlt,hl,hjop⟩)
    · exact Finset.mem_union_right _ (memTop.mpr ⟨hlt,hl,hjop⟩)) (by
      intro w hw
      obtain rfl := Finset.mem_singleton.mp hw
      exact large _ (fun _ hj => hj))
  have small : internal.card ≤ (topGates n C root .or).card := Finset.card_image_le
  exact (by simpa [support] using bound : (topGates n C root .and).card ≤ internal.card + 1).trans
    (Nat.add_le_add_right small 1)



private lemma pureBigSplit {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {S : Finset ℕ} {P : ℕ → Prop} (hp : PureSide n C S P)
    {w : ℕ} (hw : w ∈ S) (hm : 1 < (orIn n C w).card) :
    ∃ k : Fin C.size, w = outWire n k ∧ (row C k).op = GateOp.or ∧
      operand C k 0 ∈ S ∧ operand C k 1 ∈ S ∧
      orIn n C w = orIn n C (operand C k 0) ∪ orIn n C (operand C k 1) := by
  classical
  rcases hp w hw with ⟨hi,_⟩ | ⟨j,hj,rfl,ho,hs⟩
  · have sub : orIn n C w ⊆ {⟨w,hi⟩} := by
      intro i hi'
      rw [← single_orIn h, words_input C hi] at hi'
      exact Finset.mem_singleton.mpr (Fin.ext (List.cons.inj hi').1)
    have := Finset.card_le_card sub
    simp at this
    omega
  · let k : Fin C.size := ⟨j,hj⟩
    change (gateAt C k.val).op = _ at ho
    change ∀ v ∈ (gateAt C k.val).inputs, v ∈ S at hs
    rw [row_eq] at ho hs
    rw [inputs_two h k] at hs
    refine ⟨k,rfl,ho,hs _ (by simp),hs _ (by simp),?_⟩
    ext i
    change i ∈ orIn n C (outWire n k) ↔ _
    rw [Finset.mem_union, ← single_orIn h, ← single_orIn h, ← single_orIn h, words_gate h k, ho]
    rfl

private def centerCharges (n : ℕ) (C : Circuit) (S : Finset ℕ) (allowed : Finset (Fin n)) :
    Finset ℕ := (Finset.range C.size).filter fun j =>
      n+j ∈ S ∧ 1 < (orIn n C (n+j)).card ∧ orIn n C (n+j) ⊆ allowed

private theorem centerLeafBound {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    {S roots : Finset ℕ} {P : ℕ → Prop} (hp : PureSide n C S P)
    (allowed : Finset (Fin n)) (hr : roots ⊆ S) (ha : ∀ w ∈ roots, orIn n C w ⊆ allowed) :
    (roots.biUnion (orIn n C)).card ≤ (centerCharges n C S allowed).card + roots.card := by
  classical
  let G := centerCharges n C S allowed
  let W := G.image (n + ·)
  have memW {w} (hw : w ∈ S) (hm : 1 < (orIn n C w).card) (hs : orIn n C w ⊆ allowed) : w ∈ W := by
    obtain ⟨k,rfl,_⟩ := pureBigSplit h hp hw hm
    exact Finset.mem_image.mpr ⟨k.val,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr k.isLt,hw,hm,hs⟩,rfl⟩
  have bound := dagLeafBound (orIn n C) W roots (by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨_,hS,hm,ha'⟩ := Finset.mem_filter.mp hj
    obtain ⟨k,eqn,_,hu,hv,he⟩ := pureBigSplit h hp hS hm
    rw [he] at ha'
    exact ⟨_,_,eqn ▸ earlier h k 0,eqn ▸ earlier h k 1,he.le,
      fun hm => memW hu hm (Finset.union_subset_left ha'),
      fun hm => memW hv hm (Finset.union_subset_right ha')⟩)
    (fun w hw hm => memW (hr hw) hm (ha w hw))
  exact bound.trans (Nat.add_le_add_right Finset.card_image_le _)

private lemma centerChargesDisjoint {n : ℕ} {C : Circuit} {S S' : Finset ℕ}
    {A B : Finset (Fin n)} (h : (A ∩ B).card ≤ 1) :
    Disjoint (centerCharges n C S A) (centerCharges n C S' B) := by
  apply Finset.disjoint_left.mpr
  intro j ha hb
  obtain ⟨_,_,hm,hA⟩ := Finset.mem_filter.mp ha
  obtain ⟨_,_,_,hB⟩ := Finset.mem_filter.mp hb
  have := Finset.card_le_card (Finset.subset_inter hA hB)
  omega

private lemma reachedWords {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    (w : ℕ) (k : Fin C.size) (hr : OrReaches n C w k.val) :
    words n C (outWire n k) ⊆ words n C w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases wire_cases n C.size w with hi | ⟨a,rfl⟩ | hm
    · exact (orR_input C hi hr).elim
    · rcases (orR_gate h a _).mp hr with eqn | ⟨ho,hl | hl⟩
      · exact (Fin.ext eqn : k = a) ▸ Set.Subset.rfl
      · rw [words_gate h a, ho]
        exact fun _ ht => Or.inl (ih _ (earlier h a 0) hl ht)
      · rw [words_gate h a, ho]
        exact fun _ ht => Or.inr (ih _ (earlier h a 1) hl ht)
    · exact (orR_missing C hm hr).elim

private lemma centerChargeNotTop {m l : ℕ} {R : Fin m → Fin l → Prop} [DecidableRel R]
    {C : Circuit} (h : IsAO2 (m+l) C)
    (hf : ∀ z, circuitFun (m+l) C z = decide (∃ p q, R p q ∧
      z (Fin.castAdd l p) = true ∧ z (Fin.natAdd m q) = true))
    {S : Finset ℕ} {A : Finset (Fin (m+l))} {j : ℕ}
    (hj : j ∈ centerCharges (m+l) C S A) : ¬ OrReaches (m+l) C C.output j := by
  intro hr
  obtain ⟨hj,_,hm,_⟩ := Finset.mem_filter.mp hj
  let k : Fin C.size := ⟨j,Finset.mem_range.mp hj⟩
  obtain ⟨i,hi,_,_,_⟩ := Finset.one_lt_card.mp hm
  have ht := reachedWords h C.output k hr ((single_orIn h i _).mpr hi)
  let z : Fin (m+l) → Bool := fun v => decide (v = i)
  have hz : circuitFun (m+l) C z = true := (value_eq_terms h z _).mpr ⟨_,ht,by
    intro v hv
    obtain rfl := List.mem_singleton.mp hv
    exact ⟨i,rfl,by simp [z]⟩⟩
  rw [hf, decide_eq_true_eq] at hz
  obtain ⟨p,q,_,hp,hq⟩ := hz
  simp only [z,decide_eq_true_eq] at hp hq
  have eqn := congrArg Fin.val (hp.trans hq.symm)
  simp only [Fin.val_castAdd, Fin.val_natAdd] at eqn
  omega


private theorem fiberBound {n : ℕ} {C : Circuit} (ao : IsAO2 n C)
    {S : Finset ℕ} {pred : ℕ → Prop} (pure : PureSide n C S pred)
    {E : Type} [DecidableEq E] (edges : Finset E) (family : Finset ℕ)
    (wire : ℕ → ℕ) (allowed : Finset (Fin n)) (leaf : E → Fin n)
    (inject : (edges : Set E).InjOn leaf)
    (witness : ∀ e ∈ edges, ∃ k ∈ family, leaf e ∈ orIn n C (wire k) ∧
      wire k ∈ S ∧ orIn n C (wire k) ⊆ allowed) :
    edges.card ≤ (centerCharges n C S allowed).card + family.card := by
  classical
  let good := family.filter fun k => wire k ∈ S ∧ orIn n C (wire k) ⊆ allowed
  let roots := good.image wire
  have bound := centerLeafBound ao pure allowed (roots := roots) (by
    intro w hw
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp hk).2.1) (by
    intro w hw
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp hk).2.2)
  have transfer : edges.card ≤ (roots.biUnion (orIn n C)).card :=
    Finset.card_le_card_of_injOn leaf (by
      intro e he
      obtain ⟨k,hk,hl,hs,ha⟩ := witness e he
      exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_image_of_mem wire
        (show k ∈ good from Finset.mem_filter.mpr ⟨hk,hs,ha⟩),hl⟩) inject
  have small : roots.card ≤ family.card := Finset.card_image_le.trans (Finset.card_filter_le ..)
  omega

private theorem supportSide {n : ℕ} {C : Circuit} (ao : IsAO2 n C)
    {S : Finset ℕ} {pred : ℕ → Prop} (pure : PureSide n C S pred)
    {w : ℕ} (hw : w ∈ S) {v : Fin n} (hv : v ∈ orIn n C w) : pred v.val := by
  obtain ⟨u,he,hu⟩ := pureWord ao pure hw ((single_orIn ao v w).2 hv)
  exact (List.cons.inj he).1 ▸ hu

private def centerAdjacent {n m : ℕ} (I : Fin n → Fin m → Prop) :
    Fin (n+m) → Fin (n+m) → Prop :=
  Fin.addCases (fun p => Fin.addCases (fun _ => False) (fun l => I p l))
    (fun l => Fin.addCases (fun p => I p l) (fun _ => False))

private noncomputable def centerNeighborhood {n m : ℕ} (I : Fin n → Fin m → Prop)
    (c : Fin (n+m)) : Finset (Fin (n+m)) := by
  classical
  exact Finset.univ.filter (centerAdjacent I c)

private theorem centerNeighborhood_inter {n m : ℕ} {I : Fin n → Fin m → Prop}
    (free : ∀ p q l k, p ≠ q → l ≠ k → ¬ (I p l ∧ I p k ∧ I q l ∧ I q k))
    {c d : Fin (n+m)} (hne : c ≠ d) :
    (centerNeighborhood I c ∩ centerNeighborhood I d).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  simp only [Finset.mem_inter, centerNeighborhood, Finset.mem_filter, Finset.mem_univ,
    true_and] at hx hy
  obtain ⟨hcx, hdx⟩ := hx
  obtain ⟨hcy, hdy⟩ := hy
  cases c using Fin.addCases <;> cases d using Fin.addCases <;>
    cases x using Fin.addCases <;> cases y using Fin.addCases <;>
    simp [centerAdjacent] at * <;> solve_by_elim (maxDepth := 8) [And.intro]


theorem rectangleThin {α β : Type} {I : α → β → Prop}
    (free : ∀ a b x y, a ≠ b → x ≠ y → ¬ (I a x ∧ I a y ∧ I b x ∧ I b y))
    (P : Finset α) (L : Finset β) (edges : ∀ p ∈ P, ∀ l ∈ L, I p l) :
    P.card ≤ 1 ∨ L.card ≤ 1 := by
  classical
  by_contra! h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h.1
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h.2
  exact free a b x y hab hxy ⟨edges a ha x hx, edges a ha y hy, edges b hb x hx, edges b hb y hy⟩

private theorem chooseCenters {n m : ℕ} {I : Fin n → Fin m → Prop}
    (free : ∀ a b x y, a ≠ b → x ≠ y → ¬ (I a x ∧ I a y ∧ I b x ∧ I b y))
    (nonempty : ∃ p l, I p l) (K : Finset ℕ)
    (P : ℕ → Finset (Fin n)) (L : ℕ → Finset (Fin m))
    (rect : ∀ p l, I p l ↔ ∃ k ∈ K, p ∈ P k ∧ l ∈ L k) :
    ∃ center : ℕ → Fin (n+m),
      (∀ k ∈ K, ∀ p ∈ P k, ∀ l ∈ L k,
        center k = Fin.castAdd m p ∨ center k = Fin.natAdd n l) ∧
      (∀ p l, I p l → Fin.castAdd m p ∈ K.image center ∨ Fin.natAdd n l ∈ K.image center) := by
  classical
  obtain ⟨p₀,l₀,_⟩ := nonempty
  have one (k : ℕ) : ∃ c : Fin (n+m), ∀ _ : k ∈ K, ∀ p ∈ P k, ∀ l ∈ L k,
      c = Fin.castAdd m p ∨ c = Fin.natAdd n l := by
    by_cases hk : k ∈ K
    · have thin := rectangleThin free (P k) (L k) (fun p hp l hl => (rect p l).2 ⟨k,hk,hp,hl⟩)
      rcases thin with h | h
      · by_cases hp : (P k).Nonempty
        · obtain ⟨a,ha⟩ := hp
          exact ⟨Fin.castAdd m a,fun _ p hmem _ _ => Or.inl (congrArg _ (Finset.card_le_one.mp h _ ha _ hmem))⟩
        · exact ⟨Fin.castAdd m p₀,fun _ p hmem => (hp ⟨p,hmem⟩).elim⟩
      · by_cases hl : (L k).Nonempty
        · obtain ⟨b,hb⟩ := hl
          exact ⟨Fin.natAdd n b,fun _ _ _ l hmem => Or.inr (congrArg _ (Finset.card_le_one.mp h _ hb _ hmem))⟩
        · exact ⟨Fin.natAdd n l₀,fun _ _ _ l hmem => (hl ⟨l,hmem⟩).elim⟩
    · exact ⟨Fin.castAdd m p₀,fun h => (hk h).elim⟩
  choose c hc using one
  refine ⟨c,hc,?_⟩
  intro p l he
  obtain ⟨k,hk,hp,hl⟩ := (rect p l).1 he
  have mem := Finset.mem_image_of_mem c hk
  rcases hc k hk p hp l hl with e | e
  · exact Or.inl (e ▸ mem)
  · exact Or.inr (e ▸ mem)

theorem uniqueCenter {α β : Type} {I : α → β → Prop}
    (free : ∀ a b x y, a ≠ b → x ≠ y → ¬ (I a x ∧ I a y ∧ I b x ∧ I b y))
    {S : Finset β} (many : 1 < S.card) {a b : α}
    (ha : ∀ x ∈ S, I a x) (hb : ∀ x ∈ S, I b x) : a = b := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp many
  by_contra hab
  exact free a b x y hab hxy ⟨ha x hx, ha y hy, hb x hx, hb y hy⟩

private theorem countNeighborLeaves {α : Type} [DecidableEq α]
    (support : ℕ → Finset α) (pure roots : Finset ℕ) (allowed : Finset α)
    (split : ∀ w ∈ pure, 1 < (support w).card → ∃ u v, u < w ∧ v < w ∧
      u ∈ pure ∧ v ∈ pure ∧ support w = support u ∪ support v)
    (rootPure : roots ⊆ pure) (neighbors : ∀ w ∈ roots, support w ⊆ allowed) :
    (roots.biUnion support).card ≤
      (pure.filter fun w => 1 < (support w).card ∧ support w ⊆ allowed).card + roots.card := by
  classical
  apply dagLeafBound
  · intro w hw
    obtain ⟨hw, hmany, hsub⟩ := Finset.mem_filter.mp hw
    obtain ⟨u,v,hu,hv,pu,pv,eqn⟩ := split w hw hmany
    rw [eqn] at hsub
    exact ⟨u,v,hu,hv,eqn.le,fun hm => Finset.mem_filter.mpr
      ⟨pu,hm,Finset.union_subset_left hsub⟩, fun hm => Finset.mem_filter.mpr
      ⟨pv,hm,Finset.union_subset_right hsub⟩⟩
  · intro w hw hm
    exact Finset.mem_filter.mpr ⟨rootPure hw, hm, neighbors w hw⟩

theorem countPartition {α β : Type} [DecidableEq β]
    (E : Finset β) (centers : Finset α) (K T : Finset ℕ)
    (G : α → Finset ℕ) (edges : α → Finset β) (roots : α → ℕ)
    (size : ℕ) (covers : E ⊆ centers.biUnion edges)
    (counts : ∀ c ∈ centers, (edges c).card ≤ (G c).card + roots c)
    (rootCount : ∑ c ∈ centers, roots c ≤ K.card)
    (centerCount : centers.card ≤ K.card) (frontier : K.card ≤ T.card + 1)
    (separate : (centers : Set α).PairwiseDisjoint G)
    (kt : Disjoint K T) (other : Disjoint (centers.biUnion G) (K ∪ T))
    (valid : centers.biUnion G ∪ (K ∪ T) ⊆ Finset.range size) :
    E.card + centers.card ≤ size + 1 := by
  classical
  have he := (Finset.card_le_card covers).trans Finset.card_biUnion_le
  have hs := Finset.sum_le_sum counts
  rw [Finset.sum_add_distrib] at hs
  have hg := Finset.card_le_card valid
  rw [Finset.card_union_of_disjoint other, Finset.card_union_of_disjoint kt,
    Finset.card_biUnion separate, Finset.card_range] at hg
  omega

end PEqualNP.Outside.L_meta_4990

open PEqualNP.Outside.L_meta_4990 PEqualNP.TopForm PEqualNP.CircuitLowerBounds
theorem PEqualNP.Outside.L_meta_4990 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : Finset ℕ), (∀ (x8 x9 : Fin x1) (x10 x11 : Fin x2), x8 ≠ x9 → x10 ≠ x11 → ¬(x3 x8 x10 ∧ x3 x8 x11 ∧ x3 x9 x10 ∧ x3 x9 x11)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x10 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → (∀ x11 ∈ x6, x11 < x1 ∨ ∃ x13 < x5.gates.length, x11 = x1 + x2 + x13 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).inputs, x14 ∈ x6) → (∀ x12 ∈ x7, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x5.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x14).inputs, x15 ∈ x7) → (∀ x13 < x5.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x16 : ℕ) (x17 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).inputs = [x16, x17] ∧ x16 ∈ x7 ∧ x17 ∈ x6) → ∃ (x14 : Finset (Fin (x1 + x2))), (∀ (x15 : Fin x1) (x16 : Fin x2), x3 x15 x16 → Fin.castAdd x2 x15 ∈ x14 ∨ Fin.natAdd x1 x16 ∈ x14) ∧ (PEqualNP.ReadTwo.incid x3).card + x14.card ≤ x5.size + (1 : ℕ) := by
  classical
  intro n m I inst C P L free ao computes hp hl hand
  by_cases he : ∃ p l, I p l
  · obtain ⟨j, hj, hout⟩ := PEqualNP.Outside.L_meta_4990.incidenceOutputGate I C he computes
    have pureL : PEqualNP.Outside.L_meta_4990.PureSide (n+m) C L (fun v => n ≤ v ∧ v < n+m) := by
      intro w hw
      rcases hl w hw with h | h
      · exact Or.inl ⟨h.2,h⟩
      · exact Or.inr h
    have pureP : PEqualNP.Outside.L_meta_4990.PureSide (n+m) C P (fun v => v < n) := by
      intro w hw
      rcases hp w hw with h | h
      · exact Or.inl ⟨by omega,h⟩
      · exact Or.inr h
    have rect := PEqualNP.Outside.L_meta_4990.incidenceFrontier ao computes pureL pureP hand
    let K := topGates (n+m) C C.output .and
    let T := topGates (n+m) C C.output .or
    let ps (k : ℕ) := Finset.univ.filter fun p : Fin n => Fin.castAdd m p ∈ orIn (n+m) C (opnd C k 1)
    let ls (k : ℕ) := Finset.univ.filter fun l : Fin m => Fin.natAdd n l ∈ orIn (n+m) C (opnd C k 0)
    have coverRect (p : Fin n) (l : Fin m) : I p l ↔ ∃ k ∈ K, p ∈ ps k ∧ l ∈ ls k := by
      rw [rect]
      simp only [K,ps,ls,memTop,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨k,hk,hr,ho,hl,hp⟩
        exact ⟨k,⟨hk,hr,ho⟩,hp,hl⟩
      · rintro ⟨k,⟨hk,hr,ho⟩,hp,hl⟩
        exact ⟨k,hk,hr,ho,hl,hp⟩
    obtain ⟨center, star, cover⟩ := chooseCenters free he K ps ls coverRect
    refine ⟨K.image center,cover,?_⟩
    let fiber (c : Fin (n+m)) := K.filter fun k => center k = c
    let blocks (c : Fin (n+m)) := (fiber c).biUnion fun k => (ps k) ×ˢ (ls k)
    have covers : PEqualNP.ReadTwo.incid I ⊆ (K.image center).biUnion blocks := by
      intro e he
      have hedge : I e.1 e.2 := by simpa [PEqualNP.ReadTwo.incid] using he
      obtain ⟨k,hk,hp,hl⟩ := (coverRect e.1 e.2).1 hedge
      exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_image_of_mem center hk,
        Finset.mem_biUnion.mpr ⟨k,Finset.mem_filter.mpr ⟨hk,rfl⟩,Finset.mem_product.mpr ⟨hp,hl⟩⟩⟩
    have hfib : ∑ c ∈ K.image center, (fiber c).card ≤ K.card :=
      (Finset.card_eq_sum_card_fiberwise (fun k hk => Finset.mem_image_of_mem center hk)).symm.le
    have kt : Disjoint K T := Finset.disjoint_left.mpr fun k hk ht => by
      have h₁ := (memTop.mp hk).2.2
      have h₂ := (memTop.mp ht).2.2
      rw [h₁] at h₂
      contradiction
    have sep (p : Fin n) (l : Fin m) : Fin.castAdd m p ≠ Fin.natAdd n l := by
      intro e
      have := congrArg Fin.val e
      simp only [Fin.val_castAdd,Fin.val_natAdd] at this
      omega
    have operands (k : ℕ) (hk : k ∈ K) : opnd C k 0 ∈ L ∧ opnd C k 1 ∈ P := by
      obtain ⟨a,b,eqn,ha,hb⟩ := hand k (memTop.mp hk).1 (memTop.mp hk).2.2
      simpa [opnd,eqn] using And.intro ha hb
    let side : Fin (n+m) → Finset ℕ := Fin.addCases (fun _ => L) (fun _ => P)
    let G (c : Fin (n+m)) := centerCharges (n+m) C (side c) (centerNeighborhood I c)
    have counts (c : Fin (n+m)) : (blocks c).card ≤ (G c).card + (fiber c).card := by
      revert c
      apply Fin.addCases
      · intro p
        let c := Fin.castAdd m p
        have base {e : Fin n × Fin m} (he : e ∈ blocks c) :
            ∃ k ∈ fiber c, e.1 ∈ ps k ∧ e.2 ∈ ls k ∧ e.1 = p := by
          obtain ⟨k,hk,hm⟩ := Finset.mem_biUnion.mp he
          obtain ⟨hp,hl⟩ := Finset.mem_product.mp hm
          obtain ⟨hK,hc⟩ := Finset.mem_filter.mp hk
          have hc : center k = Fin.castAdd m p := hc
          have ecenter := (star k hK e.1 hp e.2 hl).resolve_right (by intro h; exact sep _ _ (hc.symm.trans h))
          exact ⟨k,hk,hp,hl,by simpa using ecenter.symm.trans hc⟩
        simp only [G,side,Fin.addCases_left,Fin.addCases_right]
        apply fiberBound ao pureL (blocks c) (fiber c) (fun k => opnd C k 0)
          (centerNeighborhood I c) (fun e => Fin.natAdd n e.2)
        · intro a ha b hb hab
          obtain ⟨_,_,_,_,h₁⟩ := base ha
          obtain ⟨_,_,_,_,h₂⟩ := base hb
          have same : a.2 = b.2 := by simpa using hab
          exact Prod.ext (h₁.trans h₂.symm) same
        · intro e he
          obtain ⟨k,hk,hp,hl,hbase⟩ := base he
          have hK := (Finset.mem_filter.mp hk).1
          have hw := (operands k hK).1
          refine ⟨k,hk,(Finset.mem_filter.mp hl).2,hw,?_⟩
          intro v hv
          have bounds := supportSide ao pureL hw hv
          cases v using Fin.addCases with
          | left x =>
            simp only [Fin.val_castAdd] at bounds
            omega
          | right y =>
            have edge := (coverRect e.1 y).2 ⟨k,hK,hp,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩
            simpa [c,centerNeighborhood,centerAdjacent,hbase] using (hbase ▸ edge : I p y)
      · intro l
        let c := Fin.natAdd n l
        have base {e : Fin n × Fin m} (he : e ∈ blocks c) :
            ∃ k ∈ fiber c, e.1 ∈ ps k ∧ e.2 ∈ ls k ∧ e.2 = l := by
          obtain ⟨k,hk,hm⟩ := Finset.mem_biUnion.mp he
          obtain ⟨hp,hl⟩ := Finset.mem_product.mp hm
          obtain ⟨hK,hc⟩ := Finset.mem_filter.mp hk
          have hc : center k = Fin.natAdd n l := hc
          have ecenter := (star k hK e.1 hp e.2 hl).resolve_left (by intro h; exact sep _ _ (h.symm.trans hc))
          exact ⟨k,hk,hp,hl,by simpa using ecenter.symm.trans hc⟩
        simp only [G,side,Fin.addCases_left,Fin.addCases_right]
        apply fiberBound ao pureP (blocks c) (fiber c) (fun k => opnd C k 1)
          (centerNeighborhood I c) (fun e => Fin.castAdd m e.1)
        · intro a ha b hb hab
          obtain ⟨_,_,_,_,h₁⟩ := base ha
          obtain ⟨_,_,_,_,h₂⟩ := base hb
          have same : a.1 = b.1 := by simpa using hab
          exact Prod.ext same (h₁.trans h₂.symm)
        · intro e he
          obtain ⟨k,hk,hp,hl,hbase⟩ := base he
          have hK := (Finset.mem_filter.mp hk).1
          have hw := (operands k hK).2
          refine ⟨k,hk,(Finset.mem_filter.mp hp).2,hw,?_⟩
          intro v hv
          have bounds := supportSide ao pureP hw hv
          cases v using Fin.addCases with
          | left x =>
            have edge := (coverRect x e.2).2 ⟨k,hK,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,hl⟩
            simpa [c,centerNeighborhood,centerAdjacent,hbase] using (hbase ▸ edge : I x l)
          | right y =>
            simp only [Fin.val_natAdd] at bounds
            omega
    apply countPartition _ _ K T G blocks (fun c => (fiber c).card) C.size covers
      (fun c _ => counts c) hfib Finset.card_image_le (topCount ao C.output)
    · intro c _ d _ hne
      exact centerChargesDisjoint (centerNeighborhood_inter free hne)
    · exact kt
    · apply Finset.disjoint_left.mpr
      intro k hk ht
      obtain ⟨c,_,hg⟩ := Finset.mem_biUnion.mp hk
      apply centerChargeNotTop ao computes hg
      rcases Finset.mem_union.mp ht with ha | ho
      · exact (memTop.mp ha).2.1
      · exact (memTop.mp ho).2.1
    · intro k hk
      rcases Finset.mem_union.mp hk with hg | ht
      · obtain ⟨c,_,hc⟩ := Finset.mem_biUnion.mp hg
        exact (Finset.mem_filter.mp hc).1
      · rcases Finset.mem_union.mp ht with ha | ho
        · exact Finset.mem_range.mpr (memTop.mp ha).1
        · exact Finset.mem_range.mpr (memTop.mp ho).1
  · exact PEqualNP.Outside.L_meta_4990.emptyIncidenceCover I C he
