import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5274

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.ReadTwo

lemma foldl_append_spec {α β : Type} (f : List α → β → α) :
    ∀ (l : List β) (acc : List α),
      (l.foldl (fun w b => w ++ [f w b]) acc).length = acc.length + l.length ∧
      (∀ i < acc.length, (l.foldl (fun w b => w ++ [f w b]) acc)[i]? = acc[i]?) ∧
      (∀ (j : ℕ) (b : β), l[j]? = some b →
        (l.foldl (fun w b => w ++ [f w b]) acc)[acc.length + j]? =
          some (f ((l.take j).foldl (fun w x => w ++ [f w x]) acc) b)) := by
  intro l
  induction l with
  | nil =>
    intro acc
    refine ⟨by simp, fun i _ => rfl, fun j b h => by simp at h⟩
  | cons a t ih =>
    intro acc
    have h1 := ih (acc ++ [f acc a])
    refine ⟨?_, ?_, ?_⟩
    · rw [List.foldl_cons, h1.1, List.length_append, List.length_singleton, List.length_cons]
      omega
    · intro i hi
      simp only [List.foldl_cons]
      have hi' : i < (acc ++ [f acc a]).length := by simp; omega
      rw [h1.2.1 i hi', List.getElem?_append_left hi]
    · intro j b hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        simp only [List.foldl_cons, Nat.add_zero, List.take_zero, List.foldl_nil]
        have hi' : acc.length < (acc ++ [f acc a]).length := by simp
        rw [h1.2.1 acc.length hi', List.getElem?_append_right (le_refl _)]
        simp
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        simp only [List.foldl_cons, List.take_succ_cons]
        have hstep := h1.2.2 j' b hj
        simp only [List.length_append, List.length_singleton] at hstep
        have heq : acc.length + (j' + 1) = acc.length + 1 + j' := by omega
        rw [heq]
        exact hstep

lemma foldl_append_take_getD {α β : Type} (f : List α → β → α) (d : α)
    (l : List β) (acc : List α) (k i : ℕ) (hi : i < acc.length + k) (hk : k ≤ l.length) :
    ((l.take k).foldl (fun w x => w ++ [f w x]) acc).getD i d =
      (l.foldl (fun w x => w ++ [f w x]) acc).getD i d := by
  have hsplit : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hlen : ((l.take k).foldl (fun w x => w ++ [f w x]) acc).length = acc.length + k := by
    rw [(foldl_append_spec f (l.take k) acc).1, List.length_take, Nat.min_eq_left hk]
  have hget := (foldl_append_spec f (l.drop k)
    ((l.take k).foldl (fun w x => w ++ [f w x]) acc)).2.1 i (by omega)
  simp only [List.getD_eq_getElem?_getD, hget]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact (foldl_append_spec
    (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) C.gates x).1

lemma wires_getD_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  unfold Circuit.wires
  have hget := (foldl_append_spec
    (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) C.gates x).2.1 i hi
  rw [List.getD_eq_getElem?_getD, hget, List.getD_eq_getElem?_getD]

lemma isAO2_inputs (C : Circuit) (hAO : IsAO2 26 C) (j : ℕ) (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < 26 + j ∧ opnd C j 1 < 26 + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have hget : C.gates[j]? = some (gateAt C j) := by
    simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have hmem : gateAt C j ∈ C.gates := List.mem_of_getElem? hget
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 (gateAt C j) hmem
  rcases h_eq : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · simp [h_eq] at hlen
  · simp [h_eq] at hlen
  · have ha : opnd C j 0 = a := by simp [opnd, h_eq]
    have hb : opnd C j 1 = b := by simp [opnd, h_eq]
    have hrb := hAO.2.1 j hj
    have hrb0 : a < 26 + j := hrb a (by rw [h_eq]; simp)
    have hrb1 : b < 26 + j := hrb b (by rw [h_eq]; simp)
    have hop := hAO.1 (gateAt C j) hmem
    exact ⟨by rw [ha, hb], by omega, by omega, hop⟩
  · simp [h_eq] at hlen

lemma wires_getD_and (C : Circuit) (hAO : IsAO2 26 C) (x : List Bool) (hx : x.length = 26)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and) :
    (C.wires x).getD (26 + j) false =
      ((C.wires x).getD (opnd C j 0) false && (C.wires x).getD (opnd C j 1) false) := by
  obtain ⟨hin, h0, h1, _⟩ := isAO2_inputs C hAO j hj
  have hget : C.gates[j]? = some (gateAt C j) := by
    simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  unfold Circuit.wires
  have hstep := (foldl_append_spec
    (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) C.gates x).2.2 j (gateAt C j) hget
  rw [hx] at hstep
  rw [List.getD_eq_getElem?_getD, hstep, Option.getD_some, hand, hin]
  simp only [List.map_cons, List.map_nil]
  have ht0 := foldl_append_take_getD
    (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) false C.gates x j
    (opnd C j 0) (by omega) (by omega)
  have ht1 := foldl_append_take_getD
    (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) false C.gates x j
    (opnd C j 1) (by omega) (by omega)
  rw [ht0, ht1]
  simp only [GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq]

lemma wires_getD_or (C : Circuit) (hAO : IsAO2 26 C) (x : List Bool) (hx : x.length = 26)
    (j : ℕ) (hj : j < C.gates.length) (hor : (gateAt C j).op = GateOp.or) :
    (C.wires x).getD (26 + j) false =
      ((C.wires x).getD (opnd C j 0) false || (C.wires x).getD (opnd C j 1) false) := by
  obtain ⟨hin, h0, h1, _⟩ := isAO2_inputs C hAO j hj
  have hget : C.gates[j]? = some (gateAt C j) := by
    simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  unfold Circuit.wires
  have hstep := (foldl_append_spec
    (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) C.gates x).2.2 j (gateAt C j) hget
  rw [hx] at hstep
  rw [List.getD_eq_getElem?_getD, hstep, Option.getD_some, hor, hin]
  simp only [List.map_cons, List.map_nil]
  have ht0 := foldl_append_take_getD
    (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) false C.gates x j
    (opnd C j 0) (by omega) (by omega)
  have ht1 := foldl_append_take_getD
    (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) false C.gates x j
    (opnd C j 1) (by omega) (by omega)
  rw [ht0, ht1]
  simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq]

lemma card_filter_range_eq_length_filter {α : Type} (l : List α) (p : α → Bool) (d : α) :
    ((Finset.range l.length).filter (fun j => p (l.getD j d) = true)).card = (l.filter p).length := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
    rw [List.length_append, List.length_singleton, List.filter_append, List.length_append]
    rw [Finset.range_add_one, Finset.filter_insert]
    have hnot : xs.length ∉ (Finset.range xs.length).filter
        (fun j => p ((xs ++ [x]).getD j d) = true) := by
      intro hmem
      have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hmem).1
      omega
    have hcongr : (Finset.range xs.length).filter (fun j => p ((xs ++ [x]).getD j d) = true) =
        (Finset.range xs.length).filter (fun j => p (xs.getD j d) = true) := by
      apply Finset.filter_congr
      intro j hj
      have hjlt : j < xs.length := Finset.mem_range.mp hj
      have hgd : (xs ++ [x]).getD j d = xs.getD j d := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hjlt]
      rw [hgd]
    have hlast : (xs ++ [x]).getD xs.length d = x := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
      simp
    rw [hlast]
    split_ifs with hpx
    · rw [Finset.card_insert_of_notMem hnot, hcongr, ih]
      simp [hpx]
    · rw [hcongr, ih]
      have hpxf : p x = false := Bool.eq_false_iff.mpr hpx
      simp [hpxf]

def isAndOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

def isOrOp : GateOp → Bool
  | GateOp.or => true
  | _ => false

def andGates (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j => isAndOp (gateAt C j).op = true)

def orGates (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j => isOrOp (gateAt C j).op = true)

lemma isAndOp_eq_true (op : GateOp) : isAndOp op = true ↔ op = GateOp.and := by
  cases op <;> simp [isAndOp]

lemma isOrOp_eq_true (op : GateOp) : isOrOp op = true ↔ op = GateOp.or := by
  cases op <;> simp [isOrOp]

lemma andGates_card (C : Circuit) : (andGates C).card = nAnd C := by
  unfold andGates nAnd
  have h1 := card_filter_range_eq_length_filter C.gates
    (fun g => isAndOp g.op) ⟨GateOp.or, []⟩
  have h2 : C.gates.filter (fun g => isAndOp g.op) =
      C.gates.filter (fun g => @decide (g.op = GateOp.and) (gateOpDecEq g.op GateOp.and)) := by
    apply List.filter_congr
    intro g _
    cases g.op <;> rfl
  rw [← h2]
  exact h1

lemma orGates_card (C : Circuit) : (orGates C).card = nOr C := by
  unfold orGates nOr
  have h1 := card_filter_range_eq_length_filter C.gates
    (fun g => isOrOp g.op) ⟨GateOp.or, []⟩
  have h2 : C.gates.filter (fun g => isOrOp g.op) =
      C.gates.filter (fun g => @decide (g.op = GateOp.or) (gateOpDecEq g.op GateOp.or)) := by
    apply List.filter_congr
    intro g _
    cases g.op <;> rfl
  rw [← h2]
  exact h1

def vecOfFinset (Z : Finset ℕ) : List Bool :=
  List.ofFn fun i : Fin 26 => decide (i.val ∈ Z)

lemma vecOfFinset_length (Z : Finset ℕ) : (vecOfFinset Z).length = 26 := by
  simp [vecOfFinset]

lemma vecOfFinset_getD (Z : Finset ℕ) (w : ℕ) (hw : w < 26) :
    (vecOfFinset Z).getD w false = decide (w ∈ Z) := by
  simp only [vecOfFinset, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true,
    Option.getD_some]

lemma vecOfFinset_pair (p l : Fin 13) :
    vecOfFinset {p.val, 13 + l.val} =
      (List.ofFn fun x6 : Fin 13 => decide (x6 = p)) ++
        List.ofFn fun x6 : Fin 13 => decide (x6 = l) := by
  apply List.ext_getElem
  · simp [vecOfFinset]
  · intro i h1 h2
    have hi26 : i < 26 := by simp [vecOfFinset] at h1; exact h1
    simp only [vecOfFinset, List.getElem_ofFn, Finset.mem_insert, Finset.mem_singleton]
    by_cases hi : i < 13
    · rw [List.getElem_append_left (by simp [hi])]
      simp only [List.getElem_ofFn, decide_eq_decide]
      constructor
      · rintro (h | h)
        · exact Fin.ext h
        · omega
      · intro h; left; exact congrArg Fin.val h
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_ofFn, List.getElem_ofFn, decide_eq_decide]
      constructor
      · rintro (h | h)
        · omega
        · exact Fin.ext (by dsimp; omega)
      · intro h; right
        have hv : i - 13 = l.val := congrArg Fin.val h
        omega

def quadFinset (Q : Finset (Fin 13)) : Finset ℕ :=
  Q.image Fin.val ∪ (missLines singerLines3 Q).image (fun l : Fin 13 => 13 + l.val)

lemma vecOfFinset_quad (Q : Finset (Fin 13)) :
    vecOfFinset (quadFinset Q) =
      (List.ofFn fun x6 : Fin 13 => decide (x6 ∈ Q)) ++
        List.ofFn fun x6 : Fin 13 => decide (x6 ∈ missLines singerLines3 Q) := by
  apply List.ext_getElem
  · simp [vecOfFinset]
  · intro i h1 h2
    have hi26 : i < 26 := by simp [vecOfFinset] at h1; exact h1
    simp only [vecOfFinset, List.getElem_ofFn, quadFinset, Finset.mem_union, Finset.mem_image]
    by_cases hi : i < 13
    · rw [List.getElem_append_left (by simp [hi])]
      simp only [List.getElem_ofFn, decide_eq_decide]
      constructor
      · rintro (⟨p, hp, hv⟩ | ⟨l, _, hv⟩)
        · have : (⟨i, hi⟩ : Fin 13) = p := Fin.ext hv.symm
          rwa [this]
        · omega
      · intro hp; left; exact ⟨⟨i, hi⟩, hp, rfl⟩
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_ofFn, List.getElem_ofFn, decide_eq_decide]
      constructor
      · rintro (⟨p, _, hv⟩ | ⟨l, hl, hv⟩)
        · omega
        · have : (⟨i - 13, by omega⟩ : Fin 13) = l := Fin.ext (by dsimp; omega)
          rwa [this]
      · intro hl; right; exact ⟨⟨i - 13, by omega⟩, hl, by dsimp; omega⟩

def choiceNodes (C : Circuit) (hAO : IsAO2 26 C) (σ : Finset ℕ) (w : ℕ) : Finset ℕ :=
  if h1 : 26 ≤ w then
    if h2 : w - 26 < C.gates.length then
      have _ : opnd C (w - 26) 0 < w := by
        have := (isAO2_inputs C hAO (w - 26) h2).2.1; omega
      have _ : opnd C (w - 26) 1 < w := by
        have := (isAO2_inputs C hAO (w - 26) h2).2.2.1; omega
      match (gateAt C (w - 26)).op with
      | GateOp.and =>
        if (w - 26) ∈ σ then choiceNodes C hAO σ (opnd C (w - 26) 0)
        else choiceNodes C hAO σ (opnd C (w - 26) 1)
      | _ => insert w (choiceNodes C hAO σ (opnd C (w - 26) 0) ∪
          choiceNodes C hAO σ (opnd C (w - 26) 1))
    else ∅
  else {w}
termination_by w

def skipAnd (C : Circuit) (hAO : IsAO2 26 C) (σ : Finset ℕ) (w : ℕ) : ℕ :=
  if h1 : 26 ≤ w then
    if h2 : w - 26 < C.gates.length then
      have _ : opnd C (w - 26) 0 < w := by
        have := (isAO2_inputs C hAO (w - 26) h2).2.1; omega
      have _ : opnd C (w - 26) 1 < w := by
        have := (isAO2_inputs C hAO (w - 26) h2).2.2.1; omega
      match (gateAt C (w - 26)).op with
      | GateOp.and =>
        if (w - 26) ∈ σ then skipAnd C hAO σ (opnd C (w - 26) 0)
        else skipAnd C hAO σ (opnd C (w - 26) 1)
      | _ => w
    else w
  else w
termination_by w

lemma choiceNodes_lt (C : Circuit) (hAO : IsAO2 26 C) (σ : Finset ℕ) {w : ℕ} (hw : w < 26) :
    choiceNodes C hAO σ w = {w} := by
  rw [choiceNodes, dite_eq_right (by omega)]

lemma choiceNodes_and (C : Circuit) (hAO : IsAO2 26 C) (σ : Finset ℕ)
    {w : ℕ} (h1 : 26 ≤ w) (h2 : w - 26 < C.gates.length)
    (hand : (gateAt C (w - 26)).op = GateOp.and) :
    choiceNodes C hAO σ w =
      if (w - 26) ∈ σ then choiceNodes C hAO σ (opnd C (w - 26) 0)
      else choiceNodes C hAO σ (opnd C (w - 26) 1) := by
  rw [choiceNodes, dite_eq_left h1, dite_eq_left h2, hand]

lemma choiceNodes_or (C : Circuit) (hAO : IsAO2 26 C) (σ : Finset ℕ)
    {w : ℕ} (h1 : 26 ≤ w) (h2 : w - 26 < C.gates.length)
    (hor : (gateAt C (w - 26)).op = GateOp.or) :
    choiceNodes C hAO σ w =
      insert w (choiceNodes C hAO σ (opnd C (w - 26) 0) ∪
        choiceNodes C hAO σ (opnd C (w - 26) 1)) := by
  rw [choiceNodes, dite_eq_left h1, dite_eq_left h2, hor]

lemma skipAnd_lt (C : Circuit) (hAO : IsAO2 26 C) (σ : Finset ℕ) {w : ℕ} (hw : w < 26) :
    skipAnd C hAO σ w = w := by
  rw [skipAnd, dite_eq_right (by omega)]

lemma skipAnd_and (C : Circuit) (hAO : IsAO2 26 C) (σ : Finset ℕ)
    {w : ℕ} (h1 : 26 ≤ w) (h2 : w - 26 < C.gates.length)
    (hand : (gateAt C (w - 26)).op = GateOp.and) :
    skipAnd C hAO σ w =
      if (w - 26) ∈ σ then skipAnd C hAO σ (opnd C (w - 26) 0)
      else skipAnd C hAO σ (opnd C (w - 26) 1) := by
  rw [skipAnd, dite_eq_left h1, dite_eq_left h2, hand]

lemma skipAnd_or (C : Circuit) (hAO : IsAO2 26 C) (σ : Finset ℕ)
    {w : ℕ} (h1 : 26 ≤ w) (h2 : w - 26 < C.gates.length)
    (hor : (gateAt C (w - 26)).op = GateOp.or) :
    skipAnd C hAO σ w = w := by
  rw [skipAnd, dite_eq_left h1, dite_eq_left h2, hor]

lemma choiceNodes_hits_true (C : Circuit) (hAO : IsAO2 26 C) (σ Z : Finset ℕ) :
    ∀ w < 26 + C.gates.length,
      (C.wires (vecOfFinset Z)).getD w false = true →
      ∃ u ∈ choiceNodes C hAO σ w, u < 26 ∧ u ∈ Z := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw htrue
    by_cases h1 : 26 ≤ w
    · have h2 : w - 26 < C.gates.length := by omega
      obtain ⟨_, hlt0, hlt1, hop⟩ := isAO2_inputs C hAO (w - 26) h2
      have hweq : 26 + (w - 26) = w := by omega
      rcases hop with hand | hor
      · have hgate := wires_getD_and C hAO (vecOfFinset Z) (vecOfFinset_length Z) (w - 26) h2 hand
        rw [hweq] at hgate
        rw [hgate, Bool.and_eq_true] at htrue
        rw [choiceNodes_and C hAO σ h1 h2 hand]
        split_ifs
        · exact ih (opnd C (w - 26) 0) (by omega) (by omega) htrue.1
        · exact ih (opnd C (w - 26) 1) (by omega) (by omega) htrue.2
      · have hgate := wires_getD_or C hAO (vecOfFinset Z) (vecOfFinset_length Z) (w - 26) h2 hor
        rw [hweq] at hgate
        rw [hgate, Bool.or_eq_true] at htrue
        rw [choiceNodes_or C hAO σ h1 h2 hor]
        rcases htrue with ht0 | ht1
        · obtain ⟨u, hu, hu26, huZ⟩ := ih (opnd C (w - 26) 0) (by omega) (by omega) ht0
          exact ⟨u, Finset.mem_insert_of_mem (Finset.mem_union_left _ hu), hu26, huZ⟩
        · obtain ⟨u, hu, hu26, huZ⟩ := ih (opnd C (w - 26) 1) (by omega) (by omega) ht1
          exact ⟨u, Finset.mem_insert_of_mem (Finset.mem_union_right _ hu), hu26, huZ⟩
    · have hw26 : w < 26 := by omega
      rw [choiceNodes_lt C hAO σ hw26]
      rw [wires_getD_input C _ w (by rw [vecOfFinset_length]; exact hw26),
        vecOfFinset_getD Z w hw26, decide_eq_true_eq] at htrue
      exact ⟨w, Finset.mem_singleton_self w, hw26, htrue⟩

def sigOf (C : Circuit) (Z : Finset ℕ) : Finset ℕ :=
  (andGates C).filter (fun j => (C.wires (vecOfFinset Z)).getD (opnd C j 0) false = false)

lemma sigOf_subset_andGates (C : Circuit) (Z : Finset ℕ) : sigOf C Z ⊆ andGates C :=
  Finset.filter_subset _ _

lemma choiceNodes_disjoint_false (C : Circuit) (hAO : IsAO2 26 C) (Z : Finset ℕ) :
    ∀ w < 26 + C.gates.length,
      (C.wires (vecOfFinset Z)).getD w false = false →
      ∀ u ∈ choiceNodes C hAO (sigOf C Z) w, u < 26 → u ∉ Z := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hfalse u hu hu26
    by_cases h1 : 26 ≤ w
    · have h2 : w - 26 < C.gates.length := by omega
      obtain ⟨_, hlt0, hlt1, hop⟩ := isAO2_inputs C hAO (w - 26) h2
      have hweq : 26 + (w - 26) = w := by omega
      rcases hop with hand | hor
      · have hgate := wires_getD_and C hAO (vecOfFinset Z) (vecOfFinset_length Z) (w - 26) h2 hand
        rw [hweq] at hgate
        rw [hgate, Bool.and_eq_false_iff] at hfalse
        rw [choiceNodes_and C hAO (sigOf C Z) h1 h2 hand] at hu
        split_ifs at hu with hmem
        · have hf0 : (C.wires (vecOfFinset Z)).getD (opnd C (w - 26) 0) false = false :=
            (Finset.mem_filter.mp hmem).2
          exact ih (opnd C (w - 26) 0) (by omega) (by omega) hf0 u hu hu26
        · have handMem : w - 26 ∈ andGates C := by
            unfold andGates
            rw [Finset.mem_filter, Finset.mem_range, isAndOp_eq_true]
            exact ⟨h2, hand⟩
          have hf1 : (C.wires (vecOfFinset Z)).getD (opnd C (w - 26) 1) false = false := by
            rcases hfalse with hf0 | hf1
            · exfalso
              exact hmem (Finset.mem_filter.mpr ⟨handMem, hf0⟩)
            · exact hf1
          exact ih (opnd C (w - 26) 1) (by omega) (by omega) hf1 u hu hu26
      · have hgate := wires_getD_or C hAO (vecOfFinset Z) (vecOfFinset_length Z) (w - 26) h2 hor
        rw [hweq] at hgate
        rw [hgate, Bool.or_eq_false_iff] at hfalse
        rw [choiceNodes_or C hAO (sigOf C Z) h1 h2 hor] at hu
        rcases Finset.mem_insert.mp hu with rfl | hunion
        · omega
        · rcases Finset.mem_union.mp hunion with hu0 | hu1
          · exact ih (opnd C (w - 26) 0) (by omega) (by omega) hfalse.1 u hu0 hu26
          · exact ih (opnd C (w - 26) 1) (by omega) (by omega) hfalse.2 u hu1 hu26
    · have hw26 : w < 26 := by omega
      rw [choiceNodes_lt C hAO (sigOf C Z) hw26, Finset.mem_singleton] at hu
      subst hu
      rw [wires_getD_input C _ u (by rw [vecOfFinset_length]; exact hw26),
        vecOfFinset_getD Z u hw26, decide_eq_false_iff_not] at hfalse
      exact hfalse

lemma choiceNodes_ge_isOr (C : Circuit) (hAO : IsAO2 26 C) (σ : Finset ℕ) :
    ∀ w < 26 + C.gates.length,
      ∀ x ∈ choiceNodes C hAO σ w, 26 ≤ x →
        x - 26 ∈ orGates C := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw x hx hx26
    by_cases h1 : 26 ≤ w
    · have h2 : w - 26 < C.gates.length := by omega
      obtain ⟨_, hlt0, hlt1, hop⟩ := isAO2_inputs C hAO (w - 26) h2
      rcases hop with hand | hor
      · rw [choiceNodes_and C hAO σ h1 h2 hand] at hx
        split_ifs at hx
        · exact ih (opnd C (w - 26) 0) (by omega) (by omega) x hx hx26
        · exact ih (opnd C (w - 26) 1) (by omega) (by omega) x hx hx26
      · rw [choiceNodes_or C hAO σ h1 h2 hor] at hx
        rcases Finset.mem_insert.mp hx with rfl | hunion
        · unfold orGates
          rw [Finset.mem_filter, Finset.mem_range, isOrOp_eq_true]
          exact ⟨h2, hor⟩
        · rcases Finset.mem_union.mp hunion with hx0 | hx1
          · exact ih (opnd C (w - 26) 0) (by omega) (by omega) x hx0 hx26
          · exact ih (opnd C (w - 26) 1) (by omega) (by omega) x hx1 hx26
    · rw [choiceNodes_lt C hAO σ (by omega), Finset.mem_singleton] at hx
      omega

lemma choiceNodes_parent_cover (C : Circuit) (hAO : IsAO2 26 C) (σ : Finset ℕ) :
    ∀ w < 26 + C.gates.length,
      ∀ u ∈ choiceNodes C hAO σ w,
        u = skipAnd C hAO σ w ∨
        ∃ x ∈ (choiceNodes C hAO σ w).filter (fun y => 26 ≤ y),
          u = skipAnd C hAO σ (opnd C (x - 26) 0) ∨
          u = skipAnd C hAO σ (opnd C (x - 26) 1) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw u hu
    by_cases h1 : 26 ≤ w
    · have h2 : w - 26 < C.gates.length := by omega
      obtain ⟨_, hlt0, hlt1, hop⟩ := isAO2_inputs C hAO (w - 26) h2
      rcases hop with hand | hor
      · rw [choiceNodes_and C hAO σ h1 h2 hand] at hu ⊢
        rw [skipAnd_and C hAO σ h1 h2 hand]
        split_ifs at hu ⊢
        · exact ih (opnd C (w - 26) 0) (by omega) (by omega) u hu
        · exact ih (opnd C (w - 26) 1) (by omega) (by omega) u hu
      · rw [choiceNodes_or C hAO σ h1 h2 hor] at hu ⊢
        rw [skipAnd_or C hAO σ h1 h2 hor]
        rcases Finset.mem_insert.mp hu with rfl | hunion
        · exact Or.inl rfl
        · rcases Finset.mem_union.mp hunion with hu0 | hu1
          · rcases ih (opnd C (w - 26) 0) (by omega) (by omega) u hu0 with heq | ⟨x, hx, hch⟩
            · refine Or.inr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_insert_self w _, h1⟩, Or.inl heq⟩
            · have hx' : x ∈ (insert w (choiceNodes C hAO σ (opnd C (w - 26) 0) ∪
                  choiceNodes C hAO σ (opnd C (w - 26) 1))).filter (fun y => 26 ≤ y) := by
                rw [Finset.mem_filter] at hx ⊢
                exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ hx.1), hx.2⟩
              exact Or.inr ⟨x, hx', hch⟩
          · rcases ih (opnd C (w - 26) 1) (by omega) (by omega) u hu1 with heq | ⟨x, hx, hch⟩
            · refine Or.inr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_insert_self w _, h1⟩, Or.inr heq⟩
            · have hx' : x ∈ (insert w (choiceNodes C hAO σ (opnd C (w - 26) 0) ∪
                  choiceNodes C hAO σ (opnd C (w - 26) 1))).filter (fun y => 26 ≤ y) := by
                rw [Finset.mem_filter] at hx ⊢
                exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ hx.1), hx.2⟩
              exact Or.inr ⟨x, hx', hch⟩
    · rw [choiceNodes_lt C hAO σ (by omega), Finset.mem_singleton] at hu
      rw [skipAnd_lt C hAO σ (by omega)]
      exact Or.inl hu

lemma choiceNodes_vars_le_nOr (C : Circuit) (hAO : IsAO2 26 C) (σ : Finset ℕ)
    {w : ℕ} (hw : w < 26 + C.gates.length) :
    ((choiceNodes C hAO σ w).filter (fun u => u < 26)).card ≤ nOr C + 1 := by
  let W := choiceNodes C hAO σ w
  let V := W.filter (fun u => u < 26)
  let T := W.filter (fun u => 26 ≤ u)
  have hsplit : V.card + T.card = W.card := by
    have hnot : T = W.filter (fun u => ¬ u < 26) := by
      apply Finset.filter_congr
      intro u _
      exact not_lt.symm
    rw [hnot]
    exact Finset.card_filter_add_card_filter_not (fun u => u < 26)
  let children : ℕ → Finset ℕ := fun x =>
    {skipAnd C hAO σ (opnd C (x - 26) 0), skipAnd C hAO σ (opnd C (x - 26) 1)}
  have hsub : W ⊆ insert (skipAnd C hAO σ w) (T.biUnion children) := by
    intro u hu
    rcases choiceNodes_parent_cover C hAO σ w hw u hu with rfl | ⟨x, hx, hch⟩
    · exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨x, hx, ?_⟩)
      dsimp only [children]
      rcases hch with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hWle : W.card ≤ 1 + 2 * T.card := by
    calc W.card
        ≤ (insert (skipAnd C hAO σ w) (T.biUnion children)).card := Finset.card_le_card hsub
      _ ≤ (T.biUnion children).card + 1 := Finset.card_insert_le _ _
      _ ≤ (∑ x ∈ T, (children x).card) + 1 := Nat.add_le_add_right Finset.card_biUnion_le 1
      _ ≤ (∑ _x ∈ T, 2) + 1 := by
          apply Nat.add_le_add_right
          apply Finset.sum_le_sum
          intro x _
          exact Finset.card_le_two
      _ = 1 + 2 * T.card := by
          rw [Finset.sum_const, smul_eq_mul]
          omega
  have hTle : T.card ≤ nOr C := by
    rw [← orGates_card C]
    have himg : T.image (fun x => x - 26) ⊆ orGates C := by
      intro j hj
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
      have hx' := Finset.mem_filter.mp hx
      exact choiceNodes_ge_isOr C hAO σ w hw x hx'.1 hx'.2
    have hinj : Set.InjOn (fun x => x - 26) (T : Set ℕ) := by
      intro x1 hx1 x2 hx2 heq
      dsimp only at heq
      have h1 : 26 ≤ x1 := (Finset.mem_filter.mp hx1).2
      have h2 : 26 ≤ x2 := (Finset.mem_filter.mp hx2).2
      omega
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card himg
  show V.card ≤ nOr C + 1
  omega

-- PG(2, 3) 10 base quadrangles (10 * 13 = 130 > 128 = 2^7)

def baseQ (i : Fin 10) : Finset (Fin 13) :=
  match i.val with
  | 0 => {0, 1, 2, 5}
  | 1 => {0, 1, 2, 6}
  | 2 => {0, 1, 2, 7}
  | 3 => {0, 1, 2, 11}
  | 4 => {0, 1, 4, 6}
  | 5 => {0, 1, 4, 8}
  | 6 => {0, 1, 4, 11}
  | 7 => {0, 1, 5, 10}
  | 8 => {0, 1, 5, 11}
  | _ => {0, 1, 6, 7}

def shiftQ (i : Fin 10) (d : Fin 13) : Finset (Fin 13) :=
  (baseQ i).image (· + d)

lemma singerLines3_shift (p l d : Fin 13) :
    p + d ∈ singerLines3 (l + d) ↔ p ∈ singerLines3 l := by
  revert p l d
  decide

lemma baseQ_valid :
    ∀ i : Fin 10,
      (baseQ i).card = 4 ∧
      (∀ l : Fin 13, (baseQ i ∩ singerLines3 l).card ≤ 2) ∧
      (∀ p : Fin 13, p ∉ baseQ i → ∃ l ∈ missLines singerLines3 (baseQ i), p ∈ singerLines3 l) := by
  decide

lemma baseQ_shift_witness :
    ∀ i1 i2 : Fin 10, ∀ d : Fin 13,
      (i1 ≠ i2 ∨ d ≠ 0) → ∃ x ∈ baseQ i1, x - d ∉ baseQ i2 := by
  decide

lemma baseQ_shift_ne (i1 i2 : Fin 10) (d : Fin 13) (h : i1 ≠ i2 ∨ d ≠ 0) :
    baseQ i1 ≠ (baseQ i2).image (· + d) := by
  obtain ⟨x, hx1, hx2⟩ := baseQ_shift_witness i1 i2 d h
  intro heq
  have hximg : x ∈ (baseQ i2).image (· + d) := heq ▸ hx1
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hximg
  rw [add_sub_cancel_right] at hx2
  exact hx2 hy

lemma shiftQ_mem_quadrangles (i : Fin 10) (d : Fin 13) :
    shiftQ i d ∈ quadrangles singerLines3 := by
  have hv := baseQ_valid i
  unfold quadrangles
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  refine ⟨⟨Finset.subset_univ _, ?_⟩, ?_⟩
  · unfold shiftQ
    rw [Finset.card_image_of_injective _ (fun a b h => add_right_cancel h)]
    exact hv.1
  · intro l
    have hcard : (shiftQ i d ∩ singerLines3 l).card = (baseQ i ∩ singerLines3 (l - d)).card := by
      have himg : shiftQ i d ∩ singerLines3 l = (baseQ i ∩ singerLines3 (l - d)).image (· + d) := by
        ext x
        simp only [shiftQ, Finset.mem_inter, Finset.mem_image]
        constructor
        · rintro ⟨⟨a, ha, rfl⟩, hxl⟩
          refine ⟨a, ⟨ha, ?_⟩, rfl⟩
          have heq : l - d + d = l := sub_add_cancel l d
          rw [← heq] at hxl
          exact (singerLines3_shift a (l - d) d).mp hxl
        · rintro ⟨a, ⟨ha, hal⟩, rfl⟩
          refine ⟨⟨a, ha, rfl⟩, ?_⟩
          have heq : l - d + d = l := sub_add_cancel l d
          rw [← heq]
          exact (singerLines3_shift a (l - d) d).mpr hal
      rw [himg, Finset.card_image_of_injective _ (fun a b h => add_right_cancel h)]
    rw [hcard]
    exact hv.2.1 (l - d)

lemma shiftQ_card (i : Fin 10) (d : Fin 13) : (shiftQ i d).card = 4 := by
  unfold shiftQ
  rw [Finset.card_image_of_injective _ (fun a b h => add_right_cancel h)]
  exact (baseQ_valid i).1

lemma shiftQ_miss_cover (i : Fin 10) (d : Fin 13) (p : Fin 13) (hp : p ∉ shiftQ i d) :
    ∃ l ∈ missLines singerLines3 (shiftQ i d), p ∈ singerLines3 l := by
  have hp0 : p - d ∉ baseQ i := by
    intro hmem
    apply hp
    unfold shiftQ
    exact Finset.mem_image.mpr ⟨p - d, hmem, sub_add_cancel p d⟩
  obtain ⟨l0, hl0m, hpl0⟩ := (baseQ_valid i).2.2 (p - d) hp0
  refine ⟨l0 + d, ?_, ?_⟩
  · unfold missLines at hl0m ⊢
    rw [Finset.mem_filter] at hl0m ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.disjoint_left]
    intro x hxl hxQ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxQ
    have hal0 : a ∈ singerLines3 l0 := (singerLines3_shift a l0 d).mp hxl
    exact Finset.disjoint_left.mp hl0m.2 hal0 ha
  · have h := (singerLines3_shift (p - d) l0 d).mpr hpl0
    rwa [sub_add_cancel] at h

lemma shiftQ_injective : Function.Injective (fun p : Fin 10 × Fin 13 => shiftQ p.1 p.2) := by
  rintro ⟨i1, d1⟩ ⟨i2, d2⟩ heq
  dsimp only at heq
  by_contra hne
  have hdisj : i1 ≠ i2 ∨ d2 - d1 ≠ 0 := by
    by_cases hi : i1 = i2
    · right
      intro hd
      apply hne
      have hd' : d2 = d1 := sub_eq_zero.mp hd
      exact Prod.ext hi hd'.symm
    · exact Or.inl hi
  apply baseQ_shift_ne i1 i2 (d2 - d1) hdisj
  ext x
  have hx : x + d1 ∈ shiftQ i1 d1 ↔ x + d1 ∈ shiftQ i2 d2 := by rw [heq]
  simp only [shiftQ, Finset.mem_image] at hx ⊢
  constructor
  · intro h1
    obtain ⟨y, hy, hyEq⟩ := hx.mp ⟨x, h1, rfl⟩
    refine ⟨y, hy, ?_⟩
    have : y + (d2 - d1) + d1 = x + d1 := by
      rw [add_assoc, sub_add_cancel, hyEq]
    exact add_right_cancel this
  · rintro ⟨y, hy, rfl⟩
    have h2 : y + (d2 - d1) + d1 = y + d2 := by rw [add_assoc, sub_add_cancel]
    obtain ⟨z, hz, hzEq⟩ := hx.mpr ⟨y, hy, h2.symm⟩
    have : z = y + (d2 - d1) := add_right_cancel hzEq
    rwa [← this]

lemma baseQ0_quadFinset_card : (quadFinset (baseQ 0)).card = 7 := by
  decide

lemma baseQ0_quadFinset_sub : quadFinset (baseQ 0) ⊆ Finset.range 26 := by
  decide

lemma baseQ0_nonmiss_hit :
    ∀ l : Fin 13, l ∉ missLines singerLines3 (baseQ 0) →
      ∃ p ∈ baseQ 0, p ∈ singerLines3 l := by
  decide

lemma solve_5274 (C : Circuit) (hAO : IsAO2 26 C)
    (hinc : ∀ p l : Fin 13, p ∈ singerLines3 l →
      C.eval ((List.ofFn fun x6 : Fin 13 => decide (x6 = p)) ++
        List.ofFn fun x6 : Fin 13 => decide (x6 = l)) = true)
    (hquad : ∀ Q ∈ quadrangles singerLines3,
      C.eval ((List.ofFn fun x6 : Fin 13 => decide (x6 ∈ Q)) ++
        List.ofFn fun x6 : Fin 13 => decide (x6 ∈ missLines singerLines3 Q)) = false) :
    8 ≤ nAnd C ∧ 18 ≤ nOr C := by
  have hout_lt : C.output < 26 + C.gates.length := by
    by_contra hge
    have h00 : (0 : Fin 13) ∈ singerLines3 0 := by decide
    have ht := hinc 0 0 h00
    have hlen : (C.wires ((List.ofFn fun x6 : Fin 13 => decide (x6 = (0 : Fin 13))) ++
        List.ofFn fun x6 : Fin 13 => decide (x6 = (0 : Fin 13)))).length =
        26 + C.gates.length := by
      rw [wires_length]; simp
    have hdef : C.eval ((List.ofFn fun x6 : Fin 13 => decide (x6 = (0 : Fin 13))) ++
        List.ofFn fun x6 : Fin 13 => decide (x6 = (0 : Fin 13))) = false := by
      unfold Circuit.eval
      exact List.getD_eq_default _ _ (by omega)
    rw [hdef] at ht
    cases ht
  have hinc_wire : ∀ (p l : Fin 13), p ∈ singerLines3 l →
      (C.wires (vecOfFinset {p.val, 13 + l.val})).getD C.output false = true := by
    intro p l hpl
    rw [vecOfFinset_pair]
    exact hinc p l hpl
  have hquad_wire : ∀ Q ∈ quadrangles singerLines3,
      (C.wires (vecOfFinset (quadFinset Q))).getD C.output false = false := by
    intro Q hQ
    rw [vecOfFinset_quad]
    exact hquad Q hQ
  constructor
  · -- Part A: 8 ≤ nAnd C via injectivity of (i, d) ↦ sigOf C (quadFinset (shiftQ i d))
    let f : Fin 10 × Fin 13 → Finset ℕ := fun x => sigOf C (quadFinset (shiftQ x.1 x.2))
    have hf_sub : ∀ x : Fin 10 × Fin 13, f x ∈ (andGates C).powerset := fun x =>
      Finset.mem_powerset.mpr (sigOf_subset_andGates C _)
    have hf_inj : Function.Injective f := by
      intro x1 x2 hfeq
      by_contra hne
      have hQne : shiftQ x1.1 x1.2 ≠ shiftQ x2.1 x2.2 := fun h => hne (shiftQ_injective h)
      have hex_p : ∃ p ∈ shiftQ x2.1 x2.2, p ∉ shiftQ x1.1 x1.2 := by
        by_contra hall
        push Not at hall
        have hsub : shiftQ x2.1 x2.2 ⊆ shiftQ x1.1 x1.2 := hall
        have heq := Finset.eq_of_subset_of_card_le hsub
          (by rw [shiftQ_card, shiftQ_card])
        exact hQne heq.symm
      obtain ⟨p, hp2, hp1⟩ := hex_p
      obtain ⟨l, hl1, hpl⟩ := shiftQ_miss_cover x1.1 x1.2 p hp1
      have hhit := choiceNodes_hits_true C hAO (f x1) {p.val, 13 + l.val} C.output hout_lt
        (hinc_wire p l hpl)
      obtain ⟨u, huV, hu26, huPair⟩ := hhit
      simp only [Finset.mem_insert, Finset.mem_singleton] at huPair
      rcases huPair with rfl | rfl
      · have huV2 : p.val ∈ choiceNodes C hAO (f x2) C.output := by rwa [← hfeq]
        have hnot := choiceNodes_disjoint_false C hAO (quadFinset (shiftQ x2.1 x2.2)) C.output
          hout_lt (hquad_wire _ (shiftQ_mem_quadrangles x2.1 x2.2)) p.val huV2 hu26
        exact hnot (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp2))
      · have hnot := choiceNodes_disjoint_false C hAO (quadFinset (shiftQ x1.1 x1.2)) C.output
          hout_lt (hquad_wire _ (shiftQ_mem_quadrangles x1.1 x1.2)) (13 + l.val) huV hu26
        exact hnot (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hl1))
    have hcard_le : (Finset.univ : Finset (Fin 10 × Fin 13)).card ≤ (andGates C).powerset.card := by
      rw [← Finset.card_image_of_injective Finset.univ hf_inj]
      exact Finset.card_le_card (fun s hs => by
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hs
        exact hf_sub x)
    have h130 : (Finset.univ : Finset (Fin 10 × Fin 13)).card = 130 := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    rw [h130, Finset.card_powerset, andGates_card C] at hcard_le
    by_contra hlt
    have hle7 : nAnd C ≤ 7 := by omega
    have hpow : 2 ^ nAnd C ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) hle7
    omega
  · -- Part B: 18 ≤ nOr C via |V(C.output, sigOf Q0)| ≥ 19
    let Q0 := baseQ 0
    let σ0 := sigOf C (quadFinset Q0)
    have hQ0mem : Q0 ∈ quadrangles singerLines3 := by
      have h := shiftQ_mem_quadrangles 0 0
      have heq : shiftQ 0 0 = Q0 := by decide
      rwa [heq] at h
    have hdisj : ∀ u ∈ choiceNodes C hAO σ0 C.output, u < 26 → u ∉ quadFinset Q0 :=
      choiceNodes_disjoint_false C hAO (quadFinset Q0) C.output hout_lt (hquad_wire Q0 hQ0mem)
    have hsub : Finset.range 26 \ quadFinset Q0 ⊆
        (choiceNodes C hAO σ0 C.output).filter (fun u => u < 26) := by
      intro u hu
      rw [Finset.mem_sdiff, Finset.mem_range] at hu
      rw [Finset.mem_filter]
      refine ⟨?_, hu.1⟩
      by_cases hu13 : u < 13
      · let p : Fin 13 := ⟨u, hu13⟩
        have hpnot : p ∉ Q0 := fun hp => hu.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp))
        obtain ⟨l, hlmiss, hpl⟩ := (baseQ_valid 0).2.2 p hpnot
        obtain ⟨v, hvN, hv26, hvPair⟩ :=
          choiceNodes_hits_true C hAO σ0 {p.val, 13 + l.val} C.output hout_lt (hinc_wire p l hpl)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hvPair
        rcases hvPair with rfl | rfl
        · exact hvN
        · exfalso
          exact hdisj (13 + l.val) hvN hv26
            (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hlmiss))
      · let l : Fin 13 := ⟨u - 13, by omega⟩
        have hlnot : l ∉ missLines singerLines3 Q0 := by
          intro hl
          apply hu.2
          refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨l, hl, ?_⟩)
          dsimp only [l]
          omega
        obtain ⟨p, hpQ0, hpl⟩ := baseQ0_nonmiss_hit l hlnot
        obtain ⟨v, hvN, hv26, hvPair⟩ :=
          choiceNodes_hits_true C hAO σ0 {p.val, 13 + l.val} C.output hout_lt (hinc_wire p l hpl)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hvPair
        rcases hvPair with rfl | rfl
        · exfalso
          exact hdisj p.val hvN hv26
            (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hpQ0))
        · have heq : 13 + l.val = u := by dsimp only [l]; omega
          rwa [heq] at hvN
    have h19 : 19 ≤ ((choiceNodes C hAO σ0 C.output).filter (fun u => u < 26)).card := by
      have hcard : (Finset.range 26 \ quadFinset Q0).card = 19 := by
        dsimp only [Q0]
        have hsum := Finset.card_sdiff_add_card_eq_card baseQ0_quadFinset_sub
        rw [Finset.card_range, baseQ0_quadFinset_card] at hsum
        omega
      rw [← hcard]
      exact Finset.card_le_card hsub
    have hle := choiceNodes_vars_le_nOr C hAO σ0 hout_lt
    omega

end PEqualNP.Outside.L_meta_5274

theorem PEqualNP.Outside.L_meta_5274 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x1.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) → (∀ x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x1.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.false) → (8 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x1 ∧ (18 : ℕ) ≤ PEqualNP.ReadTwo.nOr x1 :=
  PEqualNP.Outside.L_meta_5274.solve_5274
