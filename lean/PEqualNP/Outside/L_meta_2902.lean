import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2902

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Gate simplification follows the restriction construction used for L-meta-2553.

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2


lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | _ => (none, Sum.inl false)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg
  · simp at hg

lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : ins.length ≤ 2)
    (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]

lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj


def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

lemma elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : Ok g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1
    · simpa using hg.2
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def readers (k : ℕ) (gs : List Gate) : List Gate :=
  gs.filter (fun g => decide (k ∈ g.inputs))

lemma elim_reads (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (hok : ∀ g ∈ gs, Ok g) (hk : k < acc.1.length)
    (hc : acc.1.getD k (Sum.inl false) = Sum.inl false) :
    (elim n gs acc).2.length + (readers k gs).length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elim, readers]
  | cons g gs ih =>
    have hg := hok g List.mem_cons_self
    have hlt : k < (elimStep n acc g).1.length := by simp [elimStep]; omega
    have hc' : (elimStep n acc g).1.getD k (Sum.inl false) = Sum.inl false := by
      simp only [elimStep]
      rw [getD_snoc_ne _ _ _ _ (by omega), hc]
    have ht := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hlt hc'
    change (elim n gs (elimStep n acc g)).2.length + (readers k (g :: gs)).length ≤ _
    by_cases hread : k ∈ g.inputs
    · rw [elimStep_none n acc g hg k hread false hc] at ht
      simp [readers, hread] at ht ⊢
      omega
    · have ho := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      have hstep : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        omega
      simp [readers, hread] at ht ⊢
      omega

-- A monotone circuit is determined by the positive and negative boundary samples.
def bits (m : ℕ) (i : Fin 9) : Bool := m.testBit i.val

def encoded (x : Fin 9 → Bool) : List Bool :=
  List.ofFn x ++ [x 0 || x 4]

def edges : List (Fin 9 × Fin 9) :=
  [(0, 1), (1, 2), (2, 3), (0, 4), (3, 4), (0, 5),
    (1, 6), (2, 7), (5, 7), (3, 8), (5, 8), (6, 8)]

def edgeFun (x : Fin 9 → Bool) : Bool :=
  edges.any fun e => x e.1 && x e.2

def samples : List ℕ :=
  [3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116,
    132, 138, 160, 201, 208, 261, 264, 276, 288, 320, 385, 402]

def positive : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]

def covers (m q : ℕ) : Bool :=
  if edgeFun (bits m) then decide (q ∈ positive) && ((q &&& m) == q)
  else !decide (q ∈ positive) && ((q &&& m) == m)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
lemma coverage : ∀ m : Fin 512, samples.any (covers m.val) = true := by
  decide +kernel

def LeL (a b : List Bool) : Prop :=
  ∀ i, a.getD i false = true → b.getD i false = true

-- The gate monotonicity argument follows the LowMergeWires helper.
lemma op_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f g : ℕ → Bool) (h : ∀ i, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro hf x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (hf (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨g i, ⟨i, hi, rfl⟩, h i hx⟩

lemma wires_mono (gs : List Gate) (hgs : ∀ g ∈ gs, Ok g) :
    ∀ a b : List Bool, a.length = b.length → LeL a b →
      LeL (wiresFrom gs a) (wiresFrom gs b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    change LeL (wiresFrom gs (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]))
      (wiresFrom gs (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]))
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [hl]
    · intro i hi
      by_cases he : i = a.length
      · subst i
        rw [getD_snoc_eq] at hi
        rw [hl, getD_snoc_eq]
        exact op_mono g.op (hgs g List.mem_cons_self).1 _ _ _ h hi
      · rw [getD_snoc_ne _ _ _ _ he] at hi
        rw [getD_snoc_ne _ _ _ _ (by rwa [← hl])]
        exact h i hi

lemma encoded_length (x : Fin 9 → Bool) : (encoded x).length = 10 := by
  simp [encoded]

lemma read_encoded (x : Fin 9 → Bool) (i : ℕ) :
    (encoded x).getD i false =
      if h : i < 9 then x ⟨i, h⟩ else if i = 9 then x 0 || x 4 else false := by
  by_cases hi : i < 9
  · rw [dif_pos hi]
    unfold encoded
    have hl : i < (List.ofFn x).length := by simpa using hi
    rw [List.getD_append _ _ _ _ hl, List.getD_eq_getElem _ _ hl, List.getElem_ofFn]
  · rw [dif_neg hi]
    by_cases he : i = 9
    · subst i
      rw [if_pos rfl]
      exact getD_snoc_len _ _ _ _ (by simp)
    · rw [if_neg he, List.getD_eq_default _ _ (by rw [encoded_length]; omega)]

lemma encoded_mono {x y : Fin 9 → Bool}
    (h : ∀ j, x j = true → y j = true) : LeL (encoded x) (encoded y) := by
  intro i hi
  rw [read_encoded] at hi ⊢
  by_cases h9 : i < 9
  · simp only [dif_pos h9] at hi ⊢
    exact h _ hi
  · simp only [dif_neg h9] at hi ⊢
    by_cases he : i = 9
    · simp only [if_pos he, Bool.or_eq_true] at hi ⊢
      exact hi.elim (fun hx => Or.inl (h _ hx)) (fun hx => Or.inr (h _ hx))
    · simpa only [if_neg he] using hi

lemma eval_mono (C : Circuit) (hC : Monotone2 C) {x y : Fin 9 → Bool}
    (h : ∀ j, x j = true → y j = true) :
    C.eval (encoded x) = true → C.eval (encoded y) = true := by
  exact wires_mono C.gates hC _ _ (by simp [encoded_length]) (encoded_mono h) C.output

lemma bits_mono {a b : ℕ} (h : (a &&& b) = a) :
    ∀ j, bits a j = true → bits b j = true := by
  intro j hj
  have hbit := congrArg (fun m : ℕ => bits m j) h
  simpa [bits, Nat.testBit_and, show a.testBit j.val = true from hj] using hbit

lemma bits_from_fn (x : Fin 9 → Bool) : ∃ m : Fin 512, bits m.val = x := by
  let b := BitVec.ofBoolListLE (List.ofFn x)
  have hb : b.toNat < 512 := by simpa using b.isLt
  refine ⟨⟨b.toNat, hb⟩, ?_⟩
  funext i
  change b.toNat.testBit i.val = x i
  rw [BitVec.testBit_toNat]
  change (BitVec.ofBoolListLE (List.ofFn x)).getLsbD i.val = x i
  have hi : i.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]

lemma samples_determine (C : Circuit) (hC : Monotone2 C)
    (h : ∀ q ∈ samples, C.eval (encoded (bits q)) = decide (q ∈ positive))
    (x : Fin 9 → Bool) : C.eval (encoded x) = edgeFun x := by
  obtain ⟨m, rfl⟩ := bits_from_fn x
  obtain ⟨q, hq, hcover⟩ := List.any_eq_true.mp (coverage m)
  cases he : edgeFun (bits m.val) with
  | true =>
    have hc : q ∈ positive ∧ (q &&& m.val) = q := by
      simpa [covers, he, Bool.and_eq_true, beq_iff_eq] using hcover
    exact eval_mono C hC (bits_mono hc.2) ((h q hq).trans (decide_eq_true hc.1))
  | false =>
    have hc : q ∉ positive ∧ (q &&& m.val) = m.val := by
      simpa [covers, he, Bool.and_eq_true, beq_iff_eq] using hcover
    cases hm : C.eval (encoded (bits m.val)) with
    | false => rfl
    | true =>
      have hqm := eval_mono C hC (bits_mono ((Nat.and_comm _ _).trans hc.2)) hm
      rw [h q hq, decide_eq_false hc.1] at hqm
      contradiction

def clearBit (k : Fin 9) (x : Fin 9 → Bool) (i : Fin 9) : Bool :=
  if i = k then false else x i

def initial (k : Fin 9) : List Stat :=
  List.ofFn fun i : Fin 10 => if i.val = k.val then Sum.inl false else Sum.inr i.val

lemma initial_inv (k : Fin 9) (hk0 : k ≠ 0) (hk4 : k ≠ 4) (x : Fin 9 → Bool) :
    Inv 10 (encoded x) (encoded (clearBit k x)) (initial k, []) := by
  refine ⟨by simp [initial, encoded_length], ?_⟩
  intro j
  simp only [List.length_nil, Nat.add_zero]
  change ((initial k).getD j (Sum.inl false)).Valid 10 ∧
    ((initial k).getD j (Sum.inl false)).val (encoded x) =
      (encoded (clearBit k x)).getD j false
  by_cases hj : j < 10
  · rw [List.getD_eq_getElem _ _ (by simpa [initial] using hj)]
    simp only [initial, List.getElem_ofFn]
    by_cases he : j = k.val
    · subst j
      simp only [if_pos rfl, Stat.Valid, Stat.val, true_and]
      rw [read_encoded, dif_pos k.isLt]
      simp [clearBit]
    · simp only [if_neg he, Stat.Valid, Stat.val, hj, true_and]
      rw [read_encoded, read_encoded]
      split
      · have hjk : (⟨j, ‹j < 9›⟩ : Fin 9) ≠ k := fun h => he (congrArg Fin.val h)
        simp [clearBit, hjk]
      · simp [clearBit, Ne.symm hk0, Ne.symm hk4]
  · rw [List.getD_eq_default _ _ (by simpa [initial] using Nat.le_of_not_gt hj),
      List.getD_eq_default _ _ (by rw [encoded_length]; omega)]
    exact ⟨trivial, rfl⟩

lemma cleared_edges (k : Fin 9) (x : Fin 9 → Bool) :
    edgeFun (clearBit k x) =
      edges.any fun e => e.1 != k && e.2 != k && x e.1 && x e.2 := by
  unfold edgeFun
  congr 1
  funext e
  by_cases ha : e.1 = k <;> by_cases hb : e.2 = k <;>
    simp_all [clearBit, bne, beq_false_of_ne, Bool.and_assoc]

lemma solve (C : Circuit) (hC : Monotone2 C)
    (h : ∀ q ∈ samples, C.eval (encoded (bits q)) = decide (q ∈ positive))
    (k : Fin 9) (hk : k ∈ ([1, 2, 3, 5, 8] : List (Fin 9)))
    (hr : 4 ≤ (readers k.val C.gates).length) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 4 ≤ C.size ∧
      ∀ x : Fin 9 → Bool,
        D.eval (encoded x) = edges.any fun e => e.1 != k && e.2 != k && x e.1 && x e.2 := by
  have hne : k ≠ 0 ∧ k ≠ 4 := by
    have hall : ∀ i : Fin 9, i ∈ ([1, 2, 3, 5, 8] : List (Fin 9)) → i ≠ 0 ∧ i ≠ 4 := by decide
    exact hall k hk
  let start : List Stat × List Gate := (initial k, [])
  let acc := elim 10 C.gates start
  have hp : k.val < start.1.length := by
    simp [start, initial]
    have := k.isLt
    omega
  have hconst : start.1.getD k.val (Sum.inl false) = Sum.inl false := by
    rw [List.getD_eq_getElem _ _ hp]
    simp only [start, initial, List.getElem_ofFn, if_pos rfl, if_true]
  have hlen : acc.2.length + 4 ≤ C.size := by
    have hreads := elim_reads 10 k.val C.gates start hC hp hconst
    change acc.2.length + (readers k.val C.gates).length ≤ 0 + C.size at hreads
    omega
  have hval (x : Fin 9 → Bool) :
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (encoded x)) =
        edges.any fun e => e.1 != k && e.2 != k && x e.1 && x e.2 := by
    have hinv := inv_elim 10 (encoded x) (encoded_length x) C.gates
      (encoded (clearBit k x)) start hC (initial_inv k hne.1 hne.2 x)
    calc
      _ = C.eval (encoded (clearBit k x)) := (hinv.2 C.output).2
      _ = edgeFun (clearBit k x) := samples_determine C hC h _
      _ = _ := cleared_edges k x
  cases ho : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    have hb : b = false := by
      have hz := hval (fun _ => false)
      rw [ho] at hz
      simpa [Stat.val, edges] using hz
    subst b
    refine ⟨⟨[], 10⟩, by simp [Monotone2], ?_, ?_⟩
    · change 0 + 4 ≤ C.size
      omega
    · intro x
      have hx := hval x
      rw [ho] at hx
      change false = _ at hx
      change (encoded x).getD 10 false = _
      rw [List.getD_eq_default _ _ (by rw [encoded_length])]
      exact hx
  | inr j =>
    refine ⟨⟨acc.2, j⟩, elim_ok 10 C.gates start (by simp [start]), hlen, ?_⟩
    intro x
    have hx := hval x
    rw [ho] at hx
    exact hx

end PEqualNP.Outside.L_meta_2902

theorem PEqualNP.Outside.L_meta_2902 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       ∀ x4 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], (4 : ℕ) ≤ (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (↑x4 ∈ x6.inputs)) x1.gates).length → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x7.size + (4 : ℕ) ≤ x1.size ∧ ∀ (x8 : Fin (9 : ℕ) → Bool), x7.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x9.1 != x4 && x9.2 != x4 && x8 x9.1 && x8 x9.2 := by
  exact PEqualNP.Outside.L_meta_2902.solve
