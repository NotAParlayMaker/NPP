import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_568_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    change (wiresFrom gs (w ++ [_])).length = _
    rw [ih]; simp; omega

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (wiresFrom gs (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ h]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def activeInputs (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

theorem activeInputs_length_le (g : Gate) : (activeInputs g).length ≤ g.inputs.length := by
  unfold activeInputs
  cases g.op <;> simp

theorem activeInputs_not_length (g : Gate) (h : g.op = GateOp.not) :
    (activeInputs g).length ≤ 1 := by
  simp [activeInputs, h]

theorem gateEval_active (g : Gate) (f : ℕ → Bool) :
    g.op.eval ((activeInputs g).map f) = g.op.eval (g.inputs.map f) := by
  unfold activeInputs
  cases g.op with
  | not =>
    cases g.inputs with
    | nil => rfl
    | cons a l => rfl
  | and => rfl
  | or => rfl
  | mod _ => rfl
  | maj => rfl

def Reads (C : Circuit) (j : Fin C.gates.length) (a : ℕ) : Prop :=
  (C.gates.get j).op = GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨
  (C.gates.get j).op ≠ GateOp.not ∧ a ∈ (C.gates.get j).inputs

theorem mem_activeInputs_iff (C : Circuit) (j : Fin C.gates.length) (a : ℕ) :
    a ∈ activeInputs (C.gates.get j) ↔ Reads C j a := by
  unfold activeInputs Reads
  cases h : (C.gates.get j).op with
  | not =>
    simp only [true_and, ne_eq, not_true_eq_false, false_and, or_false]
    cases (C.gates.get j).inputs with
    | nil => simp
    | cons x l => simp [eq_comm]
  | and => simp
  | or => simp
  | mod _ => simp
  | maj => simp

def Edge (C : Circuit) (m a b : ℕ) : Prop :=
  ∃ j : Fin C.gates.length, b = m + j.val ∧ Reads C j a

def Reach (C : Circuit) (m a b : ℕ) : Prop :=
  Relation.TransGen (Edge C m) a b

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem ok_op (g : Gate) (h : Ok g) :
    g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
  simpa [Ok, Set.mem_insert_iff, Set.mem_singleton_iff] using h.1

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hs => Nat.lt_of_lt_of_le hs h

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (ceq : Bool) (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] =>
    if ceq && (j == k) then (none, Sum.inr j) else (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (ceq : Bool) (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] =>
    if ceq && (j == k) then (none, Sum.inr j) else (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (ceq : Bool) (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd ceq m ins
  | GateOp.or => simpOr ceq m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (ceq : Bool) (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify ceq op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    · split_ifs at hg
      simp only [Option.some.injEq] at hg; subst hg; simp [Ok]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    · split_ifs at hg
      simp only [Option.some.injEq] at hg; subst hg; simp [Ok]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    · subst hg; simp [Ok]
  · simp at hg
  · simp at hg

theorem simplify_sound (ceq : Bool) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify ceq op w.length ins).1.toList.length)
      (simplify ceq op w.length ins).2 ∧
    statVal (wiresFrom (simplify ceq op w.length ins).1.toList w)
      (simplify ceq op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b
      · simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval]
      · rename_i c j; cases c <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j c; cases c <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j k
        simp only [simplify, simpAnd]
        split_ifs with hcond
        · have hjk : j = k := by simp at hcond; exact hcond.2
          subst hjk
          simp_all [statValid, statVal, GateOp.eval, wiresFrom]
        · simp_all [statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b
      · simp_all [simplify, simpOr, statValid, statVal, GateOp.eval]
      · rename_i c j; cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j c; cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j k
        simp only [simplify, simpOr]
        split_ifs with hcond
        · have hjk : j = k := by simp at hcond; exact hcond.2
          subst hjk
          simp_all [statValid, statVal, GateOp.eval, wiresFrom]
        · simp_all [statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

theorem simplify_none_of_const (ceq : Bool) (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (c : Bool) (hc : Sum.inl c ∈ ins) :
    (simplify ceq op m ins).1 = none := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_const_of_not_or_and_false (ceq : Bool) (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.not ∨ op = GateOp.and) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : Sum.inl false ∈ ins) :
    ∃ b : Bool, (simplify ceq op m ins).2 = Sum.inl b := by
  rcases hop with rfl | rfl
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]

-- Stepwise elimination with skipped gates (forced to constant false)
def elimStep (m : ℕ) (ceq : Bool) (skip : ℕ → Bool)
    (acc : List Stat × List Gate) (pg : ℕ × Gate) : List Stat × List Gate :=
  if skip pg.1 then
    (acc.1 ++ [Sum.inl false], acc.2)
  else
    let res := simplify ceq pg.2.op (m + acc.2.length)
      ((activeInputs pg.2).map fun i => acc.1.getD i (Sum.inl false))
    (acc.1 ++ [res.2], acc.2 ++ res.1.toList)

def elimRec (m : ℕ) (ceq : Bool) (skip : ℕ → Bool) :
    ℕ → List Gate → List Stat × List Gate → List Stat × List Gate
  | _, [], acc => acc
  | j, g :: gs, acc => elimRec m ceq skip (j + 1) gs (elimStep m ceq skip acc (j, g))

def evalModRec (skip : ℕ → Bool) : ℕ → List Gate → List Bool → List Bool
  | _, [], w => w
  | j, g :: gs, w =>
    let v := if skip j then false else g.op.eval (g.inputs.map fun i => w.getD i false)
    evalModRec skip (j + 1) gs (w ++ [v])

theorem evalModRec_length (skip : ℕ → Bool) : ∀ (j : ℕ) (gs : List Gate) (w : List Bool),
    (evalModRec skip j gs w).length = w.length + gs.length
  | _, [], w => by simp [evalModRec]
  | j, g :: gs, w => by
    simp only [evalModRec, evalModRec_length, List.length_append, List.length_cons, List.length_nil]
    omega

theorem evalModRec_getD_lt (skip : ℕ → Bool) : ∀ (j : ℕ) (gs : List Gate) (w : List Bool) (i : ℕ),
    i < w.length → (evalModRec skip j gs w).getD i false = w.getD i false
  | _, [], w, i, _ => rfl
  | j, g :: gs, w, i, hi => by
    simp only [evalModRec]
    rw [evalModRec_getD_lt skip (j + 1) gs _ i (by simp; omega), List.getD_append _ _ _ _ hi]

theorem evalModRec_false_eq_wiresFrom : ∀ (j : ℕ) (gs : List Gate) (w : List Bool),
    evalModRec (fun _ => false) j gs w = wiresFrom gs w
  | _, [], w => rfl
  | j, g :: gs, w => by
    simp only [evalModRec, Bool.false_eq_true, ite_false]
    exact evalModRec_false_eq_wiresFrom (j + 1) gs _

theorem elimRec_fst_length (m : ℕ) (ceq : Bool) (skip : ℕ → Bool) :
    ∀ (j : ℕ) (gs : List Gate) (acc : List Stat × List Gate),
      (elimRec m ceq skip j gs acc).1.length = acc.1.length + gs.length
  | _, [], acc => by simp [elimRec]
  | j, g :: gs, acc => by
    simp only [elimRec]
    rw [elimRec_fst_length]
    have hstep : (elimStep m ceq skip acc (j, g)).1.length = acc.1.length + 1 := by
      unfold elimStep; split <;> simp
    rw [hstep, List.length_cons]; omega

theorem elimRec_getD_lt (m : ℕ) (ceq : Bool) (skip : ℕ → Bool) :
    ∀ (j : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (i : ℕ),
      i < acc.1.length →
      (elimRec m ceq skip j gs acc).1.getD i (Sum.inl false) = acc.1.getD i (Sum.inl false)
  | _, [], acc, i, _ => rfl
  | j, g :: gs, acc, i, hi => by
    simp only [elimRec]
    have hstep_len : (elimStep m ceq skip acc (j, g)).1.length = acc.1.length + 1 := by
      unfold elimStep; split <;> simp
    rw [elimRec_getD_lt m ceq skip (j + 1) gs _ i (by omega)]
    unfold elimStep
    split <;> exact List.getD_append _ _ _ _ hi

theorem elimRec_ok (m : ℕ) (ceq : Bool) (skip : ℕ → Bool) :
    ∀ (j : ℕ) (gs : List Gate) (acc : List Stat × List Gate),
      (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elimRec m ceq skip j gs acc).2, Ok g
  | _, [], acc, h => h
  | j, g :: gs, acc, h => by
    simp only [elimRec]
    apply elimRec_ok m ceq skip (j + 1) gs
    intro g' hg'
    unfold elimStep at hg'
    split at hg'
    · exact h g' hg'
    · simp only [List.mem_append, Option.mem_toList] at hg'
      rcases hg' with h1 | h2
      · exact h g' h1
      · exact simplify_ok ceq g.op _ _ g' h2

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

-- Exact drop counting: track emitted-count via recursive sum
def dropCount (m : ℕ) (ceq : Bool) (skip : ℕ → Bool) :
    ℕ → List Gate → List Stat × List Gate → ℕ
  | _, [], _ => 0
  | j, g :: gs, acc =>
    let acc' := elimStep m ceq skip acc (j, g)
    (if acc'.2.length = acc.2.length then 1 else 0) + dropCount m ceq skip (j + 1) gs acc'

theorem elimRec_len_add_drop (m : ℕ) (ceq : Bool) (skip : ℕ → Bool) :
    ∀ (j : ℕ) (gs : List Gate) (acc : List Stat × List Gate),
      (elimRec m ceq skip j gs acc).2.length + dropCount m ceq skip j gs acc =
        acc.2.length + gs.length
  | _, [], acc => by simp [elimRec, dropCount]
  | j, g :: gs, acc => by
    simp only [elimRec, dropCount, List.length_cons]
    have ih := elimRec_len_add_drop m ceq skip (j + 1) gs (elimStep m ceq skip acc (j, g))
    have hstep : (elimStep m ceq skip acc (j, g)).2.length = acc.2.length ∨
        (elimStep m ceq skip acc (j, g)).2.length = acc.2.length + 1 := by
      unfold elimStep
      split
      · exact Or.inl rfl
      · simp only [List.length_append]
        cases hopt : (simplify ceq g.op (m + acc.2.length)
          ((activeInputs g).map fun i => acc.1.getD i (Sum.inl false))).1 with
        | none => left; simp
        | some _ => right; simp
    rcases hstep with h0 | h1
    · simp only [h0, ite_true] at ih ⊢; omega
    · have hne : (elimStep m ceq skip acc (j, g)).2.length ≠ acc.2.length := by omega
      simp only [hne, ite_false] at ih ⊢; omega

-- Which gate indices were dropped (emitted 0 gates)
def isDropped (m : ℕ) (ceq : Bool) (skip : ℕ → Bool) (gs : List Gate)
    (init : List Stat × List Gate) (k : ℕ) : Prop :=
  (elimRec m ceq skip 0 (gs.take (k + 1)) init).2.length =
  (elimRec m ceq skip 0 (gs.take k) init).2.length

theorem elimRec_append (m : ℕ) (ceq : Bool) (skip : ℕ → Bool) :
    ∀ (j : ℕ) (pre post : List Gate) (acc : List Stat × List Gate),
      elimRec m ceq skip j (pre ++ post) acc =
        elimRec m ceq skip (j + pre.length) post (elimRec m ceq skip j pre acc)
  | j, [], post, acc => by simp [elimRec]
  | j, g :: pre, post, acc => by
    simp only [List.cons_append, elimRec, List.length_cons]
    rw [elimRec_append m ceq skip (j + 1) pre post]
    have hadd : j + 1 + pre.length = j + (pre.length + 1) := by omega
    rw [hadd]

theorem dropCount_append (m : ℕ) (ceq : Bool) (skip : ℕ → Bool) :
    ∀ (j : ℕ) (pre post : List Gate) (acc : List Stat × List Gate),
      dropCount m ceq skip j (pre ++ post) acc =
        dropCount m ceq skip j pre acc +
        dropCount m ceq skip (j + pre.length) post (elimRec m ceq skip j pre acc)
  | j, [], post, acc => by simp [dropCount, elimRec]
  | j, g :: pre, post, acc => by
    simp only [List.cons_append, dropCount, elimRec, List.length_cons]
    rw [dropCount_append m ceq skip (j + 1) pre post]
    have hadd : j + 1 + pre.length = j + (pre.length + 1) := by omega
    rw [hadd, Nat.add_assoc]

theorem dropCount_ge_card_dropped (m : ℕ) (ceq : Bool) (skip : ℕ → Bool)
    (gs : List Gate) (init : List Stat × List Gate)
    (S : Finset (Fin gs.length)) (hS : ∀ p ∈ S, isDropped m ceq skip gs init p.val) :
    S.card ≤ dropCount m ceq skip 0 gs init := by
  have key : ∀ (t : ℕ) (ht : t ≤ gs.length) (T : Finset (Fin gs.length)),
      (∀ p ∈ T, p.val < t) → (∀ p ∈ T, isDropped m ceq skip gs init p.val) →
      T.card ≤ dropCount m ceq skip 0 (gs.take t) init := by
    intro t
    induction t with
    | zero =>
      intro _ T hT _
      have hTe : T = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        have := hT p hp; omega
      simp [hTe]
    | succ t ih =>
      intro ht T hT hTd
      have htake : gs.take (t + 1) = gs.take t ++ [gs[t]'(by omega)] := List.take_succ_eq_append_getElem (by omega)
      rw [htake, dropCount_append]
      have hlen : (gs.take t).length = t := List.length_take_of_le (by omega)
      rw [zero_add, hlen]
      let p0 : Fin gs.length := ⟨t, by omega⟩
      by_cases hp0 : p0 ∈ T
      · have hT' : ∀ p ∈ T.erase p0, p.val < t := by
          intro p hp
          have hne : p ≠ p0 := (Finset.mem_erase.1 hp).1
          have hlt := hT p (Finset.mem_erase.1 hp).2
          have hne' : p.val ≠ t := fun h => hne (Fin.ext h)
          omega
        have h1 := ih (by omega) (T.erase p0) hT' (fun p hp => hTd p (Finset.mem_erase.1 hp).2)
        have hd0 : isDropped m ceq skip gs init t := hTd p0 hp0
        unfold isDropped at hd0
        rw [htake, elimRec_append, zero_add, hlen] at hd0
        simp only [elimRec] at hd0
        have h2 : dropCount m ceq skip t [gs[t]'(by omega)] (elimRec m ceq skip 0 (gs.take t) init) = 1 := by
          simp [dropCount, hd0]
        have hcard : T.card = (T.erase p0).card + 1 := (Finset.card_erase_add_one hp0).symm
        omega
      · have hT' : ∀ p ∈ T, p.val < t := by
          intro p hp
          have hlt := hT p hp
          have hne : p.val ≠ t := fun h => hp0 (by convert hp; exact Fin.ext h.symm)
          omega
        have h1 := ih (by omega) T hT' hTd
        omega
  have htake_all : gs.take gs.length = gs := List.take_length
  have hfinal := key gs.length le_rfl S (fun p _ => p.isLt) hS
  rwa [htake_all] at hfinal

theorem elimRec_step_at (m : ℕ) (ceq : Bool) (skip : ℕ → Bool)
    (gs : List Gate) (init : List Stat × List Gate) (k : ℕ) (hk : k < gs.length) :
    elimRec m ceq skip 0 (gs.take (k + 1)) init =
      elimStep m ceq skip (elimRec m ceq skip 0 (gs.take k) init) (k, gs[k]'hk) := by
  have htake : gs.take (k + 1) = gs.take k ++ [gs[k]'hk] := List.take_succ_eq_append_getElem hk
  rw [htake, elimRec_append, zero_add, List.length_take_of_le (by omega)]
  rfl

theorem elimRec_take_getD (m : ℕ) (ceq : Bool) (skip : ℕ → Bool)
    (gs : List Gate) (init : List Stat × List Gate) (k i : ℕ)
    (hi : i < init.1.length + (gs.take k).length) :
    (elimRec m ceq skip 0 gs init).1.getD i (Sum.inl false) =
      (elimRec m ceq skip 0 (gs.take k) init).1.getD i (Sum.inl false) := by
  have hsp : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
  conv_lhs => rw [hsp, elimRec_append]
  rw [elimRec_getD_lt _ _ _ _ _ _ i (by rw [elimRec_fst_length]; exact hi)]

theorem elimRec_len2_mono (m : ℕ) (ceq : Bool) (skip : ℕ → Bool) :
    ∀ (idx : ℕ) (l : List Gate) (ac : List Stat × List Gate),
      ac.2.length ≤ (elimRec m ceq skip idx l ac).2.length
  | _, [], _ => le_rfl
  | idx, g' :: l', ac =>
    (by unfold elimStep; split <;> simp : ac.2.length ≤ (elimStep m ceq skip ac (idx, g')).2.length).trans
      (elimRec_len2_mono m ceq skip (idx + 1) l' _)

theorem elimRec_take_len2_le (m : ℕ) (ceq : Bool) (skip : ℕ → Bool)
    (gs : List Gate) (init : List Stat × List Gate) (k : ℕ) :
    (elimRec m ceq skip 0 (gs.take k) init).2.length ≤
      (elimRec m ceq skip 0 gs init).2.length := by
  have hsp : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
  conv_rhs => rw [hsp, elimRec_append]
  exact elimRec_len2_mono m ceq skip _ _ _

theorem wiresFrom_take_getD (gs : List Gate) (x : List Bool) (k i : ℕ)
    (hi : i < x.length + (gs.take k).length) :
    (wiresFrom gs x).getD i false = (wiresFrom (gs.take k) x).getD i false := by
  have hsp : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
  conv_lhs => rw [hsp, wiresFrom_append]
  rw [getD_wiresFrom _ _ i (by rw [length_wiresFrom]; exact hi)]

-- Soundness invariant for elimRec vs evalModRec
def InvSkip (m : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧
    ∀ i, statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
      statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem invSkip_elimRec (m : ℕ) (ceq : Bool) (skip : ℕ → Bool)
    (y : List Bool) (hy : y.length = m) :
    ∀ (j : ℕ) (gs : List Gate) (w : List Bool) (acc : List Stat × List Gate),
      (∀ g ∈ gs, Ok g) → InvSkip m y w acc →
      InvSkip m y (evalModRec skip j gs w) (elimRec m ceq skip j gs acc)
  | _, [], w, acc, _, hinv => hinv
  | j, g :: gs, w, acc, hok, hinv => by
    simp only [evalModRec, elimRec]
    apply invSkip_elimRec m ceq skip y hy (j + 1) gs _ _
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    have hg := hok g List.mem_cons_self
    unfold elimStep
    by_cases hsk : skip j = true
    · simp only [hsk, ite_true]
      refine ⟨by simp [hinv.1], ?_⟩
      intro i
      rcases Nat.lt_trichotomy i w.length with hlt | heq | hgt
      · have hlt' : i < acc.1.length := hinv.1.symm ▸ hlt
        rw [List.getD_append _ _ _ _ hlt', List.getD_append _ _ _ _ hlt]
        exact hinv.2 i
      · subst heq
        rw [getD_snoc_len acc.1 _ _ _ hinv.1, getD_snoc_eq]
        exact ⟨trivial, rfl⟩
      · rw [List.getD_eq_default _ _ (by simp [hinv.1]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
        exact ⟨trivial, rfl⟩
    · simp only [hsk, Bool.false_eq_true, ↓reduceIte]
      set W := wiresFrom acc.2 y with hW
      have hWlen : W.length = m + acc.2.length := by rw [hW, length_wiresFrom, hy]
      set ins := (activeInputs g).map fun i => acc.1.getD i (Sum.inl false) with hins
      have hlen_ins : ins.length ≤ 2 := by
        rw [hins, List.length_map]
        exact (activeInputs_length_le g).trans hg.2
      have hss := simplify_sound ceq g.op (ok_op g hg) W ins hlen_ins (by
        intro s hs
        obtain ⟨i, _, rfl⟩ := List.mem_map.1 hs
        rw [hWlen]; exact (hinv.2 i).1)
      set res := simplify ceq g.op (m + acc.2.length) ins with hres
      have hres_eq : simplify ceq g.op W.length ins = res := by rw [hWlen]
      rw [hres_eq] at hss
      have heval : g.op.eval (ins.map (statVal W)) =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        have h1 : ins.map (statVal W) = (activeInputs g).map fun i => w.getD i false := by
          simp only [hins, List.map_map]
          apply List.map_congr_left
          intro i _; exact (hinv.2 i).2
        rw [h1, gateEval_active]
      have hW' : wiresFrom (acc.2 ++ res.1.toList) y = wiresFrom res.1.toList W :=
        wiresFrom_append acc.2 res.1.toList y
      refine ⟨by simp [hinv.1], ?_⟩
      intro i
      rcases Nat.lt_trichotomy i w.length with hlt | heq | hgt
      · have hlt' : i < acc.1.length := hinv.1.symm ▸ hlt
        rw [List.getD_append _ _ _ _ hlt', List.getD_append _ _ _ _ hlt, hW']
        have hv_old := (hinv.2 i).1
        refine ⟨statValid_mono (by simp) _ hv_old, ?_⟩
        cases hs : acc.1.getD i (Sum.inl false) with
        | inl c =>
          have := (hinv.2 i).2; rw [hs] at this; exact this
        | inr k =>
          have hk : k < W.length := by rw [hWlen]; rw [hs] at hv_old; exact hv_old
          have hget := getD_wiresFrom res.1.toList W k hk
          have := (hinv.2 i).2; rw [hs] at this; exact hget.trans this
      · subst heq
        rw [getD_snoc_len acc.1 res.2 _ _ hinv.1, getD_snoc_eq, hW', ← heval]
        refine ⟨?_, hss.2⟩
        have h1' : W.length + res.1.toList.length = m + (acc.2 ++ res.1.toList).length := by
          simp [hWlen]; omega
        rw [← h1']; exact hss.1
      · rw [List.getD_eq_default _ _ (by simp [hinv.1]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
        exact ⟨trivial, rfl⟩

def idStats (m : ℕ) : List Stat := List.ofFn (fun i : Fin m => Sum.inr i.val)

theorem invSkip_id (m : ℕ) (y : Fin m → Bool) :
    InvSkip m (List.ofFn y) (List.ofFn y) (idStats m, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < m
  · simp [idStats, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

-- Cleanliness of minimal circuits for non-constant functions
def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ a, g.inputs.head? = some a ∧ a < m) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < m ∧ b < m)

theorem cleanGate_active_lt {m : ℕ} {g : Gate} (h : CleanGate m g) :
    ∀ a ∈ activeInputs g, a < m := by
  intro a ha
  unfold activeInputs at ha
  rcases h with ⟨hop, b, hb, hbm⟩ | ⟨hop, b, c, hin, _, hbm, hcm⟩
  · simp only [hop] at ha
    cases hin : g.inputs with
    | nil => simp [hin] at hb
    | cons x l =>
      simp [hin] at hb ha; subst hb; subst ha; exact hbm
  · rcases hop with hop | hop <;>
    · simp only [hop, hin, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl; exact hbm; exact hcm

theorem min_clean {m : ℕ} {C : Circuit} (hmin : IsMinimalCircuit m C)
    (hnc : ∃ y y' : Fin m → Bool, circuitFun m C y ≠ circuitFun m C y') :
    ∀ j : Fin C.gates.length, CleanGate (m + j.val) (C.gates.get j) := by
  intro j
  by_contra hnot
  set skip : ℕ → Bool := fun _ => false
  set init : List Stat × List Gate := (idStats m, [])
  set res := elimRec m true skip 0 C.gates init with hres
  have hok : ∀ g ∈ C.gates, Ok g := hmin.1
  -- Show gate j is dropped in elimRec m true skip 0 C.gates init!
  -- First, note if ANY gate k < j was already dropped, then dropCount >= 1.
  -- If NO gate k < j was dropped, then at step j every wire i < m + j maps to Sum.inr i!
  have hdrop_pos : 1 ≤ dropCount m true skip 0 C.gates init := by
    by_cases hearly : 1 ≤ dropCount m true skip 0 (C.gates.take j.val) init
    · have hsplit : C.gates = C.gates.take j.val ++ C.gates.drop j.val := (List.take_append_drop j.val C.gates).symm
      rw [hsplit, dropCount_append]; omega
    · -- No gate before j was dropped! So acc_j.2.length = j.val and every i < m + j maps to Sum.inr i!
      have hzero : dropCount m true skip 0 (C.gates.take j.val) init = 0 := by omega
      have hlen_pre : (elimRec m true skip 0 (C.gates.take j.val) init).2.length = j.val := by
        have h1 := elimRec_len_add_drop m true skip 0 (C.gates.take j.val) init
        rw [hzero, add_zero, List.length_take_of_le (by omega)] at h1
        simpa [init] using h1
      -- Prove by induction on t <= j.val that every wire i < m + t maps to Sum.inr i
      have hall_id : ∀ t ≤ j.val,
          dropCount m true skip 0 (C.gates.take t) init = 0 →
          ∀ i < m + t, (elimRec m true skip 0 (C.gates.take t) init).1.getD i (Sum.inl false) = Sum.inr i := by
        intro t
        induction t with
        | zero =>
          intro _ _ i hi
          have him : i < m := by omega
          simp [elimRec, init, idStats, him]
        | succ t ih =>
          intro ht hdz i hi
          have htk : C.gates.take (t + 1) = C.gates.take t ++ [C.gates[t]'(by omega)] :=
            List.take_succ_eq_append_getElem (by omega)
          rw [htk, dropCount_append] at hdz
          have hdz1 : dropCount m true skip 0 (C.gates.take t) init = 0 := by omega
          have hdz2 : dropCount m true skip (0 + (C.gates.take t).length)
              [C.gates[t]'(by omega)] (elimRec m true skip 0 (C.gates.take t) init) = 0 := by omega
          have hlt_t : (C.gates.take t).length = t := List.length_take_of_le (by omega)
          have hacc_len : (elimRec m true skip 0 (C.gates.take t) init).1.length = m + t := by
            rw [elimRec_fst_length]; simp [init, idStats, hlt_t]
          have hacc2_len : (elimRec m true skip 0 (C.gates.take t) init).2.length = t := by
            have h1 := elimRec_len_add_drop m true skip 0 (C.gates.take t) init
            rw [hdz1, add_zero, hlt_t] at h1; simpa [init] using h1
          rw [elimRec_step_at m true skip C.gates init t (by omega)]
          by_cases hit : i < m + t
          · unfold elimStep
            simp only [skip, Bool.false_eq_true, ↓reduceIte]
            rw [List.getD_append _ _ _ _ (by rw [show (elimRec m true (fun _ => false) 0 (C.gates.take t) init).1.length = m + t from hacc_len]; exact hit)]
            exact ih (by omega) hdz1 i hit
          · have hi_eq : i = m + t := by omega
            subst hi_eq
            unfold elimStep
            simp only [skip, Bool.false_eq_true, ↓reduceIte]
            rw [getD_snoc_len _ _ _ _ hacc_len]
            -- Since dropCount at t is 0, simplify returned some gate, so .2 = Sum.inr (m + t)!
            simp only [dropCount, zero_add, hlt_t, add_zero] at hdz2
            have hne_len : (elimStep m true skip (elimRec m true skip 0 (C.gates.take t) init)
                (t, C.gates[t]'(by omega))).2.length ≠
                (elimRec m true skip 0 (C.gates.take t) init).2.length := by
              intro heq; simp [heq] at hdz2
            unfold elimStep at hne_len
            simp only [skip, Bool.false_eq_true, ↓reduceIte, List.length_append] at hne_len
            set g_t := C.gates[t]'(by omega)
            set ins_t := (activeInputs g_t).map fun r =>
              (elimRec m true skip 0 (C.gates.take t) init).1.getD r (Sum.inl false)
            have hsome : (simplify true g_t.op (m + (elimRec m true skip 0 (C.gates.take t) init).2.length) ins_t).1 ≠ none := by
              intro hn; rw [hn] at hne_len; simp at hne_len
            have hres_inr : (simplify true g_t.op (m + (elimRec m true skip 0 (C.gates.take t) init).2.length) ins_t).2 =
                Sum.inr (m + (elimRec m true skip 0 (C.gates.take t) init).2.length) := by
              cases hop_t : g_t.op <;> simp only [simplify, hop_t] at hsome ⊢
              · rcases ins_t with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
                  simp [simpAnd] at hsome ⊢
                · split at hsome <;> simp_all
              · rcases ins_t with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
                  simp [simpOr] at hsome ⊢
                · split at hsome <;> simp_all
              · rcases ins_t with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hsome ⊢
              · simp at hsome
              · simp at hsome
            rw [hres_inr, hacc2_len]
      have hid_j := hall_id j.val le_rfl hzero
      have hacc1_len : (elimRec m true skip 0 (C.gates.take j.val) init).1.length = m + j.val := by
        rw [elimRec_fst_length]; simp [init, idStats, List.length_take_of_le j.isLt.le]
      have hget_out : ∀ r, m + j.val ≤ r →
          (elimRec m true skip 0 (C.gates.take j.val) init).1.getD r (Sum.inl false) = Sum.inl false := by
        intro r hr
        exact List.getD_eq_default _ _ (by omega)
      -- Now show gate j is dropped because ¬ CleanGate (m + j.val) (C.gates.get j)!
      have hdrop_j : isDropped m true skip C.gates init j.val := by
        unfold isDropped
        rw [elimRec_step_at m true skip C.gates init j.val j.isLt]
        unfold elimStep
        simp only [skip, Bool.false_eq_true, ↓reduceIte, List.length_append]
        have hgj : C.gates[j.val]'j.isLt = C.gates.get j := rfl
        rw [hgj]
        set g := C.gates.get j
        have hokg : Ok g := hok g (List.get_mem _ _)
        set ins := (activeInputs g).map fun r =>
          (elimRec m true skip 0 (C.gates.take j.val) init).1.getD r (Sum.inl false)
        suffices hnone : (simplify true g.op (m + (elimRec m true skip 0 (C.gates.take j.val) init).2.length) ins).1 = none by
          rw [hnone]; simp
        rcases ok_op g hokg with hop | hop | hop
        · have hact : activeInputs g = g.inputs := by simp [activeInputs, hop]
          simp only [simplify, hop, ins, hact]
          rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
          · simp [simpAnd]
          · simp only [List.map_cons, List.map_nil]
            cases (elimRec m true skip 0 (C.gates.take j.val) init).1.getD a (Sum.inl false) <;> simp [simpAnd]
          · simp only [List.map_cons, List.map_nil]
            by_cases ha : a < m + j.val
            · by_cases hb : b < m + j.val
              · have hab : a = b := by
                  by_contra hne
                  exact hnot (Or.inr ⟨Or.inl hop, a, b, hin, hne, ha, hb⟩)
                subst hab
                rw [hid_j a ha]; simp [simpAnd]
              · rw [hid_j a ha, hget_out b (by omega)]; simp [simpAnd]
            · rw [hget_out a (by omega)]
              cases (elimRec m true skip 0 (C.gates.take j.val) init).1.getD b (Sum.inl false) <;> simp [simpAnd]
          · have hle := hokg.2; rw [hin] at hle; simp at hle
        · have hact : activeInputs g = g.inputs := by simp [activeInputs, hop]
          simp only [simplify, hop, ins, hact]
          rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
          · simp [simpOr]
          · simp only [List.map_cons, List.map_nil]
            cases (elimRec m true skip 0 (C.gates.take j.val) init).1.getD a (Sum.inl false) <;> simp [simpOr]
          · simp only [List.map_cons, List.map_nil]
            by_cases ha : a < m + j.val
            · by_cases hb : b < m + j.val
              · have hab : a = b := by
                  by_contra hne
                  exact hnot (Or.inr ⟨Or.inr hop, a, b, hin, hne, ha, hb⟩)
                subst hab
                rw [hid_j a ha]; simp [simpOr]
              · rw [hid_j a ha, hget_out b (by omega)]; simp [simpOr]
            · rw [hget_out a (by omega)]
              cases (elimRec m true skip 0 (C.gates.take j.val) init).1.getD b (Sum.inl false) <;> simp [simpOr]
          · have hle := hokg.2; rw [hin] at hle; simp at hle
        · have hact : activeInputs g = g.inputs.take 1 := by simp [activeInputs, hop]
          simp only [simplify, hop, ins, hact]
          cases hin : g.inputs with
          | nil => simp [simpNot]
          | cons a l =>
            have hge : m + j.val ≤ a := by
              by_contra hlt
              exact hnot (Or.inl ⟨hop, a, by simp [hin], by omega⟩)
            simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil]
            rw [hget_out a hge]; simp [simpNot]
      have hcard := dropCount_ge_card_dropped m true skip C.gates init {j} (by simp [hdrop_j])
      simpa using hcard
  have hlen_lt : res.2.length < C.gates.length := by
    have h1 := elimRec_len_add_drop m true skip 0 C.gates init
    rw [← hres] at h1
    have hinit2 : init.2.length = 0 := rfl
    rw [hinit2, zero_add] at h1
    omega
  have hinv : ∀ y : Fin m → Bool, InvSkip m (List.ofFn y) (C.wires (List.ofFn y)) res := by
    intro y
    have h := invSkip_elimRec m true skip (List.ofFn y) (by simp) 0 C.gates (List.ofFn y) init hok (invSkip_id m y)
    rwa [evalModRec_false_eq_wiresFrom] at h
  cases hst : res.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have hy := (hinv y).2 C.output
    have hy' := (hinv y').2 C.output
    rw [hst] at hy hy'
    exact hy.2.symm.trans hy'.2
  | inr out' =>
    let D : Circuit := ⟨res.2, out'⟩
    have hDfit : FanInTwo D := elimRec_ok m true skip 0 C.gates init (by simp [init])
    have hDeq : circuitFun m D = circuitFun m C := by
      funext y
      have hy := ((hinv y).2 C.output).2
      rw [hst] at hy
      exact hy
    have hle := hmin.2 D hDfit hDeq
    change C.gates.length ≤ res.2.length at hle
    omega

-- Delete a dead gate from a minimal circuit
def shiftWire (K a : ℕ) : ℕ := if a < K then a else a - 1

def normShiftGate (K : ℕ) (g : Gate) : Gate :=
  ⟨g.op, (activeInputs g).map (shiftWire K)⟩

def RelD (K : ℕ) (W W' : List Bool) : Prop :=
  W.length = W'.length + 1 ∧ K ≤ W'.length ∧
    ∀ a, a ≠ K → W'.getD (shiftWire K a) false = W.getD a false

theorem relD_wires (K : ℕ) (post : List Gate) : ∀ W W' : List Bool,
    (∀ g ∈ post, K ∉ activeInputs g) → RelD K W W' →
    RelD K (wiresFrom post W) (wiresFrom (post.map (normShiftGate K)) W') := by
  induction post with
  | nil => intro W W' _ h; exact h
  | cons g post ih =>
    intro W W' hno h
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (normShiftGate K g).op.eval ((normShiftGate K g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [normShiftGate, List.map_map]
      rw [← gateEval_active g]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun e => hno g List.mem_cons_self (e ▸ ha))
    have s1 : wiresFrom (g :: post) W
        = wiresFrom post (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl
    have s2 : wiresFrom ((g :: post).map (normShiftGate K)) W'
        = wiresFrom (post.map (normShiftGate K))
          (W' ++ [(normShiftGate K g).op.eval ((normShiftGate K g).inputs.map fun i => W'.getD i false)]) := rfl
    rw [s1, s2, hv]
    apply ih _ _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    intro a haK
    rcases Nat.lt_trichotomy a W.length with hw | hw | hw
    · have hlt : shiftWire K a < W'.length := by unfold shiftWire; split <;> omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 a haK
    · have he : shiftWire K a = W'.length := by unfold shiftWire; split <;> omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ shiftWire K a := by unfold shiftWire; split <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem split_at_fin {α : Type} (l : List α) (j : Fin l.length) :
    ∃ pre post, l = pre ++ l.get j :: post ∧ pre.length = j.val := by
  refine ⟨l.take j.val, l.drop (j.val + 1), ?_, List.length_take_of_le (by omega)⟩
  have h1 := List.take_append_drop j.val l
  have h2 : l.drop j.val = l.get j :: l.drop (j.val + 1) := List.drop_eq_getElem_cons j.isLt
  rw [h2] at h1
  exact h1.symm

theorem min_used {m : ℕ} {C : Circuit} (hmin : IsMinimalCircuit m C)
    (j : Fin C.gates.length) :
    C.output = m + j.val ∨ ∃ j' : Fin C.gates.length, Reads C j' (m + j.val) := by
  by_contra hno
  push Not at hno
  obtain ⟨ho, hnr⟩ := hno
  obtain ⟨pre, post, hsplit, hplen⟩ := split_at_fin C.gates j
  let K := m + j.val
  let D : Circuit := ⟨pre ++ post.map (normShiftGate K), shiftWire K C.output⟩
  have hDfit : FanInTwo D := by
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h2
    · exact hmin.1 g' (by rw [hsplit]; exact List.mem_append_left _ h1)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h2
      have hok0 := hmin.1 g0 (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨hok0.1, by simp only [normShiftGate, List.length_map]; exact (activeInputs_length_le g0).trans hok0.2⟩
  have hno_post : ∀ g' ∈ post, K ∉ activeInputs g' := by
    intro g' hg'
    obtain ⟨q, hq_lt, hq_eq⟩ := List.mem_iff_getElem.1 hg'
    have hidx : pre.length + 1 + q < C.gates.length := by
      have hl : C.gates.length = pre.length + 1 + post.length := by rw [hsplit]; simp; omega
      omega
    let j' : Fin C.gates.length := ⟨pre.length + 1 + q, hidx⟩
    have hgj' : C.gates.get j' = g' := by
      show C.gates[pre.length + 1 + q]'hidx = g'
      have h1 : (pre ++ C.gates.get j :: post)[pre.length + 1 + q]'(by rw [← hsplit]; exact hidx) = g' := by
        rw [List.getElem_append_right (by omega)]
        have he : pre.length + 1 + q - pre.length = q + 1 := by omega
        simp only [he, List.getElem_cons_succ, hq_eq]
      have hcongr : ∀ (l₁ l₂ : List Gate) (h : l₁ = l₂) (k : ℕ) (h₁ : k < l₁.length) (h₂ : k < l₂.length),
          l₁[k]'h₁ = l₂[k]'h₂ := by rintro _ _ rfl _ _ _; rfl
      exact (hcongr _ _ hsplit _ hidx _).trans h1
    intro hmem
    rw [← hgj', mem_activeInputs_iff] at hmem
    exact hnr j' hmem
  have hDeq : circuitFun m D = circuitFun m C := by
    funext x
    change (wiresFrom (pre ++ post.map (normShiftGate K)) (List.ofFn x)).getD (shiftWire K C.output) false =
      (wiresFrom C.gates (List.ofFn x)).getD C.output false
    have hCeq : wiresFrom C.gates (List.ofFn x) =
        wiresFrom post (wiresFrom pre (List.ofFn x) ++
          [(C.gates.get j).op.eval ((C.gates.get j).inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
      have hW : wiresFrom C.gates (List.ofFn x) = wiresFrom (pre ++ C.gates.get j :: post) (List.ofFn x) :=
        congrArg (fun gs => wiresFrom gs (List.ofFn x)) hsplit
      rw [hW, wiresFrom_append]; rfl
    rw [hCeq, wiresFrom_append]
    have hlen_pre : (wiresFrom pre (List.ofFn x)).length = K := by
      rw [length_wiresFrom]; simp [hplen, K]
    refine (relD_wires K post _ _ hno_post ⟨by simp, by omega, ?_⟩).2.2 C.output ho
    intro a ha
    by_cases hlt : a < K
    · have : shiftWire K a = a := by simp [shiftWire, hlt]
      rw [this, List.getD_append _ _ _ _ (by omega)]
    · have : shiftWire K a = a - 1 := by simp [shiftWire, hlt]
      rw [this, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
  have hle := hmin.2 D hDfit hDeq
  have hlenC : C.gates.length = pre.length + 1 + post.length := by
    rw [hsplit]; simp; omega
  have hlenD : D.size = pre.length + post.length := by simp [D, Circuit.size]
  change C.gates.length ≤ D.size at hle
  omega

theorem min_out_lt {m : ℕ} {C : Circuit}
    (hnc : ∃ y y' : Fin m → Bool, circuitFun m C y ≠ circuitFun m C y') :
    C.output < m + C.gates.length := by
  by_contra hge
  obtain ⟨y, y', hne⟩ := hnc
  apply hne
  change (wiresFrom C.gates (List.ofFn y)).getD C.output false =
    (wiresFrom C.gates (List.ofFn y')).getD C.output false
  rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
    List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)]

theorem min_out_last {m : ℕ} {C : Circuit} (hmin : IsMinimalCircuit m C)
    (hnc : ∃ y y' : Fin m → Bool, circuitFun m C y ≠ circuitFun m C y')
    (j : Fin C.gates.length) (ho : C.output = m + j.val) :
    j.val + 1 = C.gates.length := by
  by_contra hne
  have hcl := min_clean hmin hnc
  let last : Fin C.gates.length := ⟨C.gates.length - 1, by omega⟩
  have hlast_ne : C.output ≠ m + last.val := by rw [ho]; simp [last]; omega
  rcases min_used hmin last with h | ⟨j', hj'⟩
  · exact hlast_ne h
  · have hlt := cleanGate_active_lt (hcl j') (m + last.val) ((mem_activeInputs_iff C j' _).2 hj')
    simp [last] at hlt
    omega

-- Helper: Fin.snoc on Fin (n + 1) → Bool
def withLast {n : ℕ} (y : Fin n → Bool) (b : Bool) : Fin (n + 1) → Bool :=
  Fin.snoc y b

theorem withLast_castSucc {n : ℕ} (y : Fin n → Bool) (b : Bool) (i : Fin n) :
    withLast y b i.castSucc = y i := by
  simp [withLast]

theorem withLast_last {n : ℕ} (y : Fin n → Bool) (b : Bool) :
    withLast y b (Fin.last n) = b := by
  simp [withLast]

theorem eq_withLast {n : ℕ} (x : Fin (n + 1) → Bool) :
    x = withLast (fun i : Fin n => x i.castSucc) (x (Fin.last n)) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [withLast]
  · intro j; simp [withLast]

theorem getD_ofFn_withLast {n : ℕ} (y : Fin n → Bool) (b : Bool) (i : ℕ) :
    (List.ofFn (withLast y b)).getD i false =
      if h : i < n then y ⟨i, h⟩ else if i = n then b else false := by
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
    simp only [hi, dite_true]
    exact withLast_castSucc y b ⟨i, hi⟩
  · by_cases hEq : i = n
    · subst hEq
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      simp only [lt_irrefl, dite_false, ite_true]
      exact withLast_last y b
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp [hi, hEq]

-- Wire value helper for C
def wireVal {m : ℕ} (C : Circuit) (x : Fin m → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

theorem wireVal_gate {m : ℕ} (C : Circuit) (x : Fin m → Bool) (j : Fin C.gates.length) :
    wireVal C x (m + j.val) =
      (C.gates.get j).op.eval ((C.gates.get j).inputs.map fun i =>
        if i < m + j.val then wireVal C x i else false) := by
  obtain ⟨pre, post, hsplit, hplen⟩ := split_at_fin C.gates j
  unfold wireVal
  have hW : wiresFrom C.gates (List.ofFn x) = wiresFrom (pre ++ C.gates.get j :: post) (List.ofFn x) :=
    congrArg (fun gs => wiresFrom gs (List.ofFn x)) hsplit
  rw [wires_eq, hW, wiresFrom_append]
  have h1 : wiresFrom (C.gates.get j :: post) (wiresFrom pre (List.ofFn x)) =
      wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [(C.gates.get j).op.eval ((C.gates.get j).inputs.map fun i =>
          (wiresFrom pre (List.ofFn x)).getD i false)]) := rfl
  have hlen : (wiresFrom pre (List.ofFn x)).length = m + j.val := by
    rw [length_wiresFrom]; simp [hplen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hlen]), getD_snoc_len _ _ _ _ hlen]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < m + j.val
  · simp only [hi, ite_true]
    rw [getD_wiresFrom post _ i (by simp [hlen]; omega), List.getD_append _ _ _ _ (by omega)]
  · simp only [hi, ite_false]
    exact List.getD_eq_default _ _ (by omega)

theorem wireVal_gate_clean {m : ℕ} (C : Circuit) (hcl : ∀ j : Fin C.gates.length, CleanGate (m + j.val) (C.gates.get j))
    (x : Fin m → Bool) (j : Fin C.gates.length) :
    wireVal C x (m + j.val) =
      (C.gates.get j).op.eval ((activeInputs (C.gates.get j)).map (wireVal C x)) := by
  rw [wireVal_gate, ← gateEval_active]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt := cleanGate_active_lt (hcl j) i hi
  simp [hlt]

theorem evalModRec_gate {m : ℕ} (C : Circuit) (hcl : ∀ j : Fin C.gates.length, CleanGate (m + j.val) (C.gates.get j))
    (skip : ℕ → Bool) (x : Fin m → Bool) (j : Fin C.gates.length) :
    (evalModRec skip 0 C.gates (List.ofFn x)).getD (m + j.val) false =
      if skip j.val then false
      else (C.gates.get j).op.eval ((activeInputs (C.gates.get j)).map fun i =>
        (evalModRec skip 0 C.gates (List.ofFn x)).getD i false) := by
  obtain ⟨pre, post, hsplit, hplen⟩ := split_at_fin C.gates j
  have hrec_app : ∀ (k : ℕ) (p q : List Gate) (w : List Bool),
      evalModRec skip k (p ++ q) w = evalModRec skip (k + p.length) q (evalModRec skip k p w) := by
    intro k p
    induction p generalizing k with
    | nil => intro q w; simp [evalModRec]
    | cons g p ih =>
      intro q w
      simp only [List.cons_append, evalModRec, List.length_cons]
      rw [ih (k + 1) q]
      have : k + 1 + p.length = k + (p.length + 1) := by omega
      rw [this]
  have hE : evalModRec skip 0 C.gates (List.ofFn x) =
      evalModRec skip 0 (pre ++ C.gates.get j :: post) (List.ofFn x) :=
    congrArg (fun gs => evalModRec skip 0 gs (List.ofFn x)) hsplit
  conv_lhs => rw [hE, hrec_app, zero_add, hplen]
  have hlen : (evalModRec skip 0 pre (List.ofFn x)).length = m + j.val := by
    rw [evalModRec_length]; simp [hplen]
  simp only [evalModRec]
  rw [evalModRec_getD_lt skip (j.val + 1) post _ (m + j.val) (by simp [hlen]),
    getD_snoc_len _ _ _ _ hlen]
  split
  · rfl
  · rw [← gateEval_active]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hlt := cleanGate_active_lt (hcl j) i hi
    conv_rhs => rw [hE, hrec_app, zero_add, hplen]
    simp only [evalModRec]
    rw [evalModRec_getD_lt skip (j.val + 1) post _ i (by simp [hlen]; omega),
      List.getD_append _ _ _ _ (by omega)]

-- Chain invariant for an initial list of OR gates cs
def frontWire (n : ℕ) (cs : List (Fin k)) : ℕ :=
  match cs.getLast? with
  | none => n
  | some last => n + 1 + last.val

def inStrictInit (n : ℕ) {k : ℕ} (cs : List (Fin k)) (w : ℕ) : Prop :=
  match cs.getLast? with
  | none => False
  | some last => w = n ∨ ∃ j ∈ cs, j ≠ last ∧ w = n + 1 + j.val

def skipOf {k : ℕ} (cs : List (Fin k)) (j : ℕ) : Bool :=
  cs.any fun p => p.val == j

theorem skipOf_iff {k : ℕ} (cs : List (Fin k)) (j : ℕ) :
    skipOf cs j = true ↔ ∃ p ∈ cs, p.val = j := by
  simp [skipOf]

def GoodChain (n : ℕ) (C : Circuit) (cs : List (Fin C.gates.length)) : Prop :=
  cs.Pairwise (· < ·) ∧
  (∀ j ∈ cs, (C.gates.get j).op = GateOp.or ∧ (C.gates.get j).inputs.length = 2) ∧
  (∀ (i : ℕ) (hi : i < cs.length),
    let prev := if h0 : i = 0 then n else n + 1 + (cs[i - 1]'(by omega)).val
    prev ∈ (C.gates.get (cs[i]'hi)).inputs ∧
    (∀ j : Fin C.gates.length, Reads C j prev → j = cs[i]'hi) ∧
    (∃ w ∈ (C.gates.get (cs[i]'hi)).inputs, w ≠ prev ∧ w ≠ n ∧ w < n + 1 + (cs[i]'hi).val ∧ ¬ Reach C (n + 1) n w))

-- Reachability from n up to a bound: every reachable gate <= frontWire is in cs!
theorem reach_implies_lt {m : ℕ} {C : Circuit}
    (hcl : ∀ j : Fin C.gates.length, CleanGate (m + j.val) (C.gates.get j))
    {a b : ℕ} (h : Edge C m a b) : a < b := by
  obtain ⟨j, rfl, hr⟩ := h
  exact cleanGate_active_lt (hcl j) a ((mem_activeInputs_iff C j a).2 hr)

theorem reach_trans_lt {m : ℕ} {C : Circuit}
    (hcl : ∀ j : Fin C.gates.length, CleanGate (m + j.val) (C.gates.get j))
    {a b : ℕ} (h : Reach C m a b) : a < b := by
  induction h with
  | single e => exact reach_implies_lt hcl e
  | tail _ e ih => exact Nat.lt_trans ih (reach_implies_lt hcl e)

theorem reach_of_goodChain {n : ℕ} {C : Circuit} {cs : List (Fin C.gates.length)}
    (hcl : ∀ j : Fin C.gates.length, CleanGate (n + 1 + j.val) (C.gates.get j))
    (hgc : GoodChain n C cs) :
    ∀ w, Reach C (n + 1) n w →
      (∃ j ∈ cs, w = n + 1 + j.val) ∨ Reach C (n + 1) (frontWire n cs) w := by
  intro w hr
  induction hr with
  | single e =>
    cases hcs : cs with
    | nil =>
      right
      simpa [Reach, frontWire, hcs] using Relation.TransGen.single e
    | cons c0 rest =>
      left
      obtain ⟨j, rfl, hread⟩ := e
      have huniq := (hgc.2.2 0 (by simp [hcs])).2.1
      simp only [dite_true] at huniq
      have hj := huniq j hread
      refine ⟨c0, by simp, ?_⟩
      simpa [hcs] using congrArg (fun p : Fin C.gates.length => n + 1 + p.val) hj
  | @tail b c _ e ih =>
    rcases ih with ⟨j, hj, rfl⟩ | hfr
    · obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.1 hj
      by_cases hlast : idx + 1 < cs.length
      · left
        obtain ⟨j', rfl, hread⟩ := e
        have huniq := (hgc.2.2 (idx + 1) hlast).2.1
        have hne0 : idx + 1 ≠ 0 := by omega
        simp only [hne0, dite_false, Nat.add_sub_cancel] at huniq
        have hj' := huniq j' hread
        exact ⟨cs[idx + 1]'hlast, List.getElem_mem hlast, congrArg (fun p : Fin C.gates.length => n + 1 + p.val) hj'⟩
      · right
        have heq_last : cs.getLast? = some (cs[idx]'hidx) := by
          rw [List.getLast?_eq_getElem?]
          have hlen : cs.length - 1 = idx := by omega
          rw [hlen, List.getElem?_eq_getElem hidx]
        have hfw : frontWire n cs = n + 1 + (cs[idx]'hidx).val := by simp [frontWire, heq_last]
        rw [hfw]
        exact Relation.TransGen.single e
    · right
      exact Relation.TransGen.tail hfr e

theorem pairwise_le_last {k : ℕ} {cs : List (Fin k)} (hpw : cs.Pairwise (· < ·))
    {last : Fin k} (hlast : cs.getLast? = some last) :
    ∀ p ∈ cs, p ≤ last := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
  have hlen : 0 < cs.length := by omega
  have hlast_eq : cs[cs.length - 1]'(by omega) = last := by
    rw [List.getLast?_eq_getElem?] at hlast
    rw [List.getElem?_eq_getElem (by omega)] at hlast
    exact Option.some.inj hlast
  by_cases he : i = cs.length - 1
  · subst he; rw [hlast_eq]
  · have hlt : cs[i]'hi < cs[cs.length - 1]'(by omega) :=
      List.pairwise_iff_getElem.1 hpw i (cs.length - 1) hi (by omega) (by omega)
    rw [hlast_eq] at hlt
    exact le_of_lt hlt

theorem frontWire_ge_mem (n : ℕ) {k : ℕ} {cs : List (Fin k)} (hpw : cs.Pairwise (· < ·)) :
    ∀ p ∈ cs, n + 1 + p.val ≤ frontWire n cs := by
  intro p hp
  cases hlast : cs.getLast? with
  | none =>
    have hnil : cs = [] := List.getLast?_eq_none_iff.1 hlast
    subst hnil; simp at hp
  | some last =>
    simp only [frontWire, hlast]
    have hle : p ≤ last := pairwise_le_last hpw hlast p hp
    exact Nat.add_le_add_left hle (n + 1)

theorem not_reach_of_lt_front {n : ℕ} {C : Circuit} {cs : List (Fin C.gates.length)}
    (hcl : ∀ j : Fin C.gates.length, CleanGate (n + 1 + j.val) (C.gates.get j))
    (hgc : GoodChain n C cs) (j_new : Fin C.gates.length)
    (hread_front : Reads C j_new (frontWire n cs))
    (huniq_front : ∀ j : Fin C.gates.length, Reads C j (frontWire n cs) → j = j_new)
    (w : ℕ) (hw_lt : w < n + 1 + j_new.val) (hw_ne_f : w ≠ frontWire n cs)
    (hread_new : Reads C j_new w) :
    w ≠ n ∧ ¬ Reach C (n + 1) n w := by
  have hfw_lt : frontWire n cs < n + 1 + j_new.val :=
    reach_implies_lt hcl ⟨j_new, rfl, hread_front⟩
  have hj_notin : j_new ∉ cs := by
    intro hmem
    have hle := frontWire_ge_mem n hgc.1 j_new hmem
    omega
  have hne_n : w ≠ n := by
    intro hwn
    subst hwn
    cases hcs : cs with
    | nil => exact hw_ne_f (by simp [frontWire, hcs])
    | cons c0 rest =>
      have huniq0 := (hgc.2.2 0 (by simp [hcs])).2.1
      simp only [dite_true] at huniq0
      have hj0 := huniq0 j_new hread_new
      have hc0_mem : cs[0]'(by simp [hcs]) ∈ cs := List.getElem_mem _
      rw [← hj0] at hc0_mem
      exact hj_notin hc0_mem
  refine ⟨hne_n, ?_⟩
  intro hr
  rcases reach_of_goodChain hcl hgc w hr with ⟨p, hp, rfl⟩ | hfr
  · obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.1 hp
    by_cases hlast : idx + 1 < cs.length
    · have huniq := (hgc.2.2 (idx + 1) hlast).2.1
      have hne0 : idx + 1 ≠ 0 := by omega
      simp only [hne0, dite_false, Nat.add_sub_cancel] at huniq
      have hj := huniq j_new hread_new
      have hmem : cs[idx + 1]'hlast ∈ cs := List.getElem_mem hlast
      rw [← hj] at hmem
      exact hj_notin hmem
    · have heq_last : cs.getLast? = some (cs[idx]'hidx) := by
        rw [List.getLast?_eq_getElem?]
        have hlen : cs.length - 1 = idx := by omega
        rw [hlen, List.getElem?_eq_getElem hidx]
      exact hw_ne_f (by simp [frontWire, heq_last])
  · rcases Relation.TransGen.head'_iff.1 hfr with ⟨b, he, hrest⟩
    obtain ⟨j', rfl, hr'⟩ := he
    have hj' : j' = j_new := huniq_front j' hr'
    subst hj'
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 hrest with rfl | htail
    · omega
    · have hlt2 := reach_trans_lt hcl htail
      omega

-- Every gate in a GoodChain is reachable from n
theorem mem_goodChain_reach {n : ℕ} {C : Circuit} {cs : List (Fin C.gates.length)}
    (hgc : GoodChain n C cs) :
    ∀ j ∈ cs, Reach C (n + 1) n (n + 1 + j.val) := by
  intro j hj
  obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.1 hj
  clear hj
  induction idx with
  | zero =>
    have h0 := hgc.2.2 0 hidx
    simp only [dite_true] at h0
    have hor := (hgc.2.1 (cs[0]'hidx) (List.getElem_mem hidx)).1
    have hread : Reads C (cs[0]'hidx) n := Or.inr ⟨(by rw [hor]; intro h; cases h), h0.1⟩
    exact Relation.TransGen.single ⟨cs[0]'hidx, rfl, hread⟩
  | succ idx ih =>
    have hprev := ih (by omega)
    have hs := hgc.2.2 (idx + 1) hidx
    have hne0 : idx + 1 ≠ 0 := by omega
    simp only [hne0, dite_false, Nat.add_sub_cancel] at hs
    have hor := (hgc.2.1 (cs[idx + 1]'hidx) (List.getElem_mem hidx)).1
    have hread : Reads C (cs[idx + 1]'hidx) (n + 1 + (cs[idx]'(by omega)).val) :=
      Or.inr ⟨(by rw [hor]; intro h; cases h), hs.1⟩
    exact Relation.TransGen.tail hprev ⟨cs[idx + 1]'hidx, rfl, hread⟩

-- Appending a chain of OR gates to a circuit
def appendOrs (base : ℕ) : ℕ → List ℕ → List Gate × ℕ
  | cur, [] => ([], cur)
  | cur, w :: ws =>
    let res := appendOrs (base + 1) base ws
    (⟨GateOp.or, [cur, w]⟩ :: res.1, res.2)

theorem appendOrs_length (base : ℕ) : ∀ (cur : ℕ) (ws : List ℕ),
    (appendOrs base cur ws).1.length = ws.length
  | _, [] => rfl
  | cur, _ :: ws => by simp [appendOrs, appendOrs_length]

theorem appendOrs_ok (base : ℕ) : ∀ (cur : ℕ) (ws : List ℕ),
    ∀ g ∈ (appendOrs base cur ws).1, Ok g
  | _, [], _, hg => by simp [appendOrs] at hg
  | cur, w :: ws, g, hg => by
    simp only [appendOrs, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp [Ok]
    · exact appendOrs_ok (base + 1) base ws g hg

theorem appendOrs_eval : ∀ (W : List Bool) (cur : ℕ) (ws : List ℕ),
    cur < W.length → (∀ w ∈ ws, w < W.length) →
    (wiresFrom (appendOrs W.length cur ws).1 W).getD (appendOrs W.length cur ws).2 false =
      (W.getD cur false || ws.any (fun w => W.getD w false))
  | W, cur, [], _, _ => by simp [appendOrs, wiresFrom]
  | W, cur, w :: ws, hcur, hws => by
    have hw : w < W.length := hws w List.mem_cons_self
    have hrest : ∀ u ∈ ws, u < W.length := fun u hu => hws u (List.mem_cons_of_mem _ hu)
    simp only [appendOrs]
    change (wiresFrom (appendOrs (W.length + 1) W.length ws).1
      (W ++ [GateOp.or.eval ([cur, w].map fun i => W.getD i false)])).getD
      (appendOrs (W.length + 1) W.length ws).2 false = _
    set W' := W ++ [GateOp.or.eval ([cur, w].map fun i => W.getD i false)] with hW'
    have hlen' : W'.length = W.length + 1 := by simp [hW']
    have hev := appendOrs_eval W' W.length ws (by omega) (fun u hu => by have := hrest u hu; omega)
    rw [hlen'] at hev
    rw [hev]
    have hget_last : W'.getD W.length false = (W.getD cur false || W.getD w false) := by
      rw [hW', getD_snoc_eq]; simp [GateOp.eval]
    have hany : ws.any (fun u => W'.getD u false) = ws.any (fun u => W.getD u false) := by
      apply Bool.eq_iff_iff.2
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨u, hu, h⟩
        refine ⟨u, hu, ?_⟩
        rwa [hW', List.getD_append _ _ _ _ (hrest u hu)] at h
      · rintro ⟨u, hu, h⟩
        refine ⟨u, hu, ?_⟩
        rwa [hW', List.getD_append _ _ _ _ (hrest u hu)]
    rw [hget_last, hany, List.any_cons, Bool.or_assoc]

-- Initial stats for elimChain: 0..n-1 are wires, n is constant false
def chainInitStats (n : ℕ) : List Stat :=
  (List.ofFn fun i : Fin n => Sum.inr i.val) ++ [Sum.inl false]

theorem chainInitStats_length (n : ℕ) : (chainInitStats n).length = n + 1 := by
  simp [chainInitStats]

theorem chainInitStats_getD_lt (n i : ℕ) (hi : i < n) :
    (chainInitStats n).getD i (Sum.inl false) = Sum.inr i := by
  unfold chainInitStats
  rw [List.getD_append _ _ _ _ (by simp; omega)]
  simp [hi]

theorem chainInitStats_getD_n (n : ℕ) :
    (chainInitStats n).getD n (Sum.inl false) = Sum.inl false := by
  unfold chainInitStats
  exact getD_snoc_len _ _ _ _ (by simp)

theorem invSkip_chainInit (n : ℕ) (x : Fin (n + 1) → Bool) :
    InvSkip (n + 1) (List.ofFn x)
      (List.ofFn (withLast (fun i : Fin n => x i.castSucc) false))
      (chainInitStats n, []) := by
  refine ⟨by simp [chainInitStats], ?_⟩
  intro i
  by_cases hi : i < n
  · rw [chainInitStats_getD_lt n i hi]
    refine ⟨by simp [statValid]; omega, ?_⟩
    simp only [statVal, wiresFrom, List.foldl_nil, getD_ofFn_withLast, hi, dite_true]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
    rfl
  · by_cases hEq : i = n
    · subst hEq
      rw [chainInitStats_getD_n]
      simp only [statValid, statVal, true_and]
      rw [getD_ofFn_withLast]; simp
    · rw [List.getD_eq_default _ _ (by rw [chainInitStats_length]; omega)]
      simp only [statValid, statVal, true_and]
      rw [getD_ofFn_withLast]; simp [hi, hEq]

-- Non-reachable wires stay unchanged across withLast y false / true and evalModRec,
-- and always map to Sum.inr in elimRec (n + 1) false (skipOf cs)
theorem unreach_props {n : ℕ} {C : Circuit} {cs : List (Fin C.gates.length)}
    (hcl : ∀ j : Fin C.gates.length, CleanGate (n + 1 + j.val) (C.gates.get j))
    (hgc : GoodChain n C cs) :
    ∀ w < n + 1 + C.gates.length, w ≠ n → ¬ Reach C (n + 1) n w →
      (∀ (y : Fin n → Bool) (b : Bool),
        (evalModRec (skipOf cs) 0 C.gates (List.ofFn (withLast y false))).getD w false =
          wireVal C (withLast y b) w) ∧
      (∃ k < n + 1 + (elimRec (n + 1) false (skipOf cs) 0 C.gates (chainInitStats n, [])).2.length,
        (elimRec (n + 1) false (skipOf cs) 0 C.gates (chainInitStats n, [])).1.getD w (Sum.inl false) = Sum.inr k) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw_lt hwn hnr
    by_cases hlt_n : w < n
    · constructor
      · intro y b
        rw [evalModRec_getD_lt _ _ _ _ w (by simp; omega)]
        unfold wireVal
        rw [wires_eq, getD_wiresFrom _ _ w (by simp; omega), getD_ofFn_withLast, getD_ofFn_withLast]
        simp [hlt_n]
      · refine ⟨w, by omega, ?_⟩
        rw [elimRec_getD_lt _ _ _ _ _ _ w (by rw [chainInitStats_length]; omega),
          chainInitStats_getD_lt n w hlt_n]
    · have hj_lt : w - (n + 1) < C.gates.length := by omega
      let j : Fin C.gates.length := ⟨w - (n + 1), hj_lt⟩
      have hw_eq : w = n + 1 + j.val := by simp [j]; omega
      have hj_notin : j ∉ cs := by
        intro hmem
        exact hnr (hw_eq ▸ mem_goodChain_reach hgc j hmem)
      have hskip : skipOf cs j.val = false := by
        cases hs : skipOf cs j.val with
        | false => rfl
        | true =>
          obtain ⟨p, hp, hpeq⟩ := (skipOf_iff cs j.val).1 hs
          have hjp : j = p := Fin.ext hpeq.symm
          subst hjp
          exact absurd hp hj_notin
      have hact_unreach : ∀ a ∈ activeInputs (C.gates.get j),
          a < w ∧ a ≠ n ∧ ¬ Reach C (n + 1) n a := by
        intro a ha
        have halt : a < w := by rw [hw_eq]; exact cleanGate_active_lt (hcl j) a ha
        have hread : Reads C j a := (mem_activeInputs_iff C j a).1 ha
        have hedge : Edge C (n + 1) a w := ⟨j, hw_eq, hread⟩
        refine ⟨halt, ?_, ?_⟩
        · intro han; subst han; exact hnr (Relation.TransGen.single hedge)
        · intro hra; exact hnr (Relation.TransGen.tail hra hedge)
      constructor
      · intro y b
        rw [hw_eq, evalModRec_gate C hcl (skipOf cs) (withLast y false) j,
          wireVal_gate_clean C hcl (withLast y b) j, hskip]
        simp only [Bool.false_eq_true, ite_false]
        congr 1
        apply List.map_congr_left
        intro a ha
        obtain ⟨halt, han, hanr⟩ := hact_unreach a ha
        exact (ih a halt (by omega) han hanr).1 y b
      · -- Show elimRec produces Sum.inr at index w = n + 1 + j.val
        set init := (chainInitStats n, ([] : List Gate))
        have hlen_pre : (elimRec (n + 1) false (skipOf cs) 0 (C.gates.take j.val) init).1.length = n + 1 + j.val := by
          rw [elimRec_fst_length, chainInitStats_length, List.length_take_of_le (by omega)]
        have hget_at : ∀ i < n + 1 + j.val,
            (elimRec (n + 1) false (skipOf cs) 0 (C.gates.take j.val) init).1.getD i (Sum.inl false) =
            (elimRec (n + 1) false (skipOf cs) 0 C.gates init).1.getD i (Sum.inl false) := by
          intro i hi
          exact (elimRec_take_getD (n + 1) false (skipOf cs) C.gates init j.val i
            (by rw [chainInitStats_length, List.length_take_of_le (by omega)]; omega)).symm
        have hstep_get : (elimRec (n + 1) false (skipOf cs) 0 C.gates init).1.getD (n + 1 + j.val) (Sum.inl false) =
            (elimRec (n + 1) false (skipOf cs) 0 (C.gates.take (j.val + 1)) init).1.getD (n + 1 + j.val) (Sum.inl false) :=
          elimRec_take_getD (n + 1) false (skipOf cs) C.gates init (j.val + 1) (n + 1 + j.val)
            (by rw [chainInitStats_length, List.length_take_of_le (by omega)]; omega)
        rw [hw_eq, hstep_get, elimRec_step_at _ _ _ _ _ j.val j.isLt]
        unfold elimStep
        simp only [hskip, Bool.false_eq_true, ↓reduceIte]
        rw [getD_snoc_len _ _ _ _ hlen_pre]
        have hgj : C.gates[j.val]'j.isLt = C.gates.get j := rfl
        rw [hgj]
        set acc_j := elimRec (n + 1) false (skipOf cs) 0 (C.gates.take j.val) init
        have hlen2_succ : (elimRec (n + 1) false (skipOf cs) 0 (C.gates.take (j.val + 1)) init).2.length ≤
            (elimRec (n + 1) false (skipOf cs) 0 C.gates init).2.length :=
          elimRec_take_len2_le (n + 1) false (skipOf cs) C.gates init (j.val + 1)
        -- Check simplify false on clean gate C.gates.get j whose active inputs all map to Sum.inr!
        have hact_inr : ∀ a ∈ activeInputs (C.gates.get j), ∃ ka, acc_j.1.getD a (Sum.inl false) = Sum.inr ka := by
          intro a ha
          obtain ⟨halt, han, hanr⟩ := hact_unreach a ha
          obtain ⟨ka, _, hka⟩ := (ih a halt (by omega) han hanr).2
          exact ⟨ka, by rw [hget_at a (by omega), hka]⟩
        rcases hcl j with ⟨hop, a, ha_head, ha_lt⟩ | ⟨hop, a, b, hin, _, ha_lt, hb_lt⟩
        · have hact : activeInputs (C.gates.get j) = [a] := by
            unfold activeInputs; rw [hop]
            cases hgi : (C.gates.get j).inputs with
            | nil => rw [hgi] at ha_head; simp at ha_head
            | cons x l => rw [hgi] at ha_head; simp only [List.head?_cons, Option.some.injEq] at ha_head; subst ha_head; rfl
          obtain ⟨ka, hka⟩ := hact_inr a (by rw [hact]; simp)
          have hsimp : simplify false (C.gates.get j).op (n + 1 + acc_j.2.length)
              ((activeInputs (C.gates.get j)).map fun i => acc_j.1.getD i (Sum.inl false)) =
              (some ⟨GateOp.not, [ka]⟩, Sum.inr (n + 1 + acc_j.2.length)) := by
            rw [hop, hact]; simp only [simplify, List.map_cons, List.map_nil]; rw [hka]; rfl
          have hlt_res : acc_j.2.length < (elimRec (n + 1) false (skipOf cs) 0 C.gates init).2.length := by
            have h1 : (elimRec (n + 1) false (skipOf cs) 0 (C.gates.take (j.val + 1)) init).2.length = acc_j.2.length + 1 := by
              rw [elimRec_step_at _ _ _ _ _ j.val j.isLt]
              unfold elimStep
              simp only [hskip, Bool.false_eq_true, ↓reduceIte, hgj]
              change (acc_j.2 ++ (simplify false (C.gates.get j).op (n + 1 + acc_j.2.length)
                ((activeInputs (C.gates.get j)).map fun i => acc_j.1.getD i (Sum.inl false))).1.toList).length = acc_j.2.length + 1
              rw [hsimp]; simp
            omega
          refine ⟨n + 1 + acc_j.2.length, by omega, ?_⟩
          rw [hsimp]
        · have hact : activeInputs (C.gates.get j) = [a, b] := by
            unfold activeInputs; rcases hop with hop | hop <;> rw [hop, hin]
          obtain ⟨ka, hka⟩ := hact_inr a (by rw [hact]; simp)
          obtain ⟨kb, hkb⟩ := hact_inr b (by rw [hact]; simp)
          rcases hop with hop | hop
          · have hsimp : simplify false (C.gates.get j).op (n + 1 + acc_j.2.length)
                ((activeInputs (C.gates.get j)).map fun i => acc_j.1.getD i (Sum.inl false)) =
                (some ⟨GateOp.and, [ka, kb]⟩, Sum.inr (n + 1 + acc_j.2.length)) := by
              rw [hop, hact]; simp only [simplify, List.map_cons, List.map_nil]; rw [hka, hkb]; rfl
            have hlt_res : acc_j.2.length < (elimRec (n + 1) false (skipOf cs) 0 C.gates init).2.length := by
              have h1 : (elimRec (n + 1) false (skipOf cs) 0 (C.gates.take (j.val + 1)) init).2.length = acc_j.2.length + 1 := by
                rw [elimRec_step_at _ _ _ _ _ j.val j.isLt]
                unfold elimStep
                simp only [hskip, Bool.false_eq_true, ↓reduceIte, hgj]
                change (acc_j.2 ++ (simplify false (C.gates.get j).op (n + 1 + acc_j.2.length)
                  ((activeInputs (C.gates.get j)).map fun i => acc_j.1.getD i (Sum.inl false))).1.toList).length = acc_j.2.length + 1
                rw [hsimp]; simp
              omega
            refine ⟨n + 1 + acc_j.2.length, by omega, ?_⟩
            rw [hsimp]
          · have hsimp : simplify false (C.gates.get j).op (n + 1 + acc_j.2.length)
                ((activeInputs (C.gates.get j)).map fun i => acc_j.1.getD i (Sum.inl false)) =
                (some ⟨GateOp.or, [ka, kb]⟩, Sum.inr (n + 1 + acc_j.2.length)) := by
              rw [hop, hact]; simp only [simplify, List.map_cons, List.map_nil]; rw [hka, hkb]; rfl
            have hlt_res : acc_j.2.length < (elimRec (n + 1) false (skipOf cs) 0 C.gates init).2.length := by
              have h1 : (elimRec (n + 1) false (skipOf cs) 0 (C.gates.take (j.val + 1)) init).2.length = acc_j.2.length + 1 := by
                rw [elimRec_step_at _ _ _ _ _ j.val j.isLt]
                unfold elimStep
                simp only [hskip, Bool.false_eq_true, ↓reduceIte, hgj]
                change (acc_j.2 ++ (simplify false (C.gates.get j).op (n + 1 + acc_j.2.length)
                  ((activeInputs (C.gates.get j)).map fun i => acc_j.1.getD i (Sum.inl false))).1.toList).length = acc_j.2.length + 1
                rw [hsimp]; simp
              omega
            refine ⟨n + 1 + acc_j.2.length, by omega, ?_⟩
            rw [hsimp]

-- Extract the list of non-chain side inputs of a GoodChain
theorem exists_side_wires {n : ℕ} {C : Circuit} {cs : List (Fin C.gates.length)}
    (hcl : ∀ j : Fin C.gates.length, CleanGate (n + 1 + j.val) (C.gates.get j))
    (hgc : GoodChain n C cs) :
    ∃ ws : List ℕ, ws.length = cs.length ∧
      (∀ w ∈ ws, w < n + 1 + C.gates.length ∧ w ≠ n ∧ ¬ Reach C (n + 1) n w) ∧
      (∀ (y : Fin n → Bool) (b : Bool),
        wireVal C (withLast y b) (frontWire n cs) =
          (b || ws.any (fun w => wireVal C (withLast y false) w))) := by
  have hstep : ∀ (i : ℕ) (hi : i < cs.length),
      ∃ w : ℕ, w < n + 1 + C.gates.length ∧ w ≠ n ∧ ¬ Reach C (n + 1) n w ∧
        ∀ (y : Fin n → Bool) (b : Bool),
          wireVal C (withLast y b) (n + 1 + (cs[i]'hi).val) =
            (wireVal C (withLast y b) (if h0 : i = 0 then n else n + 1 + (cs[i - 1]'(by omega)).val) ||
             wireVal C (withLast y false) w) := by
    intro i hi
    have hi_prop := hgc.2.2 i hi
    set prev := if h0 : i = 0 then n else n + 1 + (cs[i - 1]'(by omega)).val
    obtain ⟨w, hw_in, hw_ne_prev, hw_ne_n, hw_lt, hw_nr⟩ := hi_prop.2.2
    have hor := hgc.2.1 (cs[i]'hi) (List.getElem_mem hi)
    refine ⟨w, by omega, hw_ne_n, hw_nr, ?_⟩
    intro y b
    rw [wireVal_gate_clean C hcl (withLast y b) (cs[i]'hi)]
    have hact : activeInputs (C.gates.get (cs[i]'hi)) = (C.gates.get (cs[i]'hi)).inputs := by
      unfold activeInputs; rw [hor.1]
    rw [hact, hor.1]
    rcases hin : (C.gates.get (cs[i]'hi)).inputs with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, l⟩⟩⟩
    · have := hor.2; rw [hin] at this; simp at this
    · have := hor.2; rw [hin] at this; simp at this
    · have hprev_in : prev ∈ [a1, a2] := by rw [← hin]; exact hi_prop.1
      have hw_in' : w ∈ [a1, a2] := by rw [← hin]; exact hw_in
      have hw_eq : wireVal C (withLast y b) w = wireVal C (withLast y false) w := by
        have h1 := (unreach_props hcl hgc w (by omega) hw_ne_n hw_nr).1 y b
        have h2 := (unreach_props hcl hgc w (by omega) hw_ne_n hw_nr).1 y false
        exact h1.symm.trans h2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hprev_in hw_in'
      rcases hprev_in with rfl | rfl <;> rcases hw_in' with rfl | rfl
      · exact absurd rfl hw_ne_prev
      · simp [GateOp.eval, hw_eq]
      · simp [GateOp.eval, hw_eq, Bool.or_comm]
      · exact absurd rfl hw_ne_prev
    · have := hor.2; rw [hin] at this; simp at this
  choose wf hwf_lt hwf_nen hwf_nr hwf_eq using hstep
  refine ⟨List.ofFn (fun i : Fin cs.length => wf i.val i.isLt), by simp, ?_, ?_⟩
  · intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hw
    exact ⟨hwf_lt i.val i.isLt, hwf_nen i.val i.isLt, hwf_nr i.val i.isLt⟩
  · intro y b
    by_cases hlen : cs.length = 0
    · have hnil : cs = [] := List.eq_nil_of_length_eq_zero hlen
      have hfw : frontWire n cs = n := by simp [frontWire, hnil]
      have hof_nil : List.ofFn (fun i : Fin cs.length => wf i.val i.isLt) = [] :=
        List.eq_nil_of_length_eq_zero (by simp [hlen])
      rw [hfw, hof_nil]
      unfold wireVal
      rw [wires_eq, getD_wiresFrom _ _ n (by simp), getD_ofFn_withLast]
      simp
    · let m := cs.length - 1
      have hm_succ : m + 1 = cs.length := by omega
      have key : ∀ t (ht : t < cs.length),
          wireVal C (withLast y b) (n + 1 + (cs[t]'ht).val) =
            (b || ((List.ofFn (fun i : Fin cs.length => wf i.val i.isLt)).take (t + 1)).any
              (fun w => wireVal C (withLast y false) w)) := by
        intro t
        induction t with
        | zero =>
          intro ht
          rw [hwf_eq 0 ht y b]
          simp only [dite_true]
          have hnval : wireVal C (withLast y b) n = b := by
            unfold wireVal; rw [wires_eq, getD_wiresFrom _ _ n (by simp), getD_ofFn_withLast]; simp
          have htk : (List.ofFn (fun i : Fin cs.length => wf i.val i.isLt)).take 1 = [wf 0 ht] := by
            rw [List.take_one, List.head?_eq_getElem?, List.getElem?_ofFn]
            simp [ht]
          rw [hnval, htk]; simp
        | succ t ih =>
          intro ht
          rw [hwf_eq (t + 1) ht y b]
          have hne0 : t + 1 ≠ 0 := by omega
          simp only [hne0, dite_false, Nat.add_sub_cancel]
          rw [ih (by omega)]
          have htk : (List.ofFn (fun i : Fin cs.length => wf i.val i.isLt)).take (t + 2) =
              (List.ofFn (fun i : Fin cs.length => wf i.val i.isLt)).take (t + 1) ++ [wf (t + 1) ht] := by
            rw [List.take_succ_eq_append_getElem (by simp; omega)]
            simp
          rw [htk, List.any_append, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
      have hlast : cs.getLast? = some (cs[m]'(by omega)) := by
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
      have hfw : frontWire n cs = n + 1 + (cs[m]'(by omega)).val := by simp [frontWire, hlast]
      rw [hfw, key m (by omega)]
      have htk_all : (List.ofFn (fun i : Fin cs.length => wf i.val i.isLt)).take (m + 1) =
          List.ofFn (fun i : Fin cs.length => wf i.val i.isLt) := by
        rw [List.take_of_length_le]; simp [hm_succ]
      rw [htk_all]

-- Agreement outside inStrictInit when W y = false vs W y = true
theorem outside_agree_false {n : ℕ} {C : Circuit} {cs : List (Fin C.gates.length)}
    (hcl : ∀ j : Fin C.gates.length, CleanGate (n + 1 + j.val) (C.gates.get j))
    (hgc : GoodChain n C cs) (y : Fin n → Bool)
    (hfront : wireVal C (withLast y false) (frontWire n cs) = false) :
    ∀ w < n + 1 + C.gates.length, ¬ inStrictInit n cs w →
      (evalModRec (skipOf cs) 0 C.gates (List.ofFn (withLast y false))).getD w false =
        wireVal C (withLast y false) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw_lt hout
    by_cases hlt_n1 : w < n + 1
    · rw [evalModRec_getD_lt _ _ _ _ w (by simp; omega)]
      unfold wireVal
      rw [wires_eq, getD_wiresFrom _ _ w (by simp; omega)]
    · have hj_lt : w - (n + 1) < C.gates.length := by omega
      let j : Fin C.gates.length := ⟨w - (n + 1), hj_lt⟩
      have hw_eq : w = n + 1 + j.val := by simp [j]; omega
      by_cases hj_in : j ∈ cs
      · -- j ∈ cs and ¬ inStrictInit means j MUST be cs.getLast!
        cases hlast : cs.getLast? with
        | none =>
          have hnil := List.getLast?_eq_none_iff.1 hlast
          subst hnil; simp at hj_in
        | some last =>
          have hjeq : j = last := by
            by_contra hne
            exact hout (by simp [inStrictInit, hlast]; exact Or.inr ⟨j, hj_in, hne, hw_eq⟩)
          subst hjeq
          have hfw : frontWire n cs = n + 1 + j.val := by simp [frontWire, hlast]
          have hsk : skipOf cs j.val = true := (skipOf_iff cs j.val).2 ⟨j, hj_in, rfl⟩
          rw [hw_eq, evalModRec_gate C hcl (skipOf cs) (withLast y false) j, hsk]
          simp only [ite_true]
          rw [← hfw, hfront]
      · -- j ∉ cs: skip j = false, and no active input of j is in inStrictInit!
        have hsk : skipOf cs j.val = false := by
          cases hs : skipOf cs j.val with
          | false => rfl
          | true =>
            obtain ⟨p, hp, hpeq⟩ := (skipOf_iff cs j.val).1 hs
            exact absurd (Fin.ext hpeq.symm ▸ hp) hj_in
        rw [hw_eq, evalModRec_gate C hcl (skipOf cs) (withLast y false) j,
          wireVal_gate_clean C hcl (withLast y false) j, hsk]
        simp only [Bool.false_eq_true, ite_false]
        congr 1
        apply List.map_congr_left
        intro a ha
        have halt : a < w := by rw [hw_eq]; exact cleanGate_active_lt (hcl j) a ha
        have hread : Reads C j a := (mem_activeInputs_iff C j a).1 ha
        have ha_out : ¬ inStrictInit n cs a := by
          intro hsp
          cases hlast : cs.getLast? with
          | none => simp [inStrictInit, hlast] at hsp
          | some last =>
            simp only [inStrictInit, hlast] at hsp
            rcases hsp with rfl | ⟨p, hp, hpne, rfl⟩
            · have hpos : 0 < cs.length := by
                cases hcs : cs with
                | nil => simp [hcs] at hlast
                | cons _ _ => simp
              have huniq0 := (hgc.2.2 0 hpos).2.1
              simp only [dite_true] at huniq0
              have hj0 := huniq0 j hread
              exact hj_in (hj0 ▸ List.getElem_mem hpos)
            · obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.1 hp
              have hidx1 : idx + 1 < cs.length := by
                by_contra hge
                have heq : cs.getLast? = some (cs[idx]'hidx) := by
                  rw [List.getLast?_eq_getElem?]
                  have : cs.length - 1 = idx := by omega
                  rw [this, List.getElem?_eq_getElem hidx]
                rw [hlast] at heq
                exact hpne (Option.some.inj heq).symm
              have huniq := (hgc.2.2 (idx + 1) hidx1).2.1
              have hne0 : idx + 1 ≠ 0 := by omega
              simp only [hne0, dite_false, Nat.add_sub_cancel] at huniq
              have hj1 := huniq j hread
              exact hj_in (hj1 ▸ List.getElem_mem hidx1)
        exact ih a halt (by omega) ha_out

theorem outside_agree_true {n : ℕ} {C : Circuit} {cs : List (Fin C.gates.length)}
    (hcl : ∀ j : Fin C.gates.length, CleanGate (n + 1 + j.val) (C.gates.get j))
    (hgc : GoodChain n C cs) (hne_cs : cs ≠ []) (y : Fin n → Bool)
    (hfront : wireVal C (withLast y false) (frontWire n cs) = true)
    (hfront_t : wireVal C (withLast y true) (frontWire n cs) = true) :
    ∀ w < n + 1 + C.gates.length, ¬ inStrictInit n cs w →
      wireVal C (withLast y false) w = wireVal C (withLast y true) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw_lt hout
    have hlast_ex : ∃ last, cs.getLast? = some last := by
      cases h : cs.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne_cs
      | some last => exact ⟨last, rfl⟩
    obtain ⟨last, hlast⟩ := hlast_ex
    by_cases hlt_n : w < n
    · unfold wireVal
      rw [wires_eq, getD_wiresFrom _ _ w (by simp; omega), wires_eq, getD_wiresFrom _ _ w (by simp; omega),
        getD_ofFn_withLast, getD_ofFn_withLast]
      simp [hlt_n]
    · have hwn : w ≠ n := by
        intro h; subst h
        exact hout (by simp [inStrictInit, hlast])
      have hj_lt : w - (n + 1) < C.gates.length := by omega
      let j : Fin C.gates.length := ⟨w - (n + 1), hj_lt⟩
      have hw_eq : w = n + 1 + j.val := by simp [j]; omega
      by_cases hj_in : j ∈ cs
      · have hjeq : j = last := by
          by_contra hne
          exact hout (by simp [inStrictInit, hlast]; exact Or.inr ⟨j, hj_in, hne, hw_eq⟩)
        subst hjeq
        have hfw : frontWire n cs = n + 1 + j.val := by simp [frontWire, hlast]
        rw [hw_eq, ← hfw, hfront, hfront_t]
      · rw [hw_eq, wireVal_gate_clean C hcl (withLast y false) j,
          wireVal_gate_clean C hcl (withLast y true) j]
        congr 1
        apply List.map_congr_left
        intro a ha
        have halt : a < w := by rw [hw_eq]; exact cleanGate_active_lt (hcl j) a ha
        have hread : Reads C j a := (mem_activeInputs_iff C j a).1 ha
        have ha_out : ¬ inStrictInit n cs a := by
          intro hsp
          simp only [inStrictInit, hlast] at hsp
          rcases hsp with rfl | ⟨p, hp, hpne, rfl⟩
          · have hpos : 0 < cs.length := List.length_pos_of_ne_nil hne_cs
            have huniq0 := (hgc.2.2 0 hpos).2.1
            simp only [dite_true] at huniq0
            exact hj_in ((huniq0 j hread) ▸ List.getElem_mem hpos)
          · obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.1 hp
            have hidx1 : idx + 1 < cs.length := by
              by_contra hge
              have heq : cs.getLast? = some (cs[idx]'hidx) := by
                rw [List.getLast?_eq_getElem?]
                have : cs.length - 1 = idx := by omega
                rw [this, List.getElem?_eq_getElem hidx]
              rw [hlast] at heq
              exact hpne (Option.some.inj heq).symm
            have huniq := (hgc.2.2 (idx + 1) hidx1).2.1
            have hne0 : idx + 1 ≠ 0 := by omega
            simp only [hne0, dite_false, Nat.add_sub_cancel] at huniq
            exact hj_in ((huniq j hread) ▸ List.getElem_mem hidx1)
        exact ih a halt (by omega) ha_out

-- Core chain extension theorem: either cs is complete or extends by one OR gate
theorem extend_chain {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool}
    (hmin : IsMinimalCircuit (n + 1) C)
    (hHnc : ∃ y y' : Fin n → Bool, H y ≠ H y')
    (hCF : ∀ x : Fin (n + 1) → Bool,
      circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc)))
    (cs : List (Fin C.gates.length)) (hgc : GoodChain n C cs) :
    (∃ last : Fin C.gates.length, cs.getLast? = some last ∧
      last.val + 1 = C.gates.length ∧ C.output = n + 1 + last.val) ∨
    (∃ g_next : Fin C.gates.length, GoodChain n C (cs ++ [g_next])) := by
  have hH01 : (∃ y0 : Fin n → Bool, H y0 = false) ∧ (∃ y1 : Fin n → Bool, H y1 = true) := by
    obtain ⟨y, y', hne⟩ := hHnc
    cases hy : H y <;> cases hy' : H y'
    · exact absurd (hy.trans hy'.symm) hne
    · exact ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩
    · exact ⟨⟨y', hy'⟩, ⟨y, hy⟩⟩
    · exact absurd (hy.trans hy'.symm) hne
  have hCnc : ∃ x x' : Fin (n + 1) → Bool, circuitFun (n + 1) C x ≠ circuitFun (n + 1) C x' := by
    obtain ⟨y0, hy0⟩ := hH01.1
    refine ⟨withLast y0 false, withLast y0 true, ?_⟩
    rw [hCF, hCF]
    simp [withLast_last, withLast_castSucc, hy0]
  have hcl := min_clean hmin hCnc
  have hout_lt := min_out_lt hCnc
  have hCF_withLast : ∀ (y : Fin n → Bool) (b : Bool),
      wireVal C (withLast y b) C.output = (b || H y) := by
    intro y b
    have h := hCF (withLast y b)
    have h1 : (fun i : Fin n => withLast y b i.castSucc) = y := by funext i; exact withLast_castSucc y b i
    rw [withLast_last, h1] at h
    exact h
  have hout_ne_n : C.output ≠ n := by
    intro heq
    obtain ⟨y1, hy1⟩ := hH01.2
    have h := hCF_withLast y1 false
    unfold wireVal at h
    rw [heq, wires_eq, getD_wiresFrom _ _ n (by simp), getD_ofFn_withLast] at h
    simp [hy1] at h
  have hout_not_sp : ¬ inStrictInit n cs C.output := by
    intro hsp
    cases hlast : cs.getLast? with
    | none => simp [inStrictInit, hlast] at hsp
    | some last =>
      simp only [inStrictInit, hlast] at hsp
      rcases hsp with heq | ⟨j, hj, hjne, heq⟩
      · exact hout_ne_n heq
      · have hlast_eq := min_out_last hmin hCnc j heq
        have hle := pairwise_le_last hgc.1 hlast j hj
        have hlt : j.val < last.val := lt_of_le_of_ne hle (fun h => hjne (Fin.ext h))
        omega
  obtain ⟨ws, hws_len, hws_props, hws_eval⟩ := exists_side_wires hcl hgc
  let W : (Fin n → Bool) → Bool := fun y => ws.any (fun w => wireVal C (withLast y false) w)
  let skip := skipOf cs
  let init : List Stat × List Gate := (chainInitStats n, [])
  let res := elimRec (n + 1) false skip 0 C.gates init
  let H' : (Fin n → Bool) → Bool := fun y =>
    (evalModRec skip 0 C.gates (List.ofFn (withLast y false))).getD C.output false
  have hH_decomp : ∀ y : Fin n → Bool, (W y || H' y) = H y := by
    intro y
    cases hWy : W y with
    | false =>
      have hf0 : wireVal C (withLast y false) (frontWire n cs) = false := by
        rw [hws_eval y false]; exact hWy
      have hag := outside_agree_false hcl hgc y hf0 C.output hout_lt hout_not_sp
      have hHy := hCF_withLast y false
      simp only [Bool.false_or] at hHy ⊢
      exact hag.trans hHy
    | true =>
      have hne_cs : cs ≠ [] := by
        intro hnil
        have hws_nil : ws = [] := List.eq_nil_of_length_eq_zero (by rw [hws_len, hnil]; rfl)
        simp [W, hws_nil] at hWy
      have hf0 : wireVal C (withLast y false) (frontWire n cs) = true := by
        rw [hws_eval y false, Bool.false_or]; exact hWy
      have hf1 : wireVal C (withLast y true) (frontWire n cs) = true := by
        rw [hws_eval y true]; simp
      have hag := outside_agree_true hcl hgc hne_cs y hf0 hf1 C.output hout_lt hout_not_sp
      have h0 := hCF_withLast y false
      have h1 := hCF_withLast y true
      simp only [Bool.false_or, Bool.true_or] at h0 h1
      rw [← h0, hag, h1]; simp
  -- Case split on whether H' is identically false
  by_cases hH'_all_false : ∀ y : Fin n → Bool, H' y = false
  · -- Then circuitFun = wireVal (frontWire n cs), so cs ≠ [] and last must be the final gate!
    have hEq_front : ∀ x : Fin (n + 1) → Bool,
        circuitFun (n + 1) C x = wireVal C x (frontWire n cs) := by
      intro x
      rw [eq_withLast x]
      set y := fun i : Fin n => x i.castSucc
      set b := x (Fin.last n)
      have h1 := hCF_withLast y b
      have h2 := hws_eval y b
      have h3 := hH_decomp y
      rw [hH'_all_false y, Bool.or_false] at h3
      change wireVal C (withLast y b) C.output = wireVal C (withLast y b) (frontWire n cs)
      rw [h1, h2, ← h3]
    cases hlast : cs.getLast? with
    | none =>
      exfalso
      have hnil := List.getLast?_eq_none_iff.1 hlast
      obtain ⟨y1, hy1⟩ := hH01.2
      have h1 := hEq_front (withLast y1 false)
      have h2 := hCF_withLast y1 false
      have hfw : frontWire n cs = n := by simp [frontWire, hnil]
      rw [hfw] at h1
      change wireVal C (withLast y1 false) C.output = _ at h1
      rw [h2] at h1
      unfold wireVal at h1
      rw [wires_eq, getD_wiresFrom _ _ n (by simp), getD_ofFn_withLast] at h1
      simp [hy1] at h1
    | some last =>
      have hlast_end : last.val + 1 = C.gates.length := by
        by_contra hne
        let D : Circuit := ⟨C.gates.take (last.val + 1), n + 1 + last.val⟩
        have hDfit : FanInTwo D := fun g hg => hmin.1 g (List.mem_of_mem_take hg)
        have hDeq : circuitFun (n + 1) D = circuitFun (n + 1) C := by
          funext x
          rw [hEq_front x]
          have hfw : frontWire n cs = n + 1 + last.val := by simp [frontWire, hlast]
          rw [hfw]
          change (wiresFrom (C.gates.take (last.val + 1)) (List.ofFn x)).getD (n + 1 + last.val) false =
            (wiresFrom C.gates (List.ofFn x)).getD (n + 1 + last.val) false
          exact (wiresFrom_take_getD C.gates (List.ofFn x) (last.val + 1) (n + 1 + last.val)
            (by rw [List.length_ofFn, List.length_take_of_le (show last.val + 1 ≤ C.gates.length from last.isLt)]; omega)).symm
        have hle := hmin.2 D hDfit hDeq
        change C.gates.length ≤ (C.gates.take (last.val + 1)).length at hle
        rw [List.length_take_of_le (by omega)] at hle
        omega
      have hout_eq : C.output = n + 1 + last.val := by
        rcases min_used hmin last with ho | ⟨j', hj'⟩
        · exact ho
        · have hlt := cleanGate_active_lt (hcl j') (n + 1 + last.val) ((mem_activeInputs_iff C j' _).2 hj')
          omega
      exact Or.inl ⟨last, rfl, hlast_end, hout_eq⟩
  · -- H' is NOT identically false! Show H' is non-constant, hence dropCount ≤ cs.length + 1!
    push Not at hH'_all_false
    obtain ⟨y1, hy1⟩ := hH'_all_false
    have hy1' : H' y1 = true := Bool.eq_true_of_not_eq_false hy1
    have hH'0 : ∃ y0 : Fin n → Bool, H' y0 = false := by
      obtain ⟨y0, hy0⟩ := hH01.1
      have hd := hH_decomp y0
      rw [hy0, Bool.or_eq_false_iff] at hd
      exact ⟨y0, hd.2⟩
    obtain ⟨y0, hy0⟩ := hH'0
    have hinv_res : ∀ x : Fin (n + 1) → Bool,
        InvSkip (n + 1) (List.ofFn x)
          (evalModRec skip 0 C.gates (List.ofFn (withLast (fun i : Fin n => x i.castSucc) false))) res := by
      intro x
      exact invSkip_elimRec (n + 1) false skip (List.ofFn x) (by simp) 0 C.gates _ init hmin.1 (invSkip_chainInit n x)
    -- Therefore res.1.getD C.output must be Sum.inr out'!
    have hout_inr : ∃ out' < n + 1 + res.2.length, res.1.getD C.output (Sum.inl false) = Sum.inr out' := by
      cases hst : res.1.getD C.output (Sum.inl false) with
      | inl c =>
        exfalso
        have h0 := ((hinv_res (withLast y0 false)).2 C.output).2
        have h1 := ((hinv_res (withLast y1 false)).2 C.output).2
        have heq0 : (fun i : Fin n => withLast y0 false i.castSucc) = y0 := by funext i; exact withLast_castSucc y0 false i
        have heq1 : (fun i : Fin n => withLast y1 false i.castSucc) = y1 := by funext i; exact withLast_castSucc y1 false i
        rw [hst, heq0] at h0
        rw [hst, heq1] at h1
        change c = H' y0 at h0
        change c = H' y1 at h1
        rw [hy0] at h0; rw [hy1'] at h1
        exact Bool.false_ne_true (h0.symm.trans h1)
      | inr out' =>
        have hv := ((hinv_res (withLast y0 false)).2 C.output).1
        rw [hst] at hv
        exact ⟨out', hv, rfl⟩
    obtain ⟨out', hout'_lt, hout'_eq⟩ := hout_inr
    -- Map each side wire w ∈ ws to its wire index in res.2
    have hws_map : ∃ ws' : List ℕ, ws'.length = ws.length ∧
        (∀ w' ∈ ws', w' < n + 1 + res.2.length) ∧
        (∀ x : Fin (n + 1) → Bool,
          ws'.any (fun w' => (wiresFrom res.2 (List.ofFn x)).getD w' false) =
            W (fun i : Fin n => x i.castSucc)) := by
      have hmem_map : ∀ w ∈ ws, ∃ w' < n + 1 + res.2.length,
          res.1.getD w (Sum.inl false) = Sum.inr w' ∧
          ∀ x : Fin (n + 1) → Bool,
            (wiresFrom res.2 (List.ofFn x)).getD w' false =
              wireVal C (withLast (fun i : Fin n => x i.castSucc) false) w := by
        intro w hw
        obtain ⟨wlt, wnen, wnr⟩ := hws_props w hw
        obtain ⟨w', hw'_lt, hw'_eq⟩ := (unreach_props hcl hgc w wlt wnen wnr).2
        refine ⟨w', hw'_lt, hw'_eq, ?_⟩
        intro x
        have hv := ((hinv_res x).2 w).2
        rw [hw'_eq] at hv
        exact hv.trans ((unreach_props hcl hgc w wlt wnen wnr).1 (fun i => x i.castSucc) false)
      -- Build ws' by induction on ws
      have hbuild : ∀ (l : List ℕ), (∀ w ∈ l, ∃ w' < n + 1 + res.2.length,
          ∀ x : Fin (n + 1) → Bool,
            (wiresFrom res.2 (List.ofFn x)).getD w' false =
              wireVal C (withLast (fun i : Fin n => x i.castSucc) false) w) →
          ∃ l' : List ℕ, l'.length = l.length ∧
            (∀ w' ∈ l', w' < n + 1 + res.2.length) ∧
            (∀ x : Fin (n + 1) → Bool,
              l'.any (fun w' => (wiresFrom res.2 (List.ofFn x)).getD w' false) =
                l.any (fun w => wireVal C (withLast (fun i : Fin n => x i.castSucc) false) w)) := by
        intro l
        induction l with
        | nil => intro _; exact ⟨[], rfl, by simp, by simp⟩
        | cons a t ih =>
          intro hall
          obtain ⟨a', ha'_lt, ha'_eq⟩ := hall a List.mem_cons_self
          obtain ⟨t', ht'_len, ht'_lt, ht'_eq⟩ := ih (fun w hw => hall w (List.mem_cons_of_mem _ hw))
          refine ⟨a' :: t', by simp [ht'_len], ?_, ?_⟩
          · intro w' hw'
            rcases List.mem_cons.1 hw' with rfl | ht'
            · exact ha'_lt
            · exact ht'_lt w' ht'
          · intro x
            simp only [List.any_cons, ha'_eq x, ht'_eq x]
      exact hbuild ws (fun w hw => let ⟨w', h1, _, h2⟩ := hmem_map w hw; ⟨w', h1, h2⟩)
    obtain ⟨ws', hws'_len, hws'_lt, hws'_eval⟩ := hws_map
    -- Rebuild circuit D = res.2 ++ appendOrs (n + 1 + res.2.length) n (ws' ++ [out'])
    let tail := appendOrs (n + 1 + res.2.length) n (ws' ++ [out'])
    let D : Circuit := ⟨res.2 ++ tail.1, tail.2⟩
    have hDfit : FanInTwo D := by
      intro g hg
      rcases List.mem_append.1 hg with h1 | h2
      · exact elimRec_ok (n + 1) false skip 0 C.gates init (by simp [init]) g h1
      · exact appendOrs_ok _ _ _ g h2
    have hDeq : circuitFun (n + 1) D = circuitFun (n + 1) C := by
      funext x
      change (wiresFrom (res.2 ++ tail.1) (List.ofFn x)).getD tail.2 false = circuitFun (n + 1) C x
      rw [wiresFrom_append]
      set W0 := wiresFrom res.2 (List.ofFn x) with hW0
      have hW0_len : W0.length = n + 1 + res.2.length := by rw [hW0, length_wiresFrom]; simp
      have htail_ev := appendOrs_eval W0 n (ws' ++ [out']) (by omega) (by
        intro u hu
        rcases List.mem_append.1 hu with h1 | h2
        · have := hws'_lt u h1; omega
        · simp at h2; subst h2; omega)
      rw [hW0_len] at htail_ev
      rw [htail_ev, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
      have hW0_n : W0.getD n false = x (Fin.last n) := by
        rw [hW0, getD_wiresFrom _ _ n (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
        rfl
      have hW0_out : W0.getD out' false = H' (fun i : Fin n => x i.castSucc) := by
        have hv := ((hinv_res x).2 C.output).2
        rw [hout'_eq] at hv
        exact hv
      rw [hW0_n, hws'_eval x, hW0_out, ← Bool.or_assoc, Bool.or_assoc, hH_decomp, hCF x]
    have hmin_D := hmin.2 D hDfit hDeq
    have hD_size : D.size = res.2.length + cs.length + 1 := by
      simp [D, Circuit.size, tail, appendOrs_length, hws'_len, hws_len]; omega
    have hdrop_add := elimRec_len_add_drop (n + 1) false skip 0 C.gates init
    change res.2.length + dropCount (n + 1) false skip 0 C.gates init = 0 + C.gates.length at hdrop_add
    have hdrop_le : dropCount (n + 1) false skip 0 C.gates init ≤ cs.length + 1 := by
      change C.gates.length ≤ D.size at hmin_D; omega
    -- Every gate in cs is dropped
    have hcs_dropped : ∀ p ∈ cs, isDropped (n + 1) false skip C.gates init p.val := by
      intro p hp
      unfold isDropped
      rw [elimRec_step_at _ _ _ _ _ p.val p.isLt]
      unfold elimStep
      have hsk : skip p.val = true := (skipOf_iff cs p.val).2 ⟨p, hp, rfl⟩
      simp [hsk]
    have hcs_nodup : cs.Nodup := hgc.1.imp (fun {a b} h => ne_of_lt h)
    have hcs_card : cs.toFinset.card = cs.length := List.toFinset_card_of_nodup hcs_nodup
    -- Status of frontWire n cs in res.1 is Sum.inl false
    have hfront_stat : res.1.getD (frontWire n cs) (Sum.inl false) = Sum.inl false := by
      cases hlast : cs.getLast? with
      | none =>
        simp only [frontWire, hlast]
        rw [elimRec_getD_lt _ _ _ _ _ _ n (by rw [chainInitStats_length]; omega)]
        exact chainInitStats_getD_n n
      | some last =>
        simp only [frontWire, hlast]
        have hlast_mem : last ∈ cs := List.mem_of_getLast? hlast
        have hsk : skip last.val = true := (skipOf_iff cs last.val).2 ⟨last, hlast_mem, rfl⟩
        have hlen_pre : (elimRec (n + 1) false skip 0 (C.gates.take last.val) init).1.length = n + 1 + last.val := by
          rw [elimRec_fst_length, chainInitStats_length, List.length_take_of_le (by omega)]
        change (elimRec (n + 1) false skip 0 C.gates init).1.getD (n + 1 + last.val) (Sum.inl false) = Sum.inl false
        rw [elimRec_take_getD (n + 1) false skip C.gates init (last.val + 1) (n + 1 + last.val)
          (by rw [chainInitStats_length, List.length_take_of_le (by omega)]; omega),
          elimRec_step_at _ _ _ _ _ last.val last.isLt]
        unfold elimStep
        simp only [hsk, ite_true]
        exact getD_snoc_len _ _ _ _ hlen_pre
    -- Helper: any gate j reading a wire a whose status in res.1 is Sum.inl c is dropped!
    have hdrop_of_const_in : ∀ (j : Fin C.gates.length) (a : ℕ) (c : Bool),
        Reads C j a → res.1.getD a (Sum.inl false) = Sum.inl c →
        isDropped (n + 1) false skip C.gates init j.val := by
      intro j a c hread ha_stat
      unfold isDropped
      rw [elimRec_step_at _ _ _ _ _ j.val j.isLt]
      unfold elimStep
      by_cases hsk : skip j.val = true
      · simp [hsk]
      · simp only [hsk, Bool.false_eq_true, ↓reduceIte, List.length_append]
        have hgj : C.gates[j.val]'j.isLt = C.gates.get j := rfl
        rw [hgj]
        have halt : a < n + 1 + j.val := cleanGate_active_lt (hcl j) a ((mem_activeInputs_iff C j a).2 hread)
        have ha_pre : (elimRec (n + 1) false skip 0 (C.gates.take j.val) init).1.getD a (Sum.inl false) = Sum.inl c := by
          have h := ha_stat
          change (elimRec (n + 1) false skip 0 C.gates init).1.getD a (Sum.inl false) = Sum.inl c at h
          rw [elimRec_take_getD (n + 1) false skip C.gates init j.val a
            (by rw [chainInitStats_length, List.length_take_of_le (by omega)]; omega)] at h
          exact h
        have hokj : Ok (C.gates.get j) := hmin.1 _ (List.get_mem _ _)
        have hnone : (simplify false (C.gates.get j).op
            (n + 1 + (elimRec (n + 1) false skip 0 (C.gates.take j.val) init).2.length)
            ((activeInputs (C.gates.get j)).map fun i =>
              (elimRec (n + 1) false skip 0 (C.gates.take j.val) init).1.getD i (Sum.inl false))).1 = none := by
          apply simplify_none_of_const false _ _ _ (ok_op _ hokj)
            (by rw [List.length_map]; exact (activeInputs_length_le _).trans hokj.2)
            (fun hn => by rw [List.length_map]; exact activeInputs_not_length _ hn) c
          exact List.mem_map.2 ⟨a, (mem_activeInputs_iff C j a).2 hread, ha_pre⟩
        rw [hnone]; simp
    -- Now check whether frontWire n cs has a reader
    by_cases hex_read : ∃ j : Fin C.gates.length, Reads C j (frontWire n cs)
    · obtain ⟨g_next, hg_read⟩ := hex_read
      have hg_notin : g_next ∉ cs := by
        intro hmem
        have hle := frontWire_ge_mem n hgc.1 g_next hmem
        have hlt := reach_implies_lt hcl ⟨g_next, rfl, hg_read⟩
        omega
      -- Unique reader of frontWire n cs!
      have hg_uniq : ∀ j : Fin C.gates.length, Reads C j (frontWire n cs) → j = g_next := by
        intro j hj_read
        by_contra hne
        have hj_notin : j ∉ cs := by
          intro hmem
          have hle := frontWire_ge_mem n hgc.1 j hmem
          have hlt := reach_implies_lt hcl ⟨j, rfl, hj_read⟩
          omega
        let S : Finset (Fin C.gates.length) := insert j (insert g_next cs.toFinset)
        have hS_drop : ∀ p ∈ S, isDropped (n + 1) false skip C.gates init p.val := by
          intro p hp
          simp only [S, Finset.mem_insert, List.mem_toFinset] at hp
          rcases hp with rfl | rfl | hmem
          · exact hdrop_of_const_in p (frontWire n cs) false hj_read hfront_stat
          · exact hdrop_of_const_in p (frontWire n cs) false hg_read hfront_stat
          · exact hcs_dropped p hmem
        have hcard1 : (insert g_next cs.toFinset).card = cs.length + 1 := by
          rw [Finset.card_insert_of_notMem (by simp [hg_notin]), hcs_card]
        have hj_not2 : j ∉ insert g_next cs.toFinset := by simp [hne, hj_notin]
        have hcard2 : S.card = cs.length + 2 := by
          rw [Finset.card_insert_of_notMem hj_not2, hcard1]
        have hge := dropCount_ge_card_dropped (n + 1) false skip C.gates init S hS_drop
        omega
      -- Show g_next MUST be GateOp.or!
      have hg_or : (C.gates.get g_next).op = GateOp.or := by
        have hokg := hmin.1 _ (List.get_mem _ g_next)
        rcases ok_op _ hokg with hop | hop | hop
        · exfalso
          -- AND gate reading Sum.inl false produces a constant in res.1!
          have hsk_g : skip g_next.val = false := by
            cases hs : skip g_next.val with
            | false => rfl
            | true =>
              obtain ⟨p, hp, hpeq⟩ := (skipOf_iff cs g_next.val).1 hs
              exact absurd (Fin.ext hpeq.symm ▸ hp) hg_notin
          have hlen_pre : (elimRec (n + 1) false skip 0 (C.gates.take g_next.val) init).1.length = n + 1 + g_next.val := by
            rw [elimRec_fst_length, chainInitStats_length, List.length_take_of_le (by omega)]
          have hlen_succ : (elimRec (n + 1) false skip 0 (C.gates.take (g_next.val + 1)) init).1.length = n + 1 + g_next.val + 1 := by
            rw [elimRec_fst_length, chainInitStats_length, List.length_take_of_le (by omega)]; omega
          have hfw_lt : frontWire n cs < n + 1 + g_next.val := reach_implies_lt hcl ⟨g_next, rfl, hg_read⟩
          have hfw_pre : (elimRec (n + 1) false skip 0 (C.gates.take g_next.val) init).1.getD (frontWire n cs) (Sum.inl false) = Sum.inl false := by
            have h := hfront_stat
            change (elimRec (n + 1) false skip 0 C.gates init).1.getD (frontWire n cs) (Sum.inl false) = Sum.inl false at h
            rw [elimRec_take_getD (n + 1) false skip C.gates init g_next.val (frontWire n cs)
              (by rw [chainInitStats_length, List.length_take_of_le (by omega)]; omega)] at h
            exact h
          obtain ⟨b, hb⟩ : ∃ b : Bool, res.1.getD (n + 1 + g_next.val) (Sum.inl false) = Sum.inl b := by
            have heq_res : res.1.getD (n + 1 + g_next.val) (Sum.inl false) =
                (elimRec (n + 1) false skip 0 (C.gates.take (g_next.val + 1)) init).1.getD (n + 1 + g_next.val) (Sum.inl false) :=
              elimRec_take_getD (n + 1) false skip C.gates init (g_next.val + 1) (n + 1 + g_next.val)
                (by rw [chainInitStats_length, List.length_take_of_le (by omega)]; omega)
            rw [heq_res, elimRec_step_at _ _ _ _ _ g_next.val g_next.isLt]
            unfold elimStep
            simp only [hsk_g, Bool.false_eq_true, ↓reduceIte]
            rw [getD_snoc_len _ _ _ _ hlen_pre]
            have hgj : C.gates[g_next.val]'g_next.isLt = C.gates.get g_next := rfl
            rw [hgj]
            apply simplify_const_of_not_or_and_false false _ _ _ (Or.inr hop)
              (by rw [List.length_map]; exact (activeInputs_length_le _).trans hokg.2)
              (fun hn => by rw [hop] at hn; cases hn)
            exact List.mem_map.2 ⟨frontWire n cs, (mem_activeInputs_iff C g_next _).2 hg_read, hfw_pre⟩
          have hg_ne_out : C.output ≠ n + 1 + g_next.val := by
            intro heq; rw [heq, hb] at hout'_eq; cases hout'_eq
          rcases min_used hmin g_next with ho | ⟨g2, hg2_read⟩
          · exact hg_ne_out ho
          · have hg2_gt : g_next.val < g2.val := by
              have := reach_implies_lt hcl ⟨g2, rfl, hg2_read⟩; omega
            have hg2_ne : g2 ≠ g_next := fun h => by subst h; omega
            have hg2_notin : g2 ∉ cs := by
              intro hmem
              have hle := frontWire_ge_mem n hgc.1 g2 hmem
              omega
            let S : Finset (Fin C.gates.length) := insert g2 (insert g_next cs.toFinset)
            have hS_drop : ∀ p ∈ S, isDropped (n + 1) false skip C.gates init p.val := by
              intro p hp
              simp only [S, Finset.mem_insert, List.mem_toFinset] at hp
              rcases hp with rfl | rfl | hmem
              · exact hdrop_of_const_in p (n + 1 + g_next.val) b hg2_read hb
              · exact hdrop_of_const_in p (frontWire n cs) false hg_read hfront_stat
              · exact hcs_dropped p hmem
            have hcard1 : (insert g_next cs.toFinset).card = cs.length + 1 := by
              rw [Finset.card_insert_of_notMem (by simp [hg_notin]), hcs_card]
            have hcard2 : S.card = cs.length + 2 := by
              rw [Finset.card_insert_of_notMem (by simp [hg2_ne, hg2_notin]), hcard1]
            have hge := dropCount_ge_card_dropped (n + 1) false skip C.gates init S hS_drop
            omega
        · exact hop
        · exfalso
          -- NOT gate reading Sum.inl false produces constant true in res.1!
          have hsk_g : skip g_next.val = false := by
            cases hs : skip g_next.val with
            | false => rfl
            | true =>
              obtain ⟨p, hp, hpeq⟩ := (skipOf_iff cs g_next.val).1 hs
              exact absurd (Fin.ext hpeq.symm ▸ hp) hg_notin
          have hlen_pre : (elimRec (n + 1) false skip 0 (C.gates.take g_next.val) init).1.length = n + 1 + g_next.val := by
            rw [elimRec_fst_length, chainInitStats_length, List.length_take_of_le (by omega)]
          have hlen_succ : (elimRec (n + 1) false skip 0 (C.gates.take (g_next.val + 1)) init).1.length = n + 1 + g_next.val + 1 := by
            rw [elimRec_fst_length, chainInitStats_length, List.length_take_of_le (by omega)]; omega
          have hfw_lt : frontWire n cs < n + 1 + g_next.val := reach_implies_lt hcl ⟨g_next, rfl, hg_read⟩
          have hfw_pre : (elimRec (n + 1) false skip 0 (C.gates.take g_next.val) init).1.getD (frontWire n cs) (Sum.inl false) = Sum.inl false := by
            have h := hfront_stat
            change (elimRec (n + 1) false skip 0 C.gates init).1.getD (frontWire n cs) (Sum.inl false) = Sum.inl false at h
            rw [elimRec_take_getD (n + 1) false skip C.gates init g_next.val (frontWire n cs)
              (by rw [chainInitStats_length, List.length_take_of_le (by omega)]; omega)] at h
            exact h
          obtain ⟨b, hb⟩ : ∃ b : Bool, res.1.getD (n + 1 + g_next.val) (Sum.inl false) = Sum.inl b := by
            have heq_res : res.1.getD (n + 1 + g_next.val) (Sum.inl false) =
                (elimRec (n + 1) false skip 0 (C.gates.take (g_next.val + 1)) init).1.getD (n + 1 + g_next.val) (Sum.inl false) :=
              elimRec_take_getD (n + 1) false skip C.gates init (g_next.val + 1) (n + 1 + g_next.val)
                (by rw [chainInitStats_length, List.length_take_of_le (by omega)]; omega)
            rw [heq_res, elimRec_step_at _ _ _ _ _ g_next.val g_next.isLt]
            unfold elimStep
            simp only [hsk_g, Bool.false_eq_true, ↓reduceIte]
            rw [getD_snoc_len _ _ _ _ hlen_pre]
            have hgj : C.gates[g_next.val]'g_next.isLt = C.gates.get g_next := rfl
            rw [hgj]
            apply simplify_const_of_not_or_and_false false _ _ _ (Or.inl hop)
              (by rw [List.length_map]; exact (activeInputs_length_le _).trans hokg.2)
              (fun hn => by rw [List.length_map]; exact activeInputs_not_length _ hn)
            exact List.mem_map.2 ⟨frontWire n cs, (mem_activeInputs_iff C g_next _).2 hg_read, hfw_pre⟩
          have hg_ne_out : C.output ≠ n + 1 + g_next.val := by
            intro heq; rw [heq, hb] at hout'_eq; cases hout'_eq
          rcases min_used hmin g_next with ho | ⟨g2, hg2_read⟩
          · exact hg_ne_out ho
          · have hg2_gt : g_next.val < g2.val := by
              have := reach_implies_lt hcl ⟨g2, rfl, hg2_read⟩; omega
            have hg2_ne : g2 ≠ g_next := fun h => by subst h; omega
            have hg2_notin : g2 ∉ cs := by
              intro hmem
              have hle := frontWire_ge_mem n hgc.1 g2 hmem
              omega
            let S : Finset (Fin C.gates.length) := insert g2 (insert g_next cs.toFinset)
            have hS_drop : ∀ p ∈ S, isDropped (n + 1) false skip C.gates init p.val := by
              intro p hp
              simp only [S, Finset.mem_insert, List.mem_toFinset] at hp
              rcases hp with rfl | rfl | hmem
              · exact hdrop_of_const_in p (n + 1 + g_next.val) b hg2_read hb
              · exact hdrop_of_const_in p (frontWire n cs) false hg_read hfront_stat
              · exact hcs_dropped p hmem
            have hcard1 : (insert g_next cs.toFinset).card = cs.length + 1 := by
              rw [Finset.card_insert_of_notMem (by simp [hg_notin]), hcs_card]
            have hcard2 : S.card = cs.length + 2 := by
              rw [Finset.card_insert_of_notMem (by simp [hg2_ne, hg2_notin]), hcard1]
            have hge := dropCount_ge_card_dropped (n + 1) false skip C.gates init S hS_drop
            omega
      -- Now construct GoodChain n C (cs ++ [g_next])!
      have hg_clean := hcl g_next
      rcases hg_clean with ⟨hnot, _⟩ | ⟨_, a, b, hin, hab, ha_lt, hb_lt⟩
      · rw [hg_or] at hnot; cases hnot
      · have hfw_in : frontWire n cs ∈ (C.gates.get g_next).inputs := by
          rcases hg_read with ⟨hnot, _⟩ | ⟨_, hmem⟩
          · rw [hg_or] at hnot; cases hnot
          · exact hmem
        have hfw_ab : frontWire n cs ∈ [a, b] := by rw [← hin]; exact hfw_in
        obtain ⟨w_other, hw_in, hw_ne_f, hw_lt⟩ :
            ∃ w ∈ (C.gates.get g_next).inputs, w ≠ frontWire n cs ∧ w < n + 1 + g_next.val := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hfw_ab
          rcases hfw_ab with rfl | rfl
          · exact ⟨b, by rw [hin]; simp, hab.symm, hb_lt⟩
          · exact ⟨a, by rw [hin]; simp, hab, ha_lt⟩
        have hw_read : Reads C g_next w_other := Or.inr ⟨(by rw [hg_or]; intro h; cases h), hw_in⟩
        obtain ⟨hw_nen, hw_nr⟩ :=
          not_reach_of_lt_front hcl hgc g_next hg_read hg_uniq w_other hw_lt hw_ne_f hw_read
        right
        refine ⟨g_next, ?_, ?_, ?_⟩
        · rw [List.pairwise_append]
          refine ⟨hgc.1, List.pairwise_singleton _ _, ?_⟩
          intro p hp q hq
          simp only [List.mem_singleton] at hq
          rw [hq]
          have hle := frontWire_ge_mem n hgc.1 p hp
          have hlt := reach_implies_lt hcl ⟨g_next, rfl, hg_read⟩
          exact show p.val < g_next.val by omega
        · intro j hj
          rcases List.mem_append.1 hj with h1 | h2
          · exact hgc.2.1 j h1
          · simp only [List.mem_singleton] at h2; subst h2
            exact ⟨hg_or, by rw [hin]; rfl⟩
        · intro i hi
          rw [List.length_append, List.length_singleton] at hi
          by_cases hlt_i : i < cs.length
          · have hget_i : (cs ++ [g_next])[i]'(by simp; omega) = cs[i]'hlt_i :=
              List.getElem_append_left hlt_i
            have hprev_eq : (if h0 : i = 0 then n else n + 1 + ((cs ++ [g_next])[i - 1]'(by simp; omega)).val) =
                (if h0 : i = 0 then n else n + 1 + (cs[i - 1]'(by omega)).val) := by
              split_ifs with h0
              · rfl
              · rw [List.getElem_append_left (by omega)]
            simp only [hget_i, hprev_eq]
            exact hgc.2.2 i hlt_i
          · have hi_eq : i = cs.length := by omega
            subst hi_eq
            have hget_last : (cs ++ [g_next])[cs.length]'(by simp) = g_next := by
              rw [List.getElem_append_right le_rfl]; simp
            have hprev_eq : (if h0 : cs.length = 0 then n else n + 1 + ((cs ++ [g_next])[cs.length - 1]'(by rw [List.length_append, List.length_singleton]; omega)).val) =
                frontWire n cs := by
              split_ifs with h0
              · have hnil := List.eq_nil_of_length_eq_zero h0
                simp [frontWire, hnil]
              · rw [List.getElem_append_left (by omega)]
                have hgl : cs.getLast? = some (cs[cs.length - 1]'(by omega)) := by
                  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
                simp [frontWire, hgl]
            simp only [hget_last, hprev_eq]
            exact ⟨hfw_in, hg_uniq, w_other, hw_in, hw_ne_f, hw_nen, hw_lt, hw_nr⟩
    · -- No gate reads frontWire n cs!
      push Not at hex_read
      cases hlast : cs.getLast? with
      | none =>
        -- cs = [], so no gate reads wire n! Then C(y0, false) = C(y0, true), contradiction!
        exfalso
        have hnil := List.getLast?_eq_none_iff.1 hlast
        have hfw : frontWire n cs = n := by simp [frontWire, hnil]
        rw [hfw] at hex_read
        obtain ⟨y0, hy0⟩ := hH01.1
        have hagree : ∀ w < n + 1 + C.gates.length, w ≠ n →
            wireVal C (withLast y0 false) w = wireVal C (withLast y0 true) w := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw_lt hwn
            by_cases hlt_n : w < n
            · unfold wireVal
              rw [wires_eq, getD_wiresFrom _ _ w (by simp; omega), wires_eq, getD_wiresFrom _ _ w (by simp; omega),
                getD_ofFn_withLast, getD_ofFn_withLast]
              simp [hlt_n]
            · have hj_lt : w - (n + 1) < C.gates.length := by omega
              let j : Fin C.gates.length := ⟨w - (n + 1), hj_lt⟩
              have hw_eq : w = n + 1 + j.val := by simp [j]; omega
              rw [hw_eq, wireVal_gate_clean C hcl (withLast y0 false) j,
                wireVal_gate_clean C hcl (withLast y0 true) j]
              congr 1
              apply List.map_congr_left
              intro a ha
              have halt : a < w := by rw [hw_eq]; exact cleanGate_active_lt (hcl j) a ha
              have hane : a ≠ n := by
                intro heq
                rw [heq] at ha
                exact hex_read j ((mem_activeInputs_iff C j n).1 ha)
              exact ih a halt (by omega) hane
        have h0 := hCF_withLast y0 false
        have h1 := hCF_withLast y0 true
        have heq := hagree C.output hout_lt hout_ne_n
        rw [h0, h1] at heq
        simp [hy0] at heq
      | some last =>
        have hfw : frontWire n cs = n + 1 + last.val := by simp [frontWire, hlast]
        rw [hfw] at hex_read
        have hout_eq : C.output = n + 1 + last.val := by
          rcases min_used hmin last with ho | ⟨j', hj'⟩
          · exact ho
          · exact absurd hj' (hex_read j')
        have hlast_end := min_out_last hmin hCnc last hout_eq
        exact Or.inl ⟨last, rfl, hlast_end, hout_eq⟩

theorem build_full_chain {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool}
    (hmin : IsMinimalCircuit (n + 1) C)
    (hHnc : ∃ y y' : Fin n → Bool, H y ≠ H y')
    (hCF : ∀ x : Fin (n + 1) → Bool,
      circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) :
    ∀ rem : ℕ, ∀ cs : List (Fin C.gates.length),
      GoodChain n C cs → C.gates.length - cs.length ≤ rem →
      ∃ cs' : List (Fin C.gates.length), GoodChain n C cs' ∧
        ∃ last : Fin C.gates.length, cs'.getLast? = some last ∧
          last.val + 1 = C.gates.length ∧ C.output = n + 1 + last.val := by
  intro rem
  induction rem with
  | zero =>
    intro cs hgc hrem
    rcases extend_chain hmin hHnc hCF cs hgc with hdone | ⟨g_next, hgc'⟩
    · exact ⟨cs, hgc, hdone⟩
    · exfalso
      have hnd : (cs ++ [g_next]).Nodup := hgc'.1.imp (fun {a b} h => ne_of_lt h)
      have hcard_le : (cs ++ [g_next]).toFinset.card ≤ Fintype.card (Fin C.gates.length) :=
        Finset.card_le_univ _
      rw [List.toFinset_card_of_nodup hnd, Fintype.card_fin, List.length_append, List.length_singleton] at hcard_le
      omega
  | succ rem ih =>
    intro cs hgc hrem
    rcases extend_chain hmin hHnc hCF cs hgc with hdone | ⟨g_next, hgc'⟩
    · exact ⟨cs, hgc, hdone⟩
    · apply ih (cs ++ [g_next]) hgc'
      rw [List.length_append, List.length_singleton]
      omega

theorem main (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (hmin : IsMinimalCircuit (n + 1) C)
    (hHnc : ∃ y y' : Fin n → Bool, H y ≠ H y')
    (hCF : ∀ x : Fin (n + 1) → Bool,
      circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) :
    ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length),
      StrictMono c ∧
      (c (Fin.last k)).val + 1 = C.gates.length ∧
      C.output = n + 1 + (c (Fin.last k)).val ∧
      (∀ i : Fin (k + 1), (C.gates.get (c i)).op = GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧
      n ∈ (C.gates.get (c 0)).inputs ∧
      (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧
      (∀ j : Fin C.gates.length, Reads C j n → j = c 0) ∧
      (∀ (i : Fin k) (j : Fin C.gates.length), Reads C j (n + 1 + (c i.castSucc).val) → j = c i.succ) ∧
      (∀ j : Fin C.gates.length, Reach C (n + 1) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧
      (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Reach C (n + 1) n w) ∧
      (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs,
        w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Reach C (n + 1) n w) := by
  have hgc0 : GoodChain n C [] := ⟨List.Pairwise.nil, by simp, by simp⟩
  obtain ⟨cs, hgc, last, hlast, hlast_end, hout_eq⟩ :=
    build_full_chain hmin hHnc hCF C.gates.length [] hgc0 (by simp)
  have hpos : 0 < cs.length := by
    cases hcs : cs with
    | nil => simp [hcs] at hlast
    | cons _ _ => simp
  let k := cs.length - 1
  have hk_len : cs.length = k + 1 := by omega
  let c : Fin (k + 1) → Fin C.gates.length := fun i => cs[i.val]'(by omega)
  have hc_last : c (Fin.last k) = last := by
    rw [List.getLast?_eq_getElem?] at hlast
    have hk_eq : cs.length - 1 = k := rfl
    rw [hk_eq, List.getElem?_eq_getElem (by omega)] at hlast
    exact Option.some.inj hlast
  have hCnc : ∃ x x' : Fin (n + 1) → Bool, circuitFun (n + 1) C x ≠ circuitFun (n + 1) C x' := by
    obtain ⟨y, y', hne⟩ := hHnc
    have h0 : ∃ y0, H y0 = false := by
      cases hy : H y <;> cases hy' : H y'
      · exact ⟨y, hy⟩
      · exact ⟨y, hy⟩
      · exact ⟨y', hy'⟩
      · exact absurd (hy.trans hy'.symm) hne
    obtain ⟨y0, hy0⟩ := h0
    refine ⟨withLast y0 false, withLast y0 true, ?_⟩
    rw [hCF, hCF]; simp [withLast_last, withLast_castSucc, hy0]
  have hcl := min_clean hmin hCnc
  refine ⟨k, c, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- StrictMono c
    intro i j hij
    exact List.pairwise_iff_getElem.1 hgc.1 i.val j.val (by omega) (by omega) hij
  · rw [hc_last]; exact hlast_end
  · rw [hc_last]; exact hout_eq
  · intro i; exact hgc.2.1 (c i) (List.getElem_mem _)
  · have h0 := (hgc.2.2 0 hpos).1
    simp only [dite_true] at h0
    exact h0
  · intro i
    have hs := (hgc.2.2 (i.val + 1) (by omega)).1
    have hne0 : i.val + 1 ≠ 0 := by omega
    simp only [hne0, dite_false, Nat.add_sub_cancel] at hs
    exact hs
  · intro j hj
    have h0 := (hgc.2.2 0 hpos).2.1
    simp only [dite_true] at h0
    exact h0 j hj
  · intro i j hj
    have hs := (hgc.2.2 (i.val + 1) (by omega)).2.1
    have hne0 : i.val + 1 ≠ 0 := by omega
    simp only [hne0, dite_false, Nat.add_sub_cancel] at hs
    exact hs j hj
  · intro j
    constructor
    · intro hr
      rcases reach_of_goodChain hcl hgc (n + 1 + j.val) hr with ⟨p, hp, hpeq⟩ | hfr
      · have hjp : j = p := Fin.ext (by omega)
        subst hjp
        obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.1 hp
        exact ⟨⟨idx, by omega⟩, rfl⟩
      · exfalso
        have hlt := reach_trans_lt hcl hfr
        have hfw : frontWire n cs = n + 1 + last.val := by simp [frontWire, hlast]
        rw [hfw] at hlt
        omega
    · rintro ⟨i, rfl⟩
      exact mem_goodChain_reach hgc (c i) (List.getElem_mem _)
  · have h0 := (hgc.2.2 0 hpos).2.2
    simp only [dite_true] at h0
    obtain ⟨w, hw1, hw2, _, hw4, hw5⟩ := h0
    exact ⟨w, hw1, hw2, hw4, hw5⟩
  · intro i
    have hs := (hgc.2.2 (i.val + 1) (by omega)).2.2
    have hne0 : i.val + 1 ≠ 0 := by omega
    simp only [hne0, dite_false, Nat.add_sub_cancel] at hs
    exact hs

end PEqualNP.Outside.L_meta_568_aux

theorem PEqualNP.Outside.L_meta_568 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) :=
  PEqualNP.Outside.L_meta_568_aux.main
