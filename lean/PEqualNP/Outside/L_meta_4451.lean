import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4451_aux

-- Wire tables and constant propagation are adapted from L-meta-2038 and L-meta-551.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

lemma simplifyGate_nok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, NOkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; exact ⟨⟨Or.inl rfl, by simp⟩, by simp⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; exact ⟨⟨Or.inr (Or.inl rfl), by simp⟩, by simp⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; exact ⟨⟨Or.inr (Or.inr rfl), by simp⟩, by simp⟩
  · simp at hg
  · simp at hg

lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)


lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplifyGate op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]
def cutRead (n : Nat) (g : Gate) : Bool := g.inputs.contains n

lemma cut_count (m n : Nat) (c : Bool) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (ok : ∀ g ∈ gs, NOkGate g) (inside : n < acc.1.length)
    (marker : acc.1.getD n (.inl false) = .inl c) :
    (elimPass m gs acc).2.length + gs.countP (cutRead n) ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    let ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
    let part := simplifyGate g.op (m + acc.2.length) ins
    have hn : n < (elimStep m acc g).1.length := by simp [elimStep]; omega
    have hm : (elimStep m acc g).1.getD n (.inl false) = .inl c := by
      unfold elimStep; rw [getD_snoc_lt _ _ _ _ inside,marker]
    have ht := ih (elimStep m acc g) (fun a ha => ok a (List.mem_cons_of_mem _ ha)) hn hm
    have add : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      change (acc.2 ++ part.1.toList).length ≤ _
      rw [List.length_append]; exact Nat.add_le_add_left (toList_opt_len_le _) _
    rw [elimPass_cons,List.countP_cons,List.length_cons]
    cases e : cutRead n g with
    | false => simp only [Bool.false_eq_true,↓reduceIte]; omega
    | true =>
      have hit : n ∈ g.inputs := by simpa [cutRead] using e
      have og := ok g List.mem_cons_self
      have epart : part.1 = none := by
        apply simplifyGate_none_of_const _ _ _ og.1.1
        · simpa [ins] using og.1.2
        · intro he; simpa [ins] using og.2 he
        · exact ⟨c,List.mem_map.mpr ⟨n,hit,marker⟩⟩
      have eLen : (elimStep m acc g).2.length = acc.2.length := by
        change (acc.2 ++ part.1.toList).length = _; simp [epart]
      simp only [↓reduceIte]; omega

lemma cut_agree (n : Nat) (gs : List Gate) (no : ∀g∈gs, n∉g.inputs) (v w : List Bool)
    (len : v.length=w.length) (agree : ∀ i, i≠n → v.getD i false = w.getD i false) :
    ∀ i, i≠n → (wiresFrom gs v).getD i false = (wiresFrom gs w).getD i false := by
  induction gs generalizing v w with
  | nil => exact agree
  | cons g gs ih =>
    rw [wiresFrom_cons,wiresFrom_cons]
    have val : g.inputs.map (fun i => v.getD i false) = g.inputs.map (fun i => w.getD i false) := by
      exact List.map_congr_left (fun i hi => agree i (fun h => no g List.mem_cons_self (h ▸ hi)))
    rw [val]
    apply ih (fun g hg => no g (List.mem_cons_of_mem _ hg)) _ _ (by simp [len])
    intro i hn
    by_cases h : i=v.length
    · rw [getD_snoc_eq _ _ _ _ h,getD_snoc_eq _ _ _ _ (h.trans len)]
    · rw [getD_snoc_ne _ _ _ _ h,getD_snoc_ne _ _ _ _ (by omega)]
      exact agree i hn

-- The elimination pass and accounting above are from L-meta-2507.
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def start {n : Nat} (v : Fin n) : List (Bool ⊕ Nat) × List Gate :=
  (List.ofFn (fun j : Fin n => if j = v then Sum.inl false else Sum.inr j.val), [])

def off {n : Nat} (v : Fin n) (x : Fin n → Bool) (j : Fin n) := if j = v then false else x j

lemma initInv {n} (v : Fin n) (x : Fin n → Bool) :
    ElimInv n (List.ofFn x) (List.ofFn (off v x)) (start v) := by
  refine ⟨by simp, by simp [start], fun i => ?_⟩
  by_cases hi : i < n
  · simp [start, List.getD_eq_getElem?_getD, hi, wiresFrom, off]
    split <;> simp_all [statVal,statValid,List.getD_eq_getElem?_getD]
  · simp [start, List.getD_eq_getElem?_getD, hi, statVal,statValid]

def Good (n : Nat) (gs : List Gate) := ∀ j (hj : j < gs.length),
  let g := gs[j]
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < n+j

lemma goodAO {n gs out} (h : Good n gs) : IsAO2 n ⟨gs,out⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
    exact (h i hi).1
  · intro j hj
    simpa [gateAt,List.getD_eq_getElem?_getD,hj] using (h j hj).2.2
  · intro g hg
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
    exact (h i hi).2.1

lemma appendGood {n gs g} (h : Good n gs)
    (hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < n+gs.length) :
    Good n (gs ++ [g]) := by
  intro j hj
  by_cases hj' : j < gs.length
  · simpa [List.getElem_append_left,hj'] using h j hj'
  · have he : j = gs.length := by simp at hj; omega
    subst j
    simpa using hg

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wv (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

lemma wv_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wv (gs ++ [g]) x = step (wv gs x) g := by
  simp [wv, List.foldl_append]

lemma wv_len (gs : List Gate) (x : List Bool) : (wv gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wv]
  | append_singleton gs g ih =>
    rw [wv_snoc]
    simp [step, ih]
    omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false = if i < w.length then w.getD i false
      else if i = w.length then g.op.eval (g.inputs.map fun k => w.getD k false) else false := by
  unfold step
  rcases lt_trichotomy i w.length with hi | hi | hi
  · rw [List.getD_append _ _ _ _ hi]
    simp [hi]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hi]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, i - w.length = k + 1 := ⟨i - w.length - 1, by omega⟩
    have h1 : ¬ i < w.length := by omega
    have h2 : i ≠ w.length := by omega
    rw [hk]
    simp [h1, h2]


lemma mono (gs : List Gate) (x y : List Bool) (hl : x.length = y.length)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∀ i, (wv gs x).getD i false = true → (wv gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ i h
    exact hxy i h
  | append_singleton gs g ih =>
    intro hm i h
    have ih' := ih (fun g' hg' => hm g' (by simp [hg']))
    have hg := hm g (by simp)
    rw [wv_snoc, step_getD, wv_len] at h ⊢
    rw [← hl]
    by_cases hi : i < x.length + gs.length
    · simp only [hi, ite_true] at h ⊢
      exact ih' i h
    · by_cases hi2 : i = x.length + gs.length
      · simp only [hi2, ite_true, ite_false, lt_irrefl] at h ⊢
        rcases hg.1 with ho | ho
        · rw [ho] at h ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at h ⊢
          rintro b ⟨k, hk, rfl⟩
          exact ih' k (h _ ⟨k, hk, rfl⟩)
        · rw [ho] at h ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at h ⊢
          obtain ⟨b, ⟨k, hk, rfl⟩, hb⟩ := h
          exact ⟨_, ⟨k, hk, rfl⟩, ih' k hb⟩
      · simp [hi, hi2] at h

lemma ofFn_getD (n : ℕ) (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> simp

lemma cf_eq (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    PEqualNP.MetaComplexity.circuitFun n C x = (wv C.gates (List.ofFn x)).getD C.output false :=
  rfl

lemma mono2 (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
  fun g hg => ⟨(hM g hg).1, (hM g hg).2⟩

lemma cf_mono (n : ℕ) (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (h : PEqualNP.MetaComplexity.circuitFun n C x = true) :
    PEqualNP.MetaComplexity.circuitFun n C y = true := by
  rw [cf_eq] at h ⊢
  refine mono C.gates _ _ (by simp) ?_ (mono2 C hM) _ h
  intro i hi
  rw [ofFn_getD] at hi ⊢
  by_cases hin : i < n
  · simp only [hin, dite_true] at hi ⊢
    exact hxy _ hi
  · simp [hin] at hi

lemma passGood (n : Nat) (gs : List Gate) (acc : List (Bool ⊕ Nat) × List Gate)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (u v : List Bool) (hin : ElimInv n u v acc)
    (hg : Good n acc.2) : Good n (elimPass n gs acc).2 := by
  induction gs generalizing acc v with
  | nil => exact hg
  | cons g gs ih =>
    have og := h g List.mem_cons_self
    have ok : OkGate g := by rcases og with ⟨ha|ha,hl⟩ <;> simp [OkGate,ha,hl]
    apply ih (elimStep n acc g) (fun a ha => h a (List.mem_cons_of_mem _ ha)) _
      (elimInv_step n u v acc g ok hin)
    obtain ⟨a,b,hins⟩ : ∃ a b, g.inputs = [a,b] := by
      have hl := og.2
      cases e : g.inputs with
      | nil => simp [e] at hl
      | cons a l =>
        cases l with
        | nil => simp [e] at hl
        | cons b l =>
          cases l <;> simp_all
    have va := (hin.2.2 a).1
    have vb := (hin.2.2 b).1
    cases ea : acc.1.getD a (.inl false) <;> cases eb : acc.1.getD b (.inl false) <;>
      rcases og.1 with hop|hop <;>
      simp_all [elimStep,simplifyGate,simpAnd,simpOr,statValid] <;>
      apply appendGood hg <;> simp_all

end PEqualNP.Outside.L_meta_4451_aux
open PEqualNP.Outside.L_meta_4451_aux
open PEqualNP.TopForm

theorem PEqualNP.Outside.L_meta_4451 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → x3 ≠ x4 → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x7 : Fin x1) => Decidable.decide (x7 = x3)) = Bool.false → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x8 : Fin x1) => Decidable.decide (x8 = x4)) = Bool.false → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x9 : Fin x1) => Decidable.decide (x9 = x3 ∨ x9 = x4)) = Bool.true → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x10 ∧ x10.size < x2.size ∧ (∀ (x11 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x10 x11 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 x11 = Bool.true) ∧ ∀ (x11 : Fin x1 → Bool), x11 x3 = Bool.false → PEqualNP.MetaComplexity.circuitFun x1 x10 x11 = PEqualNP.MetaComplexity.circuitFun x1 x2 x11 := by
  intro n C a b hC hab ha hb hp
  let A := start a
  let E := elimPass n C.gates A
  let z := E.1.getD C.output (.inl false)
  let out := match z with | .inr j => j | .inl _ => n + E.2.length
  let D : Circuit := ⟨E.2,out⟩
  have ops : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hC.1 g hg,hC.2.2 g hg⟩
  have norm : ∀ g ∈ C.gates, NOkGate g := by
    intro g hg
    rcases ops g hg with ⟨he|he,hl⟩ <;> simp [NOkGate,OkGate,he,hl]
  have sem (x : Fin n → Bool) := (elimInv_pass n (List.ofFn x) C.gates _ A
    (fun g hg => (norm g hg).1) (initInv a x)).2.2 C.output
  have eqv (x : Fin n → Bool) : circuitFun n D x = circuitFun n C (off a x) := by
    have hs : statVal (wiresFrom E.2 (List.ofFn x)) z = circuitFun n C (off a x) := (sem x).2
    change (wiresFrom E.2 (List.ofFn x)).getD out false = _
    cases hz : z with
    | inr j => simpa [out,hz,statVal] using hs
    | inl v =>
      have hz0 := (sem (fun j => decide (j = b))).2
      change statVal _ z = circuitFun n C (off a (fun j => decide (j = b))) at hz0
      have he : off a (fun j => decide (j = b)) = (fun j => decide (j = b)) := by
        funext j; by_cases hj : j = a <;> simp_all [off]
      rw [he,hb,hz] at hz0
      change v = false at hz0
      subst v
      rw [← hs,hz]; simp [out,hz,statVal,wiresFrom_length]
  have read : 0 < C.gates.countP (cutRead a.val) := by
    by_contra! hn
    have no : ∀ g ∈ C.gates, a.val ∉ g.inputs := by
      have hzero : C.gates.countP (cutRead a.val) = 0 := by omega
      simpa [List.countP_eq_zero,cutRead] using hzero
    have neout : C.output ≠ a.val := by
      intro bad
      change (wiresFrom C.gates (List.ofFn _)).getD C.output false = false at ha
      rw [bad,wiresFrom_getD_lt _ _ _ (by simp)] at ha
      simp [ofFn_getD] at ha
    have he := cut_agree a.val C.gates no
      (List.ofFn (fun j : Fin n => decide (j = b))) (List.ofFn (fun j : Fin n => decide (j = a ∨ j = b)))
      (by simp) (by
        intro i hi
        simp only [ofFn_getD]
        split <;> simp_all [Fin.ext_iff]) C.output neout
    change circuitFun n C _ = circuitFun n C _ at he
    rw [hb,hp] at he
    contradiction
  have sizeBound := cut_count n a.val false C.gates A norm (by simp [A,start])
    (by simp [A,start,List.getD_eq_getElem?_getD])
  refine ⟨D,goodAO (passGood n C.gates A ops _ _ (initInv a (fun _ => false)) (by simp [A,start,Good])),?_,?_,?_⟩
  · change E.2.length < C.gates.length
    change E.2.length + _ ≤ 0 + C.gates.length at sizeBound
    omega
  · intro x hx
    rw [eqv] at hx
    apply cf_mono n C (fun g hg => ⟨(ops g hg).1,by rw [(ops g hg).2]⟩) _ _ _ hx
    intro j; by_cases hj : j = a <;> simp [off,hj]
  · intro x hx
    rw [eqv]
    congr 1
    funext j; by_cases hj : j = a <;> simp_all [off]
