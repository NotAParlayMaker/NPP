import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3223_aux

-- The constant propagation pass is adapted from L-meta-2507, L-meta-2038 and L-meta-551.
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


lemma falseAbsorbs (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hn : op = GateOp.not → ins.length ≤ 1) (hf : Sum.inl false ∈ ins) :
    ∃ b, (simplifyGate op m ins).2 = Sum.inl b := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · have := hn rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]

def observed (g : Gate) (v : List Bool) := g.op.eval (g.inputs.map fun j => v.getD j false)

lemma changedOperand (g : Gate) (a b : List Bool) (hd : observed g a ≠ observed g b) :
    ∃ j ∈ g.inputs, a.getD j false ≠ b.getD j false := by
  by_contra! he
  exact hd (congrArg g.op.eval (List.map_congr_left he))

lemma savings (m i out : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (u v : List Bool) (q : ℕ) (hq : q ≤ 2)
    (og : ∀ g ∈ gs, NOkGate g)
    (noOr : q = 2 → ∀ g ∈ gs, g.op = GateOp.or → i ∉ g.inputs)
    (lu : u.length = acc.1.length) (lv : v.length = acc.1.length)
    (marked : 0 < q → ∀ j, u.getD j false ≠ v.getD j false →
      ∃ b, acc.1.getD j (.inl false) = .inl b)
    (initial : q = 2 → ∀ j, u.getD j false ≠ v.getD j false →
      j = i ∧ acc.1.getD j (.inl false) = .inl false)
    (different : (wiresFrom gs u).getD out false ≠ (wiresFrom gs v).getD out false)
    (variableOut : ∃ w, (elimPass m gs acc).1.getD out (.inl false) = .inr w) :
    (elimPass m gs acc).2.length + q ≤ acc.2.length + gs.length := by
  induction gs generalizing acc u v q with
  | nil =>
    by_cases pos : 0 < q
    · obtain ⟨_, h⟩ := marked pos out different
      obtain ⟨_, h'⟩ := variableOut
      change acc.1.getD out (.inl false) = _ at h'
      rw [h] at h'
      contradiction
    · simp [show q = 0 by omega, elimPass]
  | cons g gs ih =>
    let ins := g.inputs.map fun j => acc.1.getD j (.inl false)
    let part := simplifyGate g.op (m + acc.2.length) ins
    let spent := part.1.toList.length
    let next := elimStep m acc g
    let u' := u ++ [observed g u]
    let v' := v ++ [observed g v]
    have lenS : next.2.length = acc.2.length + spent := List.length_append
    have one : spent ≤ 1 := toList_opt_len_le _
    let q' := q - (1 - spent)
    have small : q' ≤ 2 := by dsimp [q']; omega
    have lug : u'.length = next.1.length := by simp [u',next,elimStep,lu]
    have lvg : v'.length = next.1.length := by simp [v',next,elimStep,lv]
    have og₀ := og g List.mem_cons_self
    have onChange (hc : observed g u ≠ observed g v) (hqpos : 0 < q) : spent = 0 := by
      obtain ⟨j,hj,hd⟩ := changedOperand g u v hc
      obtain ⟨b,hb⟩ := marked hqpos j hd
      have none : part.1 = Option.none := simplifyGate_none_of_const _ _ _ og₀.1.1
        (by simpa [ins] using og₀.1.2) (fun e => by simpa [ins] using og₀.2 e)
        ⟨b,List.mem_map.mpr ⟨j,hj,hb⟩⟩
      simp [spent,none]
    have oldU (j) (hj : j ≠ acc.1.length) : u'.getD j false = u.getD j false :=
      getD_snoc_ne _ _ _ _ (fun e => hj (e.trans lu))
    have oldV (j) (hj : j ≠ acc.1.length) : v'.getD j false = v.getD j false :=
      getD_snoc_ne _ _ _ _ (fun e => hj (e.trans lv))
    have oldA (j) (hj : j ≠ acc.1.length) :
        next.1.getD j (.inl false) = acc.1.getD j (.inl false) :=
      getD_snoc_ne _ _ _ _ hj
    have newU : u'.getD acc.1.length false = observed g u := getD_snoc_eq _ _ _ _ lu.symm
    have newV : v'.getD acc.1.length false = observed g v := getD_snoc_eq _ _ _ _ lv.symm
    have newA : next.1.getD acc.1.length (.inl false) = part.2 := getD_snoc_eq _ _ _ _ rfl
    have posQ : 0 < q' → 0 < q := by dsimp [q']; omega
    have twoQ : q' = 2 → q = 2 := by dsimp [q']; omega
    have nextMarked : 0 < q' → ∀ j, u'.getD j false ≠ v'.getD j false →
        ∃ b, next.1.getD j (.inl false) = .inl b := by
      intro pos j hd
      by_cases hj : j = acc.1.length
      · subst j
        rw [newU,newV] at hd
        have zero := onChange hd (posQ pos)
        have two : q = 2 := by dsimp [q'] at pos; omega
        obtain ⟨w,hw,hdw⟩ := changedOperand g u v hd
        obtain ⟨rfl,hwf⟩ := initial two w hdw
        have hop : g.op = GateOp.and ∨ g.op = GateOp.not :=
          og₀.1.1.elim Or.inl (fun h => h.elim (fun e => (noOr two g List.mem_cons_self e hw).elim) Or.inr)
        rw [newA]
        exact falseAbsorbs _ _ _ hop (by simpa [ins] using og₀.1.2)
          (fun e => by simpa [ins] using og₀.2 e) (List.mem_map.mpr ⟨_,hw,hwf⟩)
      · rw [oldU j hj,oldV j hj] at hd
        rw [oldA j hj]
        exact marked (posQ pos) j hd
    have nextInitial : q' = 2 → ∀ j, u'.getD j false ≠ v'.getD j false →
        j = i ∧ next.1.getD j (.inl false) = .inl false := by
      intro two j hd
      by_cases hj : j = acc.1.length
      · subst j
        rw [newU,newV] at hd
        have zero := onChange hd (by have := twoQ two; omega)
        dsimp [q'] at two
        omega
      · rw [oldU j hj,oldV j hj] at hd
        rw [oldA j hj]
        exact initial (twoQ two) j hd
    have saved := ih next u' v' q' small (fun g hg => og g (List.mem_cons_of_mem _ hg))
      (fun two g hg => noOr (twoQ two) g (List.mem_cons_of_mem _ hg))
      lug lvg nextMarked nextInitial different variableOut
    change (elimPass m gs next).2.length + q ≤ acc.2.length + (gs.length + 1)
    rw [lenS] at saved
    dsimp [q'] at saved
    omega


def assignment {m : ℕ} (w : List (Option (Fin m))) : List (Bool ⊕ ℕ) × List Gate :=
  (w.map (fun t => t.elim (.inl false) (fun j => .inr j.val)), [])

lemma assignment_sound {m : ℕ} (w : List (Option (Fin m))) (x : Fin m → Bool) :
    ElimInv m (List.ofFn x) (w.map fun t => t.elim false x) (assignment w) := by
  refine ⟨by simp, by simp [assignment], ?_⟩
  intro j
  cases hj : w[j]? with
  | none => simp [assignment,List.getD_eq_getElem?_getD,List.getElem?_map,hj,statValid,statVal]
  | some t =>
    cases t with
    | none => simp [assignment,List.getD_eq_getElem?_getD,List.getElem?_map,hj,statValid,statVal]
    | some a =>
      simp [assignment,List.getD_eq_getElem?_getD,List.getElem?_map,hj,
        statValid,statVal,wiresFrom,a.isLt]

end PEqualNP.Outside.L_meta_3223_aux

open PEqualNP.Outside.L_meta_3223_aux

theorem PEqualNP.Outside.L_meta_3223 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List (Option (Fin x1))) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x3[x4]? = Option.some Option.none → x5 ≤ (1 : ℕ) → (x5 = (1 : ℕ) → ∀ x10 ∈ x2.gates, x10.op = PEqualNP.CircuitLowerBounds.GateOp.or → x4 ∉ x10.inputs) → (∃ (x10 : List Bool) (x11 : List Bool), x10.length = x3.length ∧ x11.length = x3.length ∧ (∀ (x12 : ℕ), x12 ≠ x4 → x10.getD x12 Bool.false = x11.getD x12 Bool.false) ∧ x2.eval x10 ≠ x2.eval x11) → (∃ (x11 : Fin x1 → Bool) (x12 : Fin x1 → Bool), x2.eval (List.map (fun (x13 : Option (Fin x1)) => x13.elim Bool.false x11) x3) ≠ x2.eval (List.map (fun (x13 : Option (Fin x1)) => x13.elim Bool.false x12) x3)) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x12 ∧ x12.size + (x5 + (1 : ℕ)) ≤ x2.size ∧ ∀ (x13 : Fin x1 → Bool), x12.eval (List.ofFn x13) = x2.eval (List.map (fun (x14 : Option (Fin x1)) => x14.elim Bool.false x13) x3) := by
  intro m C w i k hf pin hk noOr sensitive nonconstant
  let gs := C.gates.map normGate
  let acc := elimPass m gs (assignment w)
  have ok (g) (hg : g ∈ gs) : NOkGate g := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok _ (hf _ ha)
  have eval (v : List Bool) : C.eval v = (wiresFrom gs v).getD C.output false :=
    (congrArg (fun ws => ws.getD C.output false) (wiresFrom_norm C.gates v)).symm
  have result (x : Fin m → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (.inl false)) =
        C.eval (w.map fun t => t.elim false x) := by
    rw [eval]
    exact ((elimInv_pass _ _ _ _ _ (fun g hg => (ok g hg).1)
      (assignment_sound w x)).2.2 C.output).2
  cases e : acc.1.getD C.output (.inl false) with
  | inl b =>
    obtain ⟨x,y,hd⟩ := nonconstant
    have hx := result x
    have hy := result y
    rw [e] at hx hy
    exact (hd (hx.symm.trans hy)).elim
  | inr j =>
    refine ⟨⟨acc.2,j⟩,elimPass_ok _ _ _ (by simp [assignment]),?_,?_⟩
    · obtain ⟨u,v,hu,hv,honly,hd⟩ := sensitive
      have only (t) (h : u.getD t false ≠ v.getD t false) : t = i := by
        by_contra ne
        exact h (honly t ne)
      have marker : (assignment w).1.getD i (.inl false) = .inl false := by
        simp [assignment,List.getD_eq_getElem?_getD,List.getElem?_map,pin]
      have nor (two : k + 1 = 2) (g) (hg : g ∈ gs) (ho : g.op = GateOp.or) : i ∉ g.inputs := by
        obtain ⟨⟨op,ins⟩,ha,rfl⟩ := List.mem_map.mp hg
        cases op <;> simp [normGate] at ho ⊢
        exact noOr (by omega) _ ha rfl
      rw [eval,eval] at hd
      have bound := savings m i C.output gs (assignment w) u v (k+1) (by omega) ok nor
        (by simpa [assignment] using hu) (by simpa [assignment] using hv)
        (fun _ t h => ⟨false,only t h ▸ marker⟩)
        (fun _ t h => ⟨only t h,only t h ▸ marker⟩) hd ⟨j,e⟩
      simpa [Circuit.size,acc,gs,assignment] using bound
    · intro x
      have hx := result x
      rwa [e] at hx
