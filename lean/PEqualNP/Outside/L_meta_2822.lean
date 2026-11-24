import Mathlib
import PEqualNP.Defs

-- Constant propagation follows the checked proofs of L-meta-2305 and stierms, L-meta-517.
namespace PEqualNP.Outside.L_meta_2822
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
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

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

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
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
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
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
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
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
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


def ConstAt (a : List Stat × List Gate) (k : ℕ) (c : Bool) : Prop :=
  k < a.1.length ∧ a.1.getD k (Sum.inl false) = Sum.inl c

theorem const_step (n : ℕ) (a : List Stat × List Gate) (g : Gate) (k : ℕ) (c : Bool)
    (h : ConstAt a k c) : ConstAt (elimStep n a g) k c := by
  have hk := h.1
  refine ⟨by simp [elimStep]; omega, ?_⟩
  change (a.1 ++ [_]).getD k (Sum.inl false) = _
  rw [getD_snoc_ne _ _ _ _ (by omega)]
  exact h.2

theorem elim_const (n : ℕ) (gs : List Gate) (k : ℕ) (c : Bool) :
    ∀ a, ConstAt a k c → ConstAt (elim n gs a) k c := by
  induction gs with
  | nil => intro a h; exact h
  | cons g gs ih => intro a h; exact ih _ (const_step n a g k c h)

theorem elim_status_length (n : ℕ) (gs : List Gate) : ∀ a,
    (elim n gs a).1.length = a.1.length + gs.length := by
  induction gs with
  | nil => intro a; simp [elim]
  | cons g gs ih => intro a; change (elim n gs (elimStep n a g)).1.length = _; rw [ih]; simp [elimStep]; omega

theorem none_of_const (n : ℕ) (a : List Stat × List Gate) (g : Gate) (hg : NOk g)
    (k : ℕ) (c : Bool) (hc : ConstAt a k c) (hk : k ∈ g.inputs) :
    (simplify g.op (n + a.2.length) (g.inputs.map fun i => a.1.getD i (Sum.inl false))).1 = none := by
  apply simplify_count _ _ _ hg.1.1
  · simpa using hg.1.2
  · intro h; simpa using hg.2 h
  · exact ⟨c, List.mem_map.mpr ⟨k, hk, hc.2⟩⟩

theorem step_len_le (n : ℕ) (a : List Stat × List Gate) (g : Gate) :
    (elimStep n a g).2.length ≤ a.2.length + 1 := by
  simp only [elimStep, List.length_append]
  exact Nat.add_le_add_left (toList_length_le _) _

theorem step_len_const (n : ℕ) (a : List Stat × List Gate) (g : Gate) (hg : NOk g)
    (k : ℕ) (c : Bool) (hc : ConstAt a k c) (hk : k ∈ g.inputs) :
    (elimStep n a g).2.length = a.2.length := by
  simp only [elimStep, none_of_const n a g hg k c hc hk]
  simp


abbrev Acc := List Stat × List Gate
def ini (v : Fin 9) : Acc :=
  ((List.ofFn fun i : Fin 8 => (Sum.inr i.val : Stat)).insertIdx v.val (.inl false), [])
def args (v : Fin 9) (b : Bool) (x : Fin 8 → Bool) := (List.ofFn x).insertIdx v.val b
theorem startInv (v : Fin 9) (x : Fin 8 → Bool) : Inv 8 (List.ofFn x) (args v false x) (ini v) := by
  constructor
  · fin_cases v <;> simp [args,ini,List.ofFn_succ]
  intro i
  by_cases hi : i < 9
  · fin_cases v <;> interval_cases i <;> simp [args,ini,List.ofFn_succ,Stat.Valid,Stat.val,wiresFrom]
  · have h₁ : (ini v).1.length = 9 := by fin_cases v <;> decide
    have h₂ : (args v false x).length = 9 := (startLen v false x)
    rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
    exact ⟨trivial,rfl⟩
where
  startLen (v : Fin 9) (b : Bool) (x : Fin 8 → Bool) : (args v b x).length = 9 := by
    fin_cases v <;> simp [args, List.ofFn_succ]
theorem args_len (v : Fin 9) (b : Bool) (x : Fin 8 → Bool) : (args v b x).length = 9 := by
  fin_cases v <;> simp [args,List.ofFn_succ]
theorem iniConst (v : Fin 9) : ConstAt (ini v) v false := by unfold ConstAt; fin_cases v <;> decide
def Agree (E : ℕ → Prop) (a b : List Bool) :=
  a.length = b.length ∧ ∀ i, ¬ E i → a.getD i false = b.getD i false
theorem initialAgree (v : Fin 9) (x : Fin 8 → Bool) :
    Agree (· = v.val) (args v false x) (args v true x) := by
  refine ⟨by rw [args_len,args_len],?_⟩
  intro i hi
  by_cases h : i < 9
  · fin_cases v <;> interval_cases i <;> simp_all [args,List.ofFn_succ]
  · rw [List.getD_eq_default _ _ (by rw [args_len]; omega),List.getD_eq_default _ _ (by rw [args_len]; omega)]
theorem agreeSnoc {E a b} (h : Agree E a b) {u z : Bool}
    (same : ¬ E a.length → u = z) : Agree E (a ++ [u]) (b ++ [z]) := by
  obtain ⟨hl,hi⟩ := h
  refine ⟨by simp [hl],?_⟩
  intro i hout
  by_cases eq : i = a.length
  · subst i; rw [getD_snoc_eq,hl,getD_snoc_eq]; exact same hout
  · rw [getD_snoc_ne _ _ _ _ eq,getD_snoc_ne _ _ _ _ (by omega)]
    exact hi i hout
theorem agreeRun {E a b} (h : Agree E a b) (gs : List Gate)
    (avoid : ∀ g ∈ gs, ∀ i ∈ g.inputs, ¬ E i) : Agree E (wiresFrom gs a) (wiresFrom gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    apply ih (agreeSnoc h (fun _ => congrArg g.op.eval
      (List.map_congr_left (fun i hi => h.2 i (avoid g (by simp) i hi))))) (fun g hg => avoid g (by simp [hg]))
theorem tightAvoid (gs : List Gate) (a : Acc) (v : ℕ) (c : Bool)
    (good : ∀ g ∈ gs, NOk g) (hc : ConstAt a v c)
    (tight : (elim 8 gs a).2.length = a.2.length + gs.length) :
    ∀ g ∈ gs, v ∉ g.inputs := by
  induction gs generalizing a with
  | nil => simp
  | cons g gs ih =>
    change (elim 8 gs (elimStep 8 a g)).2.length = _ at tight
    have cap := elim_len 8 gs (elimStep 8 a g)
    have step := step_len_le 8 a g
    simp only [List.length_cons] at tight
    have eq : (elimStep 8 a g).2.length = a.2.length + 1 := by omega
    intro h hh
    rcases List.mem_cons.mp hh with rfl|hh
    · intro hv
      have := step_len_const 8 a h (good h (by simp)) v c hc hv
      omega
    · exact ih _ (fun g hg => good _ (by simp [hg])) (const_step 8 a g v c hc) (by omega) h hh
theorem liveReaderShape (g : Gate) (ok : NOk g) (v : ℕ) (get : ℕ → Stat)
    (fixed : get v = .inl false) (reads : v ∈ g.inputs) (m : ℕ)
    (live : ∀ c, (simplify g.op m (g.inputs.map get)).2 ≠ .inl c) :
    g.op = .or ∧ ∃ j, (g.inputs = [v,j] ∨ g.inputs = [j,v]) ∧ ∃ k, get j = .inr k := by
  rcases g with ⟨op,ins⟩
  obtain ⟨⟨ho,hl⟩,hn⟩ := ok
  change op = _ ∨ op = _ ∨ op = _ at ho
  change ins.length ≤ 2 at hl
  change v ∈ ins at reads
  change ∀ c, (simplify op m (ins.map get)).2 ≠ .inl c at live
  rcases ins with _|⟨i,_|⟨j,_|⟨k,l⟩⟩⟩
  · simp at reads
  · simp only [List.mem_singleton] at reads
    subst i
    rcases ho with rfl|rfl|rfl <;> simp [fixed,simplify,simpAnd,simpOr,simpNot] at live
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at reads
    rcases reads with rfl|rfl
    · cases he : get j with
      | inl c => rcases ho with rfl|rfl|rfl <;> cases c <;> simp [fixed,he,simplify,simpAnd,simpOr,simpNot] at live
      | inr k =>
        rcases ho with rfl|rfl|rfl
        · simp [fixed,he,simplify,simpAnd] at live
        · exact ⟨rfl,j,Or.inl rfl,k,he⟩
        · simp [fixed,he,simplify,simpNot] at live
    · cases he : get i with
      | inl c => rcases ho with rfl|rfl|rfl <;> cases c <;> simp [fixed,he,simplify,simpAnd,simpOr,simpNot] at live
      | inr k =>
        rcases ho with rfl|rfl|rfl
        · simp [fixed,he,simplify,simpAnd] at live
        · exact ⟨rfl,i,Or.inr rfl,k,he⟩
        · exact False.elim (by have := hn rfl; simp at this)
  · simp at hl

def value (gs : List Gate) (o : ℕ) (v : Fin 9) (b : Bool) (x : Fin 8 → Bool) :=
  (wiresFrom gs (args v b x)).getD o false
def Paired (gs : List Gate) (o : ℕ) (v : Fin 9) : Prop :=
  ∀ j : Fin 9, j ≠ v → ∃ x : Fin 8 → Bool, value gs o v false x ≠ value gs o v true x ∧ (args v false x).getD j false = true
theorem valInv (gs : List Gate) (ok : ∀ g ∈ gs, NOk g) (o : ℕ) (v : Fin 9) (x : Fin 8 → Bool) :
    ((elim 8 gs (ini v)).1.getD o (.inl false)).val (wiresFrom (elim 8 gs (ini v)).2 (List.ofFn x)) =
      value gs o v false x :=
  ((inv_elim 8 _ (by simp) gs _ _ (fun g h => (ok g h).1) (startInv v x)).2 o).2
theorem reprOutput (gs : List Gate) (ok : ∀ g ∈ gs, NOk g) (o : ℕ) (v : Fin 9)
    (diff : ∃ x y, value gs o v false x ≠ value gs o v false y) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = (elim 8 gs (ini v)).2.length ∧
        circuitFun 8 D = value gs o v false ∧ ∃ k, (elim 8 gs (ini v)).1.getD o (.inl false) = .inr k := by
  cases he : (elim 8 gs (ini v)).1.getD o (.inl false) with
  | inl c =>
    obtain ⟨x,y,h⟩ := diff
    have h₁ := valInv gs ok o v x
    have h₂ := valInv gs ok o v y
    rw [he] at h₁ h₂
    exact False.elim (h (h₁.symm.trans h₂))
  | inr k =>
    refine ⟨⟨_,k⟩,?_,rfl,?_,k,rfl⟩
    · exact elim_ok 8 gs _ (by simp [ini])
    · funext x
      have := valInv gs ok o v x
      rwa [he] at this
theorem pairedWitness {gs o v} (sens : Paired gs o v) :
    ∃ x, value gs o v false x ≠ value gs o v true x := by
  have hex : ∃ j : Fin 9, j ≠ v := by exact exists_ne v
  obtain ⟨j,hj⟩ := hex
  obtain ⟨x,hx,_⟩ := sens j hj
  exact ⟨x,hx⟩
theorem splitRead (gs : List Gate) (v : ℕ) (hex : ∃ g ∈ gs, v ∈ g.inputs) :
    ∃ p g t, gs = p ++ g :: t ∧ v ∈ g.inputs := by
  obtain ⟨g,hg,hr⟩ := hex
  obtain ⟨p,t,e⟩ := List.append_of_mem hg
  exact ⟨p,g,t,e,hr⟩
theorem fixedOutputNe {gs o v} (diff : ∃ x y, value gs o v false x ≠ value gs o v false y) : o ≠ (v : ℕ) := by
  rintro rfl
  obtain ⟨x,y,h⟩ := diff
  have zero (w : Fin 8 → Bool) : value gs v v false w = false := by
    unfold value
    rw [getD_wiresFrom _ _ _ (by rw [args_len]; exact v.isLt)]
    fin_cases v <;> simp [args,List.ofFn_succ]
  exact h ((zero x).trans (zero y).symm)
theorem newShape (gs : List Gate) (o : ℕ) (v : Fin 9) (ok : ∀ g ∈ gs, NOk g)
    (diff : ∃ x y, value gs o v false x ≠ value gs o v false y) (sens : Paired gs o v) :
    (∃ D : Circuit, FanInTwo D ∧ D.size+2 ≤ gs.length ∧ circuitFun 8 D = value gs o v false) ∨
    ∃ p g t j, gs = p ++ g :: t ∧ 9 ≤ j ∧ j < 9+p.length ∧
      g.op = .or ∧ (g.inputs = [v.val,j] ∨ g.inputs = [j,v.val]) ∧
      ∀ h ∈ p++t, v.val ∉ h.inputs := by
  have hout := fixedOutputNe diff
  obtain ⟨D,hD,sz,funD,k,live⟩ := reprOutput gs ok o v diff
  by_cases small : D.size+2 ≤ gs.length
  · exact Or.inl ⟨D,hD,small,funD⟩
  right
  have hx := pairedWitness sens
  have existsRead : ∃ g ∈ gs, v.val ∈ g.inputs := by
    by_contra! hn
    obtain ⟨x,hd⟩ := hx
    have h := agreeRun (initialAgree v x) gs (fun g hg i hi eq => hn g hg (eq ▸ hi))
    exact hd (h.2 _ hout)
  obtain ⟨p,g,t,rfl,reads⟩ := splitRead gs v existsRead
  let a := elim 8 p (ini v)
  let b := elimStep 8 a g
  have hgs : elim 8 (p ++ g :: t) (ini v) = elim 8 t b := by simp [elim,b,a,List.foldl_append]
  have hlen : a.1.length = 9+p.length := by
    rw [show a.1.length = (ini v).1.length+p.length from elim_status_length 8 p _]
    have nine : (ini v).1.length = 9 := by fin_cases v <;> decide
    rw [nine]
  have hpre : ∀ f ∈ p, NOk f := fun f hf => ok f (by simp [hf])
  have htail : ∀ f ∈ t, NOk f := fun f hf => ok f (by simp [hf])
  have hg : NOk g := ok g (by simp)
  have fixed : ConstAt a v false := elim_const 8 p _ _ _ (iniConst v)
  have step : b.2.length = a.2.length := step_len_const 8 a g hg v false fixed reads
  have cp := elim_len 8 p (ini v)
  have ct := elim_len 8 t b
  change a.2.length ≤ 0+p.length at cp
  rw [hgs] at sz live
  simp only [List.length_append,List.length_cons] at small
  have preT : a.2.length = (ini v).2.length+p.length := by change _ = 0+_; omega
  have tailT : (elim 8 t b).2.length = b.2.length+t.length := by omega
  have preNo := tightAvoid p (ini v) v false hpre (iniConst v) preT
  have tailNo := tightAvoid t b v false htail (const_step 8 a g v false fixed) tailT
  let z := 9+p.length
  let ins := g.inputs.map fun i => a.1.getD i (.inl false)
  let sg := (simplify g.op (8+a.2.length) ins).2
  have newConst (c) (hc : sg = .inl c) : ConstAt b z c := by
    change z < (a.1 ++ [sg]).length ∧ (a.1 ++ [sg]).getD z _ = _
    rw [← show a.1.length = z from hlen]
    exact ⟨by simp, (getD_snoc_eq _ _ _).trans hc⟩
  let pref := fun (x : Fin 8 → Bool) (flag : Bool) => wiresFrom p (args v flag x)
  let bit := fun (x : Fin 8 → Bool) (flag : Bool) => g.op.eval (g.inputs.map fun i => (pref x flag).getD i false)
  have agr (x) : Agree (· = v.val) (pref x false) (pref x true) :=
    agreeRun (initialAgree v x) p (fun f hf i hi eq => preNo f hf (eq ▸ hi))
  have prefLen (x flag) : (pref x flag).length = z := by simp [pref,z,length_wiresFrom,args_len]
  have unfoldVal (x flag) : value (p++g::t) o v flag x = (wiresFrom t (pref x flag ++ [bit x flag])).getD o false := by
    unfold value; rw [wiresFrom_append]; rfl
  have liveGate : ∀ c, sg ≠ .inl c := by
    intro c hc
    have con := newConst c hc
    have avoid := tightAvoid t b z c htail con tailT
    have outZ : o ≠ z := by
      rintro rfl
      have const := (elim_const 8 t _ _ _ con).2
      rw [const] at live
      contradiction
    obtain ⟨x,hd⟩ := hx
    have prior : Agree (fun i => i = v.val ∨ i = z) (pref x false) (pref x true) :=
      ⟨(agr x).1,fun i hi => (agr x).2 i (fun e => hi (Or.inl e))⟩
    have next := agreeSnoc (u:=bit x false) (z:=bit x true) prior (fun h => False.elim (h (Or.inr (prefLen x false))))
    have final := agreeRun next t (fun f hf i hi h => h.elim (fun e => tailNo f hf (e ▸ hi)) (fun e => avoid f hf (e ▸ hi)))
    rw [unfoldVal,unfoldVal] at hd
    exact hd (final.2 o (by simp [hout,outZ]))
  obtain ⟨op,j,hj,k',hk⟩ := liveReaderShape g hg v _ fixed.2 reads _ liveGate
  have valid : j < z := by
    by_contra! hn
    rw [List.getD_eq_default _ _ (by omega)] at hk
    contradiction
  have internal : 9 ≤ j := by
    by_contra! raw
    have neq : (⟨j,raw⟩ : Fin 9) ≠ v := by
      intro eq; have he := congrArg Fin.val eq
      change j = v.val at he; rw [he,fixed.2] at hk; contradiction
    obtain ⟨x,hd,on⟩ := sens ⟨j,raw⟩ neq
    have on₀ : (pref x false).getD j false = true := by
      rw [show (pref x false).getD j false = (args v false x).getD j false from
        getD_wiresFrom _ _ _ (by rw [args_len]; exact raw)]
      exact on
    have on₁ := ((agr x).2 j (fun e => neq (Fin.ext e))).symm.trans on₀
    have bits : bit x false = bit x true := by
      simp only [List.getD_eq_getElem?_getD] at on₀ on₁
      rcases hj with h|h <;> simp [bit,op,h,GateOp.eval,on₀,on₁]
    have next := agreeSnoc (agr x) (fun _ => bits)
    have final := agreeRun next t (fun f hf i hi e => tailNo f hf (e ▸ hi))
    rw [unfoldVal,unfoldVal] at hd
    exact hd (final.2 o hout)
  exact ⟨p,g,t,j,rfl,internal,valid,op,hj,fun f hf => (List.mem_append.mp hf).elim (preNo f) (tailNo f)⟩

theorem uniquePosition (v : ℕ) (p t : List Gate) (g : Gate)
    (avoid : ∀ f ∈ p ++ t, v ∉ f.inputs) (i : ℕ) (hi : i < (p++g::t).length)
    (read : v ∈ ((p++g::t)[i]).inputs) : i = p.length := by
  by_contra hn
  by_cases h : i < p.length
  · rw [List.getElem_append_left h] at read
    exact avoid _ (List.mem_append_left _ (List.getElem_mem h)) read
  · obtain ⟨k,hk⟩ : ∃ k, i = p.length + (k+1) := ⟨i-p.length-1,by omega⟩
    have bound : k < t.length := by simp at hi; omega
    have id : (p++g::t)[i] = t[k] := by
      rw [List.getElem_append_right (by omega)]
      simp [hk]
    rw [id] at read
    exact avoid _ (List.mem_append_right _ (List.getElem_mem bound)) read
theorem normalOp (g : Gate) : (normGate g).op = g.op := by cases g with | mk op l => cases op <;> rfl
theorem normInputs (g : Gate) (ok : Ok g) :
    (if g.op.eval [false,false] = true then g.inputs.take 1 else g.inputs) = (normGate g).inputs := by
  rcases g with ⟨op,l⟩
  rcases ok.1 with h|h|h <;> change op = _ at h <;> subst op <;> rfl
theorem backOr (g : Gate) (h : (normGate g).op = .or) : normGate g = g := by
  rw [normalOp] at h
  cases g with | mk op l => change op = .or at h; subst op; rfl
end PEqualNP.Outside.L_meta_2822
open PEqualNP.Outside.L_meta_2822 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_2822 : have x1 : Fin (9 : ℕ) → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Gate) => (if x2.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs).contains ↑x1; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)),   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x2 →     have x5 : Bool → (Fin (8 : ℕ) → Bool) → Bool := fun (x5 : Bool) (x6 : Fin (8 : ℕ) → Bool) => x2.eval ((List.ofFn x6).insertIdx (↑x3) x5);     (∃ (x6 : Fin (8 : ℕ) → Bool) (x7 : Fin (8 : ℕ) → Bool), x5 Bool.false x6 ≠ x5 Bool.false x7) → (∀ (x7 : Fin (9 : ℕ)), x7 ≠ x3 → ∃ (x9 : Fin (8 : ℕ) → Bool), x5 Bool.false x9 ≠ x5 Bool.true x9 ∧ ((List.ofFn x9).insertIdx (↑x3) Bool.false).getD (↑x7) Bool.false = Bool.true) → (∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + (2 : ℕ) ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x8 = x5 Bool.false) ∨ ∃ (x8 : Fin x2.size) (x9 : ℕ), (9 : ℕ) ≤ x9 ∧ x9 < (9 : ℕ) + ↑x8 ∧ (x2.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ((x2.gates.get x8).inputs = [↑x3, x9] ∨ (x2.gates.get x8).inputs = [x9, ↑x3]) ∧ ∀ (x10 : Fin x2.size), x1 x3 (x2.gates.get x10) = Bool.true → x10 = x8 := by
  dsimp only
  intro C v hmin diff sens
  let gs := C.gates.map normGate
  have ok : ∀ f ∈ gs, NOk f := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    exact normGate_nok _ (hmin.1 _ hg)
  have ev (flag x) : value gs C.output v flag x = C.eval (args v flag x) := by
    unfold value gs; rw [wiresFrom_norm]; rfl
  obtain ⟨x,y,hd⟩ := diff
  have diff' : ∃ x y, value gs C.output v false x ≠ value gs C.output v false y :=
    ⟨x,y,by simpa only [ev,args] using hd⟩
  have sens' : Paired gs C.output v := by
    intro j hj
    obtain ⟨x,hd,ht⟩ := sens j hj
    exact ⟨x,by simpa only [ev,args] using hd,ht⟩
  have size : gs.length = C.size := by simp [gs,Circuit.size]
  rcases newShape gs C.output v ok diff' sens' with ⟨D,hD,bd,res⟩|⟨p,g,t,j,he,lb,ub,hop,ins,no⟩
  · left; exact ⟨D,hD,size ▸ bd,res.trans (funext (ev false))⟩
  · right
    have len : p.length < C.size := by rw [←size,he]; simp
    let pos : Fin C.size := ⟨p.length,len⟩
    have lookup (i : Fin C.size) : (normGate (C.gates.get i)) =
        (p++g::t)[i.val]'(by rw [←he,size]; exact i.isLt) := by
      simp [←he,gs]
      rfl
    have found : normGate (C.gates.get pos) = g := by
      rw [lookup]; simp [pos]
    have opOriginal : (C.gates.get pos).op = .or := (normalOp _).symm.trans (found ▸ hop)
    have equal : C.gates.get pos = g := (backOr _ ((normalOp _).trans opOriginal)).symm.trans found
    refine ⟨pos,j,lb,ub,opOriginal,equal ▸ ins,?_⟩
    intro i reads
    have hk : Ok (C.gates.get i) := hmin.1 _ (List.get_mem ..)
    rw [normInputs _ hk] at reads
    have member := List.contains_iff_mem.mp reads
    rw [lookup] at member
    exact Fin.ext (uniquePosition v p t g no i _ member)
