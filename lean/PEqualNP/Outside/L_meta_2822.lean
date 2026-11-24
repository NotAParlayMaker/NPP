import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2822_aux

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldKeep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi


lemma getDAppendSingleton {w : List Bool} {b : Bool} {i : ℕ} :
    (w ++ [b]).getD i false = if i < w.length then w.getD i false
      else if i = w.length then b else false := by
  split
  · exact List.getD_append _ _ _ _ (by assumption)
  · split
    · subst i
      simp
    · apply List.getD_eq_default
      simp
      omega

lemma foldAgreeExcept (gs : List Gate) (v : ℕ) (w z : List Bool)
    (hW : w.length = z.length)
    (hAt : ∀ i ≠ v, w.getD i false = z.getD i false)
    (hNo : ∀ g ∈ gs, v ∉ g.inputs) :
    ∀ i ≠ v, (gs.foldl step w).getD i false = (gs.foldl step z).getD i false := by
  induction gs generalizing w z with
  | nil => exact hAt
  | cons g gs ih =>
    change ∀ i ≠ v, (gs.foldl step (step w g)).getD i false =
      (gs.foldl step (step z g)).getD i false
    have hRead : g.inputs.map (fun i => w.getD i false) =
        g.inputs.map (fun i => z.getD i false) := by
      apply List.map_congr_left
      intro i hi
      apply hAt
      intro h
      exact hNo g (by simp) (h ▸ hi)
    refine ih (step w g) (step z g) (by simp [step, hW]) ?_ ?_
    · intro i hi
      simp only [step]
      rw [getDAppendSingleton, getDAppendSingleton, hW, hAt i hi, hRead]
    · intro h hh
      exact hNo h (List.mem_cons_of_mem _ hh)



theorem foldLength (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, step]; omega


def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)
abbrev Stat := Sum Bool ℕ
abbrev Stat.const (b : Bool) : Stat := Sum.inl b
abbrev Stat.wire (i : ℕ) : Stat := Sum.inr i

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Sum.inl c :: _ => (none, Stat.const (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Sum.inl c] => (none, Stat.const c)
  | [Sum.inr j] => (none, Stat.wire j)
  | [Sum.inl c, Sum.inl d] => (none, Stat.const (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Sum.inl c] => (none, Stat.const c)
  | [Sum.inr j] => (none, Stat.wire j)
  | [Sum.inl c, Sum.inl d] => (none, Stat.const (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd, Stat.const, Stat.wire] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr, Stat.const, Stat.wire] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [Stat.const, Stat.wire, simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [Stat.const, Stat.wire, simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [Stat.const, Stat.wire, simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [Stat.const, Stat.wire, simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [Stat.const, Stat.wire, simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [Stat.const, Stat.wire, simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [Stat.const, Stat.wire, simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [Stat.const, Stat.wire, simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [Stat.const, Stat.wire, simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [Stat.const, Stat.wire, simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [Stat.const, Stat.wire, simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

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
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

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
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
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
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Stat.const b) (fun k : Fin n => Stat.wire k) : Fin (n + 1) → Stat)

theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

theorem statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Stat.const false) = Stat.const b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

theorem statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Stat.const false) = Stat.wire k := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩



theorem sameBitsExcept (v : Fin 9) {x y : Fin 9 → Bool}
    (he : ∀ i ≠ v, x i = y i) :
    ∀ i ≠ (v : ℕ), (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
  intro i hi
  by_cases hh : i < 9
  · rw [List.getD_eq_getElem _ _ (by simpa using hh), List.getD_eq_getElem _ _ (by simpa using hh)]
    simpa only [List.getElem_ofFn] using he ⟨i,hh⟩ (fun h => hi (congrArg Fin.val h))
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]


theorem elimAppend (n : ℕ) (l r : List Gate) (acc : List Stat × List Gate) :
    elim n (l ++ r) acc = elim n r (elim n l acc) := by simp [elim, List.foldl_append]

theorem elimFirstLen (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    change (elim n gs (elimStep n acc g)).1.length = _
    rw [ih]
    simp [elimStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]


theorem agreeTwo (k j : ℕ) (gs : List Gate) (w z : List Bool) (hl : w.length = z.length)
    (hw : ∀ i, i ≠ k → i ≠ j → w.getD i false = z.getD i false)
    (hk : ∀ g ∈ gs, k ∉ g.inputs) (hj : ∀ g ∈ gs, j ∉ g.inputs) :
    ∀ i, i ≠ k → i ≠ j → (gs.foldl step w).getD i false = (gs.foldl step z).getD i false := by
  induction gs generalizing w z with
  | nil => exact hw
  | cons g gs ih =>
    apply ih (step w g) (step z g) (by simp [step, hl]) _
      (fun a ha => hk a (List.mem_cons_of_mem _ ha)) (fun a ha => hj a (List.mem_cons_of_mem _ ha))
    have hr : g.inputs.map (fun i => w.getD i false) = g.inputs.map (fun i => z.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hw i (fun h => hk g (by simp) (h ▸ hi)) (fun h => hj g (by simp) (h ▸ hi))
    intro i hi₁ hi₂
    simp only [step, getDAppendSingleton, hl, hr, hw i hi₁ hi₂]


def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

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

def input (v : Fin 9) (b : Bool) (y : Fin 8 → Bool) : Fin 9 → Bool := Fin.insertNth v b y
def w0 (v : Fin 9) (b : Bool) (y : Fin 8 → Bool) := List.ofFn (input v b y)
def result (gs : List Gate) (out : ℕ) (v : Fin 9) (b : Bool) (y : Fin 8 → Bool) :=
  (gs.foldl step (w0 v b y)).getD out false

theorem insert_eq (v : Fin 9) (b : Bool) (y : Fin 8 → Bool) :
    (List.ofFn y).insertIdx (v : ℕ) b = w0 v b y := by fin_cases v <;> rfl

theorem wlen (v : Fin 9) (b : Bool) (y : Fin 8 → Bool) : (w0 v b y).length = 9 := by simp [w0]

theorem sameExcept (v : Fin 9) (y : Fin 8 → Bool) :
    ∀ i ≠ (v : ℕ), (w0 v false y).getD i false = (w0 v true y).getD i false := by
  apply sameBitsExcept
  intro i hi
  obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hi
  simp [input]

theorem wself (v : Fin 9) (b : Bool) (y : Fin 8 → Bool) : (w0 v b y).getD v false = b := by
  change (List.ofFn (input v b y)).getD v false = _
  rw [getD_ofFn,input,Fin.insertNth_apply_same]

theorem indexNotOutput (gs : List Gate) (out : ℕ) (v : Fin 9)
    (hnc : ∃ y z, result gs out v false y ≠ result gs out v false z) : out ≠ (v : ℕ) := by
  rintro rfl
  obtain ⟨y,z,hh⟩ := hnc
  have h (u : Fin 8 → Bool) : result gs v v false u = false := by
    change (gs.foldl step _).getD (v : ℕ) false = _
    rw [foldKeep _ _ _ (by rw [wlen]; exact v.isLt), wself]
  exact hh ((h y).trans (h z).symm)

theorem anyReader (gs : List Gate) (out : ℕ) (v : Fin 9)
    (hnc : ∃ y z, result gs out v false y ≠ result gs out v false z)
    (hdep : ∃ y, result gs out v false y ≠ result gs out v true y) :
    ∃ g ∈ gs, (v : ℕ) ∈ g.inputs := by
  by_contra! hno
  obtain ⟨y,hh⟩ := hdep
  exact hh (foldAgreeExcept gs v _ _ (by simp [wlen]) (sameExcept v y) hno out (indexNotOutput gs out v hnc))

def initial (v : Fin 9) : List Stat × List Gate := (statAt 8 v false, [])
def built (v : Fin 9) (pre : List Gate) := elim 8 pre (initial v)
def added (v : Fin 9) (pre : List Gate) (g : Gate) := elimStep 8 (built v pre) g

theorem builtLength (v : Fin 9) (pre : List Gate) : (built v pre).1.length = 9 + pre.length := by
  simp [built,initial,elimFirstLen,statAt_length]

theorem builtSelf (v : Fin 9) (pre : List Gate) :
    (built v pre).1.getD v (Stat.const false) = Stat.const false := by
  rw [built,elim_getD 8 (v : ℕ) _ pre _ (by simp [initial,statAt_length])]
  exact statAt_at 8 v false

theorem addedSelf (v : Fin 9) (pre : List Gate) (g : Gate) :
    (added v pre g).1.getD v (Stat.const false) = Stat.const false := by
  change ((built v pre).1 ++ [_]).getD (v : ℕ) _ = _
  rw [List.getD_append _ _ _ _ (by rw [builtLength]; have := v.isLt; omega)]
  exact builtSelf _ _

def Saved (gs : List Gate) (out : ℕ) (v : Fin 9) := ∃ E : Circuit, FanInTwo E ∧
  E.size + 2 ≤ gs.length ∧ circuitFun 8 E = result gs out v false

theorem saved_of_len (gs : List Gate) (out : ℕ) (v : Fin 9) (hok : ∀ g ∈ gs, NOk g)
    (hnc : ∃ y z, result gs out v false y ≠ result gs out v false z)
    (hlen : (built v gs).2.length + 2 ≤ gs.length) : Saved gs out v := by
  have val (y : Fin 8 → Bool) :
      ((built v gs).1.getD out (Stat.const false)).val (wiresFrom (built v gs).2 (List.ofFn y)) =
      result gs out v false y := ((inv_elim 8 _ (by simp) gs _ (initial v) (fun a ha => (hok a ha).1)
        (inv_at 8 v false y)).2 out).2
  cases h : (built v gs).1.getD out (Stat.const false) with
  | inl b =>
    obtain ⟨y,z,hne⟩ := hnc
    have a := val y
    have b := val z
    rw [h] at a b
    exact (hne (a.symm.trans b)).elim
  | inr j =>
    refine ⟨⟨(built v gs).2,j⟩,elim_ok _ gs (initial v) (by simp [initial]),hlen,?_⟩
    funext y
    have hh := val y
    rw [h] at hh
    exact hh

theorem savedReaders (pre post : List Gate) (g : Gate) (out : ℕ) (v : Fin 9)
    (hok : ∀ a ∈ pre ++ g :: post, NOk a) (hv : (v : ℕ) ∈ g.inputs)
    (hnc : ∃ y z, result (pre ++ g :: post) out v false y ≠ result (pre ++ g :: post) out v false z)
    (hex : (∃ h ∈ pre, (v : ℕ) ∈ h.inputs) ∨ (∃ h ∈ post, (v : ℕ) ∈ h.inputs) ∨
      ((∃ c, (added v pre g).1.getD (9 + pre.length) (Stat.const false) = Stat.const c) ∧
       (∃ h ∈ post, 9 + pre.length ∈ h.inputs))) : Saved (pre ++ g :: post) out v := by
  let a := built v pre
  let b := added v pre g
  have hr : built v (pre ++ g :: post) = elim 8 post b := by rw [built,elimAppend]; rfl
  have gOk := hok g (by simp)
  have nullG : b.2.length = a.2.length := elimStep_none 8 a g gOk v hv false (builtSelf _ _)
  have hlenA : a.2.length ≤ pre.length := by
    simpa [a,built,initial] using elim_len 8 pre (initial v)
  have lB : b.1.length = 9 + pre.length + 1 := by simp [b,added,elimStep,builtLength]
  have okP (t : Gate) (ht : t ∈ pre) := hok t (by simp [ht])
  have okS (t : Gate) (ht : t ∈ post) := hok t (by simp [ht])
  apply saved_of_len _ _ _ hok hnc
  rw [hr,List.length_append,List.length_cons]
  rcases hex with hp | hs | ⟨hs,he⟩
  · have hh := elim_len_lt 8 v pre (initial v) okP (by simp [initial,statAt_length])
        ⟨false,statAt_at 8 v false⟩ hp
    change a.2.length + 1 ≤ 0 + pre.length at hh
    have ht := elim_len 8 post b
    omega
  · have ht := elim_len_lt 8 v post b okS (by have := v.isLt; omega)
        ⟨false,addedSelf _ _ _⟩ hs
    omega
  · have ht := elim_len_lt 8 (9 + pre.length) post b okS (by omega) hs he
    omega

theorem constAtImpliesNext (pre post : List Gate) (g : Gate) (out : ℕ) (v : Fin 9)
    (hok : ∀ a ∈ pre ++ g :: post, NOk a)
    (hnc : ∃ y z, result (pre ++ g :: post) out v false y ≠ result (pre ++ g :: post) out v false z)
    (hdep : ∃ y, result (pre ++ g :: post) out v false y ≠ result (pre ++ g :: post) out v true y)
    (hpre : ∀ a ∈ pre, (v : ℕ) ∉ a.inputs) (hpost : ∀ a ∈ post, (v : ℕ) ∉ a.inputs)
    (hs : ∃ c, (added v pre g).1.getD (9 + pre.length) (Stat.const false) = Stat.const c) :
    ∃ a ∈ post, 9 + pre.length ∈ a.inputs := by
  let k := 9 + pre.length
  obtain ⟨c,hc⟩ := hs
  have hout : out ≠ k := by
    intro eq
    have hc' : (built v (pre ++ g :: post)).1.getD k (Stat.const false) = Stat.const c := by
      rw [built,elimAppend]
      change (elim 8 post (added v pre g)).1.getD k _ = _
      rw [elim_getD 8 k _ post _ (by simp [added,elimStep,builtLength,k])]
      exact hc
    have foo (u : Fin 8 → Bool) : result (pre ++ g :: post) out v false u = c := by
      have h := ((inv_elim 8 _ (by simp) (pre ++ g :: post) _ (initial v) (fun a ha => (hok a ha).1)
        (inv_at 8 v false u)).2 out).2
      change ((built v (pre ++ g :: post)).1.getD out _).val _ = result _ out v false u at h
      rw [eq,hc'] at h
      exact eq ▸ h.symm
    obtain ⟨y,z,hne⟩ := hnc
    exact hne ((foo y).trans (foo z).symm)
  by_contra! hno
  obtain ⟨y,hh⟩ := hdep
  let w (b : Bool) := pre.foldl step (w0 v b y)
  have lw (b : Bool) : (w b).length = k := by simp [w,foldLength,wlen,k]
  have wp := foldAgreeExcept pre v _ _ (by simp [wlen]) (sameExcept v y) hpre
  have ht : ∀ i, i ≠ (v : ℕ) → i ≠ k →
      (step (w false) g).getD i false = (step (w true) g).getD i false := by
    intro i hi hk
    have h : (w false).getD i false = (w true).getD i false := wp i hi
    simp only [step,getDAppendSingleton,lw,ite_eq_right hk,h]
  apply hh
  change ((pre ++ g :: post).foldl step _).getD out false = _
  simp only [result,List.foldl_append,List.foldl_cons]
  exact agreeTwo v k post _ _ (by simp [step,lw]) ht hpost hno out
    (indexNotOutput _ out v hnc) hout


theorem classify (m v : ℕ) (g : Gate) (s : ℕ → Stat) (hg : NOk g)
    (hv : v ∈ g.inputs) (hz : s v = Stat.const false)
    (hnc : ¬∃ c, (simplify g.op m (g.inputs.map s)).2 = Stat.const c) :
    g.op = .or ∧ ∃ a j, (g.inputs = [v,a] ∨ g.inputs = [a,v]) ∧ s a = Stat.wire j := by
  have hop := hg.1.1
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  have hlen := hg.1.2
  rcases ha : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c,cs⟩⟩⟩
  · simp [ha] at hv
  · have eq : v = a := by simpa [ha] using hv
    subst a
    rcases hop with ho | ho | ho
    · exact (hnc ⟨false,by simp [Stat.const,Stat.wire,ha,ho,hz,simplify,simpAnd]⟩).elim
    · exact (hnc ⟨false,by simp [Stat.const,Stat.wire,ha,ho,hz,simplify,simpOr]⟩).elim
    · exact (hnc ⟨true,by simp [Stat.const,Stat.wire,ha,ho,hz,simplify,simpNot]⟩).elim
  · have eq : v = a ∨ v = b := by simpa [ha] using hv
    rcases eq with rfl | rfl
    · rcases hop with ho | ho | ho
      · cases hb : s b with
        | inl c => exact (hnc ⟨false, by simp [Stat.const,Stat.wire,ha,ho,hz,hb,simplify,simpAnd]⟩).elim
        | inr j => exact (hnc ⟨false, by simp [Stat.const,Stat.wire,ha,ho,hz,hb,simplify,simpAnd]⟩).elim
      · cases hb : s b with
        | inl c => exact (hnc ⟨c, by simp [Stat.const,Stat.wire,ha,ho,hz,hb,simplify,simpOr]⟩).elim
        | inr j => exact ⟨ho,b,j,Or.inl rfl,hb⟩
      · have := hg.2 ho; simp [ha] at this
    · rcases hop with ho | ho | ho
      · cases hb : s a with
        | inl c => exact (hnc ⟨false, by simp [Stat.const,Stat.wire,ha,ho,hz,hb,simplify,simpAnd]⟩).elim
        | inr j => exact (hnc ⟨false, by simp [Stat.const,Stat.wire,ha,ho,hz,hb,simplify,simpAnd]⟩).elim
      · cases hb : s a with
        | inl c => exact (hnc ⟨c, by simp [Stat.const,Stat.wire,ha,ho,hz,hb,simplify,simpOr]⟩).elim
        | inr j => exact ⟨ho,a,j,Or.inr rfl,hb⟩
      · have := hg.2 ho; simp [ha] at this
  · simp [ha] at hlen

theorem shield (v u : Fin 9) (hne : u ≠ v) (pre post : List Gate) (g : Gate) (out : ℕ)
    (hout : out ≠ (v : ℕ)) (hpre : ∀ a ∈ pre, (v : ℕ) ∉ a.inputs)
    (hpost : ∀ a ∈ post, (v : ℕ) ∉ a.inputs) (hop : g.op = .or)
    (hargs : g.inputs = [(v : ℕ),(u : ℕ)] ∨ g.inputs = [(u : ℕ),(v : ℕ)])
    (y : Fin 8 → Bool) (hw : (w0 v false y).getD u false = true) :
    result (pre ++ g :: post) out v false y = result (pre ++ g :: post) out v true y := by
  let w (b : Bool) := pre.foldl step (w0 v b y)
  have lb (b : Bool) : (w b).length = 9 + pre.length := by simp [w,foldLength,wlen]
  have same := foldAgreeExcept pre v _ _ (by simp [wlen]) (sameExcept v y) hpre
  have readU : ∀ b, (w b).getD u false = true := by
    intro b
    have h₀ : (w false).getD (u : ℕ) false = true := by
      change (pre.foldl step (w0 v false y)).getD (u : ℕ) false = true
      rw [foldKeep _ _ _ (by rw [wlen]; exact u.isLt),hw]
    cases b with
    | false => exact h₀
    | true => exact (same u (fun h => hne (Fin.ext h))).symm.trans h₀
  have stepVal (b : Bool) : step (w b) g = w b ++ [true] := by
    rcases hargs with ha | ha <;>
      simp only [step,hop,ha,List.map_cons,List.map_nil,readU,GateOp.eval,List.any_cons,
        List.any_nil,Bool.or_true,Bool.true_or,id_eq,Bool.or_false]
  have cmp (i : ℕ) (hi : i ≠ (v : ℕ)) :
      (step (w false) g).getD i false = (step (w true) g).getD i false := by
    rw [stepVal,stepVal,getDAppendSingleton,getDAppendSingleton,lb,lb]
    have h : (w false).getD i false = (w true).getD i false := same i hi
    rw [h]
  simp only [result,List.foldl_append,List.foldl_cons]
  exact foldAgreeExcept post v _ _ (by simp [stepVal,lb]) cmp hpost out hout

def Shape (gs : List Gate) (v : Fin 9) := ∃ (p : Fin gs.length) (a : ℕ),
  9 ≤ a ∧ a < 9 + p.val ∧ (gs.get p).op = .or ∧
    ((gs.get p).inputs = [(v : ℕ),a] ∨ (gs.get p).inputs = [a,(v : ℕ)]) ∧
    ∀ i : Fin gs.length, (v : ℕ) ∈ (gs.get i).inputs → i = p

theorem normalizeOrSave (gs : List Gate) (out : ℕ) (v : Fin 9) (hok : ∀ g ∈ gs, NOk g)
    (hnc : ∃ y z, result gs out v false y ≠ result gs out v false z)
    (hp : ∀ u : Fin 9, u ≠ v → ∃ y, result gs out v false y ≠ result gs out v true y ∧
      (w0 v false y).getD u false = true) : Saved gs out v ∨ Shape gs v := by
  by_cases saved : Saved gs out v
  · exact Or.inl saved
  have hdep : ∃ y, result gs out v false y ≠ result gs out v true y := by
    have hs : ∀ w : Fin 9, ∃ u : Fin 9, u ≠ w := by decide
    obtain ⟨u,hu⟩ := hs v
    obtain ⟨y,hy,_⟩ := hp u hu
    exact ⟨y,hy⟩
  obtain ⟨g,hg,hv⟩ := anyReader gs out v hnc hdep
  obtain ⟨pre,post,eq⟩ := List.mem_iff_append.mp hg
  subst gs
  have hpre (a : Gate) (ha : a ∈ pre) (h : (v : ℕ) ∈ a.inputs) : False :=
    saved (savedReaders pre post g out v hok hv hnc (Or.inl ⟨a,ha,h⟩))
  have hpost (a : Gate) (ha : a ∈ post) (h : (v : ℕ) ∈ a.inputs) : False :=
    saved (savedReaders pre post g out v hok hv hnc (Or.inr (Or.inl ⟨a,ha,h⟩)))
  let a := built v pre
  let s (i : ℕ) := a.1.getD i (Stat.const false)
  have hb : ¬∃ c, (simplify g.op (8 + a.2.length) (g.inputs.map s)).2 = Stat.const c := by
    rintro ⟨c,hc⟩
    have hs : ∃ c, (added v pre g).1.getD (9 + pre.length) (Stat.const false) = Stat.const c := by
      refine ⟨c,?_⟩
      rw [← builtLength v pre]
      change (a.1 ++ [_]).getD a.1.length _ = _
      rw [getD_snoc_eq]
      exact hc
    have hnext := constAtImpliesNext pre post g out v hok hnc hdep hpre hpost hs
    exact saved (savedReaders pre post g out v hok hv hnc (Or.inr (Or.inr ⟨hs,hnext⟩)))
  obtain ⟨ho,m,j,harg,hm⟩ := classify (8 + a.2.length) v g s (hok g hg) hv (builtSelf _ _) hb
  have upper : m < 9 + pre.length := by
    by_contra! h
    change (built v pre).1.getD m (Stat.const false) = Stat.wire j at hm
    rw [List.getD_eq_default _ _ (by rw [builtLength]; exact h)] at hm
    contradiction
  have low : 9 ≤ m := by
    by_contra! small
    let u : Fin 9 := ⟨m,small⟩
    have hne : u ≠ v := by
      intro eq
      have h := congrArg Fin.val eq
      change m = v.val at h
      rw [h] at hm
      have z : s v = Stat.const false := builtSelf _ _
      rw [z] at hm
      contradiction
    obtain ⟨y,hs,hh⟩ := hp u hne
    exact hs (shield v u hne pre post g out (indexNotOutput _ _ _ hnc) hpre hpost ho harg y hh)
  let p : Fin (pre ++ g :: post).length := ⟨pre.length,by simp⟩
  have gat : (pre ++ g :: post).get p = g := by simp [p]
  refine Or.inr ⟨p,m,low,upper,by rw [gat]; exact ho,by rw [gat]; exact harg,?_⟩
  intro i hread
  apply Fin.ext
  change i.val = pre.length
  by_contra hn
  by_cases hl : i.val < pre.length
  · have mem : (pre ++ g :: post).get i ∈ pre := by
      simp only [List.get_eq_getElem,List.getElem_append_left hl]
      exact List.getElem_mem ..
    exact hpre _ mem hread
  · have heq : i.val - pre.length ≠ 0 := by omega
    have mem : (pre ++ g :: post).get i ∈ post := by
      simp only [List.get_eq_getElem,List.getElem_append_right (Nat.le_of_not_gt hl)]
      rw [List.getElem_cons,dif_neg heq]
      exact List.getElem_mem ..
    exact hpost _ mem hread


end PEqualNP.Outside.L_meta_2822_aux

open PEqualNP.Outside.L_meta_2822_aux

theorem PEqualNP.Outside.L_meta_2822 :
have x1 : Fin (9 : ℕ) → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Gate) => (if x2.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs).contains ↑x1; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)),   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x2 →     have x5 : Bool → (Fin (8 : ℕ) → Bool) → Bool := fun (x5 : Bool) (x6 : Fin (8 : ℕ) → Bool) => x2.eval ((List.ofFn x6).insertIdx (↑x3) x5);     (∃ (x6 : Fin (8 : ℕ) → Bool) (x7 : Fin (8 : ℕ) → Bool), x5 Bool.false x6 ≠ x5 Bool.false x7) → (∀ (x7 : Fin (9 : ℕ)), x7 ≠ x3 → ∃ (x9 : Fin (8 : ℕ) → Bool), x5 Bool.false x9 ≠ x5 Bool.true x9 ∧ ((List.ofFn x9).insertIdx (↑x3) Bool.false).getD (↑x7) Bool.false = Bool.true) → (∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + (2 : ℕ) ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x8 = x5 Bool.false) ∨ ∃ (x8 : Fin x2.size) (x9 : ℕ), (9 : ℕ) ≤ x9 ∧ x9 < (9 : ℕ) + ↑x8 ∧ (x2.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ((x2.gates.get x8).inputs = [↑x3, x9] ∨ (x2.gates.get x8).inputs = [x9, ↑x3]) ∧ ∀ (x10 : Fin x2.size), x1 x3 (x2.gates.get x10) = Bool.true → x10 = x8 := by
  intro effective C v hmin f hnc hp
  let gs := C.gates.map normGate
  have hl : gs.length = C.size := by simp [gs,Circuit.size]
  have hok (g : Gate) (hg : g ∈ gs) : NOk g := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok a (hmin.1 a ha)
  have he (b : Bool) (y : Fin 8 → Bool) : result gs C.output v b y = f b y := by
    change (wiresFrom (C.gates.map normGate) (w0 v b y)).getD C.output false =
      C.eval ((List.ofFn y).insertIdx (v : ℕ) b)
    rw [wiresFrom_norm,insert_eq]
    rfl
  have nc : ∃ y z, result gs C.output v false y ≠ result gs C.output v false z := by
    obtain ⟨y,z,h⟩ := hnc
    exact ⟨y,z,by simpa only [he] using h⟩
  have pos (u : Fin 9) (hne : u ≠ v) : ∃ y, result gs C.output v false y ≠
      result gs C.output v true y ∧ (w0 v false y).getD u false = true := by
    obtain ⟨y,h,hz⟩ := hp u hne
    exact ⟨y,by simpa only [he] using h,by simpa only [insert_eq] using hz⟩
  obtain ⟨E,hE,hs,hh⟩ | ⟨p,m,hlo,hhi,hop,harg,huniq⟩ :=
    normalizeOrSave gs C.output v hok nc pos
  · exact Or.inl ⟨E,hE,hl ▸ hs,hh.trans (funext (he false))⟩
  · let j : Fin C.size := ⟨p.val,hl ▸ p.isLt⟩
    have hg : gs.get p = normGate (C.gates.get j) := by
      simp [gs,j,List.get_eq_getElem]
      rfl
    have sameOp (a : Gate) : (normGate a).op = a.op := by
      obtain ⟨op,args⟩ := a
      cases op <;> rfl
    have hjor : (C.gates.get j).op = .or := (sameOp _).symm.trans (hg ▸ hop)
    have hnorm : normGate (C.gates.get j) = C.gates.get j := by simp [normGate,hjor]
    rw [hg,hnorm] at harg
    refine Or.inr ⟨j,m,hlo,hhi,hjor,harg,?_⟩
    intro i hi
    let l : Fin gs.length := ⟨i.val,hl.symm ▸ i.isLt⟩
    have hgate : gs.get l = normGate (C.gates.get i) := by
      simp [gs,l,List.get_eq_getElem]
      rfl
    have hm : (v : ℕ) ∈ (normGate (C.gates.get i)).inputs := by
      have ha := (hmin.1 (C.gates.get i) (List.get_mem ..)).1
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
      rcases ha with ha | ha | ha <;>
        simpa [effective,normGate,ha,GateOp.eval] using hi
    exact Fin.ext (congrArg (fun z : Fin gs.length => z.val) (huniq l (hgate ▸ hm)))
