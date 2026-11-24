import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2153_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Cof2153

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldKeep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

def singleton (v : Fin 9) (i : Fin 9) : Bool := decide (i = v)

lemma singleton_read (v : Fin 9) (i : ℕ) :
    (List.ofFn (singleton v)).getD i false = decide (i = (v : ℕ)) := by
  by_cases h : i < 9
  · interval_cases i <;> simp [singleton, List.getD_eq_getElem?_getD, ← Fin.val_inj]
  · have nv : i ≠ (v : ℕ) := by have := v.isLt; omega
    rw [List.getD_eq_default _ _ (by simp; omega)]
    simp [nv]

lemma zero_read (i : ℕ) : (List.ofFn (fun _ : Fin 9 => false)).getD i false = false := by
  by_cases h : i < 9
  · interval_cases i <;> rfl
  · rw [List.getD_eq_default _ _ (by simp; omega)]


def graphF (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)


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

lemma firstWireComputed {g : Gate} (gs : List Gate) (out : ℕ) (x : Fin 9 → Bool) :
    ((⟨g :: gs, out⟩ : Circuit).wires (List.ofFn x)).getD 9 false =
      (step (List.ofFn x) g).getD 9 false := by
  change (gs.foldl step (step (List.ofFn x) g)).getD 9 false = _
  exact foldKeep gs _ 9 (by simp [step])

lemma readRaw (C : Circuit) (x : Fin 9 → Bool) (v : Fin 9) :
    (C.wires (List.ofFn x)).getD (v : ℕ) false = x v := by
  change (C.gates.foldl step (List.ofFn x)).getD (v : ℕ) false = _
  rw [foldKeep C.gates (List.ofFn x) (v : ℕ) (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact v.isLt)]
  simp only [List.getElem_ofFn]


theorem foldLength (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, step]; omega


def residualF (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
    (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
    (x 5 && x 7) || (x 7 && x 4)

def shiftFromFour (x : Fin 8 → Bool) : Fin 9 → Bool := Fin.insertNth 4 false x


theorem cofactor4 (y : Fin 8 → Bool) : graphF (shiftFromFour y) = residualF y := by
  change ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && false) || (false && y 0) || (y 0 && y 4) || (y 1 && y 5) || (y 2 && y 6) || (y 3 && y 7) || (y 4 && y 6) || (y 5 && y 7) || (y 7 && y 4)) = _
  simp [residualF]

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


theorem outputNotInput (v : Fin 9) (C : Circuit)
    (he : ∀ x, C.eval (List.ofFn x) = graphF x) : C.output ≠ (v : ℕ) := by
  intro hout
  have h := he (singleton v)
  change (C.wires _).getD C.output false = _ at h
  rw [hout, readRaw] at h
  have hz : ∀ w : Fin 9, graphF (singleton w) = false := by decide +kernel
  simpa [singleton, hz] using h


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

theorem firstGateShape (C : Circuit) (hC : FanInTwo C)
    (hFirst : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 4)) :
    ∃ gs : List Gate,
      C.gates = ⟨GateOp.or, [0, 4]⟩ :: gs ∨ C.gates = ⟨GateOp.or, [4, 0]⟩ :: gs := by
  obtain ⟨gs, out⟩ := C
  cases gs with
  | nil =>
    have h := hFirst (singleton 0)
    change (List.ofFn (singleton 0)).getD 9 false = (singleton 0 0 || singleton 0 2) at h
    rw [singleton_read] at h
    simp [singleton] at h
  | cons g gs =>
    have ⟨hkind, hlen⟩ := hC g (by simp)
    have gateEq (x : Fin 9 → Bool) :
        g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 4) := by
      let w := List.ofFn x
      have h := hFirst x
      change (gs.foldl step (step w g)).getD 9 false = _
        at h
      rw [foldKeep gs (step w g) 9 (by simp [step, w])] at h
      change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD 9 false = _ at h
      simpa [w] using h
    have z0 : ((0 : Fin 9) : ℕ) = 0 := by decide
    have z2 : ((4 : Fin 9) : ℕ) = 4 := by decide
    have h0 : g.op.eval (g.inputs.map fun i => decide (i = 0)) = true := by
      simpa only [singleton_read, z0, singleton, decide_true, Bool.true_or] using gateEq (singleton 0)
    have h2 : g.op.eval (g.inputs.map fun i => decide (i = 4)) = true := by
      simpa only [singleton_read, z2, singleton, decide_true, Bool.or_true] using gateEq (singleton 4)
    have he : g.op.eval (g.inputs.map fun _ => false) = false := by
      simpa only [zero_read, Bool.or_false] using gateEq (fun _ => false)
    obtain ⟨op, args⟩ := g
    change args.length ≤ 2 at hlen
    cases op with
    | mod m => simp at hkind
    | maj => simp at hkind
    | not => cases args <;> simp [GateOp.eval] at he
    | and =>
      change (args.map fun i => decide (i = 0)).all id = true at h0
      change (args.map fun i => decide (i = 4)).all id = true at h2
      simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq, decide_eq_true_eq] at h0 h2
      cases args with
      | nil => simp [GateOp.eval] at he
      | cons v vs =>
        have a := h0 v (by simp)
        have b := h2 v (by simp)
        omega
    | or =>
      change (args.map fun i => decide (i = 0)).any id = true at h0
      change (args.map fun i => decide (i = 4)).any id = true at h2
      simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq, decide_eq_true_eq] at h0 h2
      have hmem0 : 0 ∈ args := by obtain ⟨v, hv, rfl⟩ := h0; exact hv
      have hmem2 : 4 ∈ args := by obtain ⟨v, hv, rfl⟩ := h2; exact hv
      cases args with
      | nil => simp at hmem0
      | cons a t =>
        cases t with
        | nil => simp at hmem0 hmem2; omega
        | cons b t =>
          cases t with
          | cons c t => simp at hlen
          | nil =>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem0 hmem2
            exact ⟨gs, by rcases hmem0 with h | h <;> rcases hmem2 with k | k <;>
              first | omega | exact Or.inl (by subst a; subst b; rfl) |
                exact Or.inr (by subst a; subst b; rfl)⟩


def firstL : Gate := ⟨.or,[0,4]⟩
def firstR : Gate := ⟨.or,[4,0]⟩
def firstOK (a : Gate) := a = firstL ∨ a = firstR

theorem firstEval (a : Gate) (ha : firstOK a) (x : Fin 9 → Bool) :
    step (List.ofFn x) a = List.ofFn x ++ [x 0 || x 4] := by
  rcases ha with rfl | rfl <;> simp [firstL,firstR,step,GateOp.eval,Bool.or_comm]

def x0 := singleton 0
def x4 (i : Fin 9) := decide (i = 0 ∨ i = 4)

theorem vals : graphF x0 = false ∧ graphF x4 = true ∧
    (x0 0 || x0 4) = (x4 0 || x4 4) ∧ ∀ i ≠ (4 : Fin 9), x0 i = x4 i := by decide +kernel

theorem postRead (a q : Gate) (post : List Gate) (out : ℕ) (ha : firstOK a) (hq : q.op = .not)
    (hc : ∀ x, (⟨a :: q :: post,out⟩ : Circuit).eval (List.ofFn x) = graphF x) :
    (∃ g ∈ post, 4 ∈ g.inputs ∨ 10 ∈ g.inputs) ∧
    (q.inputs.headD 10 ≠ 4 → ∃ g ∈ post, 4 ∈ g.inputs) := by
  let w (x : Fin 9 → Bool) := step (List.ofFn x) a
  let bit (x : Fin 9 → Bool) := q.op.eval (q.inputs.map (fun i => (w x).getD i false))
  have lw (x : Fin 9 → Bool) : (w x).length = 10 := by simp [w,step]
  have pre (i : ℕ) (hi : i ≠ 4) : (w x0).getD i false = (w x4).getD i false := by
    have hh := sameBitsExcept 4 vals.2.2.2 i hi
    simp only [w,firstEval a ha,getDAppendSingleton,List.length_ofFn,hh,vals.2.2.1]
  have readNot (x : Fin 9 → Bool) : bit x = !((w x).getD (q.inputs.headD 10) false) := by
    cases he : q.inputs with
    | nil =>
      simp only [bit,hq,GateOp.eval,he,List.map_nil,List.headD_nil]
      rw [List.getD_eq_default _ _ (by rw [lw])]
    | cons i l => simp [bit,hq,GateOp.eval,he]
  have hout4 : out ≠ 4 := outputNotInput 4 _ hc
  have hout10 : out ≠ 10 := by
    intro eq
    let z : Fin 9 → Bool := fun _ => false
    have clear (i : ℕ) : (w z).getD i false = false := by
      rw [show w z = List.ofFn z ++ [false] from firstEval a ha z,getDAppendSingleton]
      have h := zero_read i
      change (List.ofFn z).getD i false = false at h
      rw [h]
      split <;> simp
    have hh := hc z
    change (post.foldl step (step (w z) q)).getD out false = graphF z at hh
    rw [eq,foldKeep _ _ _ (by simp [step,lw])] at hh
    have hz : graphF z = false := by decide
    have hb : bit z = true := by rw [readNot,clear]; decide
    change ((w z) ++ [bit z]).getD 10 false = _ at hh
    simp [getDAppendSingleton,lw,hz,hb] at hh
  have output (x : Fin 9 → Bool) : (post.foldl step (step (w x) q)).getD out false = graphF x := hc x
  have bad : graphF x0 ≠ graphF x4 := by rw [vals.1,vals.2.1]; decide
  constructor
  · by_contra! hno
    apply bad
    rw [← output,← output]
    apply agreeTwo 4 10 post _ _ (by simp [step,lw]) _
      (fun g hg => (hno g hg).1) (fun g hg => (hno g hg).2) out hout4 hout10
    intro i hi hi'
    simp only [step,getDAppendSingleton,lw,ite_eq_right hi',pre i hi]
  · intro hn
    by_contra! hno
    apply bad
    rw [← output,← output]
    apply foldAgreeExcept post 4 _ _ (by simp [step,lw]) _ hno out hout4
    intro i hi
    have hb : bit x0 = bit x4 := by rw [readNot,readNot,pre _ hn]
    change ((w x0) ++ [bit x0]).getD i false = ((w x4) ++ [bit x4]).getD i false
    simp only [getDAppendSingleton,lw,hb,pre i hi]

def init : List Stat × List Gate := (statAt 8 4 false,[])
def front : List Stat × List Gate := (init.1 ++ [Stat.wire 0],[])
def next (q : Gate) := elimStep 8 front q

theorem firstStep (a : Gate) (ha : firstOK a) : elimStep 8 init a = front := by
  rcases ha with rfl | rfl <;> rfl

theorem nextCase (q : Gate) (hq : q.op = .not) :
    ((next q).2 = [] ∧ ∃ c, (next q).1.getD 10 (Stat.const false) = Stat.const c) ∨
    (∃ j : Fin 8, (next q).2 = [⟨.not,[j.val]⟩] ∧ q.inputs.headD 10 ≠ 4) := by
  have fl : front.1.length = 10 := rfl
  have val (i : ℕ) : (front.1.getD i (Stat.const false)).Valid 8 := by
    let y : Fin 8 → Bool := fun _ => false
    have H := inv_elim 8 (List.ofFn y) (by simp) [firstL] _ init
      (by intro a ha; simp at ha; subst a; simp [firstL,Ok]) (inv_at 8 4 false y)
    have H' := (H.2 i).1
    change ((elimStep 8 init firstL).1.getD i _).Valid (8 + (elimStep 8 init firstL).2.length) at H'
    rw [firstStep firstL (Or.inl rfl)] at H'
    exact H'
  have h4 : front.1.getD 4 (Stat.const false) = Stat.const false := rfl
  have atNext : (next q).1.getD 10 (Stat.const false) =
      (simplify q.op 8 (q.inputs.map fun i => front.1.getD i (Stat.const false))).2 := by
    change (front.1 ++ [_]).getD 10 _ = _
    rw [← fl,getD_snoc_eq]; rfl
  cases h : q.inputs with
  | nil =>
    left
    refine ⟨by simp [next,elimStep,hq,h,simplify,simpNot,front],true,?_⟩
    rw [atNext,hq,h]; rfl
  | cons i l =>
    cases hs : front.1.getD i (Stat.const false) with
    | inl b =>
      left
      refine ⟨?_,!b,?_⟩
      · change ([] ++ (simplify q.op 8 (q.inputs.map fun j => front.1.getD j (Stat.const false))).1.toList) = _
        simp only [hq,h,List.map_cons,hs,simplify,simpNot,Stat.const,Stat.wire,List.nil_append,Option.toList_none]
      · rw [atNext,hq,h]
        simp only [List.map_cons,hs,simplify,simpNot,Stat.const,Stat.wire]
    | inr j =>
      right
      have hh := val i
      rw [hs] at hh
      refine ⟨⟨j,hh⟩,?_,?_⟩
      · change ([] ++ (simplify q.op 8 (q.inputs.map fun j => front.1.getD j (Stat.const false))).1.toList) = _
        simp only [hq,h,List.map_cons,hs,simplify,simpNot,Stat.const,Stat.wire,List.nil_append,Option.toList_some]
      · simp only [h,List.headD_cons]
        rintro rfl
        rw [h4] at hs
        contradiction

theorem programPrefix (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    ∃ tail, (elim n gs acc).2 = acc.2 ++ tail := by
  induction gs generalizing acc with
  | nil => exact ⟨[],by simp [elim]⟩
  | cons g gs ih =>
    obtain ⟨r,h⟩ := ih (elimStep n acc g)
    refine ⟨(simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList ++ r,?_⟩
    change (elim n gs (elimStep n acc g)).2 = _
    rw [h]
    simp [elimStep,List.append_assoc]

theorem compressed (a q : Gate) (post : List Gate) (out : ℕ) (ha : firstOK a) (hq : q.op = .not)
    (hf : FanInTwo (⟨a :: q :: post,out⟩ : Circuit))
    (hc : ∀ x, (⟨a :: q :: post,out⟩ : Circuit).eval (List.ofFn x) = graphF x) :
    ∃ E : Circuit, FanInTwo E ∧ circuitFun 8 E = residualF ∧
      (E.size + 3 ≤ (⟨a :: q :: post,out⟩ : Circuit).size ∨
        (E.size + 2 ≤ (⟨a :: q :: post,out⟩ : Circuit).size ∧
          ∃ j : Fin 8, E.gates.head? = some ⟨.not,[j.val]⟩)) := by
  let gs := post.map normGate
  let raw := a :: q :: gs
  have hok (g : Gate) (hg : g ∈ raw) : Ok g := by
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hf _ (by simp)
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact hf _ (by simp)
      · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
        exact (normGate_nok v (hf v (by simp [hv]))).1
  have hn (g : Gate) (hg : g ∈ gs) : NOk g := by
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok v (hf v (by simp [hv]))
  have hraw (x : Fin 9 → Bool) : (⟨raw,out⟩ : Circuit).eval (List.ofFn x) = graphF x := by
    rw [← hc x]
    change (wiresFrom (post.map normGate) _).getD out false = _
    rw [wiresFrom_norm]; rfl
  let acc := elim 8 gs (next q)
  have he : elim 8 raw init = acc := by
    change elim 8 gs (elimStep 8 (elimStep 8 init a) q) = _
    rw [firstStep a ha]
    rfl
  have val (y : Fin 8 → Bool) :
      (acc.1.getD out (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = residualF y := by
    have hh := ((inv_elim 8 _ (by simp) raw _ init hok (inv_at 8 4 false y)).2 out).2
    rw [he] at hh
    exact hh.trans ((hraw _).trans (cofactor4 y))
  have l : (next q).1.length = 11 := by rfl
  have fix4 : (next q).1.getD 4 (Stat.const false) = Stat.const false := by rfl
  have needed := postRead a q gs out ha hq hraw
  cases hs : acc.1.getD out (Stat.const false) with
  | inl b =>
    have h0 := val (fun _ => false)
    have h1 := val (fun _ => true)
    rw [hs] at h0 h1
    exact (Bool.false_ne_true (h0.symm.trans h1)).elim
  | inr j =>
    let E : Circuit := ⟨acc.2,j⟩
    have hfE (g : Gate) (hg : g ∈ acc.2) : Ok g := by
      rw [← he] at hg
      exact elim_ok _ raw init (by simp [init]) g hg
    refine ⟨E,hfE,?_,?_⟩
    · funext y
      have hh := val y
      rw [hs] at hh
      exact hh
    · rcases nextCase q hq with ⟨hzero,c,hconst⟩ | ⟨i,hfirst,ine⟩
      · left
        obtain ⟨g,hg,h4 | h10⟩ := needed.1
        all_goals
          first | have save := elim_len_lt 8 4 gs (next q) hn (by omega)
                    ⟨false,fix4⟩ ⟨g,hg,h4⟩
                | have save := elim_len_lt 8 10 gs (next q) hn (by omega)
                    ⟨c,hconst⟩ ⟨g,hg,h10⟩
          change acc.2.length + 1 ≤ (next q).2.length + gs.length at save
          rw [hzero] at save
          change acc.2.length + 3 ≤ (a :: q :: post).length
          simp only [gs,List.length_map,List.length_nil] at save
          simp only [List.length_cons]; omega
      · right
        have save := elim_len_lt 8 4 gs (next q) hn (by omega) ⟨false,fix4⟩ (needed.2 ine)
        change acc.2.length + 1 ≤ (next q).2.length + gs.length at save
        rw [hfirst] at save
        refine ⟨?_,i,?_⟩
        · change acc.2.length + 2 ≤ (a :: q :: post).length
          simp only [gs,List.length_map,List.length_singleton] at save
          simp only [List.length_cons]; omega
        · obtain ⟨r,hr⟩ := programPrefix 8 gs (next q)
          change (elim 8 gs (next q)).2.head? = _
          rw [hr,hfirst]; rfl



end Cof2153

namespace Search2153

abbrev B := BitVec 252
abbrev Sig := B × B
def top : B := BitVec.allOnes 252
def zero : Sig := (0,0)
def one : Sig := (top,top)
def target : Sig := (top,0)
def neg (a : Sig) : Sig := (~~~a.1,~~~a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~a.2
def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a::l => sep d a ||| unionSep d l

def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))

abbrev Cov := B × B × B

def addCov (z : B) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => addCov (sep d a) c) (0,0,0)

def takeOne (c : Cov) (a : B) : B := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : B) : B :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

theorem cov_one (c : Cov) (a : B) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

theorem cov_two (c : Cov) (a b : B) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

theorem add_swap (c : Cov) (a b : B) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

theorem cov_perm (d : Bool) {l r : List Sig} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (sep d a)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

theorem cov_union (d : Bool) (v : List Sig) : (coverage d v).1=unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = (sep d a ||| unionSep d v); rw [ih]

lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]



-- Each bit position pairs a positive and a negative input row.
def raw0 : Sig := (0x988c662c60004200118004e25321040016c0030d9e4a00039fffd8007000fff, 0x988c622c6d1042d111b44462532105c212dc21048e4ae20089c49b883710712)
def raw1 : Sig := (0x2130860080010c00060007c01c3e180027000332607ffff2640020007ffffff, 0x2130840090850d0886422180040e1a2125221210201110d226222444488a88c)
def raw2 : Sig := (0xf88f000070001800070463c0200039fffcc3878c001c78003fff9fff000, 0x288f043070431810c6040140208600486843828c4604588c09191234230)
def raw3 : Sig := (0xc03f0130000180001ffff8387c07c0003e0000fc07f0001f80003fffe000000, 0xc015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8)
def raw4 : Sig := (0x1c001c00001ffffe000003f8007ffffc00000fff800001fffffc0000000000, 0x1c000659406c001a00c8002680d8000d0fb70000c9f741b00340068068)
def raw5 : Sig := (0xfe0001fffffe00000000003ffff80000000000ffffffffe0000000000000000, 0xca0001f5217800170005c03ffbf0004e0004e0efdfee2f00005c00b80170170)
def raw6 : Sig := (0xfffffe00000000000000003fffffffffffffff0000000000000000000000000, 0xffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80)
def raw7 : Sig := (0xffffffffffffffffffffffc0000000000000000000000000000000000000000, 0x35eafe0ade006be01d7807c000000380003800000001c000038007000e00e00)

def raw : List Sig := [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

-- A set records the distinct signals needed by the remaining gates.
-- Read backwards, a gate replaces its output with the operand or operands.
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U))

lemma target_proper : proper target := by unfold proper target zero one top; decide
lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

lemma sep_unary (t : Nat) (a : Sig) (i : Nat)
    (h : (sep (decide (0<t)) (neg a)).getLsbD i = true) :
    (sep true a).getLsbD i = true := by
  by_cases hi : i < 252
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 252 ≤ i)] at h

lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 252
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 252 ≤ i)] at h

lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 252)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 252) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 252 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 252)] <;> simp [hi]
  | unary ha hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,sep_unary _ _ _ h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,sep_weaken _ _ _ hi h⟩
  | binary ha hb hab hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ _ _ _ h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp] <;> aesop

lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset=S) :
    unionSep (decide (0<t)) v = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,hm,ha⟩ := live_sep h i hi
  have hmem : a ∈ v := List.mem_toFinset.mp (he.symm ▸ hm)
  simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using (mem_unionSep _ _ _).2 ⟨a,hmem,ha⟩

lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l++r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep,ih,BitVec.or_assoc]

def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))

lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    change x ∈ v ↔ _
    rw [← List.mem_toFinset,he]
    simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq
    subst b
    simp [keepOf] at ha
    simp [dropped] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,keepOf,dropped,decide_eq_true_eq,
      Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all

lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e
    subst b
    simp [dropped] at hb
    exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,dropped,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all

lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (ha : a ∈ v) :
    v.length-1=(dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a)=unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_one _ _).trans (cov_union _ _)

lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length-2=(dropped [a,b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b)=unionSep d (dropped [a,b] v) := by
  have p := recover_perm [a,b] v hv (by simp [hab]) (by simp [ha,hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_two _ _ _).trans (cov_union _ _)

open PEqualNP.CircuitLowerBounds

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p,n⟩ := a
  simp only [bin,one,zero,top,reduceCtorEq,ite_true,ite_false,BitVec.and_allOnes,BitVec.or_allOnes,BitVec.and_zero,BitVec.or_zero,BitVec.and_self,BitVec.or_self,Prod.mk.injEq,and_self] <;> simp

lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one,top]

lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (side : Bool) (i : Fin 252) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 252).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
lemma bit_neg (s i) (a : Sig) : bit s i (neg a) = !(bit s i a) := by
  cases s <;> simp only [bit,neg,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp only [bit,bin,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]

lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl

lemma run_bit (s i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit s i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _ _

lemma execute_bits (gs : List Gate) (s i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit s i g w (hg g (by simp))]

def sample (s : Bool) (i : Fin 252) (j : Fin 8) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)

lemma sample_ok : ∀ (s : Bool) (i : Fin 252), edgeF (sample s i) = s := by decide +kernel
lemma raw_id : List.ofFn (fun j : Fin 8 => raw.getD j.val zero) = raw := by rfl
lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 8 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel


def gateAvailable (v : List Sig) (g : Sig) : Bool :=
  !(v.contains g) && g != zero && g != one

def tryGate (k t : Nat) (r : List Sig → Bool) (v rest : List Sig) (n : Nat) (c : B) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  let d := decide (0<t)
  let base := sep d g ||| c
  if n = k-t then
    base == top && gateAvailable v g && r (g::rest)
  else keep.any (fun h => decide (n+h.length+1 ≤ k-t+1) &&
    (base ||| unionSep d h == top) && gateAvailable v g && r (g::(h++rest)))

def scanPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => false
  | a :: t => t.any (p a) || scanPairs p t

lemma scanPairs_complete {α : Type} (p : α → α → Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b = true) (hba : p b a = true) : scanPairs p v = true := by
  induction v with
  | nil => simp at ha
  | cons h v ih =>
    simp only [scanPairs, Bool.or_eq_true]
    by_cases eqA : a = h
    · subst h
      exact Or.inl (List.any_eq_true.mpr ⟨b, (List.mem_cons.mp hb).resolve_left (Ne.symm hne), hab⟩)
    · have ha' := (List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b = h
      · subst h
        exact Or.inl (List.any_eq_true.mpr ⟨a, ha', hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))

end Search2153

namespace Search2153

inductive SignedRestricted (pos negS : List Sig) : Nat → Nat → Finset Sig → Prop
  | stop : SignedRestricted pos negS 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (fresh : neg a ∉ insert a U) (notPos : a ∉ pos) (notNeg : a ∉ negS)
      (tail : SignedRestricted pos negS k t (insert (neg a) U)) :
      SignedRestricted pos negS (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (fresh : bin d a b ∉ insert a (insert b U))
      (aPos : a ∈ pos → d = true ∧ a ∉ U) (bPos : b ∈ pos → d = true ∧ b ∉ U)
      (aNeg : a ∈ negS → d = false ∧ a ∉ U) (bNeg : b ∈ negS → d = false ∧ b ∉ U)
      (tail : SignedRestricted pos negS k t (insert (bin d a b) U)) :
      SignedRestricted pos negS (k+1) t (insert a (insert b U))

theorem SignedRestricted.live {pos negS : List Sig} {k t S} (h : SignedRestricted pos negS k t S) : Live k t S := by
  induction h with
  | stop => exact Live.stop
  | unary h f _ _ _ ih => exact Live.unary h f ih
  | binary a b n f _ _ _ _ _ ih => exact Live.binary a b n f ih

theorem signedFree {k t S} (h : Live k t S) : SignedRestricted [] [] k t S := by
  induction h with
  | stop => exact SignedRestricted.stop
  | unary a f _ ih => exact SignedRestricted.unary a f (by simp) (by simp) ih
  | binary a b ne f _ ih => exact SignedRestricted.binary a b ne f (by simp) (by simp) (by simp) (by simp) ih

end Search2153

namespace Projection2153
open Search2153
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pos0 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cb70ca41b4174c6b5c8dc87531b7a7a7a5074cd8a3e7ab966b5620c41cd99c659b5a7f5391beb8f399eb78a62dc8d4ea48db9593e7aec79a7c8b9b766e71b7a74f5ecdcc88f3e1b4141418a74b9505341cd0cec62667ab940f59beca7c6921beb87925db75062c89689e796cd9b5341b579a7dccdb7cddca741e29253e7a49bb5a77a7a7a50e20c8aec7a66b953f0cd410ccc928f531b39f5a7e359f5f4b78af0a49fdbdc9f668fec7a3ee41be766b7b9c8a77ae2393ea4e759eca74141418ae26650b5410ccd3ef0b97a66fa39873e1b92c6a7e39bc6f9b750f0e760f2c8600c87b54153e41ba40c

def neg0 : Nat := 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a51d000e00000eafaf3ca338a54e90779706a54e970505a39003060202a3970b06071d90030e0b653805a53c054e074e0b03af363c38e807a5a5a51d000e00000eafaf51e84ea538361a0306a538030505e83697066c6ce8030b06071d36970e0b654e05a551053807380b97af90514ea307a5a5a51d00af0000af0e0e774ee8a5a3363c0307a5a3030b0b4e36970744444e030507061d3697af0558e80ba5770ba306a305970e9077e83806a5a5a51d00af0000af0e0e1a38a3a5e890519707a5e8970b0b389003072c2c38970507061d9003af0558a30ba51a0be806e805030e361aa34e06a5a5a5

def pos3 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c360c3900664ec837c687dc6400cdcdcd724e7ad9a2cdb94137e50c667a91c8e7372a9ba4005d92a4f936d9e587de7439deb9e7a2cd574f2ac6b936415900cd4e9b5787c692a200666666d94eb97264667a0c57e541cdb9a69bf5572ac88f005ddc8feb3672e5c694db59947af56466374f2a877a367a872a66f28f645939f5372acdcdcd72f20cd957cd41b9645b7a660cca8f926400a49b2af4e79be336d95b39f78987f7419257cda2f300594136b9c62acdf2a4a23959e7572a666666d9f2417237660c7aa25bb9cd419da4dca2008fc82af4f5c89e36725b59e9e2c6e90cdc376664f300390c

def neg3 : Nat := 0x36363636363636363636363636363636363636360100020000022c2ca238a33665904d910a3665910b0b3890090a0e0e3891050a0401900902054ea30b36a20b65046505092ca5a2a358043636360100020000022c2c64586536a3a518090a36a3090b0b58a5910a44445809050a0401a59102054e650b36640ba304a305912c906465380436363601002c00002c02024d65583638a5a20904363809050565a591046c6c65090b040a01a5912c0be85805364d05380a380b9102904d58a30a36363601002c00002c020218a3383658906491043658910505a3900904afafa3910b040a0190092c0be83805361805580a580b0902a51838650a363636

def pos5 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c890c39660029c687c837b57266a7a7a764292aece7a7b91b87e90c002a78c6a2877a3ba4664019a4b889ece937f01839f0b9a2e7a78a797ac8b9891b3e66a7293b8a37c819e766000000ec29b96472002a0c8ae91ba7b9eb3bb38a7ac6276640b527a68964e9c875b73e752ab3720087797a372a892a377a00c527723e39b3877aa7a7a764c50cec8aa71bb9728d2a000cf427197266a43b7acaa23bcc89ec8d39ee3637ee1b198aa7e7f3663e1b89b9c87aa7c5a4e7393ea28a7a000000ecc51b6487000c2ae78db9a71b8ca4b5e76627c67acab3c63d89648d3ee5cbc8e50cb5870072f366390c

def neg5 : Nat := 0x38383838383838383838383838383838383838386c000e00000e2c2ce836a538181977750a381875090936190b0a02023675030a076c190b0e031aa50938e809180718030b2ca3e8a53c073838386c000e00000e2c2c643c1838a5a3650b0a38a50b09093ca3750a1d1d3c0b030a076ca3750e031a1809386409a507a503752c19641836073838386c002c00002c0e0e77183c3836a3e80b0738360b030318a375070101180b09070a6ca3752c09a23c03387703360a3609750e19773ca50a3838386c002c00002c0e0e65a536383c19647507383c750303a5190b07afafa57509070a6c190b2c09a236033865033c0a3c090b0ea36536180a383838

def pos6 : Nat := 0xdb00a2412a18b3d9b5c62759411b1b1b5718b953501ba70cd960002ab95db33bd9cdc81941a6371940db5360c65536a255a73b501bdc4fcdb5a7db0ca4411b18c8dcc6b53750412a2a2a5318a757592ab900dc600c1ba752c83edccdb33941a627393ddb5760b55b29a45bb93e592ad94fcdc6b9dbb9c6cd2acb3959a4a23ed9cd1b1b1b57cb0053dc1b0ca759deb92a00e13937594119c8cdcc3bc8b8db53dea262c5c6620c37dc1b50e441a40cdba7b5cd1bcb1950a2a43bdccd2a2a2a53cb0c57d92a00b950dea71b0ce31927504139b3cdcc3eb3cadb57dea45eb7b55e0027d92a59e441a200

def neg6 : Nat := 0xa3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3440002000002afaf51a21aa336384e0506a336050303a23852060101a2050906044438520209181a03a351033604360952af19511aa504a3a3a3440002000002afaf58a536a31a194d5206a31a520303a51905060e0ea5520906044419050209183603a358031a041a0905af385836a204a3a3a34400af0000af02024e36a5a3a219515204a3a2520909361905042c2c3652030406441905af033ca509a34e09a206a2030502384ea51a06a3a3a34400af0000af02024d1aa2a3a538580504a3a50509091a3852041d1d1a05030406443852af033ca209a34d09a506a5035202194da23606a3a3a3

def marker : Fin 4 → Sig := ![raw0, raw3, raw5, raw6]
def posKey : Fin 4 → Nat := ![pos0, pos3, pos5, pos6]
def negKey : Fin 4 → Nat := ![neg0, neg3, neg5, neg6]

def index (key : Nat) (j : Fin 252) : Fin 252 := Fin.ofNat 252 ((key >>> (8 * j.val)) &&& 255)

def reindex (f : Fin 252 → Fin 252) (x : B) : B :=
  (BitVec.ofBoolListLE (List.ofFn fun j => x.getLsbD (f j).val)).cast List.length_ofFn

lemma reindex_bit (f : Fin 252 → Fin 252) (a : B) (j : Nat) (hj : j < 252) :
    (reindex f a).getLsbD j = a.getLsbD (f ⟨j,hj⟩).val := by
  rw [reindex, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  have h : j < (List.ofFn fun x => a.getLsbD (f x).val).length := by simpa only [List.length_ofFn] using hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_ofFn h

lemma reindex_and (f : Fin 252 → Fin 252) (a b : B) :
    reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_and, reindex_bit _ _ _ hj]

lemma reindex_or (f : Fin 252 → Fin 252) (a b : B) :
    reindex f (a ||| b) = reindex f a ||| reindex f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, reindex_bit _ _ _ hj]

lemma reindex_not (f : Fin 252 → Fin 252) (a : B) :
    reindex f (~~~a) = ~~~reindex f a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_not, reindex_bit _ _ _ hj, hj, (f ⟨j,hj⟩).isLt, decide_true, Bool.true_and]

lemma reindex_zero (f : Fin 252 → Fin 252) : reindex f 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [reindex_bit _ _ _ hj]
  simp

lemma reindex_top (f : Fin 252 → Fin 252) : reindex f top = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [top, reindex_bit _ _ _ hj, BitVec.getLsbD_allOnes, hj, (f ⟨j,hj⟩).isLt, decide_true]

def project (i : Fin 4) (a : Sig) : Sig :=
  (reindex (index (posKey i)) a.1, reindex (index (negKey i)) a.2)

lemma project_neg (i : Fin 4) (a : Sig) : project i (neg a) = neg (project i a) := by
  simp [project, neg, reindex_not]

lemma project_bin (i : Fin 4) (d : Bool) (a b : Sig) :
    project i (bin d a b) = bin d (project i a) (project i b) := by
  cases d <;> simp [project, bin, reindex_and, reindex_or]

lemma project_target (i : Fin 4) : project i target = target :=
  Prod.ext (reindex_top _) (reindex_zero _)

set_option maxRecDepth 10000 in
lemma project_marker : ∀ i, project i (marker i) = zero := by decide +kernel

def thetaInputOrder : Fin 4 → List Sig :=
  ![[raw2,raw7,raw3,raw1,raw5,raw6,raw4], [raw1,raw4,raw0,raw2,raw6,raw5,raw7],
    [raw2,raw4,raw6,raw1,raw0,raw3,raw7], [raw1,raw7,raw5,raw0,raw4,raw2,raw3]]

def thetaInputs (i : Fin 4) : List Sig := (thetaInputOrder i).map (project i)

lemma thetaOrder (i : Fin 4) :
    (thetaInputOrder i).toFinset = raw.toFinset.erase (marker i) := by
  fin_cases i <;> decide +kernel

lemma marker_in_raw (i : Fin 4) : marker i ∈ raw.toFinset := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
lemma project_raw (i : Fin 4) :
    raw.toFinset.image (project i) = insert zero (thetaInputs i).toFinset := by
  have hm : (thetaInputs i).toFinset = ((thetaInputOrder i).toFinset).image (project i) := by
    ext a
    simp [thetaInputs, Finset.mem_image, List.mem_map, and_comm]
  rw [hm, thetaOrder, ← project_marker i, ← Finset.image_insert,
    Finset.insert_erase (marker_in_raw i)]

def Feasible (i : Fin 4) (k : Nat) (S : Finset Sig) : Prop :=
  ∃ m ≤ k, ∃ t T, Live m t T ∧ T ⊆ S.image (project i)

lemma feasible_mono {i : Fin 4} {k k' : Nat} {S : Finset Sig}
    (h : Feasible i k S) (hk : k ≤ k') : Feasible i k' S := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h
  exact ⟨m, hm.trans hk, t, T, hl, hs⟩

lemma neg_rep (w : List Sig) (a : Sig) (ha : a ∈ w) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases (Or.inl ha : represented w a) with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr (fun hh => hh.2 neg_laws.1))
  · exact Or.inl (Or.inr (fun hh => hh.1 neg_laws.2))
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

lemma feasible_pull {i : Fin 4} {q : Nat} {S S' : Finset Sig} {g : Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image (project i)).toList (project i g) ∨
      witness (S.image (project i)).toList (project i g))
    (h : Feasible i q S') : Feasible i (q + 1) S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  have sub : ∀ a ∈ T, a ∈ (S.image (project i)).toList ++ [project i g] := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (ht ha)
    rcases Finset.mem_insert.mp (hs hb) with rfl | hb
    · simp
    · exact List.mem_append_left _ (Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hb))
  obtain ⟨m', t', T', hm', h', hT'⟩ := pull_gate hl hr sub
  exact ⟨m', by omega, t', T', h', fun a ha => Finset.mem_toList.mp (hT' _ ha)⟩

lemma feasible_free {i : Fin 4} {q : Nat} {S S' : Finset Sig} {g : Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image (project i)).toList (project i g))
    (h : Feasible i q S') : Feasible i q S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  refine ⟨m, hm, t, T, hl, ?_⟩
  intro a ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (ht ha)
  rcases Finset.mem_insert.mp (hs hb) with rfl | hb
  · exact Finset.mem_toList.mp (hr.resolve_right (fun hp => hp (live_proper hl _ ha)))
  · exact Finset.mem_image_of_mem _ hb

lemma pull_unary {i : Fin 4} {q : Nat} {a : Sig} {U : Finset Sig}
    (h : Feasible i q (insert (neg a) U)) :
    Feasible i (q+1) (insert a U) := by
  apply feasible_pull (g := neg a) (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rw [project_neg]
  exact neg_rep _ _ (by simp)

lemma pull_binary {i : Fin 4} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (h : Feasible i q (insert (bin d a b) U)) :
    Feasible i (q+1) (insert a (insert b U)) := by
  apply feasible_pull (g := bin d a b) (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rw [project_bin]
  exact bin_rep _ (Or.inl (by simp)) (Or.inl (by simp))

lemma free_unary {i : Fin 4} {q : Nat} {a : Sig} {U : Finset Sig}
    (ha : ¬ proper (project i a))
    (h : Feasible i q (insert (neg a) U)) :
    Feasible i q (insert a U) := by
  apply feasible_free (g := neg a) (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rcases operand_cases (Or.inr ha : represented [] (project i a)) with hz | ho | hm
  · exact Or.inr (fun hp => hp.2 (by rw [project_neg,hz,neg_laws.1]))
  · exact Or.inr (fun hp => hp.1 (by rw [project_neg,ho,neg_laws.2]))
  · simp at hm

lemma free_binary_left {i : Fin 4} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (ha : ¬ proper (project i a))
    (h : Feasible i q (insert (bin d a b) U)) :
    Feasible i q (insert a (insert b U)) := by
  apply feasible_free (g := bin d a b) (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rw [project_bin, bin_comm]
  rcases operand_cases (Or.inr ha : represented [] (project i a)) with hz | ho | hm
  · rw [hz]
    cases d
    · exact Or.inr (fun hp => hp.1 (bin_laws _).2.2.1)
    · rw [(bin_laws _).2.1]
      exact Or.inl (by simp)
  · rw [ho]
    cases d
    · rw [(bin_laws _).1]
      exact Or.inl (by simp)
    · exact Or.inr (fun hp => hp.2 (bin_laws _).2.2.2.1)
  · simp at hm

lemma free_binary_right {i : Fin 4} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (hb : ¬ proper (project i b))
    (h : Feasible i q (insert (bin d a b) U)) :
    Feasible i q (insert a (insert b U)) := by
  rw [bin_comm] at h
  rw [Finset.insert_comm]
  exact free_binary_left hb h

lemma feasible_live {k t : Nat} {S : Finset Sig} (h : Live k t S) (i : Fin 4) :
    Feasible i k S := by
  induction h with
  | stop =>
    refine ⟨0, Nat.le_refl _, 0, {target}, Live.stop, ?_⟩
    simp [project_target]
  | unary _ _ _ ih => exact pull_unary ih
  | binary _ _ _ _ _ ih => exact pull_binary ih

lemma feasible_const {k t : Nat} {S : Finset Sig} (h : Live k t S)
    (i : Fin 4) (a : Sig) (ha : a ∈ S) (hc : ¬ proper (project i a)) :
    ∃ q < k, Feasible i q S := by
  induction h with
  | stop =>
    have ht : a = target := Finset.mem_singleton.mp ha
    exact (hc (by rw [ht, project_target]; exact target_proper)).elim
  | @unary k t U b hp hf tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨k, by omega, free_unary hc (feasible_live tail i)⟩
    · obtain ⟨q,hq,h⟩ := ih (Finset.mem_insert_of_mem ha)
      exact ⟨q+1,by omega,pull_unary h⟩
  | @binary k t U b c d hb hc' hbc hf tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | hU
    · exact ⟨k, by omega, free_binary_left hc (feasible_live tail i)⟩
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact ⟨k, by omega, free_binary_right hc (feasible_live tail i)⟩
      · obtain ⟨q,hq,h⟩ := ih (Finset.mem_insert_of_mem hU)
        exact ⟨q+1,by omega,pull_binary h⟩

lemma not_proper_bin_consts {i : Fin 4} {a b : Sig}
    (d : Bool) (ha : ¬proper (project i a)) (hb : ¬proper (project i b)) :
    ¬proper (project i (bin d a b)) := by
  rw [project_bin]
  rcases operand_cases (Or.inr ha : represented [] (project i a)) with h | h | h <;>
    rcases operand_cases (Or.inr hb : represented [] (project i b)) with j | j | j <;>
    simp_all [proper,bin,one,zero,top]

lemma feasible_two_consts {k t : Nat} {S : Finset Sig} (h : Live k t S) (i : Fin 4)
    (a b : Sig) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hca : ¬ proper (project i a)) (hcb : ¬ proper (project i b)) :
    ∃ q, q + 2 ≤ k ∧ Feasible i q S := by
  induction h with
  | stop =>
    have e1 := Finset.mem_singleton.mp ha
    have e2 := Finset.mem_singleton.mp hb
    exact (hab (e1.trans e2.symm)).elim
  | @unary k t U c hpc _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | haU
    · have hbU : b ∈ U := (Finset.mem_insert.mp hb).resolve_left hab.symm
      obtain ⟨q, hq, hf⟩ := feasible_const tail i b (Finset.mem_insert_of_mem hbU) hcb
      exact ⟨q, by omega, free_unary hca hf⟩
    · rcases Finset.mem_insert.mp hb with rfl | hbU
      · obtain ⟨q, hq, hf⟩ := feasible_const tail i a (Finset.mem_insert_of_mem haU) hca
        exact ⟨q, by omega, free_unary hcb hf⟩
      · obtain ⟨q, hq, hf⟩ := ih (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU)
        exact ⟨q + 1, by omega, pull_unary hf⟩
  | @binary k t U c e d _ _ _ _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha1
    · rcases Finset.mem_insert.mp hb with hbEq | hb1
      · exact (hab hbEq.symm).elim
      · rcases Finset.mem_insert.mp hb1 with rfl | hbU
        · obtain ⟨q, hq, hf⟩ := feasible_const tail i (bin d a b) (Finset.mem_insert_self _ _)
            (not_proper_bin_consts d hca hcb)
          exact ⟨q, by omega, free_binary_left hca hf⟩
        · obtain ⟨q, hq, hf⟩ := feasible_const tail i b (Finset.mem_insert_of_mem hbU) hcb
          exact ⟨q, by omega, free_binary_left hca hf⟩
    · rcases Finset.mem_insert.mp ha1 with rfl | haU
      · rcases Finset.mem_insert.mp hb with rfl | hb1
        · obtain ⟨q, hq, hf⟩ := feasible_const tail i (bin d b a) (Finset.mem_insert_self _ _)
            (not_proper_bin_consts d hcb hca)
          exact ⟨q, by omega, free_binary_left hcb hf⟩
        · rcases Finset.mem_insert.mp hb1 with hbEq | hbU
          · exact (hab hbEq.symm).elim
          · obtain ⟨q, hq, hf⟩ := feasible_const tail i b (Finset.mem_insert_of_mem hbU) hcb
            exact ⟨q, by omega, free_binary_right hca hf⟩
      · rcases Finset.mem_insert.mp hb with rfl | hb1
        · obtain ⟨q, hq, hf⟩ := feasible_const tail i a (Finset.mem_insert_of_mem haU) hca
          exact ⟨q, by omega, free_binary_left hcb hf⟩
        · rcases Finset.mem_insert.mp hb1 with rfl | hbU
          · obtain ⟨q, hq, hf⟩ := feasible_const tail i a (Finset.mem_insert_of_mem haU) hca
            exact ⟨q, by omega, free_binary_right hcb hf⟩
          · obtain ⟨q, hq, hf⟩ := ih (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU)
            exact ⟨q + 1, by omega, pull_binary hf⟩

def thetaRaw := thetaInputs 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma thetaInputs_eq : ∀ i, thetaInputs i = thetaRaw := by decide +kernel

def ThetaNumeric : Prop :=
  ∀ (j : Fin 7) (k t : Nat) (T : Finset Sig), k ≤ 10 → Live k t T →
    T ⊆ insert (neg (thetaRaw.getD j.val zero)) thetaRaw.toFinset → False

lemma signed_project_impossible (num : ThetaNumeric) (i : Fin 4) (p : Sig)
    (hp : p ∈ raw.toFinset) : ¬Feasible i 10 (insert (neg p) raw.toFinset) := by
  intro ⟨k,hk,t,T,hl,sub⟩
  have rp : project i p ∈ insert zero thetaRaw.toFinset := by
    rw [← thetaInputs_eq i, ← project_raw]
    exact Finset.mem_image_of_mem _ hp
  rw [Finset.image_insert,project_raw,thetaInputs_eq,project_neg] at sub
  rcases Finset.mem_insert.mp rp with hz | hraw
  · apply num 0 k t T hk hl
    intro a ha
    rcases Finset.mem_insert.mp (sub ha) with h | h
    · exact ((live_proper hl a ha).2 (by rw [h,hz,neg_laws.1])).elim
    rcases Finset.mem_insert.mp h with h | h
    · exact ((live_proper hl a ha).1 h).elim
    · exact Finset.mem_insert_of_mem h
  · obtain ⟨j,hj,hval⟩ := List.getElem_of_mem (List.mem_toFinset.mp hraw)
    have len : thetaRaw.length = 7 := rfl
    have val : thetaRaw.getD j zero = project i p := by
      rw [List.getD_eq_getElem _ _ hj, hval]
    apply num ⟨j,by omega⟩ k t T hk hl
    intro a ha
    rcases Finset.mem_insert.mp (sub ha) with h | h
    · exact Finset.mem_insert.mpr (Or.inl (h.trans (congrArg neg val.symm)))
    rcases Finset.mem_insert.mp h with h | h
    · exact ((live_proper hl a ha).1 h).elim
    · exact Finset.mem_insert_of_mem h

end Projection2153

namespace Projection2153
open Search2153

def invert (mode : Bool) (i : Fin 4) := mode && decide (i = 0)
def mark (mode : Bool) (i : Fin 4) :=
  if invert mode i then neg (marker i) else marker i
def posMarks (mode : Bool) : List Sig :=
  if mode then [raw3, raw5, raw6] else [raw0, raw3, raw5, raw6]
def negMarks (mode : Bool) : List Sig := if mode then [neg raw0] else []

lemma mark_value (mode : Bool) (i : Fin 4) :
    project i (mark mode i) = if invert mode i then one else zero := by
  cases h : invert mode i <;> simp only [mark,h,ite_false,ite_true,Bool.false_eq_true,
    project_neg,project_marker,neg_laws.1]

lemma mark_improper (mode : Bool) (i : Fin 4) : ¬proper (project i (mark mode i)) := by
  rw [mark_value]
  cases invert mode i <;> simp [proper]

def ProjectBound (mode : Bool) (k : Nat) (S : Finset Sig) : Prop :=
  ∀ i q, q + (if mark mode i ∈ S then 1 else 0) < k → ¬Feasible i q S

lemma project_bound_root {mode : Bool} {k : Nat} {S : Finset Sig} (hk : k ≤ 12)
    (marks : ∀ i, mark mode i ∈ S) (no10 : ∀ i, ¬Feasible i 10 S) :
    ProjectBound mode k S := by
  intro i q hq h
  rw [if_pos (marks i)] at hq
  exact no10 i (feasible_mono h (by omega))

lemma bound_unary {mode : Bool} {k : Nat} {a : Sig} {U : Finset Sig}
    (h : ProjectBound mode (k+1) (insert a U)) :
    ProjectBound mode k (insert (neg a) U) := by
  intro i q hq hf
  by_cases hp : mark mode i ∈ insert a U
  · by_cases ht : mark mode i ∈ insert (neg a) U
    · rw [if_pos ht] at hq
      exact h i (q+1) (by simp [hp]; omega) (pull_unary hf)
    · rw [if_neg ht] at hq
      have he : mark mode i = a :=
        (Finset.mem_insert.mp hp).resolve_right (fun hm => ht (Finset.mem_insert_of_mem hm))
      have hz : ¬ proper (project i a) := by rw [← he]; exact mark_improper mode i
      exact h i q (by simp [hp]; omega) (free_unary hz hf)
  · exact h i (q+1) (by simp [hp]; split at hq <;> omega) (pull_unary hf)

lemma bound_binary {mode : Bool} {k : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (h : ProjectBound mode (k+1) (insert a (insert b U))) :
    ProjectBound mode k (insert (bin d a b) U) := by
  intro i q hq hf
  by_cases hp : mark mode i ∈ insert a (insert b U)
  · by_cases ht : mark mode i ∈ insert (bin d a b) U
    · rw [if_pos ht] at hq
      exact h i (q+1) (by simp [hp]; omega) (pull_binary hf)
    · rw [if_neg ht] at hq
      rcases Finset.mem_insert.mp hp with ha | hb
      · have hz : ¬ proper (project i a) := by rw [← ha]; exact mark_improper mode i
        exact h i q (by simp [hp]; omega) (free_binary_left hz hf)
      · rcases Finset.mem_insert.mp hb with hb | hU
        · have hz : ¬ proper (project i b) := by rw [← hb]; exact mark_improper mode i
          exact h i q (by simp [hp]; omega) (free_binary_right hz hf)
        · exact (ht (Finset.mem_insert_of_mem hU)).elim
  · exact h i (q+1) (by simp [hp]; split at hq <;> omega) (pull_binary hf)


lemma pos_repr {mode : Bool} {a : Sig} (ha : a ∈ posMarks mode) :
    ∃ i, a = mark mode i ∧ invert mode i = false := by
  cases mode
  · simp only [posMarks, Bool.false_eq_true, if_false, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨0,rfl,rfl⟩
    · exact ⟨1,rfl,rfl⟩
    · exact ⟨2,rfl,rfl⟩
    · exact ⟨3,rfl,rfl⟩
  · simp only [posMarks, if_true, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨1,rfl,rfl⟩
    · exact ⟨2,rfl,rfl⟩
    · exact ⟨3,rfl,rfl⟩

lemma neg_repr {mode : Bool} {a : Sig} (ha : a ∈ negMarks mode) :
    ∃ i, a = mark mode i ∧ invert mode i = true := by
  cases mode
  · simp [negMarks] at ha
  · simp [negMarks] at ha
    exact ⟨0,ha,rfl⟩

lemma mark_unary {mode : Bool} {k t : Nat} {U : Finset Sig} (i : Fin 4)
    (h : ProjectBound mode (k+1) (insert (mark mode i) U))
    (tail : Live k t (insert (neg (mark mode i)) U)) : False := by
  have ho : ¬proper (project i (neg (mark mode i))) := by
    rw [project_neg,mark_value]
    cases invert mode i <;> simp [neg_laws.1,neg_laws.2,proper]
  obtain ⟨q,hq,hf⟩ := feasible_const tail i _ (Finset.mem_insert_self _ _) ho
  exact h i q (by simp; omega) (free_unary (mark_improper mode i) hf)

lemma mark_binary {mode : Bool} {k t : Nat} {b : Sig} {d : Bool} {U : Finset Sig}
    (i : Fin 4) (h : ProjectBound mode (k+1) (insert (mark mode i) (insert b U)))
    (tail : Live k t (insert (bin d (mark mode i) b) U)) :
    d = !(invert mode i) ∧ mark mode i ∉ U := by
  have hz := mark_improper mode i
  constructor
  · by_contra hn
    have hc : ¬proper (project i (bin d (mark mode i) b)) := by
      rw [project_bin,mark_value,bin_comm]
      cases val : invert mode i <;> cases d <;> simp_all [proper,bin_laws]
    obtain ⟨q,hq,hf⟩ := feasible_const tail i _ (Finset.mem_insert_self _ _) hc
    exact h i q (by simp; omega) (free_binary_left hz hf)
  · intro hm
    obtain ⟨q,hq,hf⟩ := feasible_const tail i _ (Finset.mem_insert_of_mem hm) hz
    exact h i q (by simp; omega) (free_binary_left hz hf)

theorem restrict_signed {mode : Bool} {k t : Nat} {S : Finset Sig}
    (hl : Live k t S) (hb : ProjectBound mode k S) :
    SignedRestricted (posMarks mode) (negMarks mode) k t S := by
  induction hl with
  | stop => exact .stop
  | unary ha fresh tail ih =>
    apply SignedRestricted.unary ha fresh _ _ (ih (bound_unary hb))
    · intro hm
      obtain ⟨i,rfl,_⟩ := pos_repr hm
      exact mark_unary i hb tail
    · intro hm
      obtain ⟨i,rfl,_⟩ := neg_repr hm
      exact mark_unary i hb tail
  | @binary k t U a b d ha hbb hab fresh tail ih =>
    have bRight : ProjectBound mode (k+1) (insert b (insert a U)) := by rwa [Finset.insert_comm]
    have tRight : Live k t (insert (bin d b a) U) := by rwa [bin_comm]
    apply SignedRestricted.binary ha hbb hab fresh _ _ _ _ (ih (bound_binary hb))
    · intro hm
      obtain ⟨i,rfl,hv⟩ := pos_repr hm
      simpa only [hv, Bool.not_false] using mark_binary i hb tail
    · intro hm
      obtain ⟨i,rfl,hv⟩ := pos_repr hm
      simpa only [hv, Bool.not_false] using mark_binary i bRight tRight
    · intro hm
      obtain ⟨i,rfl,hv⟩ := neg_repr hm
      simpa only [hv, Bool.not_true] using mark_binary i hb tail
    · intro hm
      obtain ⟨i,rfl,hv⟩ := neg_repr hm
      simpa only [hv, Bool.not_true] using mark_binary i bRight tRight

end Projection2153

namespace ThetaSym2153
open Search2153 Projection2153
def thetaFlat : List Sig := [(0xffffff4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b912517,0xfffff24386c0009da09c90e1b0002768270350420a044145c0d410828110517),
  (0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a,0xfffff0350420a044145c0d41082811051724386c0009da09c90e1b000276827),
  (0x911898c4c8749724462631321d25c911898c4c8749724462631321d25c,0x808390c5d024922020e4317409248808390c5d024922020e4317409248),
  (0xfffff6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3,0x4002ba9605a20001c441a981418000dbd45209a0000282330446c2e0),
  (0x850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238,0xdbd45209a0000282330446c2e0004002ba9605a20001c441a981418),
  (0x427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a6880,0x71106a60506001000aea58168800a08cc111b0b800036f514826800),
  (0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e88,0xa08cc111b0b800036f51482680000071106a60506001000aea581688)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma flat_eq : thetaRaw = thetaFlat := by decide +kernel

def key0_0 : Nat := 0x10000102059c12060a440704021e1e1e0f9c2229191e1f1d0682000522ca122f06154c1b0288411bbf10298244b7b901b71f2f191e2e77150a1f101d0d021e9c4c2e440a411902050505299c1f0f040522002e821d1e1f904c132e1512170288071785100f820a7d7f0d7d22130405067715442210224415052817040d011306151e1e1e0f2800292e1e1d1f040e22050056174104021b4c15142f4c4b10290e01434544431d412e1e1903020d1d101f0a151e281b19010d2f2e1505050529281d0f06050022190e1f1e1d1c1b07190217121514131211100f0e0d090b0a09000706050403020100
def key0_1 : Nat := 0x222222222222222222222222222222222222222210224415052817040d011306151e1e1e0f2800292e1e1d1f040e22050056174104021b4c15142f4c4b10290e01434544431d412e1e1903020d1d101f0a151e281b19010d2f2e1505050529281d0f06050022190e1f1e1d1c1b07190217121514131211100f0e0d090b0a0900070605040302010010000102059c12060a440704021e1e1e0f9c2229191e1f1d0682000522ca122f06154c1b0288411bbf10298244b7b901b71f2f191e2e77150a1f101d0d021e9c4c2e440a411902050505299c1f0f040522002e821d1e1f904c132e1512170288071785100f820a7d7f0d7d221304050677154422
def key0_2 : Nat := 0x1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d101d0d021e9c4c2e440a411902050505299c1f0f040522002e821d1e1f904c132e1512170288071785100f820a7d7f0d7d22130405067715442210000102059c12060a440704021e1e1e0f9c2229191e1f1d0682000522ca122f06154c1b0288411bbf10298244b7b901b71f2f191e2e77150a1f101f0a151e281b19010d2f2e1505050529281d0f06050022190e1f1e1d1c1b07190217121514131211100f0e0d090b0a0900070605040302010010224415052817040d011306151e1e1e0f2800292e1e1d1f040e22050056174104021b4c15142f4c4b10290e01434544431d412e1e1903020d1d
def key0_3 : Nat := 0x1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f101f0a151e281b19010d2f2e1505050529281d0f06050022190e1f1e1d1c1b07190217121514131211100f0e0d090b0a0900070605040302010010224415052817040d011306151e1e1e0f2800292e1e1d1f040e22050056174104021b4c15142f4c4b10290e01434544431d412e1e1903020d1d101d0d021e9c4c2e440a411902050505299c1f0f040522002e821d1e1f904c132e1512170288071785100f820a7d7f0d7d22130405067715442210000102059c12060a440704021e1e1e0f9c2229191e1f1d0682000522ca122f06154c1b0288411bbf10298244b7b901b71f2f191e2e77150a1f
def key0 : Fin 7 → Nat := ![key0_0,key0_1,key0_0,key0_0,key0_1,key0_2,key0_3]
def key1_0 : Nat := 0x183508353508151565051d000417401c0300041c0a0a05170903cccc051c0e031a181709080e871d0a00650a041a040e091507651d0b1a00000018350835350815152b0b04001d07060903001d090a0a0b071c0392920b090e031a18071c080e87040a002b0a1d1a1d0e1c15172b04051a000000183515353515080840040b00050765091a0005090e0e04071c1a585804090a1a0318071c150a130b0e00400e0503050a1c0817400b1d030000001835153535150808061d05000b172b1c1a000b1c0e0e1d17091a1e1e1d1c0a1a03181709150a13050e00060e0b030b0a09080706050403000000
def key1_1 : Nat := 0x183515353515080840040b00050765091a0005090e0e04071c1a585804090a1a0318071c150a130b0e00400e0503050a1c0817400b1d030000001835153535150808061d05000b172b1c1a000b1c0e0e1d17091a1e1e1d1c0a1a03181709150a13050e00060e0b030b0a09080706050403000000183508353508151565051d000417401c0300041c0a0a05170903cccc051c0e031a181709080e871d0a00650a041a040e091507651d0b1a00000018350835350815152b0b04001d07060903001d090a0a0b071c0392920b090e031a18071c080e87040a002b0a1d1a1d0e1c15172b04051a000000
def key1_2 : Nat := 0x18350835350815152b0b04001d07060903001d090a0a0b071c0392920b090e031a18071c080e87040a002b0a1d1a1d0e1c15172b04051a000000183508353508151565051d000417401c0300041c0a0a05170903cccc051c0e031a181709080e871d0a00650a041a040e091507651d0b1a0000001835153535150808061d05000b172b1c1a000b1c0e0e1d17091a1e1e1d1c0a1a03181709150a13050e00060e0b030b0a09080706050403000000183515353515080840040b00050765091a0005090e0e04071c1a585804090a1a0318071c150a130b0e00400e0503050a1c0817400b1d03000000
def key1_3 : Nat := 0x1835153535150808061d05000b172b1c1a000b1c0e0e1d17091a1e1e1d1c0a1a03181709150a13050e00060e0b030b0a09080706050403000000183515353515080840040b00050765091a0005090e0e04071c1a585804090a1a0318071c150a130b0e00400e0503050a1c0817400b1d0300000018350835350815152b0b04001d07060903001d090a0a0b071c0392920b090e031a18071c080e87040a002b0a1d1a1d0e1c15172b04051a000000183508353508151565051d000417401c0300041c0a0a05170903cccc051c0e031a181709080e871d0a00650a041a040e091507651d0b1a000000
def key1 : Fin 7 → Nat := ![key1_0,key1_1,key1_0,key1_0,key1_1,key1_2,key1_3]
def rep : Fin 7 → Fin 7 := ![0,0,2,3,3,3,3]
lemma rep_cases : ∀ j, rep j = 0 ∨ rep j = 2 ∨ rep j = 3 := by decide
def sym (j : Fin 7) (a : Sig) : Sig :=
  (reindex (index (key0 j)) a.1, reindex (index (key1 j)) a.2)
lemma sym_neg (j : Fin 7) (a : Sig) : sym j (neg a) = neg (sym j a) := by
  simp [sym,neg,reindex_not]
lemma sym_bin (j : Fin 7) (d : Bool) (a b : Sig) :
    sym j (bin d a b) = bin d (sym j a) (sym j b) := by
  cases d <;> simp [sym,bin,reindex_and,reindex_or]
lemma sym_target (j : Fin 7) : sym j target = target :=
  Prod.ext (reindex_top _) (reindex_zero _)
def thetaPerm : Fin 7 → Fin 7 → Fin 7 := ![![0,1,2,3,4,5,6], ![1,0,2,4,3,6,5], ![0,1,2,3,4,5,6], ![0,1,2,3,4,5,6], ![1,0,2,4,3,6,5], ![0,1,2,5,6,3,4], ![1,0,2,6,5,4,3]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
lemma flat_maps : ∀ (j v : Fin 7), sym j (thetaFlat.getD v.val zero) =
    thetaFlat.getD (thetaPerm j v).val zero := by decide +kernel
lemma perm_rep : ∀ j, thetaPerm j j = rep j := by decide
lemma input_maps (j v : Fin 7) : sym j (thetaRaw.getD v.val zero) =
    thetaRaw.getD (thetaPerm j v).val zero := by rw [flat_eq,flat_maps]

def CanTheta (i : Fin 7) (k : Nat) (S : Finset Sig) : Prop :=
  ∃ m ≤ k, ∃ t T, Live m t T ∧ T ⊆ S.image (sym i)

lemma pullTheta {i : Fin 7} {q : Nat} {S S' : Finset Sig} {g : Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image (sym i)).toList (sym i g) ∨
      witness (S.image (sym i)).toList (sym i g))
    (h : CanTheta i q S') : CanTheta i (q + 1) S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  have sub : ∀ a ∈ T, a ∈ (S.image (sym i)).toList ++ [sym i g] := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (ht ha)
    rcases Finset.mem_insert.mp (hs hb) with rfl | hb
    · simp
    · exact List.mem_append_left _ (Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hb))
  obtain ⟨m', t', T', hm', h', hT'⟩ := pull_gate hl hr sub
  exact ⟨m', by omega, t', T', h', fun a ha => Finset.mem_toList.mp (hT' _ ha)⟩

lemma pullNotTheta {i : Fin 7} {q : Nat} {a : Sig} {U : Finset Sig}
    (h : CanTheta i q (insert (neg a) U)) :
    CanTheta i (q+1) (insert a U) := by
  apply pullTheta (g := neg a) (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rw [sym_neg]
  exact neg_rep _ _ (by simp)

lemma pullBinTheta {i : Fin 7} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (h : CanTheta i q (insert (bin d a b) U)) :
    CanTheta i (q+1) (insert a (insert b U)) := by
  apply pullTheta (g := bin d a b) (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rw [sym_bin]
  exact bin_rep _ (Or.inl (by simp)) (Or.inl (by simp))

lemma liveTheta {k t : Nat} {S : Finset Sig} (h : Live k t S) (i : Fin 7) :
    CanTheta i k S := by
  induction h with
  | stop =>
    refine ⟨0, Nat.le_refl _, 0, {target}, Live.stop, ?_⟩
    simp [sym_target]
  | unary _ _ _ ih => exact pullNotTheta ih
  | binary _ _ _ _ _ ih => exact pullBinTheta ih


def ThreeNumeric : Prop :=
  ∀ (j : Fin 7), (j = 0 ∨ j = 2 ∨ j = 3) → ∀ (k t : Nat) (T : Finset Sig),
    k ≤ 10 → Live k t T → T ⊆ insert (neg (thetaRaw.getD j.val zero)) thetaRaw.toFinset → False

theorem three_suffice (num : ThreeNumeric) : ThetaNumeric := by
  intro j k t T hk hl sub
  obtain ⟨k',hk',t',T',hl',sub'⟩ := liveTheta hl j
  apply num (rep j) (rep_cases _) k' t' T' (hk'.trans hk) hl'
  intro a ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (sub' ha)
  rcases Finset.mem_insert.mp (sub hb) with rfl | hb
  · rw [sym_neg,input_maps,perm_rep]
    exact Finset.mem_insert_self _ _
  · obtain ⟨v,hv,he⟩ := List.getElem_of_mem (List.mem_toFinset.mp hb)
    have len : thetaRaw.length = 7 := rfl
    let i : Fin 7 := ⟨v,by omega⟩
    have e : thetaRaw.getD i.val zero = b := by rw [List.getD_eq_getElem _ _ hv,he]
    rw [← e,input_maps]
    apply Finset.mem_insert_of_mem
    apply List.mem_toFinset.mpr
    rw [List.getD_eq_getElem _ _ (by rw [len]; exact (thetaPerm j i).isLt)]
    exact List.getElem_mem _

end ThetaSym2153

namespace Orbit2153
open Search2153 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def mapWire {n : ℕ} (π : Fin n → Fin n) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩).val else w

def mapGate {n : ℕ} (π : Fin n → Fin n) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (mapWire π)⟩

def mapCircuit {n : ℕ} (π : Fin n → Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (mapGate π), mapWire π C.output⟩

theorem mapCircuit_size {n : ℕ} (π : Fin n → Fin n) (C : Circuit) :
    (mapCircuit π C).size = C.size := by
  simp [mapCircuit, Circuit.size]

theorem mapCircuit_fanin {n : ℕ} (π : Fin n → Fin n) (C : Circuit) (hc : FanInTwo C) :
    FanInTwo (mapCircuit π C) := by
  intro g hg
  change g ∈ C.gates.map (mapGate π) at hg
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
  simpa only [mapGate, List.length_map] using hc old hold

def runGates (gs : List Gate) (vals : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) vals

theorem read_compose {n : ℕ} (π : Fin n → Fin n) (x : Fin n → Bool)
    (tail : List Bool) (w : ℕ) :
    (List.ofFn (x ∘ π) ++ tail).getD w false =
      (List.ofFn x ++ tail).getD (mapWire π w) false := by
  by_cases hw : w < n
  · have hπ : (π ⟨w, hw⟩).val < n := (π ⟨w, hw⟩).isLt
    rw [mapWire, dif_pos hw]
    rw [List.getD_append _ _ _ _ (by simpa using hw),
      List.getD_append _ _ _ _ (by simpa using hπ)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, hπ, Function.comp_def]
  · rw [mapWire, dif_neg hw]
    rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hw),
      List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hw)]
    simp

theorem run_compose {n : ℕ} (π : Fin n → Fin n) (x : Fin n → Bool) (gs : List Gate) :
    ∀ (tail : List Bool) (w : ℕ),
      (runGates gs (List.ofFn (x ∘ π) ++ tail)).getD w false =
        (runGates (gs.map (mapGate π)) (List.ofFn x ++ tail)).getD (mapWire π w) false := by
  induction gs with
  | nil =>
    intro tail w
    exact read_compose π x tail w
  | cons g gs ih =>
    intro tail w
    let old := List.ofFn (x ∘ π) ++ tail
    let new := List.ofFn x ++ tail
    let b := g.op.eval (g.inputs.map fun i => old.getD i false)
    have he : (mapGate π g).op.eval ((mapGate π g).inputs.map fun i => new.getD i false) = b := by
      change g.op.eval ((g.inputs.map (mapWire π)).map fun i => new.getD i false) =
        g.op.eval (g.inputs.map fun i => old.getD i false)
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact (read_compose π x tail i).symm
    change (runGates gs (old ++ [b])).getD w false =
      (runGates (gs.map (mapGate π))
        (new ++ [(mapGate π g).op.eval ((mapGate π g).inputs.map fun i => new.getD i false)])).getD
        (mapWire π w) false
    rw [he]
    simpa only [old, new, List.append_assoc] using ih (tail ++ [b]) w

theorem mapCircuit_eval {n : ℕ} (π : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool)
    (tail : List Bool) :
    (mapCircuit π C).eval (List.ofFn x ++ tail) = C.eval (List.ofFn (x ∘ π) ++ tail) :=
  (run_compose π x C.gates tail C.output).symm

def perm (j : Fin 8) : Fin 8 → Fin 8 :=
  ![![0,1,2,3,4,5,6,7], ![0,1,2,3,4,5,6,7],
    ![3,2,1,0,7,6,5,4], ![3,2,1,0,7,6,5,4],
    ![0,4,7,3,1,6,5,2], ![5,1,2,6,7,0,3,4],
    ![5,7,4,6,1,3,0,2], ![3,7,4,0,2,5,6,1]] j

lemma rep01 : ∀ j, perm j j = 0 ∨ perm j j = 1 := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma edge_perm : ∀ j (x : Fin 8 → Bool), edgeF (x ∘ perm j) = edgeF x := by decide +kernel

theorem normalize_head {C : Circuit} {j : Fin 8} (h : FanInTwo C)
    (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = edgeF x)
    (hh : C.gates.head? = some ⟨.not,[j.val]⟩) :
    ∃ (D : Circuit) (p : Fin 8), (p = 0 ∨ p = 1) ∧ D.size = C.size ∧ FanInTwo D ∧
      (∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = edgeF x) ∧
      D.gates.head? = some ⟨.not, [p.val]⟩ := by
  let D := mapCircuit (perm j) C
  refine ⟨D,perm j j,rep01 _,mapCircuit_size _ _,mapCircuit_fanin _ _ h,?_,?_⟩
  · intro x
    have hmap := mapCircuit_eval (perm j) C x []
    simp only [List.append_nil] at hmap
    exact hmap.trans ((he (x ∘ perm j)).trans (edge_perm j x))
  · change (C.gates.map _).head? = _
    rw [List.head?_map,hh]
    simp [mapGate,mapWire,j.isLt]

def rawAt (p : Fin 8) := raw.getD p.val zero

theorem extract_tail {C : Circuit} {p : Fin 8} (h : FanInTwo C)
    (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = edgeF x)
    (hh : C.gates.head? = some ⟨.not,[p.val]⟩) (hs : C.size ≤ 13) :
    ∃ k t S, k ≤ 12 ∧ Live k t S ∧ S ⊆ insert (neg (rawAt p)) raw.toFinset := by
  obtain ⟨gs,head⟩ := List.head?_eq_some_iff.mp hh
  have mem := circuit_target C h he
  rw [head] at mem
  change target ∈ execute gs (raw ++ [neg (rawAt p)]) at mem
  obtain ⟨k,t,S,hk,hl,sub⟩ := extract gs _ (fun g hg => h g (head ▸ List.mem_cons_of_mem _ hg)) mem
  have len : gs.length + 1 ≤ 13 := by simpa [Circuit.size,head] using hs
  exact ⟨k,t,S,by omega,hl,fun a ha => by simpa [or_comm] using sub a ha⟩

theorem extract_ordinary {C : Circuit} (h : FanInTwo C)
    (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = edgeF x) (hs : C.size ≤ 12) :
    ∃ k t S, k ≤ 12 ∧ Live k t S ∧ S ⊆ raw.toFinset := by
  obtain ⟨k,t,S,hk,hl,sub⟩ := extract C.gates raw h (circuit_target C h he)
  exact ⟨k,t,S,hk.trans hs,hl,fun a ha => List.mem_toFinset.mpr (sub a ha)⟩

lemma sep_neg_xor (a : Sig) : sep true (neg a) = sep true a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [sep,neg,ite_true,BitVec.getLsbD_xor,BitVec.getLsbD_not,hi,decide_true,
    Bool.true_and]
  cases a.1.getLsbD i <;> cases a.2.getLsbD i <;> rfl

lemma needs_raw_or_sign {p : Sig} (hp : p ∈ raw) {k t S} (hl : Live k t S)
    (sub : S ⊆ insert (neg p) raw.toFinset) {a : Sig} (ha : a ∈ raw) :
    a ∈ S ∨ (a = p ∧ neg p ∈ S) := by
  by_contra ht
  have noA : a ∉ S := fun h => ht (Or.inl h)
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,hsep⟩ := live_sep hl i hi
    have hsep' := sep_weaken _ _ _ hi hsep
    have hbit : (unionSep true (raw.erase a)).getLsbD i = true := by
      apply (mem_unionSep _ _ _).mpr
      rcases Finset.mem_insert.mp (sub hb) with hb' | hb'
      · subst b
        have hne : p ≠ a := fun e => ht (Or.inr ⟨e.symm,hb⟩)
        exact ⟨p,(List.mem_erase_of_ne hne).mpr hp,by simpa only [sep_neg_xor] using hsep'⟩
      · have hne : b ≠ a := fun e => noA (e ▸ hb)
        exact ⟨b,(List.mem_erase_of_ne hne).mpr (List.mem_toFinset.mp hb'),hsep'⟩
    simpa only [top, BitVec.getLsbD_allOnes, hi, decide_true] using hbit
  have fail := List.all_eq_true.mp every_input a ha
  simp [cov] at fail

end Orbit2153

namespace Root2153
open Search2153 Projection2153 Orbit2153
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def roots (mode : Bool) : List (Finset Sig) :=
  if mode then [insert (neg raw0) (raw.toFinset.erase raw0)]
  else [raw.toFinset,insert (neg raw1) (raw.toFinset.erase raw1),
    insert (neg raw1) raw.toFinset]

def EightNumeric : Prop :=
  ∀ (mode : Bool) (k t : Nat) (S : Finset Sig), S ∈ roots mode → k ≤ 12 →
    SignedRestricted (posMarks mode) (negMarks mode) k t S → False

lemma all_marks {mode : Bool} {S : Finset Sig} (hs : S ∈ roots mode) :
    ∀ i, mark mode i ∈ S := by
  cases mode
  · simp only [roots,Bool.false_eq_true,if_false,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl <;> decide +kernel
  · simp only [roots,if_true,List.mem_singleton] at hs
    subst S
    decide +kernel

lemma feasible_sub {S U : Finset Sig} {i : Fin 4} {q : Nat}
    (sub : S ⊆ U) (hf : Feasible i q S) : Feasible i q U := by
  obtain ⟨k,hk,t,T,hl,hs⟩ := hf
  exact ⟨k,hk,t,T,hl,hs.trans (Finset.image_mono _ sub)⟩

lemma exclude_root (num7 : ThetaNumeric) (num8 : EightNumeric)
    {mode : Bool} {k t S} {p : Sig} (hp : p ∈ raw) (sr : S ∈ roots mode)
    (hk : k ≤ 12) (hl : Live k t S) (sub : S ⊆ insert (neg p) raw.toFinset) : False := by
  have no10 i : ¬Feasible i 10 S := fun hf =>
    signed_project_impossible num7 i p (List.mem_toFinset.mpr hp) (feasible_sub sub hf)
  exact num8 mode k t S sr hk (restrict_signed hl (project_bound_root hk (all_marks sr) no10))

lemma initial_cases {k t S} {p : Sig} (hp : p ∈ raw)
    (hl : Live k t S) (sub : S ⊆ insert (neg p) raw.toFinset) :
    S = raw.toFinset ∨ S = insert (neg p) (raw.toFinset.erase p) ∨
      S = insert (neg p) raw.toFinset := by
  have others : raw.toFinset.erase p ⊆ S := by
    intro a ha
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp ha
    exact (needs_raw_or_sign hp hl sub (List.mem_toFinset.mp mem)).resolve_right
      (fun he => ne he.1)
  by_cases hn : neg p ∈ S
  · by_cases hpos : p ∈ S
    · right; right
      exact Finset.Subset.antisymm sub (by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hn
        · by_cases same : a = p
          · exact same ▸ hpos
          · exact others (Finset.mem_erase.mpr ⟨same,ha⟩))
    · right; left
      ext a
      constructor
      · intro ha
        rcases Finset.mem_insert.mp (sub ha) with h | h
        · exact Finset.mem_insert.mpr (Or.inl h)
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hpos (e ▸ ha),h⟩)
      · intro ha
        rcases Finset.mem_insert.mp ha with rfl | hm
        · exact hn
        · exact others hm
  · left
    ext a
    constructor
    · intro ha
      exact (Finset.mem_insert.mp (sub ha)).resolve_left (fun e => hn (e ▸ ha))
    · intro ha
      exact (needs_raw_or_sign hp hl sub (List.mem_toFinset.mp ha)).resolve_right
        (fun h => hn h.2)

lemma both_zero_impossible (num : ThetaNumeric) {k t : Nat} (hk : k ≤ 12)
    (hl : Live k t (insert (neg raw0) raw.toFinset)) : False := by
  have hr : raw0 ∈ insert (neg raw0) raw.toFinset := by decide +kernel
  have hn : neg raw0 ∈ insert (neg raw0) raw.toFinset := Finset.mem_insert_self _ _
  have hz : project 0 raw0 = zero := project_marker 0
  have hp : ¬proper (project 0 raw0) := fun h => h.1 hz
  have hnp : ¬proper (project 0 (neg raw0)) := fun h => h.2 (by rw [project_neg,hz,neg_laws.1])
  obtain ⟨q,hq,hf⟩ := feasible_two_consts hl 0 raw0 (neg raw0) hr hn
    (by decide +kernel) hp hnp
  exact signed_project_impossible num 0 raw0 (by decide +kernel) (feasible_mono hf (by omega))

theorem ordinary_lower (num7 : ThetaNumeric) (num8 : EightNumeric)
    (C : Circuit) (hc : FanInTwo C) (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = edgeF x) :
    13 ≤ C.size := by
  by_contra! hsz
  obtain ⟨k,t,S,hk,hl,hs⟩ := extract_ordinary hc he (by omega)
  have eq : S = raw.toFinset := by
    apply Finset.Subset.antisymm hs
    intro a ha
    have hn : neg raw1 ∉ S := fun hh => (by decide +kernel : neg raw1 ∉ raw.toFinset) (hs hh)
    exact (needs_raw_or_sign (by decide +kernel : raw1 ∈ raw) hl
      (hs.trans (Finset.subset_insert _ _)) (List.mem_toFinset.mp ha)).resolve_right (fun h => hn h.2)
  subst S
  exact exclude_root num7 num8 (p := raw1) (mode := false) (by decide +kernel)
    (by simp [roots]) hk hl (Finset.subset_insert _ _)

theorem not_first_lower (num7 : ThetaNumeric) (num8 : EightNumeric)
    (C : Circuit) (hc : FanInTwo C) (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = edgeF x)
    (j : Fin 8) (head : C.gates.head? = some ⟨.not,[j.val]⟩) : 14 ≤ C.size := by
  by_contra! hsz
  obtain ⟨D,p,por,sz,ok,ev,head'⟩ := normalize_head hc he head
  obtain ⟨k,t,S,hk,hl,hs⟩ := extract_tail ok ev head' (by omega)
  have hp : rawAt p ∈ raw := by
    rcases por with rfl | rfl <;> decide +kernel
  rcases initial_cases hp hl hs with h | h | h
  · subst S
    exact exclude_root num7 num8 (mode := false) hp (by simp [roots]) hk hl hs
  · subst S
    rcases por with rfl | rfl
    · exact exclude_root num7 num8 (mode := true) hp (by decide +kernel) hk hl hs
    · exact exclude_root num7 num8 (mode := false) hp (by decide +kernel) hk hl hs
  · subst S
    rcases por with rfl | rfl
    · exact both_zero_impossible num7 hk hl
    · exact exclude_root num7 num8 (mode := false) hp (by decide +kernel) hk hl hs

end Root2153

namespace FinalBridge2153
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Cof2153 Search2153

theorem combined (seven : ThetaSym2153.ThreeNumeric) (eight : Root2153.EightNumeric) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → (16 : ℕ) ≤ x1.size := by
  intro C hf hfirst hc hsecond
  have num7 := ThetaSym2153.three_suffice seven
  obtain ⟨tail,shape⟩ := firstGateShape C hf hfirst
  obtain ⟨a,hs,ha⟩ : ∃ a, C.gates = a :: tail ∧ firstOK a := by
    rcases shape with h | h
    · exact ⟨firstL,h,Or.inl rfl⟩
    · exact ⟨firstR,h,Or.inr rfl⟩
  cases tail with
  | nil => simp [hs] at hsecond
  | cons q post =>
    have hq : q.op = .not := by simpa [hs] using hsecond
    have eqC : (⟨a :: q :: post,C.output⟩ : Circuit) = C := by cases C; simp only [← hs]
    obtain ⟨E,hE,he,hb⟩ := compressed a q post C.output ha hq (eqC.symm ▸ hf)
      (by intro x; rw [eqC]; exact congrFun hc x)
    have hev : ∀ x : Fin 8 → Bool, E.eval (List.ofFn x) = edgeF x := by
      intro x
      exact congrFun he x
    rw [eqC] at hb
    rcases hb with ord | ⟨sz,j,hn⟩
    · have lo := Root2153.ordinary_lower num7 eight E hE hev
      omega
    · have lo := Root2153.not_first_lower num7 eight E hE hev j hn
      omega

end FinalBridge2153

open Search2153
namespace Marked2153
inductive Restricted (p : List Sig) : Nat → Nat → Finset Sig → Prop
  | stop : Restricted p 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hf : neg a ∉ insert a U) (hr : a ∉ p)
      (tail : Restricted p k t (insert (neg a) U)) :
      Restricted p (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hf : bin d a b ∉ insert a (insert b U))
      (hra : a ∈ p → d = true ∧ a ∉ U)
      (hrb : b ∈ p → d = true ∧ b ∉ U)
      (tail : Restricted p k t (insert (bin d a b) U)) :
      Restricted p (k+1) t (insert a (insert b U))


theorem Restricted.live {p : List Sig} {k t S} (h : Restricted p k t S) : Live k t S := by
  induction h with
  | stop => exact Live.stop
  | unary a f _ _ ih => exact Live.unary a f ih
  | binary a b n f _ _ _ ih => exact Live.binary a b n f ih

theorem ignoreNegative {p m : List Sig} {k t S}
    (h : SignedRestricted p m k t S) : Restricted p k t S := by
  induction h with
  | stop => exact Restricted.stop
  | unary a f tag _ _ ih => exact Restricted.unary a f tag ih
  | binary a b neq f tag1 tag2 _ _ _ ih => exact Restricted.binary a b neq f tag1 tag2 ih

variable {p : List Sig}
def unaryAt (p : List Sig) (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a : Sig) : Bool :=
  !(p.contains a) &&
    tryGate k t r v (dropped [a] v) (v.length-1) (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]

def unaryMoves (p : List Sig) (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let c := coverage (decide (0<t)) v
  v.any (unaryAt p k t r v c)

def allowedKeeps (p : List Sig) (a b : Sig) : List (List Sig) :=
  [[],[a],[b],[a,b]].filter (fun w => w.all fun x => !(p.contains x))

def fastBinary (p : List Sig) (r : List Sig → Bool) (v : List Sig) (a b : Sig) (ua ub : B) : Bool :=
  let rest := dropped [a,b] v
  let use := fun (g : Sig) => gateAvailable v g && r (g::rest)
  ((ua &&& ~~~b.1) == 0 && (ub &&& ~~~a.1) == 0 &&
    !(p.contains a) && !(p.contains b) && use (bin false a b)) ||
    ((ua &&& b.2) == 0 && (ub &&& a.2) == 0 && use (bin true a b))

def slowBinary (p : List Sig) (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  let rest := dropped [a,b] v
  let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
  ((!(p.contains a) && !(p.contains b)) &&
    tryGate k t r v rest (v.length-2) mask (bin false a b) [[],[a],[b],[a,b]]) ||
    tryGate k t r v rest (v.length-2) mask (bin true a b) (allowedKeeps p a b)

def binaryMoves (p : List Sig) (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let d := decide (0<t)
  let c := coverage d v
  if t == 0 && v.length == k+2 then
    let acts := v.map (fun a => (a, c.2.1 &&& sep false a))
    scanPairs (fun a b => fastBinary p r v a.1 b.1 a.2 b.2) acts
  else scanPairs (slowBinary p k t r v c) v

def stepTest (p : List Sig) (k t : Nat) (v : List Sig) (u b : List Sig → Bool) : Bool :=
  if t>k+1 ∨ v.length>k+1-t+1 then false else
    v == [target] || (decide (0<t) && unaryMoves p k (t-1) u v) || binaryMoves p k t b v

def search (p : List Sig) : Nat → Nat → List Sig → Bool
  | 0, _, v => v == [target]
  | k+1,t,v => stepTest p k t v (search p k (t-1)) (search p k t)

private lemma gate_found {k t m : Nat} {v rest h : List Sig} {g : Sig} {opts : List (List Sig)}
    {S : Finset Sig} {r : List Sig → Bool} (l : Live m t S)
    (hle : m ≤ k) (hp : proper g) (ha : g ∉ v) (hh : h ∈ opts)
    (hn : (g::(h++rest)).Nodup) (he : (g::(h++rest)).toFinset=S)
    (hr : r (g::(h++rest)) = true) : tryGate k t r v rest rest.length (unionSep (decide (0<t)) rest) g opts = true := by
  obtain ⟨ht,hc⟩ := live_size l
  rw [←he,List.toFinset_card_of_nodup hn] at hc
  simp only [List.length_cons,List.length_append] at hc
  have hl : rest.length+h.length+1 ≤ k-t+1 := by omega
  have cv := live_cover l he
  rw [unionSep,union_append] at cv
  have cov : (sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest) ||| unionSep (decide (0<t)) h = top := by
    rw [← cv]; ac_rfl
  by_cases tight : rest.length=k-t
  · have hz : h.length=0 := by omega
    have hem : h=[] := List.length_eq_zero_iff.mp hz
    subst h
    have ok : sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest = top := by
      simpa [unionSep] using cov
    simp [tryGate,tight,ok,gateAvailable,ha,hp.1,hp.2,hr] at *
  · have hav : gateAvailable v g = true := by simp [gateAvailable, ha, hp.1, hp.2]
    simp only [tryGate, ite_eq_right tight, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq, hav, and_true]
    exact ⟨h,hh,⟨hl,cov⟩,hr⟩

private lemma unique_needed (c : Cov) (a b : Sig) (op : Bool)
    (h : sep false (bin op a b) ||| takeTwo c (sep false a) (sep false b)=top) :
    ((c.2.1 &&& sep false a) &&& (if op then b.2 else ~~~b.1)) |||
    ((c.2.1 &&& sep false b) &&& (if op then a.2 else ~~~a.1))=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun z : B => z.getLsbD i) h
  clear h
  cases op <;> simp only [sep,bin,ite_false,ite_true,takeTwo,top,BitVec.getLsbD_allOnes,
    BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,BitVec.getLsbD_zero,
    reduceCtorEq,hi,decide_true,Bool.true_and] at hh ⊢ <;>
    cases ax : a.1.getLsbD i <;> cases ay : a.2.getLsbD i <;>
    cases bx : b.1.getLsbD i <;> cases byy : b.2.getLsbD i <;>
    cases um : c.2.1.getLsbD i <;> simp [ax,ay,bx,byy,um] at hh ⊢

private lemma fast_ok {k r v c a b}
    (hlen : v.length-2=k) (h : slowBinary p k 0 r v c a b = true) :
    fastBinary p r v a b (c.2.1 &&& sep false a) (c.2.1 &&& sep false b) = true := by
  simp only [slowBinary,tryGate,Nat.sub_zero,hlen,ite_true,decide_false,Bool.or_eq_true,
    Bool.and_eq_true,beq_iff_eq] at h
  simp only [fastBinary, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rcases h with ⟨⟨ha,hb⟩,⟨hc,hav⟩,hr⟩ | ⟨⟨hc,hav⟩,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b false hc)
    exact Or.inl ⟨⟨⟨⟨h1,h2⟩,ha⟩,hb⟩,hav,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b true hc)
    exact Or.inr ⟨⟨h1,h2⟩,hav,hr⟩

private lemma unary_found {m t k : Nat} {U : Finset Sig} {a : Sig} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a U) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U) (ha : a ∉ p) (l : Restricted p m t (insert (neg a) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (neg a) U → r v = true) :
    unaryMoves p k t r v = true := by
  let h := keepOf U [a]
  let rest := dropped [a] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩ := edit_list (del := [a]) (U := U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : neg a ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : neg a ∉ U := fun hm => fresh (Finset.mem_insert_of_mem hm)
  have hnd : (neg a::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (neg a::(h++rest)).toFinset=insert (neg a) U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]] := by by_cases hm : a ∈ U <;> simp [h,keepOf,hm]
  apply List.any_eq_true.mpr
  refine ⟨a,ah,?_⟩
  unfold unaryAt
  obtain ⟨hlen,hmask⟩ := one_rest (decide (0<t)) hv ah
  rw [hlen,hmask]
  apply Bool.and_eq_true_iff.mpr
  exact ⟨by simp [ha], gate_found l.live hle (live_proper l.live _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩

private lemma slow_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ p → d = true ∧ a ∉ U)
    (hrb : b ∈ p → d = true ∧ b ∉ U)
    (l : Restricted p m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    slowBinary p k t r v (coverage (decide (0<t)) v) a b = true := by
  let g := bin d a b
  let h := keepOf U [a,b]
  let rest := dropped [a,b] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩ := edit_list (del := [a,b]) (U := U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : g ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : g ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (g::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (g::(h++rest)).toFinset=insert g U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a],[b],[a,b]] := by
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [h,keepOf,ha,hb]
  have allow : h ∈ allowedKeeps p a b := by
    apply List.mem_filter.mpr
    refine ⟨opts,List.all_eq_true.mpr (fun x hx => ?_)⟩
    have hm : x ∈ U := (List.mem_filter.mp hx).2 |> of_decide_eq_true
    rcases List.mem_cons.mp (List.mem_filter.mp hx).1 with rfl | hx
    · simpa using fun ha : x ∈ p => (hra ha).2 hm
    · obtain rfl := List.mem_singleton.mp hx
      simpa using fun hb : x ∈ p => (hrb hb).2 hm
  obtain ⟨hlen,hmask⟩ := two_rest (decide (0<t)) hv ah bh hab
  unfold slowBinary
  dsimp only
  rw [hlen,hmask]
  cases d with
  | false =>
    have na : a ∉ p := fun ha => Bool.false_ne_true (hra ha).1
    have nb : b ∉ p := fun hb => Bool.false_ne_true (hrb hb).1
    apply Bool.or_eq_true_iff.mpr
    left
    exact Bool.and_eq_true_iff.mpr ⟨by simp [na,nb],
      gate_found l.live hle (live_proper l.live _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
  | true =>
    apply Bool.or_eq_true_iff.mpr
    right
    exact gate_found l.live hle (live_proper l.live _ (Finset.mem_insert_self _ _)) nn allow hnd e (ih _ hnd e)

private lemma binary_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ p → d = true ∧ a ∉ U)
    (hrb : b ∈ p → d = true ∧ b ∉ U)
    (l : Restricted p m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    binaryMoves p k t r v = true := by
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h1 := slow_found hv he hle hab fresh hra hrb l ih
  have e' : v.toFinset = insert b (insert a U) := by rwa [Finset.insert_comm b a]
  have hf : bin d b a ∉ insert b (insert a U) := by rwa [bin_comm d b a, Finset.insert_comm b a]
  have ht : Restricted p m t (insert (bin d b a) U) := by rwa [bin_comm d b a]
  have h2 := slow_found hv e' hle hab.symm hf hrb hra ht (by simpa only [bin_comm d b a] using ih)
  unfold binaryMoves
  split
  · rename_i cut
    simp only [Bool.and_eq_true, beq_iff_eq] at cut
    obtain ⟨rfl,hvlen⟩ := cut
    have hlen : v.length - 2 = k := by omega
    let f := fun x => (x, (coverage false v).2.1 &&& sep false x)
    have na : f a ∈ v.map f := List.mem_map_of_mem ah
    have nb : f b ∈ v.map f := List.mem_map_of_mem bh
    exact scanPairs_complete _ na nb (fun e => hab (congrArg Prod.fst e))
      (fast_ok hlen h1) (fast_ok hlen h2)
  · exact scanPairs_complete _ ah bh hab h1 h2

lemma reduced_step {m t S : Nat} {s : Finset Sig} {v : List Sig} {u b : List Sig → Bool}
    (h : Restricted p m t s) (hb : m ≤ S+1) (hv : v.Nodup) (he : v.toFinset = s)
    (hu : ∀ w, w.Nodup → ∀ l ≤ S, Restricted p l (t-1) w.toFinset → u w = true)
    (hb' : ∀ w, w.Nodup → ∀ l ≤ S, Restricted p l t w.toFinset → b w = true) :
    stepTest p S t v u b = true := by
  have size := live_size h.live
  rw [← he, List.toFinset_card_of_nodup hv] at size
  rw [stepTest, if_neg (by omega)]
  cases h with
  | stop =>
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [he])
    have eq := List.perm_singleton.mp p
    simp [eq]
  | @unary m t U a ha hf hr tail =>
    apply Bool.or_eq_true_iff.mpr
    left
    apply Bool.or_eq_true_iff.mpr
    right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp, unary_found hv he (by omega) hf hr tail ?_⟩
    intro w hn hs
    exact hu w hn m (by omega) (hs.symm ▸ tail)
  | @binary m t U a b d ha hc hab hf hra hrb tail =>
    apply Bool.or_eq_true_iff.mpr
    right
    apply binary_found hv he (by omega) hab hf hra hrb tail
    intro w hn hs
    exact hb' w hn m (by omega) (hs.symm ▸ tail)

lemma search_complete {m t : Nat} {S : Finset Sig} (h : Restricted p m t S) (k : Nat) (hk : m ≤ k)
    (v : List Sig) (hv : v.Nodup) (hs : v.toFinset = S) : search p k t v = true := by
  induction k generalizing m t S v with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    cases h
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [hs])
    simp [search, List.perm_singleton.mp p]
  | succ k ih =>
    rw [search]
    apply reduced_step h hk hv hs <;>
      exact fun w hn l hl hh => ih hh hl w hn rfl

def Impossible (p : List Sig) (k t : Nat) (v : List Sig) : Prop :=
  ∀ m ≤ k, ¬ Restricted p m t v.toFinset

lemma exclude_search {k t : Nat} {v : List Sig} (hv : v.Nodup) (hc : search p k t v = false) :
    Impossible p k t v := by
  intro m hm h
  exact Bool.false_ne_true (hc.symm.trans (search_complete h k hm v hv rfl))

lemma exclude_step {k t : Nat} {v : List Sig} {u b : List Sig → Bool} (hv : v.Nodup)
    (hu : ∀ w, u w = false → Impossible p k (t-1) w)
    (hb : ∀ w, b w = false → Impossible p k t w)
    (hc : stepTest p k t v u b = false) : Impossible p (k+1) t v := by
  intro m hm h
  have hu' : ∀ w, w.Nodup → ∀ j ≤ k, Restricted p j (t-1) w.toFinset → u w = true := by
    intro w _ j hj r
    cases e : u w
    · exact (hu _ e j hj r).elim
    · rfl
  have hb' : ∀ w, w.Nodup → ∀ j ≤ k, Restricted p j t w.toFinset → b w = true := by
    intro w _ j hj r
    cases e : b w
    · exact (hb _ e j hj r).elim
    · rfl
  exact Bool.false_ne_true (hc.symm.trans (reduced_step h hm hv rfl hu' hb'))



end Marked2153

open Search2153

namespace Cache2153

def mix (s : Sig) : Nat :=
  let a := s.1.toNat % 4294967291
  let b := s.2.toNat % 4294967279
  let x := a + 37*b
  (x*x + 97*a + 1789*b) % 4294967291

def stateHash (t : Nat) (v : List Sig) : Nat :=
  v.foldl (fun h a => h + mix a) (3571*t)

def replayStep (v : List Sig) (action : Nat) : List Sig :=
  let slot := action >>> 3
  if action < 440 then
    let i := (0xaaaaaaaaaa999999999888888887777777666666555554444333221 >>> (slot*4)) &&& 15
    let j := (0x9876543210876543210765432106543210543210432103210210100 >>> (slot*4)) &&& 15
    let a := v.getD i zero
    let b := v.getD j zero
    let keep := (if action.testBit 0 then [a] else []) ++ (if action.testBit 1 then [b] else [])
    bin (action.testBit 2) a b :: (keep ++ (v.eraseIdx i).eraseIdx j)
  else
    let a := v.getD ((action-440) >>> 1) zero
    neg a :: ((if action.testBit 0 then [a] else []) ++ v.eraseIdx ((action-440) >>> 1))

def replay (basis : Nat → List Sig) : Nat → Nat → List Sig
  | 0,c => basis c
  | d+1,c => replayStep (replay basis d (c >>> 9)) (c &&& 511)

def base (raw : List Sig) (code : Nat) : List Sig :=
  let j := code/3
  let form := code % 3
  let a := raw.getD j zero
  (if form = 0 then raw.erase a else raw) ++ (if form = 1 then [] else [neg a])

def field (block : Nat → Nat) (width idx : Nat) : Nat :=
  ((block (idx >>> 6)) >>> (width*(idx &&& 63))) &&& (2^width-1)

def hit (n buckets : Nat) (offset : Nat → Nat) (record : Nat → Nat)
    (basis : Nat → List Sig) (depth t : Nat) (v : List Sig) : Bool :=
  let h := stateHash t v
  let b := h % buckets
  let a := offset b
  let z := offset (b+1)
  (List.range (z-a)).any fun j =>
    let i := a+j
    let c := record i
    decide (i < n) && (c &&& 7 == t) && ((c >>> 3) &&& 15 == (h / buckets) &&& 15) &&
      (replay basis depth (c >>> 7)).isPerm v

theorem hitSound {n buckets : Nat} {offset record : Nat → Nat} {basis : Nat → List Sig}
    {depth k t : Nat} {p v : List Sig}
    (all : ∀ i < n, Marked2153.Impossible p k (record i &&& 7) (replay basis depth (record i >>> 7)))
    (found : hit n buckets offset record basis depth t v = true) : Marked2153.Impossible p k t v := by
  unfold hit at found
  obtain ⟨j,_,hj⟩ := List.any_eq_true.mp found
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,List.isPerm_iff] at hj
  obtain ⟨⟨⟨hi,ht⟩,_⟩,hp⟩ := hj
  have hh := all _ hi
  rw [ht] at hh
  intro m hm hr
  apply hh m hm
  exact (List.toFinset_eq_of_perm _ _ hp).symm ▸ hr

def jump (p : List Sig) (bottom : Nat) (stop : Nat → List Sig → Bool) : Nat → Nat → List Sig → Bool
  | 0,t,v => stop t v
  | n+1,t,v => Marked2153.stepTest p (bottom+n) t v
        (jump p bottom stop n (t-1)) (jump p bottom stop n t)

theorem jumpSound {p : List Sig} {bottom : Nat} {stop : Nat → List Sig → Bool}
    (baseSound : ∀ t w, w.Nodup → stop t w = false → Marked2153.Impossible p bottom t w) :
    ∀ n t v, v.Nodup → jump p bottom stop n t v = false → Marked2153.Impossible p (bottom+n) t v := by
  intro n
  induction n with
  | zero => exact baseSound
  | succ n ih =>
    intro t v hv hj m hm hr
    apply Bool.false_ne_true
    have hu : ∀ w, w.Nodup → ∀ l ≤ bottom+n, Marked2153.Restricted p l (t-1) w.toFinset →
        jump p bottom stop n (t-1) w = true := by
      intro w hw l hl live
      cases h : jump p bottom stop n (t-1) w with
      | false => exact (ih _ _ hw h l hl live).elim
      | true => rfl
    have hb : ∀ w, w.Nodup → ∀ l ≤ bottom+n, Marked2153.Restricted p l t w.toFinset →
        jump p bottom stop n t w = true := by
      intro w hw l hl live
      cases h : jump p bottom stop n t w with
      | false => exact (ih _ _ hw h l hl live).elim
      | true => rfl
    exact hj.symm.trans (Marked2153.reduced_step hr (by omega) hv rfl hu hb)

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0,_ => true
  | n+1,start => f start && span f n (start+1)

theorem spanAt {f : Nat → Bool} {n start i : Nat} (h : span f n start = true)
    (lo : start ≤ i) (hi : i < start+n) : f i = true := by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp h
    by_cases eq : i = start
    · exact eq ▸ head
    · exact ih tail (by omega) (by omega)

theorem spanJoin (f : Nat → Bool) (x base y : Nat) (a : span f x base = true)
    (b : span f y (base+x) = true) : span f (x+y) base = true := by
  induction x generalizing base with
  | zero => simpa using b
  | succ x ih =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp a
    rw [Nat.succ_add]
    apply Bool.and_eq_true_iff.mpr
    exact ⟨ha,ih (base+1) hb (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using b)⟩

end Cache2153

namespace RootGlue2153
open Search2153 Projection2153 Orbit2153 Root2153 ThetaSym2153
open Cache2153 (base)

def AtBase (pos : List Sig) (n : Nat) (v : List Sig) : Prop :=
  ∀ t, t ≤ n+1-v.length → unionSep (decide (0<t)) v = top → Marked2153.Impossible pos n t v

lemma atBase_exclude {pos : List Sig} {n k t : Nat} {S : Finset Sig} {v : List Sig}
    (checked : AtBase pos n v) (nd : v.Nodup) (eq : v.toFinset = S)
    (hk : k ≤ n) (hl : Marked2153.Restricted pos k t S) : False := by
  have sz := live_size hl.live
  rw [← eq, List.toFinset_card_of_nodup nd] at sz
  have cover := live_cover hl.live eq
  exact checked t (by omega) cover k hk (by simpa only [eq] using hl)

lemma needs_basis {basis : List Sig} (holes : basis.all (fun a => unionSep true (basis.erase a) != top) = true) {p : Sig} (hp : p ∈ basis) {k t S} (hl : Live k t S)
    (sub : S ⊆ insert (neg p) basis.toFinset) {a : Sig} (ha : a ∈ basis) :
    a ∈ S ∨ (a = p ∧ neg p ∈ S) := by
  by_contra ht
  have noA : a ∉ S := fun h => ht (Or.inl h)
  have cov : unionSep true (basis.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,hsep⟩ := live_sep hl i hi
    have hsep' := sep_weaken _ _ _ hi hsep
    have hbit : (unionSep true (basis.erase a)).getLsbD i = true := by
      apply (mem_unionSep _ _ _).mpr
      rcases Finset.mem_insert.mp (sub hb) with hb' | hb'
      · subst b
        have hne : p ≠ a := fun e => ht (Or.inr ⟨e.symm,hb⟩)
        exact ⟨p,(List.mem_erase_of_ne hne).mpr hp,by simpa only [sep_neg_xor] using hsep'⟩
      · have hne : b ≠ a := fun e => noA (e ▸ hb)
        exact ⟨b,(List.mem_erase_of_ne hne).mpr (List.mem_toFinset.mp hb'),hsep'⟩
    simpa only [top, BitVec.getLsbD_allOnes, hi, decide_true] using hbit
  have fail := List.all_eq_true.mp holes a ha
  simp [cov] at fail

lemma initial_of_basis {basis : List Sig} (holes : basis.all (fun a => unionSep true (basis.erase a) != top) = true) {k t S} {p : Sig} (hp : p ∈ basis)
    (hl : Live k t S) (sub : S ⊆ insert (neg p) basis.toFinset) :
    S = basis.toFinset ∨ S = insert (neg p) (basis.toFinset.erase p) ∨
      S = insert (neg p) basis.toFinset := by
  have others : basis.toFinset.erase p ⊆ S := by
    intro a ha
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp ha
    exact (needs_basis holes hp hl sub (List.mem_toFinset.mp mem)).resolve_right
      (fun he => ne he.1)
  by_cases hn : neg p ∈ S
  · by_cases hpos : p ∈ S
    · right; right
      exact Finset.Subset.antisymm sub (by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hn
        · by_cases same : a = p
          · exact same ▸ hpos
          · exact others (Finset.mem_erase.mpr ⟨same,ha⟩))
    · right; left
      ext a
      constructor
      · intro ha
        rcases Finset.mem_insert.mp (sub ha) with h | h
        · exact Finset.mem_insert.mpr (Or.inl h)
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hpos (e ▸ ha),h⟩)
      · intro ha
        rcases Finset.mem_insert.mp ha with rfl | hm
        · exact hn
        · exact others hm
  · left
    ext a
    constructor
    · intro ha
      exact (Finset.mem_insert.mp (sub ha)).resolve_left (fun e => hn (e ▸ ha))
    · intro ha
      exact (needs_basis holes hp hl sub (List.mem_toFinset.mp ha)).resolve_right
        (fun h => hn h.2)


set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
lemma theta_holes : thetaRaw.all (fun a => unionSep true (thetaRaw.erase a) != top) = true := by
  rw [flat_eq]
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
lemma theta_forms : ∀ j : Fin 7,
    let b := thetaRaw.getD j.val zero
    let v := 3*j.val
    b ∈ thetaRaw ∧
      ((base thetaRaw (v+0)).Nodup ∧ (base thetaRaw (v+0)).toFinset = insert (neg b) (thetaRaw.toFinset.erase b)) ∧
      ((base thetaRaw (v+1)).Nodup ∧ (base thetaRaw (v+1)).toFinset = thetaRaw.toFinset) ∧
      ((base thetaRaw (v+2)).Nodup ∧ (base thetaRaw (v+2)).toFinset = insert (neg b) thetaRaw.toFinset) := by
  rw [flat_eq]
  decide +kernel

theorem theta_from_bases
    (checks : ∀ (j : Fin 7), (j=0 ∨ j=2 ∨ j=3) → ∀ f : Fin 3,
      AtBase [] 10 (base thetaRaw (3*j.val + f.val))) : ThreeNumeric := by
  intro j hj k t S hk hl sub
  obtain ⟨mem,f0,f1,f2⟩ := theta_forms j
  have hl' : Marked2153.Restricted [] k t S := Marked2153.ignoreNegative (signedFree hl)
  rcases initial_of_basis theta_holes mem hl sub with h | h | h
  · exact atBase_exclude (checks j hj 1) f1.1 (f1.2.trans h.symm) hk hl'
  · exact atBase_exclude (checks j hj 0) f0.1 (f0.2.trans h.symm) hk hl'
  · exact atBase_exclude (checks j hj 2) f2.1 (f2.2.trans h.symm) hk hl'

lemma eight_forms :
    ((base raw 0).Nodup ∧ (base raw 0).toFinset = insert (neg raw0) (raw.toFinset.erase raw0)) ∧
    ((base raw 3).Nodup ∧ (base raw 3).toFinset = insert (neg raw1) (raw.toFinset.erase raw1)) ∧
    ((base raw 4).Nodup ∧ (base raw 4).toFinset = raw.toFinset) ∧
    ((base raw 5).Nodup ∧ (base raw 5).toFinset = insert (neg raw1) raw.toFinset) := by decide +kernel

theorem eight_from_bases
    (h0 : AtBase (posMarks true) 12 (base raw 0))
    (h3 : AtBase (posMarks false) 12 (base raw 3))
    (h4 : AtBase (posMarks false) 12 (base raw 4))
    (h5 : AtBase (posMarks false) 12 (base raw 5)) : EightNumeric := by
  intro mode k t S hm hk hl
  obtain ⟨f0,f3,f4,f5⟩ := eight_forms
  have r := Marked2153.ignoreNegative hl
  cases mode
  · simp only [roots,Bool.false_eq_true,ite_false,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with h | h | h
    · exact atBase_exclude h4 f4.1 (f4.2.trans h.symm) hk r
    · exact atBase_exclude h3 f3.1 (f3.2.trans h.symm) hk r
    · exact atBase_exclude h5 f5.1 (f5.2.trans h.symm) hk r
  · simp only [roots,ite_true,List.mem_singleton] at hm
    exact atBase_exclude h0 f0.1 (f0.2.trans hm.symm) hk r

end RootGlue2153

namespace OrbitCache2153
open Search2153 ThetaSym2153

def groupSize (group : Nat) : Nat := if group = 0 then 4 else if group = 1 then 2 else if group = 2 then 8 else 1
def rawBasis (group : Nat) : List Sig := if group = 0 then thetaFlat else raw
def basis (group : Nat) : Nat → List Sig := Cache2153.base (rawBasis group)
def marks (group : Nat) : List Sig := if group = 0 then [] else if group = 1 then [raw3,raw5,raw6] else [raw0,raw3,raw5,raw6]

def thetaRot : Nat → List Sig
  | 1 => [thetaFlat.getD 0 zero,thetaFlat.getD 1 zero,thetaFlat.getD 2 zero,thetaFlat.getD 5 zero,thetaFlat.getD 6 zero,thetaFlat.getD 3 zero,thetaFlat.getD 4 zero]
  | 2 => [thetaFlat.getD 1 zero,thetaFlat.getD 0 zero,thetaFlat.getD 2 zero,thetaFlat.getD 4 zero,thetaFlat.getD 3 zero,thetaFlat.getD 6 zero,thetaFlat.getD 5 zero]
  | 3 => [thetaFlat.getD 1 zero,thetaFlat.getD 0 zero,thetaFlat.getD 2 zero,thetaFlat.getD 6 zero,thetaFlat.getD 5 zero,thetaFlat.getD 4 zero,thetaFlat.getD 3 zero]
  | _ => thetaFlat

def eightRot : Nat → List Sig
  | 1 => [raw0,raw4,raw7,raw3,raw1,raw6,raw5,raw2]
  | 2 => [raw3,raw2,raw1,raw0,raw7,raw6,raw5,raw4]
  | 3 => [raw3,raw7,raw4,raw0,raw2,raw5,raw6,raw1]
  | 4 => [raw5,raw1,raw2,raw6,raw7,raw0,raw3,raw4]
  | 5 => [raw5,raw7,raw4,raw6,raw1,raw3,raw0,raw2]
  | 6 => [raw6,raw2,raw1,raw5,raw4,raw3,raw0,raw7]
  | 7 => [raw6,raw4,raw7,raw5,raw2,raw0,raw3,raw1]
  | _ => raw

def rotRaw (group g : Nat) : List Sig :=
  if g < groupSize group then
    if group = 0 then thetaRot g else eightRot g
  else rawBasis group

def rotBase (group g code : Nat) : List Sig := Cache2153.base (rotRaw group g) code

end OrbitCache2153

namespace OrbitTransport2153
open Search2153 Cache2153

structure Hom where
  fn : Sig → Sig
  z : fn zero = zero
  o : fn one = one
  tar : fn target = target
  unary : ∀ a, fn (neg a) = neg (fn a)
  binary : ∀ d a b, fn (bin d a b) = bin d (fn a) (fn b)

def Stable (f b : Hom) (x : Sig) : Prop := b.fn (f.fn x) = x
lemma stable_neg {f b : Hom} {a} (h : Stable f b a) : Stable f b (neg a) := by
  simpa only [Stable,f.unary,b.unary] using congrArg neg h
lemma stable_bin {f b : Hom} {a c} (d : Bool) (ha : Stable f b a) (hc : Stable f b c) :
    Stable f b (bin d a c) := by unfold Stable at *; rw [f.binary,b.binary,ha,hc]
lemma inj_on {f b : Hom} {a c} (ha : Stable f b a) (hc : Stable f b c)
    (e : f.fn a = f.fn c) : a = c := ha.symm.trans ((congrArg b.fn e).trans hc)
lemma stable_zero (f b : Hom) : Stable f b zero := by unfold Stable; rw [f.z,b.z]
lemma stable_one (f b : Hom) : Stable f b one := by unfold Stable; rw [f.o,b.o]
lemma proper_map {f b : Hom} {a} (ha : Stable f b a) (hp : proper a) : proper (f.fn a) := by
  exact ⟨fun h => hp.1 (inj_on ha (stable_zero f b) (h.trans f.z.symm)),
    fun h => hp.2 (inj_on ha (stable_one f b) (h.trans f.o.symm))⟩

lemma image_reflect {f b : Hom} {a : Sig} {S : Finset Sig} (ha : Stable f b a) (hs : ∀ x ∈ S, Stable f b x) :
    f.fn a ∈ S.image f.fn → a ∈ S := by
  intro m
  obtain ⟨x,hx,e⟩ := Finset.mem_image.mp m
  exact (inj_on (hs _ hx) ha e) ▸ hx

theorem transport {p q : List Sig} (f b : Hom)
    (marks : ∀ a, Stable f b a → f.fn a ∈ q → a ∈ p)
    {k t S} (h : Marked2153.Restricted p k t S)
    (good : ∀ a ∈ S, Stable f b a) : Marked2153.Restricted q k t (S.image f.fn) := by
  induction h with
  | stop => simpa only [Finset.image_singleton,f.tar] using (Marked2153.Restricted.stop (p := q))
  | @unary k t U a hp fresh notMarked tail ih =>
    have ga := good a (Finset.mem_insert_self _ _)
    have gu (x : Sig) (hx : x ∈ U) := good x (Finset.mem_insert_of_mem hx)
    have gn := stable_neg ga
    have m : ∀x ∈ insert (neg a) U, Stable f b x := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx; exact gn; exact gu _ hx
    have n : neg (f.fn a) ∉ insert (f.fn a) (U.image f.fn) := by
      rw [←f.unary,←Finset.image_insert]
      exact fun ha => fresh (image_reflect gn good ha)
    rw [Finset.image_insert]
    exact .unary (proper_map ga hp) n (fun hh => notMarked (marks a ga hh))
      (by simpa only [Finset.image_insert,f.unary] using ih m)
  | @binary k t U a c d ha hc ne fresh ma mc tail ih =>
    have ga := good a (Finset.mem_insert_self _ _)
    have gc := good c (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have gu (x : Sig) (hx : x ∈ U) := good x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
    have gz := stable_bin d ga gc
    have gg : ∀x ∈ insert (bin d a c) U, Stable f b x := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx; exact gz; exact gu _ hx
    have n : bin d (f.fn a) (f.fn c) ∉ insert (f.fn a) (insert (f.fn c) (U.image f.fn)) := by
      rw [←f.binary,←Finset.image_insert,←Finset.image_insert]
      exact fun h => fresh (image_reflect gz good h)
    have rule {x : Sig} (gx : Stable f b x) (mk : x ∈ p → d = true ∧ x ∉ U)
        (m : f.fn x ∈ q) : d=true ∧ f.fn x ∉ U.image f.fn := by
      obtain ⟨h1,h2⟩ := mk (marks _ gx m)
      exact ⟨h1,fun h => h2 (image_reflect gx gu h)⟩
    simp only [Finset.image_insert]
    exact .binary (proper_map ga ha) (proper_map gc hc) (fun h => ne (inj_on ga gc h)) n
      (rule ga ma) (rule gc mc) (by simpa only [Finset.image_insert,f.binary] using ih gg)

lemma list_fixes {l : List Sig} {F : Sig → Sig} (h : l.map F = l) : ∀ a ∈ l, F a = a := by
  intro a ha
  obtain ⟨i,hi,hv⟩ := List.getElem_of_mem ha
  have eq := congrArg (fun v : List Sig => v[i]?) h
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,hv,Option.some.injEq] using eq

lemma map_getD (f : Hom) (v : List Sig) (i : Nat) :
    (v.map f.fn).getD i zero = f.fn (v.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : v[i]? <;> simp [f.z]

lemma map_erase (f b : Hom) (v : List Sig) (a : Sig)
    (ha : Stable f b a) (good : ∀x∈v,Stable f b x) :
    (v.erase a).map f.fn = (v.map f.fn).erase (f.fn a) := by
  induction v with
  | nil => rfl
  | cons x v ih =>
    have gx := good x List.mem_cons_self
    by_cases h : x = a
    · subst x; simp
    · have h' : f.fn x ≠ f.fn a := fun e => h (inj_on gx ha e)
      simp [List.erase_cons_head, List.erase_cons_tail, h, h', ih (fun y hy => good y (List.mem_cons_of_mem _ hy))]

lemma base_comm (f b : Hom) (v : List Sig) (c : Nat) (good : ∀a∈v,Stable f b a) :
    base (v.map f.fn) c = (base v c).map f.fn := by
  have ha : Stable f b (v.getD (c/3) zero) := by
    rw [List.getD_eq_getElem?_getD]
    cases h : v[c/3]? with
    | none => exact stable_zero _ _
    | some a => exact good a (List.mem_of_getElem? h)
  simp only [base,map_getD,List.map_append]
  split <;> split <;> simp only [List.map_nil,List.map_cons,f.unary,map_erase f b _ _ ha good]

lemma step_comm (f : Hom) (v : List Sig) (a : Nat) :
    replayStep (v.map f.fn) a = (replayStep v a).map f.fn := by
  by_cases hs : a < 440 <;> cases h0 : a.testBit 0 <;> cases h1 : a.testBit 1 <;>
    simp only [replayStep,hs,h0,h1,ite_true,ite_false,Bool.false_eq_true,List.map_cons,
      List.map_append,List.map_nil,map_getD,List.eraseIdx_map,f.unary,f.binary]

lemma replay_comm (f : Hom) (start rot : Nat → List Sig)
    (hs : ∀ c, rot c = (start c).map f.fn) (d c : Nat) :
    replay rot d c = (replay start d c).map f.fn := by
  induction d generalizing c with
  | zero => exact hs c
  | succ d ih =>
    simp only [replay,ih,step_comm]

theorem transport_impossible (f b : Hom) (p : List Sig) (l r : List Sig)
    (forward : r = l.map f.fn) (back : l = r.map b.fn)
    (keep : ∀a∈p,f.fn a ∈ p) {k t} (no : Marked2153.Impossible p k t l) :
    Marked2153.Impossible p k t r := by
  have hcomp : r.map (f.fn ∘ b.fn) = r := by rw [←List.map_map,←back,←forward]
  have gg : ∀x∈r,Stable b f x := list_fixes hcomp
  have idset : r.toFinset.image b.fn = l.toFinset := by
    rw [back]; ext x; simp only [List.mem_toFinset,Finset.mem_image,List.mem_map]
  intro m hm hr
  have out := transport b f (p := p) (q := p)
    (fun x gx hx => gx ▸ keep (b.fn x) hx) hr (fun a ha => gg a (List.mem_toFinset.mp ha))
  exact no m hm (idset ▸ out)

end OrbitTransport2153

namespace OrbitCache2153
open Search2153 Projection2153 ThetaSym2153 OrbitTransport2153

def symKeys : Fin 8 → Nat := ![
  0xfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0dfdedddcdbdad9d8d7d6d5d4d3d2d1d0cfcecdcccbcac9c8c7c6c5c4c3c2c1c0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100,
  0x9a999e949592935d4f4e626355565354e3dedfdcdd5c5b79eb747877e9eae7e88972736a696f676e6b6d71706c68664029a6a5a43a39181110150e14121317160f0d0cb8b73e3f2728201f241c23212226251e1d1bcac9c83837989796f991908ffbfaa1a09ff7f8f5f69d9c9b6160525150db5a594d46454a494744484c4b434241e4e1e05f5ee2d9dad1d0d6d4d2cfd3d8d7ced5cd5857f0f18e8d7675f4e6e588876564eeefeced8c8b8af3f2867e7d83827f818584807c7b7accb5b63d1a19c7c6a3a2360504090806070b0a03020100cbb3b4abaab0aeacadb2b1a9a8afa73c3bc5bdbcc2c0bebfc4c3bbc1bab92f2e3332303135342d2c2b2a,
  0xa19d9e9fa09b9ce3e4e25c5b5f5e58575d61605a596263f3f4f28c868d8e8788898a8b7e7f7c7b827d84858180837acac5ccc6c7c8c9cbbdbebbbac0bcc3c4bfc2c1b93d3638373c3b2f302d2c322e343531332b2a40393a3e3ffbf7f8f9faf5f698919a95949796908f999392dedfe1d9dadbdcdde0d1d2ced4d0cfd7d8d3d6d5cd4f524d55564e51504647434945444b4c484a42415354e5e6eae9efeeebf1f0e8e7edec757664657873727974776a6b686e6970716d6c6f6766a6a2a3b8b4b3a4a5b6b5b7abaca9aeaab1b2adb0afa8a718191a05060308040a0b070901020027282911120f1410161713150d0e0c20211e231f252622241c1d1b,
  0x9891f996978f90eb7974e6e576756564f48e8d8887f1f04f5d4e524d6061595adb50514c484342494b454647444a41a61840393aa4a52917130f0d1416101112150e0c3d36a3a21a190b070302080a040506090100ccc6c7b6b59a95949e999392a19dfbf7f8a09f9c9bfaf5f6eae978737289e8e777716d686e706c696a6b6f6766f38c86efeef28b8a85817c8284807d7e7f837b7aedec5b5cdedf5556e36263dcdd53545e5f5758e1d9dae4e2e0d8d3ced4d7d0d1d2cfd6d5cdca3738b82728c8c93e3fb726221e23251f2021241c1d1bc53b3c35312d32342e2f30332b2c2ab4b3cbc4bfbbc0c3bcbdbec2bac1b9b2ada9aeb1aaabacb0afa8a7,
  0xa18c3d5f5e3c3bcce4cb8d8e9fa08a8b4063623f3e6061f3cac59d865c5b38373658572d302f2c323134332e2b352af4f2e3c8c9c6c7e2bbbebdbac0bfc3c2bcc4c1b99e8987889b9c7c7f7e7b828184837d85807a5d3a39595afbeeefb8e1b3b49a789875765655282752191af0f1faecedb7b5b6e0a9acabaeada8b1b0aab2afa779997796972954531e212023221d25241f261c1b5051eae9e5e6f8f7a6dfdea2a3dad9959473729164654f184d03060508070a0904010b0200ebe8e7f9f6f5a5a4dddcdbced2d1d4d3d7d6d0d8d5cfcd749392686b6a6e6d706f69716c67668f904e0f12111413161510170e0d0c43474649484b4a454c424441,
  0x9a78b855562728a64f18e9ea94957273ca5b5c3738dfde794029997762633e3fb75354241f201c2325221e211d261beb745d3a39a5a44e1510110e1416130f12170d0c9e89e7e892936f696a676e706d686b716c66e3c8c9dddc9875763d52191aa18cfbeeef5e5f3b3ce1b3b4e5e691646536a2a34d090405080a010703060b0200f39d86f8f7c55758332e2f32342b312d30352c2adad98e8df0f19697cc6061b5b65051a09f8b8afaecede4cbe0b0aaabaeb1ada9aca8b2afa7f48887f98f90c6c7595adb4a4546494b4843474c424441f29c9b837d7e8284817c7f85807b7af6f5e2c2bcbdc0c3bfbbbec4bac1b9d6d0d1d4d7d3ced2d8d5cfcd,
  0xfbe1b8efeeb4b3caf3c5dfdef8f7dad9a6e5e6a2a3e9eae4cccbfae0f1f0b6b5b7edecb0b1b2afaeaaaca9ada8aba7e3e2f4c7c6c9c8f2c2c3c4c1c0bcbebbbfbdbab9f9dbdddcf6f5d6d7d8d5d4d0d2ced3d1cfcdeba4a5e7e8a15e5f3d8c3b3c98529a56557576191a7828275b5c9d575836373886333435322e2b302d312f2c2a4f914d9495186465090a0b0804010603070502007273616063629fa0408d8e3f3e8a8b97965150995453792977242526231f211e221d201c1b5d5a599e9b9c393a878889838485827d7f7c817e7b807a4e908f4a4b4c4945474348464442419293741516171410120f13110d0e0c6f70716e696b686d6a676c66,
  0x98523d76751a19407929606196975051ccf0f1b5b68d8e4fa618914de6e5a3a236656403070b02080604090a0105005d4eeba4a5393a740f13170d1412101516110e0cf9db595a8f9043484c424947454a4b464441f4c7c687889a5655b8782827fbe1a15e5feeefb3b48c3b3c6362995453b73f3e771e222623211d1f2425201c1be4fae09fa0cbeceda9adb2aeaca8aab0b1abafa78a8bdedf5b5c9495cae9ea37387273f7f8d9da9d5758f3c5862d313532302e33342b2f2c2ae3dcdd9e9293c9c8e7e889686d716e6b696f706a676c66e2f5f6ced3d8d4d2d0d6d7d1cfd5cd9b9cf2bbbfc4c0bebcc2c3bdc1bab97c8185827f7d83847e7b807a]

def reindexHom (u v : Fin 252 → Fin 252) : Hom where
  fn a := (reindex u a.1,reindex v a.2)
  z := Prod.ext (reindex_zero _) (reindex_zero _)
  o := Prod.ext (reindex_top _) (reindex_top _)
  tar := Prod.ext (reindex_top _) (reindex_zero _)
  unary a := by simp [neg,reindex_not]
  binary d a b := by cases d <;> simp [bin,reindex_and,reindex_or]

def invIdx : Fin 8 → Fin 8 := ![0,1,2,3,4,7,6,5]
-- The two order-four selectors use the opposite orientation in the stock table.
def eightHom (g : Fin 8) := reindexHom (index (symKeys (invIdx g))) (index (symKeys (invIdx g)))
def thetaIdx : Fin 4 → Fin 7 := ![0,5,1,6]
def thetaHom (g : Fin 4) := reindexHom (index (key0 (thetaIdx g))) (index (key1 (thetaIdx g)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma fullImages : ∀ g : Fin 8,
    raw.map (eightHom g).fn = eightRot g.val ∧
    (eightRot g.val).map (eightHom (invIdx g)).fn = raw ∧
    ((marks 2).map (eightHom g).fn).toFinset = (marks 2).toFinset := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma leafImages : ∀ g : Fin 2,
    ((marks 1).map (eightHom (Fin.castLE (by decide) g)).fn).toFinset = (marks 1).toFinset := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma thetaImages : ∀ g : Fin 4,
    thetaFlat.map (thetaHom g).fn = thetaRot g.val ∧
    (thetaRot g.val).map (thetaHom g).fn = thetaFlat := by decide +kernel

theorem onRawLists (f b : Hom) (l r p : List Sig)
    (fr : l.map f.fn = r) (br : r.map b.fn = l)
    (mp : (p.map f.fn).toFinset = p.toFinset)
    (depth code k t : Nat)
    (hi : Marked2153.Impossible p k t (Cache2153.replay (Cache2153.base l) depth code)) :
    Marked2153.Impossible p k t (Cache2153.replay (Cache2153.base r) depth code) := by
  have fixl : l.map (b.fn ∘ f.fn) = l := by rw [←List.map_map,fr,br]
  have fixr : r.map (f.fn ∘ b.fn) = r := by rw [←List.map_map,br,fr]
  apply transport_impossible f b p _ _ _ _ _ hi
  · apply replay_comm
    intro c
    rw [←fr,base_comm f b l c (list_fixes fixl)]
  · apply replay_comm
    intro c
    rw [←br,base_comm b f r c (list_fixes fixr)]
  · intro a ha
    apply List.mem_toFinset.mp
    rw [←mp]
    exact List.mem_toFinset.mpr (List.mem_map_of_mem ha)

theorem sound (group g : Nat) (hg : g < groupSize group) (depth code k t : Nat)
    (hi : Marked2153.Impossible (marks group) k t (Cache2153.replay (basis group) depth code)) :
    Marked2153.Impossible (marks group) k t (Cache2153.replay (rotBase group g) depth code) := by
  rcases group with _ | group
  · have hg' : g < 4 := hg
    let j : Fin 4 := ⟨g,hg'⟩
    obtain ⟨f,b⟩ := thetaImages j
    have rr : rotBase 0 g = Cache2153.base (thetaRot g) := by funext c; simp [rotBase,rotRaw,hg]
    rw [rr]
    exact onRawLists (thetaHom j) (thetaHom j) thetaFlat (thetaRot g) [] f b rfl depth code k t hi
  rcases group with _ | group
  · have hg' : g < 2 := hg
    let j : Fin 8 := ⟨g,by omega⟩
    obtain ⟨f,b,_⟩ := fullImages j
    have rr : rotBase 1 g = Cache2153.base (eightRot g) := by funext c; simp [rotBase,rotRaw,hg]
    rw [rr]
    exact onRawLists (eightHom j) (eightHom (invIdx j)) raw (eightRot g) (marks 1) f b
      (leafImages ⟨g,hg'⟩) depth code k t hi
  rcases group with _ | group
  · let j : Fin 8 := ⟨g,hg⟩
    obtain ⟨f,b,m⟩ := fullImages j
    have rr : rotBase 2 g = Cache2153.base (eightRot g) := by funext c; simp [rotBase,rotRaw,hg]
    rw [rr]
    exact onRawLists (eightHom j) (eightHom (invIdx j)) raw (eightRot g) (marks 2) f b m depth code k t hi
  · have hg' : g < 1 := hg
    obtain rfl : g = 0 := by omega
    exact hi

end OrbitCache2153

open Search2153 Cache2153

namespace OrbitLookup2153

def orbitHit (groups reps n buckets : Nat) (offset ref recipe : Nat → Nat)
    (rot : Nat → Nat → List Sig) (depth t : Nat) (v : List Sig) : Bool :=
  let h := stateHash t v
  let b := h % buckets
  let start := offset b
  (List.range (offset (b+1)-start)).any fun j =>
    let i := start+j
    let r := ref i
    let ri := r >>> 7
    let g := (r >>> 4) &&& 7
    (r &&& 15 == (h / buckets) &&& 15) && decide (ri < reps) && decide (g < groups) &&
      (recipe ri &&& 7 == t) && (replay (rot g) depth (recipe ri >>> 3)).isPerm v

theorem hitSound {groups reps n buckets : Nat} {offset ref recipe : Nat → Nat}
    {basis : Nat → List Sig} {rot : Nat → Nat → List Sig} {depth k t : Nat} {p v : List Sig}
    (proofs : ∀ i < reps, Marked2153.Impossible p k (recipe i &&& 7) (replay basis depth (recipe i >>> 3)))
    (transport : ∀ g < groups, ∀ code q,
      Marked2153.Impossible p k q (replay basis depth code) →
        Marked2153.Impossible p k q (replay (rot g) depth code))
    (hit : orbitHit groups reps n buckets offset ref recipe rot depth t v = true) :
    Marked2153.Impossible p k t v := by
  unfold orbitHit at hit
  obtain ⟨j,_,hj⟩ := List.any_eq_true.mp hit
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,List.isPerm_iff] at hj
  obtain ⟨⟨⟨⟨_,hi⟩,hg⟩,ht⟩,hp⟩ := hj
  have hh := transport _ hg _ _ (proofs _ hi)
  rw [ht] at hh
  intro m hm hr
  apply hh m hm
  exact (List.toFinset_eq_of_perm _ _ hp).symm ▸ hr

end OrbitLookup2153

namespace SixMinor2153

open Search2153 Projection2153 OrbitTransport2153

def six0 : List Sig := [(0xed6095a54b8f972fb5dc09c69e5221885027ae0d2fe0cce230c8124780ff4cf,0x18c834020a0d1208131564c4e84926549024f10678719700508124380454c5),(0x538f6952feab80dacfacbc11353b82c901b9e504a8530e0709b12079f32c8fc,0x220008051a7f00020c8312b3e8699c10202062f18128a52581e12008b12c85c),(0x24ffbefc9006de64935f10e4c9a81938be400973788404f2f441c39e1c30f0f,0x82116004cf0c2455408028b3a0096d8aa435306c0838a605e8c1c09c143090a),(0x5567474c17354ee07ae1861a2295f870e551667250462214cc3e03e01fc0ff0,0x4661200200003089218810c151202645bc88d0276c758da161e03600ac06a0),(0xba1bfadb29d0e155a0334b3a7644ec86eb061288072cf308028ffc001fff000,0x16203015961008430a062832916801123678a0a99868648782f364001fba000),(0x4ed82c37e67c319b5c82722dc92e56071ae899a4c0193919030fffffe000000,0x808102200046845150c54c06966089c987150662971a087c0c9bf74000000)]

def six1 : List Sig := [(0x52ce350b538086d7ca28bd249b9dec485d4c1a9937053d44f140411de267f93,0x908090202a1002280241021a142b3c2744e84c49c350a1a4c610410ce022b91),(0xabb8a37daa5f7952bdfa4cc0343652a63832ad20a96a88da0eb602267d9e1fc,0x110012400200002a002020000182050001652a2460728800c0200288e0b4),(0xa17b4a807b1ed7a96095df304f2929e5234e12c9920f9112004b8c39861861f,0x4678010c114d1941e802a5c5cb94c310a907a1a41ca9585339e38c31061040a),(0xb332f65efc7c74fd49a5f2fb8a813200d5b19532178028c80f81f03e07e07e0,0x2e12600c0b7b4824a15474507c7c61cb0fff89214d91d85777f3f03e0760740),(0x7db75e834cab1daf064d729fd0e4d539c683c07644906627f509ffc007ff800,0x614820188042cc0000809821e14480d83b17333238065648290e964007dd000),(0xde45d9fe34f5ea68d7c7a35b605a09138a8d6a4668f14221003dfffff800000,0xab44942121001d90c48445c1abb67058480c88d45a9a89356f169bfd000000)]

def sixRaw (short : Bool) : List Sig := if short then six0 else six1

def cutAt : Fin 5 → Fin 7 := ![2,3,4,5,6]

def pKey : Fin 5 → Nat := ![0xd04ee2c57f850bdee185b9dd4b451111e2c54be24b85c1dee211c44bc1850b7fe1df0b45ab6e4e8aabda6e8edf85e5dec2c1dac4e3b9b97f6e11b90bdfe2df7fc26e8a856edf45e54eb9c5e2e5e5ddc1d5dad1e1abd58ed0fbfbddc58ec48ad1c4ddc5abc4ab8ae1e3d0e1dee18edfd5c58e8ac8c1dad1fbabd5e3e3e5dadad1c18ac1c4dde3ddc5d1c8dfd5d1d0d0dedfd5dedac4de8ae1dae3c8e3d0dfe3fbd1c8e5e3e5d0d0d0fbded0d1dac1d5d1d0d08edadfe5c5dafbfbfbc8dad5e5d1e3e3fbfbd5e3dad1abfbd5d5bf8e8e4bdddd0b7fdada85c8c84e6ee1e1c4c4dfdfd1d111c1c1c5c58a8ac2e2ababd0d045b9e3e3deded5d5e5e5fbfb,0x3d7f1cbf0bda4e1cabd31c1ce77fcad46e46debfd48a1cdfd46ed16e4e6ebfabd5ca3dce1c8ee7e47f6e8e3d1c3db20bd33d6e1c0bcad3b2ca4e46de468aabcadfcec6d1de0b7f6e3d0bdec6ab46d146ce1cbfcae7e746d3c56edc468ed08e8e8ad4d1abdcc6dce48adab2dfd3abd1dcd0abdcc5d3d0d5d4c6e4b2dad0c6d1d48e8ac6dedf8ad4dc8ee4d5d5d3d3b28ec5dad1dcdfd5d3d5e4d4c58ae4da8ee4c6dadfdcd18adcde8ed1d1dac6e4c6d3c6da8ae4ded0dae4d5dedac6d5d0b2dad0d0d0d0d5c5d58ad5e4d1d1d4d1c64646bf8e8ed4d40b7fdada3dcece4e6ed3d3dfdfd1d11ccac5c58a8ab2b2ababd0d0dcdcdeded5d5e7c6c6e4e4,0xb10b904b7fdac290dfb29090e70b56d4e2bae54bd4e190abd4e2d0e2c2e24bdffb56b15a90dde7c60be2ddb190b1d37fb2b1e2907f56b2d356c2bae5bae1df56ab5ae4d0e57f0be2b17fe5e4dfbad0ba5a904b56e7e7bab2c4e2e0baddd1dddde1d4d0dfe0e4e0c6e1dad3abb2dfd0e0d1dfe0c4b2d1fbd4e4c6d3dad1e4d0d4dde1e4e5abe1d4e0ddc6fbfbb2b2d3ddc4dad0e0abfbb2fbc6d4c4e1c6daddc6e4daabe0d0e1e0e5ddd0d0dae4c6e4b2e4dae1c6e5d1dac6fbe5dae4fbd1d3dad1d1d1d1fbc4fbe1fbc6d0d0d4d0e4baba4bddddd4d47f0bdadab15a5ac2e2b2b2ababd0d09056c4c4e1e1d3d3dfdfd1d1e0e0e5e5fbfbe7e4e4c6c6,0x3db9568545e34e56e5dc5656e7b990d76e0cdf85d7c456ded76ed56e4e6e85e5d1903dce56c8e7e4b96ec83d563de045dc3d6e564590dce0904e0cdf0cc4e590decec6d5df45b96e3d45dfc6e50cd50cce568590e7e70cdce16ed30cc8fbc8c8c4d7d5e5d3c6d3e4c4e3e0dedce5d5d3fbe5d3e1dcfbd1d7c6e4e0e3fbc6d5d7c8c4c6dfdec4d7d3c8e4d1d1dcdce0c8e1e3d5d3ded1dcd1e4d7e1c4e4e3c8e4c6e3ded3d5c4d3dfc8d5d5e3c6e4c6dcc6e3c4e4dffbe3e4d1dfe3c6d1fbe0e3fbfbfbfbd1e1d1c4d1e4d5d5d7d5c60c0c85c8c8d7d745b9e3e33dcece4e6edcdcdeded5d55690e1e1c4c4e0e0e5e5fbfbd3d3dfdfd1d1e7c6c6e4e4,0xb145ca11b9e3c2cadee0cacae7451cd7e280ab11d7c5cae5d7e2fbe2c2e211ded01cb15acac1e7c645e2c1b1cab1dcb9e0b1e2cab91ce0dc1cc280ab80c5de1ce55ae4fbabb945e2b1b9abe4de80fb805aca111ce7e780e08ae2b280c1d5c1c1c5d7fbdeb2e4b2c6c5e3dce5e0defbb2d5deb28ae0d5d0d7e4c6dce3d5e4fbd7c1c5e4abe5c5d7b2c1c6d0d0e0e0dcc18ae3fbb2e5d0e0d0c6d78ac5c6e3c1c6e4e3e5b2fbc5b2abc1fbfbe3e4c6e4e0e4e3c5c6abd5e3c6d0abe3e4d0d5dce3d5d5d5d5d08ad0c5d0c6fbfbd7fbe4808011c1c1d7d7b945e3e3b15a5ac2e2e0e0e5e5fbfbca1c8a8ac5c5dcdcdeded5d5b2b2ababd0d0e7e4e4c6c6]

def nKey : Fin 5 → Nat := ![0xcde6e193e6dac9e5dd59dacde5db59cdddcdc1dae1e6dbdde6e5e693e6c91fb2c1cdd3b2dec1c9cde5e1fbb2dedee1e1e5ddcde593b54ddb1fc1e5cd59b5b2c1dbb5e64db2e1daddde1fe5d35993b2fb4dddc1fbc1ddfb4ddeddc9c9d3d3c9dec9fbdedafbd3dddaddb2b24dc9dd4ddefbb5b5fbdededbc1b5dbdbb2b5dbc1ddb5d3c9dad3c1dad34ddac9c1dab5ddb5dafbc9b5dbd3fbd3b2dec9fbc1b54db2b2d3d3dac1dbd3fbd3dac9b5c9d3d3d3dedac9d3d3c9b5fbdadbfbdb4dc9dac9c9b5b54db5d3dafbc9c9b2dad34ddac9b5c1b2dd1f93d34db5d34db5deb5ddddfb1fe1c9dac1dab2dadbc9c1b2fb93e5dedb59cddbfb59e1defbcde5,0xe5d9dae54da5d793ddd9dfd7d91f59e1e54ddafb1fe6e6dfe61fe593d8a51fe193e6fbdfdbe1d3a5e6d859d3a5e7daa593dae1e7d893e5df1fdfdb1fdd59e6dfa5e7a5e6df1ffb59b2d3e1591f59e7e5d94da5da93d7fbe7e7d793d3dddffbd9d9d8dad3d7dbdfd9dfdad3d7d3d8ddddd9d7d3fbfbdddfd7dadafbd9dadddbd3dffbd9b2d8d3dad8d3dbdbdadbd8d8d8d7ddd9b2d3fbb2d8dffbd8b2dddfb2d3fbd3b2d9d8d7fbd3d7fbdfdbdfb2b2d7d3d8ddd8d7b2b2fbddd8fbd7b2dbd7d7fbd3d8d7d9d3d3d8d7d7d7d3b2b2d8d7d8d34ddadfd9b2dd1f93d7d7d3d34ddfddddfb1fe1d8d8dab2dadbd9b2b2fb93e5a5dbdbfb59e1fbe7e1e7e5,0xe1dfb5e1c19fc71fb2dfd9c7df93cde5e1c1b5fb93e6e6d9e693e11fcf9f93e51fe6fbd9dee5c99fe6cfcdc99fe7b59f1fb5e5e7cf1fe1d993d9de93b2cde6d99fe79fe6d993fbcdddc9e5cd93cde7e1dfc19fb51fc7fbe7e7c71fc9b2d9fbdfdfcfb5c9c7ded9dfd9b5c9c7c9cfb2b2dfc7c9fbfbb2d9c7b5b5fbdfb5b2dec9d9fbdfddcfc9b5cfc9dedeb5decfcfcfc7b2dfddc9fbddcfd9fbcfddb2d9ddc9fbc9dddfcfc7fbc9c7fbd9ded9ddddc7c9cfb2cfc7ddddfbb2cffbc7dddec7c7fbc9cfc7dfc9c9cfc7c7c7c9ddddcfc7cfc9c1b5d9dfddb2931fc7c7c9c9c1d9b2b2fb93e5cfcfb5ddb5dedfddddfb1fe19fdedefbcde5fbe7e5e7e1,0xe59fb5e54ddfd7cddb9fa5d79f591fe1e54db5fb59e6e6a5e659e5cdcfdf59e1cde6fba5dde1d3dfe6cf1fd3dfe7b5dfcdb5e1e7cfcde5a559a5dd59db1fe6a5dfe7dfe6a559fb1fded3e11f591fe7e59f4ddfb5cdd7fbe7e7d7cdd3dba5fb9f9fcfb5d3d7dda59fa5b5d3d7d3cfdbdb9fd7d3fbfbdba5d7b5b5fb9fb5dbddd3a5fb9fdecfd3b5cfd3ddddb5ddcfcfcfd7db9fded3fbdecfa5fbcfdedba5ded3fbd3de9fcfd7fbd3d7fba5dda5deded7d3cfdbcfd7dedefbdbcffbd7deddd7d7fbd3cfd79fd3d3cfd7d7d7d3dedecfd7cfd34db5a59fdedb59cdd7d7d3d34da5dbdbfb59e1cfcfb5deb5dd9fdedefbcde5dfddddfb1fe1fbe7e1e7e5,0xe1a5dae1c1d9c759dea59fc7a5cd93e5e1c1dafbcde6e69fe6cde159d8d9cde559e6fb9fb2e5c9d9e6d893c9d9e7dad959dae5e7d859e19fcd9fb2cdde93e69fd9e7d9e69fcdfb93dbc9e593cd93e7e1a5c1d9da59c7fbe7e7c759c9de9ffba5a5d8dac9c7b29fa59fdac9c7c9d8dedea5c7c9fbfbde9fc7dadafba5dadeb2c99ffba5dbd8c9dad8c9b2b2dab2d8d8d8c7dea5dbc9fbdbd89ffbd8dbde9fdbc9fbc9dba5d8c7fbc9c7fb9fb29fdbdbc7c9d8ded8c7dbdbfbded8fbc7dbb2c7c7fbc9d8c7a5c9c9d8c7c7c7c9dbdbd8c7d8c9c1da9fa5dbdecd59c7c7c9c9c19fdedefbcde5d8d8dadbdab2a5dbdbfb59e1d9b2b2fb93e5fbe7e5e7e1]

def hom (i : Fin 5) : Hom := OrbitCache2153.reindexHom (index (pKey i)) (index (nKey i))

def targetOrder (i : Fin 5) : List Sig :=
  let r := sixRaw (i == 0)
  (![[r.getD 0 zero,r.getD 1 zero,zero,r.getD 2 zero,r.getD 3 zero,r.getD 4 zero,r.getD 5 zero],[r.getD 0 zero,r.getD 1 zero,r.getD 2 zero,zero,r.getD 3 zero,r.getD 4 zero,r.getD 5 zero],[r.getD 1 zero,r.getD 0 zero,r.getD 2 zero,r.getD 3 zero,zero,r.getD 5 zero,r.getD 4 zero],[r.getD 0 zero,r.getD 1 zero,r.getD 2 zero,r.getD 4 zero,r.getD 5 zero,zero,r.getD 3 zero],[r.getD 1 zero,r.getD 0 zero,r.getD 2 zero,r.getD 5 zero,r.getD 4 zero,r.getD 3 zero,zero]] : Fin 5 → List Sig) i

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem mapRaw : ∀ i : Fin 5, ThetaSym2153.thetaFlat.map (hom i).fn = targetOrder i := by decide +kernel

def basis (b : Bool) (j : Fin 6) := sixRaw b ++ [neg ((sixRaw b).getD j.val zero)]

def check6 (b : Bool) (j : Fin 6) : Bool :=
  (basis b j).sublists.all fun w => (List.range 8).all fun t =>
    !(decide (w.length + t ≤ 8) && unionSep (decide (0<t)) w == top) ||
      !(Marked2153.search [] 7 t w)

theorem noLiveOfCheck (b : Bool) (j : Fin 6) (checked : check6 b j = true)
    (unique : (basis b j).Nodup) {m t : Nat} {S : Finset Sig}
    (hm : m ≤ 7) (live : Live m t S) (hs : S ⊆ (basis b j).toFinset) : False := by
  let w := (basis b j).filter (fun a => decide (a ∈ S))
  have sub : w ∈ (basis b j).sublists := List.mem_sublists.mpr (List.filter_sublist ..)
  have he : w.toFinset = S := by
    ext a
    simp only [w,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact and_iff_right_of_imp (fun h => List.mem_toFinset.mp (hs h))
  have nd : w.Nodup := unique.filter _
  obtain ⟨le,len⟩ := live_size live
  rw [← he,List.toFinset_card_of_nodup nd] at len
  have ht : t ∈ List.range 8 := List.mem_range.mpr (by omega)
  have yes := List.all_eq_true.mp (List.all_eq_true.mp checked w sub) t ht
  have cover := live_cover live he
  have good : w.length + t ≤ 8 := by omega
  have last := Marked2153.search_complete (Marked2153.ignoreNegative (signedFree live)) 7 hm w nd he
  simp only [decide_eq_true good,cover,beq_self_eq_true,Bool.true_and,Bool.not_true,Bool.false_or,last] at yes
  contradiction

def SixNumeric := ∀ b (j : Fin 6) (m t : Nat) (S : Finset Sig), m ≤ 7 → Live m t S →
    S ⊆ (basis b j).toFinset → False


set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checkedtrue0 : check6 true 0 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checkedtrue1 : check6 true 1 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checkedtrue2 : check6 true 2 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checkedtrue3 : check6 true 3 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checkedtrue4 : check6 true 4 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checkedtrue5 : check6 true 5 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checkedfalse0 : check6 false 0 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checkedfalse1 : check6 false 1 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checkedfalse2 : check6 false 2 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checkedfalse3 : check6 false 3 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checkedfalse4 : check6 false 4 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checkedfalse5 : check6 false 5 := by decide +kernel

set_option maxHeartbeats 0 in
theorem sixNumeric : SixNumeric := by
  intro b j m t S hm live sub
  apply noLiveOfCheck b j _ _ hm live sub
  · cases b with
    | false =>
      fin_cases j
      · exact checkedfalse0
      · exact checkedfalse1
      · exact checkedfalse2
      · exact checkedfalse3
      · exact checkedfalse4
      · exact checkedfalse5
    | true =>
      fin_cases j
      · exact checkedtrue0
      · exact checkedtrue1
      · exact checkedtrue2
      · exact checkedtrue3
      · exact checkedtrue4
      · exact checkedtrue5
  · have h : ∀ b (j : Fin 6), (basis b j).Nodup := by decide +kernel
    exact h b j
end SixMinor2153

open PEqualNP.CircuitLowerBounds
open Search2153 OrbitTransport2153
namespace MinorCore2153
def Feasible (i : Hom) (k : Nat) (S : Finset Sig) : Prop :=
  ∃ m ≤ k, ∃ t T, Live m t T ∧ T ⊆ S.image i.fn

lemma feasible_mono {i : Hom} {k k' : Nat} {S : Finset Sig}
    (h : Feasible i k S) (hk : k ≤ k') : Feasible i k' S := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h
  exact ⟨m, hm.trans hk, t, T, hl, hs⟩

lemma neg_rep (w : List Sig) (a : Sig) (ha : a ∈ w) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases (Or.inl ha : represented w a) with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr (fun hh => hh.2 neg_laws.1))
  · exact Or.inl (Or.inr (fun hh => hh.1 neg_laws.2))
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

lemma feasible_pull {i : Hom} {q : Nat} {S S' : Finset Sig} {g : Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image i.fn).toList (i.fn g) ∨
      witness (S.image i.fn).toList (i.fn g))
    (h : Feasible i q S') : Feasible i (q + 1) S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  have sub : ∀ a ∈ T, a ∈ (S.image i.fn).toList ++ [i.fn g] := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (ht ha)
    rcases Finset.mem_insert.mp (hs hb) with rfl | hb
    · simp
    · exact List.mem_append_left _ (Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hb))
  obtain ⟨m', t', T', hm', h', hT'⟩ := pull_gate hl hr sub
  exact ⟨m', by omega, t', T', h', fun a ha => Finset.mem_toList.mp (hT' _ ha)⟩

lemma feasible_free {i : Hom} {q : Nat} {S S' : Finset Sig} {g : Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image i.fn).toList (i.fn g))
    (h : Feasible i q S') : Feasible i q S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  refine ⟨m, hm, t, T, hl, ?_⟩
  intro a ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (ht ha)
  rcases Finset.mem_insert.mp (hs hb) with rfl | hb
  · exact Finset.mem_toList.mp (hr.resolve_right (fun hp => hp (live_proper hl _ ha)))
  · exact Finset.mem_image_of_mem _ hb

lemma pull_unary {i : Hom} {q : Nat} {a : Sig} {U : Finset Sig}
    (h : Feasible i q (insert (neg a) U)) :
    Feasible i (q+1) (insert a U) := by
  apply feasible_pull (g := neg a) (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rw [Hom.unary]
  exact neg_rep _ _ (by simp)

lemma pull_binary {i : Hom} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (h : Feasible i q (insert (bin d a b) U)) :
    Feasible i (q+1) (insert a (insert b U)) := by
  apply feasible_pull (g := bin d a b) (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rw [Hom.binary]
  exact bin_rep _ (Or.inl (by simp)) (Or.inl (by simp))

lemma free_unary {i : Hom} {q : Nat} {a : Sig} {U : Finset Sig}
    (ha : ¬ proper (i.fn a))
    (h : Feasible i q (insert (neg a) U)) :
    Feasible i q (insert a U) := by
  apply feasible_free (g := neg a) (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rcases operand_cases (Or.inr ha : represented [] (i.fn a)) with hz | ho | hm
  · exact Or.inr (fun hp => hp.2 (by rw [Hom.unary,hz,neg_laws.1]))
  · exact Or.inr (fun hp => hp.1 (by rw [Hom.unary,ho,neg_laws.2]))
  · simp at hm

lemma free_binary_left {i : Hom} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (ha : ¬ proper (i.fn a))
    (h : Feasible i q (insert (bin d a b) U)) :
    Feasible i q (insert a (insert b U)) := by
  apply feasible_free (g := bin d a b) (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rw [Hom.binary, bin_comm]
  rcases operand_cases (Or.inr ha : represented [] (i.fn a)) with hz | ho | hm
  · rw [hz]
    cases d
    · exact Or.inr (fun hp => hp.1 (bin_laws _).2.2.1)
    · rw [(bin_laws _).2.1]
      exact Or.inl (by simp)
  · rw [ho]
    cases d
    · rw [(bin_laws _).1]
      exact Or.inl (by simp)
    · exact Or.inr (fun hp => hp.2 (bin_laws _).2.2.2.1)
  · simp at hm

lemma free_binary_right {i : Hom} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (hb : ¬ proper (i.fn b))
    (h : Feasible i q (insert (bin d a b) U)) :
    Feasible i q (insert a (insert b U)) := by
  rw [bin_comm] at h
  rw [Finset.insert_comm]
  exact free_binary_left hb h

lemma feasible_live {k t : Nat} {S : Finset Sig} (h : Live k t S) (i : Hom) :
    Feasible i k S := by
  induction h with
  | stop =>
    refine ⟨0, Nat.le_refl _, 0, {target}, Live.stop, ?_⟩
    simp [Hom.tar]
  | unary _ _ _ ih => exact pull_unary ih
  | binary _ _ _ _ _ ih => exact pull_binary ih

lemma feasible_const {k t : Nat} {S : Finset Sig} (h : Live k t S)
    (i : Hom) (a : Sig) (ha : a ∈ S) (hc : ¬ proper (i.fn a)) :
    ∃ q < k, Feasible i q S := by
  induction h with
  | stop =>
    have ht : a = target := Finset.mem_singleton.mp ha
    exact (hc (by rw [ht, Hom.tar]; exact target_proper)).elim
  | @unary k t U b hp hf tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨k, by omega, free_unary hc (feasible_live tail i)⟩
    · obtain ⟨q,hq,h⟩ := ih (Finset.mem_insert_of_mem ha)
      exact ⟨q+1,by omega,pull_unary h⟩
  | @binary k t U b c d hb hc' hbc hf tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | hU
    · exact ⟨k, by omega, free_binary_left hc (feasible_live tail i)⟩
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact ⟨k, by omega, free_binary_right hc (feasible_live tail i)⟩
      · obtain ⟨q,hq,h⟩ := ih (Finset.mem_insert_of_mem hU)
        exact ⟨q+1,by omega,pull_binary h⟩

lemma not_proper_bin_consts {i : Hom} {a b : Sig}
    (d : Bool) (ha : ¬proper (i.fn a)) (hb : ¬proper (i.fn b)) :
    ¬proper (i.fn (bin d a b)) := by
  rw [Hom.binary]
  rcases operand_cases (Or.inr ha : represented [] (i.fn a)) with h | h | h <;>
    rcases operand_cases (Or.inr hb : represented [] (i.fn b)) with j | j | j <;>
    simp_all [proper,bin,one,zero,top]

lemma feasible_two_consts {k t : Nat} {S : Finset Sig} (h : Live k t S) (i : Hom)
    (a b : Sig) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hca : ¬ proper (i.fn a)) (hcb : ¬ proper (i.fn b)) :
    ∃ q, q + 2 ≤ k ∧ Feasible i q S := by
  induction h with
  | stop =>
    have e1 := Finset.mem_singleton.mp ha
    have e2 := Finset.mem_singleton.mp hb
    exact (hab (e1.trans e2.symm)).elim
  | @unary k t U c hpc _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | haU
    · have hbU : b ∈ U := (Finset.mem_insert.mp hb).resolve_left hab.symm
      obtain ⟨q, hq, hf⟩ := feasible_const tail i b (Finset.mem_insert_of_mem hbU) hcb
      exact ⟨q, by omega, free_unary hca hf⟩
    · rcases Finset.mem_insert.mp hb with rfl | hbU
      · obtain ⟨q, hq, hf⟩ := feasible_const tail i a (Finset.mem_insert_of_mem haU) hca
        exact ⟨q, by omega, free_unary hcb hf⟩
      · obtain ⟨q, hq, hf⟩ := ih (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU)
        exact ⟨q + 1, by omega, pull_unary hf⟩
  | @binary k t U c e d _ _ _ _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha1
    · rcases Finset.mem_insert.mp hb with hbEq | hb1
      · exact (hab hbEq.symm).elim
      · rcases Finset.mem_insert.mp hb1 with rfl | hbU
        · obtain ⟨q, hq, hf⟩ := feasible_const tail i (bin d a b) (Finset.mem_insert_self _ _)
            (not_proper_bin_consts d hca hcb)
          exact ⟨q, by omega, free_binary_left hca hf⟩
        · obtain ⟨q, hq, hf⟩ := feasible_const tail i b (Finset.mem_insert_of_mem hbU) hcb
          exact ⟨q, by omega, free_binary_left hca hf⟩
    · rcases Finset.mem_insert.mp ha1 with rfl | haU
      · rcases Finset.mem_insert.mp hb with rfl | hb1
        · obtain ⟨q, hq, hf⟩ := feasible_const tail i (bin d b a) (Finset.mem_insert_self _ _)
            (not_proper_bin_consts d hcb hca)
          exact ⟨q, by omega, free_binary_left hcb hf⟩
        · rcases Finset.mem_insert.mp hb1 with hbEq | hbU
          · exact (hab hbEq.symm).elim
          · obtain ⟨q, hq, hf⟩ := feasible_const tail i b (Finset.mem_insert_of_mem hbU) hcb
            exact ⟨q, by omega, free_binary_right hca hf⟩
      · rcases Finset.mem_insert.mp hb with rfl | hb1
        · obtain ⟨q, hq, hf⟩ := feasible_const tail i a (Finset.mem_insert_of_mem haU) hca
          exact ⟨q, by omega, free_binary_left hcb hf⟩
        · rcases Finset.mem_insert.mp hb1 with rfl | hbU
          · obtain ⟨q, hq, hf⟩ := feasible_const tail i a (Finset.mem_insert_of_mem haU) hca
            exact ⟨q, by omega, free_binary_right hcb hf⟩
          · obtain ⟨q, hq, hf⟩ := ih (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU)
            exact ⟨q + 1, by omega, pull_binary hf⟩


theorem prefixPull (gs : List Gate) (legal : ∀ g ∈ gs,
    g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (w : List Sig) (m t : Nat) (T : Finset Sig), Live m t T → (∀ a ∈ T, a ∈ execute gs w) →
      ∃ q u U, q ≤ m+gs.length ∧ Live q u U ∧ ∀ a ∈ U, a ∈ w := by
  induction gs with
  | nil => intro w m t T live sub; exact ⟨m,t,T,by simp,live,sub⟩
  | cons g gs ih =>
    intro w m t T live sub
    obtain ⟨q,u,U,hq,hl,hs⟩ := ih (fun a ha => legal a (List.mem_cons_of_mem _ ha))
      (w ++ [gv w g]) m t T live sub
    obtain ⟨q',u',U',hq',hl',hs'⟩ := pull_gate hl (gate_rep w g (legal _ (by simp))) hs
    exact ⟨q',u',U',by simp only [List.length_cons]; omega,hl',hs'⟩

def ins (code : Nat) : Gate := if code.testBit 9 then ⟨.not,[code &&& 15]⟩
  else ⟨if code.testBit 8 then .or else .and,[code &&& 15,(code >>> 4) &&& 15]⟩
def instructions : Nat → Nat → List Gate
  | 0,_ => []
  | n+1,w => ins w :: instructions n (w >>> 10)

theorem legalIns (code : Nat) : (ins code).op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
    (ins code).inputs.length ≤ 2 := by
  unfold ins; split
  · simp
  · split <;> simp
theorem legalProg (n code : Nat) : ∀ g ∈ instructions n code,
    g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction n generalizing code with
  | zero => simp [instructions]
  | succ n ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hh
    · exact legalIns _
    · exact ih _ g hh
theorem insLength (n code : Nat) : (instructions n code).length = n := by
  induction n generalizing code with
  | zero => rfl
  | succ n ih => simp only [instructions,List.length_cons,ih]

def properB (a : Sig) := a != zero && a != one
lemma properB_spec {a : Sig} : properB a = true ↔ proper a := by simp [properB,proper]

def shortTest (basis images : List Sig) (paid prog cnt a b source k bound : Nat) : Bool :=
  let w := execute (instructions paid prog) basis
  decide (cnt ≤ 2 ∧ paid+k ≤ bound+cnt) &&
    (cnt == 0 || (decide (a < images.length) && !properB (images.getD a zero))) &&
    (cnt ≤ 1 || (decide (b < images.length ∧ a ≠ b) && !properB (images.getD b zero))) &&
    images.all (fun sig => !properB sig || w.contains sig)

theorem shortSound (H : Hom) {basis images v : List Sig} {paid prog cnt a b source k bound : Nat}
    (hard : ∀ m ≤ bound, ∀ t (T : Finset Sig), Live m t T → T ⊆ basis.toFinset → False)
    (im : v.map H.fn = images) (nd : v.Nodup)
    (ok : shortTest basis images paid prog cnt a b source k bound = true) :
    ∀ m ≤ k, ∀ t, ¬ Live m t v.toFinset := by
  intro m hm t live
  have hh := ok
  simp only [shortTest,Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true,beq_iff_eq,
    Bool.not_eq_true',List.all_eq_true,List.contains_eq_mem] at hh
  obtain ⟨⟨⟨⟨cap,budget⟩,s1⟩,s2⟩,okall⟩ := hh
  have hlen : images.length = v.length := by rw [←im,List.length_map]
  have atI (j : Nat) (hj : j < images.length) :
      images.getD j zero = H.fn (v[j]'(by omega)) := by
    calc
      images.getD j zero = (v.map H.fn).getD j zero := congrArg (fun l : List Sig => l.getD j zero) im.symm
      _ = _ := by rw [List.getD_eq_getElem _ _ (by simp; omega),List.getElem_map]
  have co : ∃ q, q + cnt ≤ m ∧ Feasible H q v.toFinset := by
    interval_cases cnt
    · exact ⟨m,by omega,feasible_live live H⟩
    · rcases s1 with h | ⟨ha,hpa⟩
      · omega
      · have na : ¬proper (H.fn (v[a]'(by omega))) := by
          intro h
          have ht := properB_spec.mpr h
          rw [←atI a ha,hpa] at ht
          contradiction
        obtain ⟨q,hq,hs⟩ := feasible_const live H _ (List.mem_toFinset.mpr (List.getElem_mem ..)) na
        exact ⟨q,by omega,hs⟩
    · rcases s1 with h | ⟨ha,hpa⟩
      · omega
      · rcases s2 with h | ⟨⟨hb,hab⟩,hpb⟩
        · omega
        · have ca : ¬proper (H.fn (v[a]'(by omega))) := by
            intro h
            have ht := properB_spec.mpr h
            rw [←atI a ha,hpa] at ht
            contradiction
          have cb : ¬proper (H.fn (v[b]'(by omega))) := by
            intro h
            have ht := properB_spec.mpr h
            rw [←atI b hb,hpb] at ht
            contradiction
          have ne : (v[a]'(by omega)) ≠ (v[b]'(by omega)) := by
            intro e
            exact hab (nd.getElem_inj.mp e)
          exact feasible_two_consts live H _ _ (List.mem_toFinset.mpr (List.getElem_mem ..))
            (List.mem_toFinset.mpr (List.getElem_mem ..)) ne ca cb
  obtain ⟨q,hq,z,hz,t',T,lh,sub⟩ := co
  have mem (x : Sig) (hx : x ∈ T) : x ∈ execute (instructions paid prog) basis := by
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp (sub hx)
    have hmem : H.fn y ∈ images := im ▸ List.mem_map_of_mem (List.mem_toFinset.mp hy)
    rcases okall _ hmem with he | hb
    · have hp := properB_spec.mpr (live_proper lh _ hx)
      rw [he] at hp
      contradiction
    · exact hb
  obtain ⟨s,t'',U,hz',hl,subset⟩ := prefixPull _ (legalProg paid prog) basis z t' T lh mem
  rw [insLength] at hz'
  exact hard s (by omega) t'' U hl (fun x hx => List.mem_toFinset.mpr (subset _ hx))

end MinorCore2153

namespace MinorAdapter2153
open Search2153 Projection2153 ThetaSym2153 OrbitTransport2153

/-- Select the original position before projecting; distinct original wires can have
equal projected signatures. The incoming list is already in original position order. -/
def projectedBase (images : List Sig) (code : Nat) : List Sig :=
  let j := code / 3
  let form := code % 3
  (if form = 0 then images.eraseIdx j else images) ++
    (if form = 1 then [] else [neg (images.getD j zero)])

lemma eraseAt (w : List Sig) (n : Nat) (nd : w.Nodup) (hz : zero ∉ w) :
    w.erase (w.getD n zero) = w.eraseIdx n := by
  by_cases hn : n < w.length
  · rw [List.getD_eq_getElem _ _ hn,nd.erase_getElem n hn]
  · rw [List.getD_eq_default _ _ (by omega),List.erase_of_not_mem hz,List.eraseIdx_of_length_le (by omega)]

theorem project_base (H : Hom) {w images : List Sig} (hw : w.map H.fn = images)
    (nd : w.Nodup) (hz : zero ∉ w) (code : Nat) :
    projectedBase images code = (Cache2153.base w code).map H.fn := by
  subst images
  simp only [projectedBase,Cache2153.base,List.map_append,map_getD,List.eraseIdx_map,
    eraseAt w _ nd hz]
  split <;> split <;> simp only [List.map_nil,List.map_cons,H.unary]

def fullHom (i : Fin 4) : Hom :=
  OrbitCache2153.reindexHom (index (posKey i)) (index (negKey i))

def fullOrder (i : Fin 4) : List Sig :=
  let r := thetaFlat
  ![[zero,r.getD 3 zero,r.getD 0 zero,r.getD 2 zero,r.getD 6 zero,r.getD 4 zero,r.getD 5 zero,r.getD 1 zero],
    [r.getD 2 zero,r.getD 0 zero,r.getD 3 zero,zero,r.getD 1 zero,r.getD 5 zero,r.getD 4 zero,r.getD 6 zero],
    [r.getD 4 zero,r.getD 3 zero,r.getD 0 zero,r.getD 5 zero,r.getD 1 zero,zero,r.getD 2 zero,r.getD 6 zero],
    [r.getD 3 zero,r.getD 0 zero,r.getD 5 zero,r.getD 6 zero,r.getD 4 zero,r.getD 2 zero,zero,r.getD 1 zero]] i

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem full_map : ∀ i, raw.map (fullHom i).fn = fullOrder i := by decide +kernel

def sixImages (i : Fin 5) (d c : Nat) :=
  Cache2153.replay (projectedBase (SixMinor2153.targetOrder i)) d c

def sevenImages (i : Fin 4) (d c : Nat) :=
  Cache2153.replay (projectedBase (fullOrder i)) d c

theorem six_replay (i : Fin 5) (d c : Nat) :
    (Cache2153.replay (OrbitCache2153.basis 0) d c).map (SixMinor2153.hom i).fn = sixImages i d c := by
  exact (replay_comm (SixMinor2153.hom i) _ _
    (project_base _ (SixMinor2153.mapRaw i) (by decide +kernel) (by decide +kernel)) d c).symm

theorem seven_replay (g : Nat) (hg : g ≠ 0) (i : Fin 4) (d c : Nat) :
    (Cache2153.replay (OrbitCache2153.basis g) d c).map (fullHom i).fn = sevenImages i d c := by
  have basisEq : OrbitCache2153.basis g = Cache2153.base raw := by
    simp [OrbitCache2153.basis,OrbitCache2153.rawBasis,hg]
  rw [basisEq]
  exact (replay_comm (fullHom i) _ _ (project_base _ (full_map i)
    raw_nd (by decide +kernel)) d c).symm

def sevenBasis (j : Fin 7) := thetaFlat ++ [neg (thetaFlat.getD j.val zero)]

theorem hard7 (n : ThetaNumeric) (j : Fin 7) (m : Nat) (hm : m ≤ 10) (t : Nat)
    (T : Finset Sig) (hl : Live m t T) (sub : T ⊆ (sevenBasis j).toFinset) : False := by
  apply n j m t T hm hl
  rw [flat_eq]
  intro x hx
  have mem : x ∈ thetaFlat ++ [neg (thetaFlat.getD j.val zero)] := List.mem_toFinset.mp (sub hx)
  rcases List.mem_append.mp mem with h | h
  · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr h)
  · exact Finset.mem_insert.mpr (Or.inl (List.mem_singleton.mp h))

def budget (group depth : Nat) := (if group = 0 then 10 else 12) - depth
def cut (h : Nat) := h &&& 7
def source (h : Nat) := (h >>> 3) &&& 7
def test (basis images : List Sig) (h k limit : Nat) :=
  MinorCore2153.shortTest basis images ((h >>> 6) &&& 7) (h >>> 19) ((h >>> 9) &&& 3)
    ((h >>> 11) &&& 15) ((h >>> 15) &&& 15) 0 k limit

def short (group depth trace hint : Nat) : Bool :=
  let h := hint - 1
  if hint = 0 then false
  else if group = 0 then
    if hc : cut h < 5 then
      if hs : source h < 6 then
        let i : Fin 5 := ⟨cut h,hc⟩
        let j : Fin 6 := ⟨source h,hs⟩
        test (SixMinor2153.basis (i == 0) j) (sixImages i depth trace) h (budget group depth) 7
      else false
    else false
  else if group ≤ 2 then
    if hc : cut h < 4 then
      if hs : source h < 7 then
        let i : Fin 4 := ⟨cut h,hc⟩
        let j : Fin 7 := ⟨source h,hs⟩
        test (sevenBasis j) (sevenImages i depth trace) h (budget group depth) 10
      else false
    else false
  else false

def Prior (group : Nat) : Prop := if group = 0 then SixMinor2153.SixNumeric else ThetaNumeric

theorem sound (group depth trace hint t : Nat) (prior : Prior group)
    (nd : (Cache2153.replay (OrbitCache2153.basis group) depth trace).Nodup)
    (checked : short group depth trace hint = true) :
    Marked2153.Impossible (OrbitCache2153.marks group) (budget group depth) t
      (Cache2153.replay (OrbitCache2153.basis group) depth trace) := by
  intro m hm live
  unfold short at checked
  dsimp only at checked
  split at checked
  · contradiction
  split at checked
  · rename_i hgroup
    subst group
    split at checked
    · rename_i hc
      split at checked
      · rename_i hs
        let i : Fin 5 := ⟨cut (hint-1),hc⟩
        let j : Fin 6 := ⟨source (hint-1),hs⟩
        have hard := (show SixMinor2153.SixNumeric from prior) (i==0) j
        exact MinorCore2153.shortSound (SixMinor2153.hom i)
          (fun n hn u U l h => hard n u U hn l h) (six_replay i depth trace) nd checked m hm t live.live
      · contradiction
    · contradiction
  · rename_i hgroup
    split at checked
    · split at checked
      · rename_i hc
        split at checked
        · rename_i hs
          let i : Fin 4 := ⟨cut (hint-1),hc⟩
          let j : Fin 7 := ⟨source (hint-1),hs⟩
          have h7 : ThetaNumeric := by simpa [Prior,hgroup] using prior
          exact MinorCore2153.shortSound (fullHom i) (hard7 h7 j) (seven_replay group hgroup i depth trace)
            nd checked m hm t live.live
        · contradiction
      · contradiction
    · contradiction

end MinorAdapter2153

namespace HubSeven2153

open Search2153 Projection2153 OrbitTransport2153

def hubRaw : List Sig := [(0x1c3404834182442a02c81357d8b1103398238a00b2cc16624b225912c3fc3fc,0xce57ffc5e6a9ab144b1e3cc751fa57017fc1377bb2cc16624b225912c15c15c),(0x8aedac8ac8a215638712e9a2281307e06280c434000f47838c047e23fccfccf,0xb0b0171c628c000694c503d36baaa589eb532012000547838c040a2054c54c5),(0x44cf900e63d742113628f6412c0a8e2008005028c0f098040ff861c30f0ff0f,0x4b4d20e28912dce8613ad02894455806002c5e6cc0509804017861c30b0ab0a),(0x250254a1800ced808849a537d5c0700f9f5f2aca0300e007f03f81fc0ff0ff0,0x21a8003808064468b0a18130a604888e801e40040000e004900c80640ea0ea0),(0xb25003791c28200c409700984224001000a12101fc00fff8003ffe000fff000,0x6c64c5fee916d4f8f1bed56c67a7d18e0b3a7e7dd400faa8003ffe000fff000),(0x6a223b340e0d386279110c80051141c460d4a49cffff0000003ffffff000000,0xe47e8c395713b914a1a7c0c1051427014a09fe9fffa00000033759ba000000),(0xd1104b54b77183dcf0a61268026ca91847281143ffffffffffc000000000000,0x90121a0116e923070e402a830818267174c181822baf05536e8000000000000)]

def cutAt : Fin 4 → Fin 8 := ![1,2,4,7]

def pKey : Fin 4 → Nat := ![0xdded9cda733c93c4265473da26288b2626c4718be838f6f638d89cf654ed2858c928b2d893f6edb428b2ddb29c8b28edc43c9c718538b2c9c4e873b2dad87326c9f6eded85262871da35b2933cd8dd9c3f263fb4718bb43893b4c958d835383c35582635288bd88535c4da73b2d82673b285c435b22626e8717128dac485353535e871353cc4c9c49385da85c485355873269cb2357135d885c426718b71c4d8fbfaf8f8f6f6f3f2efefededeaeae8e8e4e3e2e1e0dfdfdddddadad8d8cbcac9c9c5c4c4b8b7b4b4b2b2a1a0a09e9d9c9c9a99959593938c8b8b8986858578777373717163635f5f5c5c5858565654543f3f3c3c3838353528282626,0x8858f68b51b490c40b65518b0b1ada0b0bc44cda5ab69c9cb685f69c65581aedc71a3585909c583c1a358835f6da1a58c4b4f64cd8b635c7c45a51358b85510bc79c5858d80b1a4c8bb23590b48588f6a30ba33c4cda3cb6903cc7ed85b2b6b4b2ed0bb21ada85d8b2c48b5135850b5135d8c4b2350b0b5a4c4c1a8bc4d8b2b2b25a4cb2b4c4c7c490d88bd8c4d8b2ed510bf635b24cb285d8c40b4cda4cc485a19da0a09c9ce4e25f5f585861615a5af3f4f28c868e8e88888b8b8585c5ccc7c7cbc4c43d363c3c3535fbf8f8f9faf6f6989197979090e1dadadbe0d8d8524d51514c4ce6e6efeff1f1eded76766565a3a3b4b4b6b6b2b21a1a0b0b,0xe8549073da1af617b2edda73b2b451b2b217d851dda39393a3719093ed54b465a5b42671f6935428b426e8269051b454171a90d84ca326a517ddda267371dab2a59354544cb2b4d8730b26f61a71e890b6b2b628d85128a3f628a565710ba31a0b65b20bb451714c0b1773da2671b2da264c170b26b2b2ddd8d8b473174c0b0b0bddd80b1a17a517f64c734c174c0b65dab290260bd80b714c17b2d851d817719a99959593934f4e56565454dfdfdddd79eb747877eaeae8e87373717129a6a5a5181717b8b728282626989797f9919090fbfaf8f8f6f6525151db4d4c4ce1e0dadad8d8f1f17676e6e66565efefededb6b61a1aa3a30b0bb4b4b2b2,0x5a6593518b289c1735588b51353c733535178573883f90903f4c939058653c543a3c0b4c9c90651a3c0b5a0b93733c6517289385713f0b3a17888b0b514c8b353a90656571353c8551260b9c284c5a933835381a85731a3f9c1a3a544c263f28265435263c734c712617518b0b4c358b0b7117260b35358885853c51177126262688852628173a179c715171177126548b35930b2685264c711735857385174c9891979790907974767665658e8e88884f5d4e524d61615a5a51514c4c18403a3a2917173d361a1a0b0b9a95959e999393a19da0a09c9c787373897771718c868b8b85855c5c5656636354545f5f5858383828283f3f26263c3c3535]

def nKey : Fin 4 → Nat := ![0xe9e1e3e7fbf7eecbc8fbe3e9cbfbf8eef7f7eee9f8dee9defbfbe4e3e3defaf8fbdedef6e4f8e9fae9f6f8fae9e3e4f8e1e4f8faeee4f8f8fae4e4f7e4e9e7f6e3fbe4e3f8e7f8e1e3e7e4fbfbdefbc8e4faf8fbf8f7e7e3e9dee4c8faf7e9e9cbdee3eee7e4e3dedeeedef8e9e4defae3fbe7e1cbe9f8dee3f6f6f6e3e4e4e9c8e9e9f8def8dedef8e9fae3e4cbe3e9f6e4defbfafbfbf8f6fbfbdefbe4e9f7fbfaf8f7f6f5f8f6f8eef6ecf8e9f6e7e4e3e2e1e0e9dee7dcdad9d5cfcbe9e7c8dad5bae9e7dab3d5a8fbfae4e3f7f5e2fbfaf7def5dceeeccbc88680baeeec86728067e4e3e4e1e3dee2d9e1dee0dccbc8cbb3c872ba2bb372a867,0xceeef9c6fbfae1dadbfbf9cedafbe4e1fafae1cee4f0cef0fbfbf8f9f9f0f7e4fbf0f0e2f8e4cef7cee2e4f7cef9f8e4eef8e4f7e1f8e4e4f7f8f8faf8cec6e2f9fbf8f9e4c6e4eef9c6f8fbfbf0fbdbf8f7e4fbe4fac6f9cef0f8dbf7facecedaf0f9e1c6f8f9f0f0e1f0e4cef8f0f7f9fbc6eedacee4f0f9e2e2e2f9f8f8cedbcecee4f0e4f0f0e4cef7f9f8daf9cee2f8f0fbf7fbfbe4e2fbfbf0fbf8cefafbf7e4fae2f5e4e2e4e1e2d9e4cee2c6f8f9f6ee86cef0c68fcbecba80dacec6dbcbbad5cec6cbb3ba2bfbf7f8f9faf5f6fbf7faf0f58fe1d9dadbe0cfd5e1d9e0b5cf42f8f9f8eef9f0f6eceef0868fdadbdab3dbb5d5a8b3b52b42,0xe9eef9e7fbf7e1b5dbfbf9e9b5fbdee1f7f7e1e9def8e9f8fbfbf0f9f9f8fadefbf8f8dcf0dee9fae9dcdefae9f9f0deeef0defae1f0dedefaf0f0f7f0e9e7dcf9fbf0f9dee7deeef9e7f0fbfbf8fbdbf0fadefbdef7e7f9e9f8f0dbfaf7e9e9b5f8f9e1e7f0f9f8f8e1f8dee9f0f8faf9fbe7eeb5e9def8f9dcdcdcf9f0f0e9dbe9e9def8def8f8dee9faf9f0b5f9e9dcf0f8fbfafbfbdedcfbfbf8fbf0e9f7fbfadef7dcf5dedcdee1dce0dee9dce7f0f98feeece9f8e7f672866780b5e9e7db726742e9e772b367a8fbfaf0f9f7f58ffbfaf7f8f5f6e1e0b5dbd9cf42e1e0d9dacfd5f0f9f0eef9f88f86eef8ecf6b5dbb5b3dbda422bb3daa8d5,0xcee1e3c6fbfaee72c8fbe3ce72fbf0eefafaeecef0e4cee4fbfbdee3e3e4f7f0fbe4e48fdef0cef7ce8ff0f7cee3def0e1def0f7eedef0f0f7dedefadecec68fe3fbdee3f0c6f0e1e3c6defbfbe4fbc8def7f0fbf0fac6e3cee4dec8f7facece72e4e3eec6dee3e4e4eee4f0cedee4f7e3fbc6e172cef0e4e38f8f8fe3dedecec8cecef0e4f0e4e4f0cef7e3de72e3ce8fdee4fbf7fbfbf08ffbfbe4fbdecefafbf7f0fa8ff5f08ff0ee8f86f0ce8fc6dee3dce1d9cee4c6e2b5e042cf72cec6c8b54267cec6b5b3422bfbf7dee3faf5dcfbf7fae4f5e2ee8672c8ec8067ee86eccb80badee3dee1e3e4dce0e1e4d9e272c872b3c8cb67a8b3cb2bba]

def hom (i : Fin 4) : Hom := OrbitCache2153.reindexHom (index (pKey i)) (index (nKey i))

def targetOrder (i : Fin 4) : List Sig :=
  (![[hubRaw.getD 0 zero,zero,hubRaw.getD 1 zero,hubRaw.getD 2 zero,hubRaw.getD 3 zero,hubRaw.getD 4 zero,hubRaw.getD 5 zero,hubRaw.getD 6 zero],[hubRaw.getD 2 zero,hubRaw.getD 1 zero,zero,hubRaw.getD 0 zero,hubRaw.getD 6 zero,hubRaw.getD 5 zero,hubRaw.getD 4 zero,hubRaw.getD 3 zero],[hubRaw.getD 0 zero,hubRaw.getD 3 zero,hubRaw.getD 6 zero,hubRaw.getD 2 zero,zero,hubRaw.getD 5 zero,hubRaw.getD 4 zero,hubRaw.getD 1 zero],[hubRaw.getD 2 zero,hubRaw.getD 6 zero,hubRaw.getD 3 zero,hubRaw.getD 0 zero,hubRaw.getD 1 zero,hubRaw.getD 4 zero,hubRaw.getD 5 zero,zero]] : Fin 4 → List Sig) i

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem mapRaw : ∀ i : Fin 4, raw.map (hom i).fn = targetOrder i := by decide +kernel

def basis (j : Fin 7) := hubRaw ++ [neg (hubRaw.getD j.val zero)]

def check7 (j : Fin 7) : Bool :=
  (basis j).sublists.all fun w => (List.range 9).all fun t =>
    !(decide (w.length + t ≤ 9) && unionSep (decide (0<t)) w == top) ||
      !(Marked2153.search [] 8 t w)

set_option maxHeartbeats 0 in
theorem noLiveOfCheck (j : Fin 7) (checked : check7 j = true)
    (unique : (basis j).Nodup) {m t : Nat} {S : Finset Sig}
    (hm : m ≤ 8) (live : Live m t S) (hs : S ⊆ (basis j).toFinset) : False := by
  let w := (basis j).filter (fun a => decide (a ∈ S))
  have sub : w ∈ (basis j).sublists := List.mem_sublists.mpr (List.filter_sublist ..)
  have he : w.toFinset = S := by
    ext a
    simp only [w,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact and_iff_right_of_imp (fun h => List.mem_toFinset.mp (hs h))
  have nd : w.Nodup := unique.filter _
  obtain ⟨le,len⟩ := live_size live
  rw [← he,List.toFinset_card_of_nodup nd] at len
  have ht : t ∈ List.range 9 := List.mem_range.mpr (by omega)
  have yes := List.all_eq_true.mp (List.all_eq_true.mp checked w sub) t ht
  have cover := live_cover live he
  have good : w.length + t ≤ 9 := by omega
  have last := Marked2153.search_complete (Marked2153.ignoreNegative (signedFree live)) 8 hm w nd he
  simp only [decide_eq_true good,cover,beq_self_eq_true,Bool.true_and,Bool.not_true,Bool.false_or,last] at yes
  exact Bool.false_ne_true yes



def HubNumeric := ∀ (j : Fin 7) (m t : Nat) (S : Finset Sig), m ≤ 8 → Live m t S → S ⊆ (basis j).toFinset → False

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checked0 : check7 0 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checked1 : check7 1 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checked2 : check7 2 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checked3 : check7 3 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checked4 : check7 4 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checked5 : check7 5 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checked6 : check7 6 := by decide +kernel

set_option maxHeartbeats 0 in
theorem hubNumeric : HubNumeric := by
  intro j m t S hm live sub
  apply noLiveOfCheck j _ _ hm live sub
  · fin_cases j
    · exact checked0
    · exact checked1
    · exact checked2
    · exact checked3
    · exact checked4
    · exact checked5
    · exact checked6
  · have h : ∀ j : Fin 7, (basis j).Nodup := by decide +kernel
    exact h j
end HubSeven2153

namespace MinorHubAdapter2153
open Search2153 Projection2153 OrbitTransport2153

abbrev Prior := MinorAdapter2153.Prior

def images (i : Fin 4) (d c : Nat) :=
  Cache2153.replay (MinorAdapter2153.projectedBase (HubSeven2153.targetOrder i)) d c

theorem replayEq (group : Nat) (hg : group ≠ 0) (i : Fin 4) (d c : Nat) :
    (Cache2153.replay (OrbitCache2153.basis group) d c).map (HubSeven2153.hom i).fn = images i d c := by
  have be : OrbitCache2153.basis group = Cache2153.base raw := by
    funext code
    simp [OrbitCache2153.basis,OrbitCache2153.rawBasis,hg]
  rw [be]
  exact (replay_comm (HubSeven2153.hom i) _ _
    (MinorAdapter2153.project_base _ (HubSeven2153.mapRaw i) raw_nd (by decide +kernel)) d c).symm

def short (group depth trace hint : Nat) : Bool :=
  let h := hint-1
  if group ≠ 0 ∧ group ≤ 2 ∧ 4 ≤ MinorAdapter2153.cut h then
    let i := Fin.ofNat 4 (MinorAdapter2153.cut h - 4)
    let j := Fin.ofNat 7 (MinorAdapter2153.source h)
    MinorAdapter2153.test (HubSeven2153.basis j) (images i depth trace) h (MinorAdapter2153.budget group depth) 8
  else MinorAdapter2153.short group depth trace hint

theorem sound (group depth trace hint t : Nat) (prior : Prior group)
    (nd : (Cache2153.replay (OrbitCache2153.basis group) depth trace).Nodup)
    (checked : short group depth trace hint = true) :
    Marked2153.Impossible (OrbitCache2153.marks group) (MinorAdapter2153.budget group depth) t
      (Cache2153.replay (OrbitCache2153.basis group) depth trace) := by
  unfold short at checked
  dsimp only at checked
  split at checked
  · rename_i h
    let i := Fin.ofNat 4 (MinorAdapter2153.cut (hint-1)-4)
    let j := Fin.ofNat 7 (MinorAdapter2153.source (hint-1))
    intro m hm live
    exact MinorCore2153.shortSound (HubSeven2153.hom i)
      (fun s hs u U hl sub => HubSeven2153.hubNumeric j s u U hs hl sub)
      (replayEq group h.1 i depth trace) nd checked m hm t live.live
  · exact MinorAdapter2153.sound group depth trace hint t prior nd checked

end MinorHubAdapter2153

open Search2153 Cache2153
namespace Num70

def basis := Cache2153.base ThetaSym2153.thetaFlat
def marks : List Sig := []

def rot := OrbitCache2153.rotBase 0

def o5 (i : Nat) := field (fun b => if b<1 then (0xcdcbc6c2bebdbcbab5b0aca39f9b9795908b8982807e7c79777672706d666362605f5c5b57554e4c47464441403d3a3935342f2d2a26201c17130e0b07050300) else (0xce)) 8 i

def f5 (i : Nat) := field (fun b => if b<2 then (if b<1 then (0x830af208b87b2873a1e060c1cb3705440c7224c030089820abc207160e071b044e00309b10a531462c5d03188d1818282d8c7308d590a6ca8bc587bb7314d238dd18d187804b60964f240e012ed42cc5287860a44be18d801a9b1f1814c62861b893504fa0918515022518b4210d5400d425eec30d9880bf) else (0x512e1c260400e856c1ad0153c6998e29002a65901a909422c3ef5b43ae8538045854113be024542803cf4c1e0e10161819c8707950d14e8649da048b001f0811580222b77049eb4ac292bb192c962d118bf027b0c8a346410b8411160a1059d090b8b1512016052a9e041c4819045968b5b5aa8040851d98)) else (if b<3 then (0x59643aa8552858757660cb90c51bb4074a0e0c054430c7110e0109810f11571840488048d0b870e9c653059e8e3730640c54086ac02566814b06892e080092151c79f8f2318d619385192c2158de1d28233b03e0c46744c60509881eea3d31e1103210caa1cfc8338a6610a22d0841d8d275c0c063031407) else (0x1402ae01355cec653461b141e062c35e8330092a3e52f61453f8f))) 15 i

def r5D1 (i : Nat) := field (fun b => 0xb690ada40b6506d740b552ad540b5196d067b418ec76ab1d96c763b1bbe946ba51aa9465a4fae93e8a4f9693e3a4f8a91eba479a91e3a478a90e1a3ba28ee3a2faa8be7a2f96164785906106e841aa0bea809bc9bc126b0896ca25b14946f251b8388a0e22038850e21038830e2043880) 18 i
def r5V (i : Nat) := field (fun b => if b<1 then (0x2402e300e07d4a0390607d4a0393e09d04ab00807849a78060824a84d3c07555036420914881a2a00dcb2241209158a201a09152a14260755500e1e08b4a2ac3608b4484405018c68292a0210780a3e08f91a3c4a05612ea80e0684f8453c001c307e1e08b448461e00aca8250408749a181a0684681a1a04f49a102a07d4a0061e0684da242801c0ba24220914fa78360be4682d1807349a181a0914fa94000684da24220340480a0e08f91a3c2608b448450c0940b00e1207d4a0562e045430361e0af448a816065444544405d4ba303e014cf8253c0b75507e4206848aa80603f1841c0404b5507e120940b07e4200ec380a2a03a160192a08b448393e0784a8453c04b550212a04f49a103e0685584504014d58020e0784a8451208f91a3c3605605e500e08b44844108b3430562e05603e182a004c38020e0b7550361e0) else (if b<2 then (0xbe5582d280584f81a1a02d5500e120940b0361e0635501e2e08b4881a0e0ba4380a3e02d5507e420b343056120785580a1a08b4881a2a07d4a04d280755501e420655507e4204b5507e1e0655501e1e0560cea80e0a51841c3c0654443444065550362e0c25580a0e09904ab01c0210ca14160940b07e1e06d49a103e02d550561e040158020e0b34307e4202d5507e1e0210ca142208249aa8060325580a0e0a304ab02c0af448a8220684681a3e0ba4380a1a018c68291a0b7550361207d5227c120b34307e1e0524a83d28075550562e07d4a00e4205605e302a04b550361e08758a2408001c307e420655500e1e07544cb8400784a8692a0b75501e2e00ec380a1a04b550561e0655507e2e004d58211a09158a200e0c555029060b3430361e05606c3d0c0584f84d04013d50211a09152a14280914881a3e04b5507e420) else (0x2a03c253c0684f8492a004d58213e0755501e1e02d550361e0210780a1a04b550211a0b75507e1e0685580a1a0c5550291a08249a14400684f8493e0ab1841c3c0))) 40 i
def r5 (i : Nat) :=
  let x := r5V i
  (x &&& 127) ||| (((x >>> 7) &&& 134217727) <<< 7) ||| ((r5D1 ((x >>> 34) &&& 63)) <<< 34)

def hit5 (t : Nat) (v : List Sig) := OrbitLookup2153.orbitHit 4 141 206 64 o5 f5 r5 rot 5 t v

def ok5 (i : Nat) :=
  let t := r5 i &&& 7
  let v := replay basis 5 (r5 i >>> 3)
  decide v.Nodup && !jump marks 3 (fun _ _ => true) 2 t v

def o2H (i : Nat) := field (fun b => if b<1 then (0x663d9366381880603979f5cf16d859b160756a553d535146b4fdd38c4c592c0494d1dd45910fb42350353f58f643bdce8638b0dc03574cf3327cc332eecb572ba0a7127fc99324d48cc21a48081e7c7281b1865217e059414dc4da11a04050e843390b2c26a082c1ab05000e001a0000) else (if b<2 then (0xcdeb319cb0b25bc7eb19dc4a70b2c16eff7be66f2ebadee64b7c2d8cb4b6cb4b0eabcaad9eaefaa2ea26a70296fa3de879a03a7aa9d3e6e3999e5fd965a52e932246990323a48cea2ce899e1ec85ce11b82de0497fa5f907ce1ed87961df77629d2a72e5c516fd9b7f6c9dac0697d9fe) else (0x33d7))) 14 i
def o2L (i : Nat) := field (fun b => if b<32 then (if b<16 then (if b<8 then (if b<4 then (if b<2 then (if b<1 then (0xaabbaeb6dbafbeeaeaa279a38e392385f71d7de6da6da6da5d76145545175d65d769c7de85f6dd6d859555861865b69a) else (0x7df8628a28e18df7e19239249648a081e7a179e75e61965a5535d44d24903d238e30d3d35565da6d865a61865a69969a)) else (if b<3 then (0x4514534d455340e34e2cd3d35155134d45175d965961861a4d455761861759561855761a71c79d75d7df7dd75d69b69a) else (0x79c75d79c75c7df8629648a38e181e71b6db69c6da65969a5965da69b71b69b7a07df8218628218a18a086281f69b75a))) else (if b<6 then (if b<5 then (0x5955944945555d64d55134d75975d96575595d651655765a71e75d71965b65b6dd79d7e08617dd6dd79d7595d755765a) else (0x8e38df7e075e7dc75c65851769c6185966165d74d661965a49349351669a6995da71e79b7608648e38228a071c75a65a)) else (if b<7 then (0x4d251451348e38f30d3d14103d24134d44d661b71b6996da49249554e40e3904104504924914d75925155585996da65a) else (0x34c34e34c30a2cc34d3d249459555759869b69c71b6da69a6186db6da71f8217a08628a18de71d71a75c69971f6de75a)))) else (if b<12 then (if b<10 then (if b<9 then (0x5985d959769b6565d865b6965d965c75c65a6dc6db69b65aaa9aa78e38e39a58e289e79f71b65d7dc71f7dd65765b69a) else (0x71e81e6dc65b69a6dc79c6db6db69a69a72079e79e7dd6daa68aa9aa79e9aebb2cae89228a18238e17e081c6da69b75a)) else (if b<11 then (0x5566175135986da6d761861865a6dc6575da69869b69a69a4924915155945145155144945575d95d65da75d75e6db65a) else (0x45241044f40f38e41141038f4914d349449559659869a65a71d71d7a085f79d79f79f79d75e7e081b6dc75c69b75c69a))) else (if b<14 then (if b<13 then (0x9659659259a59617df85e75f8618a48e49a492495f79c69a7dd71b75d79c6da6196da5d961761751449459859761761a) else (0x7df7dd75a5d865b75f81e7e08607de6976175965545996daae89e8a28aeaaaaa269a28618228a26d961969b55355765a)) else (if b<15 then (0xa6592396295f7e07e18a39679a69a685f8a485f79f71b61a55459659555449041249249351559865861759761965869a) else (0x1c724824b2081c71ca2cd2ca2cb3514d349349351559765a8219268e18e29249249259659648e48e49248a27e179c6da))))) else (if b<24 then (if b<20 then (if b<18 then (if b<17 then (0x5544d555565a65b7a089e6da69769b5d63d24d45da6175da75d7df81f8a48a18629218a39668e08608628628e17de71a) else (0x30e38e3ce4124d14945165d55964d351661a6d765b71c69a82086286279d6195d76595d861a7207df6db75e75d6dd79a)) else (if b<19 then (0x85b71b71b75d6dc75f7da61955459861a61961865d75861a8e69a69639258a08a59a69259628a18e39228a28e385d69a) else (0x4515145965914104924d24534914534d459769b71e69965a9239628e28a285f82182076179e79e79e8218e382275b5da))) else (if b<22 then (if b<21 then (0x85e7e07608e07e081f71c71c71d75f8a28628a385c75b6da2cd45045459965a6de79d71e6586dd79c71e6185d659661a) else (0xaedb2fc2baebaecaeaa269648e39289648df7e071e75d6da75c6dd71c6585974d65d759655045140f34e4114925555da)) else (if b<23 then (0x7df8628a26d759859959765a65b6555da6195986986586daaab9e59e6aaaaa99a89e89659a489f79b6dc6d75d971a6da) else (0x924924964923926968a259249a58a49268a49627de69a65a2092cd40c3ce34c30d4103d041039045349149349555869a)))) else (if b<28 then (if b<26 then (if b<25 then (0x9639638628e595f71c71d7de6dd7df75d79e7de71d6dc65a81d7a08608a49a79a49a59268a28618a182281f75869b6da) else (0x71d79f8208618228a486082085e79f79e79d61965b71a69a69c7de71c8218e27e28a48e389e7de7dc71e75c79b6db6da)) else (if b<27 then (0x48f3cf34f4935145166175965d865b7185d96d969c6da69a79d71c71c6d96585d75d761965861a69a69a61965a61961a) else (0x79f7a085e79c7a08608a58217e18649649228e08a175f75a55355559765865869c79d7608a179e71c79d75c6dc69865a))) else (if b<30 then (if b<29 then (0x5d971c65b7a17dc71d6d86185d85965945565985965d861a5d765a71a69d65969c75a6db6d969c71c76079c79d6db71a) else (0x9619259a8aeba6ba6bae99e686282285c71e75b69b75c6da9249649659a59a49249a79ebaea9e896489e79b71d7dc69a)) else (if b<31 then (0x28b34e3904d35145565965d759561a69b61b71e79f75c75a4d44935175d75965db6da65c71e75b79a76079e75d75c69a) else (0x71b75c79e71c7dd75f85e7607de7e079e7df79b65b69b75a34f38d3cf3d04904125566185d86dc71a6586585575d965a)))))) else (if b<48 then (if b<40 then (if b<36 then (if b<34 then (if b<33 then (0x5514534d55d55935175555564d24d14934955565da6dd79a41048f2cb38a34e3d34934d55556186596dd71d71e71a6da) else (0x34e44e2c828c2ce3914504d55986195d561a71a69b71b65a6996196125154d555861b71d79d69b61965b69b61b69d69a)) else (if b<35 then (0x4113ce3ce4524524114cf39040f4124d459969b61b75c75aaeaa6aaa79e79217e281f82085e79f7df8628e486292075a) else (0x8a27df7596596d869b6da7186dc6d961769c71a69a71b6da65765b6165d86595d96d865a6596175d85d95d861755661a))) else (if b<38 then (if b<37 then (0x85d7de75851344f3914924103cd34b30d41249251655761a4d44945d75945944d54903d14d44d455769c59865965b61a) else (0xdb1cf0c32cafb6cb2ca678a38a28a39628a282181e6da69a55665b75f7e181d7195d861b6dd7e285f79d79e71d6575da)) else (if b<39 then (0x2ca2c924c30a1c518820720920b28928b2cf35049459561a5145535965d961a75f7df7e385e79b71c71b71b5d559761a) else (0x5965d44d551559769a65969e6d961a71a69b71a5d961a6da38e3cf4125545555996da69c69969a65a61b71b65b69869a)))) else (if b<44 then (if b<42 then (if b<41 then (0x61869761761761761861869d75a65b6996df7e175e71d71a8e08a38628e69e79a796482281d75f7e286281f79d71d79a) else (0xa6bb2aa69a259e48e07196196db75e71d6da65b61969a6da34d30c34f38c3d14d665b71e79d71c71a6dc79d75d65869a)) else (if b<43 then (0x6de79e6d86da75c79e71e8207a07df81e75d75d7e07db75abeebf0c2fbf1bedb2eb6baaaaaca298e27df82081d75969a) else (0x75e7db69a5d55985d865971f71b69b6db71b61965c6da6da71d71965a71a6dc69a69a61865969b71b71869b75b65865a))) else (if b<46 then (if b<45 then (0x40b3cf4104d45565d861a71c6da71f7de69969a71b6d861a6dc71c71c71a65869b69755861851759651765b65861761a) else (0x69d6db6dc6d66196975975d555659665b6df71c79f75c61a51551351249355659665a6db75d7a085e71e79b69c75a6da)) else (if b<47 then (0x65b75e7de75f8208e48e18a49a79658a279f7dd81c65a65a6975d55564534d34935514954944d55165165d961759661a) else (0xb6dbacaa99e89e692385e79d7e06d961969e7db6dd75c75a71c81f79e75c69c7df7a18a489e6db65b71d75b6da6d971a))))) else (if b<56 then (if b<52 then (if b<50 then (if b<49 then (0x38f4114514925134d55514124d23d14514d665c5d96dd79a71a61a71e6dc79e7607a089d6dc71d6dc6dc71b65a65965a) else (0x69a65a6195d76185da61b6dd75c79f75b6de7e17dd7e079a61865c6db69865c7e07e08227df7a07dd71c75961865a69a)) else (if b<51 then (0xb2caecaedb6c9658218a181e6dc7a179d6da69a71e75d71ac6ca6ab6fbabb6aaa381e79f82181d75b6da69869b61965a) else (0x6596586166175975d96dd69a6db61a6db71c79b65c75b6da18620a24a2cc3d14955955965134945556144945d75d865a))) else (if b<54 then (if b<53 then (0x55655241140e41049459661a55561651455869761865861a61861a6db79f71a69c71b61969b6db75d71d7a07df8207da) else (0x5175965d86da6596dd6db6db69a6dc75f79e7de71e7df71ab70c2ec30b6aa67968a648608a48a38a38e39638df71c69a)) else (if b<55 then (0xb6fb6dc2dc31cb1cb5c30b2db268e185f7e185f7df81c69a8608dd75975d71865969b65a6dc65c75c6da71c79c75b6da) else (0x4925575d45975544d65524545144924113d151651655665ab2bba99a59638a28207de7de76081d71c6de79d71a69b69a)))) else (if b<60 then (if b<58 then (if b<57 then (0x9228a279b6d95965985d961b6d96db65b7a085d79e6db6da65a6585d55965975d865a69d65b7196db71e7a179c69b61a) else (0xaeaa27a259258a186181c65c71b65a69b65b6dc65b65a6da0c40c00000c61c314614720a34e4504924934d555865961a)) else (if b<59 then (0x4535125155513ce4124935176165db71969d69a61a69b65a79b71b79d6db6175975d65986596164d451865455761969a) else (0x28a2c71871c50421030c51892cb2cc34d3d251555861969a65655559865c69a6175d75145114d255755869b6dc65761a))) else (if b<62 then (if b<61 then (0x9e7a678e081c6d765961865a5154d559965a6da69761a65aa69a6aaabaedaebaebaa8a669669a59a281f79c75d7596da) else (0x50f2cd3915135145965134914d14d24914104925155d969a4534d24d44cf40f4124d555559751759869965865c6985da)) else (if b<63 then (0x30e45144d3ce34f4115165d969c65b65a5d55985d65d86da6d965b75f7dd7df6dc71961869d61861869b69555661a61a) else (if b<64 then (0x4905165d65155d85d855655659755665a5d65996df75b65a5135955555985996186596185d455661a65c6da61a69c6da) else (0x1a)))))))) 6 i
def o2 (i : Nat) := o2H (i >>> 5) + (((i &&& 31) * 13271) >>> 12) + o2L i - 26

def f2 (i : Nat) := field (fun b => if b<104 then (if b<52 then (if b<26 then (if b<13 then (if b<6 then (if b<3 then (if b<1 then (0x9f38776b396de3414d90ba885b8f0c880154e495314288b885698a3600a442c141dc10cd302b098687f005d72451d912e5022abb329d3d27791c478dbfc08679b60f9a20651cb7e8469ba95fab74efa71cd201ad395150a4ac8e3618f2038c16a0d99c8670084692962b415267a132c0c2d2131f9b22ef2828f8e1aca0826876e4bb445863970b80f87395165e13c6e08d40c9920c8316903c96007288f2e427) else (if b<2 then (0x1b08c96b00410943df0f14d290f7ae00d3bb798c7709b5d99c5c6834661d2799f11899a618b48a183e881264adb2a8f1d0266cd005678e2f33528912a850c911045d38f5b42b5b2134eb091fc296538528f991798ca0d0028c1304696c1982abf0a69fa6602804409b2a31714dbcb440233d17bc7055f2925ceba0eebe7159460e1557315038046f32d6bf0a3c7916b3085dc085c1b513b87a21863fb1ea160d) else (0x38c8418f8316e07bb80aa0b0b5f5893092b0ca9963a1033b9e2ddb710b0600e80c670bba98482b8a63d2c4b901241951ff88154917419e6e8873b81b3330d3011c2a8a7273b474787254362081e7560b1df3f1208d62e904288c706076d40c5b1bb480070b1bfac50a923848490a676b84b40e6143b44c0b29aa72820a0511bc4009a18827908942e0f423142fea687d1876c240531cb2c809840b7710223f1f))) else (if b<4 then (0x413001df90584bc1968982f8379b041db8ba808231819168860ecae0900bbea81a268109e822cc80012046e6386613a15d087472930782281ae89b2f29c07275ad182aa7f0035b6377e08e688062a138c2b816bd991df8a0fb8a8f18d16a834e51ac1c8975b970f598a7d046802d609085e9967f08e217920640353e8c4529733507cbc8d293aaad80881b8f6c3380510004b0a0133b00808c7e05a378d58830) else (if b<5 then (0x2fd29cb387b8a0f9b5078d00e15a21bae815318a3f8973e081243811e734636bb5c5205679a0711ac5a8c6fb095db05363804510a425850d19c0008c88d957088c52e9b16d1a0919295b866ee214fc8e433838428362285317bc2f1be2ae262443f1aa0dbe705b0b8f023850221ec188ab2d0e8f40860c3203f89202161c12623f0b5cba05d335327926e6985619b38f8a42b8404680b6d8e8dc0c6893744709) else (0x673991ed051c0033dd8b30d25afb8f5e8bb5910320b1fb3506a710071a925afa711e98897a77da812c2861deaa18f270f7b7589b33801411f91837036eb1533d902a62e2780cae3826deb3264b6c94099bb8a7402b6712b586973178523087c738f6ae9c5dc30af581734b46051a4759f7e2096cb1c692a175da967d005311020a8619710152a404b8a0481701405bc3000dd0e56b9147d0d00cbf301882a221)))) else (if b<9 then (if b<7 then (0x3b08b0b3b36552f5810e4518f1de94c4e896c980643a335b882650602e862df982dbab8ec8c6ac9b47b0b02a00c558e4c9331b0ad84e0a2ce915881d547854df1fa7b041d70c36c85015062462223b182311998a0a575172f7312a9a017b8e113198bb0180a0c784856d5934e90a99509a108268bba68610517973f2172b1a52b10aa788a524822cb3d2f9af15c8dac10e71294593154b50a29ba302005ca786) else (if b<8 then (0xb82806b38b6918f79c0575a246d1382cc9591b0f863397f30f3a419984873858e0359d035038ae837c7052069114106ac7805e41f5320c208889aa07690976681660020428911c50f7f607340861bbb9cb808c11046b80a903896d8104179b431068cb806f9b96282b449001200e6759c1be051b91dc0f847dc891813f7ce85ae18a6eb213978c1458a2db062c20f14f97aac016a8165a5a75958609ebb49e0f) else (0x2c703a6f0374d885f6394d63245d9c37e9941f9b8380fadc0d47480864b46d91e8809c691b06093d55307b378760d112f81d25b14011a18868f672351f41ba79009f50ab250f744301dba44091ea5a0f873b22a32dc59087790b591852182d6622f5f1ae28ca70fe865da2836084151250599251c0c3ba0c2cf3aa028d9d08220fb5162287c4812008d0428873b3b5658da01847128063a856f627a88091ac11))) else (if b<11 then (if b<10 then (0x76e2d5c4ae581991d9050e103abb8b7f38475b3b6d8964920b48c8347d823c509904092479c145906573c6303d5c7943aa1e32d001a2abb1b0da7d854b00d1319b64e264b09511c88715025d5a05989450a056708e5ec934f01a2ad29605995c613bfd07658a023e1b8c90c84e847258864f9412583a7c8e76bbf6df9f6830565ca125a8a9200b7040a164a00b8380340c76692670974f5934f5045b51646f9e) else (0x4d81eb0b0b9438616b8268223630226168502406740996a108606b615c9c9bd82630a5c0887aa4816679c62bb6611ba45c1ec6f0673d3625eb675914161187880b6070e2b6247a78f25a180e3995111e14d80a590f7e60076fa6746be4261363d191cbbe115a64cbb52e4aaa6d8e91001647aa1c1ac771880b6119da8f3d794342831c5850e829087067131331c91b760c1bf38b010f9f48d69c23257391beb1)) else (if b<12 then (0x25b289778095d096190924788cc7866ee1d5c6a239c1d1fb060ff1b6ff9766f2e66e0f5fa15149162748120eae134be0769c60f8f4651815c12a47055b1852181d171234898b2da3d05a0d0489893004a3e83611835aa8b105865fb2c5219a24a071128a11129bb98f649b45e1220030ebc882a6a0679a09be6ae3f8133a29e2f38e2878372f852661f1cf051b098cb680a238a3f58c5650552d040148b6f126) else (0x5febd4fa9d128280821d944069cb014dc01c278cbeb05bb68d7c6835998b0dd85c0b809ca8c8330248d8528a978460a3071d12b88c1e8f4c40d3380a5f61447790ae3056d6a33f0823739e19dbcab185662ae60a94bdd899c4072b7212461f6eebe6b7124e41214da66c9aa6bd2219e17ccd84c5a017130f3e70bc8f00a308092d877181a0f7336bead685b00a8349960f545993ca05a1700890182ea3326432))))) else (if b<19 then (if b<16 then (if b<14 then (0x26c2d2042b47a02227002411709a0fc5983721976928d1dc8472f0367b022f228134a142c903c98a678a12d61615524b77084cb154788e2da2026b8ac3b81af701a73052c52d1b93a155ba93f8e61fb45e1023fd8c2c3009b10661f2a4f49c9fc849830c68b383980d1f12776b2e36f8527699c8006914027701d7189e5bd2a1a2890239175f806eb945fbb257c852a21d99f0997b064499e41008765aa6529f) else (if b<15 then (0x19c9a08b0b772bc6d23350d034af924809ca5e0a5be8d5710a5621f3610521ca620da21c43a1b1b7bce06b298d691ab289a20f88f5ef1929696a7e84a60842440b010a80778d6a503c1f046e1bc715af5d50542282b698e60b8759b941309e05e10907046218d25d0273f046c10215b8d0fc0c6f08469ca255b0f42e1d2cfb02ae8959d374249e3bc920788716726725016da385fc8b50a912d727b228a60e86) else (0x75f3937187243034a51b4630e12f8aa768499a0685406215181bf8e85b026bd3b5609647e101f33120e3973a0a57e020b9998b18a71e174c90184a087a60563a3d2b6b60268d9cd019cb872d6b71d3961d28a15f966b82e4ae0a906045deb4187ae0ce8fb500875aa41c03115eaabd1815c603407838d2bc6c58c5898d0b815b63003e51b882867bd8f253102c7890100e74e216a41513691484022e4821c20a))) else (if b<17 then (0xb030c692362a63f2800e256302252f0b33796e8aafe8d1a3970babb8d4857aa8d1f28e03c979ce8c52b0e3e404b0705b0200399862220c1d8810848ac350873e91878b015f1c00cac9570a4588532e0131b191748db8d8260d205be2b5768a48d9e4760619692758056e6062f4ad22ea27cd0d6b7ba8600b290b624bbc1e41216d910fa2fa21096f4824b890464119900252b135469d3b91d35f902668e9c28a) else (if b<18 then (0x3311d242af08f056d5145bdbe79a8a4cb301c6969b7885bd9a53e1842a912f2a710383103315a4a9706b260c88150bcccc07519150febd3b3040e6809168251a164858e481863c38537d921cb34ae686262bcc17056ce8f3340e301a211b015c02f03b0ccba8e4c58f300b375739756232301fb6f8429b280e01fab3016bcbf4960d0370bae9059c0856c50b4268418c395101004c83970004e2913e91d1ce93) else (0x68d97602354549422f2821bb1a3a0795a8023b3e0f522c2b017ef026bb9f5a004376960ba9684b0a4b41b8829f649194e5a13d78c0910c8310f6aea865b895b78159e12231be735156122d4348a16c849130462b265fd925d1a731f962970d202962a2869580a916087bc886c1a15cf855190a50e042f937bff8eac609aa98966d3373c2567513618ba2c63300f3d4bf8f2f6002072a2a90b6ac0069eb353098)))) else (if b<22 then (if b<20 then (0x66b2612f0b4ad168e50b5fa0e26f8f0aa39bf0038a2867978e73384284b324131024124ea83bcc8db3e0f2041c9320a5fba244e87c4b8abf08ebeb8663c9161ebaa7a031a88c868bb5100a4a806167bb726296e39a645864620bcc08539b8889f0067c1f651333c30a0ed8f7111c384932b405b5b0cb36052c50c1819ac7c008a6a58000374fa35440b1a695136125d3b620c2d0a119619121e38f9ee828b31f) else (if b<21 then (0x8753f3053b1c6880d59386b336ddb96673025f021b29a5c286a3f87759822cf116ea0f69a394e60a07908686ab399142a93685d846e0a867a8d50e8450b114edae2f9bc2963a1d6a90d11b2e628176268d58974c21619a92a2bb06a0fa29099c60c683260e403821026a73a69028ca981aa8896d38200621677be32f036a2825369429b34206b71b8b64040b2d4362201b02b926781e2b59c0a711a970d8810f) else (0x1d30bb2781abb085e6345d2a326e2a1d6931a507742b5680ad0f7955dc2244a83c778b6a5b167a2e2d0972a82f21f20cbf006788a0a80c1f3b70a39bc0308b6c8b2b4310e31bbda9966297243240e933b4880a4f812889313712ca686bf609516114360c1eb83c92068d6003a8180e9896e6111473d85204711086d92a20e0d26e8fc87026a52f1a30fc9286acf874f20130512110a573d86686911a2200f123))) else (if b<24 then (if b<23 then (0x8420b5c008378858690672cbc700a16e2b05dab559a0e4bb0e48d1a11d148f50d660b85f8363ba192549bb83016b93e5d6b4488113a003750bd7002d5d2090ed9865c8ab8e09685045439e4db15305a80bd8708b15c7d0b72288543031300bc178e7ff007d4806f11e6af373f71075301658895d63a258193e2922c9209538146b181b40c8bd006079147115736246b5a53619027700a508b98b85712b25f3a3) else (0x1f98a0af9996b8e359990fa1f2fe280960206805712a53538e476101ad1e0839d24993691243de062b8803291c2ef801e92d75e0e5f80f5231c4c69f570811559921f940b93228a82256acbab00ad30a5d9185d1052b0a71499dac20e100065af22075924d09f0a232c64036a32b198a95fe995a0a04b1163ea951c0235ed1cba30eb318286d8b6408c27f1727e8d210360c20d7c08639a9c318802640f05e9b)) else (if b<25 then (0x2a49902d87c718592b028821b5de06b8b04b608c682155b4163e8099380871f025d09f3131573ca85a7824bf14436152bcab07e101cb926019f5e7ac217144070f07b9930a0daae046e43e685891461169db427b862272193c08587b2b7106981045ee8b47084612a34db0873e395281e1741c6a3014050937d003639a046126d2806a6140faa5a5c8f798865b209552014b786c3f0866ba53cf1e6743226784) else (0xbbe0ea0f8065a8e2592603b9a6039b9600f6a994612325c2084af880c211a528c83e835c99f2498f637151a8a61651a6ff025c11c4c89d40c0b05f9a6db1c5c71d5c5ad50f9834695148900af1d8d3bf4030f3aa901ea1c1b9aa1450a2323076e126b2be6339939c961b330af0895e3812de9b59d24545805268b93608712191bc2c1848f6833b5e6a120f0d36e8821f3963ba05ac1d224b114e01c9b8ab658d)))))) else (if b<39 then (if b<32 then (if b<29 then (if b<27 then (0x881eb700466cb56000b308252f2800b50ab1a0eaad8289b8d6c29e2fe030eaa409988c840125b010b904cbe841e33c1649009f93a2d8724f951e68d723a95db903ad89194188ed0a6f19d225140389601a1993d0852b87505134f38f1a9917bd06659081faafcce0c92c816e93e6043c2b2af28fae1b58d735be7302b6de036ca963c59b12a0a9cc8a8488b36e93270002579c17e2e433052a92118a010411e) else (if b<28 then (0x62c9b5b30d4ca89ac00e683b1660a457000562081862216b9e029185aa981a3199d689621b54a0803a70310b90961071b598c520987e1862c2a1ab929b30e9a58d70f056b12736b171ef966babf412901cd0e69fbd05585c720f5041986b017ac0a7242713c2bbc501ab088a13066040583c0b6a7194480e2ef356d3924c61a6f2145c23329d16145361070ac700eacc88792036200e5238750b92696964f79f) else (0x61c8d45a0b0328fc2d005c90a264851c8a95eb0e5b38448a00185041391f5418324d8114ea6a3702198332a42abb60f53d184ef3d4119a3f60e0ad35b0f0a1349f8b5006a51d6961867c0326f9b152b32bf8fbe128b9609770266ddad6d58a5fc3b44b04427142ab973f79635d18681bd1dfa618b8916d0d16326a778886439813072e6af2d625019b74f78406b8569511302a21251b4c9121ba1546c888e302))) else (if b<30 then (0xba00524dbb312982de3e2901a0162d8ab044f0881f93b1990dc740d71c9f612944f30e2ed060d616c0f0689800699a857a0c27c29207311470e76f8963db760db55781229d81188ad8728a1e20615d2c7758034a031682c11f1c5fb045758f567121ebb75b085ccc8eb15050ed145e4af55c093c01e19c2005c119d6088328d7042b6ed96614ad5a12608e9b05e016e9b46073c604b2bd3327ec016a78468e89) else (if b<31 then (0x1348b88a9598d8572a966493260e3041499706872e19f2d207cd10e4211a35d9d8170064da841b840a88f25d9a0aa955ff8e42519311bb2673d135b285f8f75c3e66e915bb0154a059c1097173c5df354e8b166a1424d9e1811c0c7044cb0e2ab392a5a420b098450e3b99ebd4bd76eb759f09213b084f0004a8cad9008db8771fba6d31c4aa9a47c006048b53c873919c34f0a359890a1be60c101acb20c883) else (0x2b8a4180180dc0186f815528f24fae153180e1a703b8c919801a588ae88d5fe0943591402822471e23c051751909504bfa0c2989d1fbad1658b44d042b21712e3c61d1841b0369eaa3118411a03b2b0e65f1c638874d99c441032adb0cbb828050d47f060f31a6f6a830ab32c1ac1c333a068a53e0f46097c4f04677825b69e5e202272071eea01cf2fc78058a208766144a401ba48652f831f8245988913902)))) else (if b<35 then (if b<33 then (0x309f7b2065a20e4e2108578c65b0f5e4b85e1901a029b43815cbbc8ce873cf060708dace8d78d88500855558e1dd19768ac62a2a4f0af0c61a07a1e6542760b3b5120d24f8a695903f619080176a83a3b711208af7fa00674b8442187442a1e9991cd1f8de0b870b2662324670521e2421c09a31008bc0828591a3b8198187751272988817d0354484070008c00d70db558d321e0a2b7a85732137e80332b8a) else (if b<34 then (0xe8079ae047e40e6e6236e3815f4a270fa85ee952470a0e911a72039f8014c3091318573f2f4b49c3c2974f39842c8b3ce127b8013c4981cd849630c6ab0454f8f295b215237b158669c8a69624bb207629834ec0a0a4038b4252f1ad2a1921020066b9e00e988408f167000fe294d98f38f03321910d08c0569c992037970e5ca3c7ac86262281218c75689118190c3874530b3040b23b8e6b0bc5df2128536) else (0xb358aa340b714bb602005b8952f6bea7809558811e80c04e819340d51804900037e98d17d890e5a969f1c68098aed0f7538c746926ec895d6864a1001efac10616ada075651172681583131ff2d5b0b74150a3468d6908f62d2b62b130c18f6d4b03ce8b8150c42f8d6b59c2e310b458a56e1016f84c7a068870b704126863a2b50619d99649825dc8221a2213d280bf0d68ea95fa37466874298f6a40864e35))) else (if b<37 then (if b<36 then (0x297298d90602888702876f7a86ed16203ad1d73a9028e78a8504807656815b58658796582b43790421f0115e9214939791801c90106615869b35279520fa82759c0b53893a063560c2cb9b1d2198388b6ba056af1e083020598ab7b81b25887be0c76e8ac4f8abe1ad3221231f039dd092701c2269c1dd9f1c108760836bf8757c144f70f4c1071b2b915a1c7ea040d2b15d78c111876ada945c9a4308a3c803) else (0x24d1a879beaa80b8590e02f93cc001971064921d171bd8a78d665a0690356140619a246e313256864ad0831a232d915228230a7bd8cd0f00398a1d092ff8f60a1874ba359b1d3988788b08662b135b1b25a291c48e6df86612103cc952bb0da550449b842071517707906821b7946bf296141c29e02b3d087f5006cb3f19e0ab8b87631b72d8b5112030e99600102773936ea3a6271b5608a03e0b6793b3a882)) else (if b<38 then (0x2ca212ad98bca858fe0217f258f30e56d0d312052a1adb2b8f7df096a43004c176de2767ab46291e613816e83b0ae1e06c885d81434b8e21a1f10e0a5680a419123c51d8680953a074bc1b3eb991b4277cf8f0699000a2c9de0f93a864721a2eb9f1988276208657a03be0b06090cd605758ad6a2055850615207583954219b1403d102bf0d2ad1c3b9c340471792743053123c1040579f034b8104a0073a602) else (0x9708e1588010b1263f101093aa080b9800e8e604839871541597c8f642315a4803f78831b0f1a6166250645f8d29c1c9dd8e751a65bc0419a8d0a6be2da81109807ab0bb3105b5c8ea688d91885794012cca7942085cc0c29095b53002da98bed866f8ae1609200f862e61e2d6a807613b55809ad0a6e0bb8568c33896ccf8f2f32423d06192bd18d210e5b25ef2f46e1832280aef0814226c550f54a1f2f8ac))))) else (if b<45 then (if b<42 then (if b<40 then (0x748663e1631d1c2919869a876991335d831c9271198a9890850a1c26827233000d790ca20d9d48571c8f6ba237340490e8c6af9d666aba648076e052d7137272b5d1b32ec3923c8f17b0e6b68a2bc0c27aaf0e60298f8a5cea931d9b19fa5ae608828896d5032ac9720d965a917160181591f5c5849df046ff8f531001ee9cbda1cacf0e5d8991e19f0618c013a03379c29f2b44c8c24f06248301fcb7b6b8a) else (if b<41 then (0x3073721b061a1a1c8f873558e276011d295ccb80246b40aa09bc0889c50a2d9049de8334c924718336313652bd5d9065401a327813bd1b2fc2118a88b2a05698035fc1c54b893ff89219b9c138a2a0931bfa272f304ef2a3859bb1a836ba9fcc5859098982c0c666be65b9a5fa215f8bc49e8137a10197b574506524931de141ba02ac5847eb037012764aac3679f8a1ac699b760fb546b8d03f0c75cb50ab80) else (0x53d84506981a29a0db1b84781709b9503143f59432e991e1bd228b57549a2ccbb8620a68f99b340a6e7a310286b120a6d62223005637be529144a30f46296aba032d69714a80765b967e2b353062110d6b2300c291a5c07569061b4acab38e637aa41d012018325a01255af1fea989fa4747bb5f885586bb380820ab0b053078f20a70f966fcae240230d1037b6006a0283de131a9276068e8a82878e0364802))) else (if b<43 then (0x28238271b9242943a9102dd841f5039e3005e89e5cb8134e9227f2223406144186e2046d3a465c942e28e97a8f88b8e6b6122c61dbd73c368141bc3504888693a0764825dd0c3ce0a6f013280900a08a0968b8fc007711e6fe386dea66599333b88299012882d1ec890750b7768475f066528e15d8c0101bb56039e68f64e8815995c65044b6974a8997649a30c84769266cb0fab60b9c8807a409630965b19e) else (if b<44 then (0x6762d3b589a8c0b661212ab2226d326bbaf308321b8916dab86d5a26ad875823f68f23456911e02718c0a0001e2f69a3931f70d8265402642b03b00faa4050f68dbf481a908a99c0f724a66bebe51c8fc5d8b757965cfa51fbbe1840d8100a13b0561491168190f3914d5bb3c28406c9d378184fb024320e31c032f404701ad40d8323090bbc8b5c816244a7b8983a4c076572e5d21452a97c18045bd3e4d21b) else (0x382831ec380d88b07d18a020293e8d4ec8c3249525dbf15213068976892410aab7d50664b2b315191809dba08c6b0a2b24084019941e803f9142692620d2b17ca4899a64ae8579303673854e303b21838f9025c08644d823c2141c51b7a50956f00502830068fbf4073e71e3c4152982f271aec5308c4b08883855d73b31c8a3099521d19b100ca4a889be84272211bb9203d0071905147b3c4583bba8d8972d)))) else (if b<48 then (if b<46 then (0x1f9d2cb2d0f99994b0e70994225040f28486c007593a1b28908e075ff102dd30229a19df8369a2533c872bc261f589cc40c8d98b4ab1b0298c563891981f5641130596c0d072b4a929bbc6a6293ca8d0168f8733633d8a0f6340e53e5271baee84758995e62a54f1534f172900b2633324b802030cbb50071b891d38ca030b624b04fd891ef05c980bc7904bd8b468d0211700ad58d1aea0134396e03c3c209) else (if b<47 then (0x88a0140183315051342c5f08cbdd025ca1943e931e03318cb05d4b25c4993c7851a4b9a888e3b60f73cb46b0822279b769a52cc091d812c5f0b73b2a2d31f07c9ab810a8e4071f90c191a9adf08733343b78314b0e8fc82777886741a6432a19232af90d8f7097cc082d0ae24a1a9480f32a941ac9046d8806b1f8cb004ce1216d83aaa095cd3950d86b170e721021669c9bc047289317b9c6628a393093701c) else (0x5b1005030628c918318a693058b3082b78e28cba209a3c878f75a80587317408d6b5380f4b8ca1808c9858af8815e14755b46e4814b100336833030d1e12318c131553a7780f73b92614204e537171802e91417b2760a083878337b1023b251d1b91ceb3b91005ef82339922a18925d27a228c5b2a81ef3a1339a5f10941019105299dc8b80f061df0f1c5910bf8500402b1e8566f832fca7294ada180793f0d))) else (if b<50 then (if b<49 then (0x84808659835921429f18206ae5c6294650123e060449ab878b692161ee1b1d4329fb0c86c868640068a202aa11bc20c95087747174ca0e37502225300031ac37098a5af3ac8d11d9e00b3289a2b6c1213d199165245e408bad03b7785b418874dbc4ab073b19068fa2c358ac020fa4e068a48f76d316450d4ae9e46d1600c085330a3768212e036001d1b1026f9995940d1d3161480e4d3b61f4ab2e32b21d83) else (0x8668b5840d203958060d2f10a259ba89b0f3dd1373e826ab96679134328429227135860c00a520162d82604909b620ab42079cf8237986cb28dc75814c488306063ab0d301932ce21944828f38d5fc92060047690a275b99af092eaa80af3886eb97452a3831a14925a468a7870c6c218209301638fa1902889048410055081533873661d1b18d18983146a96ac345ae8957b8936c962b80824c171713f02d06)) else (if b<51 then (0x2450317e3103d8164baf2f310834852b2bb1f20e22b0f15e02153a90b68ebf28a6e521615006f80d3f11b2cc291d11a9418a3fa013949338117bd4326410345d82c390e1a601736b721aa658f073800a04e9e86f3466b385da8f01aaf6bb0d69c31a9c0c509104951845b8c17f9617e8cb880f3130f1f3921de0200aa370100697917101c5cb2e4750e107ae0d415bfcbf7349f644ab741074098a34584c5709) else (0x6e1af68aa750b01b78812d010233aa109180f61cc43844c08928ebf1c0891ae2c3b2842911f09fb4687055d98f1fe25bfb87252b371b3a59506523042ac0ca57074cf9217205c440fbde0d82d8c76f26248b72390f105a85cf09598191002ac9d0b845833d71b2bf3ec61007a30767ea54e6a93a69f19f920efa12f62a226bb0e3b85e29a490803298c2bd0b08c8eaeb0ea75075631e3bf8208998b2109752af))))))) else (if b<78 then (if b<65 then (if b<58 then (if b<55 then (if b<53 then (0x60a3801495caa845d6911430d10fa064f29618333b79838c170b51d03a85764ae51f00b91808028d1313366187c1b0970186bcf8e750ac6c92307b8102a8d01e1585b8d74f9c690b65509a4ea3b46e0f40b0c71b926d226661a75860222924018a6c1c2ec048e5bba656c9c0ea2d4eb842ada4287050b2974cf8c04c9926ca21c616634014e612202881c3a6099970800a8d40e72d1c70e086d61a67b958700f) else (if b<54 then (0x37b912d598299227a906746823a61d0ee2499d89866b57423671c296c7212a0242690f249ba1a0330ae8a00e2351680293ba149bf08a820abb77fc875c3ad2941a24ea6153b857d0b20c051b7b7137ac8683b41c071f19b240aa2232e1b5adace0860bb90f51530daf091894cf071fc3814b8f83403679848230d7fb8145e1a01d9d2781d0de1d7ce06642995aeb235f0b21b85be62173aba201260c68661c98) else (0x8560e5e1b44e99f113aacb48bb7806731053d5148a40b754a6508924b88f14f3c568177481924c9d1e91b8a507381043590a190a702192bed06646ab3088229c9d4790c66bb70e00e360988e48473eae6a9b4645a65b68b1b02601186bd2bb69cb05da9c5760b4f32c0ea86a2a8c77f816500618b3d18b1f5b9ad29ca71ad00756a4671a064d24600931e3151099d9cd8e5301d2043970f3f69aab5d30d3f406))) else (if b<56 then (0x84c84561122e0ba5b3bcb4c8d76dae6120ec4a08712226ae1369538667284d1343261b0f30d6cf016943a249ad0728345597cc88067f2430a311ec1cb5409705a314b1a9f984741bd6d9b468ba32962a2388e09b028d33f5410729486066876a422279261daadbd08392680875012f61cb130d4601435f802f9145dd22324853183e25e2e126074158a278a10d094b3c8d6c78e6aaa7600355de223ae1c07790) else (if b<57 then (0x2cd83245891fe331e4291a703be80c20929624ad173adaf68523aa21f68c65126390111b699141310e50b732ae6f09c6e702aba813ea11c270298e051732864b884bd111e4808d3a966c3c8748c6a1b548e1b1378961f8510fb98138f77b06765236e92d5dbbf3841727e0e23692c1c0f694b43cd9428806a2f89766bb6cabd68b095f6004a5882d40a29b00be5848ee04c2a86a230f699043190730284a6a87) else (0x2ae3223a2b1c2946f90b309351d7a0ab8834a0945e3a736809150861388d7968f37307a8101cb5053b702bd6bca588e2f1801d10315ab062b095f3231deb211109ad2022541e221a9c708d5909b38681a128f8d081695ab2a1201a49619c3c4d0b80ffa16f33d67185477049e5878bc8351a012d3851a0181912d6153e34e1e2d8ad262802149f1fa2388f9076c843d18132390635b95b33b69d986898545406)))) else (if b<61 then (if b<59 then (0x6e9a36da213b596201ac1db078fe8046a0316cabae0068ea8f80e0c2981124b104638888c1c6a70619d8c62d1622b23b2f0f9878474c0d605244918e001a66f51e422033e21050b8244a0d3a79c700373c19692e0b4b98b1db1c0561e6dd8058284557852221608494a900277b8a6dbac5c8974d01729b8508891bd7807d00f73fb06510b5948203e1c21e8c1a43b01a3e8663076a16608ab2123f7713461306) else (if b<60 then (0x67d3e6752b602bf456850269874a0457e1b2860a18299b068e485063341a24e329718481e854ef970b11f86280852866b2a8b568c64f885999f4648965f9f5a28335204167a50b193872b9757185529196586627a96d7b364d9c641b65649239e8c1bd989cf0f65c1d6582d390972ea8734c0c04a9821e9d0f4a54ae112e99b0f7196b9815718a3a30639d1b2993776b0d5af954e524c83802772c19390c0000) else (0x75b10236ad5fa88262358658d803073ed00be4a870d09688b164fb321398149ac0cf8f08800be1032dca52a592169b200b1094a8628e31120a173d0e6982e61b15374942f8852129e17a0ccc8076492105a8503f168a2a54890e1d0b1c8a0956b823880562682b7d8370908292a52672c1ed919eb89222af03a156a390644293e896383045da321f0970378abbd041a6823d5030a51405382c24006d70869a91))) else (if b<63 then (if b<62 then (0x5f384469183581f26e17252250c518cb70b2ec93b478182a876eb3b3d4903b61c0fa0204184005a89ce0162c0d37f8c2e88e15d95a498e8a58c6cc8b6770d54e81408890d49c6530042a1ac2a04bbe8c740b55b7173be1026da620c39196ab0aa80a948447e8f2b0234d79b3940a2b1bb1d4af8df8457590c78892571f221b21d892abe8c4b29f7a18c33a8822605b868474215361192420c0fe363889515388) else (0x61d065c2210e5810a29719196135300f19cabf8773baa7278d0b60165f0a5e8314a2010419f01d076ee8e62c8478e8122e8215d1b9be0a4f28e4eb220b705c5106b3008771abcac86563044e286456182a5141da987679c6299a5a3091852200a3f00a1a929826889b14b9b77a057030205e875e69c3349f32c8e20d18735ad297b90590b6178f2101d0f50dbac0d175ad0b10b04b9297d0d36b9f17c8211e87)) else (if b<64 then (0x222b80fd07825873110d2403309e1d4e8091f1b111b15c1d802c7a79510866b805bab13d70c315a257d966a3393651f0b5bf5a3a7012a6a7a8a4959d63804620b49990e6b5b162d9f3e0123ac9a268861f7054db8e4710e39b161488f7f80a62a031e5019b1864029a350071b82f1ae1910f35a19855d7b75b23400c1575f2775812bdb1cbd30f6eb0a310341d3a80ee156bc2f1160b7c6087152d58f8f03b14) else (0x9a202795843cd8cb9c8d498850b3086842d2938e253afcbd8c74a20a34846321e376141b1307b4096b182135236c281bdc9b5f7824658d6ab214fa80398132bf038bf8e7080740d9108584cc2046e2ac6998a66396460883911c27ea41643bccf0b7860d68e135ac0ccae89c710e12fbc19bb8667ae2e4b80b49f0970cada8b72c10cbd02c6d86afa8e63c016acb55e2ad0cb0c0be1f68ca801a8e9ee028930b))))) else (if b<71 then (if b<68 then (if b<66 then (0x5ac9e1e21b4c3851d7b16b22a0348f248266e530142010b433a17886cc271cabb1679b6aa811bc14174960193b8b38b80e8d8f00573312618804d3862fb881bdb41868c175b6677932df3f25d1d015ab6d21d5cd967aa0d0b009c050e436921e7a41250f005b19e2824239d22f086229c136a5acd0ea2c0d88083590044771e313b0212171239411399a77027299850c03c75044cc3a461851edacc990da968d) else (if b<67 then (0x2c8b3774030621585c876f4b44ccbfc23891c017406923791b0e32496f8d17c2616ea306a95a3b0a6633c54d08c6f84548922afb8937046ec06c9a02654aa3b69135b002868b823826aca165181603ad2310b1c40716e2e04d1a00601a3d8979008749af6bc386b110258ae20f16c5283665bc55e969748c2df082a91b123036c2b84528f03a05a8b8d899087af07774aa1cc9c9a7077ba847910b01c2568c3b) else (0x26c9f4e8a4158381288b2ce8c75f1e29c362163ec770974fb867e85607b92dc1115f0081c0951213071805029e0658f8020245b974049b2aa0427f3113b234e199c38866f28a45e992ea162513911332c548e7fe0d706a2213149d50407e93c4303c29026f915caf8b9a78992180732b01eb12ba68255a8d49c123c71a2cda00d302953016eaa82a520ac7025a18e00ba26b78524d3f102ae0d58abd9953418c))) else (if b<69 then (0x24f2285a8a59d9f3ef0f3e41a25ca815da0099102b5836e6bd0319c4580336c171150b4950835a1326c371ed2d741386aba058c0a4cab66d1195ea802e23710bbfb940ab1c8e8780b6f3806968c5fc274ceb501cab9ad8d2d020b9f8994781635151ee286189c3d00927e20215a940e932fc8a17f370828175410740184ef8f2dd972850fc930251e0a414081863092f0c660046be92694867fe8a2a08b26ea7) else (if b<70 then (0xc3974b01a273337149c6ea9658c363df8019732113b710a245d086104869018a4d33029537236899b8004969f2328f70fb82f8b418bb7181a414fb85eba12d60421b310d70f96c0017fa17f4842560d2512c0a0b5c4489bbb0d772af6a29b5498c5b5b5631061f80b1e39607687914867359d733a2b230e4bb8432a812c0051859f156be0dd9c461921dc00199ac155076fe055f490229011ae9f008be33e83) else (0x150a0ab58223eb2a92026132032e8024e1b9ed0e28c2c216b420a97145b1cb20b5aa1c36a812a03119296b3386a5b0982a073ee903e3989838366a9e4031414384ca48c714866482a40f8138d9a6d1824f51c3d68806d8b7890113d8300929253b9251bf6678d647256230a5ca9c3cf8e1f42db0888aeb8a6c6a357a85c678b7dd07568980df846aa3d69bb6641a1602115ffbf4db932b525116146cda65ca06)))) else (if b<74 then (if b<72 then (0x38a1e34408a96096b6070210f8e2056aa100b0b870dab429042e9071870277a8a714016763a5778321a361b0331188b5378d1ec941aeb9697140d510a3e0567c2a5a130258b41ff32b1f001f08c9190b4aa15282ac238082a80128f212649f05d104c6068550f5480b2002f1660f163378768300eb3965088128c60d884b58f32d9230a8113fb81303d1d9ae19a1714fad0a2802d83e2a8940628687d8953c9a) else (if b<73 then (0x68e9963e844ca3783f89780861f482815876e3391dc908708d4df8f3b1020a789bee08b84838198c6688c623af231258998e17532bdb0c756b74e394251a22921512f239c8094d4b42fc93225a81e0bb106058200d6d80a41e9d36a123ff910053d9f88e4d7864079a32d1110a8d876bc6f9af6e29823f3d03908c2207b970c48794389081b68a13f8113726b4e066258659faa2aa3c8793776d16718895ea3f) else (0x62d8f5bc9d3b5081f9936d08d67a046292756c1c559031c2ae0f93a0f3830ef238308d68ab35a21c266b90ab13bdc871a32208e19af30a9b088686291d63e19ca614908bca0bcad8f7c90065804561044ce8c35e8015392bf6878eb8991a89698993d31d1b6037328136b0625207049833c18038185b63865a52eb448da2d0a99e878e38c65a92556803b31f1ee344e68024aa5230b91cda61c314761066cd26))) else (if b<76 then (if b<75 then (0xcab0a88a1e5cab835a056221610f020a61b85e8b0138d72e2d69d86b19086e78f51d1862f155449e4fe0ac8187b670faf50a84d8283a046dc095d03b333962b19b0649e00a919fe06873096d433572972cd2c2871627d8c9528d6879166fb03af930c798be0a6546164928f395821d426237beb0e8323f201ed881c49a16e810ac97b1c056a31a311275e58525bb80132089c8549b031dd381cc2c0b0ab90080) else (0x6272315d3815a06bd90b4f91b1eca907108b61086b7a90a93c76e3c757be19b85430062d63901e0b994812ee0d2db1d07e09620122b38c22a07c408086abf246346411340f142b13cc8206999857b701728044bb1820a101a93250d9219a00a538875e2a2f7a22eb131f83b7b488617a92a7241e8ba09b816bfbb38b8ac338959ea394e0e7c2816d88015db242f093490e0ff800228c4b68b34e052572a1df29)) else (if b<77 then (0x59caa2d5292822a1580400984bcf04a088965d960b395b9d8495c0368b143f70c1ac82020188962188996649ae6433e5240f28810c068b9e788878321ddbe07a91874016e09e6658144115203bb1e8861d5af396072a2ac1618ca27086f3ac6e8ab6d33c6082e2660976d9541a113d2822849fb8c885f822b5e8227f843e4957ee0b674aa51a8c3dc192c99e299851d58e2721267db72c1b5182050d785bd5be) else (0x305011ed1a1da2f7238e6963b2d2b2aa1810539f5070e4ca1a34a802ec2ca92836e71e5871d09e303a90c2dfb60d7140388a40e0f2233a5ae90c588890c892d30a244270351e5c30a0890f03e9fbe48276a3174f82674832b4ba1ac2a4d505183ae1590e04f17b00865e9bb3921a0ad94b518882808687253fc860f40494e8e6dc945fb325b70015eb111386bf90e71511ad9844e9194120ab60006608a61f90)))))) else (if b<91 then (if b<84 then (if b<81 then (if b<79 then (0x633815071926c01cc98d6888f1bf1e124007341d56f9a895042df8f139ba0a98d7672861e203f10320e8b5af092afaea8d0f6f39a6afa92da191d203c4c82a8d8e6133d2ee83c3d82b288b4ba9d4139632c1ab4e8d7700a68088290812373d21f1b170bc0980b07f92afe0f8fb8652285be68a59d872070ba8e0a83b005969e4a887a820364c0660fa65fc0b50e9c0ba360670d003b74b6002348a1b81e90b08) else (if b<80 then (0x1c1b3b8503ae28765b135b4893218813a0c91d8f2c19001f0f76f906e42c6d02f3dc802160b05f0fbd68e80d870b4b1cac0f623b80ba17cb58186883636ad3d393bec8d5c50fad68116b262fc1f210818a700739174ec2f00d2c6f2b66d7a32122319584166160b41a0e43f588873409730005144a1af4056d9aa2f6372852e8d20d2c81156a9355c95536033e68637b002e7961333a75bb038e832de8ba8c83) else (0x139a61332d0cc9ec69035ab0c1c8b911a8f6e90059e3b4511c2da0501f866fb8c8b10a663192af8e1ca190c9987cc8b7540f692b265719544121578730726bd539b45083aa0e35e953401f6aa962dd19279a60799d00ab5a580d767be2baae678b40d608386032cab92c6a6013be94c8768d258dd0e2e8211659c159846e3ad5c691582174ce063a510b038d5bb3a3041fc5b816d1a5684b96422b3fd0c63b02))) else (if b<82 then (0xb0a81cca82bf80f974048ee8558b922a2011e29c9020381d0c3f30a2d78309c8100fa2309891500a0000da0c0c58e161050802311c7d8c95905908875cf3f41c14623333079e0e9b30d39700e0583a8560c0e768875b98d511b91e2a60f325c3a848e189714a06d723688122dc8205895b368652510261141dc216fa825e51a0de8f7318f6a6b562ba85b6005b5914d606413181eaa310f886fc09597145181a) else (if b<83 then (0x2ac3016c0c6a53c3281a2848f1d1a9c07077659e387051cc050d812042187488cb00079e08b21681659a9c8d0cc0e876b6941a83e8ba07312bd2b7ad0a700b4a036bf175d92e02f03a54096179a55f173cb8530cb81f7371c62d7c9803fe196ba886703d5c98027c0919c0bbdf12ba78acd70f6d125317ab2ffab240b90d019a078d75c956173cac8817c1038d43e6a90a5890d244b23a5033438d1ce33147a2) else (0x1b50eb9c00a05813d216060152db2c27ba7157928da0d69c936652ea89866e9862ea281d52b0588fc490b9290267a9f5d18459b04209b91032b0a58b6a487186a04c31e2951f199855170b1e00fb32046771ba14856978231406278832439881804243b617008c538f9278452f1fc1602608b3474004448b0131caa5870f6a96dcaf648991691402810acc075129446b9742916086843c48b263a80a496bcd8f)))) else (if b<87 then (if b<85 then (0x42b0827cab6ceafa038097806086125088e4c4161ebaf1c98118a2639a1900d956e13e3260e800827300c3c400716805a8851428c642aa43d880cd9dc41806e7385e23c4ac1e5e216c3c0e8798b7e38d5370a3bb8cad481996806803752c8917a2f16803c56815648c4d61202c8fbdf058d70b64199b800c623825ea2c248ac6a18f5b9027441c58ab756f1120807131b00050a4ee862a69d246a5c20066a79b) else (if b<86 then (0x231901f6b966c9c57c043bb9a19823a5a8a38e0f37b81545003711229d0143f1f1a9ad49d042e6b62199e69f0f38e1a1e084af78c69d3f36b8c2111736a0d32b1c241844d89a27a3a36e171838513e8588b987009d27a16686892a4340eb25bf38172dbc64a2415329c0c836a8a62d884241a910b2b937832f79961d823f9010450eba9045da1857805c1e0d5e1143309b2670f1e3a26b41a5bf8c5d0b855f03) else (0x727986da974919038f90280256949113a8dcbb03bfa847663471ab36c236382076660a5dc9453f0809094bd10d2bbaf20ca243b812a0b21b1996a0b3621063001e131197520f6caac2ce311dc36b3706764136c91c5bbb11978e4dc862f80e163ab9428f4551330ba0c938b9fd088e9869398b63ca61d9901a2b90529f3f496196051501d0ea9e0818473991597992e0299458a7699e47a8d221817b68e4418e))) else (if b<89 then (if b<88 then (0x12d1d85c0b300a52b9ad1b2306900d4e1053b39fc2d8cbcc066be8259a9a4df9477d0367ca7217a8027085178e237838648d8430328f1a76c0d1f0a61d807653ad4d19d5ed3a61b01557004f2ac4d68dba2088aa875e7040ae0cbe78b9a68a409962c80aba703295801948900a0dcd6866760d767ae412145f02507d0e5ee285c8014938d3bf193ba84306b62421db5e0e5e31658582162066e11e31a0ea5787) else (0x66d058ff8a8a32c487003f09fca30eaa10d79d815a027584830b8886c019602a55fd1445700a13839e1019680322287146257f90168dab2192221e3acb60c5f8a95a08c2f30f18d3a5770542d9c41087c058c97a0f6240d3cc0b5b61c58d924f124112a76a694281021610e9430f8cd8a697ae68db56320bc868091f816ea1f6a19c0b89e1a3b818c907dc0d639ad6b4804178e3348c1fa111d4161ccb119910)) else (if b<90 then (0x132104cd11420832e98d2bd8d2a3361bbab0b8035b91bc3c845e5053bc0631e8407d96a8a0c96f0f86e834ba112eab62d39dae48aac085a6c005a60254e931c32abb2809d9007602f5efa51f7937c30475530626992fcb11979888d0b2aa2eb5a08b398b9b4007109ea30025c18b1d6b81c82550c8d140bfbe527b4b04aad0ba6e8f24b092ba0a1699a3b515933815c0aa1b72414696baf0a8bd856a7226b134) else (0x6ca1662c3b5feac1148801c0353d98b57822ca950ed2c75bad75a985d41b3600a14e94bc402b3b80a3c878d1018c5056782e5d5333839427c8451f9f28db801419b4d8198c85636954de0f2a7b162782c68004f1a92c4322a3b073c8517aa56fe266e2116a3bf58a91c88016a11014088b9e8eb1487709805ba9758e3b2112b40b181c524ba28e9fa885c8853758e22c8d005805429c7e789687a962cbc61c26))))) else (if b<97 then (if b<94 then (if b<92 then (0x6b9a76621961e954329e103a10230126c8506306540036f70e44f043378f237020ad87b390c80c8d7cd8c704a31031b17ea3bfd8a99d0d7108a5833956c8bb93886f60138a092031c1498e8498c6768c2152b5020625a376699f61e8f36906155a70e38c6468044f842c40b217b1a2f027d103716be6e19d3fe0f1bb051ba3c5cb18aa0838908a73f9473c01601a14f5862efaa03d149d88f61e135c7382fa22) else (if b<93 then (0x7361f58a004e982136805eb9b5cb3744d197420258c9f3a71926e921da119db841c5aa29f9bab1097b0863ef983568014e2b6c70d49c083ff0322e01ac3879660d6b4973e9033da8c3c60e0249791c8176b9b3691ca66033649c9b00d0789365e9737c02ca10fab0008d3125978317c0b0c81e7c2071dcafca00e75c07670234eea059c172e0af1c88dbc38bb040494600713864cd0d5d299536829a4875d595) else (0x218b77998f5b62a1b7880361a01d10b59816c48451a99415933920a1950ab1102a398f3df9ba4d8b4e0062cf971a80b642832e03e280841d22788e8468e094dc93202b41f1ac0770201c89bfe8a7339e6a2ad583be688a55e72b27e98892965a22828799283290f696962870cb1b757805141100d8d499062d51e263870f3ac7a2037458d59c8e4d5321613dcd4015739d0e9a009c07348042619b7d688755ad))) else (if b<95 then (0x20a0317fb00e3310dfa2bdb991d6280142eb7482aea87889193501f29ebd280bf666803208facb0d8881d25cb63080aa8702a0c816a1394e11e3950709710b968a9a9079a50d4279a2cd07720153588504403bcd071f7af915878d30ea878e72f1717028717b560b0d2a99c27b2509f040820e73eb19f288a42876a0322d1381f21800323910828bf0d5bdaa48e80291270089c7bb034830709f1c5f33d47491) else (if b<96 then (0x89e8b4f031abd0e794855cc8bb818aa338d8290d0fab420827140119ab827058469e9726d890fdaf3d589293092679361e38616003d6110bf9f2608eb5b89309b11eb0a148261449e63317581b508d8a6081a1b4800690f0559c8250d69e3953909351092322001807866006fe1d1e2359798b89a8384c0858d1456d8734110b208499b8039e9220195670116198f2d1011b11a0b913b7c833a18e3288f2a4be) else (0x1dbb10eda22d3382d1be9f20c5cb05307a630389bd9899bd0787105747ae7298664fa14768b200a37590a26e00079816882a5f99db188c9bf0c6df31592926232254d824b91524c320b38888c815d11f5661940590a0b841f9151331b33203a758878c8929e97080859c20699a8b22916227827741a768372dd221289d940836c52047310017a46da1c32a063299767d2d4fe883bd872553671a0f2559493582)))) else (if b<100 then (if b<98 then (0x7960a6d53e02e049ea87874312d1871b7af1a4aa13c8303d95247b863bb131f1b497022d81c447825808bcb7805e08945f1d748342f2022e09026f1b0a6920948e73db44d5102dbb12459722624baa000a81a5df9c5b43f151b2bb48777483767003840c188037e508610b05221f23b07136017ab824dd921cfb612d3510e368c78b6f42e696b762b346151b5d60f5b9b82b22b606242e2a9abe07254ac210a7) else (if b<99 then (0x2739a0290a5fb174cb984438c2b08e6c4a02c9102558a211a26260e738361330701a0e15aaa7c00d70c8218dab0409b543145011b2dc3c28a122452520680c8d85c8a8d72d2b725a45171845f0d231a50bc3977e846ff312cb8a2ae0012eb752f962778d19ab9a330b8b3955c4032acb195a06454192293e20dbd601890cf190470672e856b42d619951cc86cad09511822d5b31abab0ec85c6c8f5669b1eab0) else (0x4fa092b1260888a04b1201ab81a9012548519c1222389cc18a2033a156376e81e137010a99fb66889a102869393999c247ab78388749162939f0b6b07371c40c82b52829b98a71b006d7366789224c83a100670e91522094b2122ca05c9f05685165eb2d5e61946d9c0978dc848c7800b13231109ba9ea067431c5813612e8020a3b0de0207914b68094d30837c830ca02ad28a5bc8c2f5269d70747012877bc))) else (if b<102 then (if b<101 then (0x34197939080a334081093168f8b2307001e0491fba40105f1d1d72e07e846a9232f705611254cb843ec97289b89b382976058968982207673058168935c142acad339040ee8a405862b2342b01c4488428c38ad08f8a6856de96bba0e6c3af5d80db900eb5209292b48248447b8491b8667e02411833172663da0420122d73703f9b8800c22e281818d16c185058809119622236072e4611e46c9a0549e62312) else (0x39b9e4f9073dc902b49e2a38273bbb3819186387c2e878778d6f829136330bb826cb296089f1ffa3c9d8761639b6883a49056611c519993ba911f53f06a196c9382ab0e2011113c048b80f2c8337392f5a1b75408176ead5de952bf2e9ac807118d23abb1c6bb0938175c1126316192891642cc018f3d11724ebc203261f0b54819c46a1d53f8c5081021e1a1a41fb1e0d6783049f052aea621d391959536213)) else (if b<103 then (0x631354d28347c8632a121921e8b08d764bb7411d67d1d679a2814033848218303c9c8fc02877353f7069031e092d586cc903bb7826e5863c68ba120f700bc4e59f1509110c2c0760b84a837a68262f084370723a34339891f40bc210774b885d8b10b8b82a588256996a4b87cb076ee0064a17613ad5fe352ce0c6eabf5d3a63da9784687617ba5d31157b011d531c9b01a7b8f71b1c1008e21c3bca384a4885) else (0x3d9890dd1576f14603213721334d012eb26225b91c413147170c100bb00b7ed0260ba72b92f8da8b765847438a6649c4489d2e01c48801a6e077f2000959e69c0c68e3e4a3803b4812e2181a4046e40f67137663065d19f4fc081ba2d18ba91821266b103101710a955538d1d0375c13669b2060e0e5df823f50e212ad1999f9688a6ef215daae05b9e0f186c580543e0e272821ef2bc908774daf51608252af)))))))) else (if b<156 then (if b<130 then (if b<117 then (if b<110 then (if b<107 then (if b<105 then (0x4b7192a610261071822c090844440d2f0ac8f109218adcb1856523d0f8000e59ba6b0123a96aea01772241bc001b321169a565e193f00433c1daaf003193916238ac18658bbf3879b0ce1b55b8c3660828c801a59000a835b813883074730b6042b3bc1336d8d01a9c713a05e00ba45869f08f8bb811f5b582b0a2e202c8e0c926008a22e45d0f11a9aad70753f131418f13e0405a1778b0533690a070f74800) else (if b<106 then (0x5fd3a3a08305c870540cc85077352996d0816785b890e72b88682080921b2d98dbaa806ec9853b857162f3789b65603174331ce0561a313729e5f81275cab0108069b1d5720053b193668e318020280d0043e7990e5409e2bb2e26b041bb86154270fb2b92c07928067378fb140d0300fa9c807628651f164eaaa3f80f0aa159a60086a386edbf62813459113139a0f338a9b0a36d982e18d07b0fbe9078ae0c) else (0xc288b1d83b7a58478f866401d605032d5011e3b112316c6a852f1352188d16c2a604a137e8529c2500db76f7276710241285c79853e2862830016ba5059105e9aa05f8d86d0a73f1520e111f027156ad11718a7289990846e0138c2027492847c9f45a9b3fc0587f8053b9b100afbb380678012861eae2006102a0eb0ca20835ce1e4e72e3578630e022401c88894753a272180594975639623a1f877086ecbc))) else (if b<108 then (0x299d8d23d41514212891c18eb460c1ee8073f82664b825290742963e50e6bb2f2a8882709106d00b0d067681866e2d4798f3ed942243a750322130400b84731bc72e3d5e0b229d9d230a900c32a220688f012c82d2c4b819616a62839558ea5b808088055e110ca853760d2deb1b078c5ffa45961d57d824cf3212e2815f84c0a03a600066f0e606966d9055698b3c81e37f9626f0b02a1e58d8029600200b5) else (if b<109 then (0x1e82aab408a868d8b90a1fb100aebaca0875a2ae20ebf5169b254b61fa822158a1920ec760396a0626a0d1e407c208173d126a9a94bb972ea902c6b5224a6ca5078be0e79c8398d0687a877489165a047f58674c805a0b45158e10b83c668660e2fa200c4f1002c4812b5b79850080c064c9bb3310026413248081709211e100f82471a29173086098d2d28acc50e588064e7a3311aa0401e6f4943fc9e39683) else (0x2c12ad180633003ef890f42ba748276cb26cb941918f172ab08e8b72912528864e01e4b5903ae0924e8c73c904e4aa4da141fd1c192ac0fe088ec08279ba6cbafc49877569a28c0d17226ac30f9da0d0f919aa20a6373360d3119706811802c58e2ab881cf9ea7e044f40583f0b008a83a39b4241e0d20d0a8989b8812c5961c23ab618ca118b741273ec040b788a380d901076c8a84ff9426c1a3a0131882c)))) else (if b<113 then (if b<111 then (0x4e5873728b4bd041a9199d98c58a332a5370c4113eb003bb1d7668b50f063179b24abc1782a0f92d8188b6440e56608be8861ca800b737b060f58f99266acca286bdb893fd143c613621195e2be56a871e43e0360154e041380b9c18e7a2825ff0a52e8951c963e38898b086508a2fda96c902c6e08b0d8ca650d9f7865e39a29d2119b2b6ed3b5fdb9448194400915581109a77473641a882f5ad2e29d0c609) else (if b<112 then (0x773bc0a30a8703805195ccb0c4da0741b1c29e8b25f961b2a246c0f1e300af6027382a60f264bd9a58c8254c0c25e351c99811917c7b0567a1d68f1b64c811341573a205a3244689232e15259841c387c2809be40b782855420f8ea044148c12c84a9e01748af713bd5a89726a8322711a6b824d39145b0533e9e1b61a01124ca70190f806b4b81ff0516921571946ff28605823359727d02178af7e4894f182) else (0x599130f2226d48d47c1b0bd015c7ba29ab526021045964281c2768ea360d63c3a3158d2869f1d5028952523eaf1ba871842469207630096063543186102950df0c0610692f834da964a78a41f81b26892fba08ab8a7b0096c19836f1a2cb1c22fae1fe9e2b7081eb317163826b1d68234585146578f3f3124f41b2b32f5d7042fd107e30668397a2783755265e18a4579e10b3800e1d67b100f1b7b048a96d8e))) else (if b<115 then (if b<114 then (0x8a4a85930c2841b7643d6711f6398d0e2108c70d7f18c76f045711902896ae706adf8175e8e26d2422c2cab70875d8536e0e189af72d076bc9abd88c631806311155c830f5bc891941340195f8575d0856a0cbd60760f0e4e63b28995213aa6b31169b935b92c2a1be282153e1171fe0a1871c9c5806a08f60abd1e1a2c108a988858d50a294b01dd0c13e9ccbe0fad1071d08f0a63a66713196bbcc3858b58b) else (0xbe02451b9822d0971d9469dae50e1c2b184b6a817650671a1a2099f1e6b8804843548d284031402c1108c8530f65f8073894c0b08a0e054d2b53122b2cd1922100c1a05b6d0d719bc6d19045e03c9707c30874fb13bf30c8e9057cf014da89b8385a1a8d77219c8b838a9067fb0a23d8305d0787f1f55a079668ba1a0469e0c5ebbf5ab96561892f9947a1001878184f89686bf54518743b32e22c29e1e13f05)) else (if b<116 then (0x130871261ec948172c804e9bb3648fbe5069640159dbf9db0c4679b38f191dd8242293c7c8fc32067689e64d0048b0f2358c209121efb5a69030e4a46dcbb478073c58614e1ecbc08aee0a8c18f48712425053fd998f8807022e652161768971db06d2bf6c2256620ccd18020a2d84b8d81e066d0bf67c8b63d0d284a51cb1d18f016c08c5eea10520cb0a015d0af37d8c130be2b513bf2091fb2d1a73f14798) else (0x4dd03322052ae9a297334b48c1c531161abbe5a84de1045817217218e0007230b2a78b0acb8a740e716026edac6e7975ec845362363602718aa6d6396b21c5da0c4b611621ab1fa9517803613ba39e0d28baa1c1371b0b711c0206194c618a205b00f629b768cb1d086841652e1f16195b128f7f1026b8b35e6802aa83257b907498263281f13f1ce2c0102a68a8461eab50c1929317ba187b3f802a68e1d01f))))) else (if b<123 then (if b<120 then (if b<118 then (0x2469f1b7006a93443e813738c7fd0866dbc611ab468882409397f845d13b5cd144bc0424b3ea7f06806867449672a025faa4144848fd8c6a01845e821b8ad6b0942bd2ba51087b58c70ebf6478c5bd875a5085ec3c5ba0c46593171a00cc0f93b898c60e87c193c39b61f0b5fa95cd48d95e868fa82c63835cd0e2e40c0038b9b58d5f8991fda59d2026750c49a8e6d4ac6b1bca2b079c7896b19669d1368900) else (if b<119 then (0x32809cb10c6b90c585b2c968087e985b6a82bb9800c2f81b01770a873e06400016d42c6ce0f2538a0c280ab285671b063cb1638bd620a554c8146981278226ab1857a9a1ce121bb23112bf0cd1b6a6815a58b8e086148114269528e184968631e912e7802fd381ff140190cb2e813910011c37bd918888007400b622aa06d129bc891740cbdc0cb650e3b49e1c303bd702b4a82b5f8d8dd8b6f3062fa0629c85) else (0x4a156f2a36db041a2130c3190248aaf801ade8b3a4083c6980ad05cc486a150373087610915601a4900524221ac68701b826fb2560e9c1858317014895aa6f22865d8104e08c578d9e7019a00076f34731106b816303941c5b79af8993c89711a252391319892a39d13dae11c1e6f1b4605b25788a17e976cf8e2e63f1e7941989818ea8be60d7d8864669b346022c5aa9400b5ab1d3d20b3a9906f7825482b))) else (if b<121 then (0x5b49b0408800330c5e0d431153cc1d275291d7870a1020400951e102cd9f29a3a1e5bc185beaf00307a88c9888bd6329a4062a009a918c2b48e19d1a72ca116fa95250d70e1b5ac812173a1931ea04888ef895fd8b59e8a4f817827837501d25bab23f96726a9530842448b2089b16f241b31a14401b7d0588d885e817a430f8378157b9248b86417056f0ba335892488f80b0c720012f8312d7b51bf2615e3a) else (if b<122 then (0x749886f88864e0bb3e8e5e28f2abae0b20ab50815e5bc402033748e06f8d8218b4d03c88b1c7422e2cd3122d8a87b925db153fa172b03012f900ac84865bf64c2a51b0628e81146080d902be2205db8c1c7080781f68d1e5cc1a0fba8c1905442862b615935062a8b04eba73ff1b6e121b108f04e1617035bfb013fe8b1268c0431e86f09840097158d2a6aa273876319c5b28e58593451942a7980c9118b13e) else (0xcb40329da52838826e381fd881728f8ce0f65e852e00a1c6a70f3bea4483710076e3091468f72526401012f5392618d23f821630e0f6b7930846361b5e0a14c2984910b061106bc856421b616ab4af1842093a6f889ae86854865b5a93de9e263b608f89050156700f2020e10f926faa55dfb95229a1e5968a9a6529073e10f885066950108d9c804061d4911a7a26dd00a5606a318a7bc0b6feb632b0b2198e)))) else (if b<126 then (if b<124 then (0x10d89262aa0a38473a1367cbe65c38cd38c64ca663d838a02d773a967619237ae01396c12099868090f0d52a8a4538c1a005bb08f6911b497172942a256b0206051892bc25027d08a5bb2426801180aa14a1a6393c0dc81693335f7048d38e09bb38cc88b1380ac80c6ba373f69b3ee1e2c62f2a9bb1569594c0066096b4b8c33e1e2c9b72c18c25c832222a256281ab2817e116171863b9712b0c114080c59b) else (if b<125 then (0x2d4a72cc12362068858c87c06488892e10215299745a321a8d9938e6a12a68b99693956159c5f68d9970a73a9571d841b9bc18d059d00875faf13599c420c4008d1a5110a13ab470c651bb60eb94660869f9b7303c2f68d6243d48c091648c4ac0d42a8f20f3073a8f2e43a1522aafa005b294407123ab1d1bd8db8d08506182d0800feab0608301604736356651810c03c15029c7056d00d26db71cb2211580) else (0xe48303c86aaf8972f225f31b5d0009330c6ec215fcbf5dea22f98187e815b996592034f99c2fc350e2975e0914e48e3360821c250da8bae78d12f111551812805c69858e10e54f05b510f8598d67f1f60f14c91082ef026ef1b665376603f53f9f36d0e2090a1c89e9690876d205078a2b989b978e72c9c3ee082ec1312598bda838879f52d8f0172d898a15fe8239d8fa140164b095bd065709d4bf9c69f85))) else (if b<128 then (if b<127 then (0x45c0a3e78b0d1800730066f971f00f6378446d001de850c784697b16952d588b92a73e6e72e5fb888a5257b38f3241e247311a1b720c91b64072cebb74e8054c9b3d01807380704bd60c9a4280020f2c13385c6c0c631aa71daa58dbf222332191bccd0aa050e695801abb70cf9e25e84be98fa4d090a3bf29ea12441e0f00f86bb84ff8b4be05124146799e310a51e9896db2b6172c5ed8e3bd081b6302063a) else (0x2259d1f1011c789071959150087b0573a3871800687ba43212bd83361284a2c8671e932248609db6aab036d6930398ca670b0c193095840570fb930a735063670005088a1e85676983c31897e8c4c9972f7127e88e09d1271c0f2c88451e9f4430c2372d1bb111e63d1130c6f3105d6ab3bb0d9490e48e0030211620916b62d600bb3ac0f25e9482f027db8414d032219b20d36a43894931030f8e1a38c14d10)) else (if b<129 then (0x29e2622491151017563d6bfae613143b1876d8356bb1a6aa010fa970631f045861351c05417743a20db8294f066899f86a86316960f0850d91fbe3a96fdae21ea41e61789a0c6a91b0b48c7559819a995dd874068d2f8292e58b247241fa07c2e0c8c104509903dc0509402a5d839310759c084388c2be821640486e357600066a0b618062460a0338074905529802f19f70006130111030eb6f030e18acb981) else (0x260b6dd966d20735e122481f1b994164147fc0f338831db9c7508628f018058522bae121236b009308b00dc9a0b2326c0343a68206b96c22848fa0b501814cd833269ab2d893170f2551717780a3a839e88b2229113122c230e88c017da056ad1c62d3f7369a4189a2a5b326cb0c628d67906611155c2a2730b57169b6940f639b85893f3d3850aab9280ad1ecb81b8808508a5541f2f3b89c38f6e6a766505)))))) else (if b<143 then (if b<136 then (if b<133 then (if b<131 then (0x957887638e6c2a21129dc5c85b9f04682b60b2bd0059a56e01ae58b96a8494f8674623614b443a0979d053de86c688c28d137ee8f66cab64ea44060631438a93864efb5a38886b3365f9b45e4801a331744a965503607ab720901e9be127260ae342f4231b83a03685ab5049fc0171c1566e8503a93624895ec0a4fb9c1f69dc6d005e33e37e0d327162550122aa0182b6c5d002773db33085ef0646a8e1328e) else (if b<132 then (0xda1ec3e81668075d9b722398af9895f9246e5bf450842e68c2949ea368c76c346c316abc8d6d6806811c29b125b5306d8bb3da163459a92b827c8026f4aa6eead6d9991b53e56d113128130a9809d375a9955261c8d2956038d58b8033b1587209347811081702b0f41c8f64a066400c2540c461028db0674eac5471c4d201333871fb9f17abf4dd100278202713b40816dd243a38a1350804f83439023ca1a) else (0xb198483d8a4d100266341e18f7c8852cfa994d8a7050d1e224a240dc380fc0984afd0f66b02865317660d18e8fc658b754306970d13f276cd866a2bb698145f9110afb80a01002117bde167e70f434000928e17a822928f1cf3019e8a91a0b4509a8dc857372c1949d15e270110bb32868c384742a36a6052be010bd1c6cca163e0f743926391537e100128e332822400b1aa119a9846f3bc63d3e3182d53c01))) else (if b<134 then (0x1b128086982d3b52bbb48ed8a2f0250a2b45b88619d3ea4e885db3b41e011f2b2ab482ad5068c8060bb047729069d01683af4751f0e4126ac153461f0879ead00814c107c78b986037ad0f580ba389822943ca678166f3b3318e251151e49c0ee0a56f8bc148f656259698e5ca80372052451bbd231648b95bf0abc98cb4c0014a0a0088648e9e227371d18f0d21589c0777209766aa1d9186041b10eab07715) else (if b<135 then (0xb160a7588c6e68d6c688698b16011a37713a83087f289768236ecab5dda311b840fe92c890bb49838a0a46d3015138207f1a7142d6b5870859601580690a649c932e6987ea839e60071a3a6901121c9ab728691809307b7a8388a63809ba8269b895ee03c9e0b016a9b0e057d38c78c066883b18604737ad5278e259a9227b60f20c6669d427023a2151f3a65908ac4d879058e718395659e40d0d17f188c586) else (0x6d71964db6436871ac381ab8c6ad023fa9725101bc807707886a1ae37a9830cab19b961562671194272b18860f60491236be8888677235608893fb8e295ae03c109f18861d975260231b8488c9f6a49d58009328912bf1cb708fb090f5d40724c07a408950d1f0ea1b78a0268f8967bbf5911327084784075ec155afb74e93935c022119434d93ca80a8b9868988058b0f52d1e1b906874be419072aab421b14)))) else (if b<139 then (if b<137 then (0x48683477891d7110f727b0c8551390421083cf9539c06a288d6c00068e205959630b0628b182642608196b248789e0e1e32008a98be2056b6a72ce1d2cbbb2561c2519b124886239d55801289828ac056d3255830c506034fc134621b1a23816c3e09e95c648e5f5af5b0a01a0908c68560d944cd3d4628229f82133b865d114cd9f28d2217a9bcb30d68a9f7379772a8b16bb9c4a81b3f0d759adaa3868f78c) else (if b<138 then (0xa09086e3be4640e050937cb8254e164808ac3a0a5878f2302e202aabea07be380b790089f8774d241902d1760b4d49ebac867de8b5fe1f17901119030521c5c72d2db84730a76a8b25f930535078178161a9f1f7b6c25854de8d58a8e39f993119a634934af073fc1d2e12c8d8855eab452c01148bc3308f7830370e3d6ae8b65190606ae88a837ef804ab9f31a8023e9e9d3096e8275e3b20ad158ca0067311) else (0x12909638324e0933659a2e3ab1fd900c40773120bd401b6e84ac489251875358a4550031b9a0c80bad6037d28c71e315a3810ba8fb73026602f5e6044c98b0279e6d2a5cb904603095919530e8230d86c6e887583b6818f2150302085bc60541b9a249191e58a1cf11b820d8f58b70e800e2033410a204a492589773045299a47f8b101adbc008b808fa3904629046b894550035151f0b094656a4265ac0edbc))) else (if b<141 then (if b<140 then (0x18b9462707547079ab073420c0ee98bd58c6ea869ac0372fa01b71b5df013869799589816001cc3f12c9bbc58e963897ff876f2946ed2a6d60b60b985e98615b1902c9c1b38920aa70358d2940d6c32862a994d4121dfb41152d0a4196cb833268a1600d114a30ebaa6742a5838e320961951ecae0d24a8a6859e0988c9e4001a116710206283e3430d298047770967ba95b315c5606b648f8d18e41d123e696) else (0x4a186290299ec848a60372d812052a56b154aa88201b41e89c16d2414c913321c29f37ad8896c9b246c172212f09c396b03266e3d2552b20e2d1e51d12d846152a3d40e1a7100b6320021fc0e078320c8b6066fa0d2490518ca000f0878204145a36f68402e99841847c40c754815caaa25c92a8e8b6b6b069923158be4e899406120b080722196f58712c087c383313a32f5bf1a19410236c2488be0041edbd)) else (if b<142 then (0xe709c7f8fa958f5a2313081ec1a84af28f0a03619224182382858026390010b422612909086e00e6c0916013c3211b252106c8003c997122010e51f3ad063829b2e5a521e03aec0598f0c703a01d60512fab0ec2f7888f327000439ab7a0c1673dadb0797b87617055dd362f6ac9c9045cfb05bb145048a121950182e4a28b0be0e90e0b3ed112362c28b349bb08746184dd8230a126b726606161ae8b07c1d) else (0xaff896993e5e80e5a4004848c3450220b82249325cd2a5c48d5380a37c182d42a928844399a3e0041c716101898a9872c42e1fd0d9498f77d8f482881da8b610053851a174a83a10436f0c056029d40f5bd12b66085388a47201a168c6a4a767929437153cd1539f0c3102fbd200956860f118004a3c6b878390b53e97bbf8781c8e72d9c68d862d5381d92812217669085cb9651f833ac1c368996f5335d61a))))) else (if b<149 then (if b<146 then (if b<144 then (0x5d43b29295154b72590b24e0c06290b928e8a7ac73e196b43e8a30f281862100f1d61d10e8a68a3d520892cc3d2bb8e987067eb854218939610518826749e1d3b21089e7322d6b99a2f9201f182c3607baf837673e71e8c5811c4491abbf0d9758e6bf364d58c242b82058a86fbd6212e43a17770ba67c3c0e926bde9999f877a8057898168c985080917a1766635877315dd915b6b7185138aaa47b9011aaa9) else (if b<145 then (0x682aa51b11139363a89f3062c1c39a19b0d7fd842492589aa52e1390e78f41690416041e28419f01af3859f70f77e056b73f69e252dd060af8f6c0af572134a9083b20834f9c41d9b220894080d166a20ea035550c7680738b0c2dea2221380990c952036b39567da29248288e0759f214ce9a258861423c27b0a234aa19aab76a837f88b3121b2f12882d0d5c321c8b015ce8a5ba205371fc9c0c37d120478f) else (0x271851f11c1ac0d5d8215bb8f4e31a4be8925d3e107816c88f3b885ba1005d9ae5699c1e6af11f020db9aa1c8b3990da32869898f819002e3b4c540cb9b8b29830a9d8a9f60e5f12c472862828b2318222f97229888078633a160ab9c61a0b5d52448100165a10f60c8c08c7b5086960424bab116816b10a4649b1b217156179b28b74caa0e0924eca325aac1be3aae9881e60b69e8a509802ecb129619c0603))) else (if b<147 then (0x661b92b2962258d0c4862730c2729d602945148d1f38b17e04139229a88e6ab3c66c8704387573800eab7330160a21f04d99653281e11b0fe146362c5dba35a9843989c710b721b267440d5e42887901638225ff303c9000f482c450bb9a8aa7c00bc68f1ce8fc218e5ce265000f0e12d8738f7732842c0c35c912851d1bb30ae803a5d0847d9c3a197277b665cba5e903ad40c69e1728393b5d803f41031488) else (if b<148 then (0x1503e9ff8e62f942193fc6b05c3e07c14053c8851fe89116973b40113fa71302c2e53823a828911d6831422814bd7b195f0e48d0e1a81d24895c2f097e28567d99c7e8db30818a00074d1924e9e06598c9000a3f050850b5741629cbb1fd29152866ef3f5259641a0530b3f205979f6836af2b60d092d80aaef8c8b48f2f5112750915c280841e02a913d59f062086592d648836119b60dae1ea880bb9d0301a) else (0xba60266c001e4a4146b7b4f058510e554964e5bf2d4bfb9b009fa0a48f8401bab6e41f5d6202fd8524b924f6096f1a31b73181d8f8080b6ae0f6033d1719106c1887c963f0191bc96c8c0b62fb040e862c69a0083aa1c0387b836cfa12b6880c98fbb305710aa3710625781204831baac09a860688dc5b0a6f921191baae1001c19376a9873faa734a55ec273dd041e90b1af175540f440852e5960a0906a6ad)))) else (if b<152 then (if b<150 then (0x28d061fc80b73879b6017b7876bdaf5a90523e3e19d29146360cc80aa005400191c09912694c860b875b85dfac758282e38e240811c2b499e0871f8e6438b2b118bd00ea798f9118d6f004601b22528a1ca299fe81867b86a00c740ab5f9065109b42603223ae1ba937143acd000a0101847070e424b4d034a606aed8a737006da00208baa4c8773aab3ab8137c9923a0b01b0b4ed221c797473910f5307ae0f) else (if b<151 then (0x3048e2ef9c9e4878a42c689bb684942a714215b41af9d60aa93cb0d2af9072488711366ffaea840b6e91f615ad5789b29fb4caf04bff03b948f6108b5059d4e708374111908ab388e8f689703896efbc63a0c210264590d250bf73b0b69a021bc8607d8fa848715433bec019d2842e806291086a8956848e5ee3e453983ca9425939bbb8d9a38f6662642598c88822b0b81c9ab19f10186908820f369972b092) else (0x487841c9b70fc898ac8e73da524a2114787a8f02c3f831aa343b98d3470f5c7060f1a1a630422c081f8ad10e19c47011ca990d00f0831701a2e25f807a08b1d4b55039a226ad1671c7432a5258c1c0aea320c4d3131972d06a81ab805aac858c2848848515b90c918e89d06320081c6042530195c8d6abbb9e0034171d3700128fb8205096b9225eb174ca962428e86a087482768d354500d340010d4076e108))) else (if b<154 then (if b<153 then (0x4811a00bbeb1d8b5560aa620719c8c75b247290d6e02e675872749a7d908745124ef0445d184021b0d98f0bd978de8e71129652095688817ba7141aa927028fd0258b1f1e5a066d1034d8a11d300da9c07b1314f0d67eb616dab2c930250a200482892183ea052ab10c9f869620956a1d36693189075499241d8d4009f69c15511093331b30902002962bc8b0ac11a890e632282c51f2783d1201bbef86b1684) else (0x89d8c763036301b4f48f3891eb7c05863b43db9e718ba63d98b7f878760231c1b7211c601211bca715a9327410044886bdb85f3035d5102790d0b28008404a2e0366c21572801f307bf70f651aa35f11b5889977085189d46007bdd17b75846e9954e78abce8a6c99d2d00990c0a72b1a191000c11d0811f75ab661f10252321ffbd6df174c8823020d10a120b03675700bcb8334f841cca10103672eb56c40f)) else (if b<155 then (0x27d261d51a5d8874110f2671e259938763b6bb856a215603b35968da658e5438d3b38d1278d00189bb700961876a38c419862423a8a8886689a60b2a4c8b24680730b83769106379f2cea19450285e0a632925b1a05b03bcce8f9128509202bab895bc1a534844d918365852c4a50ed080cb83948867e58279f8618e0c175040ce095b01f2ed2b2e3090a0068d68e273189fb89609197642062b8ec34818a106) else (0x209840e28971f975f98c40a079348f89f2a717842b281c7288c328761585551810e4b27d5826b0210ef8eaf48875ea17192b1ee02631295edb64e3806490930f9525daa6ad395ca256e1875ad064fa1640f0738d856d41724e25214a4c040587f9927f07b95858f48f72ea73759025c0aa298b8978164a33584133779f8e7096ca006c3881c11f6b40f4089c3bd9a35180177ae0a9b26d93c18726ac90e7020f))))))) else (if b<182 then (if b<169 then (if b<162 then (if b<159 then (if b<157 then (0x163bc0751090a09435851f512c4605ba5056b32c5f2bc2a11724b2d1dabe9318123501b7206867342a23f21c8163c24489922211a16b349ed8370c044d70b3ad133108e15e8f1e718748b9917069080c8c48f609ba1fa3214e3d144bf0a53809b94b018ca80066e8b44d48b1f2ae4b99633c9a5ed272771310d0967e1f52a0143f0d71998638ac3bf031a722185ac4949e21a03303221e52512e151080a6d5bc) else (if b<158 then (0xc500ca0d8e58a182a29168c0330691903053cb91ca88c894a37171c70b8dae504a258b79e016fe8c62f840cf004b2803580372601717aa5d8328d4145970329a0f894056aa2ea81876753c3a111342183068b0d5070bbbb05717bfc8a715bd6b3a8c808038e9028b94b26057a4876f43b62b9440a1210ca1056877d40b76bad5ea083731c0fd800e3a6b200f67f3545b103061f287b4a440c9cc0672fb92caa8) else (0x672285d1282a48c0af0f53d0b4a987312ac0ff23759974520033f0628bb3a7000691914b511262028920525e0b1cc1d2edaa0fa860fa346ca344ee2b1873f1e01100eaf6922a66c1c266933941d0580dc76852f08318c8557a14423032ae175629452d9f2379c6af096430661a253d89bbb88a51d0c4df04413898d282619b63e99381a082aebb5e8265e73c0c9067d30b6c42b5cdab4f6154350b3319d2e712))) else (if b<160 then (0x4221475fb974608560095300b18faf7ad827640f3f28c273261621b5b0954ea17b718ea3d0d62faa972835a68050a891d23823208157038df0f2959a12da6757271e6219e18232f1b2fdb21f5981de310eea48b200844813b415cc10bc8c8f719ac6f10e73680092936719b5d5892f59810f167049b66fa23cc8c0e90a0d801822836ac224f227137b28982163996110260f41a6b01141c9c7ca0c765367390a) else (if b<161 then (0x576184c78f3008b5cdb74bc873d91133d058358579508608391caa71092d7ed877479f1b4190c714004119b9095af8e1a08338b99694ab3e3051ca3bc37876afb45c6361fc131940abf10dbe082a8a8d73d913af871758aaca854f6814b70a9b48e731931e93719f890d313a69849388a6b6356392b2d7091f81e057897df872a6bdca584c4e017133fb9903812054ce335863c27a261612415684655a85a102) else (0x3861920bb3cbf866e28b6ba186a58744e00b428aa2a0c90781616955e7803a58115810bc10e72c0741e1e7bb87616be4319f25e17103b03191d0a50db5c0671a866e5ae4aa092f48b6c30521da17d788603145eb85306343058c29db6bdd9e4b08e47003a48071bf90bdf911249b0410a8ca897343d335140f49f6182b81f095d5be4b30c2d4160a68ccd28a5790e2ea063c91322fb367b861d59017b36c0d8a)))) else (if b<165 then (if b<163 then (0x9aa855b3ad2d2200860caa700946816e4ac6610265022675b5153071069976c9a5db2228b81bd28e2b5aa3ec8f151306af88513132c79912797746347139459b883d09f2ef1e1d0ad06c0cc468d59cb630b2ea5e8773c1b69a18642051a7834c7082371b2268e5a7065843c3799320d8113eb73809e2078c00d1a871be59d0c24f1e1ad8714c0357481c7f0c8ba8071322bee8b7f4055b4021aa2010a0a04f04) else (if b<164 then (0x8ad0683b8f5a11b1d820b7e03992817542a6f9860c49784d053a59f1ab12920837373e6162b52c9225ea11ea3f1a109009a26ca862af05250941b3011a8971a3a404d89bdf842b6309d18d87c835119a35e0d1a18116500779847662367d82369822ad1826ebb20037a4f099720d771bc439852950208f1c5ba833b21e07c86c1b88ba38c6801a67f8e6381533e082e4172a30b27534220a11802fb3808b028d) else (0x298b21e1099240e18d13cab82bc28b836010b58072b054869524d0a1f61dab903a61098cf836bd0f5e22a592898e286715346be233ab9e28e2727fa0aa6819b70b8610414e8fcd080ca90c7878a43a862161f180087270f5b79e5829a49d8ba00045c19a5c1004b8063e987be2ae76b856bc0062a8310724300912532b15b3ccb00e63a903210d5050c97c053e18575b896ef8a3b8053160f6f18d6b83e2c108))) else (if b<167 then (if b<166 then (0x4ee9c2582a0b4060090ca260020090186bb1299ba35078a086887897592975515630b00b9b98a3af1bda34e9283928ebb5831e70416d375f2004ab822c0812ba8523fb66e23a3370c72208212b41010b0c09f82c8eba58ea5f8c92e8b00202b6286667bf2321d19ba99790183383807087671374b035d28e48382411193229c31f8d6de8017f0a05b8969ab85f18148a823ad9e1710d10abe0c01d05181b870f) else (0x63f98b0c0ead3817103c9fd8774d096d8286e50860f9e3d309220ba8ff00896a31f72d1be1c014a42a60902592bf78ac51876843e6ad9e68c893a78ac130d5b8054bd8d1ca0c6289800f925d22b30a2f2d32a012297522e6812c1fabc19e2f16b18b920c3d99630b1e02516640924e4031828709f8838384140ae7b302206256220052b961d98386e048608d5e7b95be0936a982508021d201bfb0a708169f37)) else (if b<168 then (0x4ef1126525635066a23b46f121a8b316a120ee330330d5e7952d5a92ac111f9a3c6082be32f74d90672111b6a8b178572da15e52238c9509cbb07f0e0ba0d02c03aa5090d99c71d0352f0b10e2b2b3a8163189ef8983c8b244982398f81486adb8c98c065aa0d4d690401133fb96991866aab1211b61bd0606e85463973d88323fa96d100664803630c2df2105b02b580191e82112119e80f670b76460a21695) else (0x74166bd8e338162e1a92ca3170e2f6a5a3598062a0a2b430b007083c10c2e5b62a01d9ca03672a22faaa031899858c5bf2a370902178719cbe17a3313d0e02b8e53c162113d1938fb988f1228d0a317ac40ca9a047ba0e29e37a0f0882e076f2035cf9950f83074000051e7a3854c18a2d49b25c2409c1b681ad305b56d0ab34e8b24cb80152e620282ed83158960ab3659e2710126c3307a930a867016e51d))))) else (if b<175 then (if b<172 then (if b<170 then (0xb280e00b25641313b11a19b133969a3d90927eb276182681976638b639042dc0a2ad0eaa781757ae3f4832a7aa2352a7ae85652272f3a2672875dd1a4d71542e8224684b490d4ed814450944316a4108850026d8ae618a2609280b98c74d352c5b72aa996de1861ba572a171123c75108739bb4c80989288691074d883180b631e159b2034460914c849178b6fea46ef9533a9273f3d2b90417d2d45a160d48d) else (if b<171 then (0xcb88765c2d87e0672e1d6d78968cb3675a760f3143b07136bb71f1f6e89d16f095beac528094d40b2d127266271a9829548860a8c5a80739a0c2ad876ee344401e0b31ec1d0c1f29b05c923751b9e3826b9b25a0974161f16a981698e2b60c188853e6082cf2d22f8d0e52294d0e2d7a3aec883eb1a3c0812c68079b8133f9c0a73c014bd6328b4f88a1399240b8a245ab0d68a9f00f7161d3c11f3871d5ab87) else (0xbe42d5ae0533b0f2978b1de2f0261d65e0729a181f32a6d3b363f03613926060a000917c58a3111f2f504c3005c0c0e7af8e245b103c0e9e98e8be8b9e50d7bf0d3778f1d19817da3b5d07acd8e967025eeb13c89006483a910d74f04299ab207970e6a8abd8c01b2daf20e8570f5dcbc5d7a74d9084be1f3d0872ff2c253380078e0961f6dc8d30c201e78a5b93d1c0b9181b500d02a9a8a9f5844980b648ac))) else (if b<173 then (0x224061f01a29b9a2c38714f84a8f889c30873810736026f40c541174bc9835407aae8191e09769365e49a1c4aa1be92739a56b4a96a7a76412807f8e89c241da0487d0b7e90f62c155e03325833ac98b8618e1d9bf622b65f62f3a80018d8a66d201f52446a983740b0be8ec39875b50a301bd14eb92c41ea4b048110b3d41420cb615a366b8a95090d139858f0856d9846ab814199f1653f114231042701e80) else (if b<174 then (0x5fcaf43d097d70424ca41d12b1088000e36a4b815990a76d0f3db1e1451410eb901789a520788d177bf82562833dd9f2d1ad95b089550e3d2982153611f8d4f80b72814673a055f9b37f1f7380b6ac8159a81520914f71c1a202988076e5951fc03b238ba3c0e9e90d6ed064b381250310081887b157b18d655803508e1d1300012cb5a8674b27520012fa8b7760b67321393992e8aa164b5775197712667e3b) else (0xb6a0312ea610bad25b3719303733b53d60e719857c5026873063c1419b3c853845d4952eca00f9039980d89092148ab95d83cc7066be188f28068c2352187416863f3836f50b4fb8645a8f66d812bc3e1e2ba5e88c3f9952af3e290398c4043db0339b0d1d5b75c6b93850315c0899b0c86787a5309716aa39f8f87880089862cba0acb829a80994b81223152d2921518b1511c0bc9a4ee003aa8cc7480664aa)))) else (if b<178 then (if b<176 then (0x6d1b42aaa3295257518f643129138f4d230b2e0ca35805c38432508320110adb93650c39d0c0bc1e66d9c3a3140f02a02506c6a03b0f877de0666596c100086b8e6941a62413166bd1c22d74709228870e49c0d89bbe282ae089ad78296c803938303209c8e842b69da09867c18929a270ed300671e69d292dc2b0dc1f9730494a0c4948e25c159ec0459c942ff00250241f5aab1b845d8a22d6890780c01e96) else (if b<177 then (0x2d0be22a801ec0473e2e21c170b596af88a46e87323852f724174288ad807b98317b180b1342083d85a0c71d1f6a5916323742b933a28339d9d39c8d3971acd2015f4064e181c3b0f6df0e4cc104b7941021505b1e00423836862db3d0130c6bb3263721521030a604b4688b3a07ab985684aa6570d1bab90ff914978203108b3a81a950f4b39d44c9dbd3bdb9a09a718b19800cca0d7928c496152ebac1993e) else (0xbd48e73b85650a13bf9aa450e8e80d68a146860a63a203f88524a98223b30be957a70c744ba506844d1b43091500c82994008e8806913b60cb859d191bf076b291624960a8bea9f82736ac31d082cb060da0eb410121ab71d79ecc68121a91745961090107a02769b57493755e845269b2010c2b53202b180143988e16677ad52c14085132061b18b286e2275ba1f51d8a2f9072580d1bd151a8206358d5ff9e))) else (if b<180 then (if b<179 then (0x35b992de22298a695183204b2a248a3f98b267b10fb08a998c5951d09d8e81f830f0a00b7ba8650a8948335d04204021ae0f1663609c9f6b70733c092b6ab8898d5140e32d83201381b5b7112241ad2676d8e652ad473882888da0a0d1ff931cdb00f8a26d52c2189f6470758c1c4e8214be9a2c98713f971373c1022900f14c2f8b9d5864eebcb950393d828aa2d7fa846c182154ad0258c90a874d18f1be80) else (0x4d08e0f58f6ae28513031d8ac0bb35cc30269f2e5d4a03c0097358f58e064769118b034cc922a40134d1034c862338a1da3008d086fc2c5b00948f0d165bc8fb0554f964090177c0d71e0b6932438a923629b3240a2a500bf88178b8106e1605480bb905a76022b0065f0083be921608108b842f393c3685991085f50bbcb0bbb108a99005eaa06c82a52e014cc0c1af096a98e5a8115460d2453d0f9b20b127)) else (if b<181 then (0xb796aab8871fa84940a8b7006e7b56a3a35d2b95ce9fa478c2740c8630d76fb96da8f2d9ab6baa86b20d76aaa15b238992f72f982fb0eade0d49a092138a1b000685a6afb0a6ea2365d0c61811609ab40395288361dd26c9588c660dc0a8774f286b7910bf1ac4280891066740a132a9cc60993e026eb8323e8470a893708b2ebb511d080f107a11014b2002d231173826972163c8f06e936dc1b5fe245e01b) else (0x92d097309b437833371f1af8f42d133b01725708158a69f102759bb5108b205381519789ba58090d4e9a54c204bdc1a93b053fb0e3688360b1670a026b52f5c42e31d8e7a9867500f723223da0c2f0052c53958cb1542860641c063805df1a55d043498f0b697b678f6670806797bf18c4498f28e0309e0305c095901751e8b2f89812a88c010591d0e6cbbe69b315d02e68f3d24c207788d3c09c2de0a19009)))))) else (if b<195 then (if b<188 then (if b<185 then (if b<183 then (0x9328478f0b6d7903f20e2713cc8982676aa61f3aa9b8d9368872084575053c700336150de968a9289588475c2d17f8629fab179aac2c061f8865941639e113900ab1f876efa767aa554682271100f7048b68642e902c6021a79a179250cd0d3641d319281b62815bb202d925d3960bcb9b590046f092991025b90162a708a0c162bba548838a802b3028840e5e30958d00080974cc8e7868e5ef3830c159608e) else (if b<184 then (0x593864f98d4531f34717309a71eebe772876fe942e1b65fd292fd050c696a1b8c404803979b2118e7558c56e8e4ed099c4828270e5e59d4f02d306a776abe6adbe681005328f9048f257ad18c2e04998be30516dbd16392161bf0f989b8e8e5870f28d8cc07800ea3b0ac307a0006099a174b6ca40527da1711b900fb300288635964b18842007694202230015606004b19dc06325891ddac6fa20c4885bf505) else (0x4e20827a032431a0eb848d21375a387172d394842758813ba8b3d85699925598b85809307072c891241b71861db290a70d9b0fd270a48f29a8a2c495170aa153340a193260066f23e5c4bb5b4bcc410478d04770873e81d1aa935c1a5b8f8a6ff1e61481003a5afd83765102999e198b300da890d09c310d27a876ad2c5c213a5985a400196e0f73884610115c7a01eb965f289214837ec8647e012a70825a94))) else (if b<186 then (0x12a128f602551004cdbcb6903923045eda530aa620b331f31b8e5815b4a11178562198bd5015b5243391338b183ec1e3d10ba9e835dca55b2b5a518e8a38962035378011662588f1068fbc4889c3251420d0304302abc0b4c5082dfa71ef100ffbd92a0873c376ee9729a906c0276b50439080b7f0ba9f0e70eac2c8a02629c1cd3c05280956016bbb85960c219a21f4b51298bbc18d5bfa95889d06695b118f) else (if b<187 then (0x2410680a843e5912dc9822093616194ba8d4ad9237a08cba0e746ac5ce3f28e9c224191f49170f871d099b86088c88376dbe6daa62eb31cb082c5c02585323888e1a9b40a4b1add8c5ea9c45480ae40872e0e243aa1e8ad00b0900829b858340a933153c273a421f8011c9706b0f2dda4941056c2084f0018350d7d60c4a482308a14558a6e4961aab277c8e0ef078a72f5479da6c8065c064a68222ca70e08c) else (0x4ac990420d63b1c4dc1528dad1cba1a56866a7ba53a894d11c4c6851f0301ea2fb7b06b6c0776ca170483693103b09d1f60876987329000ec066f41666f12589132bc19a7384a46019ff0f5ad170ac0b1fd3c1e13918121b74037561311b996641a197a5b570973b1042d8d0a79707c095ff204cf1898e8315cac150226ffb813799a5589660165eb3d3d69423033151a57703366eb57719d750294820e29183)))) else (if b<191 then (if b<189 then (0x5e6b7299b32920b1e4b5104a43b68e0c5003601a019264180104d0946b0d2539c5d48c10f29bad8a58e8821eb33ae880fc2cc828963e9a4c00d4380485d0d733201803e158220f78a018803d81a3152f268ab1788d98a8926d0ac9a85a1e073fa8a30f0f271970bb1fc4c01aca0c8ef05418162890e47290131028918d8831370b035d2370b2160220476a0c5fda85038824a3d91f0088f80607125e91352a19) else (if b<190 then (0x2fd93a980c2af2d111afbef03a1f856891a3052719fbc132067170550404272a51c80bc090c7e0083899b12cb6c268d2ad3516b0eaa6076f13660534c7a87a98887b2846a631998847f70f66325c260467f993528e15cbd6242e1fb360a591caa007448b66ea75049f754b8680b8593923b906067890579ba4a096c1bd669861c2891c21017085a2e8574e015ed033141c2a811698872a98872b966a0aa61c00) else (0x41a91138907043c60c29218042140f1e69501f17277a02283f61e098b40d8723561a16602241b923066028d78b2000200b9abe18c5fd0d5ba3c20f971483aa04008f98d5e32d24f3a1cf816c0b9548804930842b1b259161ef8a15c33a1b01a0a848440783e022e51474a8b6f0a75868b4ea064599b38d055d01b220091aa802f58a25d8a23e20227a9925055dc143a49208a16aa28f7b88c4ea2b4d80847583))) else (if b<193 then (if b<192 then (0x25f127d18676a2c3af102e49818e29271001db3104f9697d866ae343f2944de948558226b9312d096973264f012dcb51b2261832f4fd034420e06502ca60cbae042913808383c620fb8a807e68b79e8a7123f2e33901982c9e85afc0c9768c6548e21709a7f8f36f92323130b01a62882aff0126d10b980d8438e2f787b750f1411b8cc0185f0a6ed88801024d299b058b77f05673b92ec0d19e327f6804958f) else (0xe30e0bc87c3d068b00956d9239f1f02f16a25047980460a291a7b20fcabb27061711a00c9fb22005f4b10500f8f80b423822f11f28d98269aa0901abd38895e0f90d87589986e3286d2945a624a5f006368e2ca8e162860ff0d05d832efbbc00869a0867528e279822658315baac168271e253329524d2d11e0c63f873cb1e71c360f1335e53e20c1f1d489aa3046df266db3cc2c8f6b88d6852b5079c32595)) else (if b<194 then (0x45c8021bab2159e767848a80e1beac1a486aa90f3719414f2cc4d0582084031146e8061ceaf6be083f6842d8962501d2712605d9e355050441858e9f1fb88180899c98c9220959da010e93ac2865e0272e52821622c95005b2251c9389a18c75f97731ae70f2229f0c1b4301132b8a18381080768bb680002ac2e76c136938927512731322af1d73012c0d1321418130ad9bf87689a86838a5de8f2de104560b) else (0x4d59704719c830aa41867323d64a8b5321051b8a263060698fa1f038e68554a8e14526c5f81b6e020199bb8c0a7329d685379750f20e900db00afc81641824821846991224200d69c019acc29876bf9f6a80b2a3a74690615a8d534074f89919d06117919c68b9678059f823089d23328c128962e02581884240a377002cdb721b94695b5659b63ef179808697e0c5bb90580993f180add015668c5010fb4f80))))) else (if b<201 then (if b<198 then (if b<196 then (0x1ab33620855cf1058f144ba04254283d48c1eb21a828a7d807719156db803e79f1409e127032e7012e60225c351ea9c7193e0a905b538867e915329d59e0955d834521534b0e123870758c03082702ac6ef056a8215cf2a3be8d236031e536982017348c5e8a75691d2e080bf58aa500738c021c42c1b1a9b40068938954b025093f76e9b738a567a3d40c1e2923471aab5a1a7693be669145de395d32773982) else (if b<197 then (0x63b83622342df112812ec1f81291b117eb18698c7342d62cad5ddb05820d5270320f8d73309205a9214b56ca276a22240d11069102e1100ff3f672bf392951693b0f43714f1114211103936be34357072621e20b984e4b60a43d9d80c24fb019da867b3a1d8b949c8541f083678a0170b5e5a94e50c4d43346810414141cb009eb0239183216a87f7806983c22b839738a7418362d0225009adc839a30f25895) else (0x3f190b9d0888e945ad8a54906212061d40f1c91e959857738575a060c308a6d079d78b7453a3821925ab7175261683157f0b75c826d6b957010542115c7895730333a0a02f816080d5cd832280b7be830052161b8737f071400ac1186bd80b8cf067182b6b51f6813e612bd5ed9d50f15a280f9f40f9ef089978f605a145f932342e684093230aa940d1fdb656b064589c1180d3d802297162968a4a70c1d002))) else (if b<199 then (0x8098a5d4230d3800b71d1dcb55548d6c60368b8e6078858616006a760ca036d110720ca060f87d956fc8135a9dc08007dd83a2b8dbc48b785042e2b02b42f2049ca97838aa0c883966640555e059d1066b1aa6008624da35640a40f9d0878f8b28d2c7b00c892bb406b888cc6300bbd822eb0e2b20c1f92cc998687a0f80d0d6341e2d3a71f7120ca1ab2f83a668364e1a64d80567082761cc038a8038b77503) else (if b<200 then (0xa91a68b2b1e0997e1066ce2e3e2088d8001ab010e88e67b245ce081cb8506e01bde8a5d9334419d1540f7428074033894212c720950016dbb964489610373ed87c318dc15888298a2d0301ec2d1b8081992068a0a62138c9785978814709132f922723c1853c4a50b1a42c69b094d00750c9283d092ec831bcbd57e842cf891d68a0b18b6661d19a306fd003559966a874188a36716176ac09d0300f2f9828d) else (0xa9d02a1d81b9e0a68eb228b0c10a32b6b0f724066733e5e71bcd585897066b2813cd061be287858f5198a4cfb23a20b6370443f8d30c052c9a69540756c022d11728f3f166851c4b7ab20f9f3084278832f870c58a5419e738ba6a09b531ab3300a24333601000cb9f055015baaf388132c90904c01b90874ad8b3e61032c9b80b817b10856e9b2c71d9228a9120a61a8114d361fc9961fa73e48037a8a63485)))) else (if b<204 then (if b<202 then (0x5d79572d345a42442d0e4c28f20b210f5a86d49e8c30273d28269835289f4e6271ea020e621aaa8a9050e8e786672044bf024b3150ce990460aaf187a00822a83755f8e1810f019174081430c9cbc9056db954929e40a84162953eb867509565110344826bca266da138d163010f2313d08c0e0229802189b3b00ab78389ca52183d1fe1c1b6b80d2920a188824036d09962e833df169e20c205121e72d1b51d) else (if b<203 then (0xc60096cc086a8811df101759475a1120ba21cfa412f3346f8b9d38125b8976b165b329574090a5b29a28b741af5e1a62f7be17bb05e43eb18029b6890bd37c85879930f92100801846389714a9010c8b8718239a8f11d8fc7b804571f0049b8758c5de183ae9a2412621cb41d93f8960b6462a43f9b255b675b0f5ee132289c1ed3e1e9a3a8b077938e687195a79133f8e2fb28297a909d9ec730b7d20f60ea8) else (0x5a198b348bbc7804e0846b91535a8f2eb84226312e39928d324741c3e0982c02b1362c2db90b54867d98d7810c610ae4ff060581f5d71758b337818f3b29b3628e2979328a07bb1845fb9fc480162e1e539831cd9a1068303e88c8100b480283000707024860b45982cd500a640e737bcb55068b4a72d19d1c63a42a063ea8230c312d48509f386fd8f0d28571b2230493722a55b39a584912a1037393032b9a))) else (if b<206 then (if b<205 then (0xb840b6f93133f121100d02d1221d09696a7858846280046e9a228aa6499e5f9aa43c803a98d0429c8b7846363d40e1b12292cc28a9ba0a85187499812ca1b670a4287a9521152c73c291a3b3c0bab6809c00e579864631a7ca8966e1d1b39212e9615b06758b06452cc5080687842d2aabbc009470b348858a8a2745be6b3b9512833af0036c032a41443c031472a5f2aa5ea152fc030871ebda0970f1962737) else (0x5c91b515963a48226d910cd8c04796bfe08b9982a15866aeb34578e28eac01d8273201a68028713774336709afa42048a12d81a89489153f39b1f6a76308a1f78f1210d75500a0e8c8818c219051e7b70ae9b5f4864e8832cf050c08268f0b57f8520ab01548567c945c127b0503714120209192a86549103fe9f3ee8d72e90424881db2502e1e615bb53b0f30d002fe899f90697f0f8871b5cc934f69c31380)) else (if b<207 then (0x6f0368c18635a744b840a20e890093100301091c5e8949f843bc843a0901ae320bc073e58c04a08af10f90b81290ac1f4378260c2ac8d1febb8eb0c672931b01c65a140451782e8e6828b4429a2d7940639bbf9828af0b4b1946bd190f2ab661946113235c82318952a4a5199b5b080c964838a6266c627184a2a858f7f987260aa91c067db0b6829067f021b5220cc15712056bc1a62933364003113aa860b) else (0x5749b8958d7e18759a1c467854038d44685b5f0a6110bb2c0528b261b9871b202ba8097a88d4c49740b963db8a093076f5291fca85149020017))))))))) 20 i

def r2D0 (i : Nat) := field (fun b => if b<2 then (if b<1 then (0x3e1ece270379b8da6c359a8d26833998ca6431988c2602e16c9a4c259289248239188a442190882401e0ec6230178b8562a1409c4a2311084401c0d8281208038180a04018080200) else (0x76bb1d6ea74ba1cee672b91c6e270b6d9acc65b2992c863b198ac461b0982c05e2ed62b057ab95aac55aa952a853a994aa451a8942a04e26d1a8c45a29128843a190a8441a090280)) else (if b<3 then (0xc6e2f1589c461f0d85c0e02f771b85bedd6db65aed569b459ecd65b258ec561b056e9b4ca5d2a9348a3d1a8b44a1d0a834095caa512792c8e43208542611078341608fb78bc1deee) else (0x1fbf8fc3dfeef6fb3d7eaf4fa3cfe6f2f93c7e2f0f83b7cde672f95c9e471f8dc5e270f85c1e06c75faed6eb357aad4e9f4ba3d1687419b))) 9 i
def r2D1 (i : Nat) := field (fun b => if b<1 then (0xae56e9549a451e8b41a04f2772a94ca24f2692c92472290c82390d85c2a130883c1603006e32990c76331588c360170b64d259289248239188a4120070360a048200e06028100600) else (0x5f2db6cb5daad368b3d9acb64b1d8ac360)) 9 i
def r2V (i : Nat) := field (fun b => if b<51 then (if b<25 then (if b<12 then (if b<6 then (if b<3 then (if b<1 then (0xa67c4299e90a6784299c90a5ac4296a914a1e05285814a3e0528d814afe052bd814b5e052d5814b3e052cd814a5e05295814a2e0528a814a2605288814b1e052c5814b7e052dd814a4e05292814a4605290814b2e052c9814b8e052e1814b0e052c2814b06052c0814b6e052da814b66052d8814b4e052d1814bae052e9814bbe052ed81480e0520181482e052098148be0522d81490e0524181491e052458148ee0523981493e0524d81494e052518) else (if b<2 then (0x550a41526905492415331054ca415321054c24156e9055b24152310548a41556909bfa426fc909c0a4270a909c2242746909d1242748909cb24273690949a425249094ca425309095ba4256c90948a4255690aeea42bb890ae7a42b9c90ae9a42baa90aea242be690af9242be890af3a42bcc90a64a4298b10a62a4298a10a6224297090a5bc4296e90a5b84296c90a60a4297e90a5ec4297a90a5e84297890a6fa429b710a6da429b610a6d2429a29) else (0x7d3a41f369074ca41d2690749241d2310748a41d6e90750a41d5690fc6a43f1890fbfa43efc90fc1a43f0a90fc2243f2c90fd1243d4a90f50a43d4090f49a43d2490f4ea43d3290f4c243d2290f48c43d5690f5ba443b8910e7a4439c910e8a443aa910ea2443cc910f92443ea91062a441749105ba4416c91060a4417b1105ea4417a1105e24416a9105ac4419e9106da41718905c7a416fe905bf241702905c2a41708905d1a41744905cb24174c9))) else (if b<4 then (0x267a41ba8906e7241be4906ee241bcc906f5a4197b1065ea4197a1065ac4196a9065bc4196e9065b8419b71066da419b610662c4198a9066284199f10667a4199e10ce7a4339c90ce92433a290cf32433e490c5ba4316c90c5ac4316a90c67a431b6903c2a40f08903bfa40efc903c1240f02903d1240f18903cb240f4c9034ca40d3090349a40d2490348c40d229035ba40d4290355a41f08907c4a41efe907bf241f06907c0a41f44907c6241f2c9) else (if b<5 then (0x14406451139144464512f9144b6451339144c64511b9144664139c904ea2413e4904f324116a9045ba4117a9046da4119e900f92403b8900f324016b1005aa401b69006dc401b610062a4018b1006284019e90067c4019e10bbf242f2c90bd1242f4510bd1042d2e90b48c42d2290b49a42d5710b55a42d5610b5ba40baa902ea240bae902e7240be4902ee240bcc902f3440bcc102fb24097b1025ea4097a1025e24096b1025aa4096e9026da4098a9) else (0x14136450539141464503b9140e64517a9145e2451669145924516e9145b2451b69146d24518a9146224519e9146724517e9145f24516a9145a2451729145c2451ba9146e24518e914632451a2914682451fb8147ec050ef9143b6450e3914386450e79143964511f914476450fb9143e64510b914426450f39143c6450f79143d64512b9144a64510791441645117914456450eb9143a645123914486450ff9143f64510f91443645127914496451039)))) else (if b<9 then (if b<7 then (0x149d60527681420a450809141ba4506c9141da4507491429a450a491422a4508891425a4509491421a450849141ca450709141ea450789142aa450a891423a4508c91426a4509891436e0500f91403645003914006450079140164503f9140f64501b9140664502b9140a645013914046450179140564504b91412645027914096450379140d64500b914026450439141064501f9140764502f9140b64504791411645023914086450339140c64504f9) else (if b<8 then (0x1351a44d4491356a44d5891330e44cc191328e44ca191337e44cdd9132ee44cb991332e44cc991338e44ce19132fe44cbd91333e44ccd9133be44ced9133ce44cf191331e44cc591335e44cd591336e44cd9914a1a45284914a3a4528c914afa452bc914b5a452d4914a2a45288914a4a45290914b0a452c0914b6a452d8914c5a0531781480e4520191482e452099148be4522d91490e4524191491e452459148ee4523991493e4524d91494e452519) else (0x36b041f841076b043f8410f6b0444241105e8841f4105e10415322056b0427841096b042c2410a6288296e20a5e8829b620a678829f411319a44c6491325a44c949131ea44c7891321a44c849131aa44c6891326a44c989131fa44c7c91322a44c8891311e44c4591312e44c499130de44c3591315e44c5591316e44c599130be44c2d9130fe44c3d91310e44c4191347a44d1c9135ba44d6c91350a44d4091355a44d5491348a44d209135ca44d709))) else (if b<10 then (0x145688515821456484dae11345244d1591345445316114c5c452759149da4527611435c4505c91417e4505f1141764505e914178450629147e0451f61147dc451fb1147e8451549145504515791455c45155914554451569145584515a9145684515891456045159914564414241047d0404241006d88018a200678801f410bd1082f8410b55882dac102f3080c241025e8809f41070904197a2065b8819b62066288199e2067d04342410c7d040f841) else (if b<11 then (0x7aee61ebb887aefe1ebbd87af9e1ebe687af961ebe487afbe1ebed87afae1ebe987a61e1e98587a6be1e9ad87a73e1e9cd87a66e1e99987a71e1e9c587a60e1e98187a5fe1e97d87a5f21e97b87a5ec1e97a87a5e81e97987a5e21e9cb87a7261e98f87a63a1e98d87a62e1e98b07a62a1e98a07a6261e98887a6fe1e9bd87a6ee1e9ba87a6e61e9b787a6dc1e9b687a6d81e9b587a6d21e96b8134548527621417c8505e21455085157214554851562) else (0x79d121e74f879d3a1e74d8794fe1e53d87953e1e54d8795ee1e5798794ae1e52987949e1e5268794961e52487961e1e58587954e1e5518795fe1e57d8794de1e5358794ce1e5328794c61e53087960e1e58187951e1e54587950e1e5428795061e5408795de1e57587948e1e56f8795ba1e56d87aede1ebb587af7e1ebdd87affe1ebcb87af261ebf787afd61ebab87aeaa1eba987aea21ebb387aeca1ebb187aebe1ebad87afee1ebf987aeee1ebba8))))) else (if b<18 then (if b<15 then (if b<13 then (0x746b61d1cf8747361d19b8746661d1838746061d17f8745f61d1c78747161d17b8745ea1d1798745e21d18f8746361d1cb8747261d18b87462c1d18a8746281d1898746221d16b8746de1d1b68746d61e717879c561e727879c961e6ff879bfa1e6fd879bf21e753879d461e703879c0a1e701879d7e1e72b879ca61e70b879c2a1e709879c221e757879d561e70f879c3a1e70d879c6e1e71a879c661e718879d6e1e759879c7e1e71d879d1e1e7458) else (if b<14 then (0x774961dd2487754e1dd5187752e1dd4987750e1dd428775061dd3b8774e61dd678775961dd7f8775f61dd378774d61dd338774ca1dd318774c21dd5f8775761dd778775d61dd2387755e1dd568775561dd6f8775ba1dd6d874ede1d3b5874f7e1d3dd874ffe1d3cb874f261d3ab874eaa1d3a9874ea21d3b3874ec61d3af874eba1d3ad874fde1d3f5874eee1d3ba874ee61d3b8874efe1d3bd874fee1d3f9874f9e1d3e5874f921d1878746161d1af8) else (0x766d81d9b5877c9e1df25877c5e1df15877bfe1defe877bf61defc877c1e1df05877c121df3b877ce61df53877d461df03877c0a1df01877cae1df29877c6e1df19877c621df23877c8a1df0b877c2a1df09877c221df13877c4a1df11877cfe1df3d877d5e1df55877c3e1df0e877c361df2f877cb61df2c877d1e1df45877d121df37877d3e1df4e87753e1dd4d8774fe1dd3d8774be1dd2d87758e1dd618775ee1dd798774ae1dd2987749e1dd268))) else (if b<16 then (0x76ee21dbc3876f061dbab876ea61dba8876f3e1dbcd876f321dbe7876f961dbe4876ece1dbb1876f5e1dbef876fba1dbed87665e1d9958765de1d97587661e1d9858766ae1d9a987670e1d9c18765ce1d9728765c61d96f8765bc1d96e8765b81d96d8765b21d9938766461d98b87662c1d98a8766281d98987660e1d98187669e1d9a58766fe1d9bd8765ae1d97b8765ec1d97a8765e81d97987667e1d99f07667a1d99e0766761d9b78766dc1d9b68) else (if b<17 then (0x73d4e1cf1b873c661cf18873c8e1cf0b873c261cf08873cbe1cf2d873cb21cf47873d161cf44873d141cf44073c4e1cf118734be1cd2d8734fe1cd3d87358e1cd618735ee1cd7987349e1cd268734961cd4b8735261cd4387350c1cd428735081cd418734ee1cd3987348e1cd338734ca1cd3187355e1cd568735561cd6f8735ba1cd6d876f1e1db9f876e7a1db9d876e721dba7876e961dbb7876ed61dbdb876f661dbf3876e8e1dba1876eee1dbb98) else (0x7eb0e1fac187eb6e1fad986ee7e1bb9d86ee721bb9d06ee701bbe786ef961bbe486e5ae1b96f86e5ba1b96d86e6de1b9b686e6d61c39f870e7a1c39d870e721c3a7870e9a1c3a5870e8e1c3cf870f361c3cc870f9e1c3e5870f921c1778705d61c1738705c61c1708705be1c16f0705ba1c16e0705b61c16c8705ae1c19f87067a1c19f0706781c19d8706de1c1b68706dc1c1b60706d61ceff873bf61cefc873c1e1cf06873c161cf17873c561cf3b8)))) else (if b<21 then (if b<19 then (0x7d97e1f65d87ea1e1fa8687ea161fa8487eaae1faaa87eaa61faa887ea3e1fa8e87ea361fa8c87ea6e1fa9a87ea661fa9887eafe1fabe87eaf61fabc87eb5e1fad687eb561fad487eace1fab187ea5e1fa9587ea8e1faa187eb1e1fac587eb7e1fadd87ea2e1fa8987eade1fab587eaee1fab987eb4e1fad187ebae1fae987eabe1faad87ea9e1faa587eb2e1fac987eb8e1fae187ea4e1fa9187eb3e1facd87eb9e1fae587ea7e1fa9d87ebbe1faed8) else (if b<20 then (0x79c625e744979d3a5e784879e101e5269794925e5329794c25e5429795025e5229795ba5e5ac8796b01ebaa97aea25ebb297aeea5ebb897af9a5ebe497b0921ec2407a5f25e97b17a5ea5e97a17a5e25e98e97a62c5e98a97a6285e98897a6ea5e9b717a6da5e9b617a6d25e96a97a7d21e9f407d87e1f61d87d85e1f61687d8561f61487d91e1f64687d9161f64487d86e1f61987d8ee1f63987d94e1f65187d92e1f64987d90e1f64187d96e1f6598) else (0x765ac5d96a9765ec5d97a9765e85d99f17667a5d99e1766dc5d9b69766d85d9f48767d01defe977bf25df04977c0a5df18977c8a5df0a977c225df12977c3a5df2c977d125df4e977e121df8407749a5dd2497750a5dd329774c25dd2317748a5dd569775ba5ddac8776b01d3aa974ea25d3ae974eea5d3b8974f925d4248750901d17a9745e25d18b17462a5d18a1746225d16a9746da5d1f48747d01e6fe979bf25e702979c2a5e708979c3a5e71a9))) else (if b<23 then (if b<22 then (0x6e5ba5b9b696e7d21b9f4070e7a5c39c970e9a5c3cc970f925c4248710901c1709705bc5c16e9705b85c16c9705ac5c16a97067a5c19f1706785c1b69706dc5c1b61707d21c1f4073bf25cf06973c625cf08973cb25cf44973d145cf44173e121cf8407349a5cd4317350a5cd4217348c5cd229734ca5cd569735ba5cdac8736b01db9e976e725dbb8976ea25dbcc976f925dbee9770921dc240765ca5d96f1765ba5d96e1765b25d98b17662a5d98a1) else (0x7eaba5faac97ea4a5fa9097ea7a5fa9c97eb0a5fac097eb6a5fad897ec661fb1887ec6a1fb1b87e80e5fa0197e86e5fa1997e81e5fa0597e83e5fa0d97e8ae5fa2997e8fe5fa3d97e87e5fa1d97e82e5fa0997e84e5fa1197e8be5fa2d97e90e5fa4197e88e5fa2197e89e5fa2597e8ee5fa3997e93e5fa4d97e85e5fa1597e8ce5fa3197e91e5fa4597e8de5fa3597e92e5fa4997e94e5fa5197e9d01bb9c96ee745bb9c16ef925bc2486f0901b96a9)) else (if b<24 then (0x7d28e5f4a197d2ae5f4a997d33e5f4cd97d38e5f4e197d35e5f4d597d29e5f4a597d32e5f4c997d37e5f4dd97d34e5f4d197d39e5f4e597d36e5f4d997d3be5f4ed97d3ce5f4f197d85a5f61497d91a5f64497d86a5f61897d92a5f64897d6ee5f5b997d6de5f5b597d75e5f5d597d72e5f5c997d77e5f5dd97d74e5f5d197d79e5f5e597d7ae5f5e997ea1a5fa8497eaaa5faa897ea3a5fa8c97ea6a5fa9897eafa5fabc97eb5a5fad497ea2a5fa889) else (0x2474a091d2024744091d0824740091ba8246dc091b68246d8091b487d4549f60627e9d09fa7527e9e09fa7627e9dc9fa7927e9e89f51517d8185fb1817e9d05fa7517e9e25fa7817e9d85fa7797e9dc5fa7997e9e45fa7a97e9e85bb9c26f0905b9f41710905c16e2706789c1b62707d05cf44273e105cd422736b05dc241765b89d98a2765e89d99e2766d89d9f4177e105ddac1750905d18a2747d05e7841796b05ec2417a5e89e98a27a6d89e9f41)))))) else (if b<38 then (if b<31 then (if b<28 then (if b<26 then (0x25064093ce824f3209413025044093aa824ea2093b282505c09415024eea093b882507c0941d02500c09402825008094010250020940002502c0940902501c0940502501209404024f9a093e48245d20916f0245ba0916e0245b2091eb0247a4091a682467c0919e8246780919c82478c091e10245f20917b0245ea0917a0245e2091e70247940919282463a0918b02462a0918a024622091ef0247b4091db02476a091da024764091d7024754091d30) else (if b<27 then (0x1e76c079d901e75c079d501e7bc079ed01e74c079d281e748079d101e742079d001e6da08efe823bf208f02823dcc08f71023c2a08f08823c3a08f77023dd408f1a823c6208f63023d8a08f62023d8408f60823d8008f7f023df408f67023d9408f64823d9008f44823d3a08d2682349208d9b02366408d328234c208d9f02367408d4282350208da702369408d8f02363408d8b02362a08d8a02362408d8882362008d6e824e7a0939c824e8a0941b0) else (0x293b60a5078294160a4bf8292fa0a4bd8292ee0a4bb0292ea0a4ba0292e60a4b882937e0a4de8293760a4f78293da0a4f581ee7a07b9c81ee9a07bcc81f06c07c1901ef4a07baa81eea207c1301f04407bae81eeea07bb881f05c07c1501f00a07c0301f00807c0081f00407c0001ef9207c0b01f02407c0881f02007c0701f01407c1f01f0740796e81e5b2079eb01e7a40799e81e78c079e101e5ea0797881e79c079e501e62c0798a81e628079888))) else (if b<29 then (0x29b3e0a6cd829b320a52c82956a0a55882955a0a5368294d20a5388294ca0a53082951a0a54482952a0a54302950a0a5420295020a5728295c20a58e8296320a52282948c0a5220295ba0a58a82934e0a4d18292de0a4b582930e0a4c182939e0a4e58293fe0a4fd8292a60a4a882929e0a4d78293560a4db8293660a50b8294260a4cb82932a0a4c982931e0a4c58293ae0a4e982940e0a5018292ce0a4b18292c20a4af8292ba0a4ad8292b20a4ef8) else (if b<30 then (0x29c1a0a72c829cca0a730829c2a0a708829c3a0a70c829c6a0a718829c7a0a71c829d120a760829d2a0a766829d920a6ab829aa60a68f829a360a69b829a660a6bf829af60a6d7829b560a683829a0a0a67d829abe0a6ad829ace0a6b1829a8e0a6a1829a820a6e3829b860a69f829a760a687829a1a0a685829a120a6c3829b060a6db829b660a68b829a260a693829a4a0a691829a420a6c7829b160a6df829b760a697829a560a6b7829ad60a6b48) else (0x285e20a18e8286320a19282862a0a1888285aa0a16b0285a80a1b682874a0a1138284460a0f78283d60a1038284060a1278284960a0e98283a20a13f8284f60a0e782845e0a11582846e0a11982843e0a10e8284360a10b82842a0a1098284220a1078284160a12b8284a60a0f38283c60a1438285060a0ef8283ba0a0ed8283b20a12f8284b60a0ff8283fa0a0fd82851e0a1458283ee0a0fa8283e60a0f882847e0a11e8284760a1378284da0a1358)))) else (if b<34 then (if b<32 then (0x28ef20a3e48290020a353828d460a337828cd60a343828d060a367828d960a32b828caa0a325828dfe0a37d828d5e0a355828d6e0a359828d2e0a34a828d260a348828d3e0a34d828d1e0a345828cbe0a32e828cb60a32c828dae0a369828cce0a332828cc60a383828e060a33b828cea0a339828ce20a36f828db60a33f828cf60a387828e160a35f828d760a35c828dde0a375828dd20a17482868a0a1a082869a0a19e8286720a17e8285f20a17a8) else (if b<33 then (0x1c62a0718881c78c071e101c5ea0717881c76c071d901c74c071d281c748071d101c67a071b6821bfa086fc821c1208702821c6208722821c2a08708821c4a08773021dc40870e821d8c08760821d8408760021cb208744821daa0876b021da808769021d3a085268214920854282166c085990214ca0853082164c0859102162c0858a8216280858902155a0856e828e9a0a3ce828f320a3d2828eaa0a3a8828eba0a3ac828eca0a3ba828ee20a3be8) else (0x27b3e09ecd827b3209d2c8274da09d348274ca09d3082748c09d2282748809d6e82762a09cb78272d609ca98272a209ce782739609cff8273f609ca78273be09ced8272ce09cb18273ae09ce982740e09d018272be09cae8272b609cac82737e09cde82737609cf78273da09cf581ce7a0739c81ce9a073a281ceea073b881ceaa073a881cec20741301d044073ae81d00c0740081d0040740001cf32073e481d02c0740881d0240740801c5ba0716c8))) else (if b<36 then (if b<35 then (0x2100208401021000083cc820f920840b021024083ee8205ca0816f0205ba0816e0205b20818b02062a0818a02076c081d90205ec0817a8205e8081d302074a081d20207440819f02067a0819e0206dc081b68206d809f06827c2a09f08827c4209f0e827c3209f44827d8209e8f827a3609e83827a0a09e7d827afe09ebd827b5e09ed5827b1e09ec5827a1e09e86827a1609e84827a2e09e89827a2209ec3827b0609edb827b6609eb7827ad609eb48) else (0x263a2098f78263d609927826496098e78264fe0993d8264be0992d8263ce098f28263c6098ef8263ba098ed82647e0991f02647a0991e026476099378264da0993581bbfa06efc81bc1a06f0081bc6a06f1881bc7a06f0881bd8c06f6081bd8406f6001bcb206f4481bd1406f4401bdac06f6881bda406f6801b49a06d2481b50c06d4281b50806d4081b64c06d9101b4ca06d8b01b62a06d8a01b62406d5681b5ba0839e820e72083b8820ea2084030)) else (if b<37 then (0x18e72063a681900c0640081900406400018f32063e48185c20616f0185ba0616e0185b2061d281874c061d20187440619e81867c0619e0186da061b70186d809ba6826ea209be482700209c0102700009b2b826caa09b25826cde09b35826d9e09b65826dfe09b7d826dbe09b6d826cbe09b2d826cb209b5f826d7609b5c826dde09b75826dd209b75026dd009b33826cc60997482660a0996b0265aa0996a0265ea099b70266da099b602674a098e98) else (0x1755a05d5701755805d6e8175bc05d6e01aee206b9c81aea206bcc81af920696a81a62c0698a81a6280696f01a5ba0696e01a5ec0697a81a5e80699f01a67a0699e01a6da069b701a6d807f1881fbf207f0881fcb207f4481fd1407f4401fc1a07f4e81f48a07d4281f49a07d3281f55c07d5681f55807d6e81dbfa076fc81dc0a0770881dc620776301dd820776101dd800774481d49a0752481d4ca0754281d62c0758a81d6280758901d5ba0639e8))))) else (if b<44 then (if b<41 then (if b<39 then (0x2c74c0b1d082c7440b19e82c6720b1b682c6d20b1e702c7940b1df02c7740b1e302c7840b1eb02c7a40b1d702c7540b1ef02c7b40b28682ca120b2aa82caa20b28e82ca320b29a82ca620b2f282cbcc0b2f082cbc40b2be82caf20b2d682cb520b30702cc140b2ff02cbf40b30302cc040b30b02cc240b30f02cc340b2f702cbd405b9c816e7405b9c016f3205be48165aa0596e81667a059b6817bf205f2c817d1205f0681748a05d2701749a05d260) else (if b<40 then (0x23d9048f8402349848d2412362848d881236b00939e124e70493a212500849400125010494240245d04916e1245b04919e1245e84918a124768491d2124740491b61247d00ad8b02b6240ad8f02b6340ad9702b6540ada302b6840ada702b6940ae0e82b8320ae1682b8520ae6282b98c0ae6082b9840ae3682b8d20ae4682b9120ae6f02b9b40ae6702b9940ae7302b9c40ae7702b9d40b16682c5920b18a82c6220b16e82c5b20b17a82c5e20b1d28) else (0x28e520a1741285a84a0e892839c4a10e92842a4a1089283ba4a0ec9283fa4a0fa9283e24a11e9284da4a154829c184a68e929b5a4a6829299f44a6a0929a1a4a684929a4a4a690929ad24a6cc929bb20a52c1295084a5221292a24a4a712932a4a4b09292ba4a4ac9292fa4a4bb1292ea4a4ba1292e24a4de9293da4a51481ee7847b9c11ee9847c0211f00047c0811f0900796e11e5b04798a11e748479d011e7d008efe123bf048f02123d8848f601))) else (if b<42 then (0x21090081721205b84816c1206284817a1207484819e1206d8481f4027c1849e8e927a0a49e7d127a1a49e84927a2249eb4927b3249eec8274b049d221272a249ca71272ba49cac92737a49cf69274520739e11ce70473a611ce884740011d0204742401c5b84716c11c748471f4021bf8486fc121c1048702121d804876a121e10085261214904858a1216b00a3a6128caa4a325128dfa4a34a928d224a32e928cb24a332928cea4a338928d724a3749) else (if b<43 then (0x1f1ec47c7a91f1e847c8691dbf8476fc11dc084776011de100752611d4904758a11d6b00639e118e70463a6119000464240185c04616e1185b0461d2118678461b61187d009ba612700049b2a926c9449b36926dfa49b2c926d7249b74926dd449b741265d04996a1266d8498e892639c498f29263ba4991f12647a4991e1264da4995481bbf846efc11bc1846f0011bd8046f4411bda046f8401b49846d2411b50846d8a11b6b00839e120e70484001) else (0x16a1245a85116a1045aa8916af24596a1161ba4588a91625a45e0c9178a245e3491748845d2611755845d6e11719c45c6691719845c7a9171ec45c7a11721a45c8711721846a9891aa1246a8c91aaa246abc91a5a84698a11a5b84697a11a678469b611a20c4688291a2084686f11a1ba4686e11a1dc4687691a1d84688b11a22a4688a11a25a4689711a25847f4411f88247e0c91f85247e2891f8d247e3511f8d047d2211f55847c7291f19a47c6e9)))) else (if b<47 then (if b<45 then (0x2b7b44adf712b7d44adfb12b7e44adff12b7f44b16a12c5a04b1d612c7504b0e312c3844b13712c4d44b0fe92c3f24b0ea92c3a24b0f292c3c24b10e92c4324b12292c4824b14712c5144b13f12c4f44b14312c5044b14b12c5244b14f12c5344b28a12ca204b2f612cbd04b20312c8044b25712c9544b21e92c8724b20a92c8224b21292c8424b22e92c8b24b24292c9024b26712c9944b25f12c9744b26312c9844b26b12c9a44b26f12c9b445b9c1) else (if b<46 then (0x375ba4dd6c9374ca4dd3093748a4dd56938f9a4e3e4938eaa4e3a8938eca4e3ce938f324e1b89386dc4e1b69386d84e1b49385f24e17b1385ea4e17a1385e24e1a293867c4e19e9386784e19c9385aa4b15812c55c4b27812c9dc4b27912c9e845a8421719885c7a2172188688221a1b88687621a2288689621f8d087c7a226dd08991e2292e88ad2212b4804ae1212b8404ae6612b9904adb312b6c44adba92b6e24adc692b7124adda92b7624adef1) else (0x314cc4c5329314c84c56e9315b24c52313148a4c54293155a4d6fe935bf24d708935d1a4d744935d224d718935cb24d7369354aa4d52713549a4d5261354924d5331354ca4d5321355bc4d56e9355b84d56c93548c4d52293550c4d5429355084d55713555a4d556133d1a4cf44933c2a4cf08933c3a4cf2c9335bc4cd6e9335b84cd6c9334ca4cd3093348a4cd56937bfa4defc937c0a4df46937d124df0a937c224df0e937cb24df3693749a4dd249))) else (if b<49 then (if b<48 then (0x3e41e4f90593e45e4f91593e49e4f92593e4be4f92d93e4ce4f93193e40e4f90193e44e4f91193e46e4f91992ef924bbe512ef904bbcc92e5aa4b9b692e67a4eb9e93ae724ebcc93af924e97093a5da4e96e93a5b24e96a93a5ac4e99e93a6da4f39c93ce824f3b893cefa4f3a893cf324f3e493cf944f3e413ceba4f3ea93c5ba4f18a93c5aa4f16b13c5ea4f19e93c6da4c6fc931c1a4c708931d1a4c744931d224c718931cb24c72d131cb04c5269) else (0x355b88d5422355588d5ac133e104cd6e2336b04df841376b04e4241386d88e17a2386788e1f413e59a4f96493e5ea4f97893e6da4f9b493e5ba4f96c93e62a4f98893e67a4f99c93e5aa4f96893e5fa4f97c93e6ea4f9b893e5ca4f97093e63a4f98c93e68a4f9a093e38e4f8e193e3be4f8ed93e47e4f91d93e39e4f8e593e3ee4f8f993e42e4f90993e3ce4f8f193e48e4f92193e3ae4f8e993e3fe4f8fd93e43e4f90d93e4ae4f92993e3de4f8f59)) else (if b<50 then (0x4d0081340104d0021340004d01c1340504ceaa133a884ceca133ba84cee2133e684cf92131e304c784131ef04c7b4131d704c754131d484c750131d304c74a131d204c744131d084c7401317c84c5ec1317a84c5e81317884c63a1318b04c62a1318a04c622131ba84c6dc131b684c6d8131b483e55c8f95823e5648f95793e55c4f95893e5604f95993e5644bbe422f0904b9f413cf908f42413c7d04c72c231e104c5322316b04d7841354988d5322) else (0x4674c119d2846748119d1046742119d00465ea1197884662c1198a846628119888466da12f6f04bdb412efe84bbf212f0284bdcc12f7104bd8c12f6284bd8812f6104bd8212f6004bdfc12f7d04bd9c12f6504bc2a12f0884bc3a12f1a84bc6212f4484bd3a12d9704b65412d2684b49212d9b04b66412da704b69412d8f04b63412d8b04b62a12d8a04b62412d8884b62012d3284b4c212d4284b50212d6e84d04c1341104d07c1341d04d00c134028))))))) else (if b<77 then (if b<64 then (if b<57 then (if b<54 then (if b<52 then (0x49c8a12773049dc41277b049de41277f049df412767049d9a12766049d841270a849c2212712849c3a1272c849d121274e84965c1259504949a1252484967c1259d04950a1259b049664125a3049684125a70496941258d0496321258c04962c125328494c21252284955a1256e84704c11c1104700c11c0284700811c0104700211c0004701c11c0504707c11c1d046eaa11ba8846eba11bba846ee211be484678c119e104675c119d50467bc119ed0) else (if b<53 then (0x4900c12402849008124010490021240004902c1240904906c1241904907c1241d04901c1240504901212404048ea2123cc848f92123ee84877c121dd0485ca1216f0485ba1216e0485b2121e70487941218b04862a1218a04876c121d90487ac121e90487bc121ed04875c121d504874c121d2848748121d1048742121d00485ec1217a8485e81219f04867a1219e0486dc121b68486d81276f049db4126fe849bf212704849c0a12777049dd4127188) else (0x42678109b68426dc109b6045dbc1176d045bf211706845ddc11775045c6211763045d8a11762045d8411760845d801176b045da41177b045de411767045d9411764845d901177f045df411708845cb211744845d141174404565c1159504549a1159f0456741154304550a1154204564c1159104568c115a104563c1158d04569c115a504562c1158a84562811589045622115880454ca115568455ba1240f0490341239e848e7212417049054123b88))) else (if b<55 then (0x51562145568514da145348515ca1457085163a1458c85148a14523051488145328515ba1458a8512de144b585129e144a6851296144cb85132a144c98512be144ae8512b6144df85137a144dd8513de144f68513d610c0f04303410b9e842e7210ba684302c10c0a84302810c0104306c10c1904307c10c1d042f3210be484277c109dd0425c21096f0425ba1096e0425b2109d9042762109d804274c109eb0427a4109ef0427b41096b04267a1099f0) else (if b<56 then (0x4ed7213b7784edd613b7484e5ca1397084e5da1396e84e5b21396a84e5ac1396a04e6da139d284e3ae138ea84e3a6138e784e39a138e584e3921391f84e47a1391d84e4de1393684e4d6146fc851c0a14700851cb214732851c2214744851d8214761051d801470e851c321474a851d9a1467f8519f61467c851a3e1468d851a8e146a1851a8214687851a1614684851ade146b5851ad2146cf851b36146cc851b34146cc0514aa1452885149a1455a8) else (0x4c750531d214c7405317a14c6385318a14c620531b614c7d014a86852a1214aaa852aa214af2852bcc14af0852bc414a8e852a3214a9a852a6214abe852af214ad6852b5214afb052be414b07052c1414aff052bf414b0b052c2414b0f052c3414af7052bd410403041002104010410001039c840e741039c040f92101d304074a101d20407441016e8406da13b9e84ee7213ba284ef9213c0084ec9e13b2684ec9613b2484ecae13b2984ed7e13b5d8)))) else (if b<60 then (if b<58 then (0x4900052404148ea0524240485b85218a148748521d01485e85219e1486d8521f4049d985264d14983a5260c94984a526571498825265314997c5264a949914526169498525261a9498a2526349496305252214919a524649491ca5249894925c5246e9491b25247a94921a51c0214700051bba146ee051c24046748519d0146628519881467d012f6214bd8052f1a14bc6052f8404b62852d8814b50852d4014b6b01340214d000533ba14cee0534240) else (if b<59 then (0x4ed7253b7494e5a8538ea94e39a538e494e47a53936951d805467c951a8254684951ad2546cc951b34546cc151bb21452215129a544ca9512ba544de9513da5451484302850b26942c9250b2a942dea50b75142e3c50b48942d725096e1427605096a142678509b61424f4508e714239a508e6142392509389424dc5094b14242a5090b1424285091e94247c5091e145d8851760145d9051708145d10517840455085158a145620515321456b0124021) else (0x625ea5897a1625e25899296263a5898b16262a5898a162622589bc9626dc589b69626d8589b496268a5899f16267a5899e1626725896b1625aa54a781529e454a7a151b30908e62424289091e252bd854af4152a7854a9c15295c54a5515283c54a0d15296c54a5915284c54a1115299c54a6515289a54a2495297c54a5d1529ac54a691529bc54a6d15285c54a151528da54a3495292a54a489410005039c141090101d21405b8501f404ec9a53b249))) else (if b<62 then (if b<61 then (0x5dc625774695dd125774895dcb25752695d4925753295d4c25754315d50a5754215d5025756e95d5b25752315d48a57556961bfa586fc961c1a58702961c2a58708961c4a5870e961c6a58718961d1a58744961d3a58748961cb25873696149a585249614ca5853096150a585409615ba5856c96148c5852296155a58b9e962e7258ba2962eaa58ba8962eca58bba962ee258be6962f9258bce962f32589749625bc5896e9625b85896c9625f25897b1) else (0x665ea5997896663a5998a9666225996a9665ac5999e9666da59efe967bf259f02967c2a59f08967c3a59f1a967c6259f2c967d1259f309674ba59d2696749259d3a9674ca59d3096750a59d4096748a59d2316755a59d6e968e7a5a39c968eaa5a3a8968eba5a3ba968ee25a3cc968f925a3e5168f905a3ea9685da5a16e9685b25a17a9685e25a18a9686225a16a9685ac5a19f16867a5a19e1686da576fe95dbf25770695dc2a5770895dc3a5771a9)) else (if b<63 then (0x594c25652315948a5656e95950a5655695ce7a5739c95ce9a573a295ceaa573a895cec2573ae95cf92573b895cf32573c295c5ba5716c95c5ea5717895c5ac5716a95c6da5718a95c67a5839e960e72583a4960e8a583aa960ea2583b2960eba583e4960ee2583cc960fb2583d69605ba5816c9605ea581789605ac5816a9606da5818a96067a59b9e966e7259baa966ea259bae966ec259bba966ee259bcc966f9259bc29665c2599769665ba5996c9) else (0x5b55a57efe95fbf257f0895fd1257f1895fcb257f3695f4aa57d2715f49a57d2615f49257d2315f48a57d3315f4ca57d3215f5bc57d6e95f5b857d4315f50a57d4215f55c57d5695f558596fe965bf259702965c2a59708965c3a59718965cb2597449654ba59526965492595389654ca5953096548c5952296550a59543165508595569655ba566fe959bf256704959c0a5670a959c2256712959c3a56744959c625672c959d3256526959492565329))))) else (if b<70 then (if b<67 then (if b<65 then (0x566785939e964e72593a0964ea2593a9164ea0593b8964f32593e49645da5916e9645b25916b1645aa5917a96462a5919e9646da5639e958e72563a8958f92563b8958f32563ec9585ca5616f1585ba5616e1585b25616b1585aa5617b1585ea5617a1586dc561b69586d85618b15862a5618a15867c5619e95867856efe95bbf256f0695bc0256f0895bd1256f1895bcb256f2d15bcb056d2695b49256d2315b48a56d3295b5bc56d6e95b5b856d429) else (if b<66 then (0x5aea256be495aee256bcc95a5ac5696a95a5bc5696e95a5b85697b15a5ea5697a15a6dc569b695a6d85698b15a62a5698a15a67a5699f15a67857b9c95eea257be495eee257bcc95ef3457bcc15ee9a57bd695e5ac5796a95e5ba5797a95e6da5798b15e62a5798a15e67a55b9e956e7255ba6956f9255ba8956ee255bcc9565c25596f1565ba5596e1565b25596b1565aa559b71566da559b61565ea5597b1565e85598a95662c5598a15667a5599f1) else (0x54ea2553b8954f325516b1545aa5516e9546da5517a95462a5519e955bf255744955c2255718955cb25570695548c5552295549c555269554985556f1555ba5556e1554ca555331554c85554295550c5554215555a5555715555858efc963c2258f18963cb258f4496348c58d2296349a58d3296350a58d569635ba55efc957c2255f44957d1455f44157c6255f2c957c1a55f4c95748c55d2295749a55d329575ba55d4295755c55d5695755856b9c9))) else (if b<68 then (0x6c0ce5b03196c12e5b04996c0de5b03596c13e5b04d96c14e5b05196c0ee5b03996c59a5b16496c5ba5b16c96c5ea5b17896c6da5b1b496c62a5b18896c67a5b19c96c5aa5b16896c5ca5b17096c5fa5b17c96c6ea5b1b896c63a5b18c96c68a5b1a096c47e5b11d96c3ae5b0e996c48e5b12196c3de5b0f596c49e5b12596c40e5b10196c44e5b11196c4ae5b12996c45e5b11596c4be5b12d96c4ce5b13196c46e5b119954e725539d154e70553e49) else (if b<69 then (0x6bcca5af3096bade5aeb596ba0e5ae8196baee5aeb996ba3e5ae8d96bafe5aebd96ba6e5ae9996baae5aea996bb0e5aec196babe5aead96bb1e5aec596bb2e5aec996bace5aeb196c1ba5b06c96c1da5b07496c20a5b08096c29a5b0a496c22a5b08896c25a5b09496c1ca5b07096c1ea5b07896c21a5b08496c2aa5b0a896c23a5b08c96c26a5b09896c0fe5b03d96c02e5b00996c04e5b01196c10e5b04196c0be5b02d96c05e5b01596c11e5b0459) else (0x586d89618a258678961f415bcb096f8415b5b896dac15fe1057d2625f4c897d6e25f50897d5625f6b059542259e10565ac15d090571f4161090581f4167090599f4167e1059dac168f909a4241686789a1f415de105754225d6b0587841616b058c241625b89897a262628989b6262678989f416bbda5aef496bbfa5aefc96bc2a5af0896bd1a5af4496bc6a5af1896bcba5af2c96bbea5aef896bc0a5af0096bc3a5af0c96bd2a5af4896bc7a5af1c9)))) else (if b<73 then (if b<71 then (0x9462c2518a894628251888947bc251ed09476c251d9094762251d809475c251d509474c251d2894748251d1094742251d00946ea251b70946da251b60946d21b15926c7e45b1fa16c5665b159154e70954241547d0557841554989556e2554c895542255558955ac157d1095f8415755895dac15b0905696e25a5e8969b625a6289699e25a7d057bcc25f0905798a25e7d055c241565b8959b62565e89598a256678959f4164ea0964241585b89617a2) else (if b<72 then (0x9369c24da509363c24d8d09362c24d8a89362824d8909362224d880935ba2540f0950342539e894e72253a2894f3a253cc89504c25411094eaa253a8894eca25417095054253ba894ee22541f0950742540309500a25402095004254008950002540b09502425407095014253e6894f92251df094774251748945bc2516e8945b82516c89469a2519f09467a2519e094672251e30947842517c8945ec2517a8945e82517889479c251e509464a2518e8) else (0x8e754239ef08e7b4239d308e74a239d208e744239d088e740239b6893dbc24f6d093bfa24efc893c1a24f02893cba24f2c893cd224f32893dcc24f71093c2a24f08893c4a24f0e893ddc24f75093c6a24f18893d8c24f62893d8824f61093d8224f60093dac24f6a893da824f69093dfc24f7d093d9c24f65093d9224f64093d1224f4e89365c24d9509349a24d2489355a24d5489366c24d990934ca24d3089367c24d9d09350a24d4089364c24d910))) else (if b<75 then (if b<74 then (0x9b2f626cbb89b2ea26cb989b2e226cdf89b37c26cde89b37826cdd89b3de26cf689b3d623c0f08f03423b9e88ee7223ba688ef3a23bcc88ef4a23c1308f04423baa88eea223bae88f05c23c1508eeea23bb888f00c23c0288f00823c0108f00223c0008f02c23c0908f01c23c0508f01223c0408f07c23c1d08ef92239df08e7742396e88e5b22399e88e672239e308e7842397a88e5e2239e708e7942398b08e62a2398a08e622239db08e764239d70) else (0x9b4da26d3489b4ca26d3089b51a26d4489b50a26d4089b5ca26d7089b63a26d8c89b48a26d2309b48826d6f09b5ba26d6e09b62a26cd389b34626cb789b2d626cc389b30626ce789b39626cff89b3f626cab89b2aa26ca989b29e26ca689b29626ca489b35e26cd589b36e26cd989b3ce26cf189b42e26d0989b33626ccc89b32e26cc789b31626ceb89b3a626d0389b40626cb389b2c626caf89b2ba26cad89b2b226cef89b3b626d0789b41626cbf8)) else (if b<76 then (0x9bd9226eab89baa626e8f89ba3626e7f89b9fa26e7d89b9f226e9b89ba6626ebf89baf626ed789bb5626e8389ba0626eaf89bab626eb389bac626ecb89bb2626ee389bb8626ea789ba9a26ea189ba1e26e8689ba1626e8489ba7e26e9d89bb0e26ec189bb6e26ed989ba2e26e8989ba4e26e9289ba4626e9089bade26eb589bad226ecf89bb3626ecc89bb3426ecc09bb1e26ec589bb7e26edd89ba5e26e9589b4aa26d2889b4ba26d2689b49226d5c8) else (0x9a39e268e689a396268e489a45e2691589a46e2691989a4ce2693189a4362690c89a52e2694989a42e2690789a4162692b89a4a6268f389a3ca268f189a50e2694189a3be268ee89a3b6268ec89a4be2692d89a3fe268fd89a51e2694589a3ee268fa89a3e6268f889a47e2691e89a4762693789a4da2693589bbfa26efc89bc0a26f0089bcda26f0a89bc2226f0e89bc3226f1a89bc6226f4489bd8226f6109bd8026f1e89bc7226f4a89bd2226f668)))))) else (if b<90 then (if b<83 then (if b<80 then (if b<78 then (0x9ae2626b2f89acba26b2d89acb226b4789ad1626b6b89ada626b3389acc626b8389ae0626b3b89acea26b3989ace226b5f89ad7626b5c89adde26b7589add226b6f89adb626b3f89acf626b8789ae162697289a5c22697689a5ba2696c89a6922697e89a5f22698289a5ea2697889a63a2698c89a62a2698889a6ea269b889a5aa2696b09a5a8269b689a74a2691389a446268f789a3d62690389a4062692789a496268eb89a3aa268e989a4fe2693d8) else (if b<79 then (0x99406264af8992ba264ad8992b2264bf8992f6264ef8993b626507899416264bb8992ea264b98992e2264df89937a264dd8993de264f68993d626b9e89ae7226ba289ae8226bd689aeaa26ba889aeba26bac89aeea26bb889af9226c0089aefa26bbc89afaa26be889ad4e26b5189acde26b3589ac9e26b2689ac9626b2489ad0e26b4189ad9e26b6589acae26b2989adfe26b7d89ad5e26b5589ad6e26b5989adce26b7189ad3e26b4e89ad2626b8b8) else (0x99b3e266cd899b3226697899a5a26695899b1e266c5899b7e266dd8994aa265288994ba265268994922655c8994da265348994ca2653089951a2654489950a2654089948a265230994882656e89962a264d3899346264b78992d6264c3899306264ab8992aa264a989939e264e58993fe264fd89929e264a6899296264a489935e264d589936e264d9899336264cc8993ce264f189942e2650989932e264c7899316264b38992c6264eb8993a6265038))) else (if b<81 then (0x99bfa266fc899c0a26700899cda2670a899c222670e899c3226710899c6a26718899d1226760899c7a2671c899c8a266ab899aa62668f899a362667f8999fa2667d8999f22669b899a6626683899a06266bf899af6266d7899b56266af899ab6266b3899ac6266a7899a9a266a1899b2e266c9899b8e266e1899a1e26686899a1626684899a7e2669d899a2e26689899a22266c3899b06266db899b6626693899a4a26691899a42266b7899ad6266b48) else (if b<82 then (0x8d024233d688c77c231dd08c5ba2316c88c62a2318888c78c231e108c5ea2317888c76c231d908c74c231d288c748231d108c67a231b6891bfa246fc891c122476f091db424702891c6a24718891c8a2470a891c2224712891dcc24771091c3a24763091d8224761091d802472c891d122476b091da224769091da02474e89165c2459509149a2452489150a2454089166c245990914ca2453089164c2459109162c2458a8916282458909155a2456e8) else (0x88e72223a488903c2240d088e8a223ba888ee2223c2888ef2223aa888ea2223b288904c22411088eba2240308900222401089000223cc888f922240b08902222409089020221df0887742216e8885b22218a888622221e30887842217a8885e2221db088764221d308874a221d20887442219e8886da2339e88ce72233a688d03c2340d08ce8a233ba88cee2233aa88cea2233b088d04c2341108ceba2340308d0022340108d000233cc88cf922340b0)))) else (if b<86 then (if b<84 then (0x974d225d328974c225d2309748a25d2209755a25d5709755825d6e89762a25cc389730625cb78972d625cab8972aa25ca989729e25ca689729625ca489734e25cd189739e25ce58973fe25cfd89731e25cc58972f625cbc8972ee25cdb89736625cef8973b625d0789741625cb38972c625cb08972be25cae8972b625cac89735e25cd58973ae25ce989740e25d0189732e25cca89732c25cca09732625cdf89737a25cdd8973de25cf68973d62239e8) else (if b<85 then (0x97c8a25f0a897c2225f0e897c3225f2c897d1225f60897a6e25e99897a3e25e8d8979fe25e7e8979f625e7c897a0e25e81897aae25ea9897afe25ebd897b5e25ed5897a7e25e9d897a5e25e96897a4625eb3897ac625ec7897b1625edf897b7625e87897a1a25e85897a1225e8b897a2625eaf897ab625ec3897b0625edb897b6625ea3897a8625ea0897ade25eb5897ad225ecf897b3625ecc8974ba25d2a8974a225d2689749225d488974e225d368) else (0x8bda422d9708b65422d2688b49222d4308b50a22d4208b50222d9308b64422d3288b62c22d8a88b62822d8908b55a22d6e890e7a2439c89103c2440d090eea243b8890ea22440309100224401091000243cc890f922440b091024243ee89077c241dd0905ca2416f0905ba2416e0905b22418b09062a2418a090622241db0907642417b0905ea2417a09074c241d2890748241d109067c2419e890678241b70906da241b6097bfa25efc897c0a25f008))) else (if b<88 then (if b<87 then (0x87bfa21efc887dbc21f6d087c6a21f18887c8a21f08887d8c21f60887d8421f60087cb221f44887dac21f68887da421f6808765c21d950874aa21d2708749a21d2608749221d4488750c21d4288750821d4088764c21d910874cc21d328874c821d8b08762a21d8a08762421d5708755a21d560875bc21d6e8875b822efe88bbf222f0688bdbc22f6d08bc0222f1a88bc6222f1e88bc2222f6308bd8222f6108bd8022f2c88bd1222f4508bd1022f6b0) else (0x96d2225b5f896d7625b5c896dde25b75896dd225b33896cc6259768965ca259708965ba2596c8966422596b0965aa2596a0965ea2599e8966da259d289640e259018963ae258ea8963a6258f78963d6258e789639a258e589639225913896446259278964962593f8964f6258fd8963f225907896416258fb89646e259198964be2592d89651e259458963ce258f18963be258ee8963b62590b89642a2590989647e2591e896476259378964da259358)) else (if b<89 then (0x825b22097e8825ec2097a8825e82097888274c209d2882748209d108262a2098b0826282099e88267c2099e0826da209b70826d825b9e896e7225ba2896e8225bc2896ea225ba9096ea025bcc896f9225c00896d0e25b41896c9e25b26896c9625b24896cae25b29896cde25b35896d4e25b51896d9e25b65896dfe25b7d896cfe25b3e896ce625b47896d1625b5b896d6625b6f896db625b87896e1625b2f896cb625b2c896cb425b2c096d2e25b498) else (0x895b8236fe88dbf22370688ddbc2376d08dc0a2370888dc622372c88dd122371288dcd22359708d6542352688d4922352288d4ca2354288d55a2356e892e7a24b9c89303c24c0d092e8a24ba8892ee224bcc892f9224bb2892fba249df0927742496e8925b22496a8925ea2498b09262a2498a09267a249b6882e7a20b9c882e9a20c0f08303420baa882ea220c0308300220c0108300020bb8882f3220be48825c2209df0827742096f0825ba2096e0))))) else (if b<96 then (if b<93 then (if b<91 then (0x84ee0213cc884f92211df0847742116e8845b22116b0845ea2118a88467a2119f084678211b6885bfa216fc885c2221718885cb221744885c0a21706885dbc2176d085c3a2159708565421526885492215230854ca2154288555a2156e889bfa226fc889dbc2276d089c0a22708889c622272c889d12227128894b2225970896542252708949a225260894922254a88948a225330894ca2253208950c225428895082255688955c225560895ba2256f0) else (if b<92 then (0x8b00422c0008af3222be488b02c22c0908a76c229d908a62c2298a88a6282296f08a5ba2296e08a5ec2297a88a5e8229d308a74a229d208a7442299f08a67a2299e08a6da229b708a6d823f1888fbf223f0888fd8c23f6088fd8423f6008fcb223f4488fd1423f4408fc1a23f6b08fda423f4e88f64c23d9108f50a23d2688f4ca23d8b08f62a23d8a08f62423d5708f55a23d5608f5ba2139e884e72213a0884e9a2140f085034213a8884ee2213b90) else (0x9548a2552209549a2553289555a2556e89562a254bd8952f2254ab8952a6254b38952c6254bb89529e254a6895296254af8952ba254ad89532e254ca895326254df89537a254dd8953de254f68953d621bb8886ee421bb8086e7221ba888700c21c0088700421c00086f3221be4886f0a21ba688702c21c0888702421c0808676c219d908662a2196e8865ea219d308674a219d20867442199e8866dc219b68866d822bb888ae7222ba888b00c22c008))) else (if b<94 then (0x80748201d108062a2019e8806da20708881bf220763081d8220761081d8020718881cb220744881c1a205330814ca2053208149c205268814982058b08162a2058a0816242054288150c2054208155a205570815582056e8815bc2056e095bf225708895cb225744895d82257228959fe2567d8959f225687895a1625684895a8e256a1895a82256b7895ad6256b4895b3e256cd895b3225697895a5a25691895a0e25681895a2e25689895522255230) else (if b<95 then (0x9c74c271d109c76c271d909c77c271dd09c78c271e109c7ac271e909c75c271d509c7bc271ed09cbcc272f109cbec272f909cbfc272fd09cc0c2730109cc2c2730909cc3c2730d09cbdc272f5083bf220f08883c6220f2c883d1220d2308349a20d2708349820d328834cc20d3208350a20d4308350820d5688355c20d560835ba20d6f0835b8203a8880e722039d080e702040308100220401081000203b8880f32203e48805ea2016e88074a201d30) else (0x9b2ea66cb899b37c66cde99b37866cf699b45223bce18ef3063bd218f00863c0018f01063c2408e6786399c18e628639d218e740639f4093cb864f2c193cd064f32193d8864f60193da864f64193e1024d5619355064d8a19362064dac094f38653cc195008654001950902516e1946986519e1946706517a194628651d8194748651d01946d8651f409c2cc270b109c2ec270b909c2fc270bd09c30c270c109c2dc270b509c32c270c909c33c270cd0)))) else (if b<99 then (if b<97 then (0x9932c664ae9992b2664ba9992e2664de9993da6651489af5866b5319ac9a66b2499ad5c66b7099ad3a66b4919ae2a66b2e99acb266b3a99ace266b5c99add2669a419a5a8668ea99a39a668e499a4326690b19a3ca668ee99a3b2668fa99a3e26691e99a4da6695489bcd866f6019b9fa66e7c99babc66ee299ba9a66ea119ba1a66e8499ba4a66e9099bad266ecc99bb3466ecc19b57066d2219b5b866caa99b29a66ca499b33266ccb19b2ba66cac9) else (if b<98 then (0x9729a65ca49972f265cbb1972c265cae9972b265cca99732c65cca19737a65cf6988ee8623b8188f08623bc189000624081890902218a188620621d21887d0233ba18cee06340018d0902318a18c620631d218c7d02471a191c6064722191d8064768191e10245421915006458a1916b0267361999fa6667c999abc666a6999a8466686999a1266688999a4a66690999ad2666cc999a5a6655c199488664d11992aa664a6999292664db199332664f29) else (0x965a8658ea99639a658e49963f2658fb1963ba6590a99647a65936987c6861f18187c8861f60187da061f8408749861d4418750861d401874c861d8a18755861d6e1876b022f1a18bc6062f1e18bd8062f4418be1022d4218b50062d8a18b6b0243ba190ee0644001910902416e190628641881905e8641d2190678641b61907d025f22197a6c65e7e9979f265e9f197a5a65e91197ac265e86997a1265ea0997ad265ecc99752065d2219755865caa9))) else (if b<101 then (if b<100 then (0x892186360e98d8326364f18d84a6361498d8826362898d8d26352218d19a6346498d1ba6347298d1ea63486992a1a64a84992a2a64a8c992a6264aa8992af26496a1926286486e9921b26487699220c648829922086488a99225a60baa182ea060c001830902096e1825f86097a1825e0609d21826286099e1826d8609f4096f0865ba8196d0465b26996c9265b3e996ce465b47196d6a65b6e996e1a65b2c996cb465b2c196d2265b5c996dd2659901) else (0x84c9a61324984caa6137d184cb261338984ce461338184d226135c9845a86119e18439a610e49843ba610fa98442a6110b1844286111e9859fa6167c985a1261690985a82616b4985a0a616d7185488614a6985292614ae9852ea614ca98537a6260e98983262612989852626209898a262634989498625221894c8625421895586256e1892746246718919a624661891926246f1891ba6246e1891cc624729891c86247a9891ec6247a18921a624871)) else (if b<102 then (0x8337c60cde180ea06039c181000604240805e8601d21807d020708181d80607840814c860526181628605421815586056e1816b0257221959f265684995a82656b4995b3265696995a4465548195488654bc9952ec654a69952ba654ca99537a654f6986ee061c00186f0861c081870902198a186748619b61867d022bb818b00062c2408a6286296e18a5e8629d218a678629b618a7d023f1818fd8063f4418fe1023d4218f62863d5618f6b0213b81) else (0x20ca62832b8a0cba283328a0cde284ce0a110a289198a246e2891c8a247a289218a4882296cb0a5cca29bb30a6cde29c2386708c19c6386718c19cab8672ac1839f260e84983a4260ea0983ad260d2218349860d3218350860d561835b860ca698329c60ca61832ba60caf1832b860cba9832ec60cba18332a60ccb18332860cde9)))))))) 22 i
def r2 (i : Nat) :=
  let x := r2V i
  (x &&& 127) ||| ((r2D0 ((x >>> 7) &&& 255)) <<< 7) ||| ((r2D1 ((x >>> 15) &&& 127)) <<< 16)

def hit2 (t : Nat) (v : List Sig) := OrbitLookup2153.orbitHit 4 6575 13271 4096 o2 f2 r2 rot 2 t v

def hintIndex (i : Nat) := field (fun b => if b<51 then (if b<25 then (if b<12 then (if b<6 then (if b<3 then (if b<1 then (0x883f09c0409c220000007c010880409c0a0880207c0100000000000880409c0a07c1f004010880109c01088220100409c27028050880409c0809c040000007c010880408c0508c010880308c0308c04) else (if b<2 then (0xec3b010220ec220043b010220943b0000000000004000000a010000fc080fc010fc080943f000020000000000004000000a000080ec220fc270080a0883f09c040ec3f0883f09c010ec220fc270103f) else (0xfc3f0042707c3f0fc3f000020000000000004080283b12c0212c040ec4b004220ec4b12c02000000000000408010001340a1340a0fc271343f004270fc4d134020000000000000010000002808))) else (if b<4 then (0xec020040002004000270fc2709c3f09c3f09c270fc2709c3f09c270fc2700000004000100a124010e01f1244900002000000040000008028010ec010ec010881f0ec3b0ec0200000000000000002004) else (if b<5 then (0x7dc007ac00808007d0007ac0000400028200ec3b0ec3b000040281f0e03807c1f0e01f07c3807c1f0040402800028000000000000000000000000800004000200a0000a000220ec22008220ec3b0ec3b) else (0x80c00804007f40a0080a0fc0a0040a0fc0a0200a0103f0283f0283f0283f0283f0283f0283f08c0a0fc0a0fc0a0fc0a0fc0a0fc0a0fc007bc007bc007e0007e0007ac007b800000007f8007ac007dc00)))) else (if b<9 then (if b<7 then (0x13001010020103b010010103b010080100a0ec040ec040ec040ec040ec040ec040ec040ec040ec040ec040ec040ec040ec007b4007b4007d8007d8007d8007b000000007fc007f4007d4007d4007d400) else (if b<8 then (0xe0010e001001ea0043800438004380043800000001ea001fc001f300200001ea001fc001f30000007c010880409c0a0000007c010880409c05000010000007c010880408c0508c010880308c0308c04) else (0x4000043b0103f0fc0a00022010000200009c2709c2709c040000100000000040000a001e700000001e8001e900000001f0001e9001f1001f2001e8001e9001e90043800438004040040a0e0010e001))) else (if b<10 then (0x8c00001f900400000000044c004017ec047b400001ec0003b819fa810238140a029ef00000001ee0003f08dfe001eb000000080007c1f07c01028000000002800088040002709c2709c270283800400) else (if b<11 then (0x734010f0050000073c030ec040f00544c6a52c9574103488764f88a0ec040f0050143b0883c08c040119d3a43c0f0050ec220f023010010ec040f03c0143b0883c08c0400c2200001000000280000000) else (0x103a0000344c6a564af58cb70f0050e83c00c036f8fb488764bc7f0f0050e83c00c0364ce30f0050e83c00c010e8030843a0f00300000001ce000007340073c00000000003b000040f005001cf00000))))) else (if b<18 then (if b<15 then (if b<13 then (0x205b13d9281e43a00c3b011402303a0ec0300c3b011923883a0843b08803004210e83b00c00000006e80000000000006f03c00005000006e80000000000006f03c00005000006e801001bc0f005001bc) else (if b<14 then (0x40152c950e0010e03c004380053e2292f1fc3c014380f00100438004380041f0e03c004380f00100000001af000006b800000000003a00c3b00004001b0000006b8010ec04001b0001b0015121a531) else (0x8c05001a20000000000000000e001004006640063c3c00005001a2001a20083800000000000003800001001990018f0f00001400664030018f010380e0004987744c6a0e0014c0804fc8b0f0050e03c))) else (if b<16 then (0x8005ec005e8010013a00c00580040017a00000001605fcc844c6a564af5bc8658cb40f03c0143c08c3c08c050154b2543c08c3c08c05488764f8864bc7f0f03c08c3c08c050f0230f0230143c08c3c) else (if b<17 then (0x5ac02000005a8010014700c004b005000050016a4486948475528914b87c0ec3b0116e2f43b0883b08804560ae0ec3b0ec040ec3b0103b0ec04000000000000000000005e8004e8000f0050017b) else (0xc4050b8050010b004000040043005000000006300000190000000000000000000e000558040011f0151019c38004010e01f0e01f004010e0380e01f07c010e03807c1f004000000000000000005a800)))) else (if b<21 then (if b<19 then (0xac0e014050f03c0140506c02014050f03c01405068010140505c030140504c040d41b44c6a0d01a0c4170b8130f0050d41b0d41a0c4170b8130d4050d01a0c4170b8130f0050c4170b8130d0050b813) else (if b<20 then (0x404000460cc3c00c3c00c3c004210f00300c000000000001000031102f014220f0230103c0883c08c010f0220f02300c220100444067004010e0380040103c050e0010a80e0ac0f0ac010a80d0ac0d) else (0x8c3c08c3c08c230f02308c3c08c05014000000100002000000000000003010001082b0f0010f03c0042307c3c0f001004000000000001014470d83b00c210ec22004210ec0300c00000000000000000))) else (if b<23 then (if b<22 then (0x40143d0900107c3807c0107c380e01f07c3807c1f00401000000080100c05000050f8260ec220ec220883b0ec3b0ec04010000000200403010000f0230f0230f023014230f023) else (0xd4050f0050d0050c4050b80506c1a05c130143c0141b0143c0141a01417014130d41b000000d01a0c4170b8130d41b0d41a0c4170b8130d01a0c4170b8130c4170b8130b81301401000010140000000)) else (if b<24 then (0x90060980908c0509807090060980908c050980608c050980308c0308c0500438004050e0010ac0100000004380040f0a80e0ac0f0a80d0ac0d0ac0e0143c014020143c0140101403014040f005) else (0xfc27010040103f0883f09c04000240142706c230681704c000901a0142706c1b08c1a0681705c1304c01000000901f07c1f00405098220102308c2308c2308c050ac010d82200c3300c2f08c2308c04)))))) else (if b<38 then (if b<31 then (if b<28 then (if b<26 then (0x73800008000000000000001cd00001001cf0000000000000000880409c050280500008010220fc27011e04083b0883f09c02550a1028220fc27011ad3c83b0fc220fc27005df40c220ec220102701422) else (if b<27 then (0x940308804728f60883b08803010030ec00000000000000000000006e800004000000000000000006f0270140a014040003f021542843f021ad3c83f005cb3ec27014250fc2700c0800c3f0000000000) else (0x3a59338c3c0f0050f0230f023014010f03c0143c0f0050000000002001af00000000000000000001001ae0000000000000000282500c0800c22010006c03b011cc3d43b554a80ec046b0f10883b08801))) else (if b<29 then (0x1c80100a7990a135542840a1340a6b4f20fc271343f005df425cb404270fc271344d5fccc44c6a564af5bcc158cb7014050f14b255a53b9be3f03c0f005488764f88a4bc7f0f0050143c0f0050159d) else (if b<30 then (0x2001e2000000000000001001e102004000007200078800000007840076c007203f0000a001e2001e2001e2008007200078400000000000076c007203f02800001e10040076c007203f0280076c03) else (0x11ac3c43b12c010883b0884b12d3d225121a5211d54a250040112e1f83b5b8c0670e80ec3b0103b0ec04009582b97e32c3b011622d83b0ec04011a43b43b0ec04648e20ec3b010010ec3b0103b0ec04)))) else (if b<34 then (if b<32 then (0x764080280076800000007640078c3b00004001c9001da001da00000768020ec04001d90000000000001e30ec000100072400001d9004007703b010007240078c03001c901404779080ec4b0098e3704b) else (if b<33 then (0xec01638dc0ec0107c0107c3b088010ec3b0000000400008000000000000000000000000000020040001f000010003f0043f550a10fc0107c0107c3f09c010fc3f000000080000000000000000000400) else (0x1ab01401634db124010e01f07c491251019c010053b21d4824838668e60e0015b0be5f0c90e038004010e038004380e00100000000000000200000004000000000000000000200a07c01004010ec01))) else (if b<36 then (if b<35 then (0x801000000000fc270fc27028270fc27550a109c3f09c270fc27014270fc2709c3f09c00000000040000004028000003800001001aa001ab001aa00000000000e001004006a8006ac006a804) else (0x35000354000009b000d50000035000000d40000000000354000009b0000000004000020000100000000000200a0000a00000000000ec040883b08802638dc0ec220ec220103b0ec000000200400)) else (if b<37 then (0x100a0041f0e01f0043807c1f0043807c1f0e01f07c00004040280002800000000018b0018c001530018c0018b004006300400153014000140062c000000000000000000000000000) else (0xe01f07c3807c1f00800004080283b0883b088220ec220883b088220ec220ec2208802000010200400004000000fc3f0fc3f09c3f09c3f000000000000400000000000a0ec020ec3b0803b088020ec00))))) else (if b<44 then (if b<41 then (if b<39 then (0x103b0880402004029de0598e371ac055e507022011ca0500a0fc0a0080a0fc0a0040a0143f09c0a0200a011e606d54285ad069df05dcb04c2701401000010100a000000000000004028000e01f0e01f) else (if b<40 then (0x140009c0809c0302000000000000001400010270102709c2708827010270100000000000000180002400014010e0010e0010043807c01010010298d36c1f005dd039e403c040ec04008040ec0400404) else (0xec04088040883b0ec020ec040ec3b0043b0ec04000000000002802000000000100c040fc0a0fc27014230f0050f0050f0230f0230043c0f005000000000000003000220102208803010000000000000))) else (if b<42 then (0x2709c0a09c2709c2709c0a00000000010000000404014380041f0041f0e0010e038004000000000000004000880108801000000040000000000270042700400000040000000800000000000100c05) else (if b<43 then (0x9c3f09c3f000000000000022008220080000000000000041f0041f07c1f00400028000000000001010050000500000000000000000000000000000000000000040000a0000008804088220100000000) else (0x400004040280000000000000100a07c1f07c1f07c3807c3807c1f0e01f07c02000010200a0882208822088220883b088220ec220883b088220ec220ec22088040080000408010000102709c3f0fc3f)))) else (if b<47 then (if b<45 then (0x7c00000000380003c22010220100408804088007b400000007b0007fc007f4000580000000054000700005027028270140a09c0509c007bc00000007b8007f8007ac0006c00000000680005c0004c01) else (if b<46 then (0x40d1080d0a4420040000000000000340f0a8010040e03c2a1082b038420a8420ac0d0a80000000000000000107c1f07c220882208822010270140008c000001f0041f0040107c00000007a8007f001) else (0xa8410a8010382a10441104000000c0040003c0d038001082b1082b03c2b1082b0ac010040f0ac420ac420ac2b1082b00400000000000f0a4010040d1040d0a44100000000010000000000038001080d))) else (if b<49 then (if b<48 then (0x20a002080683406834068340020a0020800208000000000f00001000010e00e03c00000000000100400000380e00c004380340e07c0e0040113c4f0040113c4f13c000000c004000380d03c0003c41) else (0x42b0ac0f0000103400034000042b0ac0e03c4203c0c0043403c4203c0d03c0e1080f1080f0680f1080f1080f1080f03c4203c4203c3403c4203c4203c420020c06834000000020a00208068340020c)) else (if b<50 then (0x400748000ac0500000001d700400035042910540c2b0140f0142a004010100e0100f0a8420ac0e1082a1082b004420a8420ac0d000000020c0020a0020800000000000380103c0f0002a038000ac2b) else (0xa40100403034031040d0a4410a801105bf00000000006fc006fc010040070400709bc0ac0500000001c60040e000fd37842034fd290fe3ec2b014290040100c0d00c4203442004427440074dcf74401))))))) else (if b<77 then (if b<64 then (if b<57 then (if b<54 then (if b<52 then (0x1840114c0114c0114c01004010158a348616280d03861004381080100438108010e0010e0010e00503c05004420041f108426c8006c801004006cc000a8046d1b000000001b80040f3dcaa0a8043e0f6) else (if b<53 then (0x6000100400604006000060d3a60d600ac0503c050040d03800334de1082b1082b03cce3202b1082b334a433886338b40ac050ac010040503c050ac420ac2b1082b0ac420ac0114d51264015440114c0c) else (0x7c3807c1f5c000000005cd6b031700040100171001700017351c2a0100e011734b0010340f0000f308a3104c32f42a1042a308dd30c910a80430c7c0a8010040403804104411058000000001835ec0c))) else (if b<55 then (0x1644f004560045900459004010044f13c4f44c6a0f03c0143c0f0050f03c0143c0f0050f03c014011251b1c91d004010043800449004490380f004380041f0e01f0043807c1f004010e0010e01f0e01f) else (if b<56 then (0x10010e005004534410f19801004015c98200000000000000000000000d7000002743800438030010e00d0381f038010e001004010e05345c6d00438008010e0530043800c010e00407c040045613c01) else (0x14010102b0ac2b0042b0380f1080f03001014340ac0f1080f0040f0340f0381a1601a06c1a1601a05c1a04c1a0150d43800000014680103c650040100070000010e0010380f004010e0494406700438)))) else (if b<60 then (if b<58 then (0x5004000ac2b004050ac2b0ac0f004000000000001030010040101400000000340e0141f108011080f0044200442108010000000400004030a801034010000000400004030ac01034010000000400) else (if b<59 then (0x1005004000000000000038530085300c0407c04004010f03c0f03c0f0050040000000004000040e03c1f07c1f07c1f0e01f178590041f004011781f1645e07c59004000100103c000a8010102a03801) else (0x1203706045120321203702c180c802008181203212037048370ca10856190105916459068050ac0f0142b03c1a068551801a0681b1801a0685506817068131801a1801a1801a00001000010000000449))) else (if b<62 then (if b<61 then (0x2c020001807845048450482d1143202c02048320b445000000000000000000000000b008006ec1e0600012012120121200b008120dc2d1200000000000000000002c0200000048180c8480dc1807832) else (0x140120085002c0200850140020e402008390080202c12078391145106045144181440b008021445100839008390080202c12060200600212052078520785202c02008371484814800000000000000000)) else (if b<63 then (0x2c2d0a00210c4300000000000000002c0000012078001140b1140b0c82800845114000000b0000000000000000481802c001200b1200b0dc2800848120020e4020e4020480202c180799037c4314012) else (0x114000000b000120600012037120370783712037120370dc0200837120370dc480dc020e40200839008120601e1004e02c0b1380b00802138281004e138000000b0000000000000000601e02c4302c43))))) else (if b<70 then (if b<67 then (if b<65 then (0xa0020e43902c2002c120601e00000000020080000000000000000b000180780010c2d10c2d0482d10c2d10c2d0b4020082d10c2d0b4430b400000000600b00012078000784506032114450c80200845) else (if b<66 then (0x2c000481e0c8450c8450c832114320c8020083211432114320c80002c000481800018000000dc481204800837120371200000000000120601e02c281002802c281002800802100280a0400a02810028) else (0x4818078000000000800000000000004818078000a0400a0400a02800802100280a0400a028100280a03902c120601e0080200000000000000002c00000000601e000000b44310c43008430b4430b400))) else (if b<68 then (0x213058300020e05830058300021307848078480780b0083507812078181201e1201e1201e06c1e1201e1201e06c350000006c350020b06c35002110021206c350020f06c3506c350021202c0002c00) else (if b<69 then (0x10c120442c000000442c002070442c00216002170442c0020d0442c0442c0021706045060450600b00830060120601e11418114181141805818114181141805830000000020905830002130020905830) else (0x82d0b4120780000818000370dc020dc37078400000b0000b0000b0081200818060021201e0003204800048000dc370dc020dc1804843048430480b0082c048180481e10c1210c1210c120441210c12)))) else (if b<73 then (if b<71 then (0xc8480dc0b41d030c804060040dc050c8020080406004120321203704800862148480002c00000000a0020a0280a00b000000b412000320c8020c8320601800037078000a0020a0280a00b02c000b42d) else (if b<72 then (0x400fb0dc050b4020080304803121d40000000000760027500000000001d47340002dd673dd400802001d5000320103701400049062b0180c8480dc1811432120370090629c1e0c8480dc18418f411448) else (0x10fa3d82d0080200c1200c4570c00000000000071c02049c770c00000000000070dba0000b70c0200800710000b5bb70003715bc0dc0507805060003fce112012120023fca7120123fcf41200b0b403))) else (if b<75 then (if b<74 then (0x143c0f0050043c08c3c08c050f03c015b500000000006e4026e5b500000000006d5ae0000b6d402008006d8000b4030c804060046ddb0078f92984504845008f92ac45048f93cc2d1143202c2d00c32) else (0x85a1481e0085a1480b0085f0085f00802008371484814820009131a9592bd6f305632dc3c0f0050f03c0140508002080020e4020e40200802081221d93e2292f1fc3c0143c0f0050159d3a59338c3c)) else (if b<76 then (0xe420009191bc020083915d291e9362114523c48078200082000839008390082008002008020e457578b25a0ba5e0c61201e008020e4010083900c020e4040800465ce5680eb1201e0085a1205207802) else (0xec3b0100408002080020e402008020e402081582b97e32c3b0ec04588b60ec3b01004690ed0ec04648e20ec3b010010ec3b0103b0ec040083900839080020e4020e40202c1206020060020e4020e402)))))) else (if b<90 then (if b<83 then (if b<80 then (if b<78 then (0x8020083915d5e2c9682e845061883440200839004020e403008390159739445061a83c00216845144180080216845144180085a1440b0085f008020085114420009121a5211d54a2503b0ec044b87e) else (if b<79 then (0x2203a0e80300c3a00da33b19b39c3a0e8030043a0e8030e83a00c020e4020e42000839008390080b0481e0083900839080024646f008020e4574a47a4d884114185409808002080020e4020802000839) else (0x8390144365012680eb6a0f00085a10c50048020085a140120085a1400b008020085014020009111a1572b43a0e8035f4ca5b4bf0e83a00c030800208002008020e4020e402081201d03a00d4924d3c))) else (if b<81 then (0x83900839080020e4020e4120080b0601e0083964020009191bc020083915d291e8430494523d50260200082000820080020e4020e402008020e457578b210c1204978319883440200839004020e404) else (if b<82 then (0x4003a8a61140b114023a8e01140b0a0010a00200801114450000002da6000006a4026a4000000069800001a669c00000120602802c01004003bca91200b120023bca71200b0a0010a0020080112048) else (0xb6540000198009980480000000654000019565800000180782802c01004e42a44302c43008e42944302c2800428008020044310c000000067800001a1008000000b678000019e67c000001207828)))) else (if b<86 then (if b<84 then (0x15c4e02c0200802138281004e138200091019c380e0010e038004014b47d4ec8752092080020040108039008390083900838004010e03800401584b55b0be5f0c90e03807c1f004380e0010e03800400) else (if b<85 then (0x80020e4020e4120601e080024606e008020e4541000b4d4835108e53c97080020802000839008390083900802008391504002d672e57731587340020e40300839010020e4051000215c4e02c0202c02) else (0xc4298450603211432008c4380450c802008041144500000610006240202d846140000012061840000033ce112037120370783712037008cf29c37120370dc02008050dc480dc37120370083900839))) else (if b<88 then (if b<87 then (0x590005a4025a40b59165000000601e59165000002e0df10c2d10c2d048120b4430b4022e0a50b4430b42d0080200c2d10c2d0b4430b400000005d000061790097902d745d400000120780007974) else (0xc020e404008390155d2c518008574586c0080200802571665d98608002000000000035800000000000027800364002800200820008200e4020e4020e402000d600000358000009e0000036400000a0)) else (if b<89 then (0x2c400a0400a0020a00200801100280a0400a028100280a0020e4020e42002c2002c120601e08002008020e4544606e49c784d4835108e53c970802000820008390083900839008020e4010800100839) else (0xb5462406200854518c702c1207862008020e4450082011445114455489a00854548d302c1206062188020e44800820120201203712048000000015a0015f0095a56c00000120601e02cb02882810028))))) else (if b<96 then (if b<93 then (if b<91 then (0x4818078020e439008200e4390e420080394a87b2cc120601e1892b0084a188020e439008200e4390e4394e485008544e4bc02c1807862008020e42010c2d008390802010c2d080430b4430802d10c20) else (if b<92 then (0x481e50400234a60c8450c832114320c8450c832008020103211432114320c8020000b5314d0000004818000180014c00000258e112048120370080201437120371211c1cc02478021280b048bb) else (0x802459254d1435380200800000002702000000000000009c00000360000009f00000368024dc020000b4c933000000601e4e0004c93300000208df10c4310c2d0080200c430b4430b4020000b50542))) else (if b<94 then (0x80000000000020012349000000120601e00028100280a0400a02800802004400a028100280a0400a0280e40b048180782000839150020e4010083900c020e4040083901420080024606e49c7800802) else (if b<95 then (0x10320585c0585c058150581c05804058140143706c5d06c5d06c1a06c1706c1306c051cc0b04818078200e42008039080200e42008039080200e4200800202c0002d1445400000120601e1c4000086b) else (0xf00108c3c08c3c014000080000800010000c8020c80200c1200002048000080070005000370080200c120000200800000370c837008370dc04008040dc1800c2d0445b0445b04410044030441d04419)))) else (if b<99 then (if b<97 then (0x843a00c3a0043a0e80308039008570e402080020e40215c0200403014020083b0ec04008220ec3b0103b0043b0ec0408018008570e43908002008570080100c0408004008021203c0f005008230f005) else (if b<98 then (0xe0010041f004380043807c1f0e0380000200012000010002d0080202c0000800000320080202c000080000001000370080202c20008570e4200080215c12008010100565002008020e83a00d91009bd) else (0x800000000080000000000000000200000000000b4120b4020b4020b42d04800008000001e00032008020600000800000370dc020dc020dc37078200e40215039080020080215003010050080210038))) else (if b<101 then (if b<100 then (0xb400000020000002c1207820114021144511445000000000002c12060200dc4800848080480dc481200000800000280a028008020a0280a00b0800b0080215020008390e4390e4010800100c0401402) else (0x2c12000120601e0802017c0217c5f17c201685f00000000120601e0000208040008401004010000000000000b0601e0b4200b42d0b42d0e42010c2d0082010c2d080430b4430802d10c20)) else (if b<102 then (0x805a0080b000000000200002000000a028008280a02802c201500100c0401420008020080200000000000000000800000000002d0082d04802000000c8320c8020c8320600200018000370083707812) else (0x5a1685a1685a0485a0b42d0b42d0b4370041f010230b4110c8160dc1b0000b048180782008020080200805f0805a17c201685f0805a17c201685f)))))))) 10 i
def hintVal (i : Nat) := field (fun b => if b<4 then (if b<2 then (if b<1 then (0x906800048300002412000120500009020000480c000240400012010000516800028b000014540000a2900005128000289000014460000a22000050e8000287000014360000a1a000050a8000285000014260000a1100005068000283000014160000a0900005028000281000014060000a020000500800008b40000458000022b0000115000008a4000044a00002240000111800008880000442000021d000010e0000086c00004340000219000010a80000850000042600002120000108800008340000418000020b000010500000824000040a000020400001018000080800004020000000) else (0xd0e22806871100343882018844500a0a21004c710802538860129c420094e208048711402438880121c430060a2100305104018188400c0c410058e21002a7108015388200a9442005422100287114014388800a1c430050e20802851040140882008844500442208001080800084020003a290001d010000e80400064540003222000190d0000c80800064020002a2900015010000a804000445200022020001100800068b400034480001a1b0000d0a80006844000341a0001a090000d02000068080003402000122d0000916000048940002448000121d000090d8000485400024280001211)) else (if b<3 then (0x510e2182887104141088409c1c4204e0a21026e7108136388409b044204d0e22826871101343882098844404a0a21024c7108125388409284420490e2282487110124388603214640190a2d80c8514c06428a2032144b018ca3680c6519006328b60319455018ca2a00c65144063289a030846d018423200c2116c06108aa0308451018422680b07108058388202b9c420158e2100ac1108054388a02a1c440150e2180a8710405108860241c42011ce21008c710804608840229c430114e208088711404438880221c430110e208082110c038388401b9c4200d8e21006c1108035388601a9c41) else (0xd5c22106ae110435608821aa1c450d442220690110834708841a384410d18220868211143410884131946d098ca3204c65134263288812b9c42095822104a87114254388812a1c43091ce21048c1108244388a1221c440910e2184887104237388411b044208d0e228468711016328da0b19464058ca2d82c6515416328a80b19444058ca2082c211b416108c80b0845b058422a02c2114416108880b084410560e2102b0710415738840ab1c42055822102ac110415508820aa1c450550e2202a8710c15438820a884420520e21028e710814638840a304420518220828a1104144388a0a21c44))) else (if b<6 then (if b<5 then (0x4114e20a088711504438888221c434110e20a082110d038388481c0c4240e0221206e7109036388481b144240d8621206c1109035388681a9c4140d0e22a06871110343882818844540a0e212050510902638848129c434094e21204a710502528848128c4240942212048711502438888121c434084222a0307109018388280c14424060a20a0301105016388480a9c424054e20a02a5109015188480a84424050e22a0287111014388680a1c414050a20a02831050140882808844540442208ac2110846108962308442116022108ae1108457088222b0441114422188a2110836108881ac0442) else (0x4550e22a2a8711115438868aa1c41454422122a2110514818848a39c424518e21228c510914618848a304424518220a28a510514518828a284414510e22a288711114438868a21c41450422122821105138188489b9c4244d8e21226c5109136188489b044244d0e22a26871111343882898844444a0621224c7109125388489294424494621224a1109124388a8921c444490e21a24211110642896831944d4184226a0b07109058388282b9c424158e2120ac5109056188482b04424150e22a0a87111054388682a1c414144221a090710904738848231c424118a21208c310904608848229c43)) else (if b<7 then (0x4d58220a6a8711535328869a884444d4422126a2110534818849a40c414d20221268e310934708849a384414d18620a68c110534438889a084454d0422126821105263289a93194444984226a4c21111258188492b9c42495862124ac1109254388a92a1c444950e21a4a2110924818849239c424918621248c1109244388a9221c444910e21a4887105241088691c0c4248dce21246c3109236088491a944248d0e22a46871112332886919944248c422222c6511116328828b084444584220a2b0710515818848ab9c424558e2122ac510915618848ab04424558220a2aa510515518828aa8441) else (if b<8 then (0x8044235c022118e01108bb0088455800862a400431360021893001046a8008234c004118a00208c3001045c800822a40041136002089900104498004235400211a600108c50008461800422e40021152001089b000844c8004224aac651355632888ab194415584225aac211095610882a321444518ca26a8c651114632882a3104415184225a8c211094610882a2c0c425160620a8b011094571884a2b8442515c220a8ac31054560882a2a1c455144221a8a2110945108829b2144b4d8ca26a6c65111361089a9b084444d6062126b0310535808849ab8c424d5c22126ae110535618829ab0442) else (0x204748d30210c6d8104236c08211b203748d30190c6d80c4236c062119203108c7013a4698088234c044118602208b3010846a8084234c042118e02108c3010845c808422cc02431b601218bb0090c558048235c024118e01208bb0090455))))) 29 i
def hint (i : Nat) := hintVal (hintIndex i)

def ok2 (i : Nat) :=
  let t := r2 i &&& 7
  let v := replay basis 2 (r2 i >>> 3)
  decide v.Nodup && (MinorHubAdapter2153.short 0 2 (r2 i >>> 3) (hint i) || !jump marks 5 (fun t w => !(hit5 t w)) 3 t v)

end Num70

open Search2153 Cache2153

namespace Num70

def Transport := ∀ g < 4, ∀ depth code k t,
  Marked2153.Impossible marks k t (replay basis depth code) →
    Marked2153.Impossible marks k t (replay (rot g) depth code)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H5_0 : span ok5 128 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H5_1 : span ok5 13 128 := by decide +kernel

theorem all5 : span ok5 141 0 := (spanJoin ok5 128 0 13 H5_0 H5_1)

theorem proofs5 (i : Nat) (hi : i < 141) :
    Marked2153.Impossible marks 5 (r5 i &&& 7) (replay basis 5 (r5 i >>> 3)) := by
  have hh := spanAt all5 (Nat.zero_le i) (by simpa using hi)
  obtain ⟨hd,hc⟩ := Bool.and_eq_true_iff.mp hh
  exact jumpSound (bottom := 3) (stop := (fun _ _ => true)) (by intro t w hn h; cases h) 2 _ _
      (of_decide_eq_true hd) (by simpa only [Bool.not_eq_true'] using hc)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_0 : span ok2 78 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_1 : span ok2 102 78 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_2 : span ok2 99 180 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_3 : span ok2 128 279 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_4 : span ok2 117 407 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_5 : span ok2 120 524 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_6 : span ok2 81 644 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_7 : span ok2 58 725 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_8 : span ok2 33 783 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_9 : span ok2 80 816 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_10 : span ok2 42 896 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_11 : span ok2 69 938 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_12 : span ok2 76 1007 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_13 : span ok2 51 1083 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_14 : span ok2 90 1134 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_15 : span ok2 109 1224 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_16 : span ok2 106 1333 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_17 : span ok2 112 1439 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_18 : span ok2 105 1551 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_19 : span ok2 66 1656 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_20 : span ok2 98 1722 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_21 : span ok2 84 1820 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_22 : span ok2 103 1904 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_23 : span ok2 50 2007 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_24 : span ok2 71 2057 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_25 : span ok2 72 2128 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_26 : span ok2 79 2200 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_27 : span ok2 31 2279 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_28 : span ok2 77 2310 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_29 : span ok2 103 2387 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_30 : span ok2 107 2490 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_31 : span ok2 101 2597 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_32 : span ok2 105 2698 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_33 : span ok2 121 2803 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_34 : span ok2 103 2924 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_35 : span ok2 120 3027 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_36 : span ok2 91 3147 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_37 : span ok2 92 3238 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_38 : span ok2 108 3330 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_39 : span ok2 104 3438 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_40 : span ok2 76 3542 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_41 : span ok2 109 3618 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_42 : span ok2 113 3727 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_43 : span ok2 99 3840 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_44 : span ok2 97 3939 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_45 : span ok2 104 4036 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_46 : span ok2 113 4140 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_47 : span ok2 124 4253 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_48 : span ok2 120 4377 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_49 : span ok2 104 4497 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_50 : span ok2 85 4601 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_51 : span ok2 103 4686 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_52 : span ok2 115 4789 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_53 : span ok2 115 4904 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_54 : span ok2 115 5019 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_55 : span ok2 92 5134 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_56 : span ok2 77 5226 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_57 : span ok2 108 5303 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_58 : span ok2 102 5411 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_59 : span ok2 79 5513 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_60 : span ok2 90 5592 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_61 : span ok2 109 5682 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_62 : span ok2 103 5791 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_63 : span ok2 65 5894 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_64 : span ok2 101 5959 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_65 : span ok2 115 6060 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_66 : span ok2 114 6175 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_67 : span ok2 108 6289 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_68 : span ok2 101 6397 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_69 : span ok2 77 6498 := by decide +kernel

theorem all2 : span ok2 6575 0 := (spanJoin ok2 3027 0 3548 (spanJoin ok2 1439 0 1588 (spanJoin ok2 783 0 656 (spanJoin ok2 407 0 376 (spanJoin ok2 180 0 227 (spanJoin ok2 78 0 102 H2_0 H2_1) (spanJoin ok2 99 180 128 H2_2 H2_3)) (spanJoin ok2 237 407 139 (spanJoin ok2 117 407 120 H2_4 H2_5) (spanJoin ok2 81 644 58 H2_6 H2_7))) (spanJoin ok2 224 783 432 (spanJoin ok2 113 783 111 (spanJoin ok2 33 783 80 H2_8 H2_9) (spanJoin ok2 42 896 69 H2_10 H2_11)) (spanJoin ok2 127 1007 305 (spanJoin ok2 76 1007 51 H2_12 H2_13) (spanJoin ok2 90 1134 215 H2_14 (spanJoin ok2 109 1224 106 H2_15 H2_16))))) (spanJoin ok2 761 1439 827 (spanJoin ok2 381 1439 380 (spanJoin ok2 217 1439 164 (spanJoin ok2 112 1439 105 H2_17 H2_18) (spanJoin ok2 66 1656 98 H2_19 H2_20)) (spanJoin ok2 187 1820 193 (spanJoin ok2 84 1820 103 H2_21 H2_22) (spanJoin ok2 50 2007 143 H2_23 (spanJoin ok2 71 2057 72 H2_24 H2_25)))) (spanJoin ok2 290 2200 537 (spanJoin ok2 110 2200 180 (spanJoin ok2 79 2200 31 H2_26 H2_27) (spanJoin ok2 77 2310 103 H2_28 H2_29)) (spanJoin ok2 208 2490 329 (spanJoin ok2 107 2490 101 H2_30 H2_31) (spanJoin ok2 105 2698 224 H2_32 (spanJoin ok2 121 2803 103 H2_33 H2_34)))))) (spanJoin ok2 1762 3027 1786 (spanJoin ok2 813 3027 949 (spanJoin ok2 411 3027 402 (spanJoin ok2 211 3027 200 (spanJoin ok2 120 3027 91 H2_35 H2_36) (spanJoin ok2 92 3238 108 H2_37 H2_38)) (spanJoin ok2 180 3438 222 (spanJoin ok2 104 3438 76 H2_39 H2_40) (spanJoin ok2 109 3618 113 H2_41 H2_42))) (spanJoin ok2 413 3840 536 (spanJoin ok2 196 3840 217 (spanJoin ok2 99 3840 97 H2_43 H2_44) (spanJoin ok2 104 4036 113 H2_45 H2_46)) (spanJoin ok2 244 4253 292 (spanJoin ok2 124 4253 120 H2_47 H2_48) (spanJoin ok2 104 4497 188 H2_49 (spanJoin ok2 85 4601 103 H2_50 H2_51))))) (spanJoin ok2 893 4789 893 (spanJoin ok2 437 4789 456 (spanJoin ok2 230 4789 207 (spanJoin ok2 115 4789 115 H2_52 H2_53) (spanJoin ok2 115 5019 92 H2_54 H2_55)) (spanJoin ok2 185 5226 271 (spanJoin ok2 77 5226 108 H2_56 H2_57) (spanJoin ok2 102 5411 169 H2_58 (spanJoin ok2 79 5513 90 H2_59 H2_60)))) (spanJoin ok2 378 5682 515 (spanJoin ok2 212 5682 166 (spanJoin ok2 109 5682 103 H2_61 H2_62) (spanJoin ok2 65 5894 101 H2_63 H2_64)) (spanJoin ok2 229 6060 286 (spanJoin ok2 115 6060 114 H2_65 H2_66) (spanJoin ok2 108 6289 178 H2_67 (spanJoin ok2 101 6397 77 H2_68 H2_69)))))))

theorem proofs2 (prior : MinorHubAdapter2153.Prior 0) (T : Transport) (i : Nat) (hi : i < 6575) :
    Marked2153.Impossible marks 8 (r2 i &&& 7) (replay basis 2 (r2 i >>> 3)) := by
  have hh := spanAt all2 (Nat.zero_le i) (by simpa using hi)
  obtain ⟨hd,hc⟩ := Bool.and_eq_true_iff.mp hh
  rcases Bool.or_eq_true_iff.mp hc with easy | hard
  · exact MinorHubAdapter2153.sound 0 2 (r2 i >>> 3) (hint i) (r2 i &&& 7) prior (of_decide_eq_true hd) easy
  · exact jumpSound (bottom := 5) (stop := (fun t w => !(hit5 t w))) (by intro t w hn h; exact OrbitLookup2153.hitSound (proofs := proofs5) (transport := fun g hg c q v => T g hg 5 c _ q v) (by simpa only [hit5,Bool.not_eq_false'] using h)) 3 _ _
        (of_decide_eq_true hd) (by simpa only [Bool.not_eq_true'] using hard)
end Num70

open Search2153 Cache2153 RootGlue2153

namespace Num70

def startOk (c t : Nat) :=
  let v := basis c
  !(decide (t ≤ 10+1-v.length) && unionSep (decide (0<t)) v == top) ||
    !jump marks 8 (fun q w => !(hit2 q w)) 2 t v

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem root0 : span (startOk 0) 11 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem root1 : span (startOk 1) 11 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem root2 : span (startOk 2) 11 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem root6 : span (startOk 6) 11 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem root7 : span (startOk 7) 11 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem root8 : span (startOk 8) 11 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem root9 : span (startOk 9) 11 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem root10 : span (startOk 10) 11 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem root11 : span (startOk 11) 11 0 = true := by decide +kernel

theorem solveCodeWith (prior : MinorHubAdapter2153.Prior 0) (T : Transport) (c : Nat) (ne : 0 < (basis c).length) (nd : (basis c).Nodup) (checked : span (startOk c) 11 0 = true) :
    AtBase marks 10 (basis c) := by
  intro t ht hv
  have hh := spanAt checked (Nat.zero_le t) (by omega)
  have h : jump marks 8 (fun q w => !(hit2 q w)) 2 t (basis c) = false := by simpa only [startOk,decide_eq_true ht,hv,beq_self_eq_true,Bool.true_and,Bool.not_true,Bool.false_or,Bool.not_eq_true'] using hh
  apply jumpSound (bottom := 8) (stop := fun q w => !(hit2 q w)) (by intro q w hn he; exact OrbitLookup2153.hitSound (proofs := proofs2 prior T) (transport := fun g hg c q h => T g hg 2 c _ q h) (by simpa only [hit2,Bool.not_eq_false'] using he)) 2 t (basis c) nd h

abbrev solveCode := solveCodeWith SixMinor2153.sixNumeric (OrbitCache2153.sound 0)

end Num70

open Search2153 Cache2153
namespace Num80

def basis := Cache2153.base raw
def marks : List Sig := [raw3,raw5,raw6]

def rot := OrbitCache2153.rotBase 1

def o5H (i : Nat) := field (fun b => 0x29053c00) 10 i
def o5L (i : Nat) := field (fun b => if b<2 then (if b<1 then (0x4a52a5a92a6316d6a949420432146531d2a41d0810022114ea62989529695ad8b5ad0a4a58c635ac) else (0xa5673a5a759d6928b9ce7b9cf7ca309d295be33495294ad6b4abdc95ad69525673a4e84a92a518e9)) else (if b<3 then (0xc6f76bca3294272a4eae839d0841f27be309d671a41f19d6939463194a5174251841ce4a92b6296c) else (if b<4 then (0x1908320c45299295a56c6394c5b5ae8ceb6aca0f7421273e0d5b1ab5b1cb73e2e6c1ad73e319ca96) else (0xc)))) 5 i
def o5 (i : Nat) := o5H (i >>> 7) + (((i &&& 127) * 656) >>> 8) + o5L i - 12

def f5 (i : Nat) := field (fun b => if b<5 then (if b<2 then (if b<1 then (0x1a05bc818fb1ec8053e85afe3d951a5f0129878ec116c2312045882a30046e00190f650082c6c8b1c250a324081e017a02a98b4c448a4185c068d81390214e405418dd0460cfa7620ce1abc0f23c28c4144b1c0c9c7549ba830b1043d950282280119902ad1e4d8e81851eb02cb8d66c42a001640c8e1e20caa6a1e0102e904668e9ae3cb606088d) else (0x2d0680a5d411e421816c137009b70cc306874126434bb1e161959461d23ce111100f8505b161547167f072a8385e140b1a9a0f2280b0431e608039757489063c3c000b9833c489a18160038898647b5c3d7612768e384d974348a3ce602014100600c30816031f42024161c18e50f6a0db343d710a2602118888254280ed28c5bc6a7e7916124c0f)) else (if b<3 then (0x40859021c0c0aa49f11c7080194f089b0f304081a10ad0c130961c290a212406e78e64c199604a41a298c160c8882c0320e40b52071ae449e1430810cc4b1e290d0aaf8b2246900199e025c070809132241a18c8802b05a960e0d06a2840d0583239f71cdb045800a4638252f020d898284e0e1116749e340d0b00d200c8e00434921020fc0e7a80) else (if b<4 then (0x1fc50a85e1e14f389460b9dc006016be873c0384011b51abf053e4717a11b118ba0d1b473e0296710db9a50801cc30a206998505023921dc512b68659cf2c275520e7b0b2b8042c21f502c00150c9af81ce0126e81358811c0c790a07065b878d214450cf9843a8182e320914f78e1f000380188022c905d42294214414930273412ba395616a912) else (0x34431982088126d06770931808571212820745ac62d540a518c2686ba61c900635860601c1434db16671f32063f83d223c248111c883e15661ca48937c087070020079891743c3434e70c548c1c069e2085908e8053100ab021010701851686086220b02e20b70c635e483802f28570879a800e736d2094107b8230960aed15758c358158500650f)))) else (if b<8 then (if b<6 then (0x88c39ca5c370308067ec237e215716590a154322a31df02ec8a5a0392a0a08106c850907b44258418940b6987b1a00f80c3d866e4f33e3d8a050b887d843b629bd02b48e42829ac18d0064b868181b40209f10158d68c188c1d3530890924820621de108d3812300c1809eb3acb060885a1820d51c54071cc63b0192a080e946ec08ca21fe0cf601) else (if b<7 then (0x23cc83c01d10c698a0d43bd439dc087a0d314787a181b0ce8925dc51bc25ed128e892dc13c4296c084a0d208105c1dbe14d4843dc58bc35f414f18d7547354056b1c598f190541c0d3d168f8309ca3020207089703334527429290887831f4b41e19730ab90408c8c0439f80e9f8042458ee1c06109b804209b301cd21c168508883b438d33a0984) else (0x144589865bc00a18c88800be01f90ad087454ca0a24e8124e891f8089019dd0afd077187b722d2f3a87013b02886601012f88144050de1d4610008f7a4031c086608ce0a4ac513800902a8582294011065b5350989388017c68ab1aeb046c811361078243908138602a1c071200034e41c302a0518b5054c001b804ff1e4d906b420b8703a0ae585))) else (if b<9 then (0x56829ee68eb2e630219c20101dd70c9290290a2f611171082943eca0f41c3f14638e30828f02c33201086344ba9804fd0a88842fc09603c5012b08a370c90c06150ae38857852a220a70e508c0d8140028af00bc89478117220750c109d01074242ce318318f88463dc11b4088c8c3c8443e14ef00148d49c71083d2f0aa89f450290e203b1e5e07) else (if b<10 then (0x648020021c006d40b590d2b60c91143a0d86c622618cd30a70a4b4310c4c6a0c151c4f0031c49f21c36020c050fe6dfd00f812514fa440c753011848946b0621070c1a1541863bc0d7010ae0006cf89e15211ef003534196a289332d78d40c11d61c3e081c866745a7034bc34498e1047bd00d773281127fc49ca004200048762413562d5508928b) else (0x6cc7b5849591a500915872580c02268d0f360027c0cc016468a0a83b9c1db002cc9b))))) 17 i

def r5D1 (i : Nat) := field (fun b => if b<1 then (0x118536230a204614087f7000fb8b61f706c3ee0607dc0b0fb0e41f61843e1f987c32a0dee441bdc0437b8006c6890d8d021b0d843617906c29b0d85161b0a2007b9280f72201ee0203726c06e4600dc8b01b2e403568406ac180d580019f10033e0c067c000ca89019510032a1c0654000c8f20190e603218c0636d80c6c2018d56031aa80634400c687018d02031984061c400c387018700030ba40617200c2c8018584030a980614d80c28b018512030a200614180c281) else (if b<2 then (0xe30ff7c61fc38c3f1f187e2e30fc3c61def8c3b8718765e30ec7c61d8b8c3b0f182fbe304e1c609bb8c135718267e304cdc609978c131f18262e304c3c607bb8843df10861e20ef7c41d8788132f10261df22f7be45877c130eef906ddf205bb1d8773c816e047bdc08c287dc0107b9920f70e41ee008373090655120ca614186ce830a6c4fb8009d52113aa402717844e25609c4a0138754270ca847b9108f700119510232a1c4654088c5721189e4230e804616588c2a2) else (0x38e6f2f1cd6ae39ac9c733938e2b771c56ae38acfc715978e2b1f1c425e371cfc6e38f8cbfdf1977be32ecfc65d878c47df188eee311c9c6238f8c4717188e1e310f7c621c38c437718867e310c9c6218f8c431718861))) 23 i
def r5V (i : Nat) := field (fun b => if b<4 then (if b<2 then (if b<1 then (0x95e7a0000cdb937013e5c9b80df6544a014c33210c6cb90001c70a67c104a310e09d5340e0216b8370213156340750b33e00d31a050b722adc82094327c10ce187205db1c2103a4385c81b5026e40cf01400109c141f0bb18d0d801f0143421180a1a17841987039202dc81b9432540df654360131726e03ddb90200ea016ac0f76540806fb1a25038e00dc81fe1c2341142195607d170ab04528c03c0ea166540da8cb0e076b4a2101dc008f801184cb43066c47602ab1a05082c014785e11967c0299b83216d4099f03a4065581b9858bc26a1b80006e5189f038604d580b200cb430ce185607970c2b038602c380ea4727c09aa240c18a17087044eb94301bed28b412f9011a0) else (0x1cb726e00ac0b0c85ee770e01009b8021180dc250365ab18820eca8941142e11a06b42f2109922a82048d3701c0b382c041994808d0079851084a3058b82e38031a0748289f01460b0205c70a63404d0137208b37206030a0990842cdc9b81046ac06040d101f0a8f0500041600a5c27261cdc08d870b904128f4100fe00c5c304a313e08a1071703929e4f81b98582c2dca212a071c29b900a611908444c68142cc9b8021748708d036a06cf81af432341230793e06b40b090b6a00c681c70061c115afd1207253cb9035e04d580118bc8424d0cb3e084c55b90462ee1c817b1c1b81098331a07840d9f041286438010ca88c33641c4606d465ab03728c5c8084dc9b802982e1e1)) else (if b<3 then (0x27400ac0a653a37004a5c9b80da8cb1a070c69b900b2051185bec68c40e180b5606d401950181b93701b9472ac0fa2e12a07e33e060069b937022846234029864dc16e570b9037db11681c3156ac0dc8133e070c559500720b0c85c30167c1066544a084c598704c64141005317c842ec6543606f7283f01e9850b849a026340d96ac7e0964808d00a6118b85ad0bcb420b016421430dc2501ba0637025144a0810f01400107c051f0989030005bec38ac06d8e0dc03a859ab002c05828410c885c304a311a0784558704262eca8059028642fa6604203e32a050c46bb4101c94f2541230197206fb3e2501dc009c823f4a27c1342140c0624dc010885b93702744a00c0298b93e1) else (0x14cdc030b658d1281b50067c0b042c04178455b9045b870600b43706c01e6142e12e416190c1d9f12824946a300750c30e06fb623b037d870f81cfc30540e48031a026809ab03659b1680290507c2226e4dc078419b903728e4a81c71a61c0c885e4217c31a080450864a80ea4721c0e38032a0064051f094619020490c39b808f6e4dc0614130f0b8e14c3801607c842d78cb5606e40d9f04262acf82095c2e40d96c45a076b2a1b04262cc68204d88b411b01956075d0c95036a00dc81c31a67c1098b35600cb726e029e050585e1156ac0d967c6206980a00080f6e0b86034127c0356e4dc06bc09b900a62f968478dc9b80e380356006405070b7db91f820ec387c0148282a1))) else (if b<6 then (if b<5 then (0x7b8dc8c03728e5c8242028002e18ab720825189502763837015b3700c2e48530e08a5dc2b01d400dc81e1166e40e38033e077570950365951281b95c2ac0442e4dc026865ab04098d1282295ca500b69b80216e40d8d039214d580018bc842dc82b560757181b0433860a81bccf8c41076344a08333e2500c06e0381b9036540518004216d40dab02e4050005e119e180f08b33e0754dc0109a4b93701bedf8ec07061cdc070c0f8c035a099685511682c2c88262e16f7282503862ac381bec686c06e9b80c09193e0003720ac6805f3705c1098ab56040d10150b5e864f8111370940e38d32a08133e2504128c5581b95d2e40046340a10331a0509d400c681b5026ac1098cb720) else (0x61f170c260ccf8096c39b80df69442070c05b901dc008a8219c307c0dc82b3e055e101f0cc6404680b21620c2086445a17970c1f046c0c5581b2cf89401c82c46128c74230b018d0301bdca06c0770e97206e45595038e14ca807cdc9b807d6340a1784559503cb860a81c3016540750030e088ddc2b01e9851085c3176e40da8030e029c16020b722acf81e1166540da8ab0e02b1dc020b6a32cf8008cf814200db81e18c5dc1f037dab188053119b8278c1400182518b9049e8d4601dad28b40af40c00165616230b7d8d1f80560588c2e18ab3e0825068c00231796858e0280029aa240811b3726e035e04c681b5196540dee5062041d101f0b72b84a8019014543142310e0)) else (if b<7 then (0x1d3726e03659f1f8007b70843230192a07bb3e040146000b85c71a6341066c45a03a801ab036a2adc80b90588c2e90512a06e40d870365951f821319e1810983372011b1a050c1db11681b5006ac0dc8bb7206fb0e1503728c4a8213166540a885c1618ad050e04262ac381becf8c41066344a06fb2a31038e04dc81b9056540298b956173f0c3900030f9084533708c2fa2e13e009c140d0a54b93701af196340dc82b7206cb623b0365b91f81ee1861c1098330e071c29ab03d4050005ad02c84305e504a05fb2a0e006d8d0285b2ca8c40d09b802170c59950361861c81bec38e40046540a101e2e6e0b8604dc81b2df8ec0dcae13e02fb726e036a2ac6822b49a2411c9b8021) else (if b<8 then (0x6d45595039214ca80cf088103098ab2a06d45995039f8615816b828003026c47605fb1c2d038e2cca81c3016340dc8132a029c162e08219f1186034121c0e48531a08132a250450824a805305c5c28d6e4dc06e5749501f1ab0285a9770540d966c42008c05150964ba0285270c81030aa517208ad2282002c015085b2cf86c0dc8131a03e31a050c260cd581b9462ac10aa090e06cb1a31036a32dc81c315634097ae0dc0724299f0392a05c80ea006540e18bf0c0509726e037206d5820acf8940a50061216fb3e3f0079b9370256810e40dcc2c4616fb2a3f039214dc81b9156ac0e4a795606fb4a3b03722cca81af0267c000c3cdc16cb363b03722ac681c71a6e40da8b70c0) else (0xf17908401b70843098332a06141f210b7204dc81af1961c00b03e2e16e4019f04529341001184c5c2da8ab5608a10c9f013404cf81b9036e40e4a111a0473726e039f860f8206c30e41076c4760006426e08a60b90841602c3c2d96342603f81f050b5a098b85f8c38500dca393e0203726e037dab1f8007909b82da8ab3e09cc82820245030005b2c68fc0d7a195606141f170b7204d580b204c1428b6e4dc0))))) 33 i
def r5 (i : Nat) :=
  let x := r5V i
  (x &&& 127) ||| (((x >>> 7) &&& 262143) <<< 7) ||| ((r5D1 ((x >>> 25) &&& 255)) <<< 25)

def hit5 (t : Nat) (v : List Sig) := OrbitLookup2153.orbitHit 2 551 656 256 o5 f5 r5 rot 5 t v

def ok5 (i : Nat) :=
  let t := r5 i &&& 7
  let v := replay basis 5 (r5 i >>> 3)
  decide v.Nodup && !jump marks 5 (fun _ _ => true) 2 t v

def o2H (i : Nat) := field (fun b => 0x559a754667c4c19131ae1dc137c4ef9c1b5564ebfd6d2b5510945111f438a664b413922438c5e8990d610c10800) 11 i
def o2L (i : Nat) := field (fun b => if b<4 then (if b<2 then (if b<1 then (0x73e0d845ed629294254b5b1ef739ca529294ad4b29d0a4a52b5ad8d529ab10884294e95a9295296b) else (0x310a739d2b4a14b5b5cb8c22f7358a5214b5298b310c520c864a12b6316b39ce6320a73a50852d4b)) else (if b<3 then (0x7c1ef8c610842117bdab6b9cb6b9f08c6516358b741ac7420e7be117b58b7ba104a98d631473a94b) else (0x6b5ce6c1cf7398e731abad6f5b5ab6ada529458b8ca9294e947c22f6b58b741ef94a75ac20f735cb))) else (if b<6 then (if b<5 then (0x6b5cf83dcc5298d6a54b4296b4210952d2a5294b29d0842506319284254b3a1484a92a521495ad6b) else (0x8c1aa53109531ae6b58b298e428ca4290e74254bceb18b52949c631731cb7b5cf84a738b96d6c1ab)) else (if b<7 then (0xbded6bd6729ce327b9ab00c8108861214c52992b8c1f08ce5394e528c5cb52d484a0c9625095318b) else (if b<8 then (0x4229d264256b5294b10864218c7290a74294b194c842d8d72d6d7b1abbd2f5ad694b56b5945ab) else (0xb))))) 5 i
def o2 (i : Nat) := o2H (i >>> 4) + (((i &&& 15) * 1369) >>> 9) + o2L i - 11

def f2 (i : Nat) := field (fun b => if b<11 then (if b<5 then (if b<2 then (if b<1 then (0xa3cf4a819ca08248e39851925c3c2136805f0187425da0cc49649029863c5705311d3e0b316348517081b61cc9700cb11823886f45204043b3f4785958c2786d1f0871850e4a3ae155c2251190ec25ac1e8a14e9805b86c8e30ee0650003905a280ac024eb0f1a01552062810e0860d4b33048f33e241d9085b9069352a8f919a8c0f669273a069d) else (0x1bc6056160402ca962d4488e5ed233589b5d448b82a062a4a1e2382cca761f260605af85b5872e1114c01640085c582820c3102c01c060d580c641d154ed3255e706b08faf443ac7a8700ca13628ba623cb40c1e930846bec319c00c8806bc609c36a226a686348088432db104a881487d24219d06a31673ceaae5ced20218f330a06876720cc50e)) else (if b<3 then (0x17801bc40853f6380150189a7a7d29358c224921e14be1a2b029b0532e586d129d88a703c347d6620a30b200243210f62063882742d0c467a12d3845949bd8241b00001795493be51db14ec952d8f0c86d4c2d040463c801256d502d10a250787c4e772f31027c05af44c6d2d11178387cb0257f129e0c27015b4629d173b1a35cf96631c00ed19e) else (if b<4 then (0x29852180854340e8595cfbe41d6d20a89f2d85c302c660e26896749a4e08bd2c55866d844f444da1112087cc60062545303a03064b4e250e5046d8b08cdd92664f13209cb4c551a1e2a26b21a4d0fdc465db22e20c1b02da65a7e2f198981813c439d900b61d5782c94244320d300394c15e09bc3a710d344ec34257434b4820106cea465c2c3e02) else (0x3387dc4189f3d3f04798301e796c14531e1d0a0b874530f4f9997c5c5e05ce307c00658825645443e640f0dcfc74151e108403a809d183a6e37090654c912609fa2a5c81128310601b22a70049f40924541302c6915a4d5285e4e30a59e3e40908149330e8965e4f2c0744623658c9047c70492c048f1538cdcae0d8400851c3241dae49d53e7382)))) else (if b<8 then (if b<6 then (0x6ec0a000679253884a84e3341e5920cb0aa24f9f828f4382003b746cf814e028111501cad904e55007f18210ddae3eb70ef288a0c7a16610b0ab68d24018f44c6b1e8216ab0eb60268229328f6e8eb524943129d044e492242862121611aa041a0765b108486b50bd28051a12318c88499ba421836e59c6a8e2aa548d3d6e1ab483be649820e8691) else (if b<7 then (0x83c8c183270371c8f6f86b5a2c1c056009b74b8fe2455175f93750e10210793561918a4bbd639060d3b88730d284001815538fa1453f2057d1ab41b580690c75ab2acf9b668b26464fd1a1509afc1af06153076c92b28354609c212b58e3bccc6e726e10f78045c00f0186a0224025c84178584c2f5813558ab86580d055a855c4ea9820172c031b) else (0x1c8453615f72cf2020cca40e5c272aff87694d90e0c832e2b9e924fc8830ad06b18a48c94b205d4109b9d0580da22c212a880283c7b5c38ca35400c068301412dc1508023781d9442b81126107a478ee36b313061c56c92f62556074d92898d3e479052043001ec38521674032319598090e4024276a08ac07b72209a14e51c020f43e15550d5205))) else (if b<9 then (0xb44cc4e59fa149119418e17440683e099db78c4da505831571d9a4b4d019722a8616798b2dc4152380a908dc620e00423f19033fcc9ba288214c297438696269a51c489f1a4597641d836740d2a000045126309085914836c5132152004b58dd0670ca1005879fcbcd04dfc14dc175bc2940488801640333cb9982e393312907c40a52662d089c86) else (if b<10 then (0x3d4c510123222df962dcd1cc78a41305006dc5a92564d2c2218044349a1a2c1b5c11684c270709908ac8eaec45524e9a3ac70d48061e074ea1d6f0b900913e0ecc222d1b9a44bdc25e92686898341c0a35c92caa1f548792e188b3a149c6709154146b3f551d5041a2c32a604da0d644d31e30020ea5803a40172765e262594158ad221243070d85) else (0x5409270091c16c4186108934527b367f082089c2a549e1d321829c50027e3b1ae99b39082ba305f1d559678c847c69d220e39f32c7c602d761a8b1a10480b66c322933999784980241408951f204cd1c7e8d30fc9b61452543df135609c0cc34b065fe02f0046f4e3485acc0849018ecd3bc15582a3b005ecfaa8088c243f021c8e59e46ad2c101f))))) else (if b<16 then (if b<13 then (if b<12 then (0xb18228659401e251a65c2522649030930c0f804ec165615150eb684ca00573249b174d435a016990aea80654388a0acf047f8c2583404083d073910844c3ea20f7305b8718cc4c2197038979c1c0da9e464906c1815a8a3266684332e9e528886436e0181d148941b2812bc12e09f19cc878003833119f66c988c19832ea48244c21606a81272913) else (0x588497610803747035cc321044f206181bad82b54242f2100885d05b8864313d3e1a84c0bb8719212688224468001e531f148f85003c8419e06ad118780462357a0f40149e40d18627301038b7c09200542807420d63891e61ea000c98859472141e8604968a67c1526023f1cfb8468c7142263e16631457c91642eb32f4b0a4043d841d61326691)) else (if b<14 then (0x8e89c1a7d4a04208b970497e292c3e68091e08a1e5c2b28fe80604228a1ea82ccc0649471b030662f5880a1cf36605253e18807d8eb00790928551126cc018518818f68e01c15966a6412c0912b8095650973f04813c06142481d2527965ac99a828592a9d9e4c0420a218b286b091a4cb122cfb1d4a8d9202bc479150d24165bcead029af36c111) else (if b<15 then (0x60c0fc7ac419591f92c93a22178150589590755e11fd28249709848441a380cc6137606b5838f508451c0e4655e4934044b1623c08f411d21028834fc11f65c600d52816c86afe5ca914ac92464c944349c32a116364794a26270af50c6ecfbdc55df12ba9732ce8202a8902a78228c011c5827093a8575cf39a01cb1acd8f1f43d923690355105) else (0x3f4a0bc6d1b015c9598cfa9011031c448c1948cde621732b1180d831c2046406f39a0d8a34c5d63366a819509aba745014f51d3e871ae001207628a88c4ab839e31cb39e910b8b036360e7e1198c5c5615e130941b0dc0db07cc205399f740694a74751e3619464791a184b0c0487740daae3e9c3d3a120e00b6a289d3807869a82cf05551083985)))) else (if b<19 then (if b<17 then (0xaa85502327b18a0901e4220e7ab723380c97cfb3c74f13c3117a087cc015be3e76196905a5c6ece08dc9f59c1222317e229183468b950524b0afa1e700ca906147250710370919e30b82157007b0c2ee1c5b1b6c831dc88de4e9629101500c8438413706989ca6814a249440e3996b7c5d4e5a781317033dc10a2728b31230a7fcd8ce1c5a009090) else (if b<18 then (0x37c081012200a56022f43d6821f838958b3a0d8fe4d3d2d28130643d7402432f1416534938449290145854ccb4cc6cd6374f869bc2b562c200500096fc1ae0156a0a229493813de693a30b8884f8703461bc1c00848f469ce68d33c0b189303cb47616370b0523cd27e751d1a51994a071c2441b250a1231cc85a6ed819508272449da0c7c222200) else (0x8d4aabc5522072d0e310082e3a9710ad0e164605e32a53a3b1b73c438c2e92266c9b14cd84c681e03088f794d2b6045d315310998584a74061109103c4756c50e93d560f7a00a0800982a16827e070c2225d0ce70e5dca8a0702a31359c914530e212d38fd896e82a4041023eee03348a86a101c36bf0e7348b8a21dd3ea71437cc1b0604f1ad48f))) else (if b<20 then (0x1b888284a3516cc807841b622cdc183e964f439142c3f196084a78344219302e871f0388d84758c0a8c1e31422661c8b1c128387014326da002fa927307b6a5a671a170107c232070cd1052131a89d2e45b732a7043bc519c643f29590a85c1bda758d08260e70c43000cbc1c388a94cf45a59b130d0805f4d9301c603e9b0f1d4c0603c2c0f480c) else (if b<21 then (0x778989c4e51031e177207a7c5ead1669807d058e2784f2d29048983a806a9324ed1f6e041b661dd1cbc84618400a22b52f110c57c11e4682301451c3ac5868123406bb1fb34f4c07924395c827a0a8dc12c31d309146020ca300e090a8d6a079e83e1e2d4416354e9d82ce228a38826c30e0182410091f91c9aa01903375a1c780db4069992e460a) else (0x11e0a17ce4fe0d2e144a9d8744b8e10ba02978daac63246cc10c4c99148c02a0695302e87908bbd640f60a630e9289b604d7c2b6681)))))) 17 i

def r2D0 (i : Nat) := field (fun b => if b<1 then (0x59b9665598966143ed0ee439507b41b906541844fb13c44ef13b84ec13ac4ea13884e111ec47111bc46e11b046b11a846511884610fec3ef0fb83ec0f8437b0dbc36e0db03630d840fb03c40f003bc0ee03b00eb03a80e4038c07b01c407001bc06e01b006b01a80670194064018c061) else (if b<2 then (0xdfef7f1dfbf7eedfb37ebdfab7e2df877e0df737dbdf377cbdf2b7c8df1f7c1df0377cddef771ddc376fddbb76cddaf76add93763dd87760dd7375bdd3774cdd2f74add27748dd1f742dd0774063ed8f063b98e363898e161ed87061b986361898615bed6ef5bb96e55b896e159ed66f) else (0xe3bf8e6e3978e2e3878dbe32f8c4e30f8c1e3037fc))) 14 i
def r2V (i : Nat) := field (fun b => if b<6 then (if b<3 then (if b<1 then (0x26724c649bc935925f24ba496c92c924624884a7c94d928f25164a5c9499287250a4a0c9409237246648fc91d922f245a48ac9149227244a489891218bf1176225c449887f10f6227c44e889b1132221c44288831102229c451888f111622bc455885f10b620dc419881f103620fc41d88271046211c4218) else (if b<2 then (0x4c206c40d0807100c212e424c85390a3211e422c8439086210a42108419081204e408c8039006200a401080b9016202a4050809933f26764c1c97792ed25d64ba497b92f325fe4bf497d932f26564c5c98a931326224c7c98d932726464c8496792cd25964b2496b92d525a64b7c96d92af255649dc9399) else (0x1f123e047fc8fd91f9241e482c8ef91db23b2465c8c99186230846bc8d591a7234a468c8d091bf237645dc8ba917422fe45f48bd915f22b643fc87d90f9223e441c8819127224a448c89091372266451c8a1912f225644a486b90d321a2439c87190bf217641fc83d906720c6417c82f105d20b8416c8271))) else (if b<4 then (0x4b52966531ca61949729265244a439485290c523ca46948b294e5294a51945728aa514ca28945f28ba519ca31942f285650a4a239443288250dca1a9433289e512ca2493ff27f6501ca0193f727ea4fcc9f893d727a64fbc9f593c7278a4f189e213cf279a4f2c9f393e527c6479c8f191f723ea47cc8f91) else (if b<5 then (0x67b2cf258dcb1996172c2a584cb08962f2c5a58acb1496c90d9015fcabd95df2bb6561cac195972b2656bcad595472a86557caad95b72b66571cae195672ac64e9c9d193a1272e4e4c9c8935726ac4d509bb937626ea4dd09b9936726ca4d8ca8b95132a22549ca9194ef29d653a4a8395032a0253dca5b9) else (0x7772eea5dccbb8978f2f165e1cbc297832f02602440406ff2df65cfcb9d97072e065c3cb85971f2e365b5cb6996df2db65c9cb91972f2e565b9cb71964f2c9a592cb2496af2d56597cb2d966f2cd6595cb2a96532ca259dcb3a96732ce2583cb06960b2c12589cb1296232c425a1cb4196972d2659fcb3e9)))) else (if b<9 then (if b<7 then (0x87d30f661e4c4f989d31366264c43988531066204c5398a3311e622cc5798ab30be616cc1b9833303e606cc1f983b304e608cc23984330d21e7cbce979b2f325fbcbf597af2f565e9cbd297a32f425edcbd997c72f8a5f0cbe0976f2eda5dacbb4977f2efa5decbbc97d72fa65f3cbe697cb2f925f7cbed9) else (if b<8 then (0x17542e885f50e491c821f28495090a12941a285a48b4105e40ba8171027204c406c80d1007200c410c82150422081400c80150022016402a805106490c825da8ba517ea31546228c85166a2c945aa8d249a4125d44b289191222285450288b5114a225444c889115c92b8317e62ecc4b989531266244c3f9) else (0x5f42bd257a0afb95f62bd657a8af795ee27428e451dc93b826ac8d511bb237546e88d951c493882a2293a5280a5392a7052d5248a485490c9235252a4d929b05155228a45d4852910521aa44948f251e09faa3f1478a8f191e223cd47ca9064a0c11f543e487c50f821f943b2886490c1186430886950d0a))) else (if b<10 then (0x7034e1e9c2d38fa71b4dae9b4d36fa6db4e4e9c8d397a72b4dce9b8d3a497572eac5d2cba5164d4c929955328a6754ce29835304a6254c4299f533ca6154c2298b5314a6c72d925b20b5e96bc2d825b00abfa57b4bbe976d2c3a5834b2e964d2d7a5ab4a8e950d2afa55b4b6e96cd2e3a5c34ace958d2fa9) else (if b<11 then (0x41843e0c8610c23174639085a102e304c6068c03184230046028c3211a422446448cae144aa89150faa1e544ea899510aa20542fa85b506ea0cd40fa81b507ea0ed413a823508ea10d434979d4f329e953d0a7c54f829db53b4a77d4ef29f353e4a7754ee29e153c0a80930105ff4b7fa6fb4e7e9ced383a) else (0xeacdd29afa35e86becd7a9af7386950109d253aba7564e969d2936426bc4d8097d52fa25e94bd097dd2fb25eb4bd497bd2f723b846a8cdd19c4253849b091e11e23))))) 15 i
def r2 (i : Nat) :=
  let x := r2V i
  (x &&& 127) ||| ((r2D0 ((x >>> 7) &&& 255)) <<< 7)

def hit2 (t : Nat) (v : List Sig) := OrbitLookup2153.orbitHit 2 739 1369 512 o2 f2 r2 rot 2 t v

def hintIndex (i : Nat) := field (fun b => if b<6 then (if b<3 then (if b<1 then (0x282ca8c28005891c010a2282ca8c280458b282ca8c2800584243c7006c24081020408102040810205d068421d866c1c0810205c068415c86) else (if b<2 then (0x3c00f004c51d3c546151e0408a184c5111e340151e0000a8d1c0000000480160000c8d1e3018f1e30b8c323800000200002c00c4288000) else (0xa80298ba94ea0000200001c00a0b280450b58b488d005000a7f00000120000c7e060407e29fc07e32000001800a3a780002a30a8f000050f))) else (if b<4 then (0x9e2db9a02040810204bd5165e40b02040810205b0c0204081020408102040810204a8c30d46090204081020408131046189030000a606a00) else (if b<5 then (0x206c2f2b0c60c2b2460c020462a02065a4a0a008118c06320204081acb99b468000062440016200408c2c006010205b1902040810204097) else (0x295c58b8a80a4a162c18216ac1839895e9b060c5b1168c183060e21f1830a8902066a6a4a4abc1830081020460c2a1060c2a180810204081)))) else (if b<9 then (if b<7 then (0x204081020408102040ba0d0843b0cd838102040b80d082b90c0458b28241839c9ca51162df1c0604183162ca04162ca08060c183060c183) else (if b<8 then (0x1a000040c240c080180001e0000f003c00f003c081183c6801e000041000480031e38008000000024700022c0041e380060cd84810204081) else (0xb2040810376d5eb6d030000400100204008120408102067810206ac8060c081020408102040b5120408183200810202a00a8200001c0008b))) else (if b<10 then (0x4af4d83062d88b460c1830710f83060b1e21825e0c02046041818081863248cbe040e0bb86f0c54040cb4941401023180c6404081035975c) else (if b<11 then (0x2000000018000000000100004000000301020408102040b60e0408102e03420ae4301162688b020c5841620183ae2e50b060b20b560c1cc) else (0xb1590206d5b0208183058f101bb7ae590204081bb6af5b0000089020c081))))) 7 i
def hintVal (i : Nat) := field (fun b => if b<1 then (0x40c0120a02129c501084e280842414041d31a020c94901064868082a424041120a020690501024828080a4140401208ce1090437084e21b842410d8252086c1090436014821b0024105c213882e1090416094820b0424104c25388261290413084e2098424101c213880c0290406004820184a7100c21388060290403004820084a71004213880208904010348200214160010a0380065060003282c0019407000ca0280063058003180a0010c18000860b0004301c002180a00104160008203800410140010830000841600042040002101c001080c000840500000188000002800000020000000) else (0x10184a7180c2138c060e9c600094e30004a598002524c00109c600084b300042498001d38c000e96600074929b04a414d82138a6c1090536024829b00a414d80120a2c1290516084e28b042414580920a26129c51309482898427144c2120a0c109c5060848283012414180520a0c0090503094e2818427140c2120a060690503024828180a41)) 29 i
def hint (i : Nat) := hintVal (hintIndex i)

def ok2 (i : Nat) :=
  let t := r2 i &&& 7
  let v := replay basis 2 (r2 i >>> 3)
  decide v.Nodup && (MinorHubAdapter2153.short 1 2 (r2 i >>> 3) (hint i) || !jump marks 7 (fun t w => !(hit5 t w)) 3 t v)

end Num80

open Search2153 Cache2153

namespace Num80

def Transport := ∀ g < 2, ∀ depth code k t,
  Marked2153.Impossible marks k t (replay basis depth code) →
    Marked2153.Impossible marks k t (replay (rot g) depth code)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H5_0 : span ok5 128 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H5_1 : span ok5 128 128 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H5_2 : span ok5 128 256 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H5_3 : span ok5 128 384 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H5_4 : span ok5 39 512 := by decide +kernel

theorem all5 : span ok5 551 0 := (spanJoin ok5 256 0 295 (spanJoin ok5 128 0 128 H5_0 H5_1) (spanJoin ok5 128 256 167 H5_2 (spanJoin ok5 128 384 39 H5_3 H5_4)))

theorem proofs5 (i : Nat) (hi : i < 551) :
    Marked2153.Impossible marks 7 (r5 i &&& 7) (replay basis 5 (r5 i >>> 3)) := by
  have hh := spanAt all5 (Nat.zero_le i) (by simpa using hi)
  obtain ⟨hd,hc⟩ := Bool.and_eq_true_iff.mp hh
  exact jumpSound (bottom := 5) (stop := (fun _ _ => true)) (by intro t w hn h; cases h) 2 _ _
      (of_decide_eq_true hd) (by simpa only [Bool.not_eq_true'] using hc)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_0 : span ok2 54 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_1 : span ok2 11 54 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_2 : span ok2 24 65 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_3 : span ok2 13 89 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_4 : span ok2 21 102 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_5 : span ok2 2 123 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_6 : span ok2 2 125 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_7 : span ok2 3 127 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_8 : span ok2 6 130 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_9 : span ok2 16 136 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_10 : span ok2 26 152 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_11 : span ok2 10 178 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_12 : span ok2 21 188 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_13 : span ok2 71 209 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_14 : span ok2 107 280 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_15 : span ok2 81 387 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_16 : span ok2 16 468 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_17 : span ok2 14 484 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_18 : span ok2 18 498 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_19 : span ok2 45 516 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_20 : span ok2 68 561 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_21 : span ok2 61 629 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_22 : span ok2 9 690 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_23 : span ok2 34 699 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_24 : span ok2 6 733 := by decide +kernel

theorem all2 : span ok2 739 0 := (spanJoin ok2 188 0 551 (spanJoin ok2 125 0 63 (spanJoin ok2 89 0 36 (spanJoin ok2 54 0 35 H2_0 (spanJoin ok2 11 54 24 H2_1 H2_2)) (spanJoin ok2 13 89 23 H2_3 (spanJoin ok2 21 102 2 H2_4 H2_5))) (spanJoin ok2 11 125 52 (spanJoin ok2 2 125 9 H2_6 (spanJoin ok2 3 127 6 H2_7 H2_8)) (spanJoin ok2 16 136 36 H2_9 (spanJoin ok2 26 152 10 H2_10 H2_11)))) (spanJoin ok2 310 188 241 (spanJoin ok2 199 188 111 (spanJoin ok2 21 188 178 H2_12 (spanJoin ok2 71 209 107 H2_13 H2_14)) (spanJoin ok2 81 387 30 H2_15 (spanJoin ok2 16 468 14 H2_16 H2_17))) (spanJoin ok2 131 498 110 (spanJoin ok2 18 498 113 H2_18 (spanJoin ok2 45 516 68 H2_19 H2_20)) (spanJoin ok2 70 629 40 (spanJoin ok2 61 629 9 H2_21 H2_22) (spanJoin ok2 34 699 6 H2_23 H2_24)))))

theorem proofs2 (prior : MinorHubAdapter2153.Prior 1) (T : Transport) (i : Nat) (hi : i < 739) :
    Marked2153.Impossible marks 10 (r2 i &&& 7) (replay basis 2 (r2 i >>> 3)) := by
  have hh := spanAt all2 (Nat.zero_le i) (by simpa using hi)
  obtain ⟨hd,hc⟩ := Bool.and_eq_true_iff.mp hh
  rcases Bool.or_eq_true_iff.mp hc with easy | hard
  · exact MinorHubAdapter2153.sound 1 2 (r2 i >>> 3) (hint i) (r2 i &&& 7) prior (of_decide_eq_true hd) easy
  · exact jumpSound (bottom := 7) (stop := (fun t w => !(hit5 t w))) (by intro t w hn h; exact OrbitLookup2153.hitSound (proofs := proofs5) (transport := fun g hg c q v => T g hg 5 c _ q v) (by simpa only [hit5,Bool.not_eq_false'] using h)) 3 _ _
        (of_decide_eq_true hd) (by simpa only [Bool.not_eq_true'] using hard)
end Num80

open Search2153 Cache2153 RootGlue2153

namespace Num80

def startOk (c t : Nat) :=
  let v := basis c
  !(decide (t ≤ 12+1-v.length) && unionSep (decide (0<t)) v == top) ||
    !jump marks 10 (fun q w => !(hit2 q w)) 2 t v

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem root0 : span (startOk 0) 13 0 = true := by decide +kernel

theorem solveCodeWith (prior : MinorHubAdapter2153.Prior 1) (T : Transport) (c : Nat) (ne : 0 < (basis c).length) (nd : (basis c).Nodup) (checked : span (startOk c) 13 0 = true) :
    AtBase marks 12 (basis c) := by
  intro t ht hv
  have hh := spanAt checked (Nat.zero_le t) (by omega)
  have h : jump marks 10 (fun q w => !(hit2 q w)) 2 t (basis c) = false := by simpa only [startOk,decide_eq_true ht,hv,beq_self_eq_true,Bool.true_and,Bool.not_true,Bool.false_or,Bool.not_eq_true'] using hh
  apply jumpSound (bottom := 10) (stop := fun q w => !(hit2 q w)) (by intro q w hn he; exact OrbitLookup2153.hitSound (proofs := proofs2 prior T) (transport := fun g hg c q h => T g hg 2 c _ q h) (by simpa only [hit2,Bool.not_eq_false'] using he)) 2 t (basis c) nd h

abbrev solveCode (prior : Projection2153.ThetaNumeric) := solveCodeWith prior (OrbitCache2153.sound 1)

end Num80

open Search2153 Cache2153
namespace Num81

def basis := Cache2153.base raw
def marks : List Sig := [raw0,raw3,raw5,raw6]

def rot := OrbitCache2153.rotBase 2

def o5H (i : Nat) := field (fun b => if b<1 then (0x87584a81c8067de7bb79c77c75e74071d7066e06c56a167b6556366145ee5cb5aa57f5605395154f54ca4aa48e46b44842c4043e33c13a038035e3403213092e42c32a327f25d23f2191ec1c91a817b1581361130f00d10b6092072054029000) else (0x89e)) 12 i
def o5L (i : Nat) := field (fun b => if b<8 then (if b<4 then (if b<2 then (if b<1 then (0x639ef8356a535cf631ac4a54b4a94c5318c731ac9ceb7aca74a5e4d6356c8c1ed5ad8b635ee7316c) else (0x73dee6352a6296c635cc51d28529095b5ee6b18c318e94a9273252a5b18c7be128398c5b5cf5ad8c)) else (if b<3 then (0xaded8ceb35a5a73a4a0c6b98e52d8c6c20f7c5ec6bdad6b18d6ba0f72d8c5a50a5254c739d08ad8c) else (0x8c651839ad635ea5a54cb4a329c5e642d8d5b1cc62dad62d8a3214c6b1cc5296e73969535cf835ac))) else (if b<6 then (if b<5 then (0x4a8e95ad063a96c6ad6c739cf841f18b9ad6398c6356e835cc5adae7c1cc49d2b5ad8b52d8d739ec) else (0x49d094254c639ec6358c088632990a5b56d6b9cc8c653ad6d7b5ed0735cc6a94c4a96c7318e73dac)) else (if b<7 then (0x6b98e739ce73dae845ac6252b520c73a54b4296c5a92b631ad535cc6a96c4252a4a5494b16d7316c) else (0x2990a41d09535ae7b14c94a328bdce6bdce6b94c5b1cf52d6b531284ad8c739ee6b9eb52dab5318c)))) else (if b<12 then (if b<10 then (if b<9 then (0x5b1ae7b1ae84e31839cc298ea5b16b5b1af635cc73dad7be105b18c739cc73def83dee639f073dec) else (0x9ca4f73dad5b1ae7398c6b98c739ad7bdad72d8c5a98c52d4b5b16c5b58ca4e53945ac7398e6b9ac)) else (if b<11 then (0x6ba118c1f08462f7b5cc639d08ce318c653939ec8c1f29d26f845d07c1cc4a92b52d683a54a631ac) else (0x735f07c1f183e308c1cc4a52a5a5093a56c639ac7358d6b1ae63dee83dec839494254b631ae6b9cc))) else (if b<14 then (if b<13 then (0x7b98d72d4941cc84adac28c2218843298e94ad8c7b16c6a92a5314a5ad8c6b5cf7c253a56b4ab5cc) else (0x4a1294a52a52d6b5a54c3188739484294c63a54c7b16d63a0f5a98a6316c10845298e95b16b6b58c)) else (if b<15 then (0x9d6b7bd24f84deb5296c6b56d7396b5b58a5b54c3a1295296b531ad7420c5294951ce629ce74254c) else (if b<16 then (0x9c6539d295a5e71731acad296adad3a5ad2835ccd6b558460b635cd6b5cc00465088643212b5a54c) else (0xc)))))) 5 i
def o5 (i : Nat) := o5H (i >>> 4) + (((i &&& 15) * 2206) >>> 10) + o5L i - 12

def f5 (i : Nat) := field (fun b => if b<17 then (if b<8 then (if b<4 then (if b<2 then (if b<1 then (0x91c0c5209af08b3ac596e10cfc6727a64aabc0498218a0295bc2f000caf8cc0a268f0e4d36a54fcf46e87368780e01030279c2294792f68097911e769de31046babc70cc27c65551e887b1761533591cd1b550a55334c305f1b1b05573c8aa8b4c250a803d967e8f3222111d13f3e468222ca6839ea0b090451a6f43ada02c6dd035ec1db21a1ab1) else (0x5011f635db9cc94e37000455814ae0a1f31c300c288b59d986e9073f01460bf0cb94242a9841b30c844b6685a569cf1087600ae827460d33c343849f42cec5dc80d5f4d89c43fc3d684a189d5f83a98912e4805811530c89159f1a2f81ba4bdc1ad5504a9c4ce424d41d021108023b30999101ba9940979fa2f5248ed817f25a3968019cf66171e)) else (if b<3 then (0x3738b254466642543892751e1e8912ff4161561b7a1540e9b0737c087bbced835e055dc70b3a044c7cb83dd59eb619e601510185c03e9954a4dd30410575a7069e06e1c7c19d76c017837c1844d07a5cc12c0a48c00f4ca4ec8f96040063ae1128b32c905c880b1b006f1f01d608831e287e2c382e1b82e4d6ef41d31260c039e809493837d712a9) else (0xeb07b32010e42601a144405c837c2ec8c8ea059037c85185fcb9961a96011f0e56857ec7b269c73c835b91a480cd8d49246eb80ca3000040a1c04832fc61457889f61eae088364c3f091a6eab02c8cbd21aa944887489a965d4901dc10e4eafaf980c74c20fa9ef9a5e423b1f0b0b9dc5aaf9cdec774a78b9c2263aee1ac2eb59769fbe2e47aadf8))) else (if b<6 then (if b<5 then (0x9d0711c0dd0827aa90bc884a4c1b777f83a99e88ed600e68c442bb487845b2e8b2964cde1f536266ab6ff359a028c87bdc1d4c743ba76b82a9f610badec992344169200252cb1edca670d06fa57002b42d3e0c6cad1cec0947f8b007e533381a16eaae1f5408629d750c9ec06e1fe3d3ae291eef101123038b801a65e15060c62c111c547c0020d8) else (0x354018ee452c20b0a01d3dce0c3972ba3bc3e05f820d8082f7e1310dd81e2798ba05141788c7c0e1a0fa401466ba3db61219b1d586084276c0b698c39654721895f7a4089106c36202e67dc0f8350a7e88f32e66839d9b53608e4b05208117d640359e227564501a263467902da8902d05fc36479522873d0c8ac2595023b2725cc0c8c852e1a183)) else (if b<7 then (0x116c2d714b0b65613205c874f67272ec0964870e004ed12bbc97cc55f20a653917504f45a327cc20c4a7a02fe35a1999643fa1a104ac038290a0bc1b08e2aec0763044b0b8c5945ab2b1666240e2ac5459f09acb885645295147868c00c5d829140a3d8b600fa826a4e34eeda263fdac2cf755e8014bb221839014c65bd0285573b28c885212a8dd) else (0x6e83b723d8278a30b4da49b23c1f960c960343f2617271b7d089d452ac3d486c4403c126a4e54626628645fc20c6f034165a0e1c3d88cdc99022587018ce420caf04098e390c1a3581e3c01ad6322ad55545024601b723cf5023e16b2ab30f702e9c2c25c88bb882159aca81f19876c07304497563948714e601fc0fd207c8f2b1fbf80465fa2c84)))) else (if b<12 then (if b<10 then (if b<9 then (0x3f411562a73183cbe5b83eb072dfdcaacb06566fa00d7046942c1c240e19d6b87c076f8698ae42ed13e0957e45be31396c34fb6145a52a3791f32eb7a22315a931788ffd2b246f02694d11c0a1114864231291cc8c8383263e684772b94924247e0c9d623287553395c342e955989029c3782af400ffa87284ae20e2d6e86813e7b029d6c3832b8f) else (0xa267954f033208b0f43b39f8e0dd80024acb00ccbfd62804a150bd3c03296916a0863a8783734f3d224d80bc7b11e16f0c83cf06ceb3d92c67fa7839f86ca55124bee81e48fe1d5d0791841c3d506a22ccdb18683acba13aa3479f49c3f210bc1ec6bf1f4e2e42c7e6401399463eccb402d430499609c772c4419e05b163948a624cfb3607969f85)) else (if b<11 then (0x854175616d40c45e505ce8082c41d3c8382584d9a0a7b8ae1064c50220136617890c87c00c2072281980281050d3659496c42c5e041a219cd1298e14919908086053d00fba262f280f5b2e3ce69f63f4a63406ee886ee6092783c6128ac3e756bf15df0ee13e3d968a03819faa57e36198e80918142c0296052ea5c1c07a20ecbc0df62653898cb3) else (0xc4c78f90c569262a60f23c1964b25e295edec2e5126821adc4a635f2a2c114064f6e64d82a904c41820455e7724018df6181b08180a94d4fa1c0f48e347e100dc418c2b9415e4d9f540132a00bac2d4b0de26a596d024f0ab0f750e34a9c3c0cca2d4a0e808d1a9ca083854f9cb0e30e302ecf93335081684513a27b48a493b03a6ba14d8608228f))) else (if b<14 then (if b<13 then (0x68c6ad46e531e70011a840a6867ecc2e450e577151b3c06c8e6ed43059f2de001d1688110a81e2f92f3ab5d3fad7707206f6fd027cacae0f3fc608b0f7d1e7480b74d82e512b0e3241d26e376a7de9c51825596a804cc4ac4829c0ca48e29da804296210236a69a349c0ded8e6e513335144e4871256531cd30bee145da948aec06ed222809f288e) else (0x9ed937018223db7008b8323fb18582b6601b87bd238544af3cc4499cbecd97249546e742f0c30e10e413e1b1ed8e1b3e14780a251b02000661d780d6751aae1124c27b8fd6842d139e850bc432080f5e09e10c474c207bf36005cee2b2923458f08878bdac263ba28b736f7148b6aa25548c32168c99aea8c4c3411ae1e5ee6c9064d8d8fe9911c6)) else (if b<15 then (0xdf8452635db101edb5ab122214ba03114808a24c20474799b8c314ba6e1cd6572e0220c4ec03b418e3ae916561c411f10b7c09ad65d2c0a0c3a93000c43bd60d7d1e2e53da07e657d3382850d288235f141e62e82ba2032bd102d1afd0b754f2eda85285a58bb9869cd2c5f3c2440616a1761db4064aca3785318158810b7ca5a1a0d8b1a1847edf) else (if b<16 then (0x8f86f80eaa0b2c874e889e52853ca2292cf414d811431ccdc70a076ee37311498000907d3216656cb4c4528810456c31ed8823d4f9444ac406f90b3f22bd1bc1b0c05d5c703d1412620807dae607c6e3c4a7a740c9747e151da9c2bcc45604228c476f34e3899a0a3c304a0c101584fd9bd10be1015849d8099e145e1ca4a819912e0146548399e) else (0x4322dcece6001178ddc83c640dbc86d510488602f812f0554874c87261951f9427ac9ecdc131d521c908acfc307c223f602a828e84a234909884a041d554e021d71eb985e04442101304c0aad440e1643454b2c18f00c775c1de316260017054d609d0623a83534112916211310043aa6181a77611a50ea1ababa34a0244f33ab432ea083c15a30b)))))) else (if b<26 then (if b<21 then (if b<19 then (if b<18 then (0xc943e4936140cd74f5d268b8f42ca2706911c2570306b0a3af00ec592e981996a10d005e36044aa5a4cfb1b45958866f9e98742fa0698051a98743d58e6c28760f1489e7c4e7126db231b320247daad8053a1e55090b22ea63a468f063e9ed4a7f94dc361161358c572292c978e8c9405c162cc25a0ce6d3422a21d350e5026211fd7a11c118b462) else (0x2c70ba1be0d3ed50839231604cac0ef67744678fefc75ae2915d66064b32c506063f1ed40743a8118e38c490087942dd91590172af061acff0aa42c1e3bf78176f0fa2c3768781831e414e7495e8285f82b405d2c1c584d4c1274c6d3db07e829065f61e6e9735858e712cf1e9dbbaee7cfd19f506c20e5a0e9170456333f134305a563cbdb63292)) else (if b<20 then (0x4f990e6048937ac8b7de4150ce8502f2833f83a47a4218cd96c1ee409f83000cdaeb03e272a066d0cf507510c878aee5163888065af2001811a4a5cee862b9914cb028b9130d01fa5a80a3d8d09a76bd20bd00208adcc666a073480160e62661ed70aa8e22ec3d591e80c25847cc210c484ed9650c508d20503fb193cf08cefe302ccc19fac66189) else (0x40abda03df1864e3b0840c4335de6bc4823f519ed82001546075e468cc403e355b07a6008222576640cd9ca9fbf23c4abafb3b5981eca170d1c5039958443814f20c386b84818add3671525843f061a000c3742b3fb43037b3c6020ed3ca80529c351c1b6b44ab180ae07078cb40b25500702d27e9c70aa18305435ec282e6a0547b72411326caf1))) else (if b<23 then (if b<22 then (0x23c5c563c8ea81c84895b24aec9c1811859951426346010298ab5e4cfcbe3182d5285aa7ab6e520e4ae2a11ba88735470f11027b259b932b49b1f2bc5056f2c1d90212e4c636bb3a9308d4f8ea70e72404edaa5e4c2a619110c5e79388532c58b88a4f1b850b28a09363c495f303d79f2c4a05a7f020ce0cd62a0d04585c2830c78b1e0cea428ec7) else (0xf4701e35d440b3be0942d922d2f69658e5eb2051223c08dac15d52249d8b28840ea53c3f3c1e4810ff8b73732a89b8703af08c7c32b944d2d600a152fe2875c78d5a7b4ca8032638c282b45f62ab07ac82e04c3b25d3527028ddec4bf60b14eaa02ad7c922bb1832b9394404630624c7a23c0a01e23aa9fb954462971a51272764ae0ed318a932c)) else (if b<24 then (0x30e86fe2d307f4ec64ab6004cb711d4d497005a60691f498864e9c292a2fa2136b808d8430bf3330396b1eec7db001d5fb79e850e2ae43d4968381fd605341311f23794bd6e0400fda49c9d8c84f08f4da2c02d28b3d421815ebb087fc9ed0446d81bba6c442690e63d1a6b9f142a4b841d5756726af095300840033b6eea393559810165890fb83) else (if b<25 then (0x5842cbe2a1480408f5a9520a0cd133a888b32424875745e7ec73a41e2e231010378287be953feb0113a41519d2243c8efef10da296cdb393b2049e31e23c460a1f568dbc409a900d559529280149eba21c077f9d4a6a442df592b2861a89d952c832d14ae70f264f92ee3630d290c54631dc0ce60a0c32a68427af86814177d9e61344110f0d8c8d) else (0x45a6e1702be12c383166cd902d1e707e1437325221c4f0a12b3640588d6d2a448c8c3503ea42c6c04284e0d82db71a011e9e68e6834c9a53c007ca8c3063c9089206cfca87debc03495b7018633d99024827073e4058b5964c47690d830690133a0c9f6ddb8fa1887143598103dfb894e12a7091ec3ab5e3c6b0439115a0b8abd444e19da01e3484))))) else (if b<30 then (if b<28 then (if b<27 then (0x3cc333ba96b343d07856728a5ef304dca05ac092b98761639b3d9e3aa6041f18077a68cf9f9a55b0f91053a6007b1c301ea1bf04814f63b341024f415088bd8c2273748f5d0d1773c4608166269c720e18ea3172004cfa0939c09beca11b70456e3dd20c4724c082d744b0508e3044bd36be23a109c00aaa27448320d82fd37570ba6ecd14fe2d05) else (0x7142b16f181942f4894a58f0282da9d68e9b33324dcd21e3b64b847a20cc640ed3c12c4383f8131163f08027451c359e18b18c533e43cf49c2425797eb8f720f940479b7964c2751e9014580f242509c6aab0932d83d8d03ca7061c3dd58d46de4222a14e60450a10c1a08b15ccc419a03b802d61053011742b863130b4f34082da3ac1d1fa88002)) else (if b<29 then (0xe944eb8190376640b0512240e0a9163bbf017359c191704200dbc421bb8478398f0cc441cc61628c0f3be28c6c22096f7a117e0532e8a0aea16ea002ef45c1f2180d39003f751da66420a5b0ad082cb529e7163f8a52038d122dd10db83e3173e8118904a6412cc054e140c287ebe1b4bc043cee482a45166406d261f30c68c1a594103d1b0e7845) else (0xe9506615a733cf89675b06a181be609373932a2a3c658628afc10205eeada0306bc8c461de3e06d5378e3d253cf4985254e8b3c6116110915085a102e5ab4d545fe4f0b07465623a9208de895d2c83ed5d316df89ce1b5a23289dc0deb314000308da903106185b0970eed013c0660192f49cf6858080ef46bde18a18b434f097e80a966f7e840a))) else (if b<32 then (if b<31 then (0x7288ae731390892cb0ebacd0247d1422ab04b45b6318e1093653e480a4a41b5acd894b46129967f180f7dc681a337c99d70486740118e608250270d8286a9ee393730f0371b23760506080a4b25f50cb8aa7440f6a84678903afd1b69039faf32c2b6417ce0fd1c1d00019c164e267573822fd501e337f098243a1ce4f036a8b966dd02d5c6f068f) else (0xa903ad5d8dc76335d021b2f81d4adc7b380eac8923438ce0f5905fb80cc2689da08db237cd209fd1e93d51f9ae9c0ee96f5bc584db0c60c249b168371768b3df150644835189bda32c8603ac4ec4165c01293453841d4e0880a191c48e59b87c7a3f7009458e67b8ada3045727385068222254c2cc753886f42f6104487c2019ef13bc04f9be8abb)) else (if b<33 then (0x104c03c03a91db10cd8444c175941259a5179454a3ad91331413944eda26e621180180de356090e802e194b8b1f890a2fae6f4ae1d2209c699f218c05ec1f0c06702918369d4a1c04981018a2c26604b74b8099b0fda86a98e4f45e5feb164e8a8e5ee11a48638c47541c1915784ea345409196a6a404705b15c4da9513d904ad40e0634978c1a46) else (if b<34 then (0x96c3bdf282fb38701a0c299410011f858bc15cc9a00c0039d8525c4c9405b5eeb72540b218fcd6719560973c1017a8f61089fc2dc0ec50e23549405125981e6c8181a809e205c94e2e016af8947450ee0c69de175f954044c0124807586b05a4c1b5eaccb0b51821a5417181669221cfa00e437d78a6c6d7223581b3997660779ce304ace4144d04) else (0x1646e567e861b32afd3c743f968a27b76e09569bfc92da598f4b571c18b4677845c7d4b8a5a8fb282d25ae2800fdc97246a4fbe94032d05376c0b2cf3a159c0c))))))) 17 i

def r5D0 (i : Nat) := field (fun b => if b<1 then (0x8441e0b038140600ce65b218ac36130156a851a89409b47a39188b44a210c8441a090280371a8ce65319849c4a239148641178b8562a1389446211003c1c0b050240e05018080200) else (0x7879dcbe471787c1e068b419bc7e3b198bc56271187c2e130581c05bad567b2d8ec34ea551e8b43a0d025d2a93c9647219043a170a)) 9 i
def r5D2 (i : Nat) := field (fun b => if b<1 then (0x9c70ce092704338029bd2cde8a32d519658cb1c658611f708e48471c21ee10e1086e8433c219210c7086183fdc1fbe0ecb02fb813dc09c204dd026a8133c099a04cb02638130be3c1f1dcf8e67c72be389f1c2f8cc7c65be329f188f8c37c603e211eff8f77c7ba63dd25b1dcd87b6c33b6185a4f6d26e69353499da4cad2636930b11ed88cac461) else (0x178f5bc71de386f0697832bc185e086ef6960ceb039581aac0c3604eb023d810ebdd15ed0af62d79a2bca15e4eaf22d65cab2cf5965acb0d5fa291f748f6a479523ba91c7487ba43b521ce90e5486ea433d219290c747f6a3f951fba8ee54765a17a509d284e54266a132d098e84c338e9)) 17 i
def r5V (i : Nat) := field (fun b => if b<7 then (if b<3 then (if b<1 then (0xcf83729240cd77036e810bbd1e49017b1a16a60cf9b928cc063f7051c816895167d03eb1a0a7e042ae11b5c178868b45858b860fb701d90e14e202a61d0c4c1711cc19180a3baca860331073a32042ae92b7409e216e4300abee5c80021510b88606b2e4005e00f90cb4984fe02cae3041c8138660588230a643440f8b3d810b21166d06ac01388607380f30d4085e680328212409c3306f3b605e2031656422c27f968d36801e02dcb201f516027615c73972141770067c5010b0f167102fc199f6e03fced410c0855c2371809d958bad0223363a3203d632562c0bf067b78017e03de49067c598d0b028e31710c062ca664c827e399c39035821954a03fc3c65340c5c307d8819aee1c4902fc6785eb02763409dc0ff516543010b0b05b109bb563c6603167e759c2bf1567db80cd951f190215708db20) else (if b<2 then (0x40cb469dc0bf066e41428f4d420d06010e16a602767c555c0d6158035809d94cc99013b2a04ee07fa3b2a18062c380a98171b91f1f0359723b2c04a2ac41dc0118b9b77873e31c31f00f30a6dca10a81608fc3a2c681a08109ee0c88020455ede005b6c401640cde627af011f2d1b4701b93f3a3e0149b8036424fca2e1c81032d1a7b03585600da05f80730e40bf156adb817e2ccfb703cb0a0f621078133d8424eca6f5580fe0cc83f023c29b872039e3470e416f037310811e34c6dd05dc7585040bb8379a1805ac6a79180f58c9cab02175e3c92042c2c169c254c5617a810b0b179209f40b6dda1276561eac06e5c256982de02e6ab013b0e02a6007c2cdb9c262ca654a8128950b53003e2e6dde13f8bbdbc004ecaa21c8144145c3f02791611081106545dac31a958bdb8128950b570046749ed61) else (0x2761e43741608a81a0819fcc648c006edc2d1615701c61ac166158e2a834aaf1eb801fc058762042ae12b8c0764f665080dc9f014d067c03b8860510512b6407d0bcb59050a2ac6dd013b5634d608d40d562c085006e21824d2b1e49013b7585ea0af10392300b9d88ecb00dbce4a8202fc5595ba05f80771241662443508268cc958304c22a0282044e6c000e04ec38cab820e3a1953013b1a00fa05f8af3c940d0c68f8c80f5ab073502d13e2cfa0cf81b78d41771cc075c079ee02800e7c1b946a028ee5dc0c19f06ef218168b944430204659f6205c61e56040bf3721928084018a39067c67a1780cf8ab2b8c0b44a8ba480fa8b01310ad572ee06042c2c16ac39f06e51c817e2ccfa706b91a02560af52192180bf06636980fe2bcf23005409aac21838e86534062cf803e811e34cfb101eb3e0e6a0))) else (if b<5 then (if b<4 then (0xb7d283d9c2213700a980c5874a43026b92067603f80b0eac11a958f21810bcd441f03585602b20aa254797c09adc819d808c3cca8e016fdc1e4603961d185c0cf5fa2430725ab039e04fe76c9ea05c6540d04093a2e312819ab9770902157095ba008c3e2dac27f19636e83258d045501fcdcb86a058fb8628414c8a80a0833e2ccad3013b319f0a0cf81b710c19f066e1a822c211a7b02157f8c2e05f9b90c54050ca8cdd012aa076ea01432a2cee01900a0570307204e1a80fa2ccf610ac41185421a207c65640c04aa124817e0cde43067c59ab6e06b2e40154094d5809d809d879d2302fc07b87205c6362dec089cd8006c33e07dc4901f4dc018213e8cb1a1427f016550a17195033b01b93e2a9a0276ac69c407f0161db809d8d027b046a56027e0686e47e58095d6a18480fe01ca3f013b2b3a4a0) else (0x662545d1c0bf00ee1c80dc9f167b013b2985320212210e2004ec38ca982c103370902e32b213e06b2e474641608a819a821a00e4fd07123285e20510e53c7c107a94ac780fe32f6f00084dc0cf60316340534054c5618481629144070856dc2d1612761c19ac084c282b3849db8d561049a563c720230330bc404ecac5d880cd8d1f0f013b3e04fa0528abdbc00c0cf80a080fe03ca3903fd3c887e042ae90eac0bf00ee1f804c8f055e0d512a473c02a67e749407acfc58481f58d033101a1729e460cf81b3edc07d02db7e857e03ca39013b29994202865455340bf01ef1f8128b9107d013b1a00d603f8330edc04ecacb71827e0ccaac046a9a00b20746347c9419f066e1f8280ab1d35067c599f4e0372e12b8c19f06e51f81819f013f067c599f5605f8cf0c540d60861bf81139b000781fc1987560)) else (if b<6 then (0x8d4ac04ac00137006b84fe02c6e301b7288dfa0db4ae120808fa2e30b8129ab0141018b1b211619a2548cec0bf167b78009d8d154d01fc6595a60c36ac0cbc19f036e2483852b012f02fc59ab6e0316540d5c038cacb45879495213f0343133d00027ee10c9404ecaae8c830dab033f023c6995b205a23459f41404f8ecf008419c61102d5dc38720d02562eac193f7017881ac2b0157067c0d9f620a34ac790c11e958f5b00fe02cfb101fe4234da0277b91e280bf1667d68137860ae306ac033a320776ac0ed007f016350a3408d87b701f4dc09ba13d6322aac17d772e4001ac2b174d02fc198dba03f8b3dba807f0167c1a3189f167d01fc19b87e07f25431b40930a6e1c8135870fb70358562ce2084d4a561404606618480a1950677013b0f3a320316540d641544a919d817e33c64302fc6785d70) else (0x44e6c749419f06ef24833e31c2eb846a9a00a607083bdbc019f00ee2481b606f6f4067c1bbb300cf8ab3edc19f037b8400db861c49068b1a066a0cf8b33ec40cf5c724600ab895f99018b3e00e20c627c59ec010c285b384fe01cc4306955e3a2a086d22563406e4f8bac808c8942eb01fc0595b203161d049419f19fb81804c38855e09537f861205f83371241a2c68195832789830304a595150402a6e13ec4050ca833581d19f1f2500461f212612a6e11b7419f15e52481718d9983067c558dc6033634347c06e4f80a98171ee18aa01537f860605c61e4264062ca6155810a2cc68509fc199f620cf8b32b8c1211d47c0a169c9013b00d11b096405f80b70d4054cf81a6830dab034102a5dcb91006b2e4000e194558f1980ab86431f067c0d876e05f8cf0c0e062c681a48268b91c5902e32b331a0)))) else (if b<11 then (if b<9 then (if b<8 then (0x4de183edc048f7014004dc9f9d2503333e0cb20cf8c70bd60d6158b3b81119b005501fc5b9e460942e474d40bf167b75016baf1d9602145f863e03727c551c00197a20684230f96930e7c6385e30b8833988419f1561d380f78f830301b970876e03f8af19240b148a20b867e389c3902179685ea042c3c59b407acfc57a82934d420d06811b0f5a0868ee047c0bf166571818b8615b7049a563c7e03f80b0e9c0b8d8802a82688d1e5f02c4618d0a13727e748c0bf0667d8810a2ac6d7003e772d261e16e4101c054f7014004a195154701533e2ea60cf8ab0eac089cd802f833e2acadd018b0e949205f80370fc10720ce5e00d99f1f9600bc5d950a1b780b9a2404ef723b7036d2b019e01b93e2aae0cf8b30edc0ca0767b2010ab841ab049a563c860233350bc407ad5836502de3983230046166dce1) else (0x5bec4749407d04c5d88756009c35051e5e3a32042ae13ec419f0365698332b841a7000441950a11325c15782851561d8833e06cad9067c0d95ba03f8af3c5407f01656e8300870b4906da563d6c0106f475ac24607a091817e0cc6d7046a06ab020ca2ac78e4062c6813b833e0dde3f01f40b175a13d6562bec0b6d88031817e0cdc3f041c81387e040d0f187c192cf819f830d8d0a4302161611ae13fc8469dc103c3051f8356019c33068b56067e042ae156dc19f0361d6817f43c61f02fc19875a03f83321341ae46809d833e31cf1f018b29a3020428abdba81ab06654503259f045901eb5715f605f8330eac1071d258f80c59f047d003c09950a15f803712413f0663560325c90335067c0d8db202a67c61f40cc41ce928342ee0a4301eb2b15ea05f8332b8c088cd8031830d9f0659040b48ab060)) else (if b<10 then (0x3f8bf3c7c088e7802a80dc9f015906812b175a042a2170e41aba5a206804cbb055e09fc05b886088e6c00a80950a61d3801e02cf650ab88385ea06522c45802d61580a480fa8b012f0a145595b20602ac2ee816625cf4002373d1d960358562cfa0838e8655c07f0161d6833e2ad5b700065e882e1a34bc748c19960e17a8111bf1d2302145587560d0bb828d419f19e224821b171d3b01533e06b205f8ab0eb4146958f2480fe02cf5c82d392025604466c0194186d5819a81eebcca880548b1150803f833dbc019f1567d6833e2cc68509fc19874e010cb675ac262ca6e5680fe02dd99067c0d874e0a34bc749407f0661d6833e01c843067c0d8d44844e6c005e0d65c8003c27e389c49067c0db87e083902710c09bc3056c82faee1c4905103e2ce2083c3c817c07f01656b833e06f6ea02273600030) else (0xd2b35081c09ac3856c833e2ccfb701fc05870683d63256040d6062e24827e389c3502e36200b203727c6524089cd800fc35c8d0135003e2e0b241bb8ee03ee08515657182ee38824300565a0b241cf8b31b8c0b8c6c84f817e0cc3b102fc07bc6a0cf8ab1b740119682c9073e2cf6fa01d90e14da0336540cec054cfce8c826115012b065192881a03f8331b8c04ecac2c1867e389c3301537095b205f8cf0c8c15e958f1c80fa6e02cd0afc19b8720bb8e208fc109204e1a80fe0cc6d704584234d602a61b3ddc10da44ac1833e6e411f021570875a0cf8b32b5c0855c20d6821b0f1d3b01fc579e4a0cf8ab0edc1771dc091836d2b1e49049a5602620964ac068009e458010850b0b05920ac4599ec21cf8ab3e9c04edc853683560ccf66057072edf60ddb622a10149978e8c81626e0ba10846dc16ce1))) else (if b<13 then (if b<12 then (0x5aae106dc0118bcb4986ee3882350426a52b1e02a7b95a00166254ac1819895034904fc733a260008835584307a941b980fe0cc6dd0153709f6e066bb92a00188558f1c80dcb846dd007e166dce1cf8b3558607f016adb82ee38812302fc67864a0db4ac04ec07f06657180c59f0a7d064b7208b200a80372c80dcf70647033e06dc8282c7623a320beb0392180c0cf809d80fe02c6d901b33e08be06620e748c0013703d084ec8d4f2300462f3ad61838e8651c085859b83873e06c6e30426a506e609845404ec1308a8081c17195032b019b3e8eb801c67e5a2c32695809f80fa6e02d90a145595ba00a81608cc27f00e624805e2ec6b2046a9a00be0428ab3ec41771c6141027e399d2303bb56067604272404ac0bf01e51a817195033f06db72095008d5340194062ca8136817e2cd5a70665dc38920) else (0xa44bc746416f03655602ee38812501fc1b8c7202a61b2a6c11a9e8e8f833e31cf1900143db9640e635205fc1344a8f2f833e2cc6dd01b970ab6e044e6c015406e772b40002b3b9d6b0d48952abc08d4ac050417d5d7243017e00dc3901b9709f6203f8332b740b8c6ccc6817f43c625046a563c5e03f80b712407f066adb833e31c319067c19b8720cf8ab2b5c186cfa50881626e00d90e9596840e0d16340cfc1071963540171950335003e420b2413727c052419f167b7501ac0d5c49033f90c918062e182b641ab00ce1a833e06dc39057475c90c024614db9427acac581822d1f5f5c0214dc864609845403d606ed58f1c81999f1e3f046a56026a0c021c2d3414c8a809d80a9b846e301fc05b86a08390271240b6d8802f817e2ac6d9067c599ec305f83378d419f06ee1a81999f066301b93e028e0)) else (if b<14 then (0x8d4f4749419f00ee1a817e0cc6d901b93e2ce209f8e2710c19f037b7a01acb9001f867cdc94920cf83778d40d65c803180f5ab0663067c0d95448d16340cec089cd802c82ee388115067c0d95ae02a6e12b741666e8eae022ca04373067c5995ba04466c017c107a94ac2833e06d5b701fc19908e0c37240cbc1771c4089833e0ddc39067c55edf40db4ac06d0188558f1981139b0063013bdc8eb809845403ae15843d27880fe02cfb7051a563c7e09a27c8cec146978e8a83259f033b018bdc8edc0beae10e9c1771c411982ee00c6aa01fc19906a0cf81fdbac1269580a082352b013b01b93e2ab206b2e40194138ca930c80dcb84fb705c69439161ae0e10e9c1a046c87182ee38811f06cb5609940d5806744c19f036f2180dcb84ad707423e86060cf8ab0ec407f016e1f8212409c4901fc198db20) else (0xfe02c6a344b2563a4a00780b2a2439f00e31f802a0582350cfc733a3e0d5806748c00a458642073e2cc6d3003e2f2d2613f8330ec415d20724300fe01cc3906da5604be044e6c0046088cd802c83408d87b1049a56026a0cf81b1b7419f03657180fe02cf8142fc05b87e0cf8ab3eac12695809d801f2136ef0dbc058d5a01922c4580346978e8c82ee03e41f00bc5587240cf81b0ec419f06e52182d1ab2608067c559f6203727c055c04ecac3d882354d006304d1992b1a0bb8e6045407f15e78c833e01dc3f070a56108602761c19dc177006ac500fe2bcf1f03585600fa03f80b1b7419f03fb7881999f066501f4dc018a13f80b70e412f1d7243033e01c83502273600ca0db6e4120007f0667db80fe02caa3467c599f5a0cf9b928d419f166ad380fe0ccad9067c0db86a0))))) 39 i
def r5 (i : Nat) :=
  let x := r5V i
  (x &&& 127) ||| ((r5D0 ((x >>> 7) &&& 127)) <<< 7) ||| (((x >>> 14) &&& 262143) <<< 16) ||| ((r5D2 ((x >>> 32) &&& 127)) <<< 34)

def hit5 (t : Nat) (v : List Sig) := OrbitLookup2153.orbitHit 8 958 2206 1024 o5 f5 r5 rot 5 t v

def ok5 (i : Nat) :=
  let t := r5 i &&& 7
  let v := replay basis 5 (r5 i >>> 3)
  decide v.Nodup && !jump marks 5 (fun _ _ => true) 2 t v

def o2H (i : Nat) := field (fun b => 0xc15b4ea8c9d792d8667a06dd6055394913d932f26818b0e2000) 12 i
def o2L (i : Nat) := field (fun b => if b<8 then (if b<4 then (if b<2 then (if b<1 then (0xe38d33c70beeae7a259a69e79e78a49259248228207e075e81e71e7de79e71b75f8628a28a18617df7a07df75f7df71a) else (0x800420c10851841461c924b30d34c34c38f40c28a2c82cb28d3ce40e34d34e4104935524d34d25165934945955d869a)) else (if b<3 then (0xdf7db5db5cb3cb0bf1cb0befb6eaa9aeaaedbf2c2fb6ca299e89a8a6aa67a279e69a28628a38638a181c71c71a71a69a) else (0x8e49249269a285e7585955935565d65985945135555135124924514d35545104124114d459865c71c71d6da5d969a69a))) else (if b<6 then (if b<5 then (0x830421040c51892cc34e4103904d451659861b65b6db65a5d34535155565d54d34d14d35575535155904d455761961a) else (0x4d35165555924d349145041138b2cb2cb30e30d2cb30d34e38f34c2ca30a28a3504114124514103d048f45145459869a)) else (if b<7 then (0x10720a24928a28a30d34f38e41138e40f39038f3cc2cb24928d34824c38e38e38d34c34b2cb30d3cf4945d971e75d6da) else (0x9669e9aebae9a2aaaaa2aaadb70c31d36cf3cf4d76e79ebcef9ebbe7adf5d33c72cb0baeae9a68a28aa9a279a692369a)))) else (if b<12 then (if b<10 then (if b<9 then (0xc73cf1c6fc72cf2c6fbefbefbecbaeb69aa89a69a79eab2baeca69a66a269618e08638e49258e389f6dc75e79e79f69a) else (0x75c71a65761969d79d71d6dc75d6d971d6dc7e08e48e49268a486182175d79e6dd81f7e08e385e79c71d71d75f6dd71a)) else (if b<11 then (0x81f79f85e7e0862927a279a69638e18e49638e28a38e07e07df8208a39638e486296385f79e79d75d79d69c6db69a69a) else (0x79e75d6db71b71d71965b69b6196995955555135154945575d869a71e7e08618a48e18a075e7e18a181f75b6d95d865a))) else (if b<14 then (if b<13 then (0x831450c418620930e4103d25144cf34c34e40f4134ce3cf3d25145545545954d24914d665869d6dc79f7df6dd71b6da) else (0x38e38c2cd40f30c38e3cf45449145341038e35038e38e40f38b38e3ce3ce38f3d14545535545955924945965da69865a)) else (if b<15 then (0x75d79f75b6db75b7575535165d865865b6596155533cf4914524124924d55155555145985d76186196da69a69965a69a) else (if b<16 then (0x86081c71c75a6d969659759a6de81f7dc7dd7186596996db69c6d85544d25175575944d64cf49255559655561459761a) else (0x1a)))))) 6 i
def o2 (i : Nat) := o2H (i >>> 6) + (((i &&& 63) * 3093) >>> 10) + o2L i - 26

def f2 (i : Nat) := field (fun b => if b<24 then (if b<12 then (if b<6 then (if b<3 then (if b<1 then (0x91f14998a5e51516c34410d3d8b3485c68b462630d50622a3e2a496628cd9232ff963b0757a00c30394e11cd8367f09a88d66c7943ce4b32887c87ce34e36824db53bc044410f7171aaca33833a478764d1a70846ac2dc54b401186210c4f40508e1c4263308da61ff1a6187335805ac061228c48a28c320dc062201738a388acd1c40b52a300d2ab24758308c000822) else (if b<2 then (0x69b050c0f226205f0a10998980f6cc358b0351a34be260bd34672519ad05905933194e0b48f18ad1a7c1119a0e5fc1977824323cbc172d3509d2f594183f882712a38a139c84d35217f3841ab881356a003f660ee3c1cd2cdf3a78c0dd78499a18f43d3bc980a42386c09fd215c51544a4020ccd526c90d6c4746724501a01e21bd0d30ea8ad861982d360f2ed40e18f) else (0x2d4b0609307829ef8c4a609208f3c844c3b518c7d980b5ca3d4c4c3bf8cd40432d2c5dc085110e3b79a42641566bb0da2d76103cc8016c12457808bc09ab8146d246b2703c1a5c469143d28080a63df8cf3daf4f4e4256387b0003b21f1477042da245305d06610183604fc90d7112f0985b0dfa89012e8b840263adf5c149c1d0f453bc1e55078e339c3479783e396c))) else (if b<4 then (0x61e1cedb23372cd2fb99d3cb9fe0105a650f8f159e0026f208e71901635a1404c724ba8c1a698042918d6a0f8e7540517ca07114dc943044c27083a644d82d0e938093a6db20aa4d20830730b154304903984119a8a3be8a580948814f4b739e60ab0907a3c0b025cc1c9d082380826827c409764609804118d0086e6e4064800650e11620bc8120e08738b1a51cfc86) else (if b<5 then (0x2220c56056192004d68c43d7c4b5ea2098b52067c0e0b87008f5a917760e65037ed0dd0b145363e093a1f466a607f001b073ba31748249d3819cc0267009299074e11d773e144b815a634c52b2e809c2432de4410023a63c64805bb09e5c92040c5c5687a20f45911294fd888e40e11813f24cfa27315b04ac6930394ec58de1170cf2bb5a1e0273424328278421a783) else (0x53318920021d11bbc968b04e69e338645f4b55c25114732b04248772a197e842e3d8a0db26c162f8c1b646494d1aaad4645356751b846e01d720c2a65566ca3c68246c24ca38cf47262751cc729ef8a7266926cef3e3878c683171020f20153d14d8a02ce84510812a91f4c726a6200c62e46a3fd032b6cc33b2f7048b8e1f32c0c487f83ce39f2672c180403538aa8f)))) else (if b<9 then (if b<7 then (0x46918c9c689211fe815481d418d3b4e1c4cc7422160873b214081e8fb21926262804c72942f2d00ce2fcb480888661dc20737330ce542e1d0692c1720d9f993de58d2568ed499883400019e9f35540a7756a6399f0b2861c62c803f18b6b396d05334742404f69e34a5e1d0b51800f6861ae3c663112225c6ca5070865a28a715db0d44734f85702820c41f262b1fc41) else (if b<8 then (0x3247c9a4e1cb1c62876df00cf6685715a19b2ba14a4411b7b139032f6b5118128e2c8ebc198b01a8d308d1af481b13deacc6c339f74b3ec5ce08a22d32508732940a83f114703246847256846356e8b0c11b28402323b86c4a410263dd88a7180ce7a324e41f503254086114880156c8d55d28d11b32be0a0cd14d365d058311cb86c12fa457d80236a3d8e65620908d) else (0x275a0dc1029445df844b200e4241a3b8053848c28ea0b34c305f876f93cb50c1576839ca8752d07c23a370c39405234b7ac15b424a0b6f500f72b3c41c98200a01c028197e29c6496ed39a70e860165d4690e316fcc4810997ac23020220c30ac631896420951c341800a7da77f24fdc9332944c229b2123f916f6391889195f6678a5102c8a0d0a436454a88d1cceb3))) else (if b<10 then (0x131200b8f6d2197cc85840d5b8a95001d80f4d9390a863d1b449ec3c15159821b4114f861fb20575d750252a0f25e2249c964e34e2481aa500d8e3c9081cc100bce61427b70dc80d1c83241c261c0cbb391b6f0a81827f2657078551863c70aa32490f83230f8453018c5490001290501354620b0d81718669d17049ae8f6a40ce01725b944b0b7ec18e381336cc5950) else (if b<11 then (0x6f31538093e62e1749317741f8c861019fd11b1c4288a67b0cefc21bc06114868c651d422d040e03468a35130f3cfd85f915a72ce2c719ee9a80045814e9472da506dcd128a4424750b0102ce01444880f46820ed9232938344c0244cf51e38b40b98956c08e4361901d15020c014011a3aa84c82428e5a4c8c4f50044852ef547786156250e083ba6e3d0b682011f04) else (0x3e270686499239e54e39edc6393358d8b3828eb51228b32d60bc402e50ca08923a7465bc92004594795b30c31b9003188015b02c5bcb37c78cd0d15055b2027a52147ce3ac48e80b0840a014b69018a9001e6380c046c710acaa1a8b2478e8850191a918554beaa90a6a040580a1563c252a2d10c9255923d5978230cf1d1557ce86301ff6680465484e30219c585055))))) else (if b<18 then (if b<15 then (if b<13 then (0x38c88422e02a161f0e75c15930a3b45d2e482fe6cb8844652807098f12950c035638d36e31e015bc508d2a240034dc4048355034c0442e9d20e8467b64b8ec624363c80373e8d70498062380f57804f7c93a41c69780482e38e77b20d478910785c68b3e214e85532af8c54b00a7e0e0e2bb3498fe09e3a0d8d7271191e44ed05024f330e4bd0516a15f8005362d4004) else (if b<14 then (0x3e02cf03f166424e446c41cc2096951054dc96f323e1b2a014e37901ed9ad814ba2a00877172c931116f4c5b0f81d31d105350ccaf0c29e3e5c0976604bb767cd01c2c828f14dd8132508bc00224246d6d7b534cf8e31250b8de0a314c07798a3ccf95097341680026be3d415e61d2e0748e18b7b0958016487602045f1691d186c228e491dd496e5015b4d4f03cee0a) else (0x3dc30efd019cdc050e683059acf45a06100377639294e0e01a4e8681abcdc823052ca11137e61450804b05d38b679745fd234a0df0c912a30047b2f6d9b8c15ae2093b986a093e0b27e6c630f013864e035992cfd0d38cd1200032bb4c38389a31978c5ac00c02d282516f851e725e8086b910f09a30a406d571b371d1cc70201afca595014a4d3596ca3d78fa05d3c0))) else (if b<16 then (0x47618fb7d14256394d7d61cc5595df31744e35a3c94e633a7ca7ee15145d282389e4a9b90cb325a4e65926098a92f29f70c25ea492961a46851c87222a058d66f7c57c990215e8c55b40e332a98812430f7bf31694354a3625875ff2094ab1977a3cc662e15b2c24ea38f7d3384186bb474c045d981d32d4e4651c344bc95c1010a4e2588c78a51fa04ca04316e0d31d) else (if b<17 then (0x8480ca59761a3cd6c53532855c1020c9aa472f520b48268f701f0e4a120f11482e217e0544d0e1a0f75635f4037813460129ac30b8167e409410d46c14ce2517d5d6a8d3e800d60a1b276130979939624b0c424f4fa3a30ce8461ae4c044a757391c484563cff462a44571cf325702c0734ee4a8972320594a2332609c073bc60d4a787b087f4c17a602e4e725054142) else (0x6dc29b08a35e54bdd82b82c038b353f4580a918215a08362263a925f40c304d00b8cbbcc2e33cad551565259836d420b4e393f09970e23878071a2e004a7460dc326dca8ff04061067a317c8d32e3c991e2012c6ce789836038276a21378318338530d4cb2108824071922462e14417c033980ac0e1ac02238a7bd10679364904dc76338e4c1272881c76020792c0405)))) else (if b<21 then (if b<19 then (0x90440824e08635e0cb72c09ac890ae11e9881421d51444160503422ae18a6878ed2633c112e8e2d09460289bcd50e30efbb87f2128cb34905cb432d8687d084fa1a1c8163e2a3d1d3be205e1d05115758d3acc869f57b62dce406b40d8c0f4ce18cb0b1b690464000640a7016d321928129225d20721e2dfe4a98d11a25e38a64a1488ef04fb8434b951ece20c066d89) else (if b<20 then (0x326523a805522ceb0d314d06c3327920551990b1cb58e2ca224b477e9315242387448d9317b657b86412088fcb13a860a8e7cf10574697a29eb416b801922d49b1658826e12037823aa2899568f974d41131405eec952110f4002feecb32c27c188d060d43ce21b1a354e411356845ad60020a070868470c98f84a19bfc8650996f4d55420e58d8f00cde0d13a001f45) else (0x1b538654c1553845c62eabc4e0a0f639054301f29074999c0958834f21482828fb68a2481bad9e7492fa0d962c4901415448a01a0cc62d30da9ce4c81453cb2e0857f8049419ff8057b08b9391a07178495642cccb71c321f60f38a34c7af04936250383c28a95997211d00053c1cda201f9246df16790cd66c31000cd2a5c209480f4b51d1e8290d45ce852a7d46550))) else (if b<22 then (0x33c34780117525df0270c18e9db34e58d157138ae11053e660bcca2d75ca4db3ad54df0d2642dffc12a2c4714f0ba11e4032400006a290345f6c91456c498f84b046fcd05d3407528f915e70464010af8f83525be8c4f700b4a496c0da58868a687c8576700e95c0f221bac444a010e8e394c8087e9350d14812550c11cb96835e34565d9d734038d28cf2c32a04bf86) else (if b<23 then (0x2e7686c686787c368834d361a4d2e900410900996554c68d1d4d0c3d55cbc558fa4cf02f5cb0402c291101bf8a57e1cbe3c1711954c3360625ec566e6156c120530600215015f20477229d444638084b609aa0d0f8e3f14c15088cc0ccdac17978360b6182cf4a63c1806e0c10e1991892e67db78668e1d14079772118ca2760c94071a65df0075ef187d400a134022a) else (0x3d5ac238924d6d8c8f254bc5d51120123dca67154cb186cf08f3c72d73cb2a917628c5a8300dcae491a148138089e357b0236e34f42e3a71c58d97de2958ce38684c6901b494f60f98c349b8900c0803ab317a49a57256a1ba4c21c1c629154104614f8b21a6e0378e295946368c882c203925a94335c4400d47882d310a2ff7a294f018e8cd7d0223ccde706925c1c4)))))) else (if b<36 then (if b<30 then (if b<27 then (if b<25 then (0x2e5b1e8473c6f461086801d61cc8ee298d0940420704505c3d0a0d3cecc9f1781335ac006ac196f0685929e78953718999d1b22c41858da1593a75930549ce4253cd9ad2983980cb16444e4a133d4d50803ce09dacb69314e19d87d21494823cb1ee0e79630ea1a8ae3cb1828e898eda6353a08f3216d50588710c00198b5d310d9060962a4045686300f8d7cb05d4cd) else (if b<26 then (0x4273ca8aa4d42517091f808ac8392638d6772984c994c6e70522cc1401a5b8c1a6f5ed0259c3ccc432d7b824c9010c1c70a300083d0b61f14c32f1661243c48860db38265428a28d241a5dc0091a01f48049a18d3290e511668951224a6a8280226d4980639660843410e51315b2805be9651e230987615b4023406818c901339248123c353f036991c8fae0af0a1403) else (0x7920d95ca47f0cd61681a2d96e84d030f9140ee1088c11b8f44d8b42e249e8f08a226e873ec9403308ec59ca421f258710586e293fc02cc161cc977721b58c24b40651e14eac948b34210a7ca14b1995ad3f824caad2f979d1856af297a493f050d9b82904810c73ed98c7369871d7d894e83d30003d6ea425a89c08e23938010db22161783a880b80a698570130b95e))) else (if b<28 then (0x32e5072850f82cf9022960c5384502381d4e95730a1d913c18020a0d03811073ca0893a809438001b98010fe16371bcbf002dd1c96c916a7d6a408b615a0d26815d044f93c3155864722d064518b4a44068a8299e0c0188dfcc26aa2d0802392e4e2e0337c4689905b0648851aa00478a7681dd8cc5030d1d0733a3c68ac5b33ca45d56b1d218e6f12cf01736c0c14cb) else (if b<29 then (0x65a3cf29f3b48cb6a426a2dc90a25a9c1a077df1081d21340c2d075e038cd1d4dc10e75e364f8d2c42c804ad4e1c72cf5922e71c724154b20bdf78a32c69d913c9e6a028822dc78032a54b5b82ba4804a2590389ac0167340056732052d0d16e718d8331640fa8f3467413cd71d04c2291db3c6e9f1b8b2605a44e3912c425c106f490421e1380370b8ce057aa14e2b3) else (0x8b50df94d52f097d4d298d0960c0ad1df1c51411e67c894c01b6401c02c3a0f65d20da122d6bd8e8b4962a340952228b04790911750e3e044e3a528b3a060c32770c7b03181c58c839d104d2493425bdc2333e47b8600c89568836a21a1df3ae421b0f4793da50a3462c548200631d90106e359b592d6402d8f5e212431e67d7d0b4d3cf98e25529cd047083f0120248)))) else (if b<33 then (if b<31 then (0x194d56d8e1ba08440c0e30125c045914ca1a2e854b5130c50ca31785a02064d39dec9cc08b83ccc6f25db15d831b7745a57146066c018e22c089d6fd24e6490169df1803e8ecc0994d3002f0a93e2da01845e146d118b0116e8437cb1b34e6ad059f1e3508060553c13ccc772ed0ca7af90070ea591a4e868220a52a3a0636cea3f1248410c2ac23ab546c314452640e) else (if b<32 then (0x5790e194f70f1639af4b00042890ce310705362d123488ca15ea4d6c00d288435e059dc43a0a0178c903002c847cc3970034780cc5c82e94026c239648ab4a98b22419e3017068710613de28665988ff8a34a805c036d811518d2cefca62f1dc01f9cd39268d8372f64d770739208a9429613d348b01a2e5ace67079264600ab9874139b4c941f98132124944010ebbd) else (0x9bb164b000903c02798d1aa298633cf03c096ab197f432eafc50ca0410cbb62293287f0f5af04d56620604634d023a1aa082865462079121856835da3104c43d610a05301d2dcecf41b280e897a820ef93322183dc87520cf6271a8edc48d66c00c0b62213407ad99139b14565cbcff063e37cd9977e139318632ebc449c19610468e921057a012f45c5a497fc05b5cf))) else (if b<34 then (0x2c20800c36fc2d5f0839b0483cf1b858f4d33005075485722556425153ccd8c00c660a054102cf6393204c4ae12e6fca50a6e81453e431470641d54e30046a3809cd2072f820476b9b43d9cc04612c93885dd1ccfd83ea7a410370a1d174c3949cde83136b20d0656a0db2895b805ff4269a2208852a61c9f508dc00f44b7ee3d8f052143069563f114b8a11df1065f6) else (if b<35 then (0x3c6449e18032259c411e81401031c61ca82f57f04a35834eb4621297621ca0884115f68e07208da9727b486cf043608f50529a6499d892321e18c52829308b389a4dcd01be1a405459e14a9741f63408008fd19a30c4a92cfb452a8102a445321c4c84705153e4501642420066b6e13ce7ed2cf4ca03421bb8868738904a022e1f2431a850584505805e883691096b42) else (0x37e0d030868e5953015400525429960c698611b8204807912135883551cce772ec663f5c333be2b0004a026b8352d10f07d3b01e0c045b514a7fb1d03831c008209da465b9308fe401df4e7313713865925971119872d7c5fa0e78f10d10823c71f0877261cc83029d9ce1f229258b68500ed93ac04531cd04333518b3900232654cb28128398b3647a2a8485838e31a))))) else (if b<42 then (if b<39 then (if b<37 then (0x3400cb10c2a78195e34981ce88136e5cccd1588291448207247dc858624d57a2e0d4e8981f1006ea21624a1f8a75828cbb318204009f84228c13223a38b75428a645a050561d83832a49402b882901bb0d3d49490211c221e7c86b519430f946219f884af1cfa1a31c68b9097592d098e35278cc876fb354d471b030200a80d0d9d0242300eb811ec9805286e6297b4c) else (if b<38 then (0x21a4bb8a7ae04968f1a3f93f4334ae6158b2ee44b53c1188a33ec6b31df88379830a4021a7912b086dd08fe803d4dc072e70e0d96a039d80d9860700e398f8540cd520124aa19085e4292f819171cfb9d3624ca9da91935ebc636030c08a2f9a85b8e8ce85830d4ee14f57c1b2e5d68d2f9f4a1026d505628094a110e4833de64a4b4ae08c5f68dea611946522ce5c5) else (0x5011444b584d19718e1605c000b9af262e8872e3c1d0e3cc2435892af385d1e1684201c97781c974c0811619c35cf1503c037858ac280214c07d84a7211c0c41718c1571894e362267634e687372edcbc0524390783119b4fb537eb217dc329ae86a01905120045745054b83083365e225612129013c014d64e2fcfc84881a42dfc8568101444c47d10624131a343b05))) else (if b<40 then (0x85202564183939a48b4423cf8c66080c68cd1169c02da94505c0cb86b09e50342b38e5df20028561501ac1a3554da3ceabc0990d1bc78e094e81b122bceb2a0a8364c447b31425488ee79c18949308be1926860e508371721dcf66d21004e279509d991733127853d1f1638f73008c58e16c765a8f31e50b49929e749b4b92e3535448d80e574885c194e892f63d7c00) else (if b<41 then (0x1a7e178f7f0152dca2cc446c1d33010860f0d300beb51ac4c3e8d8fc3ddd0639e089c807652db1852e25052837ac14db1433150bfa36721178ce43f30a8830ab200f464c91d028a3bfe596c96471cd62a3062c688811788ba9b1a5aa29024aa38eb4d1b4d555c13452c54c790b7dbc09723199bc813296228898e0a510055825e90033065c00866a6576c428b6861c5) else (0xb11c07e37bc2582895443913cf159759d442e9b0788a018323f8d8c83580064fb00932300e7cfb0b315c8a2102e8d5e6ca1780c188e5a03c649330704bfc60bb18928e940299c0a6661d27cc37a4049c1887155d043d27079025c42d2d8940801458f91c3635883b260d2db19e385ec73adc0ba2127e36090b3b430c1061735007995a414934219798e2f633f3cccc2)))) else (if b<45 then (if b<43 then (0x21a15ac4e616349dba06f38dc0496330d4be2100804f155e1cf41e11d24b70702281a84f3d850680d43710eba418e14e6020e41e608986302050b3de005b4471f00f0802f7847a800cc3415cb9361506861fe1e578b4cc30bff92682a03c76be10c28579a1497268eb3dbe0d1f345f28f3ecf892ef9932dd0ce53f0cea441a1084b2293719ba8702f3947482de2c4f9a) else (if b<44 then (0xbe16548373c393d0a334f04c670fc1da158302b4a71f87932080e6581958043a0ea352969d11688246b10f48037e88744099819420b32426020a68270adcc181198a8f4d71cda034572c19468d129d54a43508748219c0e000466404e61714924dc372a4d8320b5e7109e9c2d82e6cca3cf50b2961281a22096bc165f018ef7c9f499160d42400c615db8b5d835124b) else (0x64400c42c0a71408fd97f31ee43305a2421d2e498ad0894b0db68369374f7351b5c4025c6b72a1bc368864f54d39c10d4892a7049ec125324073f4e6052c4b33a888b0115112350a68f0d120f262288d847210d81021b33441c75702944c081e19038c8cc69ee8e85f1d6dc434e184fd271421a5c02fc74e20c275388e2815c08400233090619201145a8c65d02d57c8))) else (if b<47 then (if b<46 then (0x3390c65688043d0f0734160564b7b01dcacf1971446cf0ac28190a530053a4134cfcbb2828724084a00921fd03278205c903f75859de120bdfbca28946288e24624308e67758cd921791009b290a2a342507b36590a88925850257d09084024b3c652d3ff28f95e3aa65ec4c34334f18048300b8b31ae940ac45262c9ade90251818f9831236ae58c1875c01b155fd80) else (0x1303c2dc850a0056948d23cf25f19a14b9a819eb8e2a2373b00ccb024200dc177a3536c22c02a02c428d0845030124d3f839a224bb0912d101d8d82125a10e47e08d1d72fa48bd5391319ce0d59604ec142634c63d742c10d4d131c244f87716386b3d0d2200b4b580006d821083022ca52b15940b5a334cddd2a5ac47262162da60158515190824a8263c092a21f98f)) else (if b<48 then (0xe20e03031180643486e23d644052c24f3901d438b42f0590a558f6882d3b06310f830ce8f0504a609482938873adacb4352855c91031da3986cb3b6247c0d9063cb9799671250c067d04b9e34770007642f9266c4d5c52449a510231e4c838d4cb62c6767d434e372acd53a29d545d0088415a7cc66e051a8604c19b9093e528c21415e7a07c14061cf3a43764ca9a8) else (0x1fd4b3902e18897fb245e8014816568c8c2288f888dcaa10c47d904ee201434c47a405018a01424c2c61d345520f6a4))))))) 18 i

def r2D0 (i : Nat) := field (fun b => if b<2 then (if b<1 then (0x7c603dff1efe2f7ef7bf73dfb1efd6f7ea7bf13df85efb8f7cb7be53df21ef80f77c7bb83ddb9eed8f7637bae3dd6dee98f74a7ba4b63edb1ded8ee6c71b61edb0ded86e6c33b618db0c2d6fb6b7835b95acf6d6706b32b5985a5f6d2ee6971b49eda4dcd2656931b498589f6c4f16277b13b989d6c4ea623db11c588dec46e6235b11a988cac461) else (0xa3b0d1cee8e63472fa39751cae8e554723a390d0bee85e942f2a17850b9a85cb42bba15850aba855942a3a13dd09d284e54270a1335099684c74261a11dd08c2845d422ca111d08868441379c9bcdcde326f0937839bc0423ee11e108e48471c21ee10e1086784324218e10c302fb817840b9604f702708132c0985f1e0f8e67c72be389f1c2f8c4)) else (if b<3 then (0xaf7457b9ebda15ec5af3dd79d6bcd15e67af30d796ebca15e45acfdd67cab3cb59e3acbdd65cab2cf5965acb1d658691f748f6a479d23ca91e148efa4775239291c7487ba43b521ce90e54870a437d21ba90cf4864a431d21868ff747f6a3fa51fca8fdf47eea3f1d1eee8f6347afa3d751eae8f5547a1a3bdd1dda8ee94772a3b7d1dba8ecb4763) else (0x2f0697832bc185e092f0477822bbde5ded2ef6577b0bbd2dde8ac1f760f3b07958396c19d60c3b03dd81cec0e5606ab032d8186c0b7604eb023d810ebdf75ef5))) 17 i
def r2V (i : Nat) := field (fun b => if b<10 then (if b<5 then (if b<2 then (if b<1 then (0x173219e432c847908d2116422484b9093213e427485390a52146428485790ab215242dc859906f20d640dc819903f207640bc816902b2052405880a104f2096415c8299047208a410c8209007200a4018802145f08b610fc21e843b0872109c2128423084210dc219841f0836113c22583ff07f6101c2018) else (0x137226644c487390e621c8445c88b11152228444c883110421dc43b087b90f521ec43d08799247248a490c920924f249a495c9299237246648c4907920b242e484c9039205240648048ff11fc23ae47548eb11d423ce47948f191bf2376469c8d191a1235e46ac8c7918b22fe45ec8b3916522cc45dc8ba9)) else (if b<3 then (0x397272a4e4c9c893a727464edc9da93b327624dbc9b6936b26d24efc9de93bb27724f3c9e5937726ea4dcc9b893e9065e4cac99f933b263e4c6c9a7934b25be4b6c97392e525c64b8496392c525864b0497b92f325de4bb497592e9259e4b3496592c926120c2013b9273251e4a2c94b9293228e450c8a09) else (if b<4 then (0x1fc43aa87590ea21e5445248a08d0a1c9239045950b3217543324660846a089413a8295050a0a941b24360816a029402c8051022a041400a8019002207920f0517ca2d943f287a50eca1c9427284a508ca109437286a50cca18941f283a506ca0c944f28964ffc9fd940728064e3c9c6938b27124f7c9ed9) else (0x3bd47728dd51b8a3e727d24cbd195a33f46768c7d18da34f46968d5c972a2e1458a8b05176a2e9459a8b25184930826024c0093ba273451e8a2d14ba293456e4ad895792ae228284c50ac915821cc839108b21154228841908220ee41d883d507b20f4425244a0922a241449a88c51349268240a88050ff2)))) else (if b<7 then (if b<6 then (0x5310a7e14f42a385430a2e144c287050c09de13ac27b84f309ce139427184e109ae0ad9957335746108c0115ba2b6455e8ab90ac20e46228c41187630f4625089a10fe31d4645087210cc20d84028c01183c243d48729095210a4354862907520ca3ff47f6901d201a38d47128e551c8a3b547628db51b4a) else (0x4a329425324264048f291651b8a36146728ca5190a3b947628ea51d0a3994990930155ca9b95352a6654c4a9f953d2a8e550cab485680a2e544ca87150c29de53aca7b94f329ce5394a7194e129ae5358a6a15290a5012fc25384a30942123c245846e08d8119c23b847608ea11d023985570a6e14d42998)) else (if b<8 then (0x97112ce16e1ade35c06b7096f12e024c848d8d191a3a34984ad09431a6a35284b5e96ad2bfa57b4b0e960d2cba5934b7056f0ae014a149925320a37246c48ca919123b247548e89264a4c15354a6294f52b495682a1c9431272a4e149ac935129495282b5e56acabf957b2b0e560cacb95932b7012fca539) else (if b<9 then (0xa6514c8298c5310a6114c029bc5370a6b14d429a45340a7714ec29cc5390a17142a284c5088a1f143a286c5138a2313ee27d84f989f2138e270c4d789ab136e26cc4d389a5134626844cf099c13be27784ed89da13ce27984f189e213ae27584ea89d413a627484e889d012fe25ec4c3898312ee25d44b98) else (0x8140fee1fd4403880510061cfc39d875f0ebc1d6c3ad074f0e9c1d343a607430e841c5c38987110e4e1c8c347868b0d5e1ab835586aa0d361a6834c86980d2e1a5832b06540c9c193033b86730c8e191433386660cca19903318a87150c2a0c5410a5714a628dc51a8a33146228fc51d8a47148a299c5330))))) else (if b<15 then (if b<12 then (if b<11 then (0xb97172a2e4c5c88b7716ea2dd85ba0b8f171a2e2c5af8b5b168e2d145a18947128c250c4a10907120a240c4808917122a243c485892f125c24b44960923124424dc49b0933126423dc47988f110ce21984318862106e20cc417882b104e20944118821109621284248848108e211842b885610a6214840b0) else (0xcf319e233fc67e8d071a06339c6718ce119ae33546698cd119be336c6638cc31982327c64e8c9b1932329c6518c97192a324c6488c8e1918319c6328c6618c831dc63a8c73189e312c6238c451886310461f0c3c184e30946118c0718062fbc5f58be917ee2fd45f98bf117be2f6c5e38bc317822e9c5d18)) else (if b<13 then (0xdca1bae37586e98dd21b0e360c6d78dab1b3e366c6a78d4b1aae35586a98d521ade35b86b58d6a1abe35786ad8d5a1a4e348c69f8d3b164e2c985918b2116442c805838b0316022c5c5898b11154e2b9c5730ae515c82b8c5710ade15b82ab85560ab7156c2ad455a0ab3158e2b145630ac4158633dc67a8) else (if b<14 then (0xa6934d069d8d391a16342a6850d091a1134206878d0e9a1c34346898d111a99153027d8cf919c533826694cd0999e33386778ced19e633c46758cea99d433a46744ce8197e32f46618cc1197632ea65d0cb9197132e06594cb31964341228206db8db31b8e37186e18dc21b2e36546c98d911b9e37386e58) else (0x7212ed21b7cb6d96f72de65bbcb7696e32dc45b1cb6196c12d5c5aa8b4d16992d305a58b2b16542c9c5930b3a96712c8c5914b2216662cca5990b5c860f2c16589cb11961b2c32585cb0b15ee2bd85778aee15f72bec57d4afa15f3350c6a08d2a9a51346a68c4d229a6634ca6990d311a6134c069b8d351)))) else (if b<17 then (if b<16 then (0x8df31bc636cc4f989d31366264c5398a3317e62f4c5998b2319e632cc47988b31126198c31183530626094c10984a30926120c23185630a46058c0a17f62fea5fd0c0298790fbe5f6cbd397a32f3e5e74bcd97992f765ee4bdb97b62f9e5f2cbc317842efe5df4bbd975e2eb45d38ba6974c2e845c44b929) else (0xcd139be736ce639cc339827274e4c9c9539227238e461c6538cc7190e3a9cb9189e712ce239c4538867104e1f1c3c384e7094e119c5917d26fd4df89c1917be6f6cde39bc337826e54dc89b7536ec6dd0dc69bb916be6d6cda39b4536866da44a31942320a6404c8a992e325a64b0c911936326463c4cac8)) else (if b<18 then (0xdc93bac7748ec29d843b027600ed69da93b3a7664eab1d523adc75a8eaf1d5d3ab47564e929d243a427480e9e9d393ae62c98d909b2236406c18d809b0236006c44d9c8b38154c6a90d731ae535c86b88d6f1adc355c6ab0d5b1ab535686ac8d629ac635886be457c0cf539e273f4e709d1919ae7354e699) else (if b<19 then (0xbc156e8ad155b4992c51bca27544ca8bd5164a225474984850289fd13cea7994f729ed93c327844efa9fa4ba626ed4dc49b0538496984ca8993132226644c3298592f725ec4bbc97712fb25f54be898e4d322a6054d0a8515082a1c553066714ea29d052e8a5c14b22a083b8c7708eca9d913b9c7734ee51) else (0x30f1bc235ec6bb8d7d1ec22d805a48b4815902b0056706a915722adc5558aad15622af839aab345660ac8c58c8b115620ac3e5878b09562c9)))))) 15 i
def r2 (i : Nat) :=
  let x := r2V i
  (x &&& 127) ||| ((r2D0 ((x >>> 7) &&& 255)) <<< 7)

def hit2 (t : Nat) (v : List Sig) := OrbitLookup2153.orbitHit 8 1246 3093 1024 o2 f2 r2 rot 2 t v

def hintIndex (i : Nat) := field (fun b => if b<10 then (if b<5 then (if b<2 then (if b<1 then (0x22000000000680260000004000002600011000129348452802234c004a4d2114a088933e5cc008e3470e121070e0e0d089421e189880e104) else (0x3a032013190400999006402600640131c3908d1c380131c8438e00949aa004c6a00038c0200a801300007211239080003800e2e09480)) else (if b<3 then (0x4a0099300004024a009934a1c408264c4004a009931000008004c00800000060490011229048600183112290011221808000180060000000) else (if b<4 then (0x6010000249890408b82001c8801a0010000000001a60002265cc000e2638d1c384841c3838343004894314387862620384109934a34400) else (0x104c01300200001000980100040200444862200886020000000180060018080000038000640190400c803200019002468e1a3838204006a0)))) else (if b<7 then (if b<6 then (0x4000001e00016008c8221e8c00f04780801004006020000000000000034100004c11100000091c107038026287880e10426340130400987) else (0x100000000a803a500222a0000e040c000000010000007800000016008c8221e8c00f0478b00061000000100002a00ea22a0000e0000000)) else (if b<8 then (0x47c0c8920644900000000600000091850f0c3c6411806449080001500500150000103000800000580000458003091850f0c3c6411804000) else (if b<9 then (0x49c000000000026100000000883000000200009802200000000002526908a500446980094c130890b910694c024e4419308949a42294011) else (0x6a74a257638000049d700046810e363c00012f0700000871d504419106081176a5daa11c74a242eeda8e0000000000000000340130000000))))) else (if b<15 then (if b<12 then (if b<11 then (0x1cad9001c5c11a5200880008800f049d700000000d7800013046810e38401275c000000e0871d50847252695d8e1a4c21308081021c75418) else (0x423470e004c7210e393af0a0098e5e0c72b6401293540098d40007180469500268c8230040296008c010000072112387215e0000e5e10000)) else (if b<13 then (0x8216b1169443d249498000181a42e196301818b9106903242200000000000000080000e81319049c9843200c804c640002698019004c70e) else (if b<14 then (0x3000000004cc00000240070000000000000d3000c042e0cc024e0c9843024b8730000070424b98001c4800020225304c9a50e20c13) else (0x6cf80000400102363c0001239403220c1176a5daba1c5ca342eeda82000011d22441022e00b80485c0001c00000000068000093800000004)))) else (if b<17 then (if b<16 then (0x4000000000680260811c2008000001c7287439d8d084c2021ca0c353051a3b0408ea5269400e1a4c9820408e98009400e4e00d021c3c480) else (0xa0098e5e0d58000350003008d00128c8230040296008c010082472f040000e5e115802e08d000e00022003c1a7000068034087104e003bf)) else (if b<18 then (0x26b45b900204806e009832eb06170c0c8b800183802200000000000200cc3800064019049c21900640190000480320048d1c3470704393af) else (if b<19 then (0x8680031c0000d044038008d5a001a4c118000010e043c48006d5ab46a44117005c01700001270000033000002708004801210c130e60404) else (0x1200380660002700000001a9c28300680052c00004)))))) 7 i
def hintVal (i : Nat) := field (fun b => if b<1 then (0x28e0e8014703400a283a00514050024e0280125014009183a0048c0d002420e80121014008280a0040c050020202800c5014006183a0030c0d0014a02800a3014005083a002840d00142028008507c004281c00214050010202800650e0003283e001940e000ca0380065018003280a0018c1f000c60700063018003180a001841f000c2070006101400218700010c1f00086070004301c002180c0010c05000820f80041074002081c001040700082030004101400108700008437000421b00021080001083e000841d0004207000210340010810000840700042030002101400000020000000) else (0x200024e300012594502522228109b103034b28181a414041d2da020c90d01054b48082a42)) 29 i
def hint (i : Nat) := hintVal (hintIndex i)

def ok2 (i : Nat) :=
  let t := r2 i &&& 7
  let v := replay basis 2 (r2 i >>> 3)
  decide v.Nodup && (MinorHubAdapter2153.short 2 2 (r2 i >>> 3) (hint i) || !jump marks 7 (fun t w => !(hit5 t w)) 3 t v)

end Num81

open Search2153 Cache2153

namespace Num81

def Transport := ∀ g < 8, ∀ depth code k t,
  Marked2153.Impossible marks k t (replay basis depth code) →
    Marked2153.Impossible marks k t (replay (rot g) depth code)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H5_0 : span ok5 128 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H5_1 : span ok5 128 128 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H5_2 : span ok5 128 256 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H5_3 : span ok5 128 384 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H5_4 : span ok5 128 512 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H5_5 : span ok5 128 640 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H5_6 : span ok5 128 768 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H5_7 : span ok5 62 896 := by decide +kernel

theorem all5 : span ok5 958 0 := (spanJoin ok5 512 0 446 (spanJoin ok5 256 0 256 (spanJoin ok5 128 0 128 H5_0 H5_1) (spanJoin ok5 128 256 128 H5_2 H5_3)) (spanJoin ok5 256 512 190 (spanJoin ok5 128 512 128 H5_4 H5_5) (spanJoin ok5 128 768 62 H5_6 H5_7)))

theorem proofs5 (i : Nat) (hi : i < 958) :
    Marked2153.Impossible marks 7 (r5 i &&& 7) (replay basis 5 (r5 i >>> 3)) := by
  have hh := spanAt all5 (Nat.zero_le i) (by simpa using hi)
  obtain ⟨hd,hc⟩ := Bool.and_eq_true_iff.mp hh
  exact jumpSound (bottom := 5) (stop := (fun _ _ => true)) (by intro t w hn h; cases h) 2 _ _
      (of_decide_eq_true hd) (by simpa only [Bool.not_eq_true'] using hc)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_0 : span ok2 42 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_1 : span ok2 19 42 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_2 : span ok2 22 61 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_3 : span ok2 21 83 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_4 : span ok2 11 104 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_5 : span ok2 7 115 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_6 : span ok2 13 122 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_7 : span ok2 24 135 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_8 : span ok2 33 159 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_9 : span ok2 46 192 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_10 : span ok2 35 238 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_11 : span ok2 14 273 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_12 : span ok2 21 287 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_13 : span ok2 34 308 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_14 : span ok2 15 342 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_15 : span ok2 18 357 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_16 : span ok2 2 375 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_17 : span ok2 4 377 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_18 : span ok2 5 381 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_19 : span ok2 4 386 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_20 : span ok2 4 390 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_21 : span ok2 2 394 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_22 : span ok2 1 396 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_23 : span ok2 7 397 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_24 : span ok2 13 404 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_25 : span ok2 3 417 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_26 : span ok2 9 420 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_27 : span ok2 8 429 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_28 : span ok2 5 437 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_29 : span ok2 2 442 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_30 : span ok2 21 444 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_31 : span ok2 12 465 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_32 : span ok2 20 477 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_33 : span ok2 32 497 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_34 : span ok2 10 529 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_35 : span ok2 8 539 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_36 : span ok2 7 547 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_37 : span ok2 10 554 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_38 : span ok2 6 564 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_39 : span ok2 8 570 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_40 : span ok2 10 578 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_41 : span ok2 27 588 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_42 : span ok2 13 615 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_43 : span ok2 38 628 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_44 : span ok2 18 666 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_45 : span ok2 7 684 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_46 : span ok2 3 691 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_47 : span ok2 15 694 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_48 : span ok2 9 709 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_49 : span ok2 5 718 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_50 : span ok2 4 723 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_51 : span ok2 11 727 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_52 : span ok2 8 738 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_53 : span ok2 17 746 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_54 : span ok2 10 763 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_55 : span ok2 4 773 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_56 : span ok2 3 777 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_57 : span ok2 2 780 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_58 : span ok2 15 782 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_59 : span ok2 22 797 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_60 : span ok2 37 819 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_61 : span ok2 22 856 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_62 : span ok2 16 878 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_63 : span ok2 18 894 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_64 : span ok2 6 912 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_65 : span ok2 9 918 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_66 : span ok2 42 927 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_67 : span ok2 30 969 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_68 : span ok2 36 999 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_69 : span ok2 24 1035 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_70 : span ok2 13 1059 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_71 : span ok2 28 1072 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_72 : span ok2 9 1100 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_73 : span ok2 19 1109 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_74 : span ok2 42 1128 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_75 : span ok2 43 1170 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_76 : span ok2 30 1213 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem H2_77 : span ok2 3 1243 := by decide +kernel

theorem all2 : span ok2 1246 0 := (spanJoin ok2 570 0 676 (spanJoin ok2 386 0 184 (spanJoin ok2 192 0 194 (spanJoin ok2 104 0 88 (spanJoin ok2 61 0 43 (spanJoin ok2 42 0 19 H2_0 H2_1) (spanJoin ok2 22 61 21 H2_2 H2_3)) (spanJoin ok2 18 104 70 (spanJoin ok2 11 104 7 H2_4 H2_5) (spanJoin ok2 13 122 57 H2_6 (spanJoin ok2 24 135 33 H2_7 H2_8)))) (spanJoin ok2 150 192 44 (spanJoin ok2 81 192 69 (spanJoin ok2 46 192 35 H2_9 H2_10) (spanJoin ok2 14 273 55 H2_11 (spanJoin ok2 21 287 34 H2_12 H2_13))) (spanJoin ok2 33 342 11 (spanJoin ok2 15 342 18 H2_14 H2_15) (spanJoin ok2 2 375 9 H2_16 (spanJoin ok2 4 377 5 H2_17 H2_18))))) (spanJoin ok2 56 386 128 (spanJoin ok2 18 386 38 (spanJoin ok2 8 386 10 (spanJoin ok2 4 386 4 H2_19 H2_20) (spanJoin ok2 2 394 8 H2_21 (spanJoin ok2 1 396 7 H2_22 H2_23))) (spanJoin ok2 16 404 22 (spanJoin ok2 13 404 3 H2_24 H2_25) (spanJoin ok2 9 420 13 H2_26 (spanJoin ok2 8 429 5 H2_27 H2_28)))) (spanJoin ok2 87 442 41 (spanJoin ok2 23 442 64 (spanJoin ok2 2 442 21 H2_29 H2_30) (spanJoin ok2 12 465 52 H2_31 (spanJoin ok2 20 477 32 H2_32 H2_33))) (spanJoin ok2 18 529 23 (spanJoin ok2 10 529 8 H2_34 H2_35) (spanJoin ok2 7 547 16 H2_36 (spanJoin ok2 10 554 6 H2_37 H2_38)))))) (spanJoin ok2 212 570 464 (spanJoin ok2 139 570 73 (spanJoin ok2 58 570 81 (spanJoin ok2 18 570 40 (spanJoin ok2 8 570 10 H2_39 H2_40) (spanJoin ok2 27 588 13 H2_41 H2_42)) (spanJoin ok2 56 628 25 (spanJoin ok2 38 628 18 H2_43 H2_44) (spanJoin ok2 7 684 18 H2_45 (spanJoin ok2 3 691 15 H2_46 H2_47)))) (spanJoin ok2 37 709 36 (spanJoin ok2 14 709 23 (spanJoin ok2 9 709 5 H2_48 H2_49) (spanJoin ok2 4 723 19 H2_50 (spanJoin ok2 11 727 8 H2_51 H2_52))) (spanJoin ok2 27 746 9 (spanJoin ok2 17 746 10 H2_53 H2_54) (spanJoin ok2 4 773 5 H2_55 (spanJoin ok2 3 777 2 H2_56 H2_57))))) (spanJoin ok2 217 782 247 (spanJoin ok2 112 782 105 (spanJoin ok2 37 782 75 (spanJoin ok2 15 782 22 H2_58 H2_59) (spanJoin ok2 37 819 38 H2_60 (spanJoin ok2 22 856 16 H2_61 H2_62))) (spanJoin ok2 24 894 81 (spanJoin ok2 18 894 6 H2_63 H2_64) (spanJoin ok2 9 918 72 H2_65 (spanJoin ok2 42 927 30 H2_66 H2_67)))) (spanJoin ok2 110 999 137 (spanJoin ok2 60 999 50 (spanJoin ok2 36 999 24 H2_68 H2_69) (spanJoin ok2 13 1059 37 H2_70 (spanJoin ok2 28 1072 9 H2_71 H2_72))) (spanJoin ok2 61 1109 76 (spanJoin ok2 19 1109 42 H2_73 H2_74) (spanJoin ok2 43 1170 33 H2_75 (spanJoin ok2 30 1213 3 H2_76 H2_77)))))))

theorem proofs2 (prior : MinorHubAdapter2153.Prior 2) (T : Transport) (i : Nat) (hi : i < 1246) :
    Marked2153.Impossible marks 10 (r2 i &&& 7) (replay basis 2 (r2 i >>> 3)) := by
  have hh := spanAt all2 (Nat.zero_le i) (by simpa using hi)
  obtain ⟨hd,hc⟩ := Bool.and_eq_true_iff.mp hh
  rcases Bool.or_eq_true_iff.mp hc with easy | hard
  · exact MinorHubAdapter2153.sound 2 2 (r2 i >>> 3) (hint i) (r2 i &&& 7) prior (of_decide_eq_true hd) easy
  · exact jumpSound (bottom := 7) (stop := (fun t w => !(hit5 t w))) (by intro t w hn h; exact OrbitLookup2153.hitSound (proofs := proofs5) (transport := fun g hg c q v => T g hg 5 c _ q v) (by simpa only [hit5,Bool.not_eq_false'] using h)) 3 _ _
        (of_decide_eq_true hd) (by simpa only [Bool.not_eq_true'] using hard)
end Num81

open Search2153 Cache2153 RootGlue2153

namespace Num81

def startOk (c t : Nat) :=
  let v := basis c
  !(decide (t ≤ 12+1-v.length) && unionSep (decide (0<t)) v == top) ||
    !jump marks 10 (fun q w => !(hit2 q w)) 2 t v

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem root3 : span (startOk 3) 13 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem root4 : span (startOk 4) 13 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem root5 : span (startOk 5) 13 0 = true := by decide +kernel

theorem solveCodeWith (prior : MinorHubAdapter2153.Prior 2) (T : Transport) (c : Nat) (ne : 0 < (basis c).length) (nd : (basis c).Nodup) (checked : span (startOk c) 13 0 = true) :
    AtBase marks 12 (basis c) := by
  intro t ht hv
  have hh := spanAt checked (Nat.zero_le t) (by omega)
  have h : jump marks 10 (fun q w => !(hit2 q w)) 2 t (basis c) = false := by simpa only [startOk,decide_eq_true ht,hv,beq_self_eq_true,Bool.true_and,Bool.not_true,Bool.false_or,Bool.not_eq_true'] using hh
  apply jumpSound (bottom := 10) (stop := fun q w => !(hit2 q w)) (by intro q w hn he; exact OrbitLookup2153.hitSound (proofs := proofs2 prior T) (transport := fun g hg c q h => T g hg 2 c _ q h) (by simpa only [hit2,Bool.not_eq_false'] using he)) 2 t (basis c) nd h

abbrev solveCode (prior : Projection2153.ThetaNumeric) := solveCodeWith prior (OrbitCache2153.sound 2)

end Num81

namespace Finish2153
open Search2153 Cache2153 Projection2153 Root2153 ThetaSym2153 RootGlue2153
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seven
    : ThreeNumeric := by
  apply theta_from_bases
  intro j hj f
  rw [flat_eq]
  rcases hj with rfl | rfl | rfl
  · fin_cases f
    · exact Num70.solveCode 0 (by decide +kernel) (by decide +kernel) Num70.root0
    · exact Num70.solveCode 1 (by decide +kernel) (by decide +kernel) Num70.root1
    · exact Num70.solveCode 2 (by decide +kernel) (by decide +kernel) Num70.root2
  · fin_cases f
    · exact Num70.solveCode 6 (by decide +kernel) (by decide +kernel) Num70.root6
    · exact Num70.solveCode 7 (by decide +kernel) (by decide +kernel) Num70.root7
    · exact Num70.solveCode 8 (by decide +kernel) (by decide +kernel) Num70.root8
  · fin_cases f
    · exact Num70.solveCode 9 (by decide +kernel) (by decide +kernel) Num70.root9
    · exact Num70.solveCode 10 (by decide +kernel) (by decide +kernel) Num70.root10
    · exact Num70.solveCode 11 (by decide +kernel) (by decide +kernel) Num70.root11
set_option maxRecDepth 20000 in
theorem eight
    : EightNumeric := by
  apply eight_from_bases
  · exact Num80.solveCode (ThetaSym2153.three_suffice seven) 0 (by decide +kernel) (by decide +kernel) Num80.root0
  · exact Num81.solveCode (ThetaSym2153.three_suffice seven) 3 (by decide +kernel) (by decide +kernel) Num81.root3
  · exact Num81.solveCode (ThetaSym2153.three_suffice seven) 4 (by decide +kernel) (by decide +kernel) Num81.root4
  · exact Num81.solveCode (ThetaSym2153.three_suffice seven) 5 (by decide +kernel) (by decide +kernel) Num81.root5
end Finish2153

end PEqualNP.Outside.L_meta_2153_aux

open PEqualNP.Outside.L_meta_2153_aux

theorem PEqualNP.Outside.L_meta_2153 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → (16 : ℕ) ≤ x1.size :=
  FinalBridge2153.combined (Finish2153.seven) (Finish2153.eight)
