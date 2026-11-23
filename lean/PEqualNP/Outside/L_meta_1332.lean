import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1332

open PEqualNP.CircuitLowerBounds

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


inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
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
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
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

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

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
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
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


def isAO : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

def isNt : GateOp → Bool
  | GateOp.not => true
  | _ => false

def two (g : Gate) : Bool := isAO g.op && decide (g.inputs.length = 2)

theorem two_iff (g : Gate) :
    two g = true ↔ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp [two, isAO]

theorem isNt_iff (op : GateOp) : isNt op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNt]

theorem simplify_two (op : GateOp) (m : ℕ) (ins : List Stat) (gt : Gate)
    (h : gt ∈ (simplify op m ins).1) (ht : two gt = true) :
    isAO op = true ∧ ins.length = 2 := by
  cases op <;> simp only [simplify] at h
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at h <;> (subst h; simp [two, isAO] at ht ⊢)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at h <;> (subst h; simp [two, isAO] at ht ⊢)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at h <;> (subst h; simp [two, isAO] at ht ⊢)
  · simp at h
  · simp at h

theorem simplify_nt (op : GateOp) (m : ℕ) (ins : List Stat) (gt : Gate)
    (h : gt ∈ (simplify op m ins).1) (ht : isNt gt.op = true) : isNt op = true := by
  cases op <;> simp only [simplify] at h
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at h <;> (subst h; simp [isNt] at ht)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at h <;> (subst h; simp [isNt] at ht)
  · simp [isNt]
  · simp at h
  · simp at h

theorem elim_two (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → k < acc.1.length →
    (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (elim n gs acc).2.countP two + gs.countP (fun g => two g && decide (k ∈ g.inputs))
      ≤ acc.2.countP two + gs.countP two := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have hgok := hok g List.mem_cons_self
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by
        obtain ⟨c, hc⟩ := hc
        refine ⟨c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
    have hloc : (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList.countP two
        + (if (two g && decide (k ∈ g.inputs)) = true then 1 else 0)
        ≤ (if two g = true then 1 else 0) := by
      set e := (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 with he
      by_cases htg : two g = true
      · have hlen : g.inputs.length = 2 := ((two_iff g).1 htg).2
        by_cases hkg : k ∈ g.inputs
        · obtain ⟨c, hc⟩ := hc
          have hnone : e = none := by
            apply simplify_count
            · rcases ((two_iff g).1 htg).1 with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
            · simp [hlen]
            · intro h; rcases ((two_iff g).1 htg).1 with h' | h' <;> rw [h] at h' <;> cases h'
            · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
          rw [hnone]; simp [htg, hkg]
        · have := List.countP_le_length (p := two) (l := e.toList)
          have h2 := toList_length_le e
          simp [htg, hkg]; omega
      · have : e.toList.countP two = 0 := by
          rw [List.countP_eq_zero]
          intro gt hgt ht
          have := simplify_two g.op _ _ gt (by simpa using hgt) ht
          apply htg
          rw [two]; simp [this.1]
          have := this.2; simpa using this
        simp [htg, this]
    rw [h3, List.countP_cons, List.countP_cons]
    have h2 : (elimStep n acc g).2.countP two = acc.2.countP two +
        (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList.countP two := by
      simp only [elimStep, List.countP_append]
    rw [h2] at h1
    split_ifs at hloc ⊢ <;> omega

theorem elim_nt (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.countP (fun g => isNt g.op) ≤ acc.2.countP (fun g => isNt g.op)
      + gs.countP (fun g => isNt g.op) := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have h1 := ih (elimStep n acc g)
    have hloc : (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList.countP
          (fun g => isNt g.op) ≤ (if isNt g.op = true then 1 else 0) := by
      set e := (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 with he
      by_cases htg : isNt g.op = true
      · have := List.countP_le_length (p := fun g : Gate => isNt g.op) (l := e.toList)
        have h2 := toList_length_le e
        simp [htg]; omega
      · have : e.toList.countP (fun g => isNt g.op) = 0 := by
          rw [List.countP_eq_zero]
          intro gt hgt ht
          exact htg (simplify_nt g.op _ _ gt (by simpa using hgt) ht)
        simp [htg, this]
    rw [h3, List.countP_cons]
    have h2 : (elimStep n acc g).2.countP (fun g => isNt g.op) = acc.2.countP (fun g => isNt g.op) +
        (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList.countP
          (fun g => isNt g.op) := by
      simp only [elimStep, List.countP_append]
    rw [h2] at h1
    split_ifs at hloc ⊢ <;> omega

theorem card_filter_get (l : List Gate) (f : Gate → Bool) :
    (Finset.univ.filter (fun q : Fin l.length => f (l.get q) = true)).card = l.countP f := by
  induction l with
  | nil => simp
  | cons g l ih =>
    rw [Finset.card_filter]
    refine (Fin.sum_univ_succ (n := l.length)
      (f := fun i => if f ((g :: l).get i) = true then 1 else 0)).trans ?_
    rw [Finset.card_filter] at ih
    simp only [List.get_eq_getElem, Fin.val_zero, Fin.val_succ, List.getElem_cons_zero,
      List.getElem_cons_succ] at ih ⊢
    rw [List.countP_cons, ← ih]
    exact Nat.add_comm _ _

def initStatsP (n : ℕ) (p : Fin n) : List Stat :=
  List.ofFn (fun i : Fin n => if i = p then Stat.const false else Stat.wire i)

theorem initStatsP_len (n : ℕ) (p : Fin n) : (initStatsP n p).length = n := by
  simp [initStatsP]

theorem inv_initP (n : ℕ) (p : Fin n) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn (Function.update x p false)) (initStatsP n p, []) := by
  refine ⟨by simp [initStatsP], ?_⟩
  intro i
  by_cases hlt : i < n
  · by_cases hip : i = p.val
    · have hp : (⟨i, hlt⟩ : Fin n) = p := Fin.ext hip
      simp [initStatsP, hlt, hp, Stat.Valid, Stat.val, wiresFrom]
    · have hp : (⟨i, hlt⟩ : Fin n) ≠ p := fun e => hip (by simpa using congrArg Fin.val e)
      simp [initStatsP, hlt, hp, Stat.Valid, Stat.val, wiresFrom, Function.update_of_ne hp]
  · rw [List.getD_eq_default _ _ (by simp [initStatsP]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem initStatsP_p (n : ℕ) (p : Fin n) :
    (initStatsP n p).getD p.val (Stat.const false) = Stat.const false := by
  simp [initStatsP]

def outIdx (L : ℕ) : Stat → ℕ
  | Stat.const false => L
  | Stat.const true => L + 1
  | Stat.wire j => j

theorem outIdx_val (W : List Bool) (s : Stat) (hs : s.Valid W.length) :
    (W ++ [false, true]).getD (outIdx W.length s) false = s.val W := by
  cases s with
  | const c => cases c <;> simp [outIdx, Stat.val]
  | wire j =>
    simp only [outIdx, Stat.val]
    exact List.getD_append _ _ _ _ hs

theorem exists_kappa (L t : ℕ) (hL : 0 < L) (N : Finset (Fin L)) (hN : N.card ≤ t) :
    ∃ κ : Fin t → Fin L, ∀ q ∈ N, ∃ r, κ r = q := by
  classical
  let e := N.equivFin
  refine ⟨fun r => if h : r.val < N.card then (e.symm ⟨r.val, h⟩).1 else ⟨0, hL⟩, ?_⟩
  intro q hq
  have hlt : (e ⟨q, hq⟩).val < t := lt_of_lt_of_le (e ⟨q, hq⟩).isLt hN
  refine ⟨⟨(e ⟨q, hq⟩).val, hlt⟩, ?_⟩
  simp

theorem two_le_countP (l : List Gate) (f : Gate → Bool) (a b : Fin l.length) (hab : a ≠ b)
    (ha : f (l.get a) = true) (hb : f (l.get b) = true) : 2 ≤ l.countP f := by
  rw [← card_filter_get]
  have : ({a, b} : Finset (Fin l.length)) ⊆ Finset.univ.filter (fun q => f (l.get q) = true) := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · simpa using ha
    · simpa using hb
  have := Finset.card_le_card this
  rwa [Finset.card_pair hab] at this

theorem main : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ p : Fin n, (∃ i0 : Fin m, p ∈ S i0 ∧ ∃ v0 ∈ S i0, v0 ≠ p) → ∀ a b : Fin gates.length, a ≠ b → ((gates.get a).op = GateOp.and ∨ (gates.get a).op = GateOp.or) → (gates.get a).inputs.length = 2 → p.val ∈ (gates.get a).inputs → ((gates.get b).op = GateOp.and ∨ (gates.get b).op = GateOp.or) → (gates.get b).inputs.length = 2 → p.val ∈ (gates.get b).inputs → ∀ (t : ℕ) (ι : Fin t → Fin gates.length), (∀ q : Fin gates.length, (gates.get q).op = GateOp.not → ∃ r : Fin t, ι r = q) → ∀ I : Finset (Fin gates.length), (∀ q2 : Fin gates.length, ((gates.get q2).op = GateOp.and ∨ (gates.get q2).op = GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) → ∃ (gl : List Gate) (ol : Fin m → ℕ) (κ : Fin t → Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = GateOp.not → ∃ r2 : Fin t, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = GateOp.and ∨ (gl.get q4).op = GateOp.or) ∧ (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧ J.card + 2 ≤ I.card ∧ ∀ (o2 : Fin m) (x2 : Fin n → Bool), Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, v2 ≠ p ∧ x2 v2 = true) := by
  intro n m S hS gates out hok hev p hp a b hab ha1 ha2 ha3 hb1 hb2 hb3 t ι hι I hI
  have hOk : ∀ g ∈ gates, Ok g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hok g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  have hinv : ∀ x : Fin n → Bool, Inv n (List.ofFn x)
      (wiresFrom gates (List.ofFn (Function.update x p false)))
      (elim n gates (initStatsP n p, [])) := fun x =>
    inv_elim n _ (by simp) gates _ _ hOk (inv_initP n p x)
  generalize hacc : elim n gates (initStatsP n p, []) = acc at hinv
  have hE1 := elim_two n p.val gates (initStatsP n p, []) hOk (by simp [initStatsP_len])
    ⟨false, initStatsP_p n p⟩
  have hE2 := elim_nt n gates (initStatsP n p, [])
  have hE3 := elim_ok n gates (initStatsP n p, []) (by simp)
  rw [hacc] at hE1 hE2 hE3
  simp only [List.countP_nil, zero_add] at hE1 hE2
  let gl : List Gate := acc.2 ++ [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩]
  have hgl_len : gl.length = acc.2.length + 2 := by simp [gl]
  let ol : Fin m → ℕ := fun o => outIdx (n + acc.2.length) (acc.1.getD (out o) (Stat.const false))
  have hout : ∀ (o : Fin m) (x2 : Fin n → Bool),
      Circuit.eval ⟨gl, ol o⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o, v2 ≠ p ∧ x2 v2 = true) := by
    intro o x2
    have hW : wiresFrom gl (List.ofFn x2) = wiresFrom acc.2 (List.ofFn x2) ++ [false, true] := by
      simp only [gl, wiresFrom_append]
      simp [wiresFrom, GateOp.eval]
    have hlen : (wiresFrom acc.2 (List.ofFn x2)).length = n + acc.2.length := by
      rw [length_wiresFrom]; simp
    have hi := hinv x2
    have hv := (hi.2 (out o)).1
    have hval := (hi.2 (out o)).2
    show (wiresFrom gl (List.ofFn x2)).getD (ol o) false = _
    have hol : ol o = outIdx (wiresFrom acc.2 (List.ofFn x2)).length
        (acc.1.getD (out o) (Stat.const false)) := by simp only [ol, hlen]
    rw [hW, hol, outIdx_val _ _ (by rw [hlen]; exact hv), hval]
    have := hev o (Function.update x2 p false)
    have e2 : (wiresFrom gates (List.ofFn (Function.update x2 p false))).getD (out o) false
        = Circuit.eval ⟨gates, out o⟩ (List.ofFn (Function.update x2 p false)) := rfl
    rw [e2, this]
    apply decide_eq_decide.2
    simp [Function.update_apply, and_comm]
  have hNtG : gates.countP (fun g => isNt g.op) ≤ t := by
    rw [← card_filter_get gates (fun g => isNt g.op)]
    refine le_trans (Finset.card_le_card (t := Finset.univ.image ι) ?_) (Finset.card_image_le.trans (by simp))
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨r, hr⟩ := hι q ((isNt_iff _).1 hq.2)
    exact Finset.mem_image.2 ⟨r, Finset.mem_univ _, hr⟩
  have hNtL : gl.countP (fun g => isNt g.op) ≤ t := by
    simp only [gl, List.countP_append]
    have : ([(⟨GateOp.or, []⟩ : Gate), ⟨GateOp.and, []⟩]).countP (fun g => isNt g.op) = 0 := by
      simp [isNt]
    omega
  obtain ⟨κ, hκ⟩ := exists_kappa gl.length t (by omega)
    (Finset.univ.filter fun q : Fin gl.length => isNt (gl.get q).op = true)
    (by rw [card_filter_get gl (fun g => isNt g.op)]; exact hNtL)
  have h2 := two_le_countP gates (fun g => two g && decide (p.val ∈ g.inputs)) a b hab
    (by rw [Bool.and_eq_true]; exact ⟨(two_iff _).2 ⟨ha1, ha2⟩, decide_eq_true ha3⟩)
    (by rw [Bool.and_eq_true]; exact ⟨(two_iff _).2 ⟨hb1, hb2⟩, decide_eq_true hb3⟩)
  have hIc : gates.countP two ≤ I.card := by
    rw [← card_filter_get gates two]
    apply Finset.card_le_card
    intro q hq
    rw [Finset.mem_filter] at hq
    exact hI q ((two_iff _).1 hq.2)
  have hgc : gl.countP two = acc.2.countP two := by
    simp only [gl, List.countP_append]
    have : ([(⟨GateOp.or, []⟩ : Gate), ⟨GateOp.and, []⟩]).countP two = 0 := by
      simp [two, isAO]
    omega
  refine ⟨gl, ol, κ, Finset.univ.filter fun q : Fin gl.length => two (gl.get q) = true,
    ?_, ?_, ?_, ?_, hout⟩
  · intro h hh
    rcases List.mem_append.1 hh with h1 | h1
    · obtain ⟨c1, c2⟩ := hE3 h h1
      exact ⟨by simpa using c1, c2⟩
    · simp at h1
      rcases h1 with rfl | rfl <;> simp
  · intro q3 hq3
    exact hκ q3 (Finset.mem_filter.2 ⟨Finset.mem_univ _, (isNt_iff _).2 hq3⟩)
  · intro q4 hq4
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (two_iff _).2 hq4⟩
  · rw [card_filter_get gl two, hgc]
    omega

end PEqualNP.Outside.L_meta_1332

theorem PEqualNP.Outside.L_meta_1332 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ p : Fin n, (∃ i0 : Fin m, p ∈ S i0 ∧ ∃ v0 ∈ S i0, v0 ≠ p) → ∀ a b : Fin gates.length, a ≠ b → ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (gates.get a).inputs.length = 2 → p.val ∈ (gates.get a).inputs → ((gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (gates.get b).inputs.length = 2 → p.val ∈ (gates.get b).inputs → ∀ (t : ℕ) (ι : Fin t → Fin gates.length), (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin t, ι r = q) → ∀ I : Finset (Fin gates.length), (∀ q2 : Fin gates.length, ((gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) → ∃ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin m → ℕ) (κ : Fin t → Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r2 : Fin t, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧ J.card + 2 ≤ I.card ∧ ∀ (o2 : Fin m) (x2 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, v2 ≠ p ∧ x2 v2 = true) := by
  exact PEqualNP.Outside.L_meta_1332.main
