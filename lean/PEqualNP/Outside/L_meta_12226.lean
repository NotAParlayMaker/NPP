import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12226
open _root_.PEqualNP.MetaComplexity _root_.PEqualNP.CircuitLowerBounds
section Source0
namespace SixSigned
inductive Run (mask goal : Nat) : Nat → Nat → Multiset Nat → Prop
  | done {q s} (hit : goal ∈ s) : Run mask goal q 0 s
  | merge {q r a b v rest} (op : v=(a &&& b) ∨ v=(a ||| b))
      (next : Run mask goal q r (v ::ₘ rest)) : Run mask goal q r (a ::ₘ b ::ₘ rest)
  | reuse {q r a b v rest} (op : v=(a &&& b) ∨ v=(a ||| b))
      (next : Run mask goal q r (v ::ₘ a ::ₘ rest)) : Run mask goal (q+1) r (a ::ₘ b ::ₘ rest)
  | both {q r a b v rest} (op : v=(a &&& b) ∨ v=(a ||| b))
      (next : Run mask goal q r (v ::ₘ a ::ₘ b ::ₘ rest)) : Run mask goal (q+2) r (a ::ₘ b ::ₘ rest)
  | flip {q r a rest} (next : Run mask goal q r ((mask ^^^ a) ::ₘ rest)) :
      Run mask goal (q+1) (r+1) (a ::ₘ rest)
  | copyFlip {q r a rest} (next : Run mask goal q r ((mask ^^^ a) ::ₘ a ::ₘ rest)) :
      Run mask goal (q+2) (r+1) (a ::ₘ rest)
end SixSigned
end Source0

section Source1
namespace CoreHelpers
open PEqualNP.CircuitLowerBounds
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
end CoreHelpers
end Source1

section Source2
namespace CoreHelpers
open PEqualNP.CircuitLowerBounds
variable {n : ℕ}
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp
end CoreHelpers
end Source2

section Source3
namespace CoreHelpers
open PEqualNP.CircuitLowerBounds
def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)
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
end CoreHelpers
end Source3

section Source4
namespace CoreHelpers
open PEqualNP.CircuitLowerBounds
theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]
theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega
theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]
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
def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false
theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩
end CoreHelpers
end Source4

section Source5
namespace CoreHelpers
open PEqualNP.CircuitLowerBounds
def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])
def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g
theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk
theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok
theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg
theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h
theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem
def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x
def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)
theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩
theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this
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
def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Stat.const false)
theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Stat.const b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Stat.const false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩
theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]
theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)
theorem const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'
theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Stat.const false) = Stat.const c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Stat.const false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega
theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj
def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Stat.const c
end CoreHelpers
end Source5

section Source6
namespace CoreHelpers
open PEqualNP.CircuitLowerBounds
def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false
theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩
theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm
theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h
theorem agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))
theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h
theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]
theorem drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Stat.const c) (fun y => ⟨trivial, (heq y).symm⟩) hnc
abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y
def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2
def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Stat.const c
theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)
theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Stat.const c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.const c from h] at h1
  exact h1.symm
theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Stat.wire q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.wire q from h] at h1
  exact h1.symm
theorem st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]
theorem simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Stat.const c) : ∃ c, (simplify op t ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
theorem st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩
theorem const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Stat.const (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h
section Scope495
variable {n : ℕ} {gs : List Gate} {o : ℕ}
end Scope495
end CoreHelpers
end Source6

section Source7
namespace CoreHelpers.PermInputs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m
def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩
def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false
theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)
theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]
theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this
end CoreHelpers.PermInputs
end Source7

section Source8
namespace CoreHelpers.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoreHelpers
open CoreHelpers.PermInputs
def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x
def Drop {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (b : Bool) (k s : ℕ) : Prop :=
  ∃ s' : ℕ, s' + k ≤ s ∧ HasCircuitSize m (fun x => f (Function.update x y b)) s'
def RestrNC {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p : Fin m, Dep f p → ∀ b : Bool, ∃ x y : Fin m → Bool,
    f (Function.update x p b) ≠ f (Function.update y p b)
structure Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL m gs
  hev : ∀ x : Fin m → Bool, vl gs x o = f x
  hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
    gs.length ≤ gs'.length
def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs
theorem has_of_clean (k : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL k gs) :
    HasCircuitSize k (fun y => vl gs y o) gs.length := by
  refine ⟨⟨gs, o⟩, ?_, le_refl _, fun y => rfl⟩
  intro g hg
  exact (clean_nok k gs hcl g hg).1
theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw
theorem reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length := by
  obtain ⟨g, hg, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hg).1
theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
theorem vl_not {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (j : ℕ) (hop : g.op = GateOp.not) (hin : g.inputs = [j]) :
    vl gs u (k + q) = !vl gs u j := by
  rw [vl_gate gs hcl u q g hq, hop, hin]
  rfl
theorem exists_least (m : ℕ) (f : (Fin m → Bool) → Bool) (s : ℕ)
    (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (h : HasCircuitSize m f s) :
    ∃ (gs : List Gate) (o : ℕ), Least m f gs o ∧ gs.length ≤ s := by
  classical
  have hc := clean_of m f s hnc h
  have hex : ∃ t, HasClean m f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hev, ?_⟩, by omega⟩
  intro gs' o' hc' he'
  have := Nat.find_min' hex ⟨gs', o', hc', le_refl _, he'⟩
  omega
theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  exact ⟨gs'', o'', hc'', by omega, fun y => by rw [he'' y, hagree y o ho]⟩
section Scope183
variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩
theorem Least.no_const (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (c : Bool) : ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = c := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_const m gs L.hcl o p c hp hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega
theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega
theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega
theorem Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool, ∃ x y : Fin m → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b)) : ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  have hoi : o ≠ i := by
    intro e
    obtain ⟨x, y, hxy⟩ := hnc false
    apply hxy
    rw [← L.hev, ← L.hev, e, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← L.hev, ← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
end Scope183
theorem upd_ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Fin (n + 1) → Bool) :
    Function.update x i b = ins i b (Fin.removeNth i x) :=
  (Fin.insertNth_removeNth i b x).symm
theorem restr_const {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b c : Bool) (h : stF n gs i b o = Stat.const c) (x : Fin (n + 1) → Bool) :
    f (Function.update x i b) = c := by
  rw [upd_ins, ← hev]
  exact st_val_const n gs hcl i b o c h _
theorem save (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) S (by
    intro p hp
    obtain ⟨g, hg, a, ha, c, hc⟩ := hS p hp
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  simp only [List.length_nil, zero_add] at hcount
  cases hst : stF n gs i b o with
  | const c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((restr_const hcl hev i b c hst x).trans (restr_const hcl hev i b c hst y).symm)
  | wire j =>
    have hc : CleanL n (passG n gs i b) :=
      clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
        (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)
    have h2 := relabel_size (Fin.succAbove i) _ _ (has_of_clean n (passG n gs i b) j hc)
    have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i b))
        = fun x => vl (passG n gs i b) (x ∘ Fin.succAbove i) j := by
      funext x
      rw [upd_ins, ← hev, st_val_wire n gs hcl i b o j hst]
      rfl
    refine ⟨(passG n gs i b).length, hcount, ?_⟩
    rw [e]
    exact h2
section Scope308
variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem Least.save (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length :=
  CoreHelpers.Readers.save n f gs o L.hcl L.hev i b hnc S hS
theorem Least.save3 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    Drop f i b 3 gs.length := by
  have := L.save i b hnc {p1, p2, p3} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption)
  rwa [Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩] at this
theorem rc_input {gs : List Gate} {q : ℕ} {i : Fin (n + 1)} (b : Bool) (h : Reads gs q i) :
    RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  exact ⟨g, hg, i, hin, b, stF_self n gs i b⟩
theorem rc_of_reads {gs : List Gate} {q w : ℕ} {i : Fin (n + 1)} {b : Bool} (h : Reads gs q w)
    (hc : IsC n gs i b w) : RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  obtain ⟨c, hc⟩ := hc
  exact ⟨g, hg, w, hin, c, hc⟩
theorem Least.next (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p : ℕ) (hp : p < gs.length) (hc : IsC n gs i b (n + 1 + p)) :
    ∃ q, p < q ∧ Reads gs q (n + 1 + p) ∧ RC n gs i b q := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  have ho : o ≠ n + 1 + p := by
    intro e
    obtain ⟨c, hc'⟩ := hc
    obtain ⟨x, y, hxy⟩ := hnc
    rw [← e] at hc'
    exact hxy ((restr_const L.hcl L.hev i b c hc' x).trans (restr_const L.hcl L.hev i b c hc' y).symm)
  obtain ⟨q, hpq, hr⟩ := L.live hfnc p hp ho
  exact ⟨q, hpq, hr, rc_of_reads hr hc⟩
end Scope308
end CoreHelpers.Readers
end Source8

section Source9
namespace SixBridge
open SixSigned
def bag (f : Nat→Nat) (s : Finset Nat) := s.val.map f
lemma bag_insert {f : Nat→Nat} {x : Nat} {s : Finset Nat} (h : x∉s) :
    bag f (insert x s)=f x ::ₘ bag f s := by
  simp only [bag,Finset.insert_val_of_notMem h,Multiset.map_cons]
lemma feed {mask goal r : Nat} {f : Nat→Nat} {w a b m q : Nat} {s : Finset Nat}
    (hw : w∉s) (ab : a≠b)
    (op : f w=(f a &&& f b) ∨ f w=(f a ||| f b))
    (cap : (insert w s).card≤ m+1)
    (budget : m+2≤(insert a (insert b s)).card+q)
    (next : ∀q',m+1≤(insert w s).card+q' → Run mask goal q' r (bag f (insert w s))) :
    Run mask goal q r (bag f (insert a (insert b s))) := by
  let t:=(s.erase a).erase b
  have at' : a∉t := by simp [t]
  have bt : b∉t := by simp [t]
  have abt : a∉insert b t := by simp [ab,at']
  have eq : insert a (insert b s)=insert a (insert b t) := by ext z;simp only [t,Finset.mem_insert,Finset.mem_erase];tauto
  rw [eq] at budget ⊢
  simp only [Finset.card_insert_of_notMem abt,Finset.card_insert_of_notMem bt] at budget
  rw [bag_insert abt,bag_insert bt]
  have sw:=Finset.card_insert_of_notMem hw
  rw [sw] at cap
  by_cases am : a∈s
  · by_cases bm : b∈s
    · have st : s=insert a (insert b t) := by ext z; simp only [t,Finset.mem_insert,Finset.mem_erase];grind
      have card : s.card=t.card+2 := by rw [st,Finset.card_insert_of_notMem abt,Finset.card_insert_of_notMem bt]
      have rest:=next (q-2) (by rw [sw,card];omega)
      rw [bag_insert hw,st,bag_insert abt,bag_insert bt] at rest
      have result:=Run.both op rest
      rwa [show q-2+2=q by omega] at result
    · have st : s=insert a t := by ext z; simp only [t,Finset.mem_insert,Finset.mem_erase];grind
      have card : s.card=t.card+1 := by rw [st,Finset.card_insert_of_notMem at']
      have rest:=next (q-1) (by rw [sw,card];omega)
      rw [bag_insert hw,st,bag_insert at'] at rest
      have result:=Run.reuse op rest
      rwa [show q-1+1=q by omega] at result
  · by_cases bm : b∈s
    · have st : s=insert b t := by ext z; simp only [t,Finset.mem_insert,Finset.mem_erase];grind
      have card : s.card=t.card+1 := by rw [st,Finset.card_insert_of_notMem bt]
      have rest:=next (q-1) (by rw [sw,card];omega)
      rw [bag_insert hw,st,bag_insert bt] at rest
      have rev : f w=(f b &&& f a) ∨ f w=(f b ||| f a) := by
        simpa only [Nat.and_comm (f b) (f a),Nat.or_comm (f b) (f a)] using op
      have result:=Run.reuse rev rest
      rw [show q-1+1=q by omega,Multiset.cons_swap (f b) (f a)] at result
      exact result
    · have st : s=t := by simp [t,am,bm]
      have card : s.card=t.card := congrArg Finset.card st
      have rest:=next q (by rw [sw,card];omega)
      rw [bag_insert hw,st] at rest
      exact .merge op rest
lemma feed_not {mask goal r : Nat} {f : Nat→Nat} {w a m q : Nat} {s : Finset Nat}
    (hw : w∉s) (op : f w=mask ^^^ f a)
    (cap : (insert w s).card≤ m+1) (budget : m+2≤(insert a s).card+q)
    (next : ∀q',m+1≤(insert w s).card+q' → Run mask goal q' r (bag f (insert w s))) :
    Run mask goal q (r+1) (bag f (insert a s)) := by
  let t:=s.erase a
  have at' : a∉t := by simp [t]
  have eq : insert a s=insert a t := by ext z;simp only [t,Finset.mem_insert,Finset.mem_erase];tauto
  rw [eq] at budget ⊢
  rw [Finset.card_insert_of_notMem at'] at budget
  rw [bag_insert at']
  have sw:=Finset.card_insert_of_notMem hw
  rw [sw] at cap
  by_cases am : a∈s
  · have st : s=insert a t := (Finset.insert_erase am).symm
    have sz : s.card=t.card+1 := by rw [st,Finset.card_insert_of_notMem at']
    have rest:=next (q-2) (by rw [sw,sz];omega)
    rw [bag_insert hw,st,bag_insert at',op] at rest
    have got:=Run.copyFlip rest
    rwa [show q-2+2=q by omega] at got
  · have st : s=t := by simp [t,am]
    have sz := congrArg Finset.card st
    have rest:=next (q-1) (by rw [sw,sz];omega)
    rw [bag_insert hw,st,op] at rest
    have got:=Run.flip rest
    rwa [show q-1+1=q by omega] at got
def active (n : Nat) (a b : Nat→Nat) (out : Nat) : List Nat→Finset Nat
  | []=>{out}
  | j::s=>insert (a j) (insert (b j) ((active n a b out s).erase (n+j)))
def AllUsed (n : Nat) (a b : Nat→Nat) (out : Nat) : List Nat→Prop
  | []=>True
  | j::s=> n+j∈active n a b out s ∧ AllUsed n a b out s
lemma active_card {n : Nat} {a b : Nat→Nat} {out : Nat} {gs : List Nat} (all : AllUsed n a b out gs) :
    (active n a b out gs).card≤ gs.length+1 := by
  induction gs with
  | nil=>simp [active]
  | cons j gs ih =>
    obtain ⟨used,ok⟩:=all
    have e:=Finset.card_erase_add_one used
    have l:=Finset.card_insert_le (a j) (insert (b j) ((active n a b out gs).erase (n+j)))
    have r:=Finset.card_insert_le (b j) ((active n a b out gs).erase (n+j))
    have prev:=ih ok
    simp only [active,List.length_cons];omega
lemma active_mem {n : Nat} {a b : Nat→Nat} {out x : Nat} {s : List Nat}
    (outside : ∀j∈s,x≠n+j) (used : x=out ∨∃j∈s,x=a j ∨ x=b j) : x∈active n a b out s := by
  induction s with
  | nil=>simpa [active] using used
  | cons j s ih =>
    simp only [active,Finset.mem_insert,Finset.mem_erase]
    by_cases ha : x=a j
    · exact Or.inl ha
    by_cases hb : x=b j
    · exact Or.inr (Or.inl hb)
    refine Or.inr (Or.inr ⟨outside j (by simp),ih (fun i hi => outside i (List.mem_cons_of_mem _ hi)) ?_⟩)
    rcases used with rfl|⟨t,ht,which⟩
    · exact Or.inl rfl
    · rcases List.mem_cons.mp ht with rfl|old
      · exact False.elim (which.elim ha hb)
      · exact Or.inr ⟨t,old,which⟩
lemma used_range {n t k out : Nat} {a b : Nat→Nat}
    (later : ∀j,k≤ j→j<k+t→n+j=out ∨ ∃ i, j < i ∧ i < k+t ∧ (n+j=a i ∨ n+j=b i)) :
    AllUsed n a b out (List.range' k t) := by
  induction t generalizing k with
  | zero=>trivial
  | succ t ih =>
    rw [List.range'_succ];constructor
    · apply active_mem
      · intro i hi;obtain ⟨u,_,eq⟩:=List.mem_range'.mp hi;simp only [one_mul] at eq;omega
      · rcases later k le_rfl (by omega) with eq|⟨i,lt,hi,pin⟩
        · exact Or.inl eq
        · exact Or.inr ⟨i,List.mem_range'.mpr ⟨i-(k+1),by omega,by simp only [one_mul];omega⟩,pin⟩
    · apply ih
      intro j lo hi
      simpa only [Nat.add_assoc,Nat.add_comm 1 t] using later j (by omega) (by omega)
lemma active_bound (n : Nat) (a b : Nat→Nat) (out k l : Nat) (bound : out<n+k+l)
    (back : ∀j,k≤ j→j<k+l→a j<n+j ∧ b j<n+j) :
    ∀w∈active n a b out (List.range' k l),w<n+k := by
  induction l generalizing k with
  | zero=>simpa [active] using bound
  | succ l ih =>
    have tail:=ih (k+1) (by omega) (fun j lo hi=>back j (by omega) (by omega))
    have now:=back k (by omega) (by omega)
    intro w mem
    rw [List.range'_succ,active] at mem
    rcases Finset.mem_insert.mp mem with rfl|mem
    · exact now.1
    rcases Finset.mem_insert.mp mem with rfl|mem
    · exact now.2
    obtain ⟨ne,h⟩:=Finset.mem_erase.mp mem
    have lt:=tail w h
    omega
lemma signed_run {mask goal n out : Nat} {a b f : Nat→Nat} {isNot : Nat→Bool} {gs : List Nat}
    (all : AllUsed n a b out gs) (final : f out=goal)
    (rules : ∀j∈gs, if isNot j then a j=b j ∧ f (n+j)=mask ^^^ f (a j) else
      a j≠b j ∧ (f (n+j)=f (a j) &&& f (b j) ∨ f (n+j)=f (a j) ||| f (b j))) :
    ∀q,gs.length+1≤(active n a b out gs).card+q → Run mask goal q (gs.countP isNot) (bag f (active n a b out gs)) := by
  induction gs with
  | nil =>
    intro q _;apply Run.done;simp [active,bag,final]
  | cons j gs ih =>
    intro q coins
    obtain ⟨use,tail⟩:=all
    have rest:=ih tail (fun k hk=>rules k (List.mem_cons_of_mem _ hk))
    have ins:=Finset.insert_erase use
    have rule:=rules j (List.mem_cons_self ..)
    simp only [active,List.length_cons] at coins ⊢
    cases neg : isNot j with
    | false =>
      simp only [neg,Bool.false_eq_true,ite_false] at rule
      simp only [List.countP_cons,neg,Bool.false_eq_true,ite_false,Nat.add_zero]
      refine feed (w:=n+j) (m:=gs.length) (s:=(active n a b out gs).erase (n+j)) (by simp) rule.1 rule.2 ?_ coins ?_
      · rw [ins];exact active_card tail
      · rw [ins];exact rest
    | true =>
      simp only [neg,ite_true] at rule
      rw [←rule.1,Finset.insert_idem] at coins ⊢
      simp only [List.countP_cons,neg,ite_true]
      refine feed_not (w:=n+j) (m:=gs.length) (s:=(active n a b out gs).erase (n+j)) (by simp) rule.2 ?_ coins ?_
      · rw [ins];exact active_card tail
      · rw [ins];exact rest
end SixBridge
end Source9

section Source10
namespace TableReader
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoreHelpers
open CoreHelpers.PermInputs
abbrev V := Fin 6
def target (x : V→Bool) := Nat.testBit (3907577984*2^32+3900735488) (∑ i : V, if x i then 2^i.val else 0)
def t4 (x : Fin 5→Bool) := Nat.testBit 3900735488 (∑ i : Fin 5, if x i then 2^i.val else 0)
open PEqualNP.MetaComplexity.NestedCover
end TableReader
end Source10

section Source11
namespace SixBridge
open SixSigned PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoreHelpers
open CoreHelpers.Readers
def flagNot (g : Gate) := match g.op with | .not => true | _ => false
private def get (gs : List Gate) (j : Nat) : Gate := gs.getD j ⟨.or,[]⟩
private theorem get_live {gs : List Gate} {j : Nat} (h : j<gs.length) : gs[j]?=some (get gs j) := by
  simp only [get,List.getD_eq_getElem _ _ h,List.getElem?_eq_getElem h]
def word {α : Type} (f : α→Bool) : List α→Nat
  | []=>0
  | a::as=>Nat.bit (f a) (word f as)
private theorem word_bit {α : Type} (f : α→Bool) : ∀(l : List α) (j : Nat),
    (word f l).testBit j=(l.map f).getD j false
  | [],j=>by simp [word]
  | a::l,0=>by simp [word]
  | a::l,j+1=>by simp [word,Nat.testBit_bit_succ,word_bit f l j]
private theorem ops {α : Type} (f g : α→Bool) (l : List α) :
    word (fun i=>f i && g i) l=word f l &&& word g l ∧
    word (fun i=>f i || g i) l=word f l ||| word g l ∧
    word (fun i=>!(f i)) l=word (fun _=>true) l ^^^ word f l := by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro j <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,word_bit]
  all_goals
    by_cases before : j<l.length
    · simp [before]
    · have none (z : α→Bool) : (l.map z).getD j false=false := List.getD_eq_default _ _ (by simp;omega)
      simp only [none] <;> rfl
theorem least_run {n s m q mask goal : Nat} {F : (Fin n→Bool)→Bool} (gs : List Gate) (out : Nat)
    (L : Least n F gs out) (small : gs.length ≤ s) (budget : s+1 ≤ n+q)
    (nc : ∃x y,F x≠F y)
    (dep : ∀p : Fin n, Dep F p)
    (nclamp : ∀p : Fin n,∀b : Bool,∃x y : Fin n→Bool,F (Function.update x p b)≠F (Function.update y p b))
    (sample : Fin m→Fin n→Bool)
    (maskEq : word (fun _ : Fin m=>true) (List.finRange m)=mask)
    (goalEq : word (fun i=>F (sample i)) (List.finRange m)=goal) :
    Run mask goal q (gs.countP flagNot)
      (↑((List.finRange n).map (fun v=>word (fun i=>sample i v) (List.finRange m))) : Multiset Nat) := by
  classical
  let a := fun j=>(get gs j).inputs.getD 0 0
  let b := fun j=>(get gs j).inputs.getD 1 (a j)
  let ng := fun j=>flagNot (get gs j)
  let f:=fun w=>word (fun i=>vl gs (sample i) w) (List.finRange m)
  let seq:=List.range' 0 gs.length
  have bounds (j : Nat) (hj : j<gs.length) :
      (a j<n+j ∧ b j<n+j) ∧
      ((ng j=true ∧ (get gs j).op=.not ∧ (get gs j).inputs=[a j] ∧ b j=a j) ∨
       (ng j=false ∧ ((get gs j).op=.and ∨ (get gs j).op=.or) ∧
         (get gs j).inputs=[a j,b j] ∧ a j≠b j)) := by
    have loc:=get_live hj
    rcases L.hcl j _ loc with ⟨kind,p,lt,pin⟩|⟨kind,p,r,lp,lr,pin⟩
    · have vals : a j=p ∧ b j=p := by simp [a,b,pin,List.getD_eq_getElem?_getD]
      rw [vals.1,vals.2]
      exact ⟨⟨lt,lt⟩,Or.inl ⟨by simp [ng,flagNot,kind],kind,pin,rfl⟩⟩
    · have vals : a j=p ∧ b j=r := by simp [a,b,pin,List.getD_eq_getElem?_getD]
      have diff : p≠r := by
        rintro rfl
        apply L.no_alias nc j hj p lp
        intro x
        rw [vl_gate gs L.hcl x j _ loc,pin]
        rcases kind with eq|eq <;> simp [eq,GateOp.eval]
      rw [vals.1,vals.2]
      exact ⟨⟨lp,lr⟩,Or.inr ⟨by rcases kind with h|h <;> simp [ng,flagNot,h],kind,pin,diff⟩⟩
  have readPin (j t : Nat) (reads : Reads gs j t) : t=a j ∨ t=b j := by
    obtain ⟨g,loc,h⟩:=reads
    have hj : j<gs.length := (List.getElem?_eq_some_iff.mp loc).1
    have eg := Option.some.inj ((get_live hj).symm.trans loc)
    subst g
    rcases (bounds j hj).2 with unary|binary
    · rw [unary.2.2.1] at h
      exact Or.inl (List.mem_singleton.mp h)
    · simpa only [binary.2.2.1,List.mem_cons,List.not_mem_nil,or_false] using h
  have liveall : AllUsed n a b out seq := by
    apply used_range
    intro j _ hj
    change j<0+gs.length at hj
    have hlen : j<gs.length := by omega
    by_cases eq : n+j=out
    · exact Or.inl eq
    obtain ⟨k,lt,reader⟩:=L.live nc j hlen (Ne.symm eq)
    exact Or.inr ⟨k,lt,by have :=reads_len reader;omega,readPin _ _ reader⟩
  have atOut : f out=goal := by
    have e : (fun i=>vl gs (sample i) out)=(fun i=>F (sample i)) := funext fun i=>L.hev _
    change word _ _=_
    rw [e,goalEq]
  have endBound : out<n+gs.length := by
    by_contra tooBig
    obtain ⟨x,y,ne⟩:=nc
    have x0:=vl_beyond gs x out (by omega)
    have y0:=vl_beyond gs y out (by omega)
    rw [L.hev] at x0 y0
    exact ne (x0.trans y0.symm)
  have gateRule (j : Nat) (mem : j∈seq) :
      if ng j then a j=b j ∧ f (n+j)=mask ^^^ f (a j) else
        a j≠b j ∧ (f (n+j)=f (a j) &&& f (b j) ∨ f (n+j)=f (a j) ||| f (b j)) := by
    have hj : j<gs.length := by simpa [seq] using mem
    have eval := fun i=>vl_gate gs L.hcl (sample i) j _ (get_live hj)
    have wordop:=ops (fun i=>vl gs (sample i) (a j)) (fun i=>vl gs (sample i) (b j)) (List.finRange m)
    rcases (bounds j hj).2 with unary|binary
    · simp only [unary.1,ite_true]
      refine ⟨unary.2.2.2.symm,?_⟩
      have eq : (fun i=>vl gs (sample i) (n+j))=fun i=>!(vl gs (sample i) (a j)) := by
        funext i;rw [eval i,unary.2.1,unary.2.2.1];rfl
      change word _ _=_
      rw [eq,wordop.2.2,maskEq]
    · simp only [binary.1,Bool.false_eq_true,ite_false]
      refine ⟨binary.2.2.2,?_⟩
      rcases binary.2.1 with h|h
      · left
        have eq : (fun i=>vl gs (sample i) (n+j))=fun i=>vl gs (sample i) (a j) && vl gs (sample i) (b j) := by
          funext i;rw [eval i,h,binary.2.2.1];simp [GateOp.eval]
        exact (congrArg (fun z=>word z (List.finRange m)) eq).trans wordop.1
      · right
        have eq : (fun i=>vl gs (sample i) (n+j))=fun i=>vl gs (sample i) (a j) || vl gs (sample i) (b j) := by
          funext i;rw [eval i,h,binary.2.2.1];simp [GateOp.eval]
        exact (congrArg (fun z=>word z (List.finRange m)) eq).trans wordop.2.1
  have same : active n a b out seq=Finset.range n := by
    ext v
    constructor
    · intro mem
      apply Finset.mem_range.mpr
      apply active_bound n a b out 0 gs.length (by omega) ?_ v mem
      exact fun j _ h =>(bounds j (by omega)).1
    · intro mem
      let u : Fin n:=⟨v,Finset.mem_range.mp mem⟩
      obtain ⟨j,read⟩:=L.dep_read u (dep u) (nclamp u)
      apply active_mem (fun k _=>by change v≠n+k;have :=u.isLt;change v<n at this;omega) (Or.inr ⟨j,?_,readPin _ _ read⟩)
      simpa [seq] using reads_len read
  have len : seq.length=gs.length := by simp [seq]
  have run:=signed_run liveall atOut gateRule q (by rw [same,Finset.card_range,len];omega)
  have mapgs : seq.map (get gs)=gs := by
    apply List.ext_getElem
    · simp [seq]
    · intro i h hi
      simp only [List.getElem_map,List.getElem_range',seq,Nat.one_mul,Nat.zero_add,get,List.getD_eq_getElem _ _ hi]
  have count : seq.countP ng=gs.countP flagNot := by
    rw [←mapgs,List.countP_map]
    rfl
  rw [count,same] at run
  have codeRaw (i : Fin n) : f i.val=word (fun j=>sample j i) (List.finRange m) := by
    change word _ _=_
    apply congrArg (fun z=>word z (List.finRange m))
    funext j;rw [vl_input gs (sample j) _ i.isLt]
  have source : bag f (Finset.range n)=↑((List.finRange n).map (fun v=>word (fun i=>sample i v) (List.finRange m))) := by
    have indices : (List.finRange n).map Fin.val=List.range n := by
      apply List.ext_getElem <;> simp
    rw [bag,Finset.range_val,←Multiset.coe_range,←indices,Multiset.map_coe,List.map_map]
    apply congrArg (fun l : List Nat=> (↑l:Multiset Nat))
    apply List.map_congr_left
    intro v _;exact codeRaw v
  rwa [source] at run
end SixBridge
end Source11

section Source12
namespace TableReader
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoreHelpers
open CoreHelpers.PermInputs CoreHelpers.Readers
def a1 (y : Fin 5→Bool) := Nat.testBit 0xeee8e880 (∑ i : Fin 5, if y i then 2^i.val else 0)
def afwd (p : V) : V→V := if p=0 then ![5,0,1,2,3,4] else if p=1 then ![0,5,1,2,3,4] else ![0,1,5,2,3,4]
end TableReader
end Source12

section Source13
namespace SixBridge
open SixSigned PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoreHelpers
open CoreHelpers.Readers TableReader
def aMasks : Fin 17→Nat := ![7,11,13,14,19,21,22,25,26,3,5,6,9,10,17,18,28]
def bMasks : Fin 15→Nat := ![15,23,27,29,30,7,11,13,14,19,21,22,25,26,28]
def sample5 {m : Nat} (masks : Fin m→Nat) (i : Fin m) (r : Fin 5) := (masks i).testBit r.val
def aRaw : List Nat := [22199,43867,68717,78222,115184]
def bRaw : List Nat := [5871,11127,19899,29149,32286]
theorem a1_budget (q : Nat) (gs : List Gate) (o : Nat) (least : Least 5 a1 gs o) (small : gs.length≤4+q) :
    Run 131071 511 q (gs.countP flagNot) (↑aRaw : Multiset Nat) := by
  have nc : ∃x y : Fin 5→Bool,a1 x≠a1 y := by decide +kernel
  have dep : ∀p : Fin 5,Dep a1 p := by unfold Dep;decide +kernel
  have clamps : ∀p : Fin 5,∀b : Bool,∃x y : Fin 5→Bool,
      a1 (Function.update x p b)≠a1 (Function.update y p b) := by decide +kernel
  have start := least_run (m:=17) (q:=q) gs o least small (by omega) nc dep clamps
    (sample5 aMasks) (by decide +kernel : _=131071) (by decide +kernel : _=511)
  have eq : (List.finRange 5).map (fun v=>word (fun i=>sample5 aMasks i v) (List.finRange 17))=aRaw := by decide +kernel
  rwa [eq] at start
theorem b0_budget (q : Nat) (gs : List Gate) (o : Nat) (least : Least 5 t4 gs o) (small : gs.length≤4+q) :
    Run 32767 31 q (gs.countP flagNot) (↑bRaw : Multiset Nat) := by
  have nc : ∃x y : Fin 5→Bool,t4 x≠t4 y := by decide +kernel
  have dep : ∀p : Fin 5,Dep t4 p := by unfold Dep;decide +kernel
  have clamps : ∀p : Fin 5,∀b : Bool,∃x y : Fin 5→Bool,
      t4 (Function.update x p b)≠t4 (Function.update y p b) := by decide +kernel
  have start := least_run (m:=15) (q:=q) gs o least small (by omega) nc dep clamps
    (sample5 bMasks) (by decide +kernel : _=32767) (by decide +kernel : _=31)
  have eq : (List.finRange 5).map (fun v=>word (fun i=>sample5 bMasks i v) (List.finRange 15))=bRaw := by decide +kernel
  rwa [eq] at start
theorem not_budget {mask goal q r : Nat} {s : Multiset Nat} (run : Run mask goal q r s) : r≤ q := by
  induction run <;> omega
end SixBridge
end Source13

section Source14
namespace CoreHelpers.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoreHelpers
theorem gate_cases {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (a : ℕ) (ha : a ∈ g.inputs) :
    (g.op = GateOp.not ∧ g.inputs = [a] ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = !vl gs u a) ∨
    ∃ w, (g.inputs = [a, w] ∨ g.inputs = [w, a]) ∧
      ((g.op = GateOp.and ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a && vl gs u w)) ∨
       (g.op = GateOp.or ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a || vl gs u w))) := by
  rcases hcl q g hq with ⟨hop, j, _, hin⟩ | ⟨hop, j, j', _, _, hin⟩
  · left
    have e : a = j := by rw [hin] at ha; simpa using ha
    subst e
    exact ⟨hop, hin, fun u => vl_not gs hcl u q g hq a hop hin⟩
  · right
    have e : a = j ∨ a = j' := by rw [hin] at ha; simpa using ha
    rcases e with e | e
    · subst e
      refine ⟨j', Or.inl hin, ?_⟩
      rcases hop with hop | hop
      · exact Or.inl ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
      · exact Or.inr ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
    · subst e
      refine ⟨j, Or.inr hin, ?_⟩
      rcases hop with hop | hop
      · refine Or.inl ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true]
        exact Bool.and_comm _ _
      · refine Or.inr ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          Bool.or_false]
        exact Bool.or_comm _ _
section Scope50
variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem Least.no_tri (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p q a : ℕ)
    (hpa : Reads gs p a) (hqa : Reads gs q a) (hqp : Reads gs q (m + p)) : False := by
  obtain ⟨gp, hgp, hap⟩ := hpa
  obtain ⟨gq, hgq, haq⟩ := hqa
  obtain ⟨gq', hgq', hpq⟩ := hqp
  have e : gq' = gq := by rw [hgq] at hgq'; exact (Option.some.inj hgq').symm
  subst e
  have hlt_a : a < m + p := (L.hcl p gp hgp).lt a hap
  have hlt_p : m + p < m + q := (L.hcl q gq' hgq).lt _ hpq
  have hqlen : q < gs.length := (List.getElem?_eq_some_iff.1 hgq).1
  rcases gate_cases gs L.hcl q gq' hgq a haq with ⟨_, hin, _⟩ | ⟨w, hin, hq⟩
  · rw [hin] at hpq
    simp at hpq
    omega
  · have hw : w = m + p := by
      rcases hin with hin | hin <;> rw [hin] at hpq <;> simp at hpq <;> omega
    subst hw
    rcases gate_cases gs L.hcl p gp hgp a hap with ⟨_, _, hp⟩ | ⟨w', _, hp⟩
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩
      · exact L.no_const hnc q hqlen false (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
      · exact L.no_const hnc q hqlen true (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩ <;> rcases hp with ⟨_, hp⟩ | ⟨_, hp⟩
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
end Scope50
section Scope90
variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem isC_reader (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (p : ℕ) (gp : Gate)
    (hgp : gs[p]? = some gp) (hip : (i : ℕ) ∈ gp.inputs) (b : Bool)
    (h : gp.op = GateOp.not ∨ b = fixBit gp) : IsC n gs i b (n + 1 + p) := by
  rcases h with h | rfl
  · apply st_allconst n gs hcl i b p gp hgp
    intro a ha
    rcases hcl p gp hgp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · rw [hin] at ha hip
      simp at ha hip
      rw [ha, ← hip]
      exact ⟨b, stF_self n gs i b⟩
    · rcases hop with hop | hop <;> rw [hop] at h <;> cases h
  · exact const_read n gs hcl i _ p gp hgp i hip (stF_self n gs i _)
theorem Least.third (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hc : IsC n gs i b (n + 1 + p)) : Drop f i b 3 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J, hJp, hJr, hJrc⟩ := L.next i b hnc p (reads_len hp) hc
  have hJq : J ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J i hp hq hJr
  exact L.save3 i b hnc p q J hpq (by omega) (Ne.symm hJq) (rc_input b hp) (rc_input b hq) hJrc
theorem Least.not_two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (r : ℕ) (g : Gate) (hr : gs[r]? = some g) (hop : g.op = GateOp.not)
    (hin : (i : ℕ) ∈ g.inputs) (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p (n + 1 + r))
    (hq : Reads gs q (n + 1 + r)) : Drop f i false 3 gs.length ∧ Drop f i true 3 gs.length := by
  have key : ∀ b, Drop f i b 3 gs.length := by
    intro b
    have hc := isC_reader L.hcl i r g hr hin b (Or.inl hop)
    have hpr := reads_lt L.hcl hp
    have hqr := reads_lt L.hcl hq
    exact L.save3 i b (hnc b) r p q (by omega) (by omega) hpq (rc_input b ⟨g, hr, hin⟩)
      (rc_of_reads hp hc) (rc_of_reads hq hc)
  exact ⟨key false, key true⟩
end Scope90
end CoreHelpers.Readers
end Source14

section Source15
namespace TableReader
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoreHelpers
open CoreHelpers.Readers CoreHelpers.PermInputs
abbrev LeftLow := ∀ k, HasCircuitSize 5 a1 k → 10≤ k
abbrev RightLow := ∀ k, HasCircuitSize 5 t4 k → 10≤ k
def expensive (p : V) := decide (p.val<3)
def expected (p : V) : GateOp := if expensive p then .and else .or
def fiveMap (p i : V) : Fin 5 :=
  if expensive p then Fin.ofNat 5 (afwd p i).val else Fin.ofNat 5 ((Equiv.swap p (Fin.last 5)) i).val
private theorem repr5 : ∀ (p : V) (y : Fin 5→Bool),
    target (Function.update (y ∘ fiveMap p) p (expensive p)) = (if expensive p then a1 y else t4 y) := by decide +kernel
private theorem restrNC (p : V) (b : Bool) : ∃x y : V→Bool,
   target (Function.update x p b) ≠ target (Function.update y p b) := by
  refine ⟨fun _=>false,fun _=>true,?_⟩
  have tab : ∀p : V, ∀b : Bool, target (Function.update (fun _=>false) p b)≠target (Function.update (fun _=>true) p b) := by decide +kernel
  exact tab p b
theorem no_hard_drop (LL : LeftLow) (RL : RightLow) (p : V) (n : Nat) (small : n≤12) :
    ¬ Drop target p (expensive p) 3 n := by
  rintro ⟨k,len,program⟩
  have proj := relabel_size (fiveMap p) _ k program
  have identical : (fun y : Fin 5→Bool => target (Function.update (y ∘ fiveMap p) p (expensive p))) =
      (fun y=>if expensive p then a1 y else t4 y) := funext (repr5 p)
  rw [identical] at proj
  have k10 : 10≤ k := by
    cases hi : expensive p with
    | false => exact RL k (by simpa [hi] using proj)
    | true => exact LL k (by simpa [hi] using proj)
  omega
theorem double_kind (LL : LeftLow) (RL : RightLow) (gs : List Gate) (o : Nat)
    (L : Least 6 target gs o) (small : gs.length≤12) (p : V) (i j : Nat) (ij : i≠j)
    (g : Gate) (loc : gs[i]?=some g) (read : p.val∈g.inputs) (other : Reads gs j p.val) :
    g.op=expected p := by
  by_contra neq
  have ops := ((clean_nok 6 gs L.hcl g (List.mem_of_getElem? loc)).1).1
  have absorbs : g.op=.not ∨ expensive p=fixBit g := by
    rcases ops with eq|eq|eq <;> cases b : expensive p <;> simp_all [expected,fixBit]
  have const := isC_reader L.hcl p i g loc read (expensive p) absorbs
  exact no_hard_drop LL RL p _ small (L.third p _ (restrNC _ _) i j ij ⟨g,loc,read⟩ other const)
theorem raw_not_fanout (LL : LeftLow) (RL : RightLow) (gs : List Gate) (o : Nat)
    (L : Least 6 target gs o) (small : gs.length≤12) (p : V) (r : Nat) (g : Gate)
    (loc : gs[r]?=some g) (op : g.op=.not) (read : p.val∈g.inputs) (i j : Nat)
    (ri : Reads gs i (6+r)) (rj : Reads gs j (6+r)) : i=j := by
  by_contra neq
  obtain ⟨hf,ht⟩ := L.not_two_readers p (restrNC p) r g loc op read i j neq ri rj
  apply no_hard_drop LL RL p _ small
  cases e : expensive p <;> assumption
theorem raw_not_only (LL : LeftLow) (RL : RightLow) (gs : List Gate) (o : Nat)
    (L : Least 6 target gs o) (small : gs.length≤12) (p : V) (r : Nat) (g : Gate)
    (loc : gs[r]?=some g) (op : g.op=.not) (read : p.val∈g.inputs) (q : Nat)
    (other : Reads gs q p.val) : q=r := by
  by_contra ne
  have eq := double_kind LL RL gs o L small p r q (fun eq=>ne eq.symm) g loc read other
  cases e : expensive p <;> simp_all [expected]
end TableReader
end Source15

section Source16
namespace CoreHelpers.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoreHelpers
theorem lit_contra {m : ℕ} {f : (Fin m → Bool) → Bool} (hnc : RestrNC f) (v : Fin m) (c : Bool)
    (h : ∀ u, f u = xor (u v) c) : False := by
  have hd : Dep f v := ⟨fun _ => false, by rw [h, h]; cases c <;> simp⟩
  obtain ⟨x, y, hxy⟩ := hnc v hd false
  apply hxy
  rw [h, h]
  simp
section Scope39
variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem Least.not_input (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (t : ℕ) (ht : ∀ r < t, ∀ g, gs[r]? = some g → g.op = GateOp.not) (r : ℕ) (hr : r < t)
    (g : Gate) (hg : gs[r]? = some g) : ∃ v : Fin (n + 1), g.inputs = [(v : ℕ)] := by
  rcases L.hcl r g hg with ⟨hop, j, hj, hin⟩ | ⟨hop, _⟩
  · by_cases hjn : j < n + 1
    · exact ⟨⟨j, hjn⟩, hin⟩
    · exfalso
      obtain ⟨r', rfl⟩ : ∃ r', j = n + 1 + r' := ⟨j - (n + 1), by omega⟩
      have hrl : r < gs.length := (List.getElem?_eq_some_iff.1 hg).1
      obtain ⟨g', hg'⟩ : ∃ g', gs[r']? = some g' :=
        ⟨gs[r'], List.getElem?_eq_getElem (by omega)⟩
      have hop' := ht r' (by omega) g' hg'
      rcases L.hcl r' g' hg' with ⟨_, j', hj', hin'⟩ | ⟨hop2, _⟩
      · exact L.no_alias hfnc r hrl j' (by omega) (fun u => by
          rw [vl_not gs L.hcl u r g hg _ hop hin, vl_not gs L.hcl u r' g' hg' _ hop' hin']
          simp)
      · rcases hop2 with h | h <;> rw [h] at hop' <;> cases hop'
  · rcases hop with h | h <;> rw [ht r hr g hg] at h <;> cases h
theorem Least.lit_wire (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (t : ℕ) (ht : ∀ r < t, ∀ g, gs[r]? = some g → g.op = GateOp.not) (w : ℕ)
    (hw : w < n + 1 + t) (hwl : w < n + 1 + gs.length) :
    ∃ (v : Fin (n + 1)) (c : Bool), (∀ u, vl gs u w = xor (u v) c) ∧
      (w = v ∨ ∃ r g, r < t ∧ w = n + 1 + r ∧ gs[r]? = some g ∧ g.op = GateOp.not ∧
        g.inputs = [(v : ℕ)]) := by
  by_cases hwn : w < n + 1
  · exact ⟨⟨w, hwn⟩, false, fun u => by rw [vl_input gs u w hwn]; simp, Or.inl rfl⟩
  · obtain ⟨r, rfl⟩ : ∃ r, w = n + 1 + r := ⟨w - (n + 1), by omega⟩
    obtain ⟨g, hg⟩ : ∃ g, gs[r]? = some g := ⟨gs[r], List.getElem?_eq_getElem (by omega)⟩
    have hop := ht r (by omega) g hg
    obtain ⟨v, hin⟩ := L.not_input hfnc t ht r (by omega) g hg
    exact ⟨v, true, fun u => by
      rw [vl_not gs L.hcl u r g hg _ hop hin, vl_input gs u v v.isLt]; simp,
      Or.inr ⟨r, g, by omega, rfl, hg, hop, hin⟩⟩
end Scope39
end CoreHelpers.Readers
end Source16

section Source17
namespace TableReader
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoreHelpers
open CoreHelpers.Readers
private theorem ncf : ∃x y : V→Bool,target x≠target y := ⟨fun _=>false,fun _=>true,by decide +kernel⟩
private theorem nc_pin : RestrNC target := by
  intro p _ b
  exact ⟨fun _=>false,fun _=>true,by
    have h : ∀p : V, ∀ b : Bool,target (Function.update (fun _=>false) p b)≠ target (Function.update (fun _=>true) p b) := by decide +kernel
    exact h p b⟩
theorem sensitive : ∀ p q : V,p≠q → ∀b : Bool, ∃ x : V→Bool,
    x q=b ∧ target x≠target (Function.update x p (!x p)) := by decide +kernel
def Multi (gs : List Gate) (p : V) := ∃i j, i≠j ∧ Reads gs i p.val ∧ Reads gs j p.val
private def Lit (gs : List Gate) (t w : Nat) (p : V) := w=p.val ∨
  ∃r g,r<t ∧ w=6+r ∧ gs[r]?=some g ∧ g.op=.not ∧ g.inputs=[p.val]
private theorem bottleneck (LL : LeftLow) (RL : RightLow) (gs : List Gate) (o : Nat)
    (L : Least 6 target gs o) (small : gs.length≤12) (t w z : Nat) (g : Gate) (atT : gs[t]?=some g)
    (ops : g.op=.and ∨ g.op=.or) (pins : g.inputs=[w,z] ∨ g.inputs=[z,w])
    (p q : V) (diff : p≠q) (cp cq : Bool) (vP : ∀x,vl gs x w=(x p ^^ cp))
    (vQ : ∀x,vl gs x z=(x q ^^ cq)) (lP : Lit gs t w p) : Multi gs p := by
  by_contra solo
  have one (i j : Nat) (a : Reads gs i p.val) (b : Reads gs j p.val) : i=j :=
    by_contra fun ne => solo ⟨i,j,ne,a,b⟩
  have rw' : Reads gs t w := ⟨g,atT,pins.elim (fun h=>by simp [h]) (fun h=>by simp [h])⟩
  have reach (j i : Nat) (orig : i=p.val ∨ i=w) (rd : Reads gs j i) (notW : 6+j≠w) : j=t := by
    rcases lP with eq|⟨k,ng,_,eq,loc,not,ins⟩
    · rcases orig with h|h <;> subst i <;> rw [eq] at rw'
      · exact one j t rd rw'
      · rw [eq] at rd; exact one j t rd rw'
    · have raw : Reads gs k p.val := ⟨ng,loc,by simp [ins]⟩
      rcases orig with h|h
      · subst i
        exact False.elim (notW (by rw [one j k rd raw,eq]))
      · subst i
        rw [eq] at rd rw'
        exact raw_not_fanout LL RL gs o L small p k ng loc not (by simp [ins]) j t rd rw'
  let setting := fixBit g ^^ cq
  obtain ⟨x,pinned,change⟩ := sensitive p q diff setting
  let y := Function.update x p (!x p)
  have gy (u : V→Bool) (set : u q=setting) : vl gs u (6+t)=fixBit g := by
    rw [vl_gate gs L.hcl _ t g atT]
    rcases pins with ps|ps <;> rw [ps] <;> simp only [List.map_cons,List.map_nil,vQ,set]
    all_goals rcases ops with a|a <;> cases cq <;> simp [a,setting,fixBit,GateOp.eval]
  have eqG := (gy x pinned).trans (gy y (by simpa [y,Function.update_of_ne diff.symm] using pinned)).symm
  apply change
  rw [←L.hev,←L.hev]
  apply agree_B gs L.hcl x y (fun i=>i=p.val ∨ i=w) (o+1) _ _ o (by omega) _
  · intro i hi off
    rw [vl_input gs x i hi,vl_input gs y i hi]
    exact (Function.update_of_ne (show (⟨i,hi⟩ : V)≠p from fun h=>off (Or.inl (congrArg Fin.val h))) _ _).symm
  · intro k b loc _ safe bad _
    obtain ⟨i,mem,atB⟩ := bad
    have same:=reach k i atB ⟨b,loc,mem⟩ (fun h=>safe (Or.inr h))
    exact same ▸ eqG
  · rintro (out|out)
    · apply lit_contra nc_pin p false
      intro u; rw [←L.hev,out,vl_input gs u p.val p.isLt];simp
    · apply lit_contra nc_pin p cp
      intro u;rw [←L.hev,out,vP]
private theorem raw_of_multi (LL : LeftLow) (RL : RightLow) (gs : List Gate) (o : Nat)
    (L : Least 6 target gs o) (small : gs.length≤12) (t w : Nat) (p : V)
    (hs : Lit gs t w p) (m : Multi gs p) : w=p.val := by
  rcases hs with direct|⟨k,g,_,_,loc,not,ins⟩
  · exact direct
  · obtain ⟨i,j,ne,ri,rj⟩ := m
    have A := raw_not_only LL RL gs o L small p k g loc not (by simp [ins]) i ri
    have B := raw_not_only LL RL gs o L small p k g loc not (by simp [ins]) j rj
    exact (ne (A.trans B.symm)).elim
theorem another (gs : List Gate) (p : V) (m : Multi gs p) (t : Nat) : ∃s, t≠s ∧ Reads gs s p.val := by
  obtain ⟨i,j,ij,ri,rj⟩ :=m
  by_cases ti:t=i
  · exact ⟨j,ti.symm ▸ ij,rj⟩
  · exact ⟨i,ti,ri⟩
theorem first_binary (LL : LeftLow) (RL : RightLow) (gs : List Gate) (o : Nat)
    (L : Least 6 target gs o) (small : gs.length≤12) :
    ∃ (t : Nat) (g : Gate) (p q : V), gs[t]?=some g ∧ g.op≠.not ∧
    (∀ r<t, ∀ h,gs[r]?=some h → h.op=.not) ∧ p≠q ∧ g.inputs=[p.val,q.val] ∧
    Multi gs p ∧ Multi gs q ∧ g.op=expected p ∧ g.op=expected q := by
  classical
  have existsBin : ∃ (t : Nat) (g : Gate), gs[t]?=some g ∧ g.op≠.not := by
    by_contra! no
    have ht : ∀r<gs.length, ∀g, gs[r]?=some g → g.op=.not := fun r _ g hg=>no r g hg
    by_cases hol : o<6+gs.length
    · obtain ⟨v,c,hv,_⟩ := L.lit_wire ncf gs.length ht o hol hol
      exact lit_contra nc_pin v c (fun u=>by rw [←L.hev,hv])
    · obtain ⟨x,y,ne⟩ := ncf
      apply ne
      rw [←L.hev,←L.hev,vl_beyond gs x o (by omega),vl_beyond gs y o (by omega)]
  let t := Nat.find existsBin
  obtain ⟨g,loc,diff⟩ := Nat.find_spec existsBin
  have earlier : ∀r<t,∀g,gs[r]?=some g → g.op=.not := by
    intro r h g loc
    by_contra ne
    exact Nat.find_min existsBin h ⟨g,loc,ne⟩
  have tp : t<gs.length := (List.getElem?_eq_some_iff.mp loc).1
  rcases L.hcl t g loc with ⟨not,_⟩|⟨ops,w,z,wt,zt,pins⟩
  · exact (diff not).elim
  obtain ⟨p,cp,vp,LP⟩ := L.lit_wire ncf t earlier w wt (by omega)
  obtain ⟨q,cq,vq,LQ⟩ := L.lit_wire ncf t earlier z zt (by omega)
  have distinct : p≠q := by
    rintro rfl
    by_cases signs : cp=cq
    · subst cq
      apply L.no_alias ncf t tp w wt
      intro x
      rw [vl_gate gs L.hcl x t g loc,pins]
      simp only [List.map_cons,List.map_nil,vp,vq]
      rcases ops with op|op <;> simp [op,GateOp.eval]
    · rcases ops with op|op
      · apply L.no_const ncf t tp false
        intro x; rw [vl_gate gs L.hcl x t g loc,pins]
        simp only [List.map_cons,List.map_nil,vp,vq]
        cases cp <;> cases cq <;> cases h:x p <;> simp_all [GateOp.eval]
      · apply L.no_const ncf t tp true
        intro x; rw [vl_gate gs L.hcl x t g loc,pins]
        simp only [List.map_cons,List.map_nil,vp,vq]
        cases cp <;> cases cq <;> cases h:x p <;> simp_all [GateOp.eval]
  have MP := bottleneck LL RL gs o L small t w z g loc ops (Or.inl pins) p q distinct cp cq vp vq LP
  have MQ := bottleneck LL RL gs o L small t z w g loc ops (Or.inr pins) q p distinct.symm cq cp vq vp LQ
  have W := raw_of_multi LL RL gs o L small t w p LP MP
  have Z := raw_of_multi LL RL gs o L small t z q LQ MQ
  rw [W,Z] at pins
  obtain ⟨r,rt,rr⟩ := another gs p MP t
  obtain ⟨s,st,ss⟩ := another gs q MQ t
  exact ⟨t,g,p,q,loc,diff,earlier,distinct,pins,MP,MQ,
    double_kind LL RL gs o L small p t r rt g loc (by simp [pins]) rr,
    double_kind LL RL gs o L small q t s st g loc (by simp [pins]) ss⟩
end TableReader
end Source17

section Source18
namespace TableReader
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoreHelpers
open CoreHelpers.Readers
theorem pq2_passG_len (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) :
    (passG n gs i b).length + S.card ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) S (by
    intro p hp
    obtain ⟨g, hg, a, ha, c, hc⟩ := hS p hp
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  simpa [passG] using hcount
theorem pq2_passG_eval (n : ℕ) {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b)) :
    ∃ q, CleanL n (passG n gs i b) ∧
      ∀ y : Fin n → Bool, vl (passG n gs i b) y q = f (ins i b y) := by
  cases hst : stF n gs i b o with
  | const c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((restr_const hcl hev i b c hst x).trans (restr_const hcl hev i b c hst y).symm)
  | wire q =>
    refine ⟨q, clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
      (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp), ?_⟩
    intro y
    rw [← hev, st_val_wire n gs hcl i b o q hst y]
private theorem prefix_remains (n : Nat) (tail : List Gate) (start : List Stat × List Gate) :
    ∀g∈start.2,g∈(elim n tail start).2 := by
  induction tail generalizing start with
  | nil => exact fun _ mem => mem
  | cons a xs ih =>
    intro g mem
    rw [elim_cons]
    exact ih (elimStep n start a) g (List.mem_append_left _ mem)
private theorem not_survives {n : Nat} (gs : List Gate) (L : CleanL (n+1) gs) (p : Fin (n+1))
    (b : Bool) (j : Nat) (g : Gate) (loc : gs[j]?=some g) (not : g.op=.not)
    (kept : ¬RC n gs p b j) : ∃q∈passG n gs p b,q.op=.not := by
  rcases L j g loc with ⟨_,w,wlt,inputs⟩|⟨wrong,_⟩
  swap
  · rcases wrong with a|a <;> simp_all
  obtain ⟨pre,post,split,jlen⟩ := split_at gs j g loc
  let init : List Stat × List Gate := (statAt n p b,[])
  let acc := elim n pre init
  have earlier : w < init.1.length+pre.length := by
    change w<(statAt n p b).length+pre.length
    rw [statAt_length]
    omega
  have wireEq : stF n gs p b w=acc.1.getD w (.const false) := by
    unfold stF
    rw [split]
    exact elim_split_getD_lt n pre g post init w (.const false) earlier
  cases h : acc.1.getD w (.const false) with
  | const z => exact (kept ⟨g,loc,w,by simp [inputs],z,wireEq.trans h⟩).elim
  | wire j' =>
    let out : Gate := ⟨.not,[j']⟩
    have immediate : out∈(elimStep n acc g).2 := by
      apply List.mem_append_right
      change out∈(simplify g.op _ (g.inputs.map (fun i=>acc.1.getD i (.const false)))).1.toList
      rw [not,inputs]
      simp only [List.map_cons,List.map_nil,h,simplify,simpNot,Option.toList_some]
      exact List.mem_singleton_self _
    refine ⟨out,?_,rfl⟩
    change out∈(elim n gs init).2
    rw [split,elim_append,elim_cons]
    exact prefix_remains n post (elimStep n acc g) out immediate
private theorem cofactor_map : ∀ (p : V) (y : Fin 5→Bool),
    target (ins p (expensive p) y)=(if expensive p then a1 y else t4 y) := by decide +kernel
theorem pin_preserves_not (LL : LeftLow) (RL : RightLow) (gs : List Gate) (o : Nat)
    (L : Least 6 target gs o) (small : gs.length≤12) (p : V) (multi : Multi gs p) :
    ∃ (D : Circuit), D.gates=passG 5 gs p (expensive p) ∧ CleanL 5 D.gates ∧ (∀h∈D.gates,Ok h) ∧ D.size=10 ∧
    (∀x : Fin 5→Bool,D.eval (List.ofFn x)=(if expensive p then a1 x else t4 x)) ∧
    ((∃g∈gs,g.op=.not) → ∃q∈D.gates,q.op=.not) := by
  obtain ⟨u,v,uv,readU,readV⟩ := multi
  have nc : ∃x y : V→Bool, target (Function.update x p (expensive p))≠target (Function.update y p (expensive p)) := by
    refine ⟨fun _=>false,fun _=>true,?_⟩
    have table : ∀p : V,target (Function.update (fun _=>false) p (expensive p))≠target (Function.update (fun _=>true) p (expensive p)) := by decide +kernel
    exact table p
  obtain ⟨jo,cl,ev⟩ := pq2_passG_eval 5 L.hcl L.hev p (expensive p) nc
  let D : Circuit := ⟨passG 5 gs p (expensive p),jo⟩
  have saved := pq2_passG_len 5 gs L.hcl p (expensive p) {u,v} (fun i mem => by
    simp only [Finset.mem_insert,Finset.mem_singleton] at mem
    rcases mem with rfl|rfl
    · exact rc_input _ readU
    · exact rc_input _ readV)
  rw [Finset.card_pair uv] at saved
  have correct (x : Fin 5→Bool) : D.eval (List.ofFn x)=(if expensive p then a1 x else t4 x) :=
    (ev x).trans (cofactor_map p x)
  have ok : ∀g∈D.gates,Ok g := fun g mem=>(clean_nok _ _ cl g mem).1
  have low : 10≤ D.size := by
    cases h:expensive p with
    | true => exact LL D.size ⟨D,ok,le_rfl,by simpa [h] using correct⟩
    | false => exact RL D.size ⟨D,ok,le_rfl,by simpa [h] using correct⟩
  have size : D.size=10 := by change (passG 5 gs p (expensive p)).length=10; change 10≤(passG 5 gs p (expensive p)).length at low; omega
  refine ⟨D,rfl,cl,ok,size,correct,?_⟩
  rintro ⟨g,mem,not⟩
  obtain ⟨j,loc⟩ := List.mem_iff_getElem?.mp mem
  apply not_survives gs L.hcl p (expensive p) j g loc not
  intro lost
  have different (q t : Nat) (qt : q≠t) (readQ : Reads gs q p.val) (readT : Reads gs t p.val) : j≠q := by
    intro eq;subst q
    obtain ⟨z,atJ,raw⟩ := readQ
    have ze : z=g := Option.some.inj (atJ.symm.trans loc)
    have kind := double_kind LL RL gs o L small p j t qt g loc (ze ▸ raw) readT
    cases temp : expensive p <;> simp_all [expected]
  exact no_hard_drop LL RL p _ small (L.save3 p (expensive p) nc j u v
    (different u v uv readU readV) (different v u uv.symm readV readU) uv lost (rc_input _ readU) (rc_input _ readV))
theorem hard_not_core_clean (LL : LeftLow) (RL : RightLow) (gs : List Gate) (o : Nat)
    (L : Least 6 target gs o) (small : gs.length≤12) (someNot : ∃g∈gs,g.op=.not) :
    ∃D : Circuit, CleanL 5 D.gates ∧ (∀g∈D.gates,Ok g) ∧ D.size=10 ∧ (∃q∈D.gates,q.op=.not) ∧
      ((∀x : Fin 5→Bool,D.eval (List.ofFn x)=a1 x) ∨ (∀x : Fin 5→Bool,D.eval (List.ofFn x)=t4 x)) := by
  obtain ⟨t,g,p,q,_,_,_,_,_,mp,_⟩ := first_binary LL RL gs o L small
  obtain ⟨D,_,cl,ok,sz,correct,persist⟩ := pin_preserves_not LL RL gs o L small p mp
  refine ⟨D,cl,ok,sz,persist someNot,?_⟩
  cases hp : expensive p with
  | true => exact Or.inl (by simpa [hp] using correct)
  | false => exact Or.inr (by simpa [hp] using correct)
end TableReader
end Source18

section Source19
namespace SixCount
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev V := Fin 6
def target (x : V→Bool) := Nat.testBit (3907577984*2^32+3900735488)
  (∑i : V, if x i then 2^i.val else 0)
def witness : Circuit :=
  ⟨[⟨.and,[0,1]⟩,⟨.or,[0,1]⟩,⟨.and,[7,2]⟩,⟨.or,[6,8]⟩,⟨.and,[6,2]⟩,
    ⟨.and,[3,4]⟩,⟨.or,[3,4]⟩,⟨.and,[12,5]⟩,⟨.or,[11,13]⟩,⟨.or,[12,5]⟩,
    ⟨.and,[10,15]⟩,⟨.and,[9,14]⟩,⟨.or,[16,17]⟩],18⟩
theorem upper_13 : ∃C : Circuit, Monotone2 C ∧ C.size=13 ∧
    ∀x : V→Bool,C.eval (List.ofFn x)=target x := by
  refine ⟨witness,?_,rfl,?_⟩
  · simp [Monotone2,witness]
  · decide +kernel
end SixCount
end Source19

section Source20
namespace TableClaim
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoreHelpers
open CoreHelpers.Readers SixSigned SixBridge TableReader
def Checked (mask goal : Nat) (raw : List Nat) : Prop :=
  (¬Run mask goal 5 0 (raw : Multiset Nat)) ∧
  ∀r, 0<r → r≤6 → ¬Run mask goal 6 r (raw : Multiset Nat)
def Transfer (f : (Fin 5→Bool)→Bool) (mask goal : Nat) (raw : List Nat) : Prop :=
  ∀q gs o, Least 5 f gs o → gs.length≤4+q →
    Run mask goal q (gs.countP flagNot) (raw : Multiset Nat)
private theorem face_lower {f mask goal raw}
    (nc : ∃x y : Fin 5→Bool,f x≠f y) (data : Checked mask goal raw)
    (transfer : Transfer f mask goal raw) (s : Nat) (h : HasCircuitSize 5 f s) : 10 ≤ s := by
  by_contra! small
  obtain ⟨gs,o,least,sz⟩:=exists_least 5 f s nc h
  by_cases no : gs.countP flagNot=0
  · have r:=transfer 5 gs o least (by omega)
    rw [no] at r
    exact data.1 r
  · have r:=transfer 6 gs o least (by omega)
    exact data.2 _ (by omega) (not_budget r) r
private theorem face_without_not {f mask goal raw}
    (nc : ∃x y : Fin 5→Bool,f x≠f y) (data : Checked mask goal raw)
    (transfer : Transfer f mask goal raw) (D : Circuit) (clean : CleanL 5 D.gates)
    (sz : D.size=10) (uses : ∃g∈D.gates,g.op=.not)
    (ev : ∀x : Fin 5→Bool,D.eval (List.ofFn x)=f x) : False := by
  have least : Least 5 f D.gates D.output := by
    refine ⟨clean,ev,?_⟩
    intro gs o cl trueTable
    have valid : FanInTwo (Circuit.mk gs o) := fun g hg=>(clean_nok 5 gs cl g hg).1
    have low:=face_lower nc data transfer gs.length ⟨⟨gs,o⟩,valid,le_rfl,trueTable⟩
    change D.gates.length=10 at sz
    omega
  have r := transfer 6 D.gates D.output least (by change D.size≤4+6;omega)
  have positive : 0<D.gates.countP flagNot := by
    obtain ⟨g,h,not⟩:=uses
    by_contra! none
    have z : D.gates.countP flagNot=0 := by omega
    have bad := List.countP_eq_zero.mp z g h
    simp [flagNot,not] at bad
  exact data.2 _ positive (not_budget r) r
theorem conclude (ca : Checked 131071 511 aRaw) (cb : Checked 32767 31 bRaw)
    (ta : Transfer a1 131071 511 aRaw) (tb : Transfer t4 32767 31 bRaw)
    (s : Nat) (input : HasCircuitSize 6 target s) :
    ∃C : Circuit,Monotone2 C ∧ C.size ≤ s ∧ ∀x : Fin 6→Bool,C.eval (List.ofFn x)=target x := by
  by_cases room : 13 ≤ s
  · obtain ⟨C,mono,sz,ev⟩:=SixCount.upper_13
    exact ⟨C,mono,sz ▸ room,ev⟩
  have nca : ∃x y : Fin 5→Bool,a1 x≠a1 y := ⟨fun _=>false,fun _=>true,by decide +kernel⟩
  have ncb : ∃x y : Fin 5→Bool,t4 x≠t4 y := ⟨fun _=>false,fun _=>true,by decide +kernel⟩
  have nc : ∃x y : Fin 6→Bool,target x≠target y := ⟨fun _=>false,fun _=>true,by decide +kernel⟩
  obtain ⟨gs,o,L,sz⟩:=exists_least 6 target s nc input
  by_cases neg : ∃g∈gs,g.op=.not
  · obtain ⟨D,cl,_,ds,yes,correct⟩:=hard_not_core_clean
      (face_lower nca ca ta) (face_lower ncb cb tb) gs o L (by omega) neg
    rcases correct with h|h
    · exact (face_without_not nca ca ta D cl ds yes h).elim
    · exact (face_without_not ncb cb tb D cl ds yes h).elim
  · refine ⟨⟨gs,o⟩,?_,sz,L.hev⟩
    intro g mem
    obtain ⟨op,arity⟩:=(clean_nok 6 gs L.hcl g mem).1
    rcases op with a|b|c
    · exact ⟨Or.inl a,arity⟩
    · exact ⟨Or.inr b,arity⟩
    · exact (neg ⟨g,mem,c⟩).elim
end TableClaim
end Source20

section Source21
namespace TableClaim
open SixBridge
theorem from_tables (a : Checked 131071 511 aRaw) (b : Checked 32767 31 bRaw) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3907577984 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3907577984 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s input
  exact conclude a b a1_budget b0_budget s input
end TableClaim
end Source21

section Source22
namespace SixSigned
def bitMask (width : Nat) := 2^width-1
def origin (p n tag i : Nat) : Nat :=
  let k := (tag >>> (4*i))%16
  if i<p then k%p else p+k%n
def ren (p n tag w : Nat) : Nat := Nat.ofBits (fun i : Fin (p+n) => w.testBit (origin p n tag i))
theorem bit_ren (p n tag w i : Nat) : (ren p n tag w).testBit i =
    if i<p+n then w.testBit (origin p n tag i) else false := by
  by_cases hi : i<p+n
  · rw [if_pos hi,ren,Nat.testBit_ofBits_lt _ _ hi]
  · rw [if_neg hi,ren]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (Nat.ofBits_lt_two_pow _) (Nat.pow_le_pow_right
      (by decide : 0 < 2) (show p+n ≤ i by omega)))
theorem ren_and (p n t a b : Nat) : ren p n t (a &&& b) = ren p n t a &&& ren p n t b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<p+n <;> simp [Nat.testBit_and,bit_ren,hi]
theorem ren_or (p n t a b : Nat) : ren p n t (a ||| b) = ren p n t a ||| ren p n t b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<p+n <;> simp [Nat.testBit_or,bit_ren,hi]
theorem ren_xor (p n t a b : Nat) : ren p n t (a ^^^ b) = ren p n t a ^^^ ren p n t b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<p+n <;> simp [Nat.testBit_xor,bit_ren,hi]
theorem ren_mask (p n tag : Nat) : ren p n tag (bitMask (p+n))=bitMask (p+n) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h:i<p+n
  · rw [bit_ren,if_pos h]
    simp only [bitMask,Nat.testBit_two_pow_sub_one]
    apply decide_eq_decide.mpr
    simp only [h,iff_true]
    unfold origin
    split <;> rename_i hi
    · exact lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)
    · dsimp only
      have hn : 0<n := by omega
      have := Nat.mod_lt ((tag >>> (4*i))%16) hn
      omega
  · simp [bit_ren,h,bitMask]
theorem ren_goal (p n tag : Nat) : ren p n tag (bitMask p)=bitMask p := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h:i<p+n
  · rw [bit_ren,if_pos h]
    simp only [bitMask,Nat.testBit_two_pow_sub_one]
    apply decide_eq_decide.mpr
    unfold origin
    split <;> rename_i hi
    · simp [hi,Nat.mod_lt _ (show 0<p by omega)]
    · simp [hi]
  · have hp : ¬i<p := by omega
    simp [bit_ren,bitMask,h,hp]
theorem Run.transport {p n q r s} (h : Run (bitMask (p+n)) (bitMask p) q r s) (tag : Nat) :
    Run (bitMask (p+n)) (bitMask p) q r (s.map (ren p n tag)) := by
  have good {a b v : Nat} (op : v = a &&& b ∨ v = a ||| b) :
      ren p n tag v = ren p n tag a &&& ren p n tag b ∨ ren p n tag v = ren p n tag a ||| ren p n tag b :=
    op.elim (fun e=>Or.inl (e ▸ ren_and p n tag a b)) (fun e=>Or.inr (e ▸ ren_or p n tag a b))
  induction h with
  | done mem => apply Run.done;simpa only [ren_goal] using Multiset.mem_map_of_mem (ren p n tag) mem
  | merge op _ ih => simp only [Multiset.map_cons] at ih ⊢; exact .merge (good op) ih
  | reuse op _ ih => simp only [Multiset.map_cons] at ih ⊢; exact .reuse (good op) ih
  | both op _ ih => simp only [Multiset.map_cons] at ih ⊢; exact .both (good op) ih
  | flip _ ih => simp only [Multiset.map_cons,ren_xor,ren_mask] at ih ⊢; exact .flip ih
  | copyFlip _ ih => simp only [Multiset.map_cons,ren_xor,ren_mask] at ih ⊢; exact .copyFlip ih
theorem Run.need_le {mask goal q r s} (h : Run mask goal q r s) : r≤ q := by
  induction h <;> omega
end SixSigned
end Source22

section Source23
namespace SixSigned
abbrev State := Nat × Nat × List Nat
def notOpts (mask q k a : Nat) (t : List Nat) : List State :=
 if 0<q ∧ 0<k then [(q-1,k-1,(mask ^^^ a)::t)] ++
    (if 1<q then [(q-2,k-1,(mask ^^^ a)::a::t)] else []) else []
end SixSigned
end Source23

section Source24
namespace SixSigned
def All (P : Nat→Prop) (s : Multiset Nat) := ∀ x∈s,P x
def Ordered (p n w : Nat) := w.testBit p=true → w.testBit n=true
def RowLE (s : Multiset Nat) (p n : Nat) := All (Ordered p n) s
private theorem all_cons {P : Nat→Prop} {a : Nat} {s : Multiset Nat} :
    All P (a ::ₘ s) ↔ P a ∧ All P s := by
  constructor
  · intro h
    exact ⟨h a (by simp),fun x hx=>h x (by simp [hx])⟩
  · rintro ⟨ha,hs⟩ x hx
    rcases Multiset.mem_cons.mp hx with rfl|hx
    · exact ha
    · exact hs _ hx
private theorem order_gate {a b v p n : Nat} (op : v=(a &&& b) ∨ v=(a ||| b))
    (one : Ordered p n a) (two : Ordered p n b) : Ordered p n v := by
  rcases op with rfl|rfl <;>
    cases ha : a.testBit p <;> cases hb : b.testBit p <;>
    cases hx : a.testBit n <;> cases hy : b.testBit n <;>
    simp_all [Ordered,Nat.testBit_and,Nat.testBit_or]
private theorem branches {P : Nat→Prop} {a b v : Nat} {s : Multiset Nat}
    (h : All P (a ::ₘ b ::ₘ s)) (closed : P a → P b → P v) :
    All P (v ::ₘ s) ∧ All P (v ::ₘ a ::ₘ s) ∧ All P (v ::ₘ a ::ₘ b ::ₘ s) := by
  simp only [all_cons] at h ⊢
  have hv:=closed h.1 h.2.1
  exact ⟨⟨hv,h.2.2⟩,⟨hv,h.1,h.2.2⟩,⟨hv,h⟩⟩
theorem Run.zero_order {mask goal q r s} (h : Run mask goal q r s) (p n : Nat)
    (zero : r=0) (le : RowLE s p n) : Ordered p n goal := by
  induction h with
  | done hit => exact le _ hit
  | merge op _ ih => exact ih zero (branches le (order_gate op)).1
  | reuse op _ ih => exact ih zero (branches le (order_gate op)).2.1
  | both op _ ih => exact ih zero (branches le (order_gate op)).2.2
  | flip _ _ => omega
  | copyFlip _ _ => omega
theorem Run.no_drop {mask target q s p n} (h : Run mask target q 0 s)
    (hp : target.testBit p=true) (hn : target.testBit n=false) : ¬RowLE s p n := by
  intro le
  exact Bool.false_ne_true (hn.symm.trans (h.zero_order p n rfl le hp))
theorem Run.distinct_rows {mask target q r s p n} (h : Run mask target q r s)
    (mm : mask.testBit p=mask.testBit n) (ne : target.testBit p≠target.testBit n) :
    ¬(∀w∈s,w.testBit p=w.testBit n) := by
  let P : Nat→Prop := fun w=>w.testBit p=w.testBit n
  have closed {a b v : Nat} (op : v=(a &&& b) ∨ v=(a ||| b)) (aok : P a) (bok : P b) : P v := by
    dsimp [P] at aok bok ⊢
    rcases op with rfl|rfl <;> simp only [Nat.testBit_and,Nat.testBit_or,aok,bok]
  have neg {a : Nat} (good : P a) : P (mask ^^^ a) := by
    dsimp [P] at good ⊢
    simp only [Nat.testBit_xor,mm,good]
  change ¬All P s
  intro all
  induction h with
  | done mem => exact ne (all _ mem)
  | merge op _ ih => exact ih (branches all (closed op)).1
  | reuse op _ ih => exact ih (branches all (closed op)).2.1
  | both op _ ih => exact ih (branches all (closed op)).2.2
  | flip _ ih => exact ih (all_cons.mpr ⟨neg (all_cons.mp all).1,(all_cons.mp all).2⟩)
  | copyFlip _ ih => exact ih (all_cons.mpr ⟨neg (all_cons.mp all).1,all⟩)
private theorem one_inverted {mask a p0 n0 p1 n1 : Nat}
    (mp0 : mask.testBit p0=true) (mn0 : mask.testBit n0=true)
    (mp1 : mask.testBit p1=true) (mn1 : mask.testBit n1=true)
    (middle : Ordered n0 p1 a) :
    Ordered p0 n0 (mask ^^^ a) ∨ Ordered p1 n1 (mask ^^^ a) := by
  cases l : a.testBit n0 <;> cases h : a.testBit p1 <;>
    cases i : a.testBit p0 <;> cases j : a.testBit n1 <;>
    simp_all [Ordered,Nat.testBit_xor]
theorem Run.one_preserves {mask target q r s p0 n0 p1 n1} (h : Run mask target q r s)
    (one : r=1) (mp0 : mask.testBit p0=true) (mn0 : mask.testBit n0=true)
    (mp1 : mask.testBit p1=true) (mn1 : mask.testBit n1=true)
    (u : RowLE s p0 n0) (v : RowLE s n0 p1) (w : RowLE s p1 n1) :
    Ordered p0 n0 target ∨ Ordered p1 n1 target := by
  induction h with
  | done _ => omega
  | merge op _ ih => exact ih one (branches u (order_gate op)).1 (branches v (order_gate op)).1 (branches w (order_gate op)).1
  | reuse op _ ih => exact ih one (branches u (order_gate op)).2.1 (branches v (order_gate op)).2.1 (branches w (order_gate op)).2.1
  | both op _ ih => exact ih one (branches u (order_gate op)).2.2 (branches v (order_gate op)).2.2 (branches w (order_gate op)).2.2
  | @flip q r a rest next _ =>
    rcases one_inverted mp0 mn0 mp1 mn1 (all_cons.mp v).1 with h|h
    · exact Or.inl (next.zero_order _ _ (by omega) (all_cons.mpr ⟨h,(all_cons.mp u).2⟩))
    · exact Or.inr (next.zero_order _ _ (by omega) (all_cons.mpr ⟨h,(all_cons.mp w).2⟩))
  | @copyFlip q r a rest next _ =>
    rcases one_inverted mp0 mn0 mp1 mn1 (all_cons.mp v).1 with h|h
    · exact Or.inl (next.zero_order _ _ (by omega) (all_cons.mpr ⟨h,u⟩))
    · exact Or.inr (next.zero_order _ _ (by omega) (all_cons.mpr ⟨h,w⟩))
theorem Run.no_double_drop {mask target q s p0 n0 p1 n1} (h : Run mask target q 1 s)
    (hp0 : target.testBit p0=true) (hn0 : target.testBit n0=false)
    (hp1 : target.testBit p1=true) (hn1 : target.testBit n1=false)
    (mp0 : mask.testBit p0=true) (mn0 : mask.testBit n0=true)
    (mp1 : mask.testBit p1=true) (mn1 : mask.testBit n1=true) :
    ¬(RowLE s p0 n0 ∧ RowLE s n0 p1 ∧ RowLE s p1 n1) := by
  rintro ⟨a,b,c⟩
  rcases h.one_preserves rfl mp0 mn0 mp1 mn1 a b c with bad|bad
  · exact Bool.false_ne_true (hn0.symm.trans (bad hp0))
  · exact Bool.false_ne_true (hn1.symm.trans (bad hp1))
end SixSigned
end Source24

section Source25
namespace SixSignedPrune
open SixSigned
def up (xs : List Nat) (p acc : Nat) : Nat :=
  List.rec (motive:=fun _=>Nat→Nat) id
    (fun x _ rest cur=>if x.testBit p then rest (cur &&& x) else rest cur) xs acc
def same (xs : List Nat) (p acc : Nat) : Nat :=
  List.rec (motive:=fun _=>Nat→Nat) id
    (fun x _ rest cur=>if x.testBit p then rest (cur &&& x) else rest (cur ^^^ (cur &&& x))) xs acc
def anyRow (n : Nat) (f : Nat→Bool) : Bool := Nat.rec false (fun i earlier=>f i || earlier) n
def negativeMask (ps ns : Nat) := (2^(ps+ns)-1) ^^^ (2^ps-1)
def collect (xs : List Nat) (neg n startP startN : Nat) : Nat × Nat :=
  Nat.rec (motive:=fun _=>Nat→Nat→Nat×Nat) (fun a b=>(a,b))
    (fun p rest a b=>let now:=up xs p neg
                     if now==0 then rest a b else rest (a ||| (2^p)) (b ||| now)) n startP startN
def reject (ps ns r : Nat) (xs : List Nat) : Bool :=
  let neg:=negativeMask ps ns
  if r==0 then anyRow ps (fun p=>up xs p neg != 0)
  else if r==1 then
    let d:=collect xs neg ps 0 0
    anyRow ns (fun i=> d.2.testBit (ps+i) && (up xs (ps+i) d.1 != 0))
  else anyRow ps (fun p=>same xs p neg != 0)
private theorem up_sound {xs : List Nat} {p acc i : Nat} (h : (up xs p acc).testBit i=true) :
    acc.testBit i=true ∧ RowLE (↑xs : Multiset Nat) p i := by
  induction xs generalizing acc with
  | nil=>exact ⟨h,by simp [RowLE,All]⟩
  | cons w xs ih =>
    change (if w.testBit p then up xs p (acc &&& w) else up xs p acc).testBit i=true at h
    by_cases wp : w.testBit p=true
    · rw [if_pos wp] at h
      obtain ⟨a,b⟩:=ih h
      rw [Nat.testBit_and,Bool.and_eq_true] at a
      refine ⟨a.1,?_⟩
      intro x mem
      rcases List.mem_cons.mp (show x∈w::xs from mem) with rfl|tail
      · exact fun _=>a.2
      · exact b _ tail
    · rw [if_neg wp] at h
      obtain ⟨a,b⟩:=ih h
      refine ⟨a,?_⟩
      intro x mem
      rcases List.mem_cons.mp (show x∈w::xs from mem) with rfl|tail
      · exact fun yes=>(wp yes).elim
      · exact b _ tail
private theorem same_sound {xs : List Nat} {p acc i : Nat} (h : (same xs p acc).testBit i=true) :
    acc.testBit i=true ∧ ∀w∈(↑xs : Multiset Nat),w.testBit p=w.testBit i := by
  induction xs generalizing acc with
  | nil=>exact ⟨h,by simp⟩
  | cons w xs ih =>
    change (if w.testBit p then same xs p (acc &&& w) else same xs p (acc ^^^ (acc &&& w))).testBit i=true at h
    by_cases wp : w.testBit p=true
    · rw [if_pos wp] at h
      obtain ⟨a,b⟩:=ih h
      rw [Nat.testBit_and,Bool.and_eq_true] at a
      refine ⟨a.1,?_⟩
      intro x mem;rcases List.mem_cons.mp (show x∈w::xs from mem) with rfl|tail
      · exact wp.trans a.2.symm
      · exact b _ tail
    · rw [if_neg wp] at h
      obtain ⟨a,b⟩:=ih h
      rw [Nat.testBit_xor,Nat.testBit_and] at a
      have z : acc.testBit i=true ∧ w.testBit i=false := by cases u:acc.testBit i <;> cases v:w.testBit i <;> simp_all
      refine ⟨z.1,?_⟩
      intro x mem;rcases List.mem_cons.mp (show x∈w::xs from mem) with rfl|tail
      · rw [z.2];exact Bool.not_eq_true _ |>.mp wp
      · exact b _ tail
private theorem any_sound (f : Nat→Bool) (n : Nat) (h : anyRow n f=true) : ∃i<n,f i=true := by
  induction n with
  | zero=>contradiction
  | succ n ih=>
    change (f n || anyRow n f)=true at h
    rcases Bool.or_eq_true_iff.mp h with last|old
    · exact ⟨n,by omega,last⟩
    · obtain ⟨i,lt,on⟩:=ih old;exact ⟨i,by omega,on⟩
private theorem neg_range {ps ns i : Nat} (hit : (negativeMask ps ns).testBit i=true) :
    ps≤ i ∧ i<ps+ns := by
  simp only [negativeMask,Nat.testBit_xor,Nat.testBit_two_pow_sub_one] at hit
  by_cases lo : i<ps <;> by_cases hi : i<ps+ns <;> simp_all <;> omega
private theorem collect_pos (xs : List Nat) (neg n : Nat) :
    ∀ a b i,(collect xs neg n a b).1.testBit i=true → a.testBit i=true ∨ (i<n ∧ up xs i neg≠0) := by
  induction n with
  | zero=>intro a b i h;exact Or.inl h
  | succ n ih=>
    intro a b i h
    by_cases zero : up xs n neg=0
    · change (if up xs n neg==0 then collect xs neg n a b else _).1.testBit i=true at h
      simp only [zero,beq_self_eq_true,ite_true] at h
      exact (ih a b i h).imp_right fun z=>⟨by omega,z.2⟩
    · change (if up xs n neg==0 then collect xs neg n a b else collect xs neg n (a ||| 2^n) (b ||| up xs n neg)).1.testBit i=true at h
      simp only [beq_iff_eq,zero,ite_false] at h
      rcases ih _ _ i h with old|⟨lt,on⟩
      · rw [Nat.testBit_or,Bool.or_eq_true] at old
        rcases old with old|newbit
        · exact Or.inl old
        · have eq : n=i := by simpa [Nat.testBit_two_pow] using newbit
          subst i;exact Or.inr ⟨by omega,zero⟩
      · exact Or.inr ⟨by omega,on⟩
private theorem collect_neg (xs : List Nat) (neg n : Nat) :
    ∀a b i,(collect xs neg n a b).2.testBit i=true → b.testBit i=true ∨ ∃p<n,(up xs p neg).testBit i=true := by
  induction n with
  | zero=>intro a b i h;exact Or.inl h
  | succ n ih=>
    intro a b i h
    by_cases zero : up xs n neg=0
    · change (if up xs n neg==0 then collect xs neg n a b else _).2.testBit i=true at h
      simp only [zero,beq_self_eq_true,ite_true] at h
      rcases ih _ _ i h with old|⟨p,lt,on⟩
      · exact Or.inl old
      · exact Or.inr ⟨p,by omega,on⟩
    · change (if up xs n neg==0 then collect xs neg n a b else collect xs neg n (a ||| 2^n) (b ||| up xs n neg)).2.testBit i=true at h
      simp only [beq_iff_eq,zero,ite_false] at h
      rcases ih _ _ i h with old|⟨p,lt,on⟩
      · rw [Nat.testBit_or,Bool.or_eq_true] at old
        exact old.imp_right fun v=>⟨n,by omega,v⟩
      · exact Or.inr ⟨p,by omega,on⟩
theorem reject_sound {ps ns r : Nat} {xs : List Nat} {q : Nat}
    (bad : reject ps ns r xs=true) : ¬Run (2^(ps+ns)-1) (2^ps-1) q r (↑xs : Multiset Nat) := by
  intro run
  have on (i : Nat) (good : i<ps) : (2^ps-1:Nat).testBit i=true := by simp [good]
  have off (i : Nat) (no : ps≤ i) : (2^ps-1:Nat).testBit i=false := by simp;omega
  have mask (i : Nat) (inside : i<ps+ns) : (2^(ps+ns)-1:Nat).testBit i=true := by simp [inside]
  by_cases zero : r=0
  · subst r
    simp only [reject,beq_self_eq_true,ite_true] at bad
    obtain ⟨p,lt,witness⟩:=any_sound _ _ bad
    obtain ⟨i,hit⟩:=Nat.exists_testBit_of_ne_zero (bne_iff_ne.mp witness)
    obtain ⟨n,le⟩:=up_sound hit
    exact run.no_drop (on p lt) (off i (neg_range n).1) le
  by_cases one : r=1
  · subst r
    simp only [reject,show ((1:Nat)==0)=false from rfl,beq_self_eq_true,ite_false,ite_true,Bool.false_eq_true] at bad
    obtain ⟨i,lt,good⟩:=any_sound _ _ bad
    obtain ⟨nh,next⟩:=Bool.and_eq_true_iff.mp good
    obtain ⟨p,pl,up0⟩:=(collect_neg xs _ ps 0 0 (ps+i) nh).resolve_left (by simp)
    obtain ⟨q1,mid⟩:=Nat.exists_testBit_of_ne_zero (bne_iff_ne.mp next)
    obtain ⟨p1,le1⟩:=up_sound mid
    obtain ⟨ql,nonempty⟩:=(collect_pos xs _ ps 0 0 q1 p1).resolve_left (by simp)
    obtain ⟨n1,hit⟩:=Nat.exists_testBit_of_ne_zero nonempty
    obtain ⟨n0,le0⟩:=up_sound up0
    obtain ⟨n2,le2⟩:=up_sound hit
    exact run.no_double_drop (on _ pl) (off _ (by omega)) (on _ ql) (off _ (neg_range n2).1)
      (mask _ (by omega)) (mask _ (by omega)) (mask _ (by omega)) (mask _ (neg_range n2).2) ⟨le0,le1,le2⟩
  · simp [reject,zero,one] at bad
    obtain ⟨p,lt,witness⟩:=any_sound _ _ bad
    obtain ⟨i,hit⟩:=Nat.exists_testBit_of_ne_zero (bne_iff_ne.mp witness)
    obtain ⟨n,agree⟩:=same_sound hit
    exact run.distinct_rows ((mask p (by omega)).trans (mask i (neg_range n).2).symm)
      (by rw [on _ lt,off _ (neg_range n).1];decide) agree
end SixSignedPrune
end Source25

section Source26
namespace SixSigned
def renamedState (p n t : Nat) (v : State) : State :=
  (v.1,v.2.1,(List.insertionSort (·≤·) (v.2.2.map (ren p n t))))
def MRun (p n : Nat) (v : State) := Run (bitMask (p+n)) (bitMask p) v.1 v.2.1 (v.2.2 : Multiset Nat)
theorem moved {p n v} (h : MRun p n v) (t : Nat) : MRun p n (renamedState p n t v) := by
  have go := h.transport t
  change Run _ _ _ _ (↑(List.insertionSort (·≤·) (v.2.2.map (ren p n t))) : Multiset Nat)
  rw [Multiset.coe_eq_coe.mpr (List.perm_insertionSort _ _)]
  exact go
end SixSigned
end Source26

section Source27
namespace SixSigned
def symmetricOpts (q k v a b : Nat) (t : List Nat) : List State :=
 [(q,k,v::t)] ++ (if 0<q then [(q-1,k,v::a::t),(q-1,k,v::b::t)] else []) ++
 (if 1<q then [(q-2,k,v::a::b::t)] else [])
def halfNexts (mask q k : Nat) (xs : List Nat) : List State :=
 xs.flatMap fun a =>
    let tail:=xs.erase a
    notOpts mask q k a tail ++ tail.flatMap fun b =>
      if a≤ b then [a &&& b,a ||| b].flatMap fun v=>symmetricOpts q k v a b (tail.erase b) else []
private theorem pop1 (xs : List Nat) (a : Nat) (r : Multiset Nat)
    (e : (xs : Multiset Nat)=a ::ₘ r) : a∈xs ∧ ((xs.erase a : List Nat) : Multiset Nat)=r :=
 ⟨Multiset.mem_coe.mp (e ▸ Multiset.mem_cons_self _ _),by rw [←Multiset.coe_erase,e,Multiset.erase_cons_head]⟩
private theorem halfBin {mask q k a b v : Nat} {xs : List Nat} {r : Multiset Nat} {out : List Nat→State}
    (eq : (xs : Multiset Nat)=a ::ₘ b ::ₘ r) (ab : a≤ b) (op : v=a &&& b ∨ v=a ||| b)
    (mem : ∀tail,out tail∈symmetricOpts q k v a b tail) :
    ∃t : List Nat, ↑t=r ∧ out t∈halfNexts mask q k xs := by
  obtain ⟨ha,z⟩:=pop1 xs a _ eq
  obtain ⟨hb,tail⟩:=pop1 _ b _ z
  refine ⟨_,tail,List.mem_flatMap.mpr ⟨a,ha,List.mem_append_right _ (List.mem_flatMap.mpr ⟨b,hb,?_⟩)⟩⟩
  simp only [ab,ite_true]
  exact List.mem_flatMap.mpr ⟨v,by simpa using op,mem _⟩
private theorem binOrder {q k a b v : Nat} {xs : List Nat} {r : Multiset Nat} {P : Prop}
    (eq : (xs : Multiset Nat)=a ::ₘ b ::ₘ r) (op : v=a &&& b ∨ v=a ||| b)
    (direct : (xs : Multiset Nat)=a ::ₘ b ::ₘ r → a≤ b → (v=a &&& b ∨ v=a ||| b) → P)
    (reverse : (xs : Multiset Nat)=b ::ₘ a ::ₘ r → b≤ a → (v=b &&& a ∨ v=b ||| a) → P) : P := by
  by_cases ab:a≤ b
  · exact direct eq ab op
  · exact reverse (eq.trans (Multiset.cons_swap a b r)) (by omega)
      (by simpa only [Nat.and_comm b a,Nat.or_comm b a] using op)
private theorem unaryHalf {mask q k a : Nat} {xs : List Nat} {s : State}
   (ha : a∈xs) (mem : s∈notOpts mask q k a (xs.erase a)) : s∈halfNexts mask q k xs :=
   List.mem_flatMap.mpr ⟨a,ha,List.mem_append_left _ mem⟩
theorem next_half (mask goal q k : Nat) (xs : List Nat) (h : Run mask goal q k (xs : Multiset Nat))
    (no : k=0 → goal∉xs) : ∃ s∈halfNexts mask q k xs, Run mask goal s.1 s.2.1 (s.2.2 : Multiset Nat) := by
  generalize eq : (xs : Multiset Nat)=ss at h
  cases h with
  | done hit => exact (no rfl (Multiset.mem_coe.mp (eq.symm ▸ hit))).elim
  | @merge q k a b v r op hn =>
    apply binOrder (q:=q) (k:=k) eq op <;> intro e le same
    all_goals
      obtain ⟨t,tail,mem⟩:=halfBin (mask:=mask) (q:=q) (k:=k) (out:=fun t=>(q,k,v::t)) e le same
        (by intro t;simp [symmetricOpts])
      exact ⟨_,mem,by change Run mask goal q k (v ::ₘ ↑t);rwa [tail]⟩
  | @reuse q k a b v r op hn =>
    apply binOrder (q:=q) (k:=k) eq op <;> intro e le same
    all_goals
      obtain ⟨t,tail,mem⟩:=halfBin (mask:=mask) (q:=q+1) (k:=k) (out:=fun t=>(q,k,v::a::t)) e le same
        (by intro t;simp [symmetricOpts])
      exact ⟨_,mem,by change Run mask goal q k (v ::ₘ a ::ₘ ↑t);rwa [tail]⟩
  | @both q k a b v r op hn =>
    apply binOrder (q:=q) (k:=k) eq op <;> intro e le same
    · obtain ⟨t,tail,mem⟩:=halfBin (mask:=mask) (q:=q+2) (k:=k) (out:=fun t=>(q,k,v::a::b::t)) e le same
        (by intro t;simp [symmetricOpts])
      exact ⟨_,mem,by change Run mask goal q k (v ::ₘ a ::ₘ b ::ₘ ↑t);rwa [tail]⟩
    · obtain ⟨t,tail,mem⟩:=halfBin (mask:=mask) (q:=q+2) (k:=k) (out:=fun t=>(q,k,v::b::a::t)) e le same
        (by intro t;simp [symmetricOpts])
      exact ⟨_,mem,by change Run mask goal q k (v ::ₘ b ::ₘ a ::ₘ ↑t);rwa [tail,Multiset.cons_swap b a r]⟩
  | @flip q k a r hn =>
    obtain ⟨ha,tail⟩:=pop1 xs a r eq
    refine ⟨(q,k,(mask ^^^ a)::xs.erase a),unaryHalf ha (by simp [notOpts]),?_⟩
    change Run mask goal q k ((mask ^^^ a) ::ₘ (↑(xs.erase a) : Multiset Nat));rwa [tail]
  | @copyFlip q k a r hn =>
    obtain ⟨ha,tail⟩:=pop1 xs a r eq
    refine ⟨(q,k,(mask ^^^ a)::a::xs.erase a),unaryHalf ha (by simp [notOpts]),?_⟩
    change Run mask goal q k ((mask ^^^ a) ::ₘ a ::ₘ (↑(xs.erase a) : Multiset Nat));rwa [tail]
end SixSigned
end Source27

section Source28
namespace SixG
structure Witness where
  i : Nat
  j : Nat
  p : Nat
  n : Nat
  ni : Nat
  nj : Nat
  pi : Nat
  pj : Nat
  deriving Inhabited
def fillRows (width ones : Nat) : Nat→Nat→Nat
  | 0,_ => 0
  | k+1,v => (if v%2=1 then ones else 0) ||| ((fillRows width ones k (v/2)) <<< width)
def grid (p n unit u : Nat) (signed : Bool) : Nat :=
  let g:=2^n-1
  let rows:=fillRows (n+1) g p u
  let ns:=(u >>> p) &&& g
  let replicated:=ns*unit
  if signed then rows ^^^ replicated else rows &&& ((g*unit) ^^^ replicated)
def onces (all : List Nat) : Nat :=
  let (covered,many):=all.foldl (fun (z : Nat×Nat) w=>(z.1 ||| w,z.2 ||| (z.1 &&& w))) (0,0)
  covered ^^^ many
def foldCols (width : Nat) : Nat→Nat→Nat
  | 0,v => v
  | k+1,v => foldCols width k (v ||| (v >>> (width*(1 <<< k))))
structure Project where
  mat : Nat
  pos : Nat
  neg : Nat
def projected (n ps hi : Nat) (v : Nat) : Project :=
  ⟨v,hi ^^^ ((hi-v) &&& hi),(foldCols (n+1) ps v) &&& (2^n-1)⟩
def makeWitness (n unit i j : Nat) (a b : Project) : Option Witness :=
  let pp:=a.pos &&& b.pos
  let nn:=a.neg &&& b.neg
  if pp=0 ∨ nn=0 then none else
    let width:=n+1
    let p:=pp.log2/width
    let c:=nn.log2
    let atRow:=fun (v : Nat) => ((v >>> (p*width)) &&& (2^n-1)).log2
    let atCol:=fun (v : Nat) => (v &&& (unit <<< c)).log2/width
    some ⟨i,j,p,c,atRow a.mat,atRow b.mat,atCol a.mat,atCol b.mat⟩
def against (n unit i : Nat) (a : Project) : Nat→List Project→Option Witness
  | _,[] => none
  | j,b::bs => match makeWitness n unit i j a b with
    | some w => some w
    | none => against n unit i a (j+1) bs
def search (n unit : Nat) : Nat→List Project→Option Witness
  | _,[] => none
  | i,a::xs => match against n unit i a (i+1) xs with
    | some w => some w
    | none => search n unit (i+1) xs
def hint (p n : Nat) (signed : Bool) (xs : List Nat) : Option Witness :=
  let width:=n+1
  let unit:=(2^(width*p)-1)/(2^width-1)
  let grids:=xs.map (fun w => grid p n unit w signed)
  let one:=onces grids
  let hi:=unit <<< n
  search n unit 0 (grids.map fun w=>projected n (p-1).log2.succ hi (w &&& one))
end SixG
end Source28

section Source29
namespace SixRO
inductive Form
  | atom (i : Nat) (neg : Bool)
  | both (l r : Form)
  | either (l r : Form)
def Form.vars : Form → Multiset Nat
  | .atom i _ => {i}
  | .both l r | .either l r => l.vars+r.vars
def Form.eval : Form → (Nat→Bool) → Bool
  | .atom i n,x => x i ^^ n
  | .both l r,x => l.eval x && r.eval x
  | .either l r,x => l.eval x || r.eval x
def Form.monoEval : Form → (Nat→Bool) → Bool
  | .atom i _,x => x i
  | .both l r,x => l.monoEval x && r.monoEval x
  | .either l r,x => l.monoEval x || r.monoEval x
def Form.dual : Form → Form
  | .atom i n => .atom i (!n)
  | .both l r => .either l.dual r.dual
  | .either l r => .both l.dual r.dual
def Form.plain : Form → Bool
  | .atom _ n => !n
  | .both l r | .either l r => l.plain && r.plain
def Form.orient : Form → Nat → Bool
  | .atom j n,i => decide (i=j) && n
  | .both l r,i | .either l r,i => l.orient i || r.orient i
theorem Form.vars_dual (f : Form) : f.dual.vars=f.vars := by
  induction f <;> simp_all [dual,vars]
theorem Form.eval_dual (f : Form) (x : Nat→Bool) : f.dual.eval x = !f.eval x := by
  induction f with
  | atom i n => cases x i <;> cases n <;> simp_all [dual,eval]
  | both l r il ir => simp [dual,eval,il,ir]
  | either l r il ir => simp [dual,eval,il,ir]
end SixRO
end Source29

section Source30
namespace SixRO
def Form.yesCert : Form → (Nat → Bool) → Finset Nat
  | .atom i _, _ => {i}
  | .both l r, x => l.yesCert x ∪ r.yesCert x
  | .either l r, x => if l.monoEval x then l.yesCert x else r.yesCert x
def Form.noCert : Form → (Nat → Bool) → Finset Nat
  | .atom i _, _ => {i}
  | .both l r, x => if l.monoEval x then r.noCert x else l.noCert x
  | .either l r, x => l.noCert x ∪ r.noCert x
private theorem yes_mem (f : Form) (x : Nat → Bool) (on : f.monoEval x=true) :
    ∀ i∈f.yesCert x, i∈f.vars ∧ x i=true := by
  induction f with
  | atom i n => simpa [Form.yesCert,Form.vars,Form.monoEval] using on
  | both a b ia ib =>
    simp only [Form.monoEval,Bool.and_eq_true] at on
    intro i hi
    rcases Finset.mem_union.mp hi with h|h
    · exact ⟨Multiset.mem_add.mpr (Or.inl (ia on.1 i h).1),(ia on.1 i h).2⟩
    · exact ⟨Multiset.mem_add.mpr (Or.inr (ib on.2 i h).1),(ib on.2 i h).2⟩
  | either a b ia ib =>
    intro i hi
    cases ha : a.monoEval x with
    | false =>
      have hb : b.monoEval x=true := by simpa [Form.monoEval,ha] using on
      have h := ib hb i (by simpa [Form.yesCert,ha] using hi)
      exact ⟨Multiset.mem_add.mpr (Or.inr h.1),h.2⟩
    | true =>
      have h := ia ha i (by simpa [Form.yesCert,ha] using hi)
      exact ⟨Multiset.mem_add.mpr (Or.inl h.1),h.2⟩
private theorem no_mem (f : Form) (x : Nat → Bool) (off : f.monoEval x=false) :
    ∀ i∈f.noCert x, i∈f.vars ∧ x i=false := by
  induction f with
  | atom i n => simpa [Form.noCert,Form.vars,Form.monoEval] using off
  | either a b ia ib =>
    have h : a.monoEval x=false ∧ b.monoEval x=false := by
      simpa [Form.monoEval] using off
    intro i hi
    rcases Finset.mem_union.mp hi with h'|h'
    · exact ⟨Multiset.mem_add.mpr (Or.inl (ia h.1 i h').1),(ia h.1 i h').2⟩
    · exact ⟨Multiset.mem_add.mpr (Or.inr (ib h.2 i h').1),(ib h.2 i h').2⟩
  | both a b ia ib =>
    intro i hi
    cases ha : a.monoEval x with
    | false =>
      have h := ia ha i (by simpa [Form.noCert,ha] using hi)
      exact ⟨Multiset.mem_add.mpr (Or.inl h.1),h.2⟩
    | true =>
      have hb : b.monoEval x=false := by simpa [Form.monoEval,ha] using off
      have h := ib hb i (by simpa [Form.noCert,ha] using hi)
      exact ⟨Multiset.mem_add.mpr (Or.inr h.1),h.2⟩
private def Cross (a b : Finset Nat) := ∃! i, i∈a ∧ i∈b
private theorem cross_swap {a b : Finset Nat} (h : Cross a b) : Cross b a := by
  obtain ⟨i,hit,only⟩ := h
  exact ⟨i,hit.symm,fun j hj=>only j hj.symm⟩
private theorem cross_add {a b c : Finset Nat} (h : Cross a b)
    (diff : ∀i∈c,i∉b) : Cross (a∪c) b := by
  obtain ⟨i,hit,only⟩ := h
  refine ⟨i,⟨Finset.mem_union_left _ hit.1,hit.2⟩,?_⟩
  intro j hj
  rcases Finset.mem_union.mp hj.1 with l|r
  · exact only j ⟨l,hj.2⟩
  · exact (diff j r hj.2).elim
theorem Form.cert_intersection (f : Form) (simple : f.vars.Nodup) (x y : Nat → Bool)
    (on : f.monoEval x=true) (off : f.monoEval y=false) :
    ∃! i, i∈f.yesCert x ∧ i∈f.noCert y := by
  change Cross _ _
  induction f with
  | atom i n => exact ⟨i,by simp [yesCert,noCert],fun j h=>by simpa [yesCert] using h.1⟩
  | both a b ia ib =>
    obtain ⟨na,nb,disj⟩ := Multiset.nodup_add.mp simple
    have dj {i : Nat} (hi : i∈a.vars) : i∉b.vars := Multiset.disjoint_left.mp disj hi
    have hx : a.monoEval x=true ∧ b.monoEval x=true := by simpa [monoEval] using on
    cases ha : a.monoEval y with
    | false =>
      simp only [yesCert,noCert,ha,Bool.false_eq_true,ite_false]
      exact cross_add (ia na hx.1 ha) fun i hi hj =>
        dj ((no_mem a y ha i hj).1) ((yes_mem b x hx.2 i hi).1)
    | true =>
      have hb : b.monoEval y=false := by simpa [monoEval,ha] using off
      simp only [yesCert,noCert,ha,ite_true]
      rw [Finset.union_comm]
      exact cross_add (ib nb hx.2 hb) fun i hi hj =>
        dj ((yes_mem a x hx.1 i hi).1) ((no_mem b y hb i hj).1)
  | either a b ia ib =>
    obtain ⟨na,nb,disj⟩ := Multiset.nodup_add.mp simple
    have dj {i : Nat} (hi : i∈a.vars) : i∉b.vars := Multiset.disjoint_left.mp disj hi
    have hy : a.monoEval y=false ∧ b.monoEval y=false := by
      simpa [monoEval] using off
    cases ha : a.monoEval x with
    | true =>
      simp only [yesCert,noCert,ha,ite_true]
      apply cross_swap
      exact cross_add (cross_swap (ia na ha hy.1)) fun i hi hj =>
        dj ((yes_mem a x ha i hj).1) ((no_mem b y hy.2 i hi).1)
    | false =>
      have hb : b.monoEval x=true := by simpa [monoEval,ha] using on
      simp only [yesCert,noCert,ha,Bool.false_eq_true,ite_false]
      rw [Finset.union_comm]
      apply cross_swap
      exact cross_add (cross_swap (ib nb hb hy.2)) fun i hi hj =>
        dj ((no_mem a y hy.1 i hi).1) ((yes_mem b x hb i hj).1)
def separates (x y : Nat → Bool) (i : Nat) : Prop := x i=true ∧ y i=false
def OnlySep (k : Nat) (x y : Nat → Bool) (i : Fin k) : Prop :=
  ∀ j : Fin k, separates x y j → j=i
theorem Form.gurvich {k : Nat} (f : Form) (simple : f.vars.Nodup)
    (bdd : ∀ i∈f.vars,i<k) {P N : Type*} (pos : P → Nat → Bool) (neg : N → Nat → Bool)
    (accept : ∀p,f.monoEval (pos p)=true) (reject : ∀n,f.monoEval (neg n)=false) :
    (∀p n, ∃ i : Fin k, separates (pos p) (neg n) i) ∧
    ∀ (p : P) (n : N) (i j : Fin k),
      (∃ t, OnlySep k (pos p) (neg t) i) → (∃ t, OnlySep k (pos p) (neg t) j) →
      (∃ t, OnlySep k (pos t) (neg n) i) → (∃ t, OnlySep k (pos t) (neg n) j) → i=j := by
  have hit (p : P) (n : N) : ∃ i : Fin k,
      i.val∈f.yesCert (pos p) ∧ i.val∈f.noCert (neg n) ∧ separates (pos p) (neg n) i := by
    obtain ⟨i,⟨hi,hn⟩,_⟩ := f.cert_intersection simple _ _ (accept p) (reject n)
    have left := yes_mem f _ (accept p) i hi
    exact ⟨⟨i,bdd i left.1⟩,hi,hn,left.2,(no_mem f _ (reject n) i hn).2⟩
  refine ⟨fun p n=>by obtain ⟨i,_,_,hdl⟩ := hit p n; exact ⟨i,hdl⟩,?_⟩
  intro p n i j pi pj ni nj
  have fp (h : Fin k) : (∃ t, OnlySep k (pos p) (neg t) h) → h.val∈f.yesCert (pos p) := by
    rintro ⟨t,ht⟩
    obtain ⟨v,hy,_,sep⟩ := hit p t
    simpa [←ht v sep] using hy
  have fnn (h : Fin k) : (∃ t, OnlySep k (pos t) (neg n) h) → h.val∈f.noCert (neg n) := by
    rintro ⟨t,ht⟩
    obtain ⟨v,_,hn,sep⟩ := hit t n
    simpa [←ht v sep] using hn
  obtain ⟨v,_,only⟩ := f.cert_intersection simple _ _ (accept p) (reject n)
  exact Fin.ext ((only i.val ⟨fp i pi,fnn i ni⟩).trans (only j.val ⟨fp j pj,fnn j nj⟩).symm)
def WeakSep (signed : Bool) (x y : Nat → Bool) (i : Nat) : Prop :=
  if signed then x i ≠ y i else separates x y i
def OnlyWeakSep (k : Nat) (signed : Bool) (x y : Nat → Bool) (i : Fin k) : Prop :=
  ∀ j : Fin k, WeakSep signed x y j → j=i
theorem Form.weak_gurvich {k : Nat} (f : Form) (simple : f.vars.Nodup)
    (bdd : ∀ i∈f.vars,i<k) (signed : Bool) (z : Nat → Bool)
    (plain : signed=false → ∀i,z i=false) {P N : Type*}
    (pos : P → Nat → Bool) (neg : N → Nat → Bool)
    (accept : ∀p,f.monoEval (fun i => pos p i ^^ z i)=true)
    (reject : ∀n,f.monoEval (fun i => neg n i ^^ z i)=false) :
    (∀p n, ∃ i : Fin k, WeakSep signed (pos p) (neg n) i) ∧
    ∀ (p : P) (n : N) (i j : Fin k),
      (∃t, OnlyWeakSep k signed (pos p) (neg t) i) →
      (∃t, OnlyWeakSep k signed (pos p) (neg t) j) →
      (∃t, OnlyWeakSep k signed (pos t) (neg n) i) →
      (∃t, OnlyWeakSep k signed (pos t) (neg n) j) → i=j := by
  let px := fun p i => pos p i ^^ z i
  let nx := fun n i => neg n i ^^ z i
  obtain ⟨hit,force⟩ := f.gurvich simple bdd px nx accept reject
  have weak (p n i) : separates (px p) (nx n) i → WeakSep signed (pos p) (neg n) i := by
    intro ⟨hp,hn⟩
    cases h : signed with
    | false =>
      simpa [WeakSep,h,separates,px,nx,plain h i] using And.intro hp hn
    | true =>
      simp only [WeakSep,ite_true]
      intro e
      change (pos p i ^^ z i) = true at hp
      change (neg n i ^^ z i) = false at hn
      rw [e,hn] at hp
      contradiction
  have cv (p n i) (m : OnlyWeakSep k signed (pos p) (neg n) i) : OnlySep k (px p) (nx n) i :=
    fun j hj=>m j (weak p n j hj)
  constructor
  · intro p n
    obtain ⟨i,hi⟩ := hit p n
    exact ⟨i,weak p n i hi⟩
  · rintro p n i j ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩ ⟨d,hd⟩
    exact force p n i j ⟨a,cv _ _ _ ha⟩ ⟨b,cv _ _ _ hb⟩ ⟨c,cv _ _ _ hc⟩ ⟨d,cv _ _ _ hd⟩
end SixRO
end Source30

section Source31
namespace SixRO
open SixSigned
private def Rep (mask : Nat) (xs : List Nat) (wf : Nat × Form) := ∀i,mask.testBit i=true →
  wf.1.testBit i=wf.2.eval (fun k=>(xs.getD k 0).testBit i)
private def uses (wf : Nat × Form) := wf.2.vars
private def Keeps (plain : Bool) (mask : Nat) (xs : List Nat) (wf : Nat × Form) :=
  Rep mask xs wf ∧ (plain=true → wf.2.plain=true)
private theorem unpack {b : Multiset (Nat×Form)} {a : Nat} {s : Multiset Nat}
    (eq : b.map Prod.fst=a ::ₘ s) :
    ∃f rest, b=(a,f) ::ₘ rest ∧ rest.map Prod.fst=s := by
  have mem : a∈b.map Prod.fst := by rw [eq];simp
  obtain ⟨⟨v,t⟩,ht,hv⟩:=Multiset.mem_map.mp mem
  change v=a at hv
  subst v
  obtain ⟨rest,hr⟩:=Multiset.exists_cons_of_mem ht
  rw [hr,Multiset.map_cons] at eq
  exact ⟨t,rest,hr,(Multiset.cons_inj_right a).mp eq⟩
private theorem join_form {plain mask a b v xs f g}
    (op : v=(a &&& b) ∨ v=(a ||| b)) (hf : Keeps plain mask xs (a,f)) (hg : Keeps plain mask xs (b,g)) :
    ∃t, t.vars=f.vars+g.vars ∧ Keeps plain mask xs (v,t) := by
  rcases op with rfl|rfl
  · refine ⟨Form.both f g,rfl,?_,?_⟩
    · intro i hi; exact (Nat.testBit_and ..).trans (congrArg₂ Bool.and (hf.1 i hi) (hg.1 i hi))
    · intro hp; simp only [Form.plain,hf.2 hp,hg.2 hp,Bool.true_and]
  · refine ⟨Form.either f g,rfl,?_,?_⟩
    · intro i hi; exact (Nat.testBit_or ..).trans (congrArg₂ Bool.or (hf.1 i hi) (hg.1 i hi))
    · intro hp; simp only [Form.plain,hf.2 hp,hg.2 hp,Bool.true_and]
private theorem reserve {mask target q r s} (h : Run mask target q r s) : r≤ q := by induction h <;> omega
private theorem consume {mask target q r s} (run : Run mask target q r s) (eq : q=r)
    (plain : Bool) (zero : plain=true → r=0) (xs : List Nat)
    (b : Multiset (Nat×Form)) (wiring : b.map Prod.fst=s)
    (good : ∀wf∈b,Keeps plain mask xs wf) :
    ∃f : Form,f.vars ≤ b.bind uses ∧ Keeps plain mask xs (target,f) := by
  induction run generalizing b with
  | done hit =>
    have mem : target∈b.map Prod.fst := wiring ▸ hit
    obtain ⟨⟨v,f⟩,hf,eqv⟩:=Multiset.mem_map.mp mem
    change v=target at eqv
    subst v
    exact ⟨f,Multiset.le_bind b hf,good _ hf⟩
  | @merge q r a b' v s op _ ih =>
    obtain ⟨f,d,rfl,old⟩:=unpack wiring
    obtain ⟨g,rest,rfl,base⟩:=unpack old
    have hf:=good (a,f) (by simp)
    have hg:=good (b',g) (by simp)
    obtain ⟨h,ub,ok⟩:=join_form op hf hg
    have keepWF : ∀p∈(v,h) ::ₘ rest,Keeps plain mask xs p := by
      intro p hp
      rcases Multiset.mem_cons.mp hp with rfl|hp
      · exact ok
      · exact good p (by simp [hp])
    obtain ⟨z,sz,correct⟩:=ih eq zero ((v,h) ::ₘ rest) (by simp [base]) keepWF
    refine ⟨z,?_,correct⟩
    simpa only [Multiset.cons_bind,uses,ub,add_assoc] using sz
  | @reuse q r _ _ _ _ _ next _ =>
    have := reserve next
    omega
  | @both q r _ _ _ _ _ next _ =>
    have := reserve next
    omega
  | @flip q r a s next ih =>
    obtain ⟨f,rest,rfl,hr⟩:=unpack wiring
    have hf:=good (a,f) (by simp)
    have changed : Keeps plain mask xs (mask ^^^ a,f.dual) := by
      constructor
      · intro i hi
        change (mask ^^^ a).testBit i=_
        rw [Nat.testBit_xor,hi,Form.eval_dual,hf.1 i hi]
        simp
      · intro hp; have := zero hp;omega
    have preserve : ∀p∈(mask ^^^ a,f.dual) ::ₘ rest,Keeps plain mask xs p := by
      intro p hp
      rcases Multiset.mem_cons.mp hp with rfl|hp
      · exact changed
      · exact good p (by simp [hp])
    obtain ⟨z,sz,correct⟩:=ih (by omega) (fun hp=>by have:=zero hp;omega)
      ((mask ^^^ a,f.dual) ::ₘ rest) (by simp [hr]) preserve
    exact ⟨z,by simpa only [Multiset.cons_bind,uses,Form.vars_dual] using sz,correct⟩
  | @copyFlip q r _ _ next _ =>
    have := reserve next
    omega
theorem formula_of_run {mask goal q} (xs : List Nat)
    (h : Run mask goal q q (xs : Multiset Nat)) :
    ∃ f : Form, f.vars ≤ Multiset.range xs.length ∧
      (q=0 → f.plain=true) ∧ ∀i,mask.testBit i=true →
        goal.testBit i=f.eval (fun k=>(xs.getD k 0).testBit i) := by
  let ids := List.range xs.length
  let make (i : Nat) : Nat×Form := (xs.getD i 0,.atom i false)
  let b : Multiset (Nat×Form) := (ids.map make : List (Nat×Form))
  have wire : b.map Prod.fst=(xs : Multiset Nat) := by
    have l : (ids.map make).map Prod.fst=xs := by
      apply List.ext_getElem
      · simp [ids]
      · intro i hi hj
        simp only [List.getElem_map,List.getElem_range,ids,make]
        rw [List.getD_eq_getElem _ _ hj]
    exact congrArg (fun z : List Nat=>(z : Multiset Nat)) l
  have ok : ∀p∈b, Keeps (decide (q=0)) mask xs p := by
    intro p hp
    change p∈(↑(ids.map make):Multiset (Nat×Form)) at hp
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp (Multiset.mem_coe.mp hp)
    exact ⟨fun i _=>by simp [make,Form.eval],fun _=>rfl⟩
  obtain ⟨f,sub,rf⟩:=consume h rfl (decide (q=0)) (fun eq=>of_decide_eq_true eq) xs b wire ok
  have allVars : b.bind uses=Multiset.range xs.length := by
    change (Multiset.map make (Multiset.range xs.length)).bind uses = _
    simp only [Multiset.bind_map,uses,make,Form.vars]
    exact (Multiset.bind_singleton (s:=Multiset.range xs.length) id).trans (Multiset.map_id _)
  exact ⟨f,allVars ▸ sub,fun z=>rf.2 (by simp [z]),rf.1⟩
end SixRO
end Source31

section Source32
namespace SixRO
open SixSigned
theorem Form.mono_congr (f : Form) (x y : Nat→Bool)
    (agree : ∀i∈f.vars,x i=y i) : f.monoEval x=f.monoEval y := by
  induction f with
  | atom i tag => exact agree i (by simp [vars])
  | both l r li ri =>
    exact congrArg₂ Bool.and (li (fun i hi=>agree i (by simp [vars,hi])))
      (ri (fun i hi=>agree i (by simp [vars,hi])))
  | either l r li ri =>
    exact congrArg₂ Bool.or (li (fun i hi=>agree i (by simp [vars,hi])))
      (ri (fun i hi=>agree i (by simp [vars,hi])))
theorem Form.not_oriented (f : Form) (i : Nat) (absent : i∉f.vars) : f.orient i=false := by
  induction f with
  | atom j n =>
    have ne : i≠j := by simpa [vars] using absent
    simp [orient,ne]
  | both l r li ri =>
    simp only [vars,Multiset.mem_add,not_or] at absent
    simp [orient,li absent.1,ri absent.2]
  | either l r li ri =>
    simp only [vars,Multiset.mem_add,not_or] at absent
    simp [orient,li absent.1,ri absent.2]
theorem Form.plain_orientation (f : Form) (h : f.plain=true) (i : Nat) : f.orient i=false := by
  induction f <;> simp_all [plain,orient]
private theorem branch_orient (l r : Form) (x : Nat→Bool) (no : Disjoint l.vars r.vars) :
    l.monoEval (fun i=>x i ^^ l.orient i)=l.monoEval (fun i=>x i ^^ (l.orient i || r.orient i)) ∧
    r.monoEval (fun i=>x i ^^ r.orient i)=r.monoEval (fun i=>x i ^^ (l.orient i || r.orient i)) := by
  constructor
  · apply Form.mono_congr
    intro i hi
    rw [r.not_oriented i ((Multiset.disjoint_left.mp no) hi),Bool.or_false]
  · apply Form.mono_congr
    intro i hi
    rw [l.not_oriented i ((Multiset.disjoint_left.mp no.symm) hi),Bool.false_or]
theorem Form.oriented_eval (f : Form) (simple : f.vars.Nodup) (x : Nat→Bool) :
    f.eval x=f.monoEval (fun i=>x i ^^ f.orient i) := by
  induction f with
  | atom i n => simp [eval,monoEval,orient]
  | both l r li ri =>
    obtain ⟨ld,rd,no⟩:=Multiset.nodup_add.mp simple
    obtain ⟨le,re⟩:=branch_orient l r x no
    exact congrArg₂ Bool.and ((li ld).trans le) ((ri rd).trans re)
  | either l r li ri =>
    obtain ⟨ld,rd,no⟩:=Multiset.nodup_add.mp simple
    obtain ⟨le,re⟩:=branch_orient l r x no
    exact congrArg₂ Bool.or ((li ld).trans le) ((ri rd).trans re)
theorem oriented_of_run {mask goal q} (xs : List Nat) (h : Run mask goal q q (xs : Multiset Nat)) :
    ∃ f : Form, f.vars.Nodup ∧ (∀j∈f.vars,j<xs.length) ∧
      (q=0 → ∀j,f.orient j=false) ∧
      ∀i,mask.testBit i=true →
        goal.testBit i=f.monoEval (fun j=>(xs.getD j 0).testBit i ^^ f.orient j) := by
  obtain ⟨f,sub,plain,ok⟩:=formula_of_run xs h
  have unique:=Multiset.nodup_of_le sub (Multiset.nodup_range _)
  refine ⟨f,unique,fun j hj=>Multiset.mem_range.mp (Multiset.mem_of_le sub hj),?_,?_⟩
  · intro zero j;exact f.plain_orientation (plain zero) j
  · intro i hi;exact (ok i hi).trans (f.oriented_eval unique _)
end SixRO
end Source32

section Source33
namespace SixRO
def posRow {ps : Nat} (xs : List Nat) (p : Fin ps) (i : Nat) : Bool :=
  (xs.getD i 0).testBit p.val
def negRow (ps : Nat) {ns : Nat} (xs : List Nat) (n : Fin ns) (i : Nat) : Bool :=
  (xs.getD i 0).testBit (ps+n.val)
def WeakSamples (ps ns : Nat) (signed : Bool) (xs : List Nat) : Prop :=
  (∀ (p : Fin ps) (n : Fin ns), ∃i : Fin xs.length, WeakSep signed (posRow xs p) (negRow ps xs n) i) ∧
  ∀ (p : Fin ps) (n : Fin ns) (i j : Fin xs.length),
    (∃t : Fin ns, OnlyWeakSep xs.length signed (posRow xs p) (negRow ps xs t) i) →
    (∃t : Fin ns, OnlyWeakSep xs.length signed (posRow xs p) (negRow ps xs t) j) →
    (∃t : Fin ps, OnlyWeakSep xs.length signed (posRow xs t) (negRow ps xs n) i) →
    (∃t : Fin ps, OnlyWeakSep xs.length signed (posRow xs t) (negRow ps xs n) j) → i=j
theorem weak_of_run (ps ns q : Nat) (xs : List Nat)
    (h : SixSigned.Run (2^(ps+ns)-1) (2^ps-1) q q (xs : Multiset Nat)) :
    WeakSamples ps ns (decide (q≠0)) xs := by
  obtain ⟨f,unique,bdd,zero,ok⟩ := oriented_of_run xs h
  apply f.weak_gurvich unique bdd (decide (q≠0)) f.orient
  · intro eq
    exact zero (by simpa using eq)
  · intro p
    have a : p.val<ps+ns := by omega
    have e := ok p.val (by simpa [Nat.testBit_two_pow_sub_one] using a)
    exact e.symm.trans (by simp [Nat.testBit_two_pow_sub_one,p.isLt])
  · intro n
    have a : ps+n.val<ps+ns := by omega
    have e := ok (ps+n.val) (by simpa [Nat.testBit_two_pow_sub_one] using a)
    exact e.symm.trans (by simp [Nat.testBit_two_pow_sub_one])
end SixRO
end Source33

section Source34
namespace SixRO
def rowPattern : List Nat → Nat → Nat
  | [], _ => 0
  | w::ws, a => Nat.bit (w.testBit a) (rowPattern ws a)
theorem rowPattern_bit (xs : List Nat) (a i : Nat) :
    (rowPattern xs a).testBit i = (xs.getD i 0).testBit a := by
  induction xs generalizing i with
  | nil => simp [rowPattern]
  | cons w ws ih =>
    cases i with
    | zero => simp [rowPattern,Nat.testBit_bit_zero]
    | succ i => simpa [rowPattern,Nat.testBit_bit_succ] using ih i
def pairDiff (signed : Bool) (u v : Nat) : Nat := if signed then u ^^^ v else u &&& (u ^^^ v)
private theorem diff_bit {ps ns : Nat} (xs : List Nat) (signed : Bool) (p : Fin ps) (n : Fin ns) (i : Nat) :
    (pairDiff signed (rowPattern xs p.val) (rowPattern xs (ps+n.val))).testBit i=true ↔
      WeakSep signed (posRow xs p) (negRow ps xs n) i := by
  cases signed <;>
    simp only [pairDiff,WeakSep,Bool.false_eq_true,ite_false,ite_true,Nat.testBit_and,Nat.testBit_xor,
      rowPattern_bit,posRow,negRow,separates] <;>
    cases (xs.getD i 0).testBit p.val <;> cases (xs.getD i 0).testBit (ps+n.val) <;> decide
theorem weak_diff_unique {ps ns signed xs} (h : WeakSamples ps ns signed xs) (p : Fin ps) (n : Fin ns) (i j : Nat)
    (hiP : ∃t : Fin ns, pairDiff signed (rowPattern xs p.val) (rowPattern xs (ps+t.val)) = 2^i)
    (hjP : ∃t : Fin ns, pairDiff signed (rowPattern xs p.val) (rowPattern xs (ps+t.val)) = 2^j)
    (hiN : ∃t : Fin ps, pairDiff signed (rowPattern xs t.val) (rowPattern xs (ps+n.val)) = 2^i)
    (hjN : ∃t : Fin ps, pairDiff signed (rowPattern xs t.val) (rowPattern xs (ps+n.val)) = 2^j) : i=j := by
  have atBit (a : Fin ps) (b : Fin ns) (k : Nat)
      (eq : pairDiff signed (rowPattern xs a.val) (rowPattern xs (ps+b.val))=2^k)
      (v : Fin xs.length) (hv : WeakSep signed (posRow xs a) (negRow ps xs b) v) : v.val=k := by
    have bit := (diff_bit xs signed a b v).mpr hv
    rw [eq,Nat.testBit_two_pow] at bit
    exact (of_decide_eq_true bit).symm
  obtain ⟨a,ha⟩ := hiP
  obtain ⟨b,hb⟩ := hjP
  obtain ⟨c,hc⟩ := hiN
  obtain ⟨d,hd⟩ := hjN
  obtain ⟨u,hu⟩ := h.1 p a
  obtain ⟨v,hv⟩ := h.1 p b
  have ui := atBit p a i ha u hu
  have vj := atBit p b j hb v hv
  have uv := h.2 p n u v
    ⟨a,fun w hw=>Fin.ext ((atBit p a i ha w hw).trans ui.symm)⟩
    ⟨b,fun w hw=>Fin.ext ((atBit p b j hb w hw).trans vj.symm)⟩
    ⟨c,fun w hw=>Fin.ext ((atBit c n i hc w hw).trans ui.symm)⟩
    ⟨d,fun w hw=>Fin.ext ((atBit d n j hd w hw).trans vj.symm)⟩
  exact ui.symm.trans ((congrArg Fin.val uv).trans vj)
end SixRO
end Source34

section Source35
namespace SixG
def valid (ps ns : Nat) (signed : Bool) (xs : List Nat) (w : Witness) : Bool :=
  let d := fun (p n : Nat)=>SixRO.pairDiff signed (SixRO.rowPattern xs p) (SixRO.rowPattern xs (ps+n))
  decide (w.i≠w.j ∧ w.p<ps ∧ w.n<ns ∧ w.ni<ns ∧ w.nj<ns ∧ w.pi<ps ∧ w.pj<ps) &&
    decide (d w.p w.ni=2^w.i ∧ d w.p w.nj=2^w.j ∧ d w.pi w.n=2^w.i ∧ d w.pj w.n=2^w.j)
theorem valid_sound {ps ns q xs w}
    (h : valid ps ns (decide (q≠0)) xs w=true) :
    ¬SixSigned.Run (2^(ps+ns)-1) (2^ps-1) q q (xs : Multiset Nat) := by
  intro run
  have sample := SixRO.weak_of_run ps ns q xs run
  simp only [valid,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with ⟨⟨ij,p,n,ni,nj,pi,pj⟩,a,b,c,d⟩
  exact ij (SixRO.weak_diff_unique sample ⟨w.p,p⟩ ⟨w.n,n⟩ w.i w.j
    ⟨⟨w.ni,ni⟩,a⟩ ⟨⟨w.nj,nj⟩,b⟩ ⟨⟨w.pi,pi⟩,c⟩ ⟨⟨w.pj,pj⟩,d⟩)
def reject (ps ns q : Nat) (xs : List Nat) : Bool :=
  match hint ps ns (decide (q≠0)) xs with
  | none => false
  | some w => valid ps ns (decide (q≠0)) xs w
theorem reject_sound {ps ns q xs} (bad : reject ps ns q xs=true) :
    ¬SixSigned.Run (2^(ps+ns)-1) (2^ps-1) q q (xs : Multiset Nat) := by
  unfold reject at bad
  split at bad
  · contradiction
  · exact valid_sound bad
end SixG
end Source35

section Source36
namespace SixSigned
def blocked (p n : Nat) (x : State) : Bool :=
  if x.1 < x.2.1 then true else if SixSignedPrune.reject p n x.2.1 x.2.2 then true else
    (x.1==x.2.1) && SixG.reject p n x.1 x.2.2
theorem blocked_sound {p n x} (ok : blocked p n x=true) : ¬MRun p n x := by
  intro h
  unfold blocked at ok
  split at ok
  · have := h.need_le;omega
  split at ok
  · rename_i bad
    exact SixSignedPrune.reject_sound bad h
  rw [Bool.and_eq_true,beq_iff_eq] at ok
  have run:=h
  change Run (2^(p+n)-1) (2^p-1) x.1 x.2.1 (x.2.2 : Multiset Nat) at run
  rw [←ok.1] at run
  exact SixG.reject_sound ok.2 run
def scan (p n tagBits width : Nat) (tags : Nat→Nat) (rows : Nat→State) (i : Nat) :
    List State→Nat→Bool
  | [],_ => true
  | x::xs,marks =>
    if blocked p n x then scan p n tagBits width tags rows i xs marks else
     let entry:=marks%2^width
     let j:=entry >>> tagBits
     let tag:=tags (entry%2^tagBits)
     decide (j < i) && (rows j==renamedState p n tag x) &&
       scan p n tagBits width tags rows i xs (marks >>> width)
private theorem scan_sound {p n tagBits width tags rows i xs marks} (ok : scan p n tagBits width tags rows i xs marks=true)
    {x : State} (mem : x∈xs) (run : MRun p n x) : ∃ j < i, MRun p n (rows j) := by
  induction xs generalizing marks with
  | nil => simp at mem
  | cons a tail ih =>
    rw [scan] at ok
    split at ok
    · rename_i bad
      rcases List.mem_cons.mp mem with rfl|inTail
      · exact (blocked_sound bad run).elim
      · exact ih ok inTail
    · simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at ok
      rcases List.mem_cons.mp mem with rfl|inTail
      · exact ⟨_,ok.1.1,(congrArg (MRun p n) ok.1.2).mpr (moved run _)⟩
      · exact ih ok.2 inTail
def closedRow (p n tagBits width : Nat) (tags : Nat→Nat) (rows : Nat→State) (marks : Nat→Nat) (i : Nat) : Bool :=
  let x:=rows i
  (x.2.1!=0 || !x.2.2.contains (bitMask p)) &&
   scan p n tagBits width tags rows i (halfNexts (bitMask (p+n)) x.1 x.2.1 x.2.2) (marks i)
theorem avoid_closed (p n tagBits width : Nat) (tags : Nat→Nat) (rows : Nat→State)
    (marks : Nat→Nat) (bound : Nat) (ok : ∀i<bound,closedRow p n tagBits width tags rows marks i=true)
    (j : Nat) (limit : j<bound) : ¬MRun p n (rows j) := by
  induction j using Nat.strong_induction_on with
  | ind i ih =>
    intro h
    have tested:=ok i limit
    simp only [closedRow,Bool.and_eq_true] at tested
    have absent (r:(rows i).2.1=0) : bitMask p∉(rows i).2.2 := by intro seen;simp [r,seen] at tested
    obtain ⟨s,mem,step⟩:=next_half _ _ _ _ _ h absent
    obtain ⟨a,lt,run⟩:=scan_sound tested.2 mem step
    exact ih a lt (lt_trans lt limit) run
end SixSigned
end Source36

section Source37
namespace SixRowsData
open Nat (blt)
abbrev State := Nat × Nat × List Nat
def a1Pack0 (i : Nat) : Nat :=
  bif blt i 8 then bif blt i 4 then bif blt i 2 then bif blt i 1 then 0x2f71540 else 0x13326a51816c84
  else bif blt i 3 then 0x5ae35adce486a1a108e827432a3851c09f130797bcb1e52d29613b0a564c7242128c9844e131803a82920080430 else 0x14c4da868
  else bif blt i 6 then bif blt i 5 then 0x9ec4a1b349b2411a89b18da98109a3389a20559004908d801000 else 0x78bb59ab598a698986798579457935798479937985781278616769766b7522755245816485738a725712500185905250573050200020
  else bif blt i 7 then 0x3a2e8c741a18e8ac31d12c628630b130c112c521a57a4389f00674590e251e1c4b34389a60742cc0e25981d0a303d2c586720a0e23121906103d48187b8c20ed1841c42083a82087a0000e2518145230189c602825902271c0087380 else 0xd265a317cc4205187bca30e18c41c114838021070c61ce8bf11ae3de314c3062d85cc6a6a98d51331c7a063543cc6a6798e3cf31c91862992cc71e298d4dd2da9a65b5334b52ac14a4d82989a8529344a626614a4d02463104186207
  else bif blt i 12 then bif blt i 10 then bif blt i 9 then 0x8a4fb313df67893ccf0f799b34c3367d766cda8cc5f499b3e8b3184f674d5ac49ab588b56b1a5a46349c8c6937588b2db1a65a634c34c691598bb54af17e25e4d58b6938d68b562b17aa52cdd29d9aa53d2722717e24b49ba8e93591 else 0x8bcfb534dd6a29bad69871a8b0db517996a2d32d65a5dab34bb517956a309ed46139aa4783368ef66cdd6cd1ea59b3b4b3672966cdd2cc5fa198bf3b357e6662fccce939998c113347e266cfc2cb9285971f0b313e06630becc587d9
  else bif blt i 11 then 0x22d530c62ba08b52bf16a47e27b6fe1a91ed2d23da4e47a2d52ed9aa5c8bd53717a96e2fc4dc4f79b9c783516ad6a2ed8d4dab1a9bd53537a96a2fccd45a99ab350b4a621694942d28f85a else 0xbaa8fb4e9693f118e212c3e977dd6fac1d563465629ab4b16b4ad4c55b293b10861da534c462a8ae292a0219839906f18c031d4231184430428010e0
  else bif blt i 14 then bif blt i 13 then 0x149f653ebebc84b6fb6996d3e3a7bf55765e9c42577caefa5a93ad555 else 0x397db5965f3b2a946005a1024de4c1d2617ca08a5010a4048202680
  else bif blt i 15 then 0x155be31458558c5155be114556f805155bdf14556f40554e0c814556f14515548214555108515530214554a0851552421455480851551c215de0108553804214598108514b0421451810851450421450c108514104214500108508b1811553832041611080ca8432031610c80ca843202155c63055383200 else 0x155c1234556f48d155bde30556f68c155bd930554324c14b0c431538320b16fc92285bb248a54e0c8285543209155c5e2055433481550cb2055432884da0c821538320816e0c420555200815544020554b0081552802055480081551c020554000854e0c81c556f8c6155be21822c6486295be314656f8c5
def a1Pack1 (i : Nat) : Nat :=
  bif blt i 24 then bif blt i 20 then bif blt i 18 then bif blt i 17 then 0xd5bd25c5d954972a10c85c556f0d72a10c85953832162a10c855368321454e0c85055432131550c848555c8d11551484455442112950c844554321154e0c84552032110440c84455431d11550c6445dc211114208444008211115a0c840a84320f4da0c83c568320f54e0c83d528320f4da0c839538320e else 0x155612a058554a8155bd1a055714a754e0c89953832252a10c89153832242a10c88c51c32221470c884a84322028b0c880a1c32201470c880524321f2a10c878a84321d155bdc705c2f49c155bd270456f49c155a1270585549c155bdd6ca84321a54e0c868a843219155bd2605caf497171bd25c56ef497
  else bif blt i 19 then 0x54e612ac58574ab161592aca8554ab221552ac58554ab0e1552ac58154ab15f552ac55154ab153552ad53954ab78a552aca8544ab54e4d2ad53924ab54e412ad368f4ab54e3d2aca84e4ab54e392ad538d4ab2a10cfad53833eb2a10cead538332b54e0c8ac55ef4aa155bd5a55383229315bd2a0556f4a8 else 0x550bd2ad53af4ab54dbd2ad532f4ab195b92ac56ac4ab159b12ac56ab4ab54b992ad52e54ab54b912ad52e34ab54e892ad15614ab295852ac55614ab15e812ac57604ab15a812ac35604ab15e7d2ad369e4ab54e792ac585d4ab1616d2ad539a4ab54b692ac55594ab4da612ad35584ab495612ad05584ab
  else bif blt i 22 then bif blt i 21 then 0x569c12ad5a304ab567c12ad59b04ab565c12ad59304ab563c12ad58b04ab561c12ad54b04ab550c12ad53f04ab54ec12ad36af4ab49abd2ad06af4ab3dabd2ace6af4ab29abd2ad062f4ab3d8bd2acd5ef4ab196bd2acb56f4ab295bd2ac956f4ab215bd2ac756f4ab195bd2ac556f4ab552bd2ad546f4ab else 0x155a57ac556a5ab155bd4ac572f4eb295bd3ac856f4eb155bd3ac556d4eb161553ad8e734ab579cd2ae1eb04ab83ac12adfeb04ab7bac12addeb04ab73ac12adbeb04ab6bac12ad9eb04ab63ac12ad7eb04ab5bac12ad5eb04ab575c12ad5d304ab573c12ad5bf04ab56ec12ad5b704ab56cc12ad5af04ab
  else bif blt i 23 then 0x155be5b4556f92d155bd3b0d56f6eb16ac98ac656f62b155a18ac556762b else 0x71f2cc0b8f7a605ca3d202e51e781728f3a0b976dd05c292002f3dec0071ef60038f96801e7cb380e3e59c0d1cf4e068972701c84b000e3e58007212be03cf95f01c7caf80e51e7c071c9be038f49f01c7cad00e3e564071ef2c038f71501c7a6a00e3cb500392e1601ce4cb00e724580738b2c0
  else bif blt i 28 then bif blt i 26 then bif blt i 25 then 0x72e49833976cb18e4b458c72502c639471631c934b1a8b9258c82492c658a49632c10cb18e49c50da7de246728f12339724819608440ce5c91c670a488349714419c08220c52530c621298630834431b460a08ce3c004671ef5a29c96cb15c7bd688725b2c408229e1b8f79d09c7bd702e3deb41 else 0x72303a339379d19c93ce8d445e746722f3a344f79d19cbbae8ce5d8746392c3a33975dd1a8face8ce5d6746712b3a379f55d1a4baae8ce5d5746d12aba339749d19c21ee8ce5cd74672e63a338f99c19c7c2e0da25c706d129b836a4adb19e7bcc8da39e646d128b2338f79819cb92b8ce1893c6
  else bif blt i 27 then 0x71ef46339182219c8bd10d43de88671ef4433947e019ca3d00ce41e80671ef4033976e01a8fd6f0ce3e378671f0bc338f81e19c7bef0d051e786724f3c339179e1a07bcf0ce3d8786392c3c339755e19c7aaf0da25478671e93c3522add1acfd6e8d47eb7469bf5ba345fadd19cf56e8d47e2746 else 0x728f26838f79241c7bd69e725544e72e4a271c961135cd1289b21c53cd71ef0c6c8010534648a79820c538c71ef605b8f7962f438a795a30534ad00204500214d2744a7290e3de887abf5ba3b9179d1dcbaae8f67ebb46a3f5da349faed19c8bd68ce3deb0671ef56338f8651b44b928ce3e08c6
  else bif blt i 30 then bif blt i 29 then 0x7375baa38f45151cb928a9e14945470a4a2a2c52515042928a9a2484543923a2a38f45051cb9282810453d471ef5a9d0f9734927cb9a493e4cd2728fe6928f7ae4927bd72563deb52a1ef5a930f7ad48e4b70a4725c712a28f2691c214e49608a724725b312d4829e8b8f9734287c19a0e3deb50 else 0x71ef38b3917ad55ce4f2aba25c955a1ef44ab947e055ca3d02ae5db815828f3cab9cadd5688bceaae5dd755f36abaab8f99c5744b8e2a635e455d16f22ab9765155cb9a8aae5cc455390522ab98251562b928aab20945570c4a2af852515722928aad149455f04422af811d157448c8aae6e7954
  else bif blt i 31 then 0xa3f5eed397ab76b51d59b547e9cdaa1f066d3977b269c7bd935e7ebb5ab3f5dad51faed69cd576b4e45eb5a72eed4d3976ea6a87bd33543de89a72edc0d38f9b365c7cd832e3e5c1971f0e0ce8f7b065e7bd832e3dec1971f34ecb8f9676744b93b3a8eacd871ef5abedf9f359c7cd9ace3e5cd6 else 0xd1ef60fb8f7b07dc7bd6bd47e7cdd71ef5aeb9097371c7cb9b8e51fcdc72ef5ae38f7ad728fd7cb747ece1bd3f56edb97ab76f4fcfbb787e7ddba3f3eedb9a9f76e0fd59b70527cdb728fe6db8f7b16dc7bd836e527b9b7353dadd0f7a96dc7cb336e51e81b7292bedb9479f6dcedbd3547ece9a
def a1Pack2 (i : Nat) : Nat :=
  bif blt i 40 then bif blt i 36 then bif blt i 34 then bif blt i 33 then 0x7a93ef33949f799ca4fb4ce527d6683f5693394ab49a8fcf9cb47e7de472d3e71b949f38f4fd79c5a7eace272f5671394a338af1cf9c548a7ce2fbf3e7179f9f38bafcf9c5c7e7ce2b3f3e7155f9f38a8fcf9c4e7a7ce27353e713999f389c7c19c4e527ce1a3f57103949f781ca4f7c167e7b60 else 0x148a7de6a433ef35209f799cb4fbcce567de6
  else bif blt i 35 then 0xf0 else 0x5a48e13324609692304b431825a76e110b35096a9404b366c259634118b1009782602bbf30159f980acfcb0567e402b491c17e18c0d0b3a0567dc82b4edc159b680d0db30567d902b54a8159f3a0aef9c0567ce024b640121b20090d8f05f86300b4edc0
  else bif blt i 38 then bif blt i 37 then 0x2161a3ac30c1d69c58eb2c2c7586163ac28b1d60458e42c2872961238eb051c54428e2941471490a3acf841ce7c18eb000c7080063800031cf7c10e4060875a18c310b1118a5880cfbf18565f8c2aefc61567e30ab3ebc55a750290b101567e608b4edc3 else 0x5a7503a13a81d67940eb3aa0759a5039a7281d63140f616a07a194e3d0ca61e85920f42c8c7216443d0b201c858a8e3ac4c729622394c101cc5c80e5ac40729620392b101c85880e42440734f203904101cd1c80e68c40734520390b8e1cc5870e42c387
  else bif blt i 39 then 0x2162041a3102189238f1531877e28c3bf0c61d88630ecc11876208c3af0461de7e30ecbf1875df8c3acfc61e87230e4391875df8a3acfbe1d699e0eb4edc75df603acfb01d77d78eb4eb075a7563ad3a91d68d48e41ca47775503ad4281d99d40ebcea07 else 0x59f026ad24731692318bbf30b5a48e5bf0c62d67e216b3f0cba16745acfb92d69db96b0000b59f8c52cfc22a859994b3e78a2162052cfc624858812b431885a08c436fc621a7e310b3f18859f8442cfc12169db910beb485a75042d3a521658d90b0c648
  else bif blt i 44 then bif blt i 42 then bif blt i 41 then 0x2160caad3b751cc8ba880c5d45860ea2b6c64df9232742ce932167498a8b34c5449a63044d3a022692cfb74567db22b3e8510c2268d5a884567dc2042041059f7e7d0c973d77e61cbbf18e59f8472cfc03967df9cb4ca0e59f3e710a903885081d45e5cd else 0x5a76ef1ab3778859bbc42cd9e21b5cf10da978d3d43c2a26dea8436f18b9378d3c9bcc4919d5a48ce98fc674c589ba6844dc70226dac1136960893408241a7df8ccacfc6648589b34491987e18cc2d0c66086233042cc5829626c10b0a61c9cbaf23f196
  else bif blt i 43 then 0x79f8d1a6fc68d69dbc742c823727311d0d178e864bc69325e34592f1ceb178c758bc74265e3b0d2f190b148e858b454325e11062f0d16c682b7e33ea5945e36498f2d2477ae9233cc4919eaa18cf3f0c67896e33c62f19e21676f10b397a17dc3c42ce1e else 0x59f996ad247b589235ab3ee2d5a76f6ad247b1892358fc31ac5a77762d3b8b217dc58b4edec5a76d62cfcdad67e65742ceab5a76f53f0c6a569dbd35731a8a167543efc69d67e34d43f1a559f8d2d0b3a968599cab3f1a4a2b931b12478df8a346fc31a3
  else bif blt i 46 then bif blt i 45 then 0x835a3abfad1d5cd68eab654755aea3aad651d56ae8eab554755a7a3aad3ccd569e36ab4b1b55a38daad0c6d568236abbf1b559f8daacfbdd569dbeab3f1b471f8d9acfc6cdf7e364b3f33159f738acfb7c6859d60fbf1af5a48f72d246b969dbdcb4132d else 0xab69fcd3b4fe68da7f32ed3f98f69fcc3b4fe5fda7f2fe33f97ee9fcbf5cfe5fa27f2fcf3f97e49fcbf0cfe59aa772fd13b97e199cb2fcce577e672b492b97df91cb1247e56923f366b3b85a79dc2cfc6e167e36eb3f1b6b35a3ad5ad1d65d68eb0eb475
  else bif blt i 47 then 0x4da52e68ce97336f439a36a1cbf850e66e27f36ed3f9 else 0x89f6ee37536d39556c72b3a32fa89a001248
def a1Pack3 (i : Nat) : Nat :=
  bif blt i 56 then bif blt i 52 then bif blt i 50 then bif blt i 49 then 0xf61b3c3648aa551a13336408458300 else 0x8d0f61bbcb648aa551a13336408458300
  else bif blt i 51 then 0x3764b54900013a516a94591d3629498b5161b4581d16054580316072581d1207000 else 0xc522254050cca2214050cb222140520522214050c522214050cc8e214050cc82109850c502103850cc82102050c522214040c522254030c8a221403205222140318522214030c522214030c520214030cc8e2140300385214030c522213030c522214020c522354010c52b2140110522214010c522214010c521214010c522213810c5228000120522214000c522214000cc8e214000c502103800c52280000
  else bif blt i 54 then bif blt i 53 then 0xc5228098a0c5227c98a0c5224098a0c5228090a0c5228068a0c5222060a0c5228058a0c5228040aa304a8038a7304a8038a0d34a8038a0c5228038a0c50d8038a0c5224838a0c50c4838a0c50c1038a0c5061038a0c5021038a0c50c0438a0c5228020a0c5228008a0c5225008a0c5060008a0c5228000a0c522394090c522214090c522800090c522214080c522214070cc8e214070c522211070c52221406 else 0xcd4af648a0cccaf648a0c52bf648a0c522f648a0c522f248a0c522ba48a0c522a248a0c5228e48a0c5228648a0c5228248a0c5228238aa304af630a0c5228230a0c52281d8a0c52239d8a0c5228140a0c5227540a0c5225940a0c5223940a0c5223540a0c5223140a0c5222d40a205222140a105222140a0c5222140a0cc8e2140a0c5222128a0c5222108a0c5228100a0c5222100a0c5221d00a0c52280a0a
  else bif blt i 55 then 0xc5020c1120c502081120dbca214110c522214110c502103910c502101110c522214100c5222188f0c5442140f0c5222140f0c53b2140e0c5222140e0c51b2140e0c52220b0e0c5222140d0c5222140c0c51c2140c6c3912140c0c52220f0c0c5227df0b0c5222140b0c52220f8be304af648acf04af648aa704af648aa304af648a0e7caf648a0e14af648a0dbcaf648a0d74af648a0d34af648a0ce4af648a else 0xc519214120c518214120c517214126c391214120c510214120cc8e214120c502154120c522213920c522212120e14a210120c52220e920c52220e120e14a20d920c52220d920c51720d920c52220d120e14a20c920c502149920c382108120e14a207920c522205120e322204920c502103920c502102920e14a481920c522481920c506201920c506101920c502101920c501101920c503101120c50210112
  else bif blt i 60 then bif blt i 58 then bif blt i 57 then 0xe14a4df120e14a49f120c52b49f120c52b45f120e14a21d928f04a219128304a219120eb4a219120eaca219120d34a219120c522219120c506219120c522218920c522218120c522254120e14a214120dbca214120d94a214120c544214120c53f214120c53e214120c53b214120c52b214120c529214120c526214122052221412185222141210522214120c522214120c521214120c51d214120c51a21412 else 0xc52251f1d0c5224df1d0c52249f1d0c52245f1d0c52221d9d0c52221b9d0c5225141d0dbca2141d0c5222141d0c5222101d0c52220d9d0c52250c9d0dbca20c9d0c52220c9d0c5222079d0c5222141c0c5222141b0c5222141a0c522214190c522214180c522218170c522214176c391214170c52220d170c522214160c526214150c522214150c522214140c522214130e14a81f120e14a79f120e14a51f12
  else bif blt i 59 then 0xc7222142220522214220c522214220c515214220c513214226c391214220c510214220c70f214223050f214220c50f214220cc8e214220c70a21422003852142200284214220c702109a20c382108220c282108220cc82107220c502103a20c502103220c522214210c522214200c5292141f205222141f0c5222141f6c3912141f0c5102141f0c5222141e0eecaf629d0c5225221d0c52281f1d0c52279f1d else 0xc50210aa50c502109a50c502108a537002108250d302108250c382108250c182108250c102108250c082108250c000048250c502106a50c502105a50c502104250c502103a50e94a214240e14a214240ce4a214240ccca214240c522214240c50f214240c522214230c522254226f04d214220d04a214220ce4a214220ccca214220c9ca214220c74a214220c544214220c53f214220c52b214220c52621422
  else bif blt i 62 then bif blt i 61 then 0xd74a214250d34a214250d1ca214250cfca214250ce4a214250cd4a214250ccca214250c54a214250c549214250c52d214250c526214250c522214250c514214256c511214250c511214256c391214250c50e214250c50d214250c50c214250c50a214250c509214250c508214256c308214250c507214250c506214250c502194250c502154250c502114250c502111a50c502110250c50210da50c50210ca5 else 0xc522214276f5cd214266c526214260c5262142620522214260c522214266c4a2214266c422214260c516214266c392214266c411214266c3912142630510214260cc8e214260c522211260c52220f260ec4a81425e304a21425c704a21425b704a21425a304a214258704a214258304a214257704a214257304a214256f04a214250e7ca214250e34a214250e2ca214250e14a214250dbca214250d8ca21425
  else bif blt i 63 then 0xc522214373050f214370cc8e214370c522214360c5222143520522214340c522214340ea4af5f330e14af5f330d74af5f330c52221db30c522214330cc8e214330c52220bb30c522214320c522214310c522214300c5222142f0c5222142e0c7222142d205222142d0c5222142d0c51c2142d3050f2142d0cc8e2142d0c52220c2d205222142c0c5222142c0c5222142b0c5222142a0c522214290c52221428 else 0xc522214470c522214460c522214450c522214440c522214430c522214420c522214410c522214400c5222143f0c5222143e5f04af5f3d0efcaf5f3d0eecaf5f3d0eb4af5f3d0d34af5f3d0cccaf5f3d0c5223df3d0c5222143d0c522209bd0c5222143c0c5222143b0c52221dba0c5222143a0c52281f390c52221db90c522214390c522214380c52221db70c522219370c522218b70c722214372052221437
def a1Pack4 (i : Nat) : Nat :=
  bif blt i 72 then bif blt i 68 then bif blt i 66 then bif blt i 65 then 0xcc902145530510214553070f214553050f2145520c8e214550cc8e214550c522213550c5222115514522214540c522214541c522214530c522214532304d2145220ca22145220522214520c5222145220c8e214520cc8e214520c522214510c522214500cc8e214500c38e214500c20b214500c5222144f0c5222144e0c5222144d0cc8e2144d0c5222144c0c5222144b0c5222144a0c522214490c52221448 else 0xd74af5f5d205222145d0c5222145d0cc8e2145d0c5262145c0c5222145c6c3912145c0c5222145b0c5222145a0c522214590c522214580c522214570c522214560c522294550c522254556f5cd214552304d214556f0262145520ca22145530722214550c722214550c6a2214550c622214550c5a2214552052221455185222145510522214550c5222145504522214556c422214550c516214556c39321455
  else bif blt i 67 then 0xc522217660c522216e60c522216660c522215e60eeca215660c522215660c522214e620522214660c522214660cc8e214660e84af5f650e14af5f650c522214650c522214640c52281f630c52271f630c526214630c522214636c391214630c522214620c52221461b304af5f600ebcaf5f600eb4af5f600d34af5f600cccaf5f600c522214600c5222145f0e14af5f5e0d74af5f5e0c5222145e0d7caf5f5d else 0x6c39169f660cc8e69f660c52265f660c52261f660c7225df660c5225df666c3935df660cc8e5df660c52259f660c52255f660c52221ee60c52221e660c72221de62052221de60c52221de63050f21de60cc8e21de62052221d660c52221d660c52221ce60c52221c660c52221b660c52221ae60c52221a660852221a660c522219e60ee4a219660c522219660c522218e60c522218666c391218660c522217e6
  else bif blt i 70 then bif blt i 69 then 0x205228df66185228df660c5228df660c51f8df660c51e8df660c5158df660cc948df660cc938df663050f8df660cc8e8df660c82289f662052289f661852289f660c52289f660cc8e89f662052285f660c52285f660cc8e85f662052281f660c52281f660cc8e81f660c52671f660c52271f666c39171f660c5226df666c52669f660c52669f660c52469f662052269f660c52269f666c42269f666c41169f66 else 0x4f04d8df664704d8df663f04d8df663b04d8df663304d8df662b04d8df662704d8df662304d8df660f04d8df660ea4d8df660e7cd8df660e4cd8df660e14d8df660dbcd8df660d7cd8df660d74d8df660d4cd8df662134d8df660d34d8df660d14d8df660d04d8df660ce4d8df660cd4d8df660cccd8df660ccb28df6620ca28df660cca28df660cb228df660c8a28df660c8228df660c7a28df660c7228df66
  else bif blt i 71 then 0xdbcab9f660c53fb9f660c53eb9f660c526b9f6620522b9f6618522b9f660c522b9f660c51ab9f660c522b5f660c522b1f660c522adf660c522a9f660c522a5f660c522a1f666f5ca9df66b304a9df660dbca9df663134a9df660ccca9df66305229df66205229df660c5229df660c52299f660c52295f660c52291f66e304d8df66d704d8df66d304d8df66b304d8df66a304d8df665b04d8df665304d8df66 else 0xc522edf660c522e9f660c522e5f660d04ae1f660ce4ae1f660cccae1f660c522e1f660c522ddf660c522d9f660c522d5f660c526d1f660c522d1f668b04acdf666f04acdf660eb4acdf660e34acdf660d34acdf660c522cdf660c522c9f660ea4ac5f660e14ac5f660dbcac5f660ce4ac5f660cccac5f660c522c5f660e4cac1f660dbcac1f660cccac1f660c522c1f660e14abdf660dbcabdf660c522bdf66
  else bif blt i 76 then bif blt i 74 then bif blt i 73 then 0xc538f5f660c537f5f660c536f5f660c535f5f660c534f5f660c533f5f660c532f5f660c531f5f660c530f5f660c52ff5f660c52ef5f666c52cf5f660c52cf5f660c52bf5f660c52af5f660c529f5f660c528f5f660c527f5f666d326f5f666c526f5f660c526f5f660c525f5f660c524f5f660c523f5f6620522f5f660c522f5f66a704af1f660cccaf1f660c522f1f660e8caedf660e14aedf660cccaedf66 else 0xd04af5f660cf4af5f660cecaf5f6620e4af5f660ce4af5f660cdcaf5f6620d4af5f660cd4af5f6620ccaf5f660cccaf5f660cc4af5f660cbcaf5f660cacaf5f660ca4af5f660c9caf5f660c94af5f660c548f5f660c547f5f660c546f5f660c545f5f660c544f5f660c543f5f660c542f5f660c541f5f660c540f5f660c53ff5f660c53ef5f660c53df5f660c53cf5f660c53bf5f660c53af5f660c539f5f66
  else bif blt i 75 then 0xde4af5f660ddcaf5f660dd4af5f660dccaf5f660dc4af5f6621bcaf5f660dbcaf5f660db4af5f660dacaf5f660da4af5f660d9caf5f660d94af5f660d84af5f66217caf5f660d7caf5f662174af5f660d74af5f660d6caf5f660d64af5f660d5caf5f660d54af5f66214caf5f660d4caf5f660d44af5f660d3caf5f662134af5f661d34af5f661934af5f661134af5f660d34af5f660d24af5f660d0caf5f66 else 0xbb04af5f66b704af5f66b304af5f66ab04af5f66a704af5f66a304af5f669f04af5f660ea4af5f660e9caf5f660e94af5f660e8caf5f660e84af5f66227caf5f660e7caf5f660e74af5f66226caf5f660e6caf5f660e64af5f660e5caf5f660e54af5f660e4caf5f660e44af5f660e3caf5f660e24af5f660e1caf5f662214af5f660e14af5f660e0caf5f660e04af5f660dfcaf5f660df4af5f660decaf5f66
  else bif blt i 78 then bif blt i 77 then 0x9b34af5f666f34af5f666734af5f66af2caf5f66472caf5f66332caf5f66b324af5f663324af5f66e31caf5f66d71caf5f66d31caf5f66a31caf5f665b1caf5f66571caf5f66531caf5f664b1caf5f66471caf5f66431caf5f663f1caf5f663b1caf5f66331caf5f66231caf5f66db14af5f666b14af5f66df0caf5f66a30caf5f66830caf5f66e304af5f66cf04af5f66cb04af5f66c304af5f66bf04af5f66 else 0xc522521666704af60e60ef4af60e69b04af60660ef4af6066db04af5fe66b04af5fe60eb4af5fe60d34af5fe60d2caf5fe60c5228dfe60c5227dfe66f5cffdf666f64ef5f666f64df5f666f5cdf5f666f5ccf5f663134bf5f66676caf5f66636caf5f667f5caf5f667b5caf5f666f5caf5f666f54af5f666f4caf5f669744af5f667b44af5f666f44af5f666744af5f666344af5f666f3caf5f66673caf5f66
  else bif blt i 79 then 0xec50fa5e70c522a25670eccaf64e60ec4af64e60c522a24e60edcaf6466676caf61e66704af61e62f04af61e60ed4af61e60eccaf61e60ec4af61e69304af61660ef4af61660ec4af6166 else 0x286338110a198a844286618110a198f1c328631400c20c20803286108908a382224228e088904a18c780128631400508231c402887c5100a198f3c0286338f00a198f360286338900a198aa40286618901b0c6224028632a080a18ce00028632e000a18cb00028662a000b18ca80028632a000a1986000286318000a18c400028618c00020c60800
def a1Pack5 (i : Nat) : Nat :=
  bif blt i 88 then bif blt i 84 then bif blt i 82 then bif blt i 81 then 0x28c7bc7110198f1c428663c7107198f1c40c663c710a196f1c42863bc710a18cd9c4085326711018c81c40c631e710318c59c4406314711018c29c408530a710214c11c4083084710214c09c428b7bc690a198f1a4286320690a18c51a428630a690a3822144286300510a198f124085302491b81ef0e42887bc390a21ef0c40c6302310a1922064 else 0x4209bcc91b822f32428e8bcc91591ef3244227bcc92181ef3248207bcc91f81ef3244a07bcc91081ef32429f7bcc90a49ef32428643cc90a38ccb24286332c90a18c9b244207a0c90a18c6b24286338c10a18cab046e87bcb91591ef2e428663cb10a21ef2a428631a91108265244287314910a38852446e8988911b10c224428663c790a18c51e4
  else bif blt i 83 then 0x4607bcc95a81f14442907c5110a21f14444207c3111b81f04442887c1111081efc443207bf110a21efc442887bd110a21ef42428673d091081ef4042887bd011581ef3e44a07bcf91081ef3e43a07bcf90a39ef3e42887bce90a21ef3842887c4d11b822f34428e8bcd10a220f3446e07bcd11081ef3442927bcd10a21ef344286330d11b826f324 else 0x2947bca30a4def28c2927bca30e826224c282088930a18c218c2800065b1418c224b4c630892d018c224b80318892c10c6224b00110892ca18c222b28c788928418019ca286508925b0c62249001006424a21f144828600621d08231c462887c5118a55ef286286338a18a198aa86286618a19b04422466c3188818a18422066e07bc298a29ef0a6
  else bif blt i 86 then bif blt i 85 then 0x28e7bc9cca184225328e08894de81f14524207c5148a21f145240663c9483198f25224e308949b34c22526c9308949b20c225214830894a0184225280e08894883822252142088949518c22321463088c9b80c2251546308940818c2250186308940a3822250140006741081f144f28663c93d518c224f546308938a6def28d28e7bca34a69ef28c else 0x29a79ca50a18c6a94292796a52082652945e0994a51082652943e0994a50a6a65294292994a50a4665294287314a50a38a5294820214a520388529454e214a50e388529428e214a5200c852946c3214a51ba264a94829310a51b0c4429480630ea50a3823a942969c714ca39ef2938207a2a4db81e8a93286322a4e0826529328e314a4ca18c5293
  else bif blt i 87 then 0x2979c7150a21f14544a07bcfd1081ef3f4820a46e520829233429d9b2cd0a726cb342969b2cd0a18ce3146e593ca51b922f2946e77bca51b95ef2946657bca51591ef2945637bca51089ef2947217bca51b85ef29428f7bca50d39ef2942866bca51b826ea94286334a50a18ca2946e07a4a50a21e92948207a2a51d81e8a942987a2a50a1928a94 else 0xa7ab1c7a7a08c71e988231c7a5a08c71e958231c7a4208c71e8a6631c7a2968c71e8a4a31c7a28e8c71e8a21f147a2887c5168a21f14594208c7160a21f14582887bcfe1081f14572887c515d281ef3f74207bcfdca18ce3d62887c5155b9a91c546e5a4715159291c54
  else bif blt i 92 then bif blt i 90 then bif blt i 89 then 0xb12b91a171ac2e2585c2b0b816172a42e5385c0aeb915971baae0755ca66b81616db89d5313a6e272044e02c2bd31360a26b484d40012861340b0e6145082901058910b10215044290887130 else 0x162b42c3659a5c
  else bif blt i 91 then 0x5869f0602b0d36070569a7c080ac34f81015869b8202b4db6040571a6c080ad34d81015869b0202b0d35040628e4c080ac348c1015898f0202b0d15040569a28080ac345010158689820214983040430e06080851c0c1010a3810202b0d36030561a28060ac34d8081587db0082b0d3e000561a6cde02d34d81005869b0200b131e040028e060802c34f8000 else 0xb5625c38342c4b87062d8970e0ac872e1c158fa5c382b17cb870562d970e0ac4d2e1c1587e5c382b0dcb870561a7d0e0ad34fa1415869f4282b0d36720561a6cde0ac34f9b415869f3302b0d3e640561a7cc00d0b12d5c15869f2b82b0d3e560561a6cac0ad34f90415869f2082b0d13410561a7c6a08526d8d410a4c39a82b0d3e1f0561a7c220ac34d8441
  else bif blt i 94 then bif blt i 93 then 0xa9625c28cb134b851961a6c8232c34d8f465869b020cb130c41146010e6a2ac34d81050a381820ab0d36051161a6c0822c34d9bc3689862086b0d36060d61a6c0a1b034d81035869b0206b131e040d60e1e081851c0c103589a6c284b16cb850961a7d0a12c3ed9042587db0204b0db6040979a6c0812c34d81025898f0204b070f040828e060812cab56201 else 0x8a3930616b0d230c2d6263c185ac345830b5868a8616b0d140c2d61a2618585260c30b0a3818616b0d360b2d61a6c145851c0c28b5869b0496b0d36082d61a6c0a5ad34d810b5869b0216b131e042c28e06085ac34fa14a5869b1b141470736282936c6a5051c10d4a6e69b0214b0d36042960e1e085051c1010a0a3818214b0d36042561a6c0842c34d8107
  else bif blt i 95 then 0x7669b0b96b0d36172c71a6c2e5ac34845cb5868d0b96b0d14172d60e1e2e58e341c5cb1c6818b9614983172c28e062e585100c5cb5869b0b16b0d36152d61a6c285ac34d844b5868a089614703112d61a6c205ac34d83cb5869b0716b0d370d2d61a6c1a5ac34f830b5869b8616c0d360c2d71a6c185ad34d830b5869b0616b0d350c2d61a62185ac34c030b else 0x5869b1096b070f212c28e06425ac34d878b5869b0e96147031d2d61a6c385ac34d86cb0a3818d96f4d361a2db9a6c345ac34d868b8a3930d16147261a2d61a2834582141c68b0a3818d16b0d3e192d61a6c325ac347864b5868e8c96b0d1c192d61a28325851c0c64b0a1818c96b0701192d60602325ac000464b5869b0c1614703182d629962e5ac34f85cb
def a1Pack6 (i : Nat) : Nat :=
  bif blt i 104 then bif blt i 100 then bif blt i 98 then bif blt i 97 then 0xa3839a16b0d36332d61a6c645ac34d8c4b0a38198974cd36302dd9a6c605ac34d8c0b58387981614703302d61a6c525851c0ca4b5869b1416b0d36272d61a6c4c5ac34d894b0a3819296b0d36242c28e06485c034d88cb6e69b1196b0d36232d60e1e465851c108cb0a381919614700232d61f6c445ac34d888b5898f1116b070f222c28e06445bf34d884b else 0xa3929a9614723352c28e446a5bb3484d4b0a3909a961471f352d6263c6a58c1c78d4b0a38f1a961471d352c28e386a5851c6cd4b0a38c9a9614712352c28e226a5851c40d4b8a3879a961470f352c10a1e6a5851c28d4b0a3849a9614708352c38e0e6a5861c1cd4b0a3839a9630387352c28e0c6a5851c14d4b0a3821a9614703352d71a6c685ac34d8d0b
  else bif blt i 99 then 0x3669b1a9668d36352cc9a6c6a59834d8d4b2e69b1a9658d36352ca9a6c6a59334d8d4b2469b1a9644d36352c81a6c6a58f34d8d4b1c69b1a9634d36352c61a6c6a58b34d8d4b0a61b1a9614b36352c2936c6a58524d8d4b0a45b1a9614836352c28f6c6a5851cd8d4b0a39a9a9614734352c28e5a6a5851cb0d4b0a3959a961472a352c28e526a5851c9cd4b else 0x7669b1b16b0d36362c71a6c6c5c556d8d4b8a7db1a9630fb6352d61c6c6a5ac36d8d4bb669b1a9764d36352ec1a6c6a5d434d8d4ba669b1a9744d36352e81a6c6a5c234d8d4b8269b1a9700d36352df9a6c6a5be34d8d4b7a69b1a96f0d36352dd9a6c6a5ba34d8d4b6e69b1a96d0d36352d69a6c6a5ac34d8d4b5669b1a967cd36352cf1a6c6a59d34d8d4b
  else bif blt i 102 then bif blt i 101 then 0x5869b2e16b0d365b2d61a6cb45ac34d964b5869b2516b0d36492d61a6c905ac34d918b5869b2296b0d36442d61a6c845b738d904b5a6db2096c0d36412d79a6c825ad34d904b5869b2096b0d33412d61a5c825ac4ca504b586922096b131f412d6263c825c51c6504b8a4462096b0d363f2d61a6c7c5ac34d8f4b5869b1e16b0d363b2d61a6c725ac34d8dcb else 0x58d673216b17ce642d62d9cc85ac4d3990b5899f3216b1336642d6206cc85ac3cd990b5871b3216b0db6642d69a6cc85ac34d990b58696b216b1329642d6264ec85ac348990b76690b216b131e642d61a6cc65ac34d988b6869b3096b0d36612d6263cc25b434d980b5a69b3016b0d36602c69a6cc05ac4c7980b5869b2f1714d365d2d61a6cba5c51c9974b
  else bif blt i 103 then 0x5869b3a96b0d36742d61a6ce65ac34d9c4b5899b3796b0d366f2d61a6cdc5ac34d9b0b91625b59716c4b6b2d61f96d65ac34d9acba9625b516b134b6a2d61a6cd45ac34d9a0b5869b3396b134d652d62d96ca5ac4d2d94b5869f3296b1336652d61b6cca5ac34d994ba9627321742c4e642e0589cc85bbb13990b6f6273216d2c4e642d64b9cc85ac7d3990b else 0x586a04296b0d3f852d71a7d0a5ad34fa14b5869f4296b0d3d852d61a790a5ac34ee14b5869d4296b0d39852d61a710a5ac3ede14b5c69bc296b0d37852d69a6d0a5ac34da14bb5625c21746c4b842d62697085ac34da10b5869b4196b0d36822d61a6cf45ac34d9e4b5869b3c172ac4b772e2d896ee5ac872ddcb5869b3b96b134b762d61a7cec5ac34d9d8b
  else bif blt i 108 then bif blt i 106 then bif blt i 105 then 0x58ea5c296b1bcb852d635970a5ac692e14b58c65c296b184b852d6af970a5ac5f2e14b58b65c296b164b852d62a970a5b7532e14b58a65c296b144b852d627970a5af4d2e14b5a9a5c296b134b852d625970a5ac492e14b588e5c296b114b852d61a930a5ac352214b586a3c296b0fc6852d61a8d0a5ac351614b586a24296b0d43852d61a850a5ac350614b else 0xa1665c2971accb852e2d9970a5c0b32e14b77665c296deccb852d6d9970a5dbb12e14bb1625c2975ec4b852eb58970a5d5b12e14ba9625c2974ac4b852e8d8970a5d0b12e14b592e5c296b254b852d649970a5ac912e14b6f1e5c296b23cb852d646970a5ac8b2e14b59125c296b1fcb852d73e970a5ad7d2e14b58fa5c296b1ecb852d63c970a5ac772e14b
  else bif blt i 107 then 0x5869b2818d0d364f3161a6c9e62c4c793cc58387a798b0d364b3161a6c8262c4c7904c58387a098b0d363a3161a6c7062c34d8d4c4869b1a981471e353028e186a6051c1cd4c5869b0918b0d36113161a6c1862c34d814c8b6e6c2970ef4b852e3dd970a5c3b92e14bb16e5c29752dcb852e9db970a5bfb72e14b776e5c296eadcb852dbda970a5dab32e14b else 0x5869b279ab0d364136dd8970a64fb12e14c89625c2990ec4b8532058970a63bb12e14c71625c298d2c4b8531655970a62ca12e14c593a5c298b264b853163e970a62c6b2e14c58be5c298b134b853161a7d0a62c34da14c5869b3e18b0d366f3161a6cd262ca13990c5899b3218b0d36643161a6cc262c34d980c5869b2f98b2836553161a6caa62c1c7954c
  else bif blt i 110 then bif blt i 109 then 0x593eac41f42c4b873d657970e7ac5f2e1cf587e5c39eb0d36723d61a6cde7d0b12d5cf59365a79eb0d3e4f3d61a269e7ac5f2d18f58686231eecf0c413e29118827ac342d04f58fa59d9e1498c353c281126a7ac7c30bcf5869f099eb0d36133d61a3c267ac34704cf5868a099e14703133d61a7c247ac772d04e5869b089d16c4b8535652970a6ac34d9a8d else 0x5869b282ab0d374f55a1a6c9eab234d93d55869b27aab0cb64f5561a629eac51c993d55898f27aab0d144f5561a6282aac34d8ed58669b1aaaa8d36355428e186aaac1c30bd55869b162a147032c5561a6c56aac34d8a955869b10aab0d36205561a6c26aac34d93d40a3861aa8b0d364f4d63f969e92c7d2d3d28a44620a4b0d0c414561a6c9e82ca15620f
  else bif blt i 111 then 0x58bc397b0b00872f600810e5ec00000cbd85878620ae38d0c415c2821882b89021cd57594e5c2acb0d3a4f5961a6c9eb50b12e15599625c2ab2ec4b85564d8970aaacaf2e155594e5c2aab284b855564f970aaac852e15558be5c2aab10cb855561f970aaacaf2df1559565be2ab0d367c5561a6ce6aac34d9615595e5abaab17cb575561a2eaeaac34d94d5 else 0xa38616bc1470a2d7828e0e5af051c0cb5e5869b27bab20b64f7161f6c9ee1434d93dc592cf27b8d130c417161a6c5ce2134d905b5869b12369c7264169da61882d45223105a0a44620b41070c416818e1882d02163105a0628620b40850c416961a1882cd0b12d81858be5a0b0b0d0d4161a1a1882c2c34310581a68620b11450c41622841882c05021cd58
def a1Pack7 (i : Nat) : Nat :=
  bif blt i 120 then bif blt i 116 then bif blt i 114 then bif blt i 113 then 0x6898620cab130c419460e18832851c31065181c620cab038c419162618831ac1c31063581c620c6b028c418d61a7d0b12c34d8da287625c2c2b17cb858561a6c9f0a234d93e158698a7c2b131e4f8560e1e9f0851c30d615869b27c01470c35821d8970afac5f2e15f5869b27beb070f4f7e19a6c6af851c30d5f4069b27bc1470c497828e186cf2c34d8b5e else 0xa39534d01472964a141a6c8342634d90684a69b20d090d3641a119a6c8342934c906852698a0d01472a41a028e52834244c790680a38720d01470d41a1a26188344522310681238620d02070c41a038e18834061c310680a38620d01468c41a0609188340c0e310681814620d00c18c41a028e18814051c30fa80a3861ed0dcd3636a028e18833851c31066
  else bif blt i 115 then 0xa38623e0b0d3643c161a188782ca72e16f58be5c2deb0d364fbe28e4c9f7c51c653ef5869b275eb0d364fb962f970b6ac34d93ed58691a7dab131e4fb561a6c9b6ac6b2e16c58d25c2d8b0d364cb161a6c8362c4c7906c58e25c2d6b0d3641ae28e4c835ac34d906aa1625c2d2dec4b85a52b6970b4246b2e1686e69f42d028d3e85a161a6ce142c34d9be8 else 0x8a397a7e0d0d2e4fc161a5c9f82c42b13f05879627e050d2c4fc1626529f84522a13f08a39427e0b0d244fc1d9e469f83b348d3f074691a7e1148a34fc1626409f82c4c7d3f06d60f27e0d131e4fc18263c9f82c4c793f02898f27e03531e4fc16173c9f82c2a793f08a44f27e15061e4fc22913a9f84522713f08a44ca7e1147194fc228e309f84334d9230
  else bif blt i 118 then bif blt i 117 then 0xa97dd27e12afba4fc22df749f84586e93f08afdd27e115f3a4fc22b8749f8455ee93f08a99d27e1148ba4fc2adf6c9f83d56d93f07679b27e0e8f364fc1a1e6c9f80e3cd93f07475b27e0dce364fc169b6c9f83534d93f06869b27e0c4d364fc181a6c9f82f34d93f05a69b27e0b0d364fc0e1a6c9f80d34d93f08a51b27e014a364fc22916c9f80e34d13f0 else 0x58ee5bae0b1dcb73c161a6ce382c4cd9bf05869b37e0b0d366ec1daf96d582c34f9970a16273260b2a4e64c16519cc982ca139930593e73260b18ce64c1a2f9cc982c5f39930595e53260b132964c22d36cbb82c34d96b05869b2ce0fcd3654c24d896a582d34d94b058698a960b0d3651c16206ca183434d94306069b2860b0d3650c16263ca1845bb393f0
  else bif blt i 119 then 0x59125c2e0b204b85c163a970b82c732e17058ce5c2e0b194b85c1631970b8345f2e17066be5c2e0c17cb85c16af970b82c5f2e17058ba5c2e0b0fca85c169a7d0b8455eea170587dbc2e146c4b84c161a6d0382c34da0305869b3fe0b0d367ec165596fb82ca52df7059425bee0b17cb7dc165596f982ca32df305869f3e60b2b4b7bc165596f782c5f2ddf0 else 0x5869b3972b0d366fe161a6cddc50b12e1775869b37eeb0d366ede858970bb2c34d9cb6a1625c2eab0d3660d561a6ce5a2c34d9b74a1625c2e742c4b85c9650970b8ac5f2e1718b767c4e1169d485c22db9b0b83b5f32170b16e5c2e142ccb85c2858970b84eb12e1709b625c2e0b6acb85c1652970b83aa32e17061425c2e0b284b85c164f970b8378f2e170
  else bif blt i 124 then bif blt i 122 then bif blt i 121 then 0x59468c47eb285188fd650a111fac9f4223f8b6e5c3feeedcb87fe458970ffac3f2e1ff587e5c37f16c4b85fa858970bec0b12e17d77625c2fae6c4b85f5bd8970beb4b12e17d58fa5c2fab1acb85f562f970beac4d2e17d5869f42fab0d3685f561a6cdfeac34d9c7c587e5c3f6b0d3e85ed61a6cdfdaca14627a5869b3874b13366fe961a6cdfd2c34d9bba else 0x1652a711fbba34a23f
  else bif blt i 123 then 0x2ef876e756e725d680052484300446630663266225b157112991311125d026402620 else 0x0
  else bif blt i 126 then bif blt i 125 then 0x8791e1e66879962d8584494d0a5b99926264a79925e64879921e248b7921dc48b6922d84c459150a444290d0a462290d08403112002477010d0c38798a2a6197b021ec087500d8a0 else 0x33715cebd65ed58aa561e748b9ce1e73879ca1ed18b7c21e6f879bb32adb99b62dedc5434910d34830d1ec613ae04ea341a444e8
  else bif blt i 127 then 0x4a2654b18549525214a562a64526645a264522644a2644a2244b1e44a1c44b1a44b18469564314a4294a4214a438ca4088a4008a421484090444802442004214c34a2624ae61522c04a2c04a14021ca0 else 0x6c7168c6f67c2f67bef673ef6522d64ae9683ef54a2744b2734a2734a2724a2d17bf304b1f04a26f4a26e6b6ad62a6d4b1ed6990d1950d7a26c2160c215ec7952c384eb484ea21469104e84a2474a266
def a1Pack8 (i : Nat) : Nat :=
  bif blt i 136 then bif blt i 132 then bif blt i 130 then bif blt i 129 then 0x6bb56 else 0x2a
  else bif blt i 131 then 0x2a else 0x2a
  else bif blt i 134 then bif blt i 133 then 0xa1deec1ec602002a00 else 0x5ed838ac0201f0715804000c3ab008001810c41000302110200060421068b60e2b003d6c1c560001b838ac0002f071580005a0e2b0000941c560000f838ac00011071580001a0e2b0000019c560000032aac000006415800000c7ab0000018e5600000314ac00000604b800000c087000001810dc000030218800006042800000c084e0000181094000030212000006042200000c084200001810800
  else bif blt i 135 then 0x3021b8c0006043218000c706230001830c46000302188c0006043018000c0850300018109c6000302128c0006042418000c3a8430001810886000302108c0006043114000c08502800181084582d838ac0800d0715810000c82b018001810c43000302120735b07158090b60e2b01011c1c560200f838ac040006415808000c6ab0100018456020003021884000604220a7b60e2b00bd6c1c5601 else 0x3ed838ac100006042721db60e2b03a56c1c560702a838ac0ef5b072181808e0e4303007c1c860600031f0c0d45b071581a3b60e2b033f6c1c56067ad838ac0c037071581805e0e2b0300b41c5606012838ac0c01f07158180220e2b0300341c56060004b8ac0c0006715818000cdab030001955606000320ac0c00063d5818000c72b0300018a56060003025c0c0006043819eb60e2ae3007c1c55c6
  else bif blt i 140 then bif blt i 138 then bif blt i 137 then 0x30eab16000604362c000c086858001810ccb0178021896000604312c000c085e58001810b8b00030216960006042c2c000c085658001810a8b0003021496000604282c000c084e5800181098b0003021296000604242d7b6008465807c0108cb0003021196000104232c000000065800181088b00f838ac140006555828000c086e5000181088a00030218920006042824000c084848001810889 else 0x3838ac16001071582c001ee2b0580039c560b000538ac16000671582dab60c2b05811c18560b000330ac16000655582c000c9ab05800190560b00031eac16000639582c000c62b0580018a560b000312ac16000621582c05e03ab05800187560b000306ac16000609582c000c0ab058001814e0b0003028c16000604f82c05e009b05800181360b0003025c16000604382c000c086e5b56c1c558b
  else bif blt i 139 then 0x23bc8ac1602f491582c05a922b05d16c1c560b9ed838ac1715b071582deb60e2b05b96c1c560b6ed838ac16d5b071582d7b60e2b05a96c1c560b4ad838ac16057071582c0aa0e2b05814c1c560b028838ac1604f071582c0920e2b05811c1c560b01b838ac16033071582c0620e2b0580bc1c560b016838ac16025071582c0420e2b05807c1c560b00e838ac16013071582c0220e2b0580341c560b else 0x326ac1e000645583c000c82b0780018e560f000318ac1e000431583c000c3ab07800184560f0003025c1e000604783c0220086278034010c4f000302189e000404313c000c085878001810a0f000302121e95b0715838000c084a701441c674d66d838ac1a051071583408e0e2b06807c1c560d00030eac1a0510715434000c086868001810c4d4ad838ac18000604253005e0e33a5b56de4560b
  else bif blt i 142 then bif blt i 141 then 0x30218a400060425493b60e2b08807c1c5611000326ac2200063d58453b6072b08807c0e561100031cac220003395844000c52b0880014a561100030eac2200021d5844000c086288000810c510003025c2000060431428b60e2b07ab6c1c560f4ad838ac1e4db071583c4b60e2b07816c1c560f019838ac1e02f071583c03e0e2b07804c1c560f008838ac1e00d071583c0160e2b0780019c560f else 0x5b8ac26000665584c000c8ab09800190561300031cac26000611584c000c1ab0980018156130003021c26000604314c000c084e9a57c1c56124ae838ac2545b071584a0b60e2b09316c1c56124ad838ac24033071584805e0e2b09007c1c5612009838ac2400d07158480020e2b0900021c5612480326ac2400064d5848000c92b09000190561200031cac2400061d5848000c08b090001810d52
  else bif blt i 143 then 0x6b8ac2a0006455854000c82b0a80018e5615000308ac2a00060d5854000c0970a8001810e1500030258aa0006043154000c0856a8001810a153ad838ac28047071585003e0e2b0a00341c5614000308ac280006043150fb60e2f099f841c5613a2d838ac268db071584cfb60e2b09936c1c56131ed838ac2625b071584c0b60e2b0981441c5613023838ac2602f071584c03e0e2b0980341c5613 else 0x3023c3a0006043874000c086ee8001810cdd000302193a00060431741b60e2b0e020190561c000320ac3800d071586c000c0862d856c1c561a017838ac320006043164cb60e2b0c00441c561700030218ae00060d5858000c0862b516c1c56153ed838ac2a6db07158549b60e2b0a896c1c561502d838ac2a05707158540a20e2b0a811c1c5615017838ac2a01f07158540220e2b0a80341c5615
def a1Pack9 (i : Nat) : Nat :=
  bif blt i 152 then bif blt i 148 then bif blt i 146 then bif blt i 145 then 0xa838ac3a011071587401e0e2b0e80341c561d004838ac3a000d7158740018e2b0e80025c561d0003b8ac3a0006715874000cd2b0e800197561d00032cac3a0006555874000ca2b0e800192561d12d822ac3a0026455874400c8ab0e800191561d006320ac3a0806415874000c82b0e80018f561d00031cac3a0006355874000c52b0e800186561d00030aac3a0006115874000c0970e800181261d else 0x26838ac3c00064d5878fb60e2f0ea56cdc561d4ad8b8ac3a95d07158768b60e2b0ec16c1c561d7ad838ac3a5db0715874ab60e2b0e936c1c561d1ed838ac3a35b07158745b60e2b0e896c1c561d0ed838ac3a15b07158741b60e2b0e816c1c561d01f838ac3a03d071587406e0e2b0e80bc1c561d016838ac3a029071587404e0e2b0e80941c561d00f838ac3a01b07158740320e2b0e805c1c561d
  else bif blt i 147 then 0x17838ac46025071588c03e0e2b1180341c5623000330ac46000641588c000c7ab1180018e56230003025c46000604388c06e0e2b110001935621000314ac4202d071588003e0e2b10009524e75fa2d838ac3ef5b071587c0a20e2b0f81241c561f023838ac3e02f071587c05a0e2b0f80941c561f00f838ac3e00d071587c000caab0f800190561f00031cac3e000605587c000c0870f8001810ddf else 0xa2d838ae467db0715c8c9b60e2b91896c1c572302d838ae460510715c8c08e0e2b9181041c572301e838ae4602f0715c8c03e0e2b9180441c5723006838ae460006455c8c000c82b9180018e5723000306ae46000604bc8c0aa0e2b71810c1c56e35ed838ad460470715a8c08a0e2b51807c1c56a34ad838acc745b071588deb60e2b11815c1c5623028838ac4604f071588c0920e2b11811c1c5623
  else bif blt i 150 then bif blt i 149 then 0x168390ec60250721d8c03e0e43b180441c87630078390ec600d0721d8c000ce43b180019587630003210ec600063e1d8c000c743b18001937f63a2d838eec70db071dd8d2b60e3bb180cc1c7763017838eec602b071dd8c03e0e3bb180341c7763000838eec6000771dd8c000e9bbb1a401937763000326eec6000641dd8c000c7bbb180018e7763000316eec6000629dd8c01a0e37b18001946f63 else 0x2d8393ec60370727d8c05e0e4fb180b41c9f630138393ec60250727d8c0460e4fb1827c1c9f6300f8393ec60170727d8c0220e4fb1803c1c9f630068393ec60006727d8c000cacfb18001919f630003213ec601f0725d8c000cacbb18001909763a2d8391ec602f0723d8c04a0e47b1807c1c8f630068391ec60006723d8c000c847b180018f8f63a2d8390ec6f5b0721d8c06e0e43b180bc1c8763
  else bif blt i 151 then 0x16a495ec745b072bd8d7b60e57b1a56c1caf6302a8395ec6051072bd8c08e0e57b180cc1caf630188395ec602f072bd8c05a0e57b180941caf6300f8395ec600d072bd8c00a0e57b180029caf630003395ec6000656bd8d2b60e53b1807c1ca76300f8b93ec745b0727d8e5b60e4fb1c96c1c9f637ad8393ec655b0727d8c9b60e4fb18f6c1c9f631ad8393ec62db0727d8c4b60e4fb1836c1c9f63 else 0x42d847cec604708f9d8c03e11f3b1807c22e7633ed843cec601f0839d8c01a1073b1bd6c1fe76300f83fcec695b07b9d8c03e0ef3b1d16c1ce7635ed839cec6a5b0739d8d2b60e73b180cc1ce763017839cec602d0739d8c03e0e73b180441ce763006839cec60006739d8deb60e6fb180dc1cd7630098399ec60470731d8c0660e63b1807c1cc7630188397ec601f072fd8c04a0e5bb1807c1cb763
  else bif blt i 156 then bif blt i 154 then bif blt i 153 then 0x11a49cec60214939d8c03e9273b1d16ca4e76326d949cec603d2939d8c0665273b180bca4e76300f949cec60152939d8c0265273b18044a4e763a2d8c9cec705b1939d8deb63273b1956c64e76326d8c9cec645b1939d8c7b63273b18d6c64e76316d8c9cec625b1939d8c07e3273b180dc64e76301a8c9cec602f1939d8c05a3273b1809464e76300f8c9cec60151939d8c0223273b1803464e763 else 0xa2db49cec60556939d8c0a2d273b180d5a4e763019b49cec60316939d8c05ed273b180b5a4e763a2dac9cec60515939d8c05eb273b180b564e763012ac9cec67e14939d8d2ba9273b1d16d24e76382da49cec6f5b4939d8c0b29273b1815d24e763028a49cec604f4939d8c0969273b1812524e763023a49cec603f4939d8c06e9273b180d524e763017a49cec602d4939d8c04e9273b1809524e763
  else bif blt i 155 then 0x499939e8c0920e47d1d196a4e763a31d49cec6fe3a939d8dec75273b1d16e24e76301dc49cec60398939d8c06f1273b1d16de4e7637adbc9cec6d5b7939d8d7b6f273b1ad6de4e76302bbc9cec60557939d8c0a2f273b180fde4e76301ebc9cec60377939d8c066f273b180bde4e763 else 0x423394171b59724c6ce5c931b19704c83394131ece504c6b3941118ce504c6b214131ac6504c6b3939302222c44088891110f970341355c0d04ced0356b3ac0f20ce5036733940d08ce5034093940d028e2c360888b0c42222c34233918d0222243408a908d08ce502423394071ace500408a9401022a200
  else bif blt i 158 then bif blt i 157 then 0x42339438c8ce50e2233943906ce50e40ab9439028e50e108b143b022850e6089143842222ce4233943442222cd4233943108ce50b10888b2f1aee50a66b39429022c50a40888a2b9ace50942339425026e509408a14250226509c6b394231ace507c0888b1d02222a70000029f1ace5064088891b1ace505 else 0x76b5dcc19ad7730c6b55cc10ed573042355cc104d5730c6b4dcc31ad1730c6b3dcc31acf530c6b3ccc3a579130c6be44c39acf130c6b3c4c112cef304133b4c39aeeb30c6bbacc39aceb3056b3acc1082cb30408b2cc320ce93042339cc39af972f4233943d10f970ee833943b20ce50ee233943988ce50e
  else bif blt i 159 then 0x39b1b97086c6e5c19b1b970c6c65d432399730b8e65cc32119730e6be5cc35af973096be5cc21af973066be5cc116f9730453e5cc10ef9730433e5cc10af9730c6b5dcc29ad7730 else 0xa42a7804c153c0290a9c0148ecd00a42a6805212340290a980f98ecb07cc2a58366152c0290a96014054b00a42658040002c0290a94014854900a42a40052151df139e8c089cf4600a51a300527518029128c014854600a4283005271180290a8a014854400a42a1805215080290a820148540
def a1Pack10 (i : Nat) : Nat :=
  bif blt i 168 then bif blt i 164 then bif blt i 162 then bif blt i 161 then 0xa42af009215744290aba014855d20982ae810a15744290ab8014855c00a42ad805215680290ab2014855800a42ab805215580290d2a014855500a42aa0052154c0290aa480385525c4c2a8822615440290aa2013855100902a8804615440220aa201085510080028805215400d30a9e049854f else 0xa61728052fb9402975ca014b6e506cd9728052cb940295dca08a2ae502255728852ab9402955ca014a6e500a517280527b9402935ca01516e500a4b72a00e5b9402925ca01486a500a4332805218940290bca01485a500a42b2805215900290ac6014856205ce770805215840290ac0014855f
  else bif blt i 163 then 0xace77285273b942739dca129cee508ce77284273b941f39dca0e9cee506ce77283273b941739dca0a9cee504ce7728a273b941139dca079cee5034e77281673b940939dca039cee500ca77280633b940309dca017cee500ba772805b3b9402c9dca015cee500aa77280533b9402995ca014c6e5 else 0x179cf653c4e7929ea73b95b339dca999cee5dc4e772e6273b96f139dcb589cee59c4e772c6273b95f139dca169cee5
  else bif blt i 166 then bif blt i 165 then 0x6ccb2c0816cab2c0816c97ec0816c96ac0816c969f0816c969a0816c96970816c96930816c97c80817096880816c96880816c92080816c96860810440060816c96840816c96810816c96800816c96800416c9680001d38b2c6806edb2c6806d6b2c6806c968e6806c96886400440884c0d38b2c0806d6b2c0806c969a0806c96880806c96860800440060806c9680000 else 0x6c968f6836cd68e68378968e68374968e6836c968e6836d03ce6836c414e6830440884c36c969a0836c968e0836c96880836c96810836c968e6826d0b2c0826c9688082d38b2c6816f4b2c6816d6b2c6816c97ec6816c96906816c97ce68170968e6816c968e6816c920e6810440884c1eb8b2c081d38b2c081af8b2c0816e3b2c0816e0b2c0816d6b2c0816d0b2c081
  else bif blt i 167 then 0x6c96840c96c96830c96c96820c96c96810c9d38b2c0896e0b2c0896d6b2c0896d0b2c0896c97ec0896c969a0896c96970896c96880896c96860890440060896c96810896c96800896c968e6880440884c86c96880886c96860880440060886c968e6876c968e6866c968e6850440884c56c90882056c968e6846c968e2c46ecb2c9036dab2c9036eeb2c6836d6b2c683 else 0x6c968e1096c9688109d38b2c0c9cb8b2c0c9af8b2c0c96f5b2c0c96f4b2c0c96ecb2c0c96e3b2c0c96e0b2c0c96d6b2c0c96d0b2c0c96cdb2c0c96ccb2c0c96c97ec0c96c96ac0c96c969f0c96c969a0c96c96970c96c96930c96c96900c96c97ce0c96c968e0c96c920e0c96e0b080c96c97c80c96c96880c96c92080c96c96860c90440860c90440060c96c96850c9
  else bif blt i 172 then bif blt i 170 then bif blt i 169 then 0x441084c90440884c90440484c90440084c96c96874c90440074c96c96864c90440064c97f8b2c4896c96884896c968e3896c96883896c96863890440863890440063896d0b2c3496c968e3496c9688349a78b2c3096c968e3096c9688309af8b2c2496c96882496c96972096c96882096c93482096c90882096c96881c96c96861c90440061c96f4b2c1096c97ec109 else 0x978b2c4c9878b2c4c97f8b2c4c96f8b2c4c96e0b2c4c96d6b2c4c96d2b2c4c96d0b2c4c96c97ec4c96c969d4c96c969a4c96c96974c96c96924c96c968b4c9ec96884c9d096884c9a496884c99496884c98496884c97c96884c96c96884c96496884c95496884c94496884c93096884c91896884c91096884c90466884c90444084c90443c84c90443484c90441484c9
  else bif blt i 171 then 0x6c976c6896c96ec6896c96ac6896c96ab6896c96a86896c96a76896c96a46896c96a16896c96a06896c969e6896c969b6896d069a6896c969a6896c96986896c96976896c96956896c96916896c969068978968e68970968e6896c968e6896d03ce6896c968b6896c968a6896c9688689d38b2c6496d6b2c6496c968e6496c96886496c9688509ef8b2c4c9d38b2c4c9 else 0x6d0b2ca496c97eca496c969aa496c9698a496c9697a496c969fa0987ab2c689ef8b2c689e78b2c689db8b2c689d78b2c689d38b2c6896f7b2c6896f6b2c6896f4b2c6896f3b2c6896eeb2c6896edb2c6896ecb2c6896ebb2c6896e7b2c6896e0b2c6896ddb2c6896dab2c6896d9b2c6896d6b2c6896d5b2c6896d2b2c6896d0b2c6896c9aec6896c99ac6896c97ec689
  else bif blt i 174 then bif blt i 173 then 0x6d6b2edc96d5b2edc96d0b2edc96ccb2edc96c97eedc96e0b2cdc96d0b2cdc96c97ecdc9d38b2cd896e3b2cc896d6b2cbc9af8b2cb896ccb2cb49d38b2cb09978b2cb09878b2cb097f8b2cb097b8b2cb096e0b2cb096dab2cb096d6b2cb096d0b2cb096c97ecb096c96acb096c96a0b096c969db096c969ab096c969aa89ef8b2ca49d38b2ca496e0b2ca496d6b2ca49 else 0x6c968e68aefee33dc9d7ee33dc9d3ee33dc9ef8cb3dc9d38cb3dc96f5cb3dc96f4cb3dc96ebcb3dc96e3cb3dc96e0cb3dc9ef8bf3dc9d38bf3dc96f4bf3dc96ecbf3dc96e0bf3dc96ddbf3dc96d9bf3dc96d6bf3dc9db8b73dc9d38b73dc9978b73dc9878b73dc96ebb73dc96e0b73dc96d6b73dc96d5b73dc96d0b73dc9d38b2edc9af8b2edc96e3b2edc96e0b2edc9
  else bif blt i 175 then 0x6c920e60f6c968e5cf44968e4cf4490884cf0440884cf6c408844f6c96883cf6c968e2cf6e368e28f6c908820f6e0b2c18f6c968e18f6e0b0818f6c968818f6c908818f6d6b0814f6c90c814f6c908814f04000614f6c968e10f6d6b2c68e6c968e68e6c968864e6c968e68d0440884cd6c968e68c6c968e68b6eeb2cb0a6eeb2c90a6c969a90a6eeb2c68a6c969a68a else 0x6c968e88f6c968e78f6e0bf368f6ddbf368fd38b2c68f6f1b2c68f6eeb2c68f6edb2c68f6d6b2c68f6c968f68fbf8b0e68f6e0b0e68f6ddb0e68f6c998e68f6c97ce68f6c974e68f78968e68f74968e68f70968e68f6c968e68f6c960e68f6c95ce68fac448e68f6c944e68f6d03ce68f6c924e68f6c920e68f6c908d68f6c908c68f6c908a68f6c968864f6c968e60f
def a1Pack11 (i : Nat) : Nat :=
  bif blt i 184 then bif blt i 180 then bif blt i 178 then bif blt i 177 then 0x6c96909146c968e9146f5b2c6946d6b2c6946c968e6946c920e6946c968e5946c968e4d464968e4d40440884d46c968e1146c968e6936c974e6926c968e6926c968e6916c968e6906f4cb390f6eccb390fd38b2c90f6f3b2c90f6ecb2c90f6e0b2c90f6dcb2c90f6dab2c90f6d9b2c90f6c97ec90f6ecb2790f6e0b1a90f6e0b1790f6ecb1390f6e0b1390f6c968e8cf else 0x18968e6966c940e6966c92ce6966c920e6966c414e6961890884d61090884d60440884d60420884d66c968e6956f5df3dd46f4bf3dd4ef8b2c914c78b2c914af8b2c9146f7b2c9146f5b2c9146f4b2c9146ecb2c9146e3b2c9146e0b2c9146d6b2c9146d0b2c9146ceb2c9146c9aac9146c97ec9146c96ac9146c969f9146c969a9146c96979146f4b139146c9693914
  else bif blt i 179 then 0x440884d96d6b2c6986d6b17698ef8b0e698b38b0e698af8b0e6986e3b0e6986e0b0e6986d6b0e6986d0b0e6986c968e6986c948e6986c93ce6986c938e6986c934e6986c928e6986c920e6986c908a6986c90886986c90884d80440884d80410884d86c40884586c10884586c90882186c968e6970440884d76d6b2c6966d2b0e6966d0b0e69684968e6966c968e696 else 0x6d6b2c69c94968e69c6c968e69c6c414e69c04408b69c44968e4dc04408b4dc0440884dc04408841c6ecb2c91b6ebb2c91b6e0b2c91b6d6b2c69b6c968e69b6d03ce69b6c414e69b0440884db6ecb2c91a6f4b2c69a6d6b2c69a6c969169a90968e69a6c968e69a6c414e69a0440884da6d6b2c6998c968e69984968e6996c968e699ac448e69904448e6996c920e699
  else bif blt i 182 then bif blt i 181 then 0x440886a76c96886670440886670440885670440885270440884e778968e6a66c968e6a60443ce6a66c968e6a56c968e6a40440884e46c968e6a36c968e6a20440884e26c968e6a16c968e6a06f7b2c91f6f4b2c91f6d0b2c91f6c968e69f6c968e69e0440884de6c969191d6c968e69d6c968e4dd04410e4dd0440884dd6f6b2c91c6ecb2c91c6e0b2c91c6c968e81c else 0x14968e6a710968e6a70c968e6a704868e6a704768e6a704668e6a704568e6a704468e6a704464e6a704458e6a704454e6a704450e6a70444ce6a704444e6a784940e6a708440e6a704440e6a76d03ce6a71043ce6a70443ce6a704438e6a704434e6a704430e6a704428e6a70441ce6a704418e6a7ac414e6a704414e6a700314e6a704408b6a704408a6a70440896a7
  else bif blt i 183 then 0xa496916a7ad368e6a7ad068e6a76cb68e6a7ec968e6a7d8968e6a7d0968e6a7a0968e6a79c968e6a794968e6a790968e6a78c968e6a788968e6a784968e6a780968e6a77c968e6a778968e6a76c968e6a750968e6a74c968e6a748968e6a744968e6a740968e6a73c968e6a738968e6a734968e6a730968e6a72c968e6a728968e6a724968e6a720968e6a718968e6a7 else 0xef8b2c6abd38b2c6ab6f4b2c6ab6edb2c6ab6ecb2c6ab6e0b2c6ab6ddb2c6ab6d9b2c6ab6d6b2c6ab6d0b2c6ab6c96a16ab6c969a6ab6c96976ab6c968e6ab6c96886ab6c968866b6f1b2c6aa6c969f6aa6c968e6aa6c968e6a96c968e6a8d38b2c6a7a74b2c6a76b4b2c6a76efb2c6a76eeb2c6a76edb2c6a75acb2c6a7a56b2c6a76d6b2c6a760969d6a75c969a6a7
  else bif blt i 188 then bif blt i 186 then bif blt i 185 then 0x6c96969306c9755930ac96959306c9695930ac44959306c96949306c968e8706d6b2c8306c968e8306c968e7f06d6b2c7b06c968e7b06c968e7706c968e7306c968e6f0d38b2c6b06edb2c6b06d6b2c6b06c968e6b06c968e6af6c969f92e6c969592e6c968e6aedb8b2c92d6d0b2c92d6c968e6ad6d6b2c6ac6c968e6ac6d9bf3debd38b2c92b6ecb2c92b6d9b2c92b else 0x6c969c9306c969b930db8b5a930978b5a930878b5a9307b8b5a9306ebb5a9306e0b5a9306dab5a9306d6b5a9306d0b5a9308b869a93079069a9306d069a9306cd69a9306cb69a93078969a93074969a9306c969a93014969a9306c959a9306d04da93084941a9306d03da9306c96999307896989306c96989306d03d89307896979306c96979301496979306d03d7930
  else bif blt i 187 then 0x6c97ec9306c97ac930ac976c9306c976c9306c972c9306c96ec9307896ac9306c96ac9306c96ab9306c96aa9306c96a99306c96a6930c38b25930af8b259306e3b259306c96a59306ebb249306e0b249306d0b249306c96a49306c96a39306c96a2930bf8b219306ddb219306c96a19306c96a0930afcb1e930db8b1e9306d0b1e93084969e93078969e9306c969e930 else 0x7a0b2c9306e0b2c9306dfb2c9306deb2c9306ddb2c9306dbb2c93079ab2c9306dab2c9306d9b2c9306d8b2c9306d7b2c930796b2c9306d6b2c9306d5b2c9306d4b2c930ad2b2c9306d2b2c9301d2b2c9306d1b2c930790b2c9306d0b2c9306cfb2c9306c9a6c9306c9a2c9306c99ec9306c99ac9306c996c9306c992c9306c98ec9306c98ac9306c986c9306c982c930
  else bif blt i 190 then bif blt i 189 then 0x6d6b2c9f06f5b2c9b06d6b2c9b06c969a970afcb6c930a7db2c930b7cb2c930afcb2c930afbb2c930a7bb2c93087ab2c9309b9b2c930979b2c930879b2c9307b9b2c930ef8b2c930e78b2c930e38b2c930df8b2c930db8b2c930d78b2c930d38b2c9306ebb2c9306eab2c9306e9b2c9306e8b2c930a67b2c9306e7b2c9306e6b2c9306e5b2c9306e4b2c9306e1b2c930 else 0x6edb2ccf06d6b2ccf06d6b2ccb06d6b2cc706d6b2cc306ddbf3bf06f4b2cbf06ddb2cbf06d6b2cbf06f0b2cbb06d6b2cbb06eeb6cb306d6b6cb30d38b2cb306efb2cb306eeb2cb306edb2cb306d8b2cb30796b2cb306d6b2cb306c96a0b306d6b2caf06eeb2cab06edb2cab06d6b2cab0d38b2ca706eeb2ca706edb2ca706d6b2ca706f1b2ca306d6b2ca30a78b2c9f0
  else bif blt i 191 then 0x6dabf3df06d9bf3df06d8bf3df06d7bf3df06d6bf3df06d6bb3df0d38b73df06f2b73df06efb73df06eeb73df06edb73df06d6b73df06f5b32df06d6b32df06d6b31df06d6b30df06d6b2fdf0d38b2edf06f5b2edf06d6b2edf06ccb2edf06f1b2ddf06d6b2ddf06eeb2cdf06d6b2cdf0d38b2cdb06f5df3d706f4b2cd706eeb2cd706d6b2cd706f1b2cd306edb2cd30 else 0x6f4d73df06f3d73df06edd73df0d38d33df06eed33df06edd33df0a78cf3df0d38cb3df0bb8cb3df06f1cb3df06eecb3df06edcb3df06f5c73df06e2c73df06eec33df0a7dbf3df0afcbf3df0ef8bf3df0db8bf3df0d38bf3df06f7bf3df06f6bf3df06f4bf3df06f3bf3df06eebf3df06edbf3df06ecbf3df06ebbf3df06e7bf3df06e5bf3df06e0bf3df06ddbf3df0
def a1Pack12 (i : Nat) : Nat :=
  bif blt i 200 then bif blt i 196 then bif blt i 194 then bif blt i 193 then 0x6eec33df26ecbf3df16d9bf3df1efee33df0d7ee33df0d3ee33df0d38df3df0cf8df3df06f5df3df0ef8db3df0ab8db3df0a78db3df06f4db3df06eedb3df0ef8d73df0 else 0x5cbbadad46d71b2b8e058402c26d40b9505b896db404ca0140
  else bif blt i 195 then 0xa626560128 else 0x8c2614230185599a59566692508c0495666905599a3956668c5599a2956640a5599a214230085599a115668025599a09566302508c009566680508c001566680408c0011666803599a0096683e159a0785668001619a005666801598c004230001599a000230000
  else bif blt i 198 then bif blt i 197 then 0x599ad15666b25599ac15696ae5599ab95666ac5599aa95666a85599a895666a05619a7956669e55a527956669c5599a696e66985999a616266985819a615e66985599a614e66985319a614a66985199a61425698508d461423498508d061423298508c6614231185 else 0x8c8621668247598881d6668675da4f99666ae6599a9196669e686e4f96fa93e5b6a4f96ba93e5a6a4f967a93e55d24f957393e55c64f957093e55be4f956e93e55b24f956b93e55aa4f956993e559a2f956683e5599ef956673e5599af95666bc5599ae15666b65
  else bif blt i 199 then 0x911a9556662558196955c94a555a52956433a55599a951666a535ba4fc96669f2599a7c54669f0499a7c10669f010c87c02321f018487c02321ef599a939666a4d08c863423222c00887ad6c91ea59887a820118a5804528a621e95e64fa16c93e8599a921663248 else 0x176a4385a25061666b579ea4fda7a93f55de4fd57693f55d64fd57293f55b64fd5cc93f55b24fd57893b55c24dd5666b555da6bd56c9af5599a9d65c9a5581da955c66a55699a955866a55599a954866a55
  else bif blt i 204 then bif blt i 202 then bif blt i 201 then 0x71da595c769251100495c7690571da395c768c571da295c740a571da21444008571da115c7802571da095c730251100095c768051100015c768041100011c7680371da00adc93e171e0f85c781e171e0005e7680171da005c730011100006dc93e071da000440000 else 0x729ab95c76ae571dab15c76aa571daa15c76a2571da815e769e571da795ca49e571da715c769a5d1da616c76985a1da61667698591da615c7698549da614e7698531da614876985119a6144451851112614444185110a61444198511046142111851102614440185
  else bif blt i 203 then 0x71da19dd893e671dab99c76a4671da79a7d93e5d724f973c93e5c724f96fc93e5b724f95d593e57524f95d293e57464f95d093e573e4f95cd93e57324f95cb93e572a4f95c78be571e0f95c77be571dcf95c76be571daf15c76b8571dad95c76b4571dac95c76b05 else 0xb724fc14d93f04364fc2c769f069da7c18769f059da7c0e429f019087c04421f020887c00121f011047404421ef71da939c76a4d110863444222c08c87adcd91ea71c87a840118a7004528c721e976e4fa1cd93e871da921c732481108622dc93e771e091dc72207
  else bif blt i 206 then bif blt i 205 then 0x7624fd5d793f574e4fd5ce93f58b64fd5cd93f576a4ed5d1937571dad55d89af57366bd5c76a75afa6956686a5589da956076a5579da955c76a5529da956a56a5571d8956675a558a92955ca4a55a90e955c76a5471da94edc93f275a4fc9cf93f271da7c9c769f1 else 0x35fbc39bfef0e6dfbc39b72d0e5d8ac39b7290e5d0a43973e90e6dc9c39b725065c99419b724fe2dc93f771dad5edc93f6b724fd5d993f5
  else bif blt i 207 then 0x0 else 0x6734b66a99665d1005a0
def a1Pack13 (i : Nat) : Nat :=
  bif blt i 216 then bif blt i 212 then bif blt i 210 then bif blt i 209 then 0xb6e4dd88cadb4da6d94d95112410014e0 else 0xb6e4dd88cadb4da6d94d95112410014e0
  else bif blt i 211 then 0x24a400ee90ec2641b098f2c25d4b09732c25c4b0970cc25c1b09704c25c0b09700325c00a97001a5c0029700015c00007000019cb09592c25000003b2c2483b09206c2480049200000b4b09106c2440000106c24000000 else 0x3cf3e911cfa43f3e90dcfa42f3e909cfa41f3e9074fa41b1a906c5a41b129
  else bif blt i 214 then bif blt i 213 then 0x4525900949640152590004964001059000316400085900019640002590000064000015000004400000d00000240000051f94963085258c114963025258c00c963000c58c002163000018c000053000004c000003000c58800001200000440000010452580000050 else 0xb525b821496e00085b811496d9e525b0f9496c2e525b039496c08525b011496c03525b009496c000e5b000316c00085b000116c00003b000005c000016c09496a4e525a5794968000859c0000560c52595b949645e525903549640c525902d49640952590214964
  else bif blt i 215 then 0x4955fa39d57e3e755f8b9d57e0a755f821d57e04755f809d57e08535f8094d7e09533f8114c7e5e52ff8f94b7e2e52df8794b7e0852df8194b7e0452df8094b7e0012df8003b7e000cdf80032fe9e529f8214a7e04529f8094a7e000c9f8002a7e00089f80041fe else 0x9eb55f836d57e0cb55f82ad57e09b55f822d57e9e955f832557e0b955f822557e07955f816557e
  else bif blt i 220 then bif blt i 218 then bif blt i 217 then 0xfddf7a3c02a0400 else 0xa3a963a91fa91ba917a913a90fa90ba907a901a90169012900e900a9006900190009000800070006000500040003000200010000
  else bif blt i 219 then 0x57553aa8589155754e8a8aa745255222a2891142c488a1224400001a2840092a15486aeaa4355d521aa2a90d495486a2aa4350c521a85990d42c886a1624350b021a8580cc000066a1621350b009a85800d42c484a1624150b000a92a90142c480000030 else 0x50b2bf28591f942c6fca1626e50b12f285893949549aa1624d525526605893202c498e1624c50b1262058930c2c49841624c10b126001493000849800324c0009260000530000078a1624b00001da85892942c492a1624850b123a84c91d42c48c000036
  else bif blt i 222 then bif blt i 221 then 0x5465df29f2ef94b977ca4cbbe525ddf292aab95b553ca4aa9e5255474c6a9fb2154fd70aa7ea8553f2aaa9f95354fca8aa7e53d53f29aa9f94b54fca4aa7e51d53f28aa9f94334fca18a7e50bd3f285a9f942d2fca1687e50b3bf28999f982ccfca1667e else 0xafebbe566ddf6432ef95d977cabcbbe
  else bif blt i 223 then 0x57553aa8589155754e8a8aa745255222a2891142c488a1224400001a2840092a15486aeaa4355d521aa2a90d495486a2aa4350c521a85990d42c886a1624350b021a8580cc000066a1621350b009a85800d42c484a1624150b000a92a90142c480000030 else 0x50b2bf28591f942c6fca1626e50b12f285893949549aa1624d525526605893202c498e1624c50b1262058930c2c49841624c10b126001493000849800324c0009260000530000078a1624b00001da85892942c492a1624850b123a84c91d42c48c000036
def a1Pack14 (i : Nat) : Nat :=
  bif blt i 232 then bif blt i 228 then bif blt i 226 then bif blt i 225 then 0x5465df29f2ef94b977ca4cbbe525ddf292aab95b553ca4aa9e5255474c6a9fb2154fd70aa7ea8553f2aaa9f95354fca8aa7e53d53f29aa9f94b54fca4aa7e51d53f28aa9f94334fca18a7e50bd3f285a9f942d2fca1687e50b3bf28999f982ccfca1667e else 0xafebbe566ddf6432ef95d977cabcbbe
  else bif blt i 227 then 0x0 else 0xfdf5d7d6df62e54b954a54b7125b4b8bf7965e577955e53394bc52e94b652d100452c94b052c0
  else bif blt i 230 then bif blt i 229 then 0x1be8ed747b55f39af9c57d09a664d333499933a899c004e3226d93456ab96d5cb4ae59d72ca3964d8b26a59332c9912208b26259302c980 else 0x1be8ed747b55f39af9c57d09a664d333499933a899c004e3226d93456ab96d5cb4ae59d72ca3964d8b26a59332c9912208b26259302c980
  else bif blt i 231 then 0x38 else 0x155500
  else bif blt i 236 then bif blt i 234 then bif blt i 233 then 0x155500 else 0x155500
  else bif blt i 235 then 0x3e0 else 0xffbf7f170f020100
  else bif blt i 238 then bif blt i 237 then 0xffbf7f170f020100 else 0xffbf7f170f020100
  else bif blt i 239 then 0x0 else 0xd601a8
def a1Pack15 (i : Nat) : Nat :=
  bif blt i 247 then bif blt i 243 then bif blt i 241 then 0xd601a8
  else bif blt i 242 then 0xd601a8 else 0xd601a8
  else bif blt i 245 then bif blt i 244 then 0x0 else 0x0
  else bif blt i 246 then 0x0 else 0x0
  else bif blt i 250 then bif blt i 248 then 0x0
  else bif blt i 249 then 0x0 else 0x0
  else bif blt i 252 then bif blt i 251 then 0x0 else 0x0
  else bif blt i 253 then 0x0 else 0x0
def a1Pack (i : Nat) : Nat :=
  bif blt i 128 then bif blt i 64 then bif blt i 32 then bif blt i 16 then a1Pack0 i else a1Pack1 i
  else bif blt i 48 then a1Pack2 i else a1Pack3 i
  else bif blt i 96 then bif blt i 80 then a1Pack4 i else a1Pack5 i
  else bif blt i 112 then a1Pack6 i else a1Pack7 i
  else bif blt i 192 then bif blt i 160 then bif blt i 144 then a1Pack8 i else a1Pack9 i
  else bif blt i 176 then a1Pack10 i else a1Pack11 i
  else bif blt i 224 then bif blt i 208 then a1Pack12 i else a1Pack13 i
  else bif blt i 240 then a1Pack14 i else a1Pack15 i
def a1Palette0 (i : Nat) : Nat :=
  bif blt i 8 then bif blt i 4 then bif blt i 2 then bif blt i 1 then 0xe0f840fce043f01fe80f9c07ca03e101e380f04064a0321018e80c14060207e701fe80f9c07ca03e101e380f04063a0301007e8038401b200c50061800fc0072001f000e800fc003e001b000c8000fc7fb83f951fea0fe407b156b63def15ad837b416b654b70a53812940427f1fee0fe407b39bfaab5b14a582524a16c3def0a5381294094a0213 else 0x63682d6c14b6ffff2b5f95adca96e3def0b5b8529c1bda06b70252810940427f1fee0fe707c39bfbc3f3e0f84f7be631d0ded80f64003156b73def99cfc31b556b656b714a58252618daffff2b5b942d87bde294b0a5382524094affff1ef78529c094a021380ff407ce03e501f080f1c0782003f001c8007c003600190001f8ff70fcf83e7c1f2
  else bif blt i 3 then 0x810fc01b600d9001f800e4003e001b000c8000bffbdfcfefe7e7f37bf9b5fc3efc6c7e0615adca96e3e1f1f078f83478183c000a5b8529c1c0204a5010b8084c002600030000ff7ffe3fdc3f3e0fe707c2e3fd51fea0f84078183e17fffafffcf7be633d318e86f7c37b60bdb01ec80062ad6c631d0c6d810fbfffd56beab5b2b5b8f7bc56b60ded else 0x80f7c079e03c701e080c0401fa00e1000c7f3fbf87d56b63ff314a5825267fff3dff9ef7c3ffe1cff0c7d8637c31b607ff03f781f9c0e7e0727027f810fc07c203df01e380f04064a0321018e80c0401fa00e3007080364018a00c30060800fc00720021000f800740036001900017f3fbf87156b6a95b285b0f87c7c1e3def1ef18529c094b03ff
  else bif blt i 6 then bif blt i 5 then 0x1f078f8347bc63c1c1e060529c1c0204a501098004c00060001feffff7cfe3fdcfffe6fef0fff87e7c1fce0f9f07cb83e3c1f0ab52552927bdf339f98cf4c63e631d0f81873fc31b603e101ec80f1c07820301006c8006737f783e1c1e09fffcf7fe7bdf339f98ff4c67e633d318e87ffc39fe1cdb0ded863ec31be18db03f381c9c09fe043f01f0 else 0xe0fe707cf83e5c1f1e0f8547fa83f941f09ef7cce7e673b319e98c743e0618db01f080f64078203003e0fe0f84fffe7bff3def9ce7cce7e633d318e8ef7c3ffe1bdf0ded8637c31b607e70393810fc01fa001d000c55ad8f7bc7bc62b5b06f682d6e18db063f813fc087e042701ef803fc01be00db006c800fc0072001f000d800640005f8d854b7
  else bif blt i 7 then 0xa00038041bda0ced0636830b4181a0c01035b818dc0c0204a50236810940800021701098080000180004000080003e3fdcdfde0f8737f787e7c1f09ef7cce7e631d0ded80064f7be673f318e86f6c31b60018ab5b873fc31b5fffeab5b2b5b8a52e18daffff55ad95adc529614a704a481295fffe56b71ef78529c094a0213feffff7b3e3fdc3f3 else 0x18c70c60a043f02137fffbffedffdefded7ef63ef6dd7f6eb5b5eae2ef7d77b6af7f57afabd6d57b6ab7f55afaad6d52b67fff3f5f9fadcbdfe5eb72d6d96b68b19256b72b4b94a4c7bde318e15ad831b4181a0a5b7fff95afcad6e56a72b1b952dca94a54a42a120f83c7c063def1ef38f78c78c63c0f1e0185adc2c2e16070b01852dc294e1404
  else bif blt i 12 then bif blt i 10 then bif blt i 9 then 0x86c6c360618db01e080c640602001900007fffbc1f99ce2ab5b2b5b8f83e7bdf318e873fc37b618db0c6c8634c30b6181b086d8434c21361093078182d2c16920b0104a48236c10b608590424810fc084e041901ec8036c01b20059000d8006400120000ffff7fcfbfbfdfcfefe1f7f09bf7b1f7b6f7b779c9bce49e300c1f055edaad7d56b656b7 else 0xe6f8f27c38bebc5f4e2f870fcf87e1c1fde0fe707d783e9c1f3e0f8f07c303e141f098c74060183e1f1fee6fef07c356b77fffbf57ddefeeb5d739eb8df5c63abfff5effaf52d77b6b9db58c9abdbd5adeab4954a4a8524ffbe7f1f3e6f9ef7cf79e7bc739cf9ce74d6be673f31ee98e74c6ba633d318f98c7477be2bcf0fed87c6c3e061cdb0ded
  else bif blt i 11 then 0x1ef78f03c7818295b14a58529c1c02094902528084e18db063f8216c09fe043f007e8036c01b2003b001c8007c0036001900017fffbffbdf8d856b72a5b8f87c7c1e3def1e060f000296e14a70700831b0094a0425011b8085c0426020f010180800002600030000ffffffdfffe7ffeffff7b3effff7b6fb5b7d7fbe7fdf39ef9c97c7fb9ce3cdfd else 0x803040072001f000e8006c0031fcfefe1f7e3faad6cad6e3e1f1f078a52c12933def99cfcc63a1cff0e6f863fc31be18db03f381cfc0e4e04ff0273810fc083e03d901e080c84060603010070803640182003b001c80084003e001d000d800640005fffeff8f7f3fbf9f9fc3efc6c79c93c6019ce2cc6055adaa56cad6e54b7285b0f87c7c1e3e0d
  else bif blt i 14 then bif blt i 13 then 0xe0f8f07c383c1abfbab52552927fff3e1f9effcf7be67ff33bf99cfcc7fa633f319e98c7cc63a1cff0e6d86f6c360618df0c6d80f8407b203c701e080c14060200d9000c55add5fde7fff3def99cfcc67a631f318e87ffc39fe1cdf0dfd86f7c37b618fb0c6f8636c0fce0727021f8107c083203e101ec80f1c0782032101808038401b200c50061 else 0x700837b418da0c0d035b818dc094a04270212808dc043e021701098080c0026000500020000c00020000f8ff707c21bda318e55ad831b4ad6e0213fff7ff7fffbf9fdf0fe36fc7fbabefcfffe6fef0fff87efc3f3e1f8707f383e7c1f2e0f8f07c2fbff3e1f9ef7ccffe673f319e98c743e061cff0e6d86c0c31b603c10180e6fef0fcf83f9c1f2
  else bif blt i 15 then 0x61082ad7d56b6aa5b3f079aaacad6e56b31f0f8f83c7c1c3e0d1f060f7bc7bc63c1c1e060c63856b62a1b0700837b418da0c0d05ad8296e18db027f811fc08ee043f02178109c01fa00db006c800e4003e001b000c8000c0001fffefe7f7f37bf7b1f8d8fc0c2b5b958dca96e54241f0f8f83c7c1a3e031ef78f78c78383c0c0b5b8585c2c0e14a7 else 0x80063ffcde724c19055ad95adc631d57b79ef7cce7e633d318e87ffc39fe1cfd0def86f6c31fe18df0c6d86364297e14b7086d8434c21361093046d8232c10b607e70393813fc09ce043f021380f84063a0301007e8038401b600d90061803040072001f000e8006c00320000ffff7ff9bf9fdfcdefe0f7ef63f1b1ef2cf39278c0bc6019ce2cc60
def a1Palette1 (i : Nat) : Nat :=
  bif blt i 24 then bif blt i 20 then bif blt i 18 then bif blt i 17 then 0x99cfcc67e633d318f98c743e061bdb0c6d80f03c1f983e0ab5b1f07fc7fbafefd1f6e1f9f07c363bdabdbbfffddefee37d5fffaf7fd5edead7f54a49fffcfe3e7bff3def9ce7cd6be673f31ee98cfcc67a631f318e8ef7c579e1f030e7f86f7c37b618fb0c6f8636c21a6109b05ed8236c0e4e04e7021f80f8407b203c701e080c14060200db000d else 0x7008084fe3fdc3f3e0f9707c203c13def99cfcc67a631d0c6d80f1c00321fff0c6f8636c0fce0727021f80062ad6e00d9001c8007c0036001900012a5b8084ffffbffeffeffff7f3fbd9f3fff8ff7c1fbd7f7d7f7eafa73fff9fe3cdfde1fff0fcf87c7c21ce0fe707d783e9c1f3e0f9707c783e1abdbd5afe5552e3fd51fea0f84f9be7c1f3def
  else bif blt i 19 then 0x98c7437b618db0e7f8636c31b156b70c6d7fffafd7d5eb6ab5b2b5baad6cad6e294b0a5383034ad6e14a7031b8184c0427f1fee1f9f0f8f83e13def99cfcc67a631d0f818636cf7be633d318e8637c31b60727021f1ef1fc7fb87e7c1f09ef7cce7e633d318e87c0c31b67bdf319e8637c31b60727021f1ef1c31b6043efc6c1f078f83478383c0c else 0xb078581c2c0a16040b018529c294a14a40a1385094280e14040a00038941c3e0e130707838341c020c6d061683094181a0c0c060283004180006370313818940c2e06130303818040c0004a502168109c084a04240206810140808040102000085c042602030100808000048000c000280010000600010000737f787e7c1f09ef7cf7b6673f318e
  else bif blt i 22 then bif blt i 21 then 0x18c70c608601c16070a5385010252e10860700831b418c20c4d06068296c109204250109bfffcad6e56a72b52958dcac4e56172a5b9529ca94a54a42a12150107d5e3e6f1f1f8f8bc7c3e3e0f1f068f81c7c063def1ef18f2bc78de3c0f1e0607a1c3cbe1e4f0f078781c3c0a1e010e738723c389a1c0f0e0687010319e16b70b53858dc2c4e1617 else 0x2b5b95ad8a5243e0f0424c31b60000ffff7fbfbf9fdfbd8fbdb79c92fd7d5efeaf5f57adaad7d56b67fff3f7f9fafcfd6e7eaf3f519fa3cfc7e7e2f3f079b0a0bdfe5ebf2f5b97a7cbd025e7f2e7696b6cb19256bf2b5b95ad8ad6656a72b4b958dca96e54a52a5215280a56e5296294994a48a16c5080235b918c485663e6f1f0f8f83c78183202
  else bif blt i 23 then 0x60c82bdfd56b6a1002b5bcf7be631d0c6d8636430b618590c258606c18de0b4b05a48252411b608d9042d8216410960849040d8206410120801021f8109c01b2005900248006c0032000900007fffbffcdff3eff7f7f7fbfafdfcfefe6f7f1fbf87dfbd8fc6c7dedbdedde724f1806bfbb39c57ebeaf7f57afabd6d56f6ab5f55adaa520fd7e5eff else 0x8f37c79b63c9f1def8ef6c73be39db1ce58e37c71b635bf18cd8b33c583e2bcf15e48a53c5296294914648a12450322809108487c0c39fe1cdf0e6d8706c38061bdb0d8d8676c31be18db0c6c8634c319618c30c4d8436c21a6109b084c8424c212208db046582124078203190180803640182001900007fffbffcdff3efeff7f3fbdedde724c1f0
  else bif blt i 28 then bif blt i 26 then bif blt i 25 then 0xae36d6b6aaf6f56ffab5fd5adead4f56a4aa76552b6a95954a7aa52d5292a9415424a840502827fff3fef9fc7cfbbe7cff3e6f9f17cf83e7bdf3ded9ef64f63e79df3caf9e37cf1b66b5f35ae9ac74c7ba635d319e98c7cc63a1f030ded8636c060200c1000c80003fffd9ce2ab5bab5bd52927f1f3def99c74c7ba631d31828f7fc7bbe3d1f1e7f else 0xe0f9707c783e181f0a0f84c63babe9cff1e6fef37c78fe3c5f5e2fa717c387e7c3f0e0fe707d383e3c1f0dfffeef7f5effad6dd5edeadef56bfab5bd5a46a52342017fffbff7dfbfefddf7ebfbf57dfab6fd4f7e6fbf17df7fefbdf7cedbe565defeeb5d6e29afffd7bfebddf5eedaf5fd7adebd5f5ea5af3fd77b6b9ff5cefae76d73b2b95b5ca4
  else bif blt i 27 then 0xa5383804181a0c01031b81294084a021701098080c040000030000ffffffffdfffbfffbfffcfffdfffedffcfffbfffddffebfff3fff7fffbf9fdeffef6ff7b3f9d9fbfffdfd7ef6ff7b5f7fffbdbfdedbe7fdf3f2f9cf7ce4be3fdef79f5fdfa7e3d291def5ebfff5fdfad69d5fceafa73ff79fe3ce7de738f37f787e7c3f0e10e707f383f1c1f4 else 0x800e4003a001b000c7fffbf9fdfc3ef3926738aad6cad6e3e1f1f078a52e1cff0c6d8636410b6043f01808036c01b2001d000d800640005fffefe7f7f37aad6d52b656b72a5b942d87c3e3e0f1e060ad6c529614a707078380418da0c0d052d82524094a042501498084e18db021f8006c00320002ffff2b5b952dc7c1e3def1e078f0303c0a14b7
  else bif blt i 30 then bif blt i 29 then 0x9fffcffbe7f1f3dff9ef7cf63e78df3c6d9defcd6be673f319e98c7439fe1bdb0c6d80f040602001977bfaa524f7be6b5f339f98c7cc63a63190fff873fc39be1cdb0ded863ec31be18db01ec80f04060200d9000c55adcf7be631d0e7f86f7c37b618df0c6d8216c0e4e043f01ec80f0406420305018180c0401fa00e1006d80364018600c1002c else 0x700831b4181a063702128084c0019ffeffeffff7f3fbd9f5fff8fffc7fbe31de1faebfbf57df9fffcdfde6f8f17d787ffc3f7e1f9f0fc383f9c1f3e0f9707c783e171be9ff7cfe3e7cdf3def9e37cce7e631d0e6d8636fc7fb9bfbcdf1e4fcf17d787e7c3f0e0fe707c783e1c1e0ddefeafef56bf8d7dbeffd7bfeb9ff56a4aa52543fa83e140f0
  else bif blt i 31 then 0x252811b4086e04250212008dc042e021301018080404000024000980030000a00040001800040001f1fee6fef07f383e9c1f1e0f8737f6a9493def98f74c63a1f030ded80c04003156b73def86f6c31b608db006c80063fffdfcfef39255ad95ade0426ffff7ef63ef6d56beab5b2f7f95adc631c0c6d052dbfffcad6e54b71f078f80c7bc616b7 else 0x424818dc0c0204a502168109c084a042402028101008000293010d8085c0426021200090000800030c6d813fc087e00d9000d8006400060000ffff7f3fbf7b1f8d87ebf2f7f95afcad6e56372b0b952dca94854242a020f87c7c1e3e0d1f038f80c7bde3de31e0605adc2c6e16170b03852dc294e14040700837b418da0c0d035b818dc0c2e0613
def a1Palette2 (i : Nat) : Nat :=
  bif blt i 40 then bif blt i 36 then bif blt i 34 then bif blt i 33 then 0x57bfaadfd56beab5b552daa56d529081503fff9fafcfc5e7e0f2f7f97afcbd6e58c92b5f95adcad6656a72b1b952dca94a54a42a501509081603e2f1f0f8f83c7c1a3e031ef78f03c7818318e15ad8a86c5416294b118d8783c3c0a18cf0b5b8589c2c2e16070a5385010252e1086073f8387c1c260e0f0700831b4185a0c0d06060300418000a5b else 0x2f5f95adca9483e2f1f0f8f83c7c1c318e1505cf7be631d0e7f8637c31b618d90c2d8606c2f6e15b70a5f852dc21b6109b0849831fc18de0b4b046d8216c10b2084b042481c9c09fe04e7021f8109c060200fd006d8036401820059001c800740036001900048000c0001fffefff37f7fbf9fdfcdefe1f7ef63f1b1f7b6f39278c0339c57ebebbdf
  else bif blt i 35 then 0x8f37c77be39df1ced8e36c6b7e2bcf14a48a0243ffe1cff0e6f8736c37be1bdb0ced863fc31be18db0c6c8606c21b610d3084d84244169608db04658216c109204e7021f80f640782030100708036c01b200c30060801640036001900007fffbffcdff3efe7f7f0fbef6def6ef39379c93c601bdeed7f76739b39c556f6ab5f55ada8c4cfd7e5eff else 0xaa76552b2a94b54a4aa124fffe7fdf3f8f9f3fcf9be7c1f3dff9ef7cf7b67bd93c6f9e36ce73e6b5f339f98f74c6ba633d318f98c74863a3cdf1def8e77c579e1f030e7f8737c37b618fb0c6f8636c11b603c1018c80c0401b200c1000c7fffbffcdfcfece7160c82ad6cad6f5effabdbd5bfeadef56bfab5bd52927bdf339f98f74c63a5adf1eff
  else bif blt i 38 then bif blt i 37 then 0xa0504fffe7fdf3e7f9f37cf83e7bdf3c6f99cfcc7ba635d319e98c7cc63a1f030ded8636b07c156b7f1feeafa737f78bebc3f3e0fe707c783e1bbdfd7ffebdff57f7abdbd5bfeadef56bfab5bd4a46840302a17fffbf7fdfbbefd7f7eafbeffdf7bef95977bfbad75c6fad5575fffaf7fd7a96b9ff5cedae7657292af6f56ffab7bd5afead6f56a4 else 0xfef7ff7b7fbd9fde8feb67f3b3f7fffbdbfbfffdedbe7fff3f2f8fffc7fbd7ffebfbeffff7bd7afefd5f4e7fff3fc79cfbcdfde2faf0fff87efc3f3e10e707f783f9c1f8e0fb707d783e9c1f3e0f9707c783e1c1e0ddefebdff57f7abdbd5bfeadef56bfab5bc0f8605c302817fffbf7fdfabed5575effae76d5bdead7f56b7aa52533f683e140f0
  else bif blt i 39 then 0x7ef63f1b0ad6e3e0f1f018f78c2c0e0e01031b808dc042e021301018004c00060001f8ff437b556b656b7fefff0fff87e7c1f099cff07c27bdf339f98cf4c63a03c13def98c7439fe18db01e08036400321cff0c6d81c9c06020039000e80062ad6e18db021f800095adca96e3e0f1e060084c0003ffffffff7fff7ffdfffedff7fff9fffbfffdfc else 0x1098080c002600030000fc7fb87e7c1f3e0f8f07c27cdf3def98cf4c63e631d0f8186f6c31b787e7abdbaa524f7be673f319e98c7cc63a1cff0ded8636c06020018ab5b18c755ede673f0e7f86f6c31be18db084d8236c09ce043f006d8006c0031fcfef1806738aad6cad6e3e1f1f078f83454360e0106368303618db027f810fc084e001b000c
  else bif blt i 44 then bif blt i 42 then bif blt i 41 then 0x79c970fcf83e3c1f0d5edd52927bdf339f98cf4c63e631d0e7f86f6c31b60301000c6738aad6c631d57b79ef7cce7e631d0e7f86f6c31be18db084d8236c09ce043f006d8006c0031fcfef1806738aad6cad6e3e1f1f078f83454360e0106368303618db0c6c813fc087e0427000d80063f7b1f8d856b71f078f80c7bc616070700818dc046e0217 else 0xa020380418da0c2d0606830040c6e0601021281090080a040402000084c0406020000060001000020000fef67c7fb9bfbc1f0e0f8552927bdf3def98c74c63a18db0c6d79c92ad6d56b656b72b5b8f83c1c0204250109f0fcf83e13def98cf431b6043fffeffef6ff7b3f9d9f1fee1f9f07cf83e3c1f09f37cf7be633d318f98c743e061bdb0c6d
  else bif blt i 43 then 0x7fffbfbfdfcfefe1f79c92fd7d56b6ab5a54a428c4942007ebf2f7f97afcbd6e56b71f07bfffd56b67ebf3f1797bfcbd6e56b72a5214a48a16c50801f178f87c7c1e3c0c1d050c8086304300e15058a020421416070a02042181c020c0d042481094042600002b5b95a9cac6e54a52a52150907c1e3e031e078f0303c1e1e050b138585c2c0e14a7 else 0x9084479be39df1c6d8842439fe1cdb0ded8636c060200c100007fffbce4956b7318e8e77c73b638db14a4873fc39b61bdb0c6d86364303610d308488232c10b6084901e080c0401b200c1000c80003fffdffe6ff9f7f7fbf9fdf7b6f7b779c937bddafeece715fafabdfd56b656b78636c31b2185b0c0d8216c10b2084b042480364003200090000
  else bif blt i 46 then bif blt i 45 then 0xe0f87fffffbd9d5f4e7f8f37f783e1bfffdfa7eef7f739daf7fd6b6eaf6f56bfab5bd4a46840303a18140bfffdfbfefddf7ebfbf57df7beef7f75aeaf7fd73b6af6f56f7ab5fd5adea95954a5aa525420299fb40f0a0504ffbe7f1f3e6f9f07cf7be7b1f3c6f9ad7cd6ba63dd318ee0f86a522fd5f5effae76d5adea9493f8f9f37cf7be631d318a else 0x1f078c038529614a7070081094042656b72a5b8f83c781e16b70b038529c1c020c6d0606830040c6e042501098080000060001ffffffffbfff7fff7fff9fffbfffbffe7ffeffff7b7fbd9fbfffdef7ef6ff7b5f9c8fbfffdedbeb49f3f2f9cf7ce4be3fdeffff7bcfafefd6b1e9f8f0fd77fffbdebd7f7eb5a757d39fe3ce7de6fef17d787e7c1fc
  else bif blt i 47 then 0xf8ff75fdf9bfbc5f5e1f9f07c363bd7eafbeffdc6faa9493fff9ff7cf9be7bdf3c6f99cfcc63a18dbcdfde0f86a522bdff54a49ef7cc63a39df0e7f8736c37b618daab5b9ef7cc63a39df0e7f8736c37b618db01e080c0401b1e724ce7155ad95ade631d0c6d8236c10b600d9002c8006c0031fffefe1f55ad95adc7c1f0c6d80362ad6cad6e50b6 else 0x3f5f9f8bcbdfe5ebf2f5b95adca948529228400f83c109256b72b53958dca94a54a42a120f8bc7c3e3e0f1f018f03c78181e0f0f028589c2c2e16070a53850101c020c6d0616830341802063703008109408480405020201000042602030100000300008000100007f7fffbd9f1fef5fdf77ffabefd5f4e8fb737f787e7c1f09ff7cf9be7bdf318e
def a1Palette3 (i : Nat) : Nat :=
  bif blt i 56 then bif blt i 52 then bif blt i 50 then bif blt i 49 then 0xbf5fdfabefbdf7cacaf7fd7a96b9db56bfab5bd52b2a94b54a49ff7cf9be7c1f3def9e37cc7ba631d0c6d9ef7cc63a3cdf1cef8e76c71b629491404873fc39b61bdb0c6d84244060200c1000c80003fffdfcfef39255adc31b618d90c2d8606c10b6085904258212401b20019000480003fffdfdfefe7f7f0fbce497ebeab5b2b5bbfffd7ebeab5b else 0x2a120f8bc7c3e3e0f1f018f7bc781e3c0c0f0787814319e16b70b138585c2c0e14a70a020380418da0c2d0606830040c6e06010252810b4084e042502120101408080400010b8084c04060200001200030000a00040001800040001fffffff7ffbfffcfffdfffef6ff7b3e7e5f392f8ff7afef9bfbc1fce0f8757d39bfbc1f0d5addfffefdff7eef
  else bif blt i 51 then 0x8636c31b2109b08498424410b6085904258212401b2001b000c800240001fffefe7f5fafabdfd56beab5b54a428400fffe7ebf3f1797bfcbd7e5eb72b5f95adca9485292285b142007c5e3e1f1f078f030631c2a0b118d8581c294e1404094b842181c020c6d06068296c1092063702128084c0004000180063fffcad6e56a72b1b952dca94a54a4 else 0x7fcfbf9fdef6ef3926f7bb5fdd9ce2bf5f57bfaad6cfd7e56b798c74b5be39df1ced8a52439fe1bdb0c6d8636430b6181b084d84244169608db042d8216410960849021f80c0401b200c1002c8006c0032000900007fffbfbfdfcfefe1f79c9339c57ebeaf7f55afaad6d4624a1003f5f97bfcbd7e56b71f0f8f83c421410860424818dc084a0213
  else bif blt i 54 then bif blt i 53 then 0x9f37cf83e7bdf3c6f9bdfcd6be673f31ee98c7cc63a3cdf1cef873fc37b618db018080303fffd56b7c1f0d7bfead7f56b7a948bf57d7bfeb9db56bfaa524f9be7bdf318e96b7c843a3dff1e6f8ef7c73be39db1c6d8d6fc579e29491404873fc39b61bdb0ced8637c31b6181b084d842441196085b042480f04060200d90060800640001fffefff3 else 0xbf7fdfabebdff5cedab7bd5afead6f54a4a67ed03c281413fef9fc7cf9be7c1f3def9e37cc7ba631d0c6dfef6757d39bfbc5f5e1f9f07f383e1bfffdfa7eef7f5effad6dd5fdeaf6f56ffab7bd5afead6f52917fffbf7fdfbbefd7f7eafbeffdf7bef95977bfbad757ffebdff5ea5ae7fd73b6af6f56ffab5fd5adea95954a5aa524fffe7fdf3f8f
  else bif blt i 55 then 0xe0f84f7be673f318e9ef7cc63a1cff0c6d80f0439fe18db018080364003218db000d80062ad6c7c1e02132b5b952dc04260001ffffffffbffdffeffff3fff7fffbdbfdecfdfffef6bf391f7fffbdb7d693e7e5f392f8ff7afffd7f7dfffef7af5fffafefd5f4e7f8f39f79bfbc5f5e1f9f07f383e9c1f1e0f86ef7f5effab7bd5afead6f52917fff else 0x7f3faad7d56b67ebf2f7f95adca9483e1f1f078f030631c16070a53850101c020c6d06068296c0c6e04250109c31b60018ffff2b5b958dca96e54a42a120f83c7c0616b70b0b8581c1c020c6d0606818dc084a021701098080c0008000300008000383f9c1f08636c003156b6ffff55ad95adcad6e0c6d0109ff7ffe3fdcdfde1f9f07c38bebc3f3
  else bif blt i 60 then bif blt i 58 then bif blt i 57 then 0x8636f37f787e7c1f0ddefebdff56ffab5fd5addfffefd5f7cacaf7fd73b6ad7f56b7aa56552927fff3e6f9ef7cce7e63dd318e873fc37b618db018080062ad6ead7f3def98c7473be1cff0ded8637c31b608db006c803040031fffefe7f79c9339c556b67ebf2b5b8f87c7c1f318e873fc31b618d9084d8216c1092043f006c8006c00320000ffff else 0x8637c31b608db006c803040031fffefe7f79c9339c556b67ebf2b5b8f87c7c1f0c6d863640031fffe56b72b1b952dca94854241f078f80c2d6e16170b038380418da0c0d031b81094042e02130101800100006000100007ffffffdffdfffef6ff7b3e3fdd7f7e6fef0fcf83f9c1f4e0f8f07c356f7ab5fd5add7bfea9493e6f9f07cf7be63dd318e
  else bif blt i 59 then 0xfef67c7fbafefcdfde1f9f07f383e9c1f1e0f86adef56bfab5bd4a457bfead6f54a49f37cf83e7bdf31ee98c7431b5e725fdece6fef0fcf83e1bbdfd7bfeadff56bfab5bd4a45fffefd5f7cacaf7fd73b6ad7f56b7aa56552927fff3e6f9ef7cce7e63dd318e873fc37b618db01808006339c556b7c1f0af7fd5afea9493def98c7473be1cff0ded else 0x2b5b8f83cad6e54a41f078581c28080e0106068109404260000fef67c7fb83e3c1f098c7431b783e13def98c7437b618dace7198c7439fe18db000c55ad8f83e18db021f2b5b8f83c042e02130000fc7fb83e3c1f098c74f7be631d0ded8636c39fe18db000c55ad8f83e043e56b7010b8084c0003c1f099cfcc63a1cff0c6dfffffffbffbfffded
  else bif blt i 62 then bif blt i 61 then 0x55ad95adc7c1e210a084302124084a02132b5b952907c1e16070a53850101c020c6d0606818dc084a02130002000040001fffffef67ef6be3fdebfbebfbf37f783e1c1f0d7bfea522bdff5cedab5bd52927cdf3def98c7552927bdf318e8636cc63a18db01808030400320000ffff79c9339c556b70c6d821240031fffefe7f55ad9fafcad6eab5b else 0xe6fef07c383e13def8636c01b156b656b71f07810940427fffffeffff7b3f7b5f1fef5fdf5fdf9bfbc1fce0f8707c377bfaf7fd4a45fffeef7f5effae76d5afead6f54a49f37cf7be6b5f318eaf7fd52927bdf318e873fc31b6631d0c6d80c040182001900007fffbce499ce2af7f55adc31b6085b04248036400320000ffff7f3faad6cfd7e56b7
  else bif blt i 63 then 0x8636ebdff529154a49ef7cc63a39df0e7f86f6c31b600c1000c7fffbce499ce2ab5b98c7431b6085b04248036400320000ffff7f3faad6cfd7e56b78636c10920018ffff55ad9fafcbdfe56b71f0782124084a0213ffffff7b383e1c1f0bf57d7bfeb9db56b7aa524f9be7bdf318e8636c1092001900007fffbf9fd56b6ab5b3f5f95adffbfff1fe else 0x10980007fbd9c1fce0f84c63b83e1ab5fd5add7bfea9493def98c7431b6631d0e7f8636c003156b656b78636c0031fffeab5b2b5b8f83c084a02132b5b9529018da0637010980007fffffdfffef67c7fbafefcdfde0fe707c2bdff54a49f37cf7be631dcdfde0f86ef7f5effab5fd5adea522ffff7eafaf7fd73b6ad7f56b7aa524f9be7bdf318e
def a1Palette4 (i : Nat) : Nat :=
  bif blt i 65 then 0x80063fffd56b754a498c7431b556b656b71f07ff7b383e1318ee0f84c63a18db318e86368f83e18da0213e0f84c63a18da3e0f0109ff7b383f9c1f0aa524c63a18dbc1f0d5afead6f52915effab5bd52927bdf318e8636b39c6a949318e873fc31b60018ab5b2b5bcc63a18db000c7fffaad6cad6e3e0f02128084e18da56b72a520f83c18da0637
  else 0xaa524c63a18db318e8636aad6e18da56b72b5b8f83c04275effaa524f7be631d0c6d
def a1Palette (i : Nat) : Nat :=
  bif blt i 32 then bif blt i 16 then a1Palette0 i
  else a1Palette1 i
  else bif blt i 48 then a1Palette2 i
  else bif blt i 64 then a1Palette3 i
  else a1Palette4 i
def a1Info (i : Nat) : Nat :=
  bif blt i 5847 then bif blt i 2178 then bif blt i 299 then bif blt i 45 then bif blt i 11 then bif blt i 4 then 0x5052000c0c8001012000000438008000000400 else 0x2c14c008823001a0084000e004004301 else bif blt i 39 then 0x64214010035003600c6803800800b311 else 0x25033008800c3000c00c027212 else bif blt i 85 then bif blt i 58 then 0xdc3880328a400bc1cc02a83400a000c8001a01002d500 else 0x4a8c4011221003e84400e20108003601403a401 else bif blt i 239 then 0x8b92501e4318060866013e018b8134018055411 else bif blt i 286 then 0x2d82940a905502680147805e02c0ef312 else 0xd38f2033e30c0cc093032418c0c5033030800c8801a03411e600
  else bif blt i 1249 then bif blt i 888 then bif blt i 563 then 0x4da61811912603fc3180ec0660354018f021003812b501 else 0x68861418f92605e231815b066051e018e828a05c233511 else bif blt i 890 then 0x1b503106d00841b301106c800420004088378402 else 0x21993607f23581d306706d8018c82ce08c37a412 else bif blt i 1272 then bif blt i 1261 then 0x23c89308e418c23503308c400c600180bc4e1422 else 0x91c1d024384308fc010580160c04ed313 else bif blt i 1284 then 0x93e1d024b84308fc010580180c44f8323 else bif blt i 1299 then 0x34e4082600d3097a2c825c892096618c257033095200c9001e0c8504700 else 0x33d2260c186dc2dd9470af6398297877098e01d406de0cc513601
  else bif blt i 3630 then bif blt i 3505 then bif blt i 2494 then bif blt i 2459 then 0x3ab9c60e5a59838b9150de42d83670560d660151023213c882611 else 0xf4e40c3ce8c40f242103c38440ef20109804616099b502 else bif blt i 3488 then 0x125a71c46695710ee39c3f68680f5a019187c41689be512 else 0x134e34c4d08a313341cc4c90431312010800221e8da0522 else bif blt i 3561 then bif blt i 3506 then 0x4d7800135c0004d68001358000000021ecdb1403 else 0x4f70e413be2904e305513600149006e1f0db2413 else bif blt i 3626 then 0x51f8f5145a29450905513f6014a00821f8de9423 else bif blt i 3628 then 0x14aa08452981114a200418004204e2a314 else 0x14aa08452981114a200418004208e2c324
  else bif blt i 4589 then bif blt i 3638 then bif blt i 3632 then 0x14aa08452981114a20041800420ce2e334 else 0x5340a214ca20853187114c218452f04214b80c452c81214ae0046000c210e30800 else bif blt i 4333 then 0x167e8585861b615e2594566106155e2d454806514d80193856e214e36701 else bif blt i 4448 then 0x17806905d695517404505c90d4170a2505bc85416d0014f00e626d0ed711 else 0x623994185851460b8f518062945fa864179e018e811a27d160602 else bif blt i 5512 then bif blt i 5500 then 0x6b61e61a5a61867a126198031864406618aa0192071e2911ed612 else 0x6e10e31b782cc6db8831b6414c6d60231b500088801830557c622 else bif blt i 5517 then 0x1ba01c45318611b9a1086e50221b8e0084000a309588503 else bif blt i 5670 then 0x1c7e5547111051c1a2d46f58561ba4014d013230d58d513 else 0x1d525547449051ce22d46f58561cae014d0162321626523
  else bif blt i 6351 then bif blt i 6162 then bif blt i 5878 then bif blt i 5856 then bif blt i 5848 then 0x1d900007638001d8c0007628001d88000000023396d7533 else 0x76b8821da61887670331d9200c5001033d6d8414 else bif blt i 5867 then 0x7770931dd018c7710331db600c600163416e0424 else 0x7770931dd018c7710331db600c600163456eb434 else bif blt i 6029 then bif blt i 5921 then 0x1e424cc78b8f41e263487848941e0218c77f0421de8010b00563496f6702 else 0x1ed65907ae1241eac3cc7a58b41e801d079c0431e52010d00d8351721712 else bif blt i 6035 then 0x1efc2087be07114c61845308511ef20c852e0211eea0085000c36178d722 else bif blt i 6061 then 0x7ca8e21f182905308911f0a18c7c10421de801080034365793603 else 0x7e89541f7e4147d80c41f482107cc0441e52010c80ca3697ad613
  else bif blt i 6338 then bif blt i 6264 then bif blt i 6263 then 0x7e89541f7e4147d80c41f482107cc0441e52010c80ca379812623 else 0x1d900007630001d880004d6800135800000002389877504 else bif blt i 6286 then 0x1ff43087f90931fd818c7f20331fbc00c7002c38d878514 else bif blt i 6312 then 0x204238c80b0a4201e1cc8030341ffc00c8803439188e524 else 0x204238c80b0a4201e1cc8030341ffc00c880343958a8534 else bif blt i 6343 then bif blt i 6340 then 0x81502114c2044814001204e000180043998c2415 else 0x81a05220620c881701220580043800639d8c4425 else bif blt i 6346 then 0x81a05220620c88170122058004380063a18c7435 else bif blt i 6349 then 0x81a05220620c88170122058004380063a58ca445 else 0x7640502076104530831207208452e011206e004280043a98cd604
  else bif blt i 6389 then bif blt i 6376 then bif blt i 6367 then bif blt i 6359 then 0x7640802082188530851207a0c852e0211eea008400103ad8cf614 else 0x7640802082188530851207a0c852e0211eea008400103b18d7624 else bif blt i 6375 then 0x7640802082188530851207a0c852e0211eea008400103b58df634 else 0x1d900007630001d880004d68001358000000023b98e7505 else bif blt i 6382 then bif blt i 6379 then 0x20541c482685220940c8824021208a008400063bd8e8515 else 0x20541c482685220940c8824021208a008400063c18eb525 else bif blt i 6385 then 0x20541c482685220940c8824021208a008400063c58ee535 else bif blt i 6388 then 0x20541c482685220940c8824021208a008400063c98f1545 else 0x7640001d8c000762000204e000000023cd8f4416
  else bif blt i 6394 then bif blt i 6391 then bif blt i 6390 then 0x7640001d8c000762000204e000000023d18f5426 else 0x7640001d8c000762000204e000000023d58f6436 else bif blt i 6392 then 0x7640001d8c000762000204e000000023d98f7446 else bif blt i 6393 then 0x7640001d8c000762000204e000000023dd8f8456 else 0x1d900007630001d880004d68001358000000023e18f9516 else bif blt i 6396 then bif blt i 6395 then 0x1d900007630001d880004d68001358000000023e58fa526 else 0x1d900007630001d880004d68001358000000023e98fb536 else bif blt i 6397 then 0x1d900007630001d880004d68001358000000023ed8fc546 else bif blt i 6398 then 0x1d900007630001d880004d68001358000000023f18fd556 else 0x1d900007630001d880004d68001358000000023f58fe566
def a1Code (i inf : Nat) : Nat :=
  let j := i-((inf >>> 12) &&& 0x3fff)
  a1Pack (((inf >>> 26) &&& 0x7ff)+j/32) >>> (((inf >>> 51) &&& 127)*(j%32))
def a1Word (code desc : Nat) : Nat :=
  let cw := desc &&& 15
  let id := ((desc >>> 11) &&& 0x7fff) + ((code >>> ((desc >>> 4) &&& 127)) &&& ((1 <<< cw)-1))
  (a1Palette (id >>> 6) >>> (17*(id &&& 63))) &&& 0x1ffff
def a1Decode (code : Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,desc => a1Word code desc :: a1Decode code n (desc >>> 26)
def a1RowAt (i : Nat) : State :=
  bif blt i 6399 then
    let inf := a1Info i
    (inf &&& 15,(inf >>> 4) &&& 15,a1Decode (a1Code i inf) ((inf >>> 8) &&& 15) (inf >>> 58))
  else (0,0,[])
def b0Pack0 (i : Nat) : Nat :=
  bif blt i 8 then bif blt i 4 then bif blt i 2 then bif blt i 1 then 0x1d10 else 0x274a2b85864
  else bif blt i 3 then 0x129c84ea870de50ea8911b8aaa1150e046022380780e20 else 0x9a6d8922c7153b19d6cea674b3e19cace367033019d8aed27613449c04ec17603b0d4c6a2e2a69b18cd62781638
  else bif blt i 6 then bif blt i 5 then 0x34b420 else 0x274a2b85864
  else bif blt i 7 then 0x2936b146838a44148de0a28ee5147528cba1461d0a2ce85147428a32144110a202652aa128bd0945a84a2b42514a128a48945004a02402d01016809a251e20a8ece547862a2d0851e4424242147a0081980 else 0x670001ccc8a6633a2818ce99e636143199450c66702298ced806670c0199d2cc561aa99586a9c533a6790ce89e433b60119c3004222a98d46aa63322a88d86a9c3675ed098ea9a2639c6098eb002670c0084eaa4113a89050ea98163a06058eb001670c0059c3000
  else bif blt i 12 then bif blt i 10 then bif blt i 9 then 0x670e4a59c3129674a4259c31096d661a5b3986967561a59d286967321a59ca86967141a592a849639e12586704967081259c184967041259c084933b60a59c3029670c02546aa6833a679cca99e733a479cce888733b601cce6007670c01cc23007600c01d9c2807 else 0x68e64a5a1992967e64a59d992967644a59d892967604a59d612967544a59d492967504a59d3929674c4a59d292967464a59d0129673e4a59ce92967384a59cd12967304a59cb9296d2c4a590b12963ac4a584b129671a4a59c592967144a580512967124a59c4129
  else bif blt i 11 then 0x674b3259d24c967433259cf4c96f3b3259d2c69674b1259d2c29674b0259d6b49674ad259d2b29674ac259d2ae9674aa259d2969674a526bf99299fe64a63f99296f664a5bb99296e664a5b799296d664a5b199296be64a5ad99296ae64a5a9992969e64a5a59929 else 0x774af419d2bd0675cb419d7ab06754f3d9553cf674af3d9b2bcf654af3c152bcf674aebd9d2b8f674adbd9d7aaf672aabd9d28ef674af399d2c8d674afb5ab2bcd674af34d72bcd6744f359d2cac33b6f319ca92c674af2d9d2bca
  else bif blt i 14 then bif blt i 13 then 0x18af68dec9be617800a69b2a265a4ab4d15122dba1a743e247448d4814803e40 else 0x36
  else bif blt i 15 then 0x6a8243b521d69266492324899240c95e648b323499220c90a642532499524c68cc34851a498924c28c69362018100d8406c00393214690a1de2d4e19330c6b0239012670 else 0x24d50889794a34a4da324ad514
def b0Pack1 (i : Nat) : Nat :=
  bif blt i 24 then bif blt i 20 then bif blt i 18 then bif blt i 17 then 0x456b3455b3454b3613b3513b3493b3453b3a6fab5afab56fab4efab4afab46fab467ab5ef8b45f8b4506b4522b00a4645106450064506d442644522445260 else 0x343dc006343ce6453438e645a430e6453ba4e645343ce5853444e6443440e644343ce644343ce5c4343ce384343dc004343ce643343ce64233bce642b33ce642b2bce6423014e642443ce602343ce602b2bce60212bce602343cd60200104602343ce3c236bce382343ce202343dc002343ce641343ce640343ce200343dc000
  else bif blt i 19 then 0x1018400c1008300c343c200c3420200c3404200c3400000c343ce64b343ce70a343ce64a11bce64a1018e64a343cb64a343ca64a943c964a343c864a343ce54a843ce4ca343ce4ca113ce4ca101094ca343c42ca346c428a343ce20a343dc00a343ce649343ce648343ce488343ce647343cf646343ce646343ce546343ce4c6 else 0x343cc0cf343c70cf367010cf340410cf343dc08f343dc00f343ce64e343ce64d343ce64c1018e64c1010564c343cf54c343ce54c3434e54c343ce50c843ce4cc643ce4cc101ce4cc843ca4cc343ca4cc1010a4cc100c44cc343ce20c11bce20c30bce20c343ce1cc343ce04c343dc00c343d900c343d700c1021700c343c600c
  else bif blt i 22 then bif blt i 21 then 0x343d164f343d064f343cf64f343ce64f3438e64f342ce64f3428e64f3ba4e64f343c664f343ce48f343ce44f343ce40f343dc34f3a72030f3572030f3a71c30f3571c30f343dc30f3a70430f3570430f343c430f3420430f3410430f343ce20f343ce18f343ce14f343ce10f3454e0cf3450e0cf3444e0cf3440e0cf343ce0cf else 0x343d8893343ce653343dc892343ce712343ce652343ce651243ce651343ce650dc72090f3bf2090f3b72090f3af2090f3a72090f3456090f3452090f344e090f344a090f3446090f3442090f343e090f343df90f343de90f343dd90f343dc90f3a7208cf343dc8cf3a72084f3672084f343dc70f343cf70f343dc64f343d564f
  else bif blt i 23 then 0x35f2089934f2089934720899346e089934620899345e0899325a0899343dc899343d4899343d3899343d2899343d1899343cf899343ce899343ce7193450e659343ce65930bce659343ce359343ce259343ce219343ce658343ce817343ce657343ce656343ce655343ce654243ce654343ce494243ce49439f2089334660893 else 0x343dc8a1343db8a1343da8a1343d68a13468e861343ce861343ce821343ce7e1343ce7a1343ce761343ce721343ce6e1843ce6a1343ce6a1343ce661343ce660343ce65f343ce65e343ce65d343ce65c343ce65b343ce65a346e1899dc720899bc7208993972089938f208993872089937f208993772089936f2089936720899
  else bif blt i 28 then bif blt i 26 then bif blt i 25 then 0xbcf608a1ad7208a1bcf208a17cf208a15cf208a1dc7208a1cc7208a1 else 0x1515f64dbe70eb62bad90cb6422d8e8b411aeb42b648ad822b0981824066001990f9642d590f1634919104421112444644810860
  else bif blt i 27 then 0x93bd94ad943c93bc8bbc93bb93ca93c293b2a5129d12939293129112900a4199428190810220 else 0x54acf2aa5471404520aa958a514ac52aa5621552b04aa9880554c002aa5e01552700aef1805548c02a94601542300aa000055661c22a56a1152a488efc3e3732d21b99668d4eb484efe30174acc0ba50585d2d002ef180144ad201a56900c8b480695a20
  else bif blt i 30 then bif blt i 29 then 0x7af8733d3c399e5e1ccf1f0e677f4733bf6399df91ccefc0e677c8733be2399d2d1cce568e6779c733bcc399c661ccef20e6778c733bf0199dee0ccef58667798333cfc119d4b08ce948467320233bc4119de108cef180654ad22aa5881552b40aa85a05 else 0x25e1c63bf0db1df8698efc32c79f9263bf0331df8716a95a4a54acd53bf0e255b8712efb38977e1c43bf0e1ddf884cefc40677e1f33beef99df57cca9a3e677cdf33da4f99df878cefc3a677e1833bf0b99df854ca9a24677e0a35dfc39aafe1ccf6f0e6
  else bif blt i 31 then 0x130c39087e1c83bf0e41dfc5a0a95a70a4ad27b25693e92b49ca95a4e0118972a56935e7e898f3f38c77e9c63bf0e31dd8718ebc38c else 0x0
def b0Pack2 (i : Nat) : Nat :=
  bif blt i 40 then bif blt i 36 then bif blt i 34 then bif blt i 33 then 0x0 else 0xa4816eb92e9a2324684a00
  else bif blt i 35 then 0xa4816eb92e9a2324684a00 else 0x6c80
  else bif blt i 38 then bif blt i 37 then 0x9c7544488dd51122111c44884424522110910ab5d5111bc754446b1d51112575444489d51112175444685b5111216d4444844f1112111c4448442511ac7544048442501211093448442451211091048442411bc754440844f11021109c408442510211093008442450211091008442420211090408442400 else 0x211091588442256211081588442446bc754455f1d51156c75445571d51152c75445485951152155445485351152113c45484451152110bc5484427152110945485550e52110939484424b52110929484424552110991484424452110891484424352110909484424542110911084424248c75444c8451113
  else bif blt i 39 then 0x2110921c84424772110915eb1f5116bc75445971d51164c754458f1d51162c754458844f11621134458844b1162112445800291162110b458844291621109c5884425167c7543d884424f65c75439944424e62110939800004e62110931884424b6216542588442496211091d88442466211391588444456 else 0x2575447091d511c21754470844f11c2110ac7084424cc2165446c84424ca2b7544649dd511917754464844511828754c5ef1d51172b75445ca9d51172975445ca1d51172145445c84f51172135445c84b51172125445c84751172115445c84531172114445c844f11721109c5c84425172110931c99d5087
  else bif blt i 44 then bif blt i 42 then bif blt i 41 then 0xbe85d4f6f1d533d2b754cf4851533d2113ccf6f1d512d7c7544b571d512d216544b4844f12d211144b4844272dbc754474859511d215d4474844f11d21109c74844251dbc754472b1d511c else 0xa9f254b92a33aa4d4ae6a54252a2a8098a00c55442a83115148a8c0
  else bif blt i 43 then 0x4911c921f924372486d4a958921b12435a486a490d2521a5243427cb7496ce9259d2433a4817490cc001992423348364904c92c19243aa48654906a921912431a4862490c30a1852428a4860 else 0x4bcaeb395c92eb925572489e
  else bif blt i 46 then bif blt i 45 then 0x4464c0ee8c979d1192f388061e7100a3ce88c961d0026838805027100984e201209c402603a2325e64464acc88c9794402612a2325e4446cbc688c978d1072f1a2325434467086201308d5192f122325e29364bc426c97891072f122325c2100984488c97851192f00804c20 else 0x4464bd020797a040d2f408165e81024bd020167a0402af408051e81009bd108c96a11192d40804da87464b1020136204026944804d081009a10001342111926409324c8100999020132204026342233848103989020231204026240804848100809020130a1127f53a24bea7
  else bif blt i 47 then 0x48b7d92890fb2511bf64a233ac9447fbd288ef7a5119cf4a232de944653d288c97a51172f4a22a5e9444cbd292897a5118cf4a23256944671d288c33a510e674a204ce9446499289092a511b254a2324a9446395288012a5119c24cab25e8a464bd0e8c97a19192f42a325e8 else 0x4466d6288ccac5119348a2326714464ca288c98c5119308a2325f19464be088c97c2aadf57cd5beaf47b7d5e8d6fabd12bf57a147eaf446755e88cbabd119357a2325ef4164bde88c933d1192f722325ed4464bd868c97b09192f62253eab4464bd688c97aaaadf64a4dbec9
def b0Pack3 (i : Nat) : Nat :=
  bif blt i 56 then bif blt i 52 then bif blt i 50 then bif blt i 49 then 0x1376fac6aadf58a233ab1 else 0x0
  else bif blt i 51 then 0x8c else 0x2a446257a90d321912ad484a92751cea19d333a267404d129224244448c091308250
  else bif blt i 54 then bif blt i 53 then 0x7c988a677c9674964a657c947ca37c837c337b33793378134a624a5201424a224b024a712a60 else 0x0
  else bif blt i 55 then 0x0 else 0x0
  else bif blt i 60 then bif blt i 58 then bif blt i 57 then 0xea4ed46da8cb5181a300c6006c009800b0006000ab508000 else 0xf9fb94fdc17ee01f700d783eb8a75a33ad05d681eb4055a01ad001680054001bf3ac79d61ceb00358006c0012000700018000400018002ae7520000
  else bif blt i 59 then 0x0 else 0xf5836038060140400c0200400
  else bif blt i 62 then bif blt i 61 then 0xe92215388549e1526854961525757219525654d5552555489752549495152540295001540011000340005000045494c0003549495251549400000 else 0xe92215388549e1526854961525757219525654d5552555489752549495152540295001540011000340005000045494c0003549495251549400000
  else bif blt i 63 then 0x0 else 0x8c
def b0Pack4 (i : Nat) : Nat :=
  bif blt i 72 then bif blt i 68 then bif blt i 66 then bif blt i 65 then 0xefdbc80 else 0xefdbc80
  else bif blt i 67 then 0x0 else 0xe10
  else bif blt i 70 then bif blt i 69 then 0xe10 else 0xe10
  else bif blt i 71 then 0x0 else 0x0
  else bif blt i 76 then bif blt i 74 then bif blt i 73 then 0x0 else 0x0
  else bif blt i 75 then 0x0 else 0x0
  else bif blt i 78 then bif blt i 77 then 0x0 else 0x0
  else bif blt i 79 then 0x0 else 0x0
def b0Pack5 (i : Nat) : Nat :=
  0x0
def b0Pack (i : Nat) : Nat :=
  bif blt i 48 then bif blt i 16 then b0Pack0 i
  else bif blt i 32 then b0Pack1 i
  else b0Pack2 i
  else bif blt i 64 then b0Pack3 i
  else bif blt i 80 then b0Pack4 i
  else b0Pack5 i
def b0Palette0 (i : Nat) : Nat :=
  bif blt i 8 then bif blt i 4 then bif blt i 2 then bif blt i 1 then 0x33fe64cc8ee8fff1b76366c69d89330b76146c25d86ef05ce099c07780670047ff7ff0f71dde3bbc0730eecdbb983526660ccbfff7c3cc7755bbaa1642aa36ec499960e29de50382558267019a0117f0f701cdc3d0665f0f11dd1b36146c0ee819904ce019c011fe1e8332f87950b0199281c01140338023 else 0x983506678eef01ca33336ee60d41997cccaddd50b2155219b36edfffb1dd56eead5d50b295542aa5bbc866893309565838a77940e1b7624cc2d584ab04ce011413381e101c2019c011960e281c0117feffe1ee3baf87bceef1dde33bc37782ef01cdfff87768eecdbb83bb0665b0f31dd7ffef879eff9fff
  else bif blt i 3 then 0x7efefdddeffbdf97b76f6617bbab7756aea5dd1bb9fff3b767660cff997332665ffcb7796cf2d1e59bcb0714ef23ba43347ff8dfb1b7636605bb89330dde19bc2dd84ab07ce099cb7786ef0d9e0bbc173828f04de099c13001e101c2019c0308060004600800007e1ef7bbe777beef3dde3fbc77780e4dbb else 0xc3bb47767114dbb9a7732ee60d41997ffef8798eef1dde331c11380e6fffdf7fb6eefffdeaabb775bbeaf4cfff9bf736ee6cdcd98937716ee133c1e183770665fffbe1e7b30dffdb77b3e563baaddd5abaa77546ea8591bba1dd42aa7ffcf0f17ef2dde3ffc7f18dfb1b7632ec5bb89f312e624cc2ddbfff
  else bif blt i 6 then bif blt i 5 then 0xe3bac7746dd85bb04cfff7ff0f71dde03906678eef01cc3bb36ee60d41997ccc8555fffbe1e63baaddd5abaa1642aa36ec49984ab04ce07840338023ffffff7ffee7e1ffc3df07bb0f71dde33bc07370f7e1efbfff7e7eeefdbbfb31e913bfff6efed99d7779fff3e5e7bbc99f92271fde3bbc57770f6a1e else 0x4ce011413381e101c2008ffeffe1ee3bb36edf0f31dded99c7778cef0dde0bbc0737ffe1ddbd5547766ddc1e183bb0665b0f31dd56ee64cc6dd8cbb0b77c7770eecdbb8bc30785fffbe1e7bfe7ffccff99332dde47747ff8dbb1b3624cc2dd851b0976099cb778fc30dde0bbc13381e101de019c011fe1e
  else bif blt i 7 then 0x1fc63f0c3f787e30fc21bbc37386e30d800f9c1f082ef05ce0b84140026704c6078c0f080e301c20380033806300c201800118021004000040007e1efbbbf663deef9ddebbbcf778fef1dd9b77c77780e5eaa9b77306a0cccdbb9b3736662ccc19956eea8590aaab7742aa5bbcb0710cd09565bbc49984ab else 0x7c3cf7fdecc3b776ddecf957ffaff757eeaddd5abab54566ea9dd50b297742aa7ffcf0f16ef2c1c36ec49984ab7ffef6615bb9fff3fde7f8ccff97ff2fde5dbcb8716ef2d9e5b30b47966f2c5e5838a7794e929564bbc8668fe31b762ddc49987ef0dde19bc2f585ab09d612ac1f382ef04ce5bbcb738fe7
  else bif blt i 12 then bif blt i 10 then bif blt i 9 then 0xfbfff7e7eddfd98fa21efffdbbfb54f3e3e777bfff6cce7bbc9138fef1dde1bbc0f380e6fffdc3da0430eecdbbe3fbc7777ffedbbd7ffaddf4f8e1ddbfff76eeb77d5e99fff37ee6ddcd9b9a77306a2ddc1bb8332fffdf7fbe1e63baaddd53baa162dde24ceeddcdbb9b31099e0f0bfff7fdeff9df7fbe66 else 0x2c1c36ec25582672dde1bbc177826703c20083f0f71dde0397aaa6ddc199e3bbc0726ddcc1a8332cf955bbaa1642aa4334499cdbb8332fffd8eeab7756aea8590aa96ef219a24cc25596ef2c1c53bca070dbb0956099c022ffffffdfff7ffcfff7ffdfffb7ff3ffe5efc7df87be0f71dde039f9fbf1f7e1e
  else bif blt i 11 then 0x2ffe5fbcb8716ef2d9e59bcb17960e29de47748668fff1fc638886dd8b770dde19bc2dd84ab05de099cb778fe31f861f8437786cf07c20bbc147826f04ce0784070806700c0008c0107e1ee3bbc073ecc7244e3bb87766ddf1dddfff76ee6ddbfff7c3caddd53b96ef1b7624cdfffbd9856ee7ffcc9996cf else 0xed99cfff92271fde3bbc57750f6810c3bb47766ddcd3b98350665fffb24463baaddcb778933e3bbc0737ffdfffbb773ffe6ddcd9b937716ee0f0c1bb8332fffdf7fbe1e6ffec7755fbab7754ee87750aa9fff2dde5b3c7ff8dbb16ee24cc255efff84cf0785fffbdff7b30addd5aba97746ee7ffccff9933
  else bif blt i 14 then bif blt i 13 then 0xdc60f84173826703c20384030806000460080000701c9b7736ee60d419956ee5bbc7f1826704ce0787f0f71dd9b77db338eecdbb63baaddc6ddf1dd83c264ccb778dbb0b76099cb778fc30dde099c0f0f1dd1b7706650aa84abffffff7ff1f7e1ffc3ddf7f8eef03ce039b87b0eecdbbfc3df7ffecc77ff else 0x9b77f87b8fef1dde039bfff5bbe9f1d2217ffeeddd6efabd33ffe6fdcdbb7ffeaddf8eecdbb9b310665fffbeff7cccf8799222bf756eea85a6ddbfff56eea858fff9fef3dde5fbcb77960e0956addcbf796ef2d9e59bcb0710cd1fc6388849986ef09560f9c173826703c20584070802000005bbc7f186ef
  else bif blt i 15 then 0x4ce5bbc7f186ef0dc60f9c1f082e704ce0784070806100c0008c0100000e3bbc0726ddcc1a833336ee6cdc19956ee85555bb96ef219a12acb778fe30956099c022826703c2008ffffffdfffb9fe7ffbfff1efdfff9fff1f7e1efbffc777ffffe3efc3df7ffefcfdbbfb31f07bdaa77ffedffdb338fef1dd else 0x2cde5838a7790cd1fc638886dd86ef09560f9c173826703c20584b778fe30dde1b8c1f383e105de0b9c13381e101c2019c0308060004600800008000ffffff7ff7ffe1ef83dc777f1f7e1efb31c77780e4dbbe3bbbffe6ddbe1e9b76fffdff3abf756eefffd5bb9fff3fde5fbcb7796cf2cde583837784ab
def b0Palette1 (i : Nat) : Nat :=
  bif blt i 18 then bif blt i 17 then 0xfbfff07b8eef01cfc7df87befffd98f7ffdfff8fef1dde039bfff0eecdbbe3bbbfff5ffe9f1d2218776fffd6efabd33ffe6ddcd9b8b7706ee0ccbfff7dfef999f0f324457eeaddcb77cdbb7ffeff9deffafff57eeaddd50b21553ffe7bbcbf796ef2c1c24cc255bfff56ee7ffcff799ff2ffe5fbcb7796cf
  else 0xffbff87b8eef01c6489c7770eecdbb56eefffd5bb9fff2fde5bbcb378e221b761bbc2558267ffbff87b8eef01ce3bb87766ddcdbb7ffeaddcb7789337ffeaddcfff97ef2dde59bc6dd86ef0956099cb778fe30dde0f84177826703c203840103fff56ee5bbc37782679b77fffffefff7ffdfff9fff1f7e1e
  else bif blt i 19 then 0x2dde3f8c13381e101c200800007e1efbfff6638eef1dddfff7ffe7ffcdbb9b770665fffab777ffeaddcbf796ef56ee5bbcb070e220956099c0f096ef0dde099c0f080e1004600800007fffffbffbfff0f7e1efb31c7778eecdbb9b76fffd5bbab772fde5bbcb77960e1c44099c0f0826703c203840100000
  else 0xaddcb7796ef04ce07840f0fe1e9b77c7755bbcdbb2ddefffd5bb8e222dde1bbc13381e1fffffbfff0f71dde3bbbffe6ddbfff56ef36edfffab772fde5bbd5bb9fff2fde5bbcb070e220956099c0f096ef1fc61bbc13381e101c2008c0100000fffff87bf0f71dd
def b0Palette (i : Nat) : Nat :=
  bif blt i 16 then b0Palette0 i
  else b0Palette1 i
def b0Info (i : Nat) : Nat :=
  bif blt i 1089 then bif blt i 585 then bif blt i 92 then bif blt i 23 then bif blt i 3 then 0x38410008088001011000000428006000000400 else bif blt i 9 then 0x2414800602300120083800c004003301 else 0x582c8012883003a14c00b02300120086801c008009500 else bif blt i 55 then bif blt i 51 then 0x290b200881d001a834005e00c6803800c017401 else 0x385100080c802b012000000430008010033411 else bif blt i 61 then 0x2414800602300120083800c014037312 else 0x1613200fc3d00398b400ce1d002f03400b200ca803e01803d600
  else bif blt i 268 then bif blt i 248 then 0x22a59007a91501822d804d0560112014d013801c05c501 else bif blt i 265 then 0x26c30c097093024815000b0230240008780220300f8511 else 0xa0020027c04409e001027600010006034109402 else bif blt i 331 then bif blt i 306 then 0xba0e302be2540a504502820108804c03810c412 else 0x584880cb8e403222cc0c4883030614c0bf02302f4008a0032040132700 else bif blt i 562 then 0x1219c404505d410512503d03180e18660342019001ce04414b601 else 0x1610204e034c13289404b215012882302400089002e064232611
  else bif blt i 738 then bif blt i 718 then bif blt i 604 then 0x52c3881488b3050c1d013e03404ec00c80026068249502 else bif blt i 717 then 0x608550176105059a2d41550560532014c80e206c25c512 else 0x280000189000062200018800002760000000207c2cd522 else bif blt i 727 then bif blt i 719 then 0xa000006280001898000276000000020802ce403 else 0x193892064218c18d033062a00c580100842cf413 else bif blt i 735 then 0x193892064218c18d033062a00c580100882d7423 else 0xa005006281401998410660088197820065c08019601106540042800608c2df800
  else bif blt i 936 then bif blt i 886 then 0x71c6901bf96406dc4541b10d406ae2501a1845066a010f01280902e2701 else bif blt i 899 then 0x583c81938d2075628c1d307307441481ce82307340088801a0a4376711 else 0x1ed10307a834c1e80b2079620c1df84407600109804a0a8383602 else bif blt i 1068 then bif blt i 1067 then 0x21e17408604d020c8e508122901f905507c0014d81060b03a8612 else 0xa0000062800022380006220001880000276000000020c442b622 else bif blt i 1071 then 0x2800c018a030088e0c02258210890008180060c842c503 else 0x8d03482328b208c020c22b044089a010780240cc42f513
  else bif blt i 1227 then bif blt i 1153 then bif blt i 1110 then bif blt i 1108 then 0x8f634c23b8b208c020c236044089a010800260d0441523 else bif blt i 1109 then 0xa000006280001898000276000000020d4454414 else 0xa000006280001898000276000000020d8455424 else bif blt i 1124 then bif blt i 1111 then 0xa000006280001898000276000000020dc456434 else 0x92a3482490b209202842468820914188242833090000c7801a0e0457702 else bif blt i 1152 then 0x92a3c825a8d2096028c2560820950188250833093200c880380e4464712 else 0x28000018a000088e000189000065e0001970000276000000020e8480722
  else bif blt i 1215 then bif blt i 1163 then 0x2610910980204248071091a148245032097200c500140ec481603 else bif blt i 1189 then 0x270102064e38826d8b309ac20c2668440988010900340f048b613 else 0x270102064e38826d8b309ac20c2668440988010900340f44a5623 else bif blt i 1219 then bif blt i 1216 then 0x28000018a000088e000197800065c000000020f84bf504 else 0x2800c018a030088e0c02258210890008180060fc4c0514 else bif blt i 1223 then 0x9de18427685109d610427402209c8008380081004c3524 else 0x9de18427685109d610427402209c8008380081044c7534
  else bif blt i 1240 then bif blt i 1234 then bif blt i 1228 then 0xa00000628000223800065e00019700009e2000000021084cb604 else bif blt i 1231 then 0xa0040062810022384008960c427a82109e40082000610c4cc614 else 0xa0040062810022384008960c427a82109e4008200061104cf624 else bif blt i 1238 then bif blt i 1237 then 0xa0040062810022384008960c427a82109e4008200061144d2634 else 0x28000018a000088e000197800065c000000021184d5505 else bif blt i 1239 then 0x628000223800065e00019700009e20000000211c4d6515 else 0x628000223800065e00019700009e2000000021204d7525
  else bif blt i 1244 then bif blt i 1242 then bif blt i 1241 then 0x628000223800065e00019700009e2000000021244d8535 else 0x628000223800065e00019700009e2000000021284d9545 else bif blt i 1243 then 0x28000018a000088e000197800065c0000000212c4da516 else 0x28000018a000088e000197800065c000000021304db526 else bif blt i 1246 then bif blt i 1245 then 0x28000018a000088e000197800065c000000021344dc536 else 0x28000018a000088e000197800065c000000021384dd546 else bif blt i 1247 then 0x28000018a000088e000197800065c0000000213c4de556 else 0x28000018a000088e000197800065c000000021404df566
def b0Code (i inf : Nat) : Nat :=
  let j := i-((inf >>> 12) &&& 0x3fff)
  b0Pack (((inf >>> 26) &&& 0x7ff)+j/32) >>> (((inf >>> 51) &&& 127)*(j%32))
def b0Word (code desc : Nat) : Nat :=
  let cw := desc &&& 15
  let id := ((desc >>> 11) &&& 0x7fff) + ((code >>> ((desc >>> 4) &&& 127)) &&& ((1 <<< cw)-1))
  (b0Palette (id >>> 6) >>> (15*(id &&& 63))) &&& 0x7fff
def b0Decode (code : Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,desc => b0Word code desc :: b0Decode code n (desc >>> 26)
def b0RowAt (i : Nat) : State :=
  bif blt i 1248 then
    let inf := b0Info i
    (inf &&& 15,(inf >>> 4) &&& 15,b0Decode (b0Code i inf) ((inf >>> 8) &&& 15) (inf >>> 58))
  else (0,0,[])
end SixRowsData
end Source37

section Source38
namespace SemiData
def a1Tags0 : Array Nat := #[0x76543210876543210,0x74365210873216540,0x76521430658743201,0x72165430653208741,0x74321650328716504,0x72143650326508714,0x75634120785642310,0x73456120782315640,0x75612340567842301,0x71256340562307841,0x73412560237815604,0x71234560235607814]
def a1TagsA : Array (Array Nat) := #[a1Tags0]
def a1Tags (i : Nat) := (a1TagsA[i/32]?.getD #[])[i%32]?.getD 0
def a1Marks0 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def a1Marks1 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10,0x10,0x20,0x8c00420020,0x0,0x30,0x30,0x10,0x34,0x20,0x0,0x0,0x0,0x40,0x50,0xa60040,0x0]
def a1Marks2 : Array Nat := #[0x60,0xe00060,0x66,0x40,0x80,0x90,0x1200080,0x86,0x50,0xa0,0xa0,0x14c00a0,0x93,0x70,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7c802660135,0x250,0x1b3,0x250,0x1c0,0x0,0x0,0x0,0x0,0x0,0x0]
def a1Marks3 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x1c0,0x0,0x1c0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def a1Marks4 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def a1Marks5 : Array Nat := #[0x0,0xb0,0xc0,0xd0,0xe0,0xb0,0x0,0x0,0x0,0x0,0x0,0x100,0x110,0x120,0x130,0x140,0x132,0x120,0x150,0xc4,0x2c001c0,0x140,0x160,0xd4,0x100,0x160,0x160,0x0,0x0,0x0,0x0,0x0]
def a1Marks6 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1d0,0x1e0,0x1f0,0x200,0x210,0x143,0x220,0x210,0x220,0x131,0x131,0x225,0x1d0,0x213,0x1d0,0x213,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def a1Marks7 : Array Nat := #[0x0,0xb4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xe4,0x0,0x0,0x0,0x0,0x11900a4803c402a0,0x8980acc02e60283,0xc000a00020002a0,0xa800a00024002c0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def a1Marks8 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x1e00270,0x3200280,0x3600280,0x3400280,0x4800290,0x4a002a0,0x2b0,0x2c0,0x4c602c3,0x2a3,0x2a3,0x295,0x283,0x283,0x274,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x5c002d0,0x2f0]
def a1Marks9 : Array Nat := #[0x60002f0,0x0,0x320,0x392,0xc8006260311,0x66002d0,0x6c002f0,0x7000310,0x1c180e0407000320,0x390,0x394,0x278013c009e004f0,0xa860545,0x27a013d00a2004f4,0x4f4,0x27a013d00a200516,0xa200520,0x9e004f0,0x0,0x0,0x3b0,0x0,0x1d000ec0076003b0,0x3b0,0x3b0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def a1Marks10 : Array Nat := #[0x0,0x3b0,0x76203b0,0xc40062403d0,0xc2405cc0303017000f8009e004f0,0x0,0x0,0x0,0x0,0xf9007a00530,0x0,0x543,0x7c803c4,0x0,0x0,0x0,0x9e004f0,0x0,0x0,0x0,0x0,0x0,0x3f0,0x7e203f0,0x3f0,0x9e004f0,0x9e404f2,0x0,0x0,0x0,0x0,0x0]
def a1Marks11 : Array Nat := #[0xd4006600340020800b8009e004f0,0x0,0x8200400,0x4f0,0x3f6,0x0,0x0,0x0,0x0,0x0,0x8400406,0x4f0,0x4f2,0x4f0,0x4f0,0x4f2,0x4f2,0x4f4,0x4f2,0x3a0,0x3b0,0x3b0,0x0,0x0,0x0,0x4f0,0x4f0,0x0,0x4f4,0x0,0x0,0x0]
def a1Marks12 : Array Nat := #[0x0,0x86003c0,0x0,0x0,0x9e804f4,0x4f0,0x9e804f4,0x440,0xdc006c00344023000c0009e804f4,0x114008c00440,0x450,0x0,0x0,0x0,0x0,0x4f4,0x4f0,0x4f4,0x0,0x8e00446,0x0,0x0,0x0,0x0,0x0,0x4f4,0x4f4,0x0,0x0,0x4f4,0x4f4,0x4f4]
def a1Marks13 : Array Nat := #[0x0,0x90003d0,0x0,0x0,0x0,0x4f0,0x4f0,0x0,0x0,0x92004a4,0x493,0x0,0x0,0x4f0,0x0,0x0,0x278013c009e004f0,0x4f0,0x4f4,0x4f0,0x4f4,0x0,0x0,0x0,0x0,0x0,0x4f0,0x4830218013c009e003e0,0x9e004f0,0x9e804f4,0x12c0092c0490,0x9e004f0]
def a1Marks14 : Array Nat := #[0x0,0x4e4,0x0,0x0,0x9880450,0x4f4,0x4f4,0x9e804f4,0x504,0x4f4,0x9e004f0,0x0,0x0,0x4f2,0x9e404f2,0x0,0x96004f0,0x12c009e004f001bc80d5806e60350,0x0,0x530,0x4f0,0x4f2,0x0,0x0,0x4e3,0x0,0x0,0x0,0x4e5,0x0,0x4f0,0x4f0]
def a1Marks15 : Array Nat := #[0x4f0,0x4f0,0x0,0x4f2,0x0,0x4f2,0x0,0x4f0,0x4f0,0x4f0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4f4,0x504,0x0,0x540,0x0,0x0,0x9e404f4,0x4f2,0x4f2,0x4f2,0x4f2,0x4f2,0x278013c009e004f0,0x0]
def a1Marks16 : Array Nat := #[0x0,0x4f0,0x4f0,0x0,0x0,0x4f0,0x4f0,0x0,0x0,0x4f0,0x4f0,0x0,0x4f0,0x0,0x4f0,0x4d002780109809e00410,0x0,0x4f0,0x0,0x278013c009e004f0,0x0,0x0,0x4f0,0x4f0,0x0,0x0,0x4f00260011e409e00463,0x0,0x4f00278012c0094c04a0,0x0,0x4f0,0x278013c009e004f0]
def a1Marks17 : Array Nat := #[0x13d009e404f0,0x9e804f2,0x510,0x0,0x0,0x0,0x510,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x520,0x0,0x530,0x842,0x112008a0,0x10e40882,0x0,0xf4607b3,0x1e0c0f0a0793,0x0,0x0,0x13c009e1,0x9b2,0x15401a440d24,0x2a802b8c19640b03,0x1ba40e30]
def a1Marks18 : Array Nat := #[0x1b640e32,0x36c81b840db2,0x1b840e42,0x39081c640e32,0x39081c840e42,0xbc3,0xc73,0x308c184a0e53,0x308c18c60c23,0x1ca60e53,0x0,0x0,0x2c8019400cc006a0,0x17600e20,0x18a00e30,0xe30,0x18620c24,0xe61,0xdb4,0x0,0x0,0xe60,0x0,0x0,0x0,0x0,0x0,0x5b0,0x5b0,0xe400730,0x6d0,0x6e0]
def a1Marks19 : Array Nat := #[0x5c0,0x5c0,0x0,0x0,0x0,0x0,0x0,0x600,0x7e0,0x800,0x104008b0,0x0,0x610,0x0,0x870,0x880,0x0,0x8c0,0x8c0,0x660,0x970,0x9c0,0x9d0,0xc6005e3,0x9e0,0x180c0c020600,0x190014400a60,0xa60,0xc800a80,0xa80,0x15600e20,0xac0]
def a1Marks20 : Array Nat := #[0xcc00554,0xaf0,0x17a00e94,0x17c00e74,0x17e00e84,0x5a0,0xcc00b50,0x3300198016c00be0,0x330019800cc00574,0xc10,0xeb4,0x2e800b000be0,0x19800b200be0,0x18a00c52,0xc20,0xc20,0xc30,0xc40,0xc60,0x660,0xed0,0x19800ca00c80,0x0,0x660,0x680,0x0,0xcc0,0xd10,0xd90,0x1b400e74,0x1ae00eb4,0x36000ac40d90]
def a1Marks21 : Array Nat := #[0x1b600dd0,0x0,0x0,0xdb0,0x0,0x0,0xdf0,0xdf0,0x690,0xe20,0x1c600e32,0x1c600e42,0xe30,0xe40,0xe50,0xe50,0x0,0x0,0x0,0x0,0xd460e70,0x0,0xee0,0x0,0x0,0x644,0x6b4,0x6c0,0x18000e74,0x0,0x6f0,0x0]
def a1Marks22 : Array Nat := #[0xbe3,0x903,0x5b0,0x700,0x700,0x0,0x0,0x0,0x0,0x5c0,0x0,0x704,0x750,0x750,0x760,0x760,0x770,0x0,0x0,0x0,0x7b0,0x0,0x600,0x800,0x0,0x0,0x0,0x810,0x860,0x0,0x0,0x0]
def a1Marks23 : Array Nat := #[0x0,0x812,0x870,0x0,0x0,0x0,0x8c0,0x900,0x8d0,0x8d3,0x8e0,0x8f0,0x900,0x12000900,0x120005a0,0x4800240011a00900,0x900,0x903,0x910,0x913,0x0,0x11cc08e0,0x11ec08f0,0xecc0900,0x900,0x120c0900,0x660,0xeac0750,0x0,0x0,0x0,0x0]
def a1Marks24 : Array Nat := #[0x0,0x0,0x0,0x6d0,0x0,0x0,0x910,0x0,0x0,0x920,0x0,0x0,0x0,0x0,0x0,0x0,0x923,0x0,0x940,0x0,0x0,0x0,0x13e00a00,0x0,0xa300530029c014c00bc3,0xa2005400308c184a0e53,0x51802a0015000a80,0x14c00a80,0xa90,0x14c00aa0,0x14e00a80,0xa80]
def a1Marks25 : Array Nat := #[0x15000a80,0x15000a80,0x558038801c400e20,0x15800c200611039401ca00e50,0x5780310018440df4,0xb10060803a101ce80e74,0x59002f8017c00be0,0xbc0,0x17000ab0,0x16600a24,0x16e00a34,0x16200ad0,0x5e802f4817c00ee0,0x17c00be0,0x18440c22,0x18400c70,0xc20,0x0,0x16a00af0,0x2f8017400b60,0xbe0,0x19200e30,0xc90,0x650038c01c600e30,0x33401bc00db4,0x1a2a0df5,0x1aa00c90,0x0,0xdf0,0xdf0,0x0,0xdb0]
def a1Marks26 : Array Nat := #[0x6d80348015c20e00,0x1ae00c90,0x19860cc0,0x1a000cd0,0x15e60ce0,0x0,0x1a200cf0,0x36401b000cd3,0x1a800d15,0x38801c600e32,0xe20,0x39001c600e30,0xe32,0xe42,0x0,0xe50,0x0,0x73803a401d220ee0,0xe70,0x1d400a44,0x1aca0d02,0x1b0a0d02,0x3ac01aea0d73,0x16a60ce0,0x0,0x0,0xeb4,0xed0,0x0,0x0,0xa84,0x0]
def a1Marks27 : Array Nat := #[0x0,0xe60,0x0,0xe50,0x0,0xe30,0xe30,0x0,0xe94,0xd95,0x1d880df2,0x0,0x0,0x1c600e30,0x7288308418480c61,0xe60,0x0,0x0,0xdd2,0x0,0xdf2,0xe31,0x0,0x0,0x0,0x0,0x464023201190,0x474023a011d0,0x1002,0x1032,0x40c820641032,0x3f4c1faa0fe3]
def a1Marks28 : Array Nat := #[0xfd3,0xfe3,0xac00ef0070104288194410b0,0x1e001120,0x57007800420c158610c3,0x3bc422061112,0x23201190,0x234011a1,0x23261193,0x23a011d0,0x23a811d4,0x238611c5,0x0,0x23a611d5,0x23a611d3,0x0,0x1030,0xfd4,0x0,0xb000f10064004240156010b0,0x1e201124,0x23201190,0x11c0,0x11d4,0x0,0x23a811d4,0x23201190,0x11d5,0x0,0x2d003c8015a010d0,0x1e461120,0x0]
def a1Marks29 : Array Nat := #[0x11c3,0x0,0x0,0x0,0x0,0x11d0,0xf51,0x0,0x3b0,0x0,0x0,0x3b1,0xf30,0x1ee00fa0,0xfa0,0xfa0,0x1ee006d0,0x0,0x0,0xf50,0x1ea00f50,0x0,0x0,0xf50,0xf60,0x0,0x1000,0x1000,0x0,0xf40,0x1010,0x1010]
def a1Marks30 : Array Nat := #[0x0,0x20200800,0x0,0x0,0x1032,0x0,0x0,0x1030,0x0,0x0,0xf70,0x0,0x0,0x0,0x0,0xf53,0x1ec60f30,0x7c01150,0xf200590041c0162010e4,0xce00680078202d00166006b4,0x78802e40170010f4,0x1160,0x0,0x1170,0x1180,0x1190,0x0,0x19c021200bb0,0x31c021000bc0,0xf74,0x3bc81ac00d50,0x0]
def a1Marks31 : Array Nat := #[0x1190,0x350042c01c401190,0x21801190,0x11a0,0x0,0x11a0,0x1190,0x11b0,0x0,0x11d3,0x0,0x0,0x0,0x11d3,0x0,0x0,0x0,0x11d1,0x0,0x23a011d1,0x11d0,0x0,0xf70,0x0,0x1010,0x0,0xfa4,0x0,0x0,0x1190,0x0,0x1190]
def a1Marks32 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x11d5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1190,0x0,0x1193,0x0,0x11b6,0x11d0,0x11d4,0x11d3,0x11d4,0x11d4,0xf80,0x1f200f80,0x0,0x0,0x0,0x11b0,0x0]
def a1Marks33 : Array Nat := #[0x0,0x0,0x11d3,0x11d3,0xf86,0x0,0x0,0x1191,0x3b0,0x0,0x0,0x0,0x1190,0xf30,0x4f0,0x0,0xfa0,0x0,0xe400740,0xfa0,0xfa0,0xfb0,0xfc0,0x1f800fb0,0x1190,0x0,0x0,0xfb6,0xfe0,0x0,0xfd2,0xf040fd2]
def a1Marks34 : Array Nat := #[0x0,0xf8407a0,0xfd0,0x0,0x0,0x0,0xf40,0xf50,0xf50,0xf60,0x4f4,0x0,0x1000,0x7e0,0xfe007e0,0x0,0x0,0x0,0xfa0,0x20201010,0x1032,0x0,0x0,0x1010,0x1010,0x11600860,0x0,0x0,0x0,0x0,0x10801030,0x1032]
def a1Marks35 : Array Nat := #[0x0,0xfd0,0x8a2,0x20401000,0x11240870,0x40c820601010,0x1010,0xfe0,0x0,0x20800f20,0x1040,0x0,0x0,0x208c1040,0xfc3,0xf70,0x0,0xf90,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4f0,0x0,0x1050]
def a1Marks36 : Array Nat := #[0x12c00940,0x1050,0x1050,0x0,0x0,0x0,0x20a00ff3,0x0,0x0,0x8c80464023200530,0xa1005280418014c0119305300298023260a60,0x23a611d5,0xaa105500418014820a40054802a4415000a80,0x22a81190,0x23201190,0x23221191,0x0,0x41c017200b4005f802f8017c00c10,0xb02057004200184011d006100308023a00c20,0x23a211d1,0x23a811d4,0x23201190,0x1164,0xd300570842801b6011d106d8036c023a20db0,0x23a811d4,0x11d5,0x23aa11d5,0xe10052a042c01c40119007100388023200e20,0x3494160210b00718038c01c8011d4,0xd350580842c01c8011d407200390023a80e40,0xcb306588430023a011d2,0x10e00709828401ce011930738039c023260e70]
def a1Marks37 : Array Nat := #[0x1162,0x0,0x0,0x1a860cf1,0x0,0x1154,0x0,0x532038802320119005320388023201190,0x1172,0x1190,0x11d3,0x232011d5,0x0,0x1190,0x1190,0x1190,0x1190,0x73a0464023200e7408c8046401c400e20,0x87a04640232010b0,0x0,0x1190,0x1190,0x460023201190,0x46401d080a74,0x1190,0x8c80450023201064,0x1190,0x1190,0xed0,0x8c80464021c810d0,0x0,0x0]
def a1Marks38 : Array Nat := #[0x0,0xbd5,0x20e61120,0x38c0184811d4,0x31841b8011d1,0xc32,0xc44,0x11d3,0xc52,0x11d0,0x22481080,0x22481090,0x7218474023a00e4308e80474018400c20,0x11d0,0x11d0,0x89a0474023a01080,0x0,0x11d0,0x11d0,0x8e80474023a011d007218390c1b620db1,0x11d0,0x8e80444c23a010a1,0x11d0,0x11d0,0x8e80474021661100,0x0,0x11d0,0x11d0,0x11d0,0x474423a01193,0x23a211b9,0x1193]
def a1Marks39 : Array Nat := #[0x11b5,0x18400c400634,0x470023d012200926,0x3880218c128009f3,0x408020440ee60a03,0x41001cd0126009d4,0x3c001f8410e609e4,0x3e801e84112609b5,0x41801d1012c80984,0x42001ec411460994,0x42801f040fea09a4,0x3c802204110609c4,0x390022cc12a00973,0x17c00bc005d0,0x6e0,0x710,0x780,0x0,0x7d0,0x830,0x850,0x950,0x39d014c80e20,0x390c1b620c20,0x3d001ee80ff0,0xf53,0x1193,0x11d0,0x0,0x11d1,0x1190,0x11d4]
def a1Marks40 : Array Nat := #[0x1193,0x40401f481054,0x3f8020421023,0x3f4020021033,0x0,0x240011f0,0x0,0x1210,0x0,0x0,0x24601292,0x24401240,0x0,0x0,0x0,0x0,0x24c011f0,0x940049cc24e21240,0x252812a0,0x14a00a5005280294014a0,0x17b00bd805ec02f6017b0,0x25681c500e280714038a01c50,0x1ed00f6807b403da01ed0,0x25681f200f9007c803e401f20,0x258014b00a5885280294014a0,0x6bcc35ea1ed0,0x79803cc21ed0,0x1ee00f7087b403da01ed0,0x1ee00fa007b803dc01ee0,0x4b003ea61f55,0x45a022d1,0x1ef00f7087b8c3da01ed0]
def a1Marks41 : Array Nat := #[0x35c81ed0,0x17b40bda060102fc817b4,0x25a01c600e280714044401c50,0x791c3da02230,0x1f000f6807b4044801ed0,0x1f000f8007c0044a01f00,0x25a01f200f9007c8044c01f20,0x3ee22270,0x225011200890044802240,0x1f100f7087b4044801ed0,0x4b802e2012e0,0x25c017c00bd805f402fac17b0,0x348012e0,0x97804b8038e01c500e2804b8044402226,0x25c01f200f6807b4044802246,0x25e01f200f9007c8044c02266,0x25c01fc1,0x4b803fa212e0,0x2600226011200890044802300,0x1f000f8087b4045001ed0,0x1ac00d6086b0c35601ed0,0x98a0748038a01c50,0x3da01ed0,0x3da01ed0,0x294014a0,0x3da01ed0,0x0,0x294014a00a5005280294014a0,0x4f402a601536,0x52802bc01680,0x294014a0,0x4c80294014a0]
def a1Marks42 : Array Nat := #[0x4d4426601420,0x50802f6017b0,0x27e013d0,0x9a084d0028401420,0x26a813520a1004f4027a013d0,0x27a014a0,0x2840142009b884dc0294017f0,0x138109c005280284014a0,0x27221390,0x4f40274813a2,0x5000276213b0,0x14a0,0x14a0,0xa2b062c031641960,0x14a0,0x278814a0,0x27a814a0,0x27a814a0,0x27a814a0,0x4f90294014a0,0x1460,0x29401ed0,0x14a0,0x528034e01ed0,0x29401ed0,0x90a05110240c12000a48074c038a01c50,0x52803da01ed0,0xa5807d4c3dc01ee0,0x288811ea08f2053003e401f20,0x14a0,0x14a0,0x14a0]
def a1Marks43 : Array Nat := #[0x14a0,0x29401460,0x14a0,0x294014a0,0x14a0,0x4fd0294014a0,0x280814020a000528028c01460,0x1460,0x14140a0905080294014a0,0xa1205088284014a00a5005090284414200a5005280294014a0,0xa500528029402310,0x14900a600528029402320,0x8c4029402310,0x14a0,0x14a0,0xa5005280294014a0,0x48d4246614a0095084a80294012c0,0x92085280248614a00a48050c024621233,0x0,0x14a0,0x0,0x14a0,0x14a0,0x294014a0,0x0,0x1460,0x29401470,0x528029401480,0x14a00a5005280294014a0,0x29c01ed0,0x53c044801ed0,0x29a014e0]
def a1Marks44 : Array Nat := #[0x19730cba8658c33061ed0,0xa800714c3be01c53,0x1dd60eeb87b4045201db6,0x3da01ed0,0x3da01ed0,0x2cc81961,0x765c3da022a0,0x3da01ed0,0x0,0x3da01ed0,0x0,0x0,0x3da02246,0x2bac17b0,0x2f6017b0,0x3da01ed0,0x0,0x15c0,0x15d0,0x57402bac17b0,0x2bac15d6,0x2a801656,0x2ae015d0,0x2a801530,0x2aa01530,0x2a601686,0x2a601530,0x2ba017b0,0x57402f6017b0,0x0,0x2ce41960,0x1510]
def a1Marks45 : Array Nat := #[0x56002f6417b2,0x0,0x0,0x630c318a1ab0,0x0,0x1ed0,0x0,0x32461ed0,0x1ed0,0x0,0x1ed0,0x1ed0,0x2ba015d0,0x568438a01c50,0x72c039621db0,0xac80714c3c201c53,0x1ed0,0x3da022b0,0x3acc1ed0,0x76983da022c0,0x1ed0,0x1ed0,0x3da01ed0,0x7b8045a01ee0,0x7dc43e001f00,0xad087ec43e401f20,0x56403e461f23,0x0,0x0,0x0,0x0,0x0]
def a1Marks46 : Array Nat := #[0x0,0x0,0x0,0x0,0x89c044802240,0x0,0x0,0x1530,0x15d0,0x0,0x22e6,0x0,0x0,0x15b0,0x0,0x54802bc022f9,0x2a6015e0,0x1530,0x1540,0x2b801550,0x2b001560,0xac0857402b001570,0x3dc61ed0,0x3da02246,0x58403e061ed0,0x2c0012500b10047803e461f23,0x1ed0,0x634c31aa1ed0,0x58c03c401c53,0x1ed0,0x0,0x1ed0]
def a1Marks47 : Array Nat := #[0x1ed0,0x1ed0,0x1ed0,0x1ed0,0x2a2c1660,0x2d001ed0,0x0,0x1680,0x2d001ed0,0x1ed0,0x1ed0,0x0,0x1680,0x0,0x0,0x2a4c1680,0x2a6c1680,0x1556,0x2a8c1680,0x2c801566,0xb20859002aec14a0,0x2a6c1680,0x2d001680,0x1ed0,0x730039821ed0,0x5ac038a61e70,0x1ed0,0x5b043f821f20,0x0,0x1ed0,0x1ed0,0x17b0]
def a1Marks48 : Array Nat := #[0x17b0,0x12e0,0x5bc02f2417b2,0x17b2,0x346416f0,0x19c1,0x264017b4,0x370416f0,0x5c4038a012e0,0x5bc038a21ed0,0x2e001c51,0xb7805bc038e21f21,0xb780734039821ed0,0x5b8038a61e80,0xb6805bc039aa1f23,0x3da022a6,0x1ed0,0x5c403f821f20,0xb8007f403e4216f0,0x2dc01f23,0x0,0x0,0x0,0x2de01e92,0x0,0x12e0,0x0,0x0,0xb7805b4025c02200,0x2240,0x1ed0,0x5c8038a21ed0]
def a1Marks49 : Array Nat := #[0x1ed0,0x12e0,0x0,0x0,0x0,0xbd805ec02f6017b0,0x0,0x17b0,0x17b0,0x1330,0x1350,0x2e6017400ba004d802e801740,0x2e8017500bab04dc02f6017b2,0x4e002f641740,0x2eac1390,0x13a0,0x0,0x0,0x17b0,0x17b0,0x17b0,0x17b0,0x17b0,0xbd805ec02f6017b0,0x5ec02f6015d0,0x17b0,0x13d0,0x5d982f6013f0,0x5e0037001790,0x17b0,0x2f6017b0,0xba005dd82ee01410]
def a1Marks50 : Array Nat := #[0x2e8217400bd805ec0284017b0,0x5ec02f601ed0,0xbe005ec038a01ed0,0xbd00714c2f201e90,0xbc805ec02f601f23,0x5e402f201fd2,0x1ed0,0x3da017b0,0x5e803e4617b0,0x17b0,0x17b0,0xbd805ec02f6017b0,0x5ec02f6012e0,0x0,0x17b0,0x17b0,0x0,0x0,0x17b0,0x29b217b0,0x17b0,0x2f6017b0,0x17b0,0xbd8059202f601582,0x0,0x5ec02f601790,0x0,0x17b0,0x0,0x2ecc17b0,0x0,0x17b0]
def a1Marks51 : Array Nat := #[0x5ec02eec1770,0x17b00bd805ec02f6017b0,0xba885ec02ea01420,0x1983,0x1ac3,0x1831,0x1830,0x30401ea0,0xc1006080400012b0,0x30401eb0,0x2296,0xc1007b003fe016b0,0x1ea0,0x0,0x1831,0x1820,0x6080408012b0,0x18310c180608044242214,0x0,0x0,0x0,0x0,0x0,0x1ed0,0xc2007e443f261f20,0x32e81ed0,0x618038a01c50,0x30a41c51,0x3bae1db6,0x1ed0,0xc3007e443f261f20,0x30a41f21]
def a1Marks52 : Array Nat := #[0x1ed0,0x1ed0,0x1ed0,0x1ed0,0x1ed0,0x31a41ed0,0x310012600c480480038a01c50,0x1ed0,0x0,0x0,0x0,0x628031201870,0x1ed0,0x31e01f20,0x1ed0,0x1ed0,0x32201c50,0x32041c51,0x1ed0,0x32201f20,0x32041f21,0x0,0x0,0x0,0x2246,0x1ed0,0x0,0x2ec814a0,0x1ed0,0x0,0x1ed0,0x1ed0]
def a1Marks53 : Array Nat := #[0x0,0x3da01960,0x0,0xcb00658032601876,0x0,0x0,0x650832c01960,0x19500cb00658032c01960,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x668038a012e0,0x0,0x17b0,0x0,0x2f0819c0,0x678033801c50,0xcf80670038a019c0,0x19c0]
def a1Marks54 : Array Nat := #[0x24e012720d08050c02f6417b0,0x1a20,0xd1006880428812b4,0x0,0x1a20,0x688042a816c1,0x688043a812b4,0x0,0x0,0x0,0x0,0x0,0x0,0x348012e0,0xd2006900428812f0,0x1a32,0xd19068c8408412b2,0x1a32,0x348012e0,0x346016d0,0x0,0x68c0406016e0,0x0,0x0,0x0,0x0,0x1a40,0x0,0x0,0x0,0x346416f0,0x68c840841700]
def a1Marks55 : Array Nat := #[0x690042a81710,0xd1805bc843e012b0,0xd2004b8043e812b4,0xd20068c834602214,0x0,0x0,0x0,0x0,0x0,0x17b0,0x0,0x1ed0,0x34a01c53,0x1ed0,0x34a01f23,0x34c81c50,0x1ed0,0x34c81f20,0x0,0x0,0x1ed0,0x0,0x0,0x1ed0,0x3da01ab0,0xd5206ac035601a90,0x0,0x0,0x0,0x1ab00d5806ac035001ab0,0x1ed0,0x1ed0]
def a1Marks56 : Array Nat := #[0x35a01c53,0x1ed0,0x35a01f23,0x0,0x5dd02ee414a0,0x1ed0,0x1ed0,0x0,0x0,0x1b040e280714038a01c50,0xf6807b403da01ed0,0x1b040f9007c803e401f20,0x448c1ed0,0x0,0x1650,0x15c0,0x17b0,0x17b0,0x0,0x0,0x36201c53,0x1ed0,0x1ed0,0x5ec02ba01ed0,0x2f6015d0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def a1Marks57 : Array Nat := #[0x1ed0,0x36401f20,0x6d0025c01c50,0x36641c51,0x1ed0,0x36801f20,0x6cc82e401f21,0x2f601ed0,0x2be817b20bd80659828a01ed0,0x0,0x1460,0x36e012e0,0x6d80336616d0,0x0,0x36c416f0,0x0,0x17b0,0x372212e0,0x6e0033861790,0x37001b800ce985e4043e012b0,0x6e0043a017a0,0x17b0,0x372217c0,0x17b0,0xdc005bd02de417b0,0xdc00678c43e01702,0x1ed0,0xdd00680c2f201c53,0x2f601ed0,0x1ba00b9205c8830001f23,0x6ed02f281a1009700714038a01490,0x2f6817b20bd807b403da014a0]
def a1Marks58 : Array Nat := #[0x6ed0302817c20be007c803e4014c0,0xde20714038a01c50,0x7b403da01ed0,0xde207c803e401f20,0xde80718038a01c50,0x7c003da01ed0,0x7c003e001f00,0xde807c803e401f20,0x1f61,0xe380714038a01c500e380714038a01c50,0xdf90714438a21cd0,0x1be00e280714039481d04,0x38a01d51,0x70483b021db0,0x71403c621ed0,0x71403ca21ed0,0xe2807c803da01ed0,0xe3007c803e001f00,0xe3807c803e401f20,0x1bf20e2807e003e421f21,0x38a01f91,0x38a01fa1,0x38a01fb1,0x38a01fc1,0x71403fa21c50,0x1c700fe887f443fa21c70,0x38a02064,0x714038a01c500e28084d038a01c50,0x42881c50,0x42a81c50,0x714042c81c50,0x71403a881e04]
def a1Marks59 : Array Nat := #[0x2074,0x103a0821037a02074,0x41081c50,0x41281c50,0x829038a01c50,0x42081c50,0x845038a01c50,0x714042e81c50,0x43281c50,0x710038a021a40e28064d838a01890,0x38a01c500e28071403d281e94,0x71c038a01e940e2807f9037881e94,0xf520714040081ea4,0x71403d881ff4,0x714038a02024,0x38a02044,0x38a02034,0x38a020b4,0x20d4,0xe280700041c81c50,0x2124,0x38a021b4,0x714038a01be00e2808710352c1a90,0x7140384021d4,0xe28070c043c81c50,0x38a01c500e28087d038a01c50,0xe4007cc03dc21ed0,0x7c003e021ed0,0xe4807c803e021ed0,0x1cd00e6887c803e421ed0,0x1cd00e7087c803f001f20,0x73403fa01cd0]
def a1Marks60 : Array Nat := #[0x73443fa61c50,0x2072,0x0,0x6f8c354c1aa0,0x734039a02023,0x2310,0x3a602320,0x1ed0,0x1ed0,0x1ed0,0x1ed0,0x3b2c1ed0,0x1ed0,0x3ec21f00,0x75443f421f20,0x3a801f23,0x0,0x0,0x0,0x1ed0,0x0,0x0,0x1ed0,0x1c50,0x0,0x0,0x1ed0,0x1c50,0x0,0x0,0x0,0x3ae01946]
def a1Marks61 : Array Nat := #[0x1ed0,0x3da01db0,0x0,0x75d43b601db0,0x0,0xed8076c0388618a3,0x1db00ed8076c032b21db0,0x1f03,0x3bc01f23,0x3c001f23,0x3c201f23,0x0,0x1ed0,0x1c50,0x0,0x0,0x1ed0,0x1ed0,0x1ed0,0x1c50,0x0,0x0,0x1ed0,0x1c50,0x0,0xf6807b403da01ed0,0x3fa21f200f9007f443e401f20,0x3dc61ed0,0x3e061ed0,0x3d001f23,0x7a403e461ed0,0x1e900e690808037e01fd2]
def a1Marks62 : Array Nat := #[0x82c03a802070,0x0,0x0,0x1ed0,0x1ed0,0x1ed0,0x1ea0,0x3d401c53,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1c00,0x0,0x0,0x0,0x0,0x1ed0,0x1ed0,0x0,0x1ed0,0x1ed0,0x1ed0,0x76c838201ed0,0x0,0x1ed0,0x1ed0,0x1ed0]
def a1Marks63 : Array Nat := #[0x0,0x1ed0,0x3da01960,0x1ed0,0x1ed0,0x0,0x1ed0,0x0,0x1ed0,0x7b403da01c50,0x3fa21f200fe987c8042681c70,0x0,0x2144,0x0,0x1ed0,0x3e402154,0x1ed0,0x1ed0,0x3da01ed0,0x1cf40f6807b4032cc1960,0x0,0x0,0x0,0x0,0x0,0x2074,0x0,0x0,0x0,0x2084,0x0,0x0]
def a1Marks64 : Array Nat := #[0x0,0x0,0x1ed0,0x41281f20,0x1ed0,0x41481f20,0x3b601ed0,0x0,0x1ed0,0x0,0x0,0x0,0x1ed0,0x3e402104,0x1ed0,0x3da01ab0,0x1ed0,0x1ed0,0x0,0x0,0x1ed0,0x1ed0,0x1ed0,0x1ed0,0x3da01ed0,0x7c8042281f20,0x1db40ed907b402d2c1ed0,0x0,0x0,0x1ed0,0x3da01ed0,0x1db40f6807b4031cc1ab0]
def a1Marks65 : Array Nat := #[0x0,0x1ed0,0x0,0x2184,0x0,0x0,0x2194,0x1ed0,0x1ed0,0x3da01ed0,0x3da01ed0,0x1db40f6807b4032cc1ed0,0x0,0x0,0x1ed0,0x3da01ed0,0x1ed00f6807b40356c1ab0,0x1ed0,0x1ed0,0x1ed0,0x3da01ed0,0x1ed0,0x3da01ed0,0x1ed00f6807b403da01ed0,0x1af3,0x1e60,0x1ed00f700798035f21af3,0x1e47,0xf68079243c8e1f00,0x1f200f9007c803e401fe4,0xf9007c8039a02024,0x3e402044]
def a1Marks66 : Array Nat := #[0x7b403c622034,0x7c803e402054,0x3e0020b4,0x3e4020c4,0x3e001d830ec0883903e401614,0x7c803b841dc0107a05aa83e401624,0x3ca22124,0x21b4,0xf68078cc3c6221d4,0x1f000f298794443c81f20,0x3e401f200f90087d03e401f20,0x3da01c51,0x7b40358c1ac0,0xf7007204316e18b1,0x3da01a74,0x7b4034f41a74,0x1ed0,0x3da01c53,0x7b403bac1973,0x3da01d97,0x3e001c93,0x3da01d67,0x3dc01da7,0xf800724c396018c3,0x1ed0,0x3da01d67,0x7b4038a618d3,0x7b4038a61cc0,0xf900734839a02200,0x3da01c51,0x7c8039a02210,0x1ed0]
def a1Marks67 : Array Nat := #[0x1ed0,0x81c842041d50,0x39a42214,0x1fd10fe807a4044002200,0x3d022212,0x1ea0,0x81d040e42070,0x2fc81ae4,0x11100898044802240,0x0,0x0,0x0,0x2230,0x22401119088c03da01ae4,0x1ed0,0x8a403da01983,0x2240,0x8a803da01664,0xaeb07b4032461680,0x45601ed0,0x8b0044801672,0x8ac03da01923,0x1ed0,0x2240,0x1ed0,0x2d0815e4,0x3da01684,0x0,0x3da014e3,0x29402310,0x3da014a0,0x448014f0]
def a1Marks68 : Array Nat := #[0x118808c4046202310,0x2310,0x11a808d804dc426f2,0x11c809acc4d6a26d3,0x8ec04f002781,0x23f012000a80854842aa0,0x12000a8c855842400,0x247012500a38c51ca2ae3,0x9200496028e314918a38c560628e3,0x247014798a3d455e62470,0x924049402b0315828ab8c55c62ae3,0x12500a84c54a62b23,0x12500ae0c570a24a0,0x12500af4c57aa2bf3,0x5fa63003,0xc28861842400,0x18418c21461c62470,0xc44c622a24a0,0x12000cfc8480034c0,0x9140494024a012500c9cc64ea34e3,0x48c0247019798cbd448e034f3,0x47e037201b880dd446e203710,0x494037131bb10dc4c6ec83713,0x24e01271094c051a02aa0,0x250012a00a40451c82b21,0x5f802ff0,0x4ac03010,0x2563,0x4ae02700,0x4b002b70,0x2e50,0x2400]
def a1Marks69 : Array Nat := #[0x2470,0x24a0,0x4b8025b0,0x0,0x0,0x0,0x0,0x0,0x0,0x2600,0x98404c002cc0,0x2d20,0x98c047082d30,0x2374,0x2d50,0x0,0x0,0x4d202d70,0x0,0x0,0x2da0,0x4d802de0,0x2332,0x46a42e00,0x0,0x2340,0x271016f008e505cc02580,0x4dc02e20,0x0,0x5c802e40,0x0,0x2e50]
def a1Marks70 : Array Nat := #[0x5ca02e50,0x0,0x4e402e60,0x0,0x0,0x2790,0x13100c1c061e82830,0xc200622028e0,0x4e602970,0x61c02ae0,0x23c2,0x4ee023b0,0x4cc23172,0x9e404ce62671,0x9e804f8028e314728ab8c632031b0,0x9ec04fa02b8315c28c7c0636024a0,0x13f80a38051c42ae015700ab80646034e0,0x14000a4c847c833b1,0x5020291014710a990648033c4,0xa0805044283015aa0ad8065803514,0x14180a0c065a03524,0x14710a38865c03580,0x514035a0,0x528035b0,0xa5c048e835c0,0x530035e0,0x3600,0x4aa03610,0x3620,0xa64048e83630,0x940466043640,0x938066203660]
def a1Marks71 : Array Nat := #[0xa38066003670,0x14300a5c052e03320,0x50403680,0x14d80a004536a2a1015380a9d4542a339011e90ce54678033c5,0x2402,0xa780682035a0,0x14d18aa00684035c0,0xa04c4a263440,0x49e03650,0x93c068a03660,0x2a1014d80948c68c03670,0x0,0x538a3690,0xa7d46aa03690,0x2aa01ad0094c06cc03662,0x57202ae013e20d78049483630,0xae806b8035c0,0x15d809f506bc035e0,0x1590095046c803672,0x0,0x6d6036c0,0x0,0x3710,0x6e203710,0x2aa015200db406e203753,0x2ae114708a390524236e0,0x15908a9446e223765,0xa9806e843773,0x56c02b50,0xa9c452603744,0x6e203710,0x0]
def a1Marks72 : Array Nat := #[0x0,0x57c035d0,0x0,0x0,0x58202f10,0x58202f03,0x58202f73,0x2400,0x2470,0x24a0,0x0,0x6e203710,0x3713,0x584025b0,0x3710,0x2c80,0x3020,0x0,0x0,0x0,0x2c70,0x25d0,0x4bc03030,0x58ec2c70,0x0,0x0,0x0,0x59202600,0x0,0xb0504c402f80,0x0,0x59a02cc0]
def a1Marks73 : Array Nat := #[0x0,0x0,0x2ca0,0xb3c059c02ca6,0x0,0x0,0x0,0x0,0x2d50,0x2640,0x2650,0x0,0x0,0x0,0x5ac02670,0x2d80,0x2d92,0x26a0,0x0,0x5b0c2d80,0x5b2c2d90,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2e50,0x2d50,0x5ce02f00]
def a1Marks74 : Array Nat := #[0x5ce62f10,0x5d282e80,0x5e002550,0xbb005e002f00,0x5e002f0017780bc005d002f00,0x5dc62f10,0x17880bc405da62f10,0x5e202f1017798bc405d202f10,0x5e282f00,0x5e682f20,0x5ea02740,0xbd405d4c2ea0,0x5ec02760,0x17b00bd005d6c2eb0,0x16b18b5845ac02790,0x5f202820,0x17c80be405d8c2ec0,0x5f202830,0x5f202840,0x2f90,0x2f9017c80be405dac2ed0,0x2f9017c80bb985dc02850,0x2890,0x5fa028e0,0x0,0xbec0598c2cc0,0xbdc059cc2f00,0x2960,0x5f402970,0x5f002f00,0xbe405e0c2f00,0x2fe0]
def a1Marks75 : Array Nat := #[0x60002ae0,0x0,0x2b50,0x5f062f10,0xbdcc59f22f10,0xbe4c5e2c2f10,0x2fe5,0xbecc59b22cd3,0x2fa3,0x2b60,0x0,0x0,0x2fc0,0x2fd0,0x0,0x2fd3,0x0,0x0,0x0,0x0,0x0,0x0,0x3170,0x0,0x304018280c44c622a24a0,0x3060,0x2bc0,0x58083340,0x60c02f20,0x60c62f30,0x0,0x3054]
def a1Marks76 : Array Nat := #[0x0,0x62083090,0x0,0x0,0x0,0x3174,0x318018d00c6c0636031e018d80c9cc64ea34e3,0xca40632835e01b180d7006b8035c0,0x654031a41af00d7806bc035e0,0x33101b880dc406e203710,0x19200cc08664037411bb80dc446e223711,0xce8066a03650,0xcd40682034501b880dd446e203710,0x33c019c80ce0c68e034801ba18dc4c6ec83713,0xd6806e203710,0x6e2037101b880dc406e203710,0x6e2037101b880dc406e203710,0xdc406e203310,0x1ab20dc406e2037101ad00d0486e203410,0x0,0x6e203710,0x1b880d70c684a34231b888d704684835c01a110d08468403713,0x37101ab90d1086e203321,0xdc406d2435521b880d1d06e203430,0x37101b618dacc6d8236b1,0x0,0x3710,0x7a5025e03794097004b8026001306,0x99284c8c284013e0,0x270813611bc084e0826c037800a100508028401420,0x14a0,0x14240a1105080294014a0]
def a1Marks77 : Array Nat := #[0xa88854402aa01540,0x2ba015d0,0x1546,0x7f542e003792,0x4d1826803780,0x17900bc8071cc2f403790,0x0,0x10f804ac0402016b00d8b058d836201630,0x0,0x33a01c50,0x10fa04ad042c819900d93063d8364018f0,0x10f805c0840a016e00d9b0641836601900,0x10fa04bc042c819a00da30645836801910,0x0,0x10f8067cc43e017a00dd306b5837401ad0,0x1e940e380de5038a01c50,0xff2071c06f281c70109a071c06f281c70105504b58414812d0,0x1cd00e6807a4839c03792,0x0,0xe800870039401fe00f480de403d2020e60acb083802b201210,0x38a61ec0,0x0,0x0,0x0,0x7f4c3fa23794,0x42641fd01bc907f4040441ce0108c05698422415a0,0x10b80818041801de010f804ac041201a60,0x8094404837941011880886f24202110100de4025001220,0x0,0xbfa05fc82fe014a0,0x6f6637b51c680e34071a038d0,0x1e180f0c078603c30]
def a1Marks78 : Array Nat := #[0x37a01ec80f6407b203d90,0x1f600fb007d803ec0,0x37b31f680fb407da03ed0,0x37a0254812a4095204a90,0x71c038e11c680e34071a038e01c708e34071a038d0,0x38911c500e34871a43970,0x1c580e58c72ca39f0,0x1d198e8d474863c33,0x1c680e94c74aa3ec0,0x37c01de10ee8878603ba2,0x37d01e200f0c078603c30,0x37e01e200f10078803c40,0xdf4078e437d0,0x1d898ec54764637f0,0xf14c78aa3c33,0x1e298f20c79263c53,0x79263c95,0x38601ed00f6407c003d90,0x1c380f8c07c623e40,0x24601c200914071003dc31ec989fcc7c463d93,0x1c680fa407d223ec0,0x38d01f680fb447d803ec0,0x38e01f680fc007da03ed0,0x38911f700fc407da43ed2,0x38f01f800fc007e003f00,0x714038d01f890fcd07da63ed3,0x1c680fd0c7e8a38d0,0x71c03f431fb90fd0c7e8638e0,0x20319019480464023,0x1c681058082c238d0,0xe34084404221,0x1c68108c0846238d0]
def a1Marks79 : Array Nat := #[0x1c681050c82a44172,0x8a0437d0,0xdf408be037d0,0x46a0234023110b8888c8438d0,0x21e990f54886637f0,0x11e8c8f4a38d0,0x47a323e111e8c8f4638e0,0x2201910146fe04443,0x11b888dc05a8a441316a1910546fe04453,0x8c064605,0xdfc08c264615,0x1220c910a38d0,0x38d01c68124c892844990,0x11f008f40704024001c6809000480038d012000d0084820497219f1090809304240012000cdc8486049c2,0x1c2008f8447c024701c68091c048e038d012380cb9449004923197189204924a247012380c8cc492049e3,0x70c038d0255012ac095204a90,0x38801ac2892c095863583125892b1449404a93125009280952624a0,0x1c68131c098e238d0,0x38e02638131c098e038e0,0x480224001c680e340480224001c680e3406da84d331b69134d471a038d0,0x48e024811c708e340486024201b7113108986438d026628ded46da44c32,0x1c681324c71a04cd5,0x1c681350c71a04d75,0xe14471a038d01c101354c71a04d85,0x9a064d05,0x1c681358c71a04d65,0x1c681344c71a04d25,0xe34071a038401c181328c99c64ce5,0x9b264d95,0x38d01c680e3009b464da5,0xe3409b664db5,0x720039021e200f10878603c30]
def a1Marks80 : Array Nat := #[0x1c900f18478a83c31,0x4980393012680e54052a03db01ec809f807c203d90,0x72e039721f700fb447da63ec0,0x730039821f700fc807e443ee0,0x72e039921f900fb447e683ed1,0x1cb80fd447e883970,0x11ec48f483970,0x944049c439721b7a1320098e238d0,0xe50072604cb0,0xe5c072e04d74,0x1e180f0c078603f90,0x78623fb0,0x1cd00f6407b203fd0,0xfb007d804020,0x4030,0x20181008080404020,0x10098804c4080,0x4734239a11d408e6821ea,0x1cd012a4095204a90,0x1cd80fb447d804020,0x39b020201014080404020,0x1e180f0c078604070,0xfb007d804080,0x12e0,0x4734,0x1d100e88474463ee01f708fb8c7d8039f0,0x39f0,0x39f0,0x1cf20e7c073e039d0,0x1cf80e7c073e039f0,0x7d8040d0,0x3ec0]
def a1Marks81 : Array Nat := #[0x3ec0,0xe90078603c30,0x74803a40,0x3c31,0x3ec0,0x0,0x74803a40,0x5c6437d0,0x3a40,0x0,0xdc446e0438d0,0x1e180f0c078603c30,0x14b80f9807b203d9014b80f9807b203d90,0x1f600fb007d803ec0,0x7e863ed01f680fd0c7da03ed0,0x80403ec0,0x3ec0,0x3ec0,0x78603c30,0x3ec0,0x3ec0,0x3c30,0x37d0,0x37f0,0x0,0x0,0x0,0x7b2040f0,0x7d004100,0x7b264110,0x7d804120,0x1f3b0fb0082604200]
def a1Marks82 : Array Nat := #[0x3ec0,0x3ec0,0xfb4082c04220,0x7da44141,0x0,0x7da64150,0x38d0,0x7da64170,0x7da64180,0x3ec0,0x0,0x0,0x3c30,0x3c33,0x3ec0,0x3ec0,0x3ec0,0x3ec0,0xe9c078604260,0xe9c078603c30,0x37d0,0x74e03a70,0x3a70,0x3c31,0x3a60,0x74c03cf2,0xf6447d804270,0x74e03a70,0x3ec0,0x0,0x38d0,0x0]
def a1Marks83 : Array Nat := #[0x3c30,0x3ec0,0x272c3aa0,0x3a9009b80ea8075403aa0,0x26a43aa0,0x75001420,0x3c30,0x0,0x75423aa0,0x50807d8042b0,0xa088f6407d8042c0,0x27a03ec0,0x278038d0,0x3c30,0xf28085e03ad0,0x0,0xeb407d404310,0x25d01d680a58c7d604320,0x3ad0,0x75c04330,0x75a03f60,0x3c30,0x0,0x3ec0,0x3c30,0x3ec0,0x3ec0,0x3c30,0x0,0x0,0x43a0,0x0]
def a1Marks84 : Array Nat := #[0x0,0x98807b204380,0x0,0x3970,0xf0c087204396,0x3c30,0x3a40,0x0,0x0,0x0,0x0,0x3c30,0x3ec0,0x0,0x0,0x3ec0,0x0,0x0,0x3c30,0x0,0x3c30,0x0,0xdfd05aa42d50,0x72224422,0x6fe84670,0x3c30,0x0,0x267013390ee004cc02662,0x0,0x89603ba0,0x4d0044d0,0x4d0044e0]
def a1Marks85 : Array Nat := #[0x1e180f0c078603c30,0xf0c078603a40,0x3c30,0x0,0x89e03be0,0x3c30,0x8a043c40,0x3c50,0x3c30,0x3c30,0x78603c30,0x75a04520,0x0,0x3cf0,0x3c30,0x3c30,0x3c30,0x78603c30,0x77a03c30,0xf0c029403c30,0xf0c078604560,0x1df00f0c078604570,0xef8077c04580,0x4d402650136009c408b202720,0x3bf01e200f0c08a804570,0x786045a0,0x45b0,0xf0c08aa045a0,0x786045c0,0x78a445a0,0x45d0,0x3c1022b80f0c05ae02570]
def a1Marks86 : Array Nat := #[0x170008d888b403c30,0x3c30,0x3c30,0x3c30,0x3c30,0x3c30,0x1e180f0c078603c30,0xf108786045e0,0x9ac878a43c30,0x3c30,0x78602e30,0x1e180b900786037d0,0x3c30,0x3c30,0x3c30,0xf0c078603be0,0x27a83c30,0xf0c078603a70,0xf0c078603c30,0xf0c078603c30,0x1e180f0c078603c30,0x0,0x0,0x3c30,0x0,0x3c30,0x3c30,0x3c30,0x3c30,0x78603c30,0x3c30,0xf0c078603c30]
def a1Marks87 : Array Nat := #[0x1e180f0c078603c30,0x0,0x0,0x4622,0x0,0xf0c05ca42e50,0x0,0x3c30,0x3c30,0x3f60,0xf00878603c30,0x0,0x3c30,0x0,0xf08878603c30,0x0,0x3c30,0x4670,0xf0c0786039c0,0xf0c078603c30,0xf0c077404630,0x1e180f0c078603c30,0x4dc44642,0x8c003a50,0x1e200efc072004650,0x78a03923,0x78603a72,0xf0c074e03a40,0x3ec0,0x0,0x0,0x0]
def a1Marks88 : Array Nat := #[0x0,0x0,0x39f0,0x3ec0,0x0,0x130c897184c2625c01e8011cc08e6021b0,0x76663cf0,0x8ee03d90,0x8ee03e00,0x3e40,0x11dc08ee03e60,0x3e80,0x3e86,0x3ec0,0x8f463ed0,0x11ec48f663ee0,0x0,0x8f843f00,0x11e808f403f40,0x3ec0,0x3ec0,0x3ec0,0x3ec0,0x0,0x3ec0,0x3ec0,0xf300626023a0,0x0,0x3ec0,0x79c04840,0x1e780ed4c90a03d93,0x79e03ec0]
def a1Marks89 : Array Nat := #[0x79e03b63,0x3ec0,0x1e820ee0090e03d90,0xa120f0c075643ab0,0x3ec0,0x91063ed0,0x7a083ac4,0xf4507b203d901ec805240912048d0,0x3ec01f600fb0029404a40,0xf45029804a50,0x7da03ed11f600520c91604a40,0xfb007d804a60,0x1ec80f6407b203d901ec80f64091c048e0,0x1ec88f64491e04901,0x1ea90f7c47c804961,0xa1407a4028301ec80a0c050603d9014180a1005060283014480930064c028c024880c940568849f4,0xa6004f4827e015c80f9807cc03d90194809150650024d024700f64094e037a0,0xf5c87d004a80,0x1ec80fb007d804a90,0x3da01f680fb4092644aa0,0x3d901f688fb4492844ab0,0x3dc014700fb5051c028e01f6a0a38065e028f024900c9c057004ac0,0x7b204ad0,0x7b204ae0,0xf6407b204af0,0x28101ec80cc807b204b00,0x28301ec80f64050603d901ec80f6407b204b10,0x28b01ea00f6407b2033301ec80e4c065004b20,0x4b30,0xf6407b204b40,0xf6407b204b50,0x3d801ec80f6407b204b60]
def a1Marks90 : Array Nat := #[0x3d9014480a1007b203d1414c00a64057204b70,0xa5c052e03d9014400a1c07a60298014c80a5c052e0297014b80f64048c8384419980ca4057404b80,0xf6407b204ba0,0x1ec80f5807b204bb0,0xa5007b204bc0,0x1ec80f64050a03d201ec80e74065604bd0,0x3e001f688fb0093204a90,0x3e001f688fb4493404ab0,0xf8007c004af0,0x53403f451a1008fc8932038d0,0x14e00f8007b204af2,0x29f01ef00d1c0704433a0,0x29b51f000d2007c004b02,0x7c402b001f6a0ac087daa34f015781278069c04a90,0x7d804bf0,0x7d804c00,0xa0947b204c10,0xf48c73c04c20,0x1f600f90094404c00,0xa7947bca3e401ab00f90070a43540,0x1f200f9007a863943,0x1f200f9007c803e40,0x50ca28631e998fb8c6ae24a301ab8128c470604c00,0x518094803ec0,0x3e601ae00929095203ec0,0x3e601f0012c0070c04af0,0x7c8036911b480e1c098003ec0,0x3ec0,0x3ec0,0x3ec0,0x3ec0,0x6d6038d0]
def a1Marks91 : Array Nat := #[0x3d90,0x7d803e80,0x7d003e80,0xfa007d003d83,0x1f400fa007d003e80,0x0,0x3ec0,0x6d803ec0,0x3ec0,0x3ec0,0x3ec0,0x3d90,0x0,0x0,0x1f600fb007d803ec0,0x7da03ed01f680fb4098e04c70,0x14720fb4c7d804c30,0x2b0114908fc087da44c40,0x15600a3d07e8836d026180e5c099a838a0,0x520829021f718fb006de24c501b781314473e038b0,0x3ec0,0x3ec0,0x3e42148a0f5407d804c60,0x3ec0,0x7d803700,0x3ec01b888dc407d8038d0,0x55622a021fa18fb406ea0372026380fb409a6638e0,0x56683ed21bb00dc8899223ed2,0x7c883e421f600dd106e843ec0,0x0,0x0,0x3d60]
def a1Marks92 : Array Nat := #[0x3ec0,0x3ec0,0x3ec0,0x3ec0,0x72e04dc4,0xfa087ae03ec0,0x3ec0,0x7d803ec0,0x3ec0,0x3ec0,0x0,0x3ec0,0xfb007d803d90,0x1f680fb407b404d43,0x1f700fb807b604cb0,0x7c883ec01f600f700994039f0,0x0,0x3ec0,0x0,0x7d803ec0,0x7d803ec0,0x1f220fb007d803ec0,0x0,0x4d03,0x0,0x0,0x3ec0,0x3ec0,0x7d003ec0,0x0,0x3ec0,0x7d8039f0]
def a1Marks93 : Array Nat := #[0x0,0x7d803ec0,0xfb407da04d63,0xfb487da44d11,0x1f420fa087d803ec0,0x0,0x7d803ec0,0x1f420fb007d8039f0,0x0,0x0,0x3ec0,0x3ec0,0x7d803ec0,0x1f420fb007d803ec0,0x0,0x3ec0,0x7d803ec0,0x1f600fb007d8039f0,0x7d803ec0,0x7d803ec0,0x3ec0,0x7d803ec0,0x1f600fb007d803ec0,0xfb407da03ed01f680a38c51c64cc3,0xfb4054263ed01cb88dd886ea04cd3,0x1f680fb407c024d73,0xfb407da04d23,0x7d803ed01ec98f8c072c64ce3,0x7da03ed01ee18f94074004cf3,0x7d204d93,0x3ec01f680fa4074a64da3,0x7d803df31ef88e3506ee43770]
def a1Marks94 : Array Nat := #[0xfb4072e24dc3,0x1f680f80472e24dd2,0x7d8038d4,0x7d8038d4,0x7dc03a20,0x3ef0,0xfb407cee4de2,0x7d803d91,0x3ec0,0x3f411fa00f98c9ba04dd0,0x20101008080404020,0x4020,0x4020,0x4020,0x3f90,0x3c30,0x1fc00fe407f204570,0x3f90,0x0,0x4020,0x0,0x3fb0,0x8ee03fd0,0x4020,0x4020,0x3c31,0x8eec3d90,0x3ec0,0x0,0x4020,0x7f6045a1,0x0]
def a1Marks95 : Array Nat := #[0x3fb0,0x7f803ec0,0x4020,0x402020101008029e04a60,0x1fe81008080404a90,0xff407fa04af0,0xff407fa04b46,0x1ff01008080404bf1,0x3ff01ae80929095204020,0x4020,0x20101008080404020,0x40201b988dc40804039b0,0x1008080403fd0,0x0,0x4020,0x80404020,0x4020,0x0,0x4020,0x80404020,0x4020,0x2010100806e663731,0x1008080403fe0,0x80404020,0x20101000880003ec0,0x20101004880204020,0x0,0x20101008080404020,0x40d0,0x3ec0,0x81a04c00,0x818040d0]
def a1Marks96 : Array Nat := #[0x1034081a040b0,0x0,0x0,0x38d0,0x0,0x0,0x81c240e0,0xab0904c083cc4206,0x1530,0x2a4038d0,0x40e0,0x15d0,0x37d0,0x0,0x0,0x11cc08e602196,0x11cc88e642129,0x0,0x15d0,0x37f0,0x38d0,0x2ba04789,0x0,0x103c095c04a90,0x10440952624a0,0x73604dc5,0x0,0x104c073604de4,0x0,0x4120,0x82604e0b,0x39f0]
def a1Marks97 : Array Nat := #[0x0,0x16200b080586041a012e011cc08e602186,0x0,0x83404190,0x3ec0,0x3c30,0x3ec0,0x3ec0,0x4020,0x0,0x3ec0,0x0,0x0,0x0,0x40e6,0x3c30,0x83603f90,0x83803fb1,0x0,0x4200,0x3c33,0x3d90,0x3d93,0x0,0x3e88,0x3ec0,0x0,0x0,0x3ed3,0x4020,0x4020,0x2d003c33]
def a1Marks98 : Array Nat := #[0x0,0x3fb2,0x3ec0,0x1680,0x4200,0x84004200,0x84004200,0x1008073643710,0x840041e0,0x0,0x0,0x83e03ec0,0x84004020,0x83e03ec0,0x84004020,0x0,0x83e03ec0,0x842040d0,0x0,0x3ec0,0x84804196,0x84a04023,0x16f0,0x74c04481,0x3a70,0x4732,0x75001740,0x3a90,0x3aa0,0x1740,0x17b0,0x85201790]
def a1Marks99 : Array Nat := #[0x4730,0x2e823ab0,0x0,0x4734,0x0,0x17b0,0xa1010a8085024280,0x85a03ac0,0x21700eb408de01c53,0x85c01c73,0x85c01cd2,0x85c01e90,0x1d8011bc060601ea0,0x1fd2,0x2130,0x85c02200,0x7f464340,0x43a0,0x0,0x4350,0x16580b24058684370130811cd08e6820da,0x10d8086e04350,0x4360,0x3970,0x0,0x39f0,0x4390,0x4390,0x87204390,0x4390,0x0,0x87203a40]
def a1Marks100 : Array Nat := #[0x4390,0x0,0x872c3c30,0x872c3c30,0x3c31,0x3ec0,0x43a0,0x3ec0,0x3c30,0x3ec0,0x32c03c30,0x32c03c31,0x10ec086ac3d90,0x0,0x3e8a,0x3ec0,0x1960,0x40d4,0x6fe84670,0x21f0110885aa02d50,0x852819c0223b111c076804480,0x3b50,0x3b60,0xedc089001ea4,0x89203b80,0x89401c70,0x89401f20,0x89401fd1,0x1e94,0x1fe4,0x1f06,0x77401ee2]
def a1Marks101 : Array Nat := #[0x78603a40,0x73801ab0,0x3c30,0x3c30,0x42e0,0x1118077a044a0,0x77c01c50,0x1cd1,0x78401db0,0x78601ed0,0x78801ee1,0x78a01ee4,0x1f01,0x1f21,0x1fd4,0x1e94,0x7f202240,0x7f622241,0x7f004660,0x89e03f90,0x3fb1,0x41b0,0x41c0,0x3c30,0x3f90,0x3fb1,0x4090,0x40a4,0x2298115c08ae04570,0x8b4045a0,0x459016f80b7006b2025a0,0x8b604270]
def a1Marks102 : Array Nat := #[0x17200b9008ae0454222a0119405c802e40,0x22d0115405ca02e50,0x8ae04660,0x45a0,0x7d8038d4,0x4670,0x0,0x4680,0x0,0x4680,0x0,0x0,0x4830,0x0,0x0,0x39f0,0xbb805da0469023520bc005e0039d0,0x17628bb0c8d2639e0,0x39f0,0x1ab0,0x3ec0,0x8d603ec0,0x111cc8d603cf0,0x3d93,0x3ec0,0x0,0x3ec0,0x0,0x0,0x3b743cb0,0x41d4,0x1cd4]
def a1Marks103 : Array Nat := #[0x1120c38a63cf0,0x1c73,0x892642d00de011cc08e603d00,0x239811cc037603d10,0x17c80be405f202f9023680bbd85cec469617780b9c08d203d20,0x11cc08e601b94,0x3d60,0x8e483d70,0x1794,0x11b9086c03d80,0x8e683d90,0x4734,0x11cd08e681b84,0x67008de83dd0,0x8e883e00,0x4734,0x11cc08e601b73,0x0,0x4732,0x11cc88e641b63,0x3e40,0x8da04730,0x236811cc08e601b50165c8b11859662c40,0xbfc090e03e60,0x0,0x4723,0x3e70,0x3e80,0x4725,0x4730,0x0,0x8e601a43]
def a1Marks104 : Array Nat := #[0x3ea0,0x3eb0,0x17b4,0x0,0x3ec0,0x3ed0,0x3ee0,0x0,0x0,0x4734,0x4744,0x3f00,0x91003f40,0x0,0x16f5,0x8e644734,0x4732,0x8e641a33,0x8de03f60,0x25c64700,0x8e6047300d1191cc08e601a23,0x30684730,0x1b06,0x34ac4730,0x30d24730,0x8e2018492398109188e6041a0,0x30ae4730,0x8e6047300c1011cc08e601820,0x2a0c4730237010ee48e604373,0x26204730239811b408d4c46a0,0x11cd08e644730,0x8ea03fd0]
def a1Marks105 : Array Nat := #[0x4020,0x4030,0x4750,0x0,0x40d0,0x4200,0x4220,0x2bac46c3,0x43a0,0x4760,0x0,0x3fc3,0x477023b80ff40968039a0,0x83c44e04,0x38a047d4,0x71c08fa847d4,0x0,0x3d90,0x7fa04df4,0x3fe1,0x40b4,0x0,0x8f4a39b0,0x39a047d2,0x3ec0,0x8ee04020,0x11dc096a040f0,0x820040d0,0x0,0x0,0x1db0,0x41f0]
def a1Marks106 : Array Nat := #[0x4250,0x840039b0,0x4001,0x4200,0x1db6,0x4010,0x40c0,0x4210,0x82403ec0,0x82604020,0x4023,0x4023,0x0,0x6180308423d2105c09a484150,0x3d2047d0,0x23d1908809ac64160,0x82e04deb,0x2243,0x1ed0,0x1ee0,0x1f00,0x1f06,0x3e4047d4,0x0,0x0,0x1ab6,0x1969,0x0,0x0,0x0,0x0,0x3ec0]
def a1Marks107 : Array Nat := #[0x4020,0x4030,0x4e09,0x40d0,0x84404db3,0x0,0x0,0x0,0x0,0x4790,0x3fa047d2,0x11e848f404773,0x8ee64df0,0x23ea088008fa447d0,0x2246,0x4080,0x0,0x0,0x11fc090204810,0x480018a00c4806be62c60,0x42a4215110a8090602310,0x28c04830,0x2428109d084e43ec0,0x90c04810,0x215a10ac885603ec0,0x243810b0885804080,0x29404830,0x4a4025201290094802310,0x91204a90254812a4095202320,0x63a231d024500c840640048c01ac28c7009586358318e092b1463604a9318d80c6c0952631b0,0x48d025281290094804a90,0x247012a4095204a90]
def a1Marks108 : Array Nat := #[0x48e0257812bc091c04af0,0x91e04900256892a4495224c00,0x2470137d09be84df4,0x495024c812ac095204a90,0x1264098e24990,0xce5468c049901a080cd8093204cd5,0x98004c00,0x4a701af00c6d095204a901af00c6d095204a90,0x95e04a90254812bc095204a90,0x678835a01b390d98896004a901ba08dc4095204990,0x6c2035141b4012bc095203682257912a40962048e01ad00d2406cc03662,0x4b30,0x96804a90,0x12a4096a04a90,0x4a9025b80d78069c031e4,0x1ae00d700952033b324b18d908676249611b2012e006bc04a4018fa122d06e263711,0x1af00d7809520353225010d4c094004b901af00d780952032141902123106e863741,0x25480d840952049011b4112e806a003672,0x4a90254112a0097604a60,0xd8006b604bc0,0x98004c00196a8cb4c92264c20,0x1b68130c069844992197a135d092804c73,0x1b880dc409520499224c8137506e203710,0x98004a20,0x37502638130c46cc24af126e90d14466044dd2,0x37601a41928c06ce23461,0x4a40,0x4a60,0x95204df4,0x4be0,0x95e24df2,0x4c00]
def a1Marks109 : Array Nat := #[0x4660234111b808f049ce44e92,0x8d4046a2238011d81398c9cca4eb3,0x236011b088e4047403623,0x4d4025d413a009d909ca04ec4,0x26b0134089b8c4f084e60,0x26301360138404be82774,0x26d0137889bcc4ea84eb0,0xb4485a443711,0x3710,0xb48c5b443711,0x5b004e20163a0bad05e403096,0x5b204e2316c88ba8c5e603106,0x95805ea02f6427130c1809c403066,0xb6c09c602db116e19390062403163,0x2d3016f00b8045c063134,0x5a002df017088b84c9c883144,0x2e4016a88b9445aa62e53,0x10e007440434c1889107b058184340188310780580037601440,0x1198117886fc04f421be80df406fa037d0,0x470043f51c0013c0c87e63801278290f0c70204f13,0x91c048022400261a0e3809ee64c321c7093dd471a038d0,0x4900244112081330c71c04f731c701310871e037b326998e3809ee638e0,0x4a442500127813150730039701cb8130c073204f74,0x4aa6255112a80e84074223a13,0x74803a40,0x74e03a70,0x99804e80274413b0,0x12f00f74c76004ee012f810c0075e04ef0,0x1130077604f20,0xef8077c0264022980f0409e602690,0x0,0x117c078e44f42]
def a1Marks110 : Array Nat := #[0x9ac079203a30,0x9d8076e63b43276989dc079e03cf0,0xa0c07b203d9014b8123807cc04f60,0xa7407c003e001540125407cc04f60,0x51464a10,0x56882bb013da0aa407c202ba025c00e2109640395025380f9809ec03e60,0x0,0x0,0x1471931c07e864f73,0x15118a88451a03a1026410fd4499003f53,0x56263f72,0xab4c546228f026980fd009ee03f4026680e64c99203890,0x0,0x0,0xaf007fa03fd015f0123807fe04f60,0x0,0x0,0x0,0x30403790,0x0,0xecd876604ed0,0x34403794,0x458222c013cc05ba02590,0xb8405b644260,0xf29879404ee0,0xc100688c40e02076,0x30f418220c2c09760411425b010e0096803ff0,0x30d318508c2009ac0423426901060c9a204140,0x40e03790,0x4821241013d4062a02c50,0x0,0x19580c9406540318419400c88096e048902588123809ec048e02538123809ec048e0]
def a1Marks111 : Array Nat := #[0x1a200c90c686033801a080cd4898c84c3224d013dd493204990,0x0,0x4af2257813d806bc031b4,0xd490974048f1258812bc09ec04af018ea0d28096004950,0x196193044982036a119ea0da8067a44a10,0xd014994232e11a581270099c832e124921361067c049802662130c09ee84c30,0xcbcc69a233f226b9926849a8649322699931c09ee64c70,0x4d71266893dc49ae04cd027b812c1496064f63,0x12d2496864f63,0xe3409fe44632,0x1c6813ecc9f6a4fc3,0x37d01be88dfc0a0665035,0x6f8037e11c00140cca0664da3,0x1c800e44072445034,0xe700738239c3,0x4670,0x74c03f62,0x1d400eac475664280,0x13e407b264fa0,0x7da44fd0,0x4510,0x78603c31,0xef407b204fe0,0x3ec0,0x7da24ff2,0x7da84610,0x1de993e0c7b264860,0x1df00eb5079e85010,0x1df80eb9079ca5010,0xf00078023cd3,0x4e203c101d7a0f310a0204bc0,0xf08078423cb9]
def a1Marks112 : Array Nat := #[0xf0c078623c33,0x1dd10f10478a65033,0xee4078c23c63,0xef0877883c83,0x3b101dd88f1cca0604d90,0x4020,0x4020,0x1fc00fe807f805010,0xfe407f603fb2,0x10240812240a0,0x106c0838241d1,0x4730,0x43a6,0x111809f0046f4,0x4734,0x4510,0x9fc04a90,0x8a444a91,0x3c30,0x89064f90,0x21701128c8fa047d6,0x227810bd08ec84b36,0x21e8112c48a064d06,0x4730,0xa0004a93,0x4a40,0x8a60430423fa14040a0204854,0x7b204864,0x454022a890f8ca06a4845,0x22b0115848ac64830,0x457022d0940408b464814,0x4580218a140408b664824]
def a1Marks113 : Array Nat := #[0x22e0117048ba647e3,0x4673,0x2e2022f00b50487e24e90226a93990a0684625,0x44c222f89100ca0664603,0x4029,0x3ec0,0x7da04613,0x1c6a140808c624633,0x10cc0a062442028181404c88424653,0x434023401404c8d0c4663,0x97a049f425c812290964049b0,0x9b0049d326a8125c499e04920,0x4590279813b1086484ef4271a13a0090084f54,0x4410278013a8c89c24f212738939808c864f43,0x13f809f485004,0x13ec09fa24ff3,0xa18050c6,0x282114100a1a050d6,0x0,0x0,0xa0c45060,0x0,0xa2c0516028b014580a2c0516028b014580a2c0516028b014580a2c05160,0xa260516028b015680ab4055a02ad015680ab405160,0x516028b016d80b6c05b602db016d80b6c05160,0x28b018400c2006100308018400c2005160,0x19b40cda066d0336819b40cda05160,0x28b019f40cfa067d033e819f40cfa05160,0x28b01a480d240692034901a480d2405160,0x1b5c0dae06d7036b81b5c0dae05160,0x28b01bc00de006f0037801bc00de005160,0x28b014580a2c0516038501c280e14070a0385014580e1405160]
def a1Marks114 : Array Nat := #[0x28b01c900e480724039201c900a2c07240,0x28a01cd40e6a0735039a814580e6a07350,0x514428a114500a2c0516028981cfc0e7e073f039f814580e7e073f0,0xa2c0516028b01d080e84074203a1014580e8407420,0x14540a2e0516028b01d400ea0075003a8014580ea007500,0x28b01e300f18078c03c6014580f18078c0,0x28b014580a2c051603dc81ee40f72051603dc814580f7207b90,0xa2c0516028a81fa40fd2051603f481fa40fd207e90,0x28b01fb80fdc051603f701fb80fdc07ee0,0x1fd40fea051603fa81fd40fea07f50,0x28b0200810040516040102008100408020,0x28b02030101805160406020301018080c0,0x516028b0206010300516040c02060103008180,0x2094104a0516041282094104a08250,0x20b40a2c082d0416820b4105a082d0,0x28b014580a2c0516028b020dc0a2c0837041b820dc106e08370,0x14600a3a051b028d8156c0ab6255a02ad015680ab4051b0,0xa36051e028d816dc0b6e25b602db016d80b6c051b0,0x1b600db606d7036b81b5c0dae051b0,0x1b70cdb8a6d73373194580dae66d73,0x1fd80ff4051603fb09fd40fea07f50,0x28c8209cca2c0838041c0a094d04a68253,0x28d020b80a2c0839041c8a0b4105a082d0,0x28d8146c0a340519628c820dc0a2c083a041d0a0d8d06c68363,0xa4e05240292016e00b6c05b602e2016d80b6c05240,0x1b640dae06d7037201b5c0dae05240,0x1b744dae26d71373894580dca26d71,0x521029001cdd0e6a8735439e2145810ce07354,0x14880a4c0524029201d440ea0075003a80149010d007500,0x1fdc0fea052403fa81fd410d407f50,0x1fe18ff8c51603fab1fd590d607f56,0x291820a1ca2c083b0412ba095d0d808257]
def a1Marks115 : Array Nat := #[0x2920148c8a4605240290020dc0a2c083c041a520d290da0834a,0xa5405300297018440c200610030e818758c20052e0,0x29601b680dae06d7037201b918dae052e0,0x14b40a5e052e029701d480ea0075003a8014b810d008686,0x536029b014d40fe4051604258a12ccfd207e90,0x29b014d80a6c0534629a020dc0a2c084c04260a130d06008300,0x14e00a72053902ad015680ab405390,0xa740539034901a480d2405390,0xa74053a636b81b5c0dae05390,0x53b02ad015680ab4055a02ad015680ab4055a0,0x53e02ad0157c0ab405bc02db016d80bd4051b0,0xa78053d02b0495424ba005f00,0x14100a7e050912ad015780abcc6140308018400cea051b0,0x152c0aba055d6336819b40ce805370,0x15300ac0055a033e819f40d3205160,0x15380ac0055a034901a480d3205390,0x153c0ac00560635b81adc0dcc05160,0x15480ac00560636b81b5c0dcc05390,0x2a9015800ac8053a0,0xa84855202b1815940a9c05520,0x154c0ac00560637301b980dcc055a0,0x55602b1815680aaa06f00378015540e1405160,0x2aa815d00de407f50,0x2aa015540af2082d0,0x158c0ab4055a02b1815680ab4070a0385015680e14055a0,0x56302b2815818ab407240392015680e4805606,0x2a0815880ac4c568039a815680e6a07350,0x15050a82454102b1815680ac6c55a02b4814ec0e7e055a039f8158c0e7e05636,0x2ad015680ab4056a03c2814580e8407420,0xab2050742ae015680ab4056b03c3014580ea007500,0xab4056d03d5814580f18078c0,0x14184a0c05084284115680adc051a03e2814580f6c07b60]
def a1Marks116 : Array Nat := #[0x14244a12055a02ad014244a12055a02ad015bc0f8a051b03e28146c0f7207b90,0x14294a14655a02b8014484a2407c502ad014740f8a07c50,0xa1625090284815680a1665090284815680ab2050562a6b14140a9a057103f98147c0a14284d12851a134ca1207e90284814240fd205090,0xab4057303f8014e40fdc07ee0,0xaaa05740401014580fea07f50,0xab40575040101568100408020,0x2ad0155c0aec0818028d82138d018080c0,0x15680ab40577040c01568103008180,0xab005780413814e4104a08250,0x15558aaa0579041b81458105a082d0,0x55a02abb155c0af40837028d8213cd05c082e0,0x55a02ad015618ab0057b041b814e4106c08360,0xab4055a02ad015680ab4057c041b81568106e08370,0x2b18158c0ac605750289815a810fa056a0,0x2ba815580ae805740,0xaaac57c0289815d190fc05746,0x56102be015580af205790,0x2c18160c1053051604280a06210dc08188,0x58302c181604103c65160428821444fd267e93,0x2c18160c0b04058302c0020dc0a2c085204290a0ae50de082b9,0xb100587033e819f40cfa05870,0xb0e058602c3816141056e51604298206290e20818a,0xb12058902db016d80b6c05890,0xb12058b0308018400c2005890,0xb140589034901a480d2405890,0x36b81b5c0dae05890,0xb1e058f02db016d80b6c058f0,0xb20058f037801bc00de0058f0,0x58f03c601e300b1e078c0,0x59003fa8163c0fea07f50,0x2db016d80b6c05b602db016d80b6c05b60,0x16840b42c6310]
def a1Marks117 : Array Nat := #[0xb22c591029e0171c0b8ec63a0,0xb6c059302db017200b6cc59302e4316d98c8e051b0,0x5c202e4816340b96c6510,0xb22c59202e6016340b9ac65c0,0xb6c05c60308018400c4005890,0xb7605c50336819b40cec05840,0xb3a059d22db016fc0b6c05bf22db116d88d0e05240,0xb7a05b6033e819f40d0205870,0xb8005b6034901a480d3805890,0xb6c05b602db416da0d5245160,0x5b6033eb19f58d5ac5160,0xb6c0692634b31a498d68c51b0,0xb6c06152308118408d5c45240,0xb3e05b6030819840cd5e45160,0x336919b48d6c45160,0x358c1ac60dce05160,0x36b81b5c0dce05890,0x5ce0,0x37381b9c0dce05b60,0x16880b8405b6033e999f4cde805160,0x5a602e1816d80b4a06923349196940e1405160,0x2e8816940d2e66d73,0x16900b4a08259,0x16a40b8405b6037801bc00de8058f0,0x170c0b6c05b602e1816d80b6c070a0385016d80e1405b60,0xb9c05b6039201c900b6c07240,0x5b6033ec9c358a2c067d9,0x2ca8170c0ba4070e6,0xb22c5b6034949c3d8a2c06929,0xb1ac5b6037831c418a2c06f06,0x2c9316358b6c0706928cb1c5d8a2c07069,0x2c9816d80b6c059302db016d80e14c717628d81c5d8a36070a6]
def a1Marks118 : Array Nat := #[0x2ce016500b6c0717638bb16d80a3c07176,0xb3605b6039231c9d8b1207246,0xba205a5036b99c90ca2c06d73,0x59702e8817480b4c05d10,0xba405b6039219c90cb6c07243,0xb2605b602e98169c0a7a0724939f8146c10e407249,0x59c039a81cd40b6c07350,0x16800ba805aa039a91cf08b1207352,0x16804b40059c02db017540b6c053e039f81cfc0b6c073f0,0x16d80b6c05b603a101e4c0a2c07420,0x5ad02dc816d80b6c075603a801e680a4807500,0x2d7816d80b6c05ba03a819ea80a2c07503,0x5b603c601e4c0b1e078c0,0x16d80b60078c62d801ee40a2c078c6,0x16c00f24c7f56,0x16c00b4808259,0x5b602db016d80b6c07b902db01ee40b6c07b90,0x16d80b7c079123e6814900f18478c2,0x5b603e9b14580f19078c8,0xb6c052323ec914580f6527b29,0xb6c05b602db016d80fb2452403ec914900f7247b92,0xb6c07d922db0149c0fb247d92,0x16d80b6c05ad03f4816d80fd207e90,0x5b603f7016d80fdc07ee0,0x5b603f8916240fdc47ee2,0x5c203fd014580f9067c83,0x5c203fd0163c0fea07f50,0x5c203fd016d80ff407fa0,0xb8605b60401016d8100408020,0x17080b6c080c02db020300b84080c0,0x2e1816d80b6c081802db020600b8608180,0x5b604071163c1018480c2]
def a1Marks119 : Array Nat := #[0x16d80b6c059d040c116d8103048182,0x412816d8104a08250,0x5b00406314580feac7f56,0x16c40b6c0818628d8200990e608026,0x5b60406316d81018c80c6,0xb6c05b6040c316d81030c8186,0x16d80b64081e6292021545019080c8,0xb6c05b302db016781056c529042b0a06210e808188,0x5b4041431624104ac8256,0x16d80b6c05af02d70168c103e6533042b8215c4fd267e93,0x16d80b5008293292021604fdc67ee3,0x5ab04139963c104a68253,0xb6005a5041b81458104b28259,0x2d8816d80b4e0837028d8209e50ea08279,0x2db016c80b500837029202164505128289,0x5b504170163c105a082d0,0x2db016d00b6c05aa041b81624106908348,0x2db016d80b6a05ab041b8163c106c68363,0x5b602db016d80b6c05b6041b816d8106e08370,0xb8405900,0xb8605a90,0xb6008609,0xb8205a60,0x5d102d2816640ba2087a9,0x2ef019b40cda05dd0,0x5dd02ee817700bb6082b328b0216810b427e93,0x2f701b5c0dd005df0,0x2f5817b00bd405e5033e997940e1405160,0x5e502f2817d80bca08186,0x2cc317b00be205e80392194e4cdae65f00,0x5eb02f4820080b1e07f50,0x20618a2c07f56]
def a1Marks120 : Array Nat := #[0x5ea02f5020618bd408186,0x2f2820dc0a2c081c9,0x5f002f8016698bec05f00,0x2fe019b40cda05fa0,0x5fa02fd017e40bf00830028b0216c10b627e93,0xc2006100308018400c2006100,0xc2c0610034901a540d6605890,0x18040c200618030c118408d72052e0,0x604030d01b3c0dae06090,0x30d01b5c0dae06100,0x30d818040a5806190,0xc34061a0,0x610038b01c580c20058b0,0x30801c900e4806100,0x2ff81b5c4dd225fa0,0x1b5cce6a45160,0xc0e0605030101cc88e6a46090,0x30181cd48e6a46100,0x6060301818000c200610029f81cfc0e7e06100,0x304018440c20061003ab81d400f58052e0,0xc1406100309018400c12075813a8098240f7205160,0x18340c200610030981d40cf7a05160,0x308018400c20061003dc818400f7206100,0xc20061903f2118400a6007e42,0x610030c818400c1007e90308014c40fd206190,0xc34061003f7018400fdc061a0,0x610030d81fb88c2007ee2,0x20280b0e07f50,0x6100308020600c2008180,0xc200610041491630103048706,0x18400c2006100308018240c1207e9128b01fa44a2c07b94,0xc200610030501fa44c2007e91]
def a1Marks121 : Array Nat := #[0x6100307817928c20059f441589624103088716,0xc2006100306818300c38083002970217010b627e93,0xc200609041b8145810ba07ee5,0x308018400c2006100308020dc0c2008370,0x31101b5c0dce06100,0x624031001c900e4806200,0x315098a40c62063102a0019000c6206310,0xc9c0600036b818c40dd206100,0x315218a88c80063a031d018e80a88063a0,0x19840a280545036b998e80e7e05160,0x63c031e818f40c0486022330814500e7006440,0xcbe0625039a818f40e6a06470,0x6400320018b04c580661028a019880c8206626320815180e7e06410,0x18b44c5a066103128191c0c8e0547039f819000e7e06470,0x62e1330818d40c5c06510331319440a9006510,0x330818e80c5e862f232d019680a92065a0,0x3238191c0c8e064103a1019040f7205160,0x64303238191c0c90064103a8199100f7c05160,0xca8064604060163c0fea06510,0xcc20641041b814580fd6665a0,0x336819b40cda066d0,0xdae066d0,0x3368176c0e2a05160,0x33681c540cda05de0,0xe5a65360,0x318218c08c4c066d03368152c0e7e066d0,0xcca066e0336819b40f8405160,0x333019984cdc066e1336817e00f8605160,0xcce066d0336819bc0f8c05160,0xcce0667033801dbcca2a67c70,0x33681f0c0cda05fc0,0x336819b40cda066d03f7114580fdc45160]
def a1Marks122 : Array Nat := #[0xcda066d033281fc80bf4084b3,0x19b40fdc466d0,0x102405830,0x336819b41030066d0,0x66d0336820a48bba086e6,0x19b40cda0667041b8145810ba485d4,0x336819b40cd406636336820dc0bba086f6,0x336819b40cda06646332020dc0bf4084c3,0x19b40cda066d0336819b4106e066d0,0x19b80cd2066603388217890c828622,0x3368199c10ba48650,0xcfa067d033e819f40cfa067d0,0x1b5c0dae067d0,0x33e819f40cfa067d0385019f40e14067d0,0x67d033e819f40cfa0724628b01c918a2c070a6,0x33e81c918cfa07246,0x1c704b0606d71,0x63343139189c0cfa067d02a601cfc0cfa073f0,0x67a033f019f40cfa075403aa11f240a4807500,0x19ec0cfa067f033e81f2c0a2c07501,0x67d02c301f540a2c079a7,0x67d03ea819f40b1007d50,0xcfa067d033d01fa40cfa07e90,0x1fd40cfa07f50,0x67d033e820600cfa08180,0x20718a2c07f56,0xcfa067d0414b161c10a068186,0x67d033e819f40cfa080c428b020310a2c07b94,0x19f40cfa067b040f0961c10a267e91,0x33e820310cfa080c4,0xcfa067d02d1220610cfa08184,0x33e819f40bca8837028b0218010f40818a]
def a1Marks123 : Array Nat := #[0x67d033e119f40cfa0679041b8161c10a4682b7,0x33e819f40cfa067d033e820dc0cfa08370,0x67d02f32218010f608600,0x67d02f3a21ec10f4087a0,0x34401b5c0dd406800,0x34281c904b1226d71,0x687034381a180a20068b028281fa40d0e07e90,0x34481fec0d0607f50,0x20798a2c07f56,0x2eda20dc0a2c0812a,0xd240692034901a480d2406920,0xd240697034bb1a498dae05390,0x34b81b5c0dae06920,0xd2e06970,0x34901a480d240692038501a480e1406920,0xd2e0692039201a480e4806970,0x692039231a480a7407246,0x1c744bba06d71,0x6344314118a00d24069202a701cfc0d24073f0,0x1a400d260692034901f440a4807500,0x1a440d240694034901f480a2c07501,0x69203ef01a480b1407de0,0xd240692034801fc80d0007e90,0x34901fb80d2407ee0,0x20040cfa07f50,0x6920349020600d2408180,0x20958a2c07f56,0x6920349020a58bbe08186,0x20958d2408256,0x1a480d2406920349016950b4a8818428b020610a2c07b94,0x34901a480d22068514158962410b467e91,0xd24069202d3220610d2408184]
def a1Marks124 : Array Nat := #[0xd2405a5441b8145810c0c80ca,0x1a480d2405e8441b814e410f40818a,0x34901a480d2406920349020dc0d2408370,0x34d01b5c0dcc06920,0xd32069b039231a640ac007246,0x34e81b5c0dce06920,0x34e01fb80d3807ee0,0x358820dc0a2c08598,0xdae06b30,0x35981acc103006b30,0xd6e05efa2e7d17bd0b9e8837028b0213c10f208796,0xdae06b90,0x1ae40d7206b803f481ae40c3246190,0xd8206c4036181b0c0fd605160,0xd8406c4036201b100fd805170,0x1b100d8606c6041b81458109005170,0x36b81b5c0dae06d70,0xdcc06d70,0xdce06d70,0x1b5c0e3e067d0,0x36b81b5c0dae06d7039201a480e4806920,0x36b81c900d6606950,0xc6205a1036b81c9c0d6606960,0x36b81c900dae06970,0xe6a066d0,0x31d217c28b8e86d702a801cfc0d240872a,0x1b5c0e7806b20,0x18c40e6a06d70,0xc7486cc6366015440e7e06c30,0x31d218c48c6206d7036b815480e7e06d70,0x6d7036b81b5c0fd605160,0xd9a06da036b81b5c0fd6052e0]
def a1Marks125 : Array Nat := #[0xd9c06da036d01b680fd8052f0,0xd9a06e0036681d740c1005310,0x1b3c0dae06de036b818240fdc05160,0x6cf036f81b3c0ede260a0,0x1b400dbc06de036f0182c107e25171,0x1b3c0d9e06e1230481de44a2a285d5,0x36881b480db406de036b818300fdc052e0,0x6d3036991b5c0dbc06de2307118380fe405160,0x1b5c0fda05870,0x36b81e700fda058c0,0x36b8183c0fdc05890,0x36b81eb80fd606100,0x36b81b5c0dae06d703f7018400fdc06100,0x36a81b788dae061723f901840108066130,0x36b81fc00ce606140,0x36b81fc40d5806150,0x36b81fb80d6606160,0x36b81fb80d7206180,0x1b5c0dae06cd03f901ae40c3246190,0xfd606d70,0x36b81fb80dae061a0,0xdae06d703f901b5c0c36461b0,0x1b5c104a05160,0x1b5c105205160,0x36b820a40c2008585,0x104a067d0,0x36b8209c0d2408766,0x36b8209c0d3008776,0x36b820a40d2408786,0x1b5c105006ab0,0x36b81b5c105206b30,0x104a06d70]
def a1Marks126 : Array Nat := #[0x36b81b5c105206d70,0x1b580dae06d7035031b5c105606d70,0x36b81b5c0dae06d7041b81458106e05160,0x1b680dae06e2041b814b8109405170,0x6d702f8517428be085d0441b814e410f208796,0x1b5c106e05890,0xdae06d70367820dc0c20085d5,0x1b5c106206720,0x1b5c106e066d0,0x1b5c106e067d0,0x1b5c0be146d702e8a20dc0d24087a6,0x106806b10,0x1b5c0da846d7035139b5c106e06b30,0x106c06b70,0x1b5c0dae06d70365b1b2c106e06b90,0x1b5c0dae06d7036b81b5c106e06d70,0xdb406d1236881b8c10c828643,0x1b780da606d203718186490bc861c0,0x36b81b3c8c34485d4,0x6d702e8d17d50d2ec87a0,0x1bb00dda06ed037701ff0ca2c07503,0xdda057d341b8145810f808049,0xde006f0037801bc00de006f00,0x37801bc00de006f0038501bc00e1406f00,0x1bc00de006f00378015540aaa073f028b01cfc0a2c070a6,0x635431a918d40de006f002ab01cfc0de0073f0,0x37781bc40de006f0037981ff00a4807500,0xde006f203c901fd40b1e078c0,0xde006f00377820780d0607e90,0x37901fd40de007f50,0xde406f0040101bc0100406f20,0x6f0040601bc00b20080c0]
def a1Marks127 : Array Nat := #[0xde006f002d4820600de008180,0x20b40a2c07f56,0xde00555041b8145810fc08026,0x1bc00de005e9041b8163c10c068186,0x20b40de0082d0,0x37801bc00de006f00378020dc0de008370,0xde406f20,0x37a81fe80de007f50,0xde806f6040601bd00b84080c0,0x636038181cd40e0207350,0x38001c040e02070202901a010ca2c07503,0x384020940e0c08250,0x38501c280e14070a038501c280e14070a038501c280e14070a0,0x39201c280e480724039201c280e4807240,0xc6e8637231b81c280e7e070a02b181cfc0e7e073f03850158c0e7e073f0,0x1c280e14070a0401014580e8407420401014580e8407420,0x38481c2c0e14070a0402014900ea007500402014900ea007500,0x1c280b600818028b01e318f18c5b0040c014580f18c78c6,0x70a038501c2410560687028481fa40fd2082b0343814240fd207e90,0x40101bc00fea07f5040101bc00fea07f50,0x40101c2810040802040101c28100408020,0x1c281030070a02e1820601030081803850170c103008180,0x41b814580feac7f5641b814580feac7f56,0x1c28106e055a043f020099004c83702ad021f81004c8026,0x1c28106e05b604304a0319018c83702db021825018c80c6,0xe14070a041b817a81030c818641b817a81030c8186,0x41b81a48104ac825641b81a48104ac8256,0x41b81bc0105a082d041b81bc0105a082d0,0x38501c280e14070a041b81c28106e0837041b81c28106e08370,0x715038a81c50106e06873287321bd8a18c7e93,0x103006f00328821cd8b9207f50,0x1c60106e05160328321d58b9407c89]
def a1Marks128 : Array Nat := #[0xe30083702c7b19458b9607f56,0x106e0706332e021d58b9808253,0x38e01619106e05160,0x71c038e020dc0d6705ed2,0xe480724039201c900e4807240,0x1c900e7e06e6034d31a680ac807246,0xc768639231c81c900e7e0724034db1c900aca073f0,0x39101c940e4807240413814b810eec7500,0x723039201c980e48061f04148149050f0c7501,0xe4807240391020ac0d760621231081a200a1ac7e90,0xe4808290373818880d3a07ee0,0x41381bc010ecc7f50,0x1c9010520716031181c900b9c08180,0xe4808290392018900e4808290,0xe4805b0441b8145810f4c78ca,0x20dc0cfac7f56,0xe480724041b81ad58bdc08186,0x1c900e4807240392020dc0b6c883702db221e990f4c7b94,0xe4807240391820dc0d5e27e91,0xe4805f2a41b81c280b86887a63920174910f4c8184,0x1c900e4805d3a41b81c3e8be28818a,0x39201c900e480724041b81c900e4808370,0xe58072c239681cb80e5c45f8430711838106e05160,0x1cb40e5a072b041b81ae40c3246190,0xc7a0735039a818f40e6a07350,0xc7a063e039e01cd40e6a07030,0x18fd0c7e463d032001cfc0e6a0735038231cd40e0805680,0xe6a0735039a81904106205160,0x1cc40e6c0735039a819081062052e0,0x732039a81cd40e700609430491910106e05160,0x1cc80e640739035e99de4cc1446450,0x733039c01ce00e70060b430591910109465173]
def a1Marks129 : Array Nat := #[0x734039c01cd40c2e8617241b8191c109066480,0x735039a81cd40e6a08370308120dc0c20464b0,0x1cd40e6a0731041b81ae80c32464c0,0x20d00dda06510,0x106e07010329815fe4e6a087c6,0x735041a01c440caa07350,0x1cd4106e0713232b817ce0e6a05d42,0xe6a07350399020dc0d7e66590,0x39a820c40e6a065f0,0x39a81cd40e6a0837039a819840e6a07350,0x1cec0e78073c039e8187d0c3e4644041b81490d0f8c7503,0x19010c804640039f81cfc0c808640232001cfc0e7e073f039f81cfc0e7e05690,0x73f039f81cfc0c8286412320820dc0a2c087e03a1021f98e84056a0,0xe7c0740039f81cfc0c8886422321020dc0a5c087f03a8021fd8ea0056b0,0xe7e0649432491918106e058f03c6021f98f18056d0,0x73f039f81cfc0e7e064b4325920dc0c8e0837032381ee40f72056f0,0x511139f81444ce7e073e032ca20dc0d80064c232601fa40fd205710,0x32d220dc0dae064d232681fac0fd605720,0x73f032da20dc0dd2064f232701fb80fdc05730,0x651441b81bc00ca2465103fa821f98fea05740,0x329220dc0e14065223290158c1004087e639f821f9900405750,0x73f032b220dc0e200656232a02030101805760,0x39f8195d106e0717032b919540be8c818039f81754103005770,0x32e220dc0e3e0658232c02094104a05780,0x41b81ca80cbc865e232f020b4105a05790,0x73f039f81cfc106e073f0330a19848cc2073f041b81cfc106e057c0,0xe84074203a101d080e84074203a101d080e8407420,0x74103a181d080e84075003a801d400ea007420,0xe84074203a101d080f7207b903dc81d080f7207420,0x3a101d080e8207e903f481d080fd207e90,0x7f503fa81d080fea07f50,0x1004080203a102008100407420]
def a1Marks130 : Array Nat := #[0x1d081030081803a102060103007420,0xe84074203a1020dc0e840837041b820dc0e8407420,0x74403a381d140e8a075103a801d400ea007450,0x1d200e8a078d03c601e300f1807450,0x7f703fa81d140fea07f50,0x1d240ea4075003a801d400ea0075203a801d400ea007500,0xe94074a13a801d4c0ea0075313a809d404efa07420,0x3a601d540ea0078e03c601e300f2c07450,0x3ac01d400ea0075803a801d400f7407b903dc81d400f7207500,0x75803a801d608ea0075b03a481fa80fd2075003f481d600fd207582,0xeb807ec03f581d400fd607eb0,0x1d400eba07ef03f701d400fdc07ee0,0x1d400ebe078f43d4a1d080f18878c4,0xec007f903fe01d140fea07f50,0xec207f903fe81d1c0ff207f90,0xec407fd03fe01d400ff807fc0,0x1d8c1006080403a282008100407500,0x1d90100a080403a802010100807500,0x1d400eca080d040601d401018080c0,0x3a801d981032081803a802060103007500,0xed00826041281d40104a08250,0x1d400ea0075003a801da80f7c874203df21d080f7287b94,0x75203a801dac0f7c8750041e81d0c0f7c87be4,0x75003a801d280edc07e913a8020f80fd227e91,0x1d400ede07ee13a8020fc0fdc27ee1,0x3a801d380ee007f213a1021000fdc87ee4,0x1d400ee2081043a2821081018880c4,0xea0074d23a681dcc10348745042202061103087500,0x1d3c0ee8082813a282118104a28251,0xeea082d03a80211c105a082d0,0x75003a711d380eee083703a102120106288314,0xea0074f23a781de0106e07450424820d1106887500]
def a1Marks131 : Array Nat := #[0x1d400ea0075003bc820dc0ea0084a041b820dc0ea007500,0x76503a601d8010c227600,0x3c081e080f0227f903ff81dec0ff227f50,0x1df40efa074b33c181e100f0827e933be820f8907c87e93,0xf18078c03c601e300f18078c0,0x3c601e300f18078c03dc81e300f72078c0,0xf18079003c811f300e8a078c2,0x78c03ec11e300e9007d82,0xf18078c03a601fa40f1807e90,0x3c901fd40f1807f50,0x40101e301004078c0,0xf24078c040601e30101807920,0x78c040c01e301030078c0,0x3c6020308f18080c2,0x78c040c11e301030478c0,0x202d8e8407f56,0x78c040c31e301030c78c0,0x1e300f16082b63a28214c5031078c0,0x3c601e300ebe681e33bd8215010a827e93,0x2094cf1808253,0x3c601e300f18083703c6020dc0f18078c0,0xf2407920,0x3ca01fe80f1807f50,0x795040101e4c100407930,0x3cc01ff00f1807f50,0x79603cc820308f2c080c2,0x3ce81ff80f1807f50,0xf34079f040c11e681030479a0,0x3c5b20318e8ac7f56,0x7ac03d781fb88f5807ee2,0x3da820940f6408250,0x3dc020b40f6c082d0]
def a1Marks132 : Array Nat := #[0x3dc81ee40f7207b903dc81ee40f7207b903dc81ee40f7207b90,0x1ee40fd207b903ac01fa40fd207e903dc81d600fd207e90,0x3f701ee40fdc07ee03f701ee40fdc07ee0,0x40601e300fea07f5040601e300fea07f50,0x40601ee41018080c040601ee41018080c0,0x81803dc820601030081803dc82060103007b90,0xf72082b03cd020609030482b03cd02060903047b90,0x1ee40f72076a341801df410b8085c13f499fa4d060077d042e021704fd267e93,0x1ee4106e0750042e89fb8cfdc683703a8021744fdc67ee3,0x41b81e30104a6825341b81e30104a68253,0x3dc81ee4106e07b9041b820dc106e07b9041b820dc0f7207b90,0x1f00102007a7042119e3c0ff267f50,0x1f0c0f86076d341b81df410bc485e44261a18890c487e93,0x40c01e30109c67f50,0x41b81ed8109e682d0,0x7cc03f481f300f98075a0,0xfea07cc0,0xfaa083703cd3a148d03147d50,0x40601f300f2007f50,0x40701f300f2207f50,0x40f31e3190aa67f56,0x41b81ec9d0b268257,0x7e903f481fa40fd207e903f481fa40fd2075b0,0x1fc80fc807ad23f701fa40fdc075d0,0x1fc80fd207e903f901fa40fe4075e0,0x81e03e601fd40fea07600,0x41581f381004080203b1814240fd206890,0x20780fb00797240601fa4101807650,0x82b03ec81e6c903007e9040c01d980fd2068a0,0x20780fd207e9040f01fa4103c07670,0x20a80fca07b3241281ecc104a07680,0x1e95105607e903f4820ac0fd2082b03b481a8d8fd2068b0]
def a1Marks133 : Array Nat := #[0x7e9041801ef80f008780243181fa450b867e903b70a170cfd2276e0,0x83703dc81d600fdc285d33f482174cfdc276f0,0x3f4820dc0f7a286403f722178cfdc87700,0x1fa4106007cf03c122031101887710,0x83703e602049102487720,0x3f4820dc0fa00818440c21dcc0a1f47e90,0x83703eb82094504a27740,0x20bc0fce07b7241681edc105a07750,0x1fa4106007e903c1a1fa4106007e9041801dd80df2c6f90,0xfd2083703f481fa4106e07e9041b81de40fd207e90,0xfdc07ee03f701fb80fdc07ee0,0xfe407eb03f701eb88f5c07ee2,0xfe407ee03f701ebc8fdc07f20,0x20a00f9407f50,0x82903ef01fb8103007ee0,0x105607e023f701e70103047ee0,0x82903f701fb8105207ee0,0x7ee041b81f48103087ee0,0x3f7020dc0fdc07ee03f7020dc0fdc07ee0,0x3fa81fd40fea07f50,0xff407f50,0xff807f50,0x40101fd40fea06f20,0x40201fd40fea06f30,0x40601fd40fea07920,0x40c01fd40fea07f50,0x40f01fd40fea07f50,0x104a07f50,0x1e89105607f503fa81fd40d4ac7f50,0x105a07420,0x20dc0e8407f50,0x20dc0e8a07f50]
def a1Marks134 : Array Nat := #[0x41701e300fea085f3,0x83703c601fd410c067f50,0x106c07c80,0x1e92906e07cc03fa81fd40fea06a40,0x105a07f50,0x1fd4106007f503fa81fd40df6c6fa0,0x1fd4106e07f503fa81fd40fea07f50,0x3fc81e048f0208660,0x1fd40f2488600,0x10040802040102008100408020,0x103007fa040101e500dea080c0,0x10300802040101e54100408180,0x83703d582008100408186,0x401020dc10040802040102008100408370,0x1018080c0406020301018080c0,0x1030080c040602060101806f60,0x103c07fc040601e608f30080c2,0x105607fe040601e741030480c0,0x103c080c040601e649018081e0,0x20dc0f720860340602180d030c80c0,0x83703e9820301031080c0,0x406020dc1018080c0406020dc1018080c0,0x40c0206010300818040c02060103008180,0x415820101030079e23cf02060903008182,0x1052081303da020940e0e08250,0x10520818040c020a4103008290,0xf46882b040c020600f3e4818041581a999030082b0,0x106e07c5040c02061903008186,0x106e07d4040c02062103008188,0x41b81f70104ac8256,0x41b81fd41038681c3,0x41b82004d04a68253]
def a1Marks135 : Array Nat := #[0x41b8201c104b28259,0x41b8202c105a082d0,0x818041b8206010300818041b82060103008370,0x41282094104a08250,0x41382094104a07080,0x41402094104a07b50,0x2094106e0825041282094104a08250,0x416820b4105a082d0,0x417020b4105a07b80,0x20dc105a082d0416820b4105a082d0,0x106e0837041b820dc106e0837041b820dc106e0837041b820dc106e08370,0x21f810fc087e043f01d080ad408810,0x43f01fd58de4c5746,0x22401122088704639a31d519268870,0x88e04438255cd2aea9603,0x447025b4d2dc096e1,0x1132096c0,0x44da226812e229713,0x221c121009090,0x1424d23009181,0x22a81152091f0,0x1424126a09352,0xa1229362,0x127608bf0,0x231012d609703,0x12e429723,0x8cc04b9025d892e409720,0x118a08cd0,0x8c804502224112fc08d80,0x227c911e48e40,0x4c002600130008fe0,0x1424130429823]
def a1Marks136 : Array Nat := #[0x123209191,0x9370,0x48282410124469483,0x127269395,0x2418120809640,0x9731,0x12e809741,0x4ba025dc12e809740,0x0,0x130609831,0x121409030,0x1308c9847,0x9723,0x0,0x487824441234091a1,0x244012ea09751,0x122409122,0x122609132,0x9380,0x9751,0x8a60,0x0,0x9150,0x122c09110,0x9713,0x245c1228c9140,0x123608a90,0x2474120889634,0x9743,0x0,0x0,0x0]
def a1Marks137 : Array Nat := #[0x91c6,0x1252092c0,0x92a0,0x0,0x0,0x9340,0x9310,0x126c48bf0,0x9372,0x24e0918209130,0x92b0,0x1264092c0,0x0,0x92d0,0x24cc125ec92f0,0x0,0x49a124c19260092d0,0x0,0x2501127e09480,0x4a402520128e894804a402510128209480,0x1296094a0,0x4a7024b8d25c28cd0,0x129e094f24a88258912d208d30,0x95004a98254412a208d40,0x12b8096b44b802422921088d80,0x4af02509928408db0,0x253c12bc08e20,0x12a0095e04af025781286c9430,0x4af8241e120e48e40,0x9610,0x12a269650,0x95534b282594128ac9450]
def a1Marks138 : Array Nat := #[0x12ca09533,0x259412ca096504aa1a594128cc9460,0x25a812e829203,0x9213,0x0,0x25a412c408fc0,0x95b3,0x25d9130a08fe0,0x12e469723,0x12cc895f2,0x12b869680,0x12e869743,0x9772,0x12c289247,0x0,0x0,0x9580,0x4b3a2564123ec91f0,0x96444ad0248d929009220,0x0,0x0,0x0,0x258d12ba09480,0x5090,0x4b2a25781290c9480,0x0,0x9720,0x4ba125d012d4696a1,0x12f2697d0,0x0,0x0,0x25f512f809490]
def a1Marks139 : Array Nat := #[0x3dca1458136a051603dc91458136a051603dc81458136a0516038531458136a0516038501458136a05160,0x3dda1470136c051603dd91470536c251603dc8146c136a051b03853146c136a051b03850146c136a051b0,0x3de21494136e051603dc91490136a052403dc81490136a05240386314a013780516038501490136a05240,0x14c48a62099b03df214bc1370051603dc914b8136a052e03dc814b8136a052e0386314c8137805246386014c99378c5240,0xf86851603e1914580f8605160385314d8136a05360385014d8136a05360,0xf8a851603e21146c8f88051b0385314e4136a05390385014e4136a05390,0x15150a88899c42a0115000af8051302b9914fc8ae6053f02b481548133e055202a9015480aa605380,0x2b1b1558133e055502aa81bc00ab409b50,0x284994244a12056362b18267c0f8a851b43e29146c8f8a051b038531568136a055a038501568136a055a0,0xa1a053d42b2b158c133e087902b0015800ac005600,0x150d0a86454302bba14f90aee453e22bb814f80ad2056304cf8158c0ac6056302b18158c0a76099f0,0x15bd0ad4099f02b5015bc8ad4099f02b5015bc0ad4099f02b5015190a8c454602be0144c1100056c04de8144c0ad4056a0,0x15d90ada857622b6915d80ada054842be015580a90454802ba8144c0ae805740,0x57a42b7215e88adc457a02b7015f00ace056604cf015290a94454a02be0144c0af205790,0xfaa851603ea914580f72058304da8160c0e2ac51603850160c136a05830,0xfb0851603ea914900f72058704da8161c0e2cc51603850161c136a05870,0xfb2851603eb114900f72058904da816240e2cc51b038501624136a05890,0x16340fb0852413ec114900f72058f04da8163c0e2ec51603850163c136a058f0,0x59302c9816b00b28c9a102d6316501342c59302c9816718b3809a60,0x16440b4c05a502d281a48cb6c09b50,0x16358b86078c62db026d40b6005b00,0x2c98170c0fb2852413ec914900f7205b604da816d80e2ec51b0385016d8136a05b60,0x164c0b8605c202e101c618b8405c20,0xb2c059d42e18170c0b3a45d502e18170c0b8605c30,0xb3e25a602cf816680b3009a002e9817440ba205d20,0x3ef214580fbc451603e1816100e2ac537038501774136a05dd0,0xb2ac58552c2997980be405e704d1019f4cbd409b50,0x50f02cb316790b3c45f403f1214a50fc4452923e2816d80e2ec55a0385017a8136a05ea0,0x5e412f2016658b2ec9a062fa817c8134405f10,0x3f2214580fc8451603dc817e8136a05fa038ab16118e2a05840,0x18240c12061703058268c0eb0860a04d789d404c2009b50,0xc12061903f4894580fc8452e03dc81840136a0610038b316258e2c05890]
def a1Marks140 : Array Nat := #[0x18380c380619030c8141010b86619030c814c48a54099b0,0x609030d821754c34061a0,0x30f818840b36c62303f4894904fcc452e03dc81880136a0620038bb16258e2c05b60,0xcc2051403278180c8c72c628631c818a00c6406000,0x65b13032996c0c0c663b631a318ec0c68054262a1026700c8005140,0x3308180d0cc20603231f318d98c7c0636031e818f40c4a09a60,0x19840c5a862b14d2099840c5a462b04d2019000c80063764d3019000c80063704d30150d8a86099d0320019000c4a09a60,0x32589904134c0641032581904134c06410329314500ca4051403a10191c136a05140,0x19144c8a09a5032589910134c0644032581910134c06440329b14864ca6052133a919920137065140,0xc9826421326019080caac59c632a816700fd2252e13f4814b80f72064704da8191c0c4a09a6038bb16d98e2e05b60,0xcac2649132b019240cc205140329018d40ca8058e0,0xcb6264a132d819280cbac634632e818d00cc205140,0x6670333819ac0cd009a703bc99454ceda65f903b6199b013680515338a317718e2805dc0,0xfdc851603f7114580f8605fa038ab17758e2a05dd0,0x406214580faa458723ea8161c0e48c5160385019f4136a067d0,0x2d1a1a288d14054d0407a14cd0fb245b623ec816d80e50c51f038501a1c136a06870,0x5a5440c214580fbc458923ef016240e48c539038501a48136a06920,0x5a5443d314e98d2e06970,0xb4e869b040c2146d0fbe458923ef816240e48c55a038501a64136a06990,0x5a8440c214904fc2458923ef016d80e4ec539038501a70136a069c0,0x1050851603f71161c8fba05fd0392317758e2a068f0,0x1056251603f7116308fbc061003923177d8e2c06920,0x105c851603f1917f88fc605fe0392319f58e48067d0,0x1060051603f2118408fc80610039231a018e4806800,0x1062851603f7117e88fdc05fa039031a318e40068c0,0x6c52362826a81094051703f7917ec8fde05fb0390b1a358e42068d0,0x6e20367026b00d9a06cd03bc814540ebc06b803ae014b40a58099b039131a418e4406900,0x1b3c0d9e06d52368026ac8ef2260a03b8098348ede25151391b1a458e4606910,0x106e051603f7118408fdc0610039231a498e4806920,0x6e02370026b01094052f03f7918448fde06110392b1a4d8e4a06930,0x1b848dbe09ab24250945c50822613241f898480c0809a3039331a518e4c06940,0x106e051b43f8118408fe00610039231a658e4806990]
def a1Marks141 : Array Nat := #[0x106e052413f8918408fdc06200393b1a498e48069c0,0x4062161d1018458724040163c0e78c516038501bb4136a06ed0,0x55504062163d1018458f24060163c0e7e0516038501bc0136a06f00,0x2aa81bc80de4087e6,0xdec055704072163d101c458f2406016d80e7e051b038501bd0136a06f40,0x16a90b544704040c21625103045892408816d80e78c55a038501c04136a07010,0x2d5a1c1c8e0e0558040c2163d102e45b6240b816d80e7e0539038501c18136a07060,0x40c216d9103045b6240c016d80e7e055a038501c28136a070a0385026d4103085b6440c116d8903005b6039f815680e14070a04da81c280e1409b50,0x414a16d9105245b6240c018780e7e05e064373a1b98b8a055d638a81c540e1409b50,0x415896d9105245d7240c018800e7e05e16438b21c18b8c055e638b01c580e1409b50,0x4158975d105605d7240c0191c0c7009a6039f817a990e8e87462e4016b01342055f638b81c5c0e1409b50,0x106e058744141184090420620039e31a498e4806ff0,0x106e05b644149188090520620039f81a6590f4c560639201c900e1409b50,0x106e05fa44189184090620610039d31bf98e7406fe0,0x1cc80e6407340399826b80ef266be335e1a6a4ceee6643031e026940ef26515339db1c018e7607000,0x41b81841106e061024188191c0c7a09a6039e31c058e7807010,0x1ce44e7209ae0425198490c0e89a34425198488c0e49a32425199200c7a09a6039eb1c098e7a07020,0x20dc0c4088370310120d00c8e063e04d301cfc0e02c73c039e01c28136a05626,0x20dc0c8e864044d3220dc0c8e464024d3120dc0c8e064004d301cfc0e7e070a64da81cfc0e7e070a04da8158d8ac6099f0,0x3dca1d08136a074203dc91d08136a074203dc81d08136a0742040131458100405160,0x3de21d18136e074203dc91d14136a074503dc81d14136a0745040231458100405240,0x1d608eb009af03df21d481370074203dc91d40136a075003dc81d40136a0750040231491900805240,0x1d648eb209b0041e81d481370075203dd11d481370075203dd01d48137007520402b1499900a05260,0x1db80e94275b03ac026bc0eb007bf43ac826e44eb0075803ac01d600e9209af03b3316b58ecc05ad0,0x1dc40ebe076703ad01f010ec209ba43b101d100ec0076003bc814540ec606ef0,0x3c009dfc1362078003bf8a6c44f7c877e04dc01d404f7c477e14dc09d400f72077d04da81df40b5cc8066299b16b8100c05330,0x7d843a289f608e8a07b903c6026d40f1805b0640c314581004058f0,0x79203c9016c190c065900,0xfb2874513ec91d140f72079304da81e4c0b62c818628d81e54100405b60,0xf2e07da43a289f608ea007b903cb026d40f2c05b2640c314919008058f0,0x3a689e6c0fb6874513ec91d400f72079a04da81e680b66c8186294b1e78100805b60,0xe9c27ad03f489d080fc8475003dc81eb0136a07ac040ab1625902a05890]
def a1Marks142 : Array Nat := #[0x3a789ecc0fd2274513f311d400f7207b204da81ec80b68c81862c4b1ed0102a05b60,0x3db89edc0fd0875013f411d400f7207b604da81ed80b6ac81862c7b16d41030058f0,0x3f489d404fd2075003dc81ee4136a07b903dc826d40fd2275013f481d400f7207b904da81ee40f7209b5040c316d99030c5b6640c016d8103005b60,0xf7e27bf04d981fa44efa87e903be920f94ea6883e33a9920f4cf7c09b833df01ee4136a081a62ec321124b74c81a02ec02110cb7405070,0x3f909d404fe407500425aa12ccf8607c303dc826d41030c5e262ddb20600bc405bb0,0x3f989de90fe6077a2426aa134cf8a07c503dc826d41030c5ea62de320600bd405bc0,0x1018874203ea91e208faa07880413b14581004067d0,0x1018877b43ec11e308fb0078c0415b1458100406830,0x40f09d404fd20789242899d508faa07d503dc826d41052c5b664281a0600d0205bd0,0x40f09df10fd20796242a19d548fb007d803dc826d41056c5b664299a0600d0805be0,0x40f89df10fd2079a242b99d588fb207d903dc826d41056c5d6642b1a0600d0e05bf0,0x1056275013f901e2890b467de03ef01ee4136a082962f1b20600d3805c00,0x1060075013f481eb090b667e403f201ee4136a07572414b1a09905206820,0x41801df510b827e903f481ee4936a085c33f481fa40f7209b503ac11d60135e082b6343b20ac0d0e05090,0x106e074203f711eb08fdc07ac0413b1a49904e06920,0x83703a809fc80f58485d53f701fb80f7209b50414b1a719052069c0,0x41b81df510bc87f203f901ee4936a085e53f901fc80f7209b50415b1a7d9056069f0,0x1018878c440611e309018078c041b81458100406f00,0x84303d4220348f1c480d03c702184d0c229ba44250145c100606f10,0x101c878c440711e3090180793041b8146c100406f40,0x1020878c440611e5890180796041b81491900806f00,0x81843c9a20608f26481803c9820dc0ab40802040101c28136a087e6,0x81a43c9a20608f34481803cd020dc0afcc804040201c28136a087f6,0x103c2796440f01e589018080c03dc826d4106e05b664301a0600de805c20,0x1050878c441411e30902c07b0041b81775902807050,0x20ac4f34882b03cd12060103007b904da820dc0bd4c818040c01c28136a05c30,0x105c878c440e91ec4903a07b1041b819f5904e06f00,0x106007a0440f020780f7249b5040f020780f7209b5041b81a1d905606f70,0x106e078c441411ec8905007b2041b81a49904e07060,0x41b81e4d105247b2241481ec8106e069964138209c0e1409b50,0x41b81e59105407b22414020a00f7209b5041b81a71905207060,0x106e079a441581ec89052082903dc826d4106e069e6414820a40e1409b50]
def a1Marks143 : Array Nat := #[0x41b81e850f4c89b24415820ac0f7249b50415820ac0f7209b5041b81a9d8d42c9a86415820ac0e1409b50,0x105c87b6441711ed8905c07b6041b81bc1906e06f00,0x41789ed9105e07b62417020b80f7209b5041b81bd1906e06f40,0x418020c00f7289b50418020c00f7249b50418020c00f7209b5041b81bf58df0c9ad641b81bf40df009ad0,0x41b81eb1106e07ac2418820c40f7209b5041a31c05906807010,0x106e07b2441b81ec89068083403dc826d4106e0701641a020d00e1409b50,0x106e07b6441b020d80f7249b5041b020d80f7209b5041b81c19906e07060,0x41b820dc0f7289b5041b820dc0f7249b5041b820dc0f7209b5041b820dc0e14c9b5041b820dc0e1409b50,0x107c483e04dc0217010b8078423bf926c48f08077f04d88217010b808632431826ec0a22050b0,0xfdca7e914da821780ede875814d78a17410ba08642,0x2062901889b50430021800b8745eb4,0x87a043d020628e48c9b502e9517d90bd889a24,0x19891004c73f04da819888cc4057562b18267c10fc087e0,0x26f8138409c214e08270413aa09d504ea8275413aa09c10,0x26fc154a0aa50552826fc154a0aa50,0x2b88137e0ae2057102b8813820ae20,0x2704161a0b0d058682c3413820b0d0,0x138009c104e08270c16640b32059902cc813820b320,0x172c0b9604e082e58172c0b960,0x175c09c105d702eb8175c0bae0,0x26fc0a2c0ca90654832a419520ca90,0xccb06658332c19960ccb0,0x27041a080d040682034101a0808370,0xa2c0d5206a9035481aa40d520,0x13820d5f06af8357c1abe0d5f0,0xd6706b38359c1ace0d670,0x9c404eb0275853aa09d504ea8275413ac09d614ea8275413aa09d50,0x4e28271493ae09d504ec8275413ae49d924ea92754940409c10,0x9da04ea8275413b409d504ea828b8145c2a2d051682754145a09d50,0x9d504ee8277814840a4215208290413aa0a410,0x4ea8278014864a4525209291c93820a412,0x4f082728154c0aa5055282728154a0aa50]
def a1Marks144 : Array Nat := #[0x110409e30571826fc11764af6057102b8813aa0ae20,0x139c0aa73553aaa94d39c0aa53,0x4f282754161c0b0e158682c3413aa0b0d0,0x4f302758161c0b11058702c3813ac0b0e0,0x279413ca09da05891ac4953b409e50,0x9e904e402bdcd5eeaae234e702bf0d3820ae23,0x9eb04ea82c94164a2b240592027541648057b3,0x274413aa09d504f6027bc16660b34059902d1813820b320,0x9d3044382754110e088704ea8221c1128088904f70224c111809f0046aaa220166a68d534440acd5510e0b32344382340d1140b4d34e08221c166468870,0x9d504ea8275413aa09f104f882dbc16de2b6e04ea82db813aa0b6e0,0x4428a21413b409d5044a8a25413e209d504f98271011f08b7a047c12de856f209d505bc8276816f209f10,0x88704440a75853aa09f4047c92dc496e049d505db8a70856e04b702,0x222c53aa089604ea82714112a09f5047d22dec96f249d505dc0a3dc16f24b792,0x13aa09d504e8827d8171a0b8c04ea82ee457180b8c0,0x27e0172e0b9804e082e5c572c0b960,0x9d504ea827e417440ba104ea82e8857420ba10,0x9d504ea827e817464ba124ea82ee857424ba12,0x4ea8275413a609d204e3027ec171e69c105dd82eec57186b8c3,0x4ea027f0175e09c105de82ef4575c0bae0,0x275413aa09d404e4027f4176c09c105df02ef8576a6bb53,0x27280a360caa0654832a419520ca90,0xa3609ce06559b2ad59526ca93,0x27541a0a0d051682034101a0808363,0x27581a0a0d0b0682834141a0a083a0,0x13d609da06861b43153ca09e56,0x27781a4c0d261,0x4f28277813f209dd06a78353c53ca09f10,0x51b06a98354c5aa40d520,0x4ef027f81ac80d641,0x6b4035a05ace0d670,0xa06050312808161e0b0e15871ac3414040b0d0,0x5010280814020a08050482824971c0b8c050102ee457726b8c0]
def a1Marks145 : Array Nat := #[0x28081a0c0d0516829b4101a0808354,0x283414880a41052082904141a0bcb0,0x283416200b0d058682c34141a0bd70,0x141a0b0d6586b2c4d93820bdb0,0xa0c05068283414240b32059902cc8141a0be40,0x28280a480ca90654832c019520ca90,0xa480a0b06560b2a459622ca91,0x5088283019d60cea06750347c19d407786,0x28341a0e0d040682034801a080834a,0x28381a0e0d070683834841a0e083c0,0x28441a120d090684834881a1208496,0x1a1a2d230,0x283c1a420d200690034801a40086d0,0xa480d5406a9035481aa40d520,0x141e0d6106b0035801ac00d600,0xa1006b0335819ac0cd6f6,0xa480d5566abb35499aa4cd6e6,0x14260c3a261e130e4987a4c392,0x284c1a100d051682034801a080833b,0x286018c60c6206320319198c406601,0x50b828540a5c0ca90654832c01960cca90,0x50c028581a120d040682034801a40c8314,0x28781a0e0d071682034901a0808329,0x50f834101a0808300,0x14420a28055282884154a0aa50,0x271d113c489e051482b94137e08bc245e02b8814480ae20,0x51202c3414480b0d0,0xa21029c832a419520ca90,0x512034101a08082e4,0x516828b4145a0a2d0516828b4145a0a2d0516828b4145a0a2d0,0x28b4148c0a4e04ea8290414820a4605270275414820a410,0x552828ac154a0aa50552828ac154a0aa50]
def a1Marks146 : Array Nat := #[0x57282739117e48bf057e0289015c40ae2057282739117e48bf057e0289015c40ae20,0x586828b4161a0b0d0586828b4161a0b0d0,0x16480a2d059202c900af20b24051682c90164805790,0x28b0145a0a2d046c0221d16b009c1059902cc811b0088745ac0270416640b320,0x28b411fc28fe05bc828b413b40b7905bc823f851fc0b7905168276816f20b790,0x28b4145a0a2c05ca8280817822bc135c602e30172a0a0205e08af04d7180b8c0,0x5cd02704172c0b9605cd02704172c0b960,0xa2d05d0828b417420ba105d0828b417420ba10,0x5db02704175c0bae05db02704175c0bae0,0x14820a4105208290414820a410,0x148c0a4e052702904148209de0,0x29e029041482ca6b04ea8300c18100c086,0x5208290495040a0d0,0x52082906152049c10,0x55282a94146a0a350,0x154acaa964e503030146a0c2f0,0xae605058ab8815fc0a330,0x51d02a94d4700a380,0x58682c3414820a410,0x2918148c09e50,0x0,0x557ca73814700c340,0x161acb1664ea8305014820c390,0x9da060a03050148c09e56,0x58b32c5994820a410,0x5711a8e0163069c10,0xb240592029040af12a410,0x51d8290414820b37059902d78141a0c170,0x147a0a41052082cc8d6ca09c1045002284183008870,0x5208290414820a4105b70290416dc0a410,0x291814820b79052082de4148c090b14858290413ba09f10,0x52082e1c94260bc0147b82de492180a4104f01242c18320c470]
def a1Marks147 : Array Nat := #[0x52082e0c94820b832,0x14820a41051d82e3014820b8c0,0xb98051a02e5818340c490,0xa4105d08290417420a410,0xa4105d09290417424a410,0x51f02e7993820b966,0xa4105d0b29041742ca410,0xa41051f82eb594260bc615d0c290418360c4e0,0x290414820a3d051e02e9cd43c0b8c3,0x51f02ed813820ba89,0x14800baf051a02eb818380c520,0x58682938149c0b0d0,0x162cca2d061c8293818720b0d6,0xa4e05bc82938148c090e14870293813be0b790,0xa4e05d0b2938149c0ba16,0x14ac0aa50554028c8154a0a530,0x5290297c15ce09bf046092b8815c40a5c0,0x58682c5414660a5c0,0x5340318818c4065e0,0xa621531029a00a90ca680,0x542058682c5814820a6b0,0x54405320a99016480a680592029ac0ae46a6b0,0x53702c5014960a720,0x29c814e40a7105db02704178e4bc74,0x2c3414fa0a7d0,0x58c3270414fa0c850,0x14fa0bb604e082f2014fa0c870,0x2c3415040a820,0x1632ca02063b831dc95040c8f0,0xa82054102a0417180a820,0x55282a14154a0a850,0x2a101554ca210552b2a1418fe0c820]
def a1Marks148 : Array Nat := #[0x576026fc15c40a880,0x54502c3415100a880,0x58c3289015100c850,0x28dd16300a7d04f22249c924e0a960,0xa960456922b4176c09c105e18240152008a9604f4224a092500cc40,0xaaa054282a94154a0aaa054282a94154a0aa00,0x57a826fc15c40ae2057a826fc15c40ae20,0x2aa815160a86055282a84154a0a280,0x2bd4139c8afc05710328015c40a290,0x154a0aa5055282a94154a0aa50,0xaaa055282a94154a0aaa0,0x2acc1456055a065482a9419520aa56,0x15660a8b055281580154a0aaa6,0x2ac0150e2aac0,0x15660aa505528158c154a0ab30,0x2a90154a0aa5056d0282819660ab50,0xaa5056d8282c59680ab90,0x55282b7414980a36049d02a9413c20acb0,0x154a0aa5055202b8014fe0acf0,0x154a0adf054682a9414ac0ad10,0x2b6415460ad80,0xaa5056e82a94154a0add0,0x57a826fc196e0ad86,0xaa5057a82930154a0add6,0xaec051c22c6015100ae20,0x2bb0149a8a890552824ec92760ae50,0x55282bb815002ae70,0xaec055282a28154a0aec0,0x57a82935154a0aec6,0x2bd415460aef0,0x2a94154a0af5055282a94154a0af50,0xaf5051c22c6015c40ae20]
def a1Marks149 : Array Nat := #[0x155a0aab05748296115d22a58258f829c8116808b41,0x15ea0a67459202b880ade8ae20,0x156e0ae4055a02b8815c4055105c802858116a0883445d032f81184089d0,0x55d02b8815720ae2052d02e4413820cbf0,0x8b72575022e4157a0af9245f822fc15c408ff045212e4c11500a76052f024f411800cc1049e022fc117e0ae204f18230c113c0a2a0,0x2bc8157c0ae2057102adc17280a9a0,0x2bd415720afa257102e4415c40a5f0,0x57582b5417500a7d0,0x15dc0ad6057102eb015260ae20,0x57102b8815c40ae205db02704176c09c10,0xae5057102ed814480ae204f4a24f4927a0cc40,0x2b9c15c40ae2055d02ed814b80bc75,0xaec057102ed815100ae20,0x57882b84176a0a9604f5224f8927c0cc50,0x2bd415c40ae2057102ed815c40ae20,0xa39458c02a3015f80b0d0,0x58682c0019960b000,0x5920270416000d040,0x55505cb02c00199a0d520,0x2eb816000d670,0x161a0b0d058682c34161a0b0d0,0x58b02c34161a0b160,0xa3a458c02c34161a0b180,0x46222c151154c8aa0591028b012b8088e44ac8226419ee0cea0583833a8160ec7750,0x2c90145a0d04058683410161ac82d0,0x592828b81a186d05058703414161cc8390,0x2c15114548a24593034241a1208470,0x59202938161a0b166,0x59202a30161a0b186,0xb06059082c0c161a0b1f0,0xb240586815d1961a0b240,0x58682c34161a056305cd027041a700b280]
def a1Marks150 : Array Nat := #[0x2c1c161a0b0d05cd828341a720b320,0x160e0b07059f028ec1a740b380,0x58402c38561a0b9b0509834d81a720b460,0x161a0a3c05ce028781a760b4f0,0x161408a145cd828bc12fc0891469c82c341a720b580,0xb0d02b01ae6814680b5b0,0x58682e6c14820b5e0,0x161a0a3e05d0827041a900b5b6,0x2c34147e0ba10509835041a920b5e6,0xb0d052002e8414680b6a0,0xb0d058682c34161a0ba1052082e8414820b6e0,0x8c745871ac3417420a4705dd1a9141a9a0b700,0x58682e9014940b750,0xb0d05d082938148c098014c002c3413ca0b790,0x58682e8415040b830,0x161a0bad052382f1a5aa00b836,0x161a0b0d058382eb415040b8c0,0x58682eb0151c0b910,0x2c25161a0b0d05d682a3c161a0b950,0x55a05cd02c001aa40b960,0x55565cd02c34161a0b9a0,0x5cd82c34161a0b9b0,0x58682e8416020b9e0,0xb0d05d082c34161a0ba10,0x5d502c101abc0ba80,0x2c2d161a0b0d05d682c34161a0bad0,0x5db027041abe0b966,0x176c0a2d06af82c341abe0b9a6,0x176c0a2f06b002c341ac00b9b6,0xb0d05db0290417912b9e6,0xb0d05db02938161a0ba16,0x2ed815100ba86]
def a1Marks151 : Array Nat := #[0x2c31161a0b0d05db02a3c161a0bad6,0x5db02c001ace0bae0,0x58682ed816020baf0,0x2c34161a0b0d05db02c0814360bb10,0x161a0b0d05db02c101ad20bb50,0x2c34161a0b0d05db02c34161a0bb60,0x161c0b0815418a8185ad64bc10,0xb1e058f82c7c14b48a5a25db027041aec0b323,0x14d08a68253402c901648056a0534229a094d00b240592015a816480b240,0x2c9016480b2402b4829a514d24a6905db027041af00b280,0x2c88164c0b240592015a114d44a6a05db028581af20b320,0xa9e68cc54661ac90114a88a525db029e814d8098514c282c9013d60b790,0x2a5a2334564808cd359202c88114c8bb6054d8233051986b8c0,0x2b1b2ed816000b960,0xa992b2405db02c5816480ba10,0x53b05db02c6c1af40bae0,0x28982c9016480b2405db02c9016480bb60,0x59382ca416500b28059902cc816640b320594015ac1af80d7e0,0x2cb016640b32059902cc816640b32059902cc81afe0d7f0,0x59682cb456640b36059902cd856642b3215a782ca01b020d811,0x166008d90467223bc16b00b5805ac02cc8130e089346bf82cc81b0e09c30,0x59c02cc816640b38059902cc816dc0b6e059902db816640d880,0x8d2046b0238091be4b390599023ed11ee4b7905bc82cc816f2098a04c482cc813d80d890,0x236c11a608e2059c02cc811c44b38259902ce8165808fc45c602cc817180b3805c602ce091ac0897046f8237c91dc0d8a0,0x16780b99059582e58172c0d8b0,0x2cf417360b3205cd82e6c16640d8c0,0x59902cf817420b3205d082e8416640d8d0,0x59902d0016ea8b32059482dd516ea88d90443a237411de0d8e0,0x46c02360166408d125971237891a20b2e046f0238491c20b41046c82df1165008dd05df823dcd1b00b79446c023dc51b00b79446c0236011b00b32044a2222513dc898a24c50261c11e00d8f0,0x2cc811b60b3205968238896840b8c159902e3057182898146f0238091e40d910,0x16640b31259882d0c17488b2b05d0a2e8516640d920,0x46d0235c16880bae059902eb8175c0d930]
def a1Marks152 : Array Nat := #[0x8e304750239011c80b4604688a394169608e905a6023f511c80b79247202d1811d00bb8147b8239016f248e404c68239011c80b4604491221893da498c04758361413160d892,0x169e0b4f046a2a350d65e6b5105c61ad3c17186d940,0x2e5816b60b960,0xb5e05d092d7817424b5e0,0x11ea28f505b602eb816d40bae0,0xb7905b702de416f20b7905b702de416f2098f14c782db813e209f10,0x2db817180b6e059c02e3017180b8c05b702ce017180b8c0,0xba105b702e8417420ba105b702e8417420b6e0,0x239111c84b7905bc8239111c84b7905bc82de416f2099014c802de416f209f30,0x239951fc08fe047b92de411cc8b9505ac023ac969248eb05a482f2511fc08fe047b82de4932a089644c8123f81b2c08fe05bc82640912a49f524c8023f81b2c08fe05bc92640112a09f50,0x476223dc96f208e745ca82dc0169448e045e09ade411be4b3905e09ae30132c2a0704c883660571809f60,0x23b516a688f725bc82e5416f208e525a592de4172a099715bc82648172a09f70,0x5d082d6c17846b9604c98a64c172c09f80,0x23cd11e64ba105bc82de41742099415bc82650174209f90,0x47a2a3dc96f20bad05b382d7c1742499815bc82650974249fa0,0x11ee8b79047b92de411c2a8e135a09aed816ac0bc435c61b65c132c8d9904cb13664571869fb0,0x11ec88f625db02da817866bae04cc8a664175c09fc0,0xb8c05c602e3017180b8c05c602e3017180b3a0,0x16a88b9505c602e30172a0b8c05ca82cec17180a080,0xba605bf02e58172c0b3c0,0x5d682e0c16c04ba105c602e84167c0b8c0,0xb6345d682e3017180bad05c602eb4167e0b8c0,0x5c602ec416ea0b5045a812e30571808e245a10ae3051c44b420,0x2e30176c0b7f05d0a2e8516860b8c0,0x2ec017140b6b25d702dac175c0b440,0x17180bb105c602d4517180bb105c602ec4168a0a1c0,0x5cb02e58172c0b960,0x2e68172c0b960,0x2e78172c0b960,0x5d082e58172c0b960,0x175c0b280,0xbb605ad82e5817906b960]
def a1Marks153 : Array Nat := #[0x175c0b960,0x172c0bb605cb02e58172c0b960,0x5d082e8417420ba105d082e8417420ba10,0x175a0b9b05d082e8497420ba12,0x5b122eb417420ba105d082eb417420bad0,0xbb605bc82e841742c99a45d082e85933449fe0,0x176c0b8005d082e8617420ba18,0x5db02e74175c0bae0,0x5d082ed817420ba105d082ed817420bb60,0x5d702eb8175c0bae0,0x5d782eb8175c0b6c0,0x176c0bae05d702eb8175c0bae0,0x2f88145e0d2005868341017b6082ca,0x2f5817ae0bd705f70283c1a720be40,0x17f60bca06b002f5c1ac00bf20,0xbda05ee02f6c17b6057f05f9028419a72cb320,0x57d05f902f6c17b60b9b6,0x2f9817e40be405f902fc817c80d8c6,0x518034101a08082b9,0x518834101a080829b,0xa3202c4832a419520ca90,0x519834101a080828b,0x6010332c19960ccb0,0x51a034101a0808279,0x58f0601035481aa40d520,0xc140520830e413bc0c390,0x2c98302c1816cc5e0,0x30441822cc620,0x30459822c5cc6,0x164c18240c650,0x180c0c110,0x5970520830e59872cc080]
def a1Marks154 : Array Nat := #[0x5950,0x2cc03050181009de6,0x6040166818100c080,0x6088318818c4065c6,0x0,0x520830e4987c4c8f0,0x290418730c398,0x6050318898c446589,0x51a816d819520ca90,0x5c30,0xc040,0x31e0d8f0acd20,0x169419006ca93,0xd040,0x303419960ccb0,0x30440b960c110,0xb860cdb6,0x5c20,0x16d814700ca93,0x16c0181c0a3a0,0xc10151d833a819d407748,0x51e033c419e22cfb0,0x120c0c0f0482828f412b46cea367e8223819d467689,0x147c0d040,0x51f833e99a080d250,0x520834101a0808259,0xa420682834981a0a08386,0xa4406868b41c1a0e083b2,0xc1016880b4241a1208468,0x60783424da1268269,0x291813ca0c140,0x0]
def a1Marks155 : Array Nat := #[0x0,0x0,0xb260d270,0xbcb0691834801a40086c2,0x16d81aa40d520,0x520830741abe0d5f0,0xbcb060f035885ac00d600,0x2f4cdac06d603,0x1ace0d670,0xb840c020,0xb860c0d0,0x171c18100c110,0xcdc6,0xccb6,0xc050,0x0,0x6050b04418140c060,0x5d41603830781a5b0d436,0x16c01a78cd526,0x182805d006040300c182809f10,0x29041abecd5f6,0x2f359ac0cd606,0x2f625ac12d609,0xba20c080,0xb6c0d526,0x5a50,0x1acecd706,0xb860c1d0,0x1688182809fe0,0x52383414da080824b,0x524834101a40c820b,0xc2205250341cda0808229]
def a1Marks156 : Array Nat := #[0x3084121a0c23045103424da1268239,0x292c1a08081e9,0x149c0c39061c8293818720c390,0xa4c02f502a9419520c2f0,0x617830bc185e0add6,0x30c4185a0ae20,0x310814fa6d040,0x5ea052682a94d9526c340,0xa4e0586834101872081c9,0x2f5030c81aa40c490,0x619830a017ae0c4e0,0x18720c39061c830e4161acb0d6,0x30e418720b166,0x301598840ae23,0x30d018680aec9,0x185c2c2e0603330e418720b240,0xc35061d830e4187205f31603b31301a92cb320,0x186c0c39061c831341a96cb323,0xc39061c817c018720c3902f8030219810cb6e0,0x17bc18720c270604b30e418280b790,0x61c817b458980b5e8,0xc3906150240998720b872,0xc39061c830d418560b8c0,0x1abecb960,0x61c8309c18720ba10,0x61c830a818720ba12,0x17a818960b966,0x5e5061c830e418720ba16,0x18720c370627030e417b60ba18,0x18702c39061c830e418720bad6,0x18720c39061b031441206cb8c3,0x18a00ba59]
def a1Marks157 : Array Nat := #[0x18720c39061c830e418720bb60,0x310c18920c490,0xc4c06228313817e60c4e0,0x29401a0807f23,0xc560529031600c120ca90,0xa53062c0184019520ca90,0xc320a170,0x52a831600c340c580,0x184014ae0ca91,0x315c0c200a580,0x62b8182414b20ce02,0x62c8296819d42d040,0x316014b60c580,0x29701a0807ee5,0x14ba085d0,0xa180,0xa5f0,0xc200d520,0x29800c400ca90,0x29841a0807edb,0x18c40c62032d0318818c4065a0,0x316c0c580c5c062e0298c18b80c5c0,0x62a25320318898b8064d3,0x316818bc0c5e0532831780c800c5e0,0x5330191c19520c5e0,0x64b1,0x18c40c620328b318818c406516,0x3283318818c40c110,0xc8e0a670,0x317c0c880c620,0x317058b8064106310318814d00c620,0xc6206310190014d20d040]
def a1Marks158 : Array Nat := #[0x18c60c62031f8a9a819d40d040,0xc600631031880c7a0d093,0x63a05358341018c407eb3,0x3180b18818c40a180,0x6376,0x18cd98c40c620,0x6277631030ba18c40c0a2,0x3130318818c40c600,0x6250,0xa280c6206310318818c40c620,0x640062e8b17418ca0c650,0x191c1aa40c650,0x29b40cda0ca90,0xcda0a6f0,0xc680636829c01a0007583,0x917048a831a018dc0a7104ad9a4401a02075b3,0x31a014e407e93,0x31a818de085c0,0x634029d01a24085d2,0x66d0,0x53d819f419520ca90,0x19f414f80ca91,0x29f41a080818a,0x29f81a5008600,0x31c41a50087a0,0x19f41aa40d520,0x18e40c290,0xcfa0d5d6,0x29fc0d0e0ca90,0x1a1c15000ca91,0x91d048f031d012360905463a822a81502095d06750226419d407726,0x2a081a080812a]
def a1Marks159 : Array Nat := #[0xd0e0d520,0x12400c2b6,0x921063b031d412380c730,0x6870,0x542032001900cca90,0xa85064001a4819520ca90,0x63d032000d2e0c800,0xc2c6,0x31ec19000c800,0x1a48150e0ca91,0x2a201a08080ca,0x151408606,0xd240d520,0xc7e0,0xc2d6,0x190206920,0x190205a54,0x15160c7d634c82a9419520c820,0xc820641031f199040aaa6,0x320c18fccae20,0xa8c058683410190a080ba,0x60753214190a0b186,0x2a340d380ca90,0x2a381a08080ab,0x151e06a5058683410191e0809a,0xcc68c8f06478323018e6cb8c0,0xcf26c8d26478323c18720ba16,0x32380b008c8f06478323c191e0bad6,0x1520081b5,0x2494152207d9b,0x2a480d660ca90,0x152607d5b]
def a1Marks160 : Array Nat := #[0x124c49260609d304d152c07c54,0xa990495924ac0d720ca90,0x496924b4153407c34,0x24b8125c4c98054d8318898c407c14,0xc99064d032681a0407520,0x3270153807be4,0x193a083d0,0x2a8019520ca9036b832a4195206d70,0x2a841904cc82063fb31fc195206e60,0x2a88195206e70,0x2a8c195206f00,0x0,0x2a9419520ca90552832a41952070a0,0x612b2aa0195207160,0x18bc0c2f660582aa4195207170,0x1904caaa0654832a4190007240,0x329015560c680,0x155806d71,0x155a0ce00,0x61a532a4155e07174,0x6423b2a4156007241,0x18bc0ca2665102ac4195207350,0x194a0ca3665182ac8193407354,0x317898bc0ca9065482acc1952073f0,0x32a419520cb7065bb2ad01a0407420,0x653032a419520cb8065c32ad41a0407500,0x65303298156c07580,0x499824c4195e0ab704ac024a81430076a0,0x195a0ca9065c832e5957207501,0x656832b41a1c07521,0x32b8957407584,0x329c195a0ca9065d032e99578077d0]
def a1Marks161 : Array Nat := #[0x195a0cad265d832ed957c077d4,0x654832dd9582078c0,0xca9065ab32e19584079a0,0xca9065b332e59586079a1,0xca90562033f81a0407ac0,0x19520ca90654832a4158c07b90,0x656932a4159207be0,0x49a932a4185ecc0c661783030159607c50,0x32a4159807d90,0x32a4159a07de0,0x65482b38122407e40,0xca9065483298159e07e90,0x63a456803408195207eb0,0xca90568832a418b007ee0,0xca9065482b4c195207f20,0x65bb2b541902c78c4,0x32e595ac079a4,0x654824e495ae07d91,0x32dd95b007f50,0xaa5065bb32a415b208020,0xbcf665c332a415b408040,0xbd9765cb32a415b608041,0x32a415b8080c0,0xca90617b32a415ba08180,0x2b78195208250,0x19520c88665482b7c195208290,0x32a419520c8a665482b801952082b0,0x15c407b94,0x32bc15c807be4,0x61a530d115ca07c54,0x15cc07d94,0x32a415ce07e91]
def a1Marks162 : Array Nat := #[0x32a415d007ee1,0x2ba41a2407ee4,0x2bac1a50080c4,0x61a532a415d808184,0x15da08251,0x19504ca90645bb2a415dc082b1,0x15de082d0,0x19520ca90650b328415e408300,0x32a419520ca9065482bd4195208370,0x32b898b207ba4,0x32b4194e085c1,0x65482be818b0485d4,0xca9061fa320c1900c87a0,0x19640cb8065c032e017a00cc20,0x65c832e417bc2cc30,0x6d70,0xc404,0x196e0ad86,0xae20,0xbd20,0xbdf1,0xcb8065a932d418604c300,0x65c832d818828c310,0x182c8d710,0x57e03215990a07b64,0x15fc07b2b,0x2bfc1a0808049,0xcc706640332019920d573,0x17a86d603,0x19960ccb06658332c19960ccb0,0x19960ccb06658332c19960ccb0,0x2c001a0808026]
def a1Marks163 : Array Nat := #[0x332c1996087e0,0xcca06658332c199c0d570,0x665833341a780d520,0x332c19960cca0,0x6f006668354819960d520,0x6668332c19960ccd0,0x332c19960c020,0x6658332c181a0ccb0,0xd670,0x16000d5f0,0x19960c320,0x359c19960d670,0xccb06658332c19960ccb0,0x16000d5f6,0x1bc019980d676,0x2aa833301acecd7a0,0x33340de40ccd0,0x2c041a0808019,0x1bd019960d520,0x160406fb050d8341019a408006,0x128a89464668a19911290094806690252012900cd204a19250c19a00a1c0,0x14d019a40cd206690333c19a40a1d0,0xb0305868341019b007fc9,0x66b0335419b00b1f0,0x19ae0cd8066c033681ac12b323,0x2c101a0807faa,0x586834101a0807f56586834101a0807f56,0x1c2819960d5206a90332c1aa40d520,0x161a0d5f06af82c341abe0d5f0,0x19960d6706b38332c1ace0d670,0x17b6c7f4a589834819a08086a6,0x61231f3256280d040]
def a1Marks164 : Array Nat := #[0x61331f2ad62a0d040,0x18c40c3963e44b044162c0d040,0x71706658319418240d520,0x33780f356b170,0x642b1e3296300d040,0x1c9019960d520,0x308118c44c620647b1e1e96320d040,0x19be0cdf23bea335199a80b1c0,0x19c00ce1064a9b1800e926d2b066bb34ad99ae0b1e0,0x19c00c6203a81b36199b00b1f0,0x67003258ceb06b200,0xce1062ca316498c407523,0xc6203a2cb3619a080b210,0x6712318119300a1803a0833a819d40b220,0x190119520c612630834081a040b230,0x318918c44c6203a1034101a080b240,0x6712319d18c64c6303a1834241a120b260,0x671a33a819d40cea039f034c41a62cb270,0x34101a080d04039f8357c1abecb280,0x19c68d090684834240e800b290,0x341c1a080d04039e535801abecb2b0,0x33b019d40cea067501cc919d80cea0675033a80e648d320699034c99a64cb2c0,0x672933a859d42cf20398a34cc5a66eb2d0,0x95504aa0339012a20cea04a88254419d4095103958254819e0895104a88255819ea8906a48eb25ec1a68097a04832247412f6cd3464bd32319918c0b2f0,0xce7267c8b3ec1a84eb310,0x6444674034081a040d020,0x675034241a080d04039aa35801ac0cb320,0x19d60d0906838341c0e6e8d610,0xcec0684834241a1207384,0x339499d40d0f06848b4244e6c8b360,0xcea06880b5885a5b0b370,0xcea03679b44459d40b380]
def a1Marks165 : Array Nat := #[0x33b00da06d1116888b44459d807394,0xc126d0e1,0x12bc09510675033a80cce895e04a8833a819d40667468da33a819d40b3a0,0x384b34591a62cb3c0,0x3765345d19d40bda66b6234c999d40b3d0,0xcf72d1a4675030d599d40b3e0,0xce902c0d33a81a388cea0646333a818ea0b3f0,0xd820cec067501b3812bc095604a9033fd19d40d144671a33fd0e688b400,0x199499d4095e04a9833a81a2a8b420,0x19e999d40ce6068c230da99d40b430,0x14d412bc095e06750257812bc0cea04aa8255019c8095e04af033a81a3a895e04af02511927eccd064a2024fc19a00b450,0x677034281a0a2d0403982b5801ac0cb460,0x677834241a0e2d040397db58c1ac0cb4e0,0xcf206790b4241a122d0403969b58c1ac6cb4f0,0x19e40cf316848343c1a12072e3,0x67901b4cda220cf20,0x2594129eacf213688b444d9d40b500,0x4b28259412ca096504a82a540d9c8696504b28251d9280ccd164a38250019a20b510,0x333033c819e40d153,0x33dc12d687294484d358017b6c90946b032f6c1af20b580,0x68201c925abecb5b0,0x0,0xb60cc819,0xd04038fcb4fd9abecb5c0,0x68201c76dac0cb5d0,0xd04038e5b50d9ac0cb5e0,0x25a819d40b600,0x186ecd436,0x19f00c8d6,0x1b58da080cfb038dcb51d9ac6cb610,0x19f0a67c767d830e219f60b620,0xcd40cfb067d833a4d8ec6b630]
def a1Marks166 : Array Nat := #[0x160999f60cfb067d8323a59f60b640,0xcfd068499c7a5ac12b650,0x34100dd2ab680,0x34100dcf6b690,0x34100dcc6b6a0,0x34101a0806d73682034100dae6b6e0,0x6888b4241a1206de36888b4241a1206de3,0x4b689b2552dc695746829b4100db06b700,0x6c796839b4100db26b740,0x19fe06c336849b4100db46b750,0x33fc0daa2cf2268a833941a2246e03,0x6b934b8aa5c4da080b770,0x6b734b92a5c8da080c39660a330e418280b790,0x38bd30569abecb7d0,0x1c569abecb7e0,0x712a673024291ac74b7f0,0x38cab0e598724b800,0x1aceda080b810,0x1acada080b820,0x358da5d0da080b830,0xcfb23585b39c1a080b850,0x1aaeda080b860,0x6aab682030e5991e0b870,0x3392a5d4da080b890,0x66d46820341019d40b8c0,0x66f46888b4240dbe2d1136848346d19d806df3,0xc8e8b900,0x340819fc4cfe0,0x18415a080b910,0x6195,0x2fd234101a080b940,0x33d10bee8d0406820323d991e0b950]
def a1Marks167 : Array Nat := #[0x1c299abecb960,0xe16cd164,0x1c1a5abecb980,0x1c069ac0cb990,0x6f065868357d9a080b9a0,0x6eda5edb35819a080b9b0,0x3775345d17b8cd090,0xdd72cfb05feb358d9a080b9c0,0x1a4a5a080b9e0,0x68e96820307d99a40b9f0,0xd0f2ba00,0x67d9682030e59a080ba10,0x67f9684834691876cd090,0x33ed0cef2cfb26820314d9a080ba40,0xbd54ba50,0x2eed34101a080ba60,0x33ed0bb54d040682031e599a40ba70,0xb6d4ba80,0x1a0605c3a,0x2c7d32159a080baa0,0x1626da080bab0,0x587b682032259a080bac0,0x33ed0b074d0406820323d9a080bad0,0x15681af40bae0,0x14e4da080baf0,0x14d81a080d0406820334999a40bb10,0xa5c6d1306820336199b00bb20,0x5249682033619a080bb30,0x28da34101a080bb50,0x14581a080d040682034101a080bb60,0x34241a1206c40684834240d880d144,0x66e26848342419e40d154]
def a1Marks168 : Array Nat := #[0x19f99a0e0cf9367c8b4611a120c224,0x33c3342419f84cfc068ca31529a120c234,0x341412e4097206770b1ddd8ee2bc10,0x341419f4ebc60,0x1a0e097404ba033bcd9e20c783,0x684833c899e40d1e0,0x341019d42bc70,0x1a080bc80,0x1a222d11067f834781a3c06e33,0x68f834881a400d200433835801adecbe40,0x1c5d98ca0c490,0x69283480187c4c4e0,0x34a00e48cc860,0x341018848c870,0x39a8332018ca0cd90,0x6958336197c26cda0,0xe7e0c6546658319498ca0d520,0x341016480d5f0,0x348017c40d600,0x2b1834a81af40d670,0x74206a9035481aa40d520,0x357c1abe0d5f06af821f816500d9a0,0x35801ac00d6006b0021fc17c60d9b0,0x74506aa035481aa40d520,0x34b01a720d39069c82f901b180a120,0xea00d2e06ab0355c1aa40d520,0x7520697835581aac0d560,0x6980355c1aae0d570,0x1a620d6006af8357c16640d9b6,0x1a640d6006b00358017c80d9c0,0x1a660d6306b00b58057ce2d9d0,0x69a8359c1ace0d670]
def a1Marks169 : Array Nat := #[0x3ac034b81ad42d2e0,0x699034c817ca0d9e1,0x1df41a6e0d3716ab035601aac2d520,0x6b18358c17fc0d9f0,0x3c6034f01aa40d520,0x1a780d3c0,0x10f46c430,0x34f00f240d3c0,0xf260d520,0x3cb034f41aae0d520,0xf340d520,0x1e319ab60d520,0x357c1abe0b5b6,0x69f8357c1abe0b5c6,0x6a003580dac06bf03,0xf34cd520,0x6a1835801ac00be90,0x350c1a860c440,0x350c1a860c460,0x35301ace0d670,0x7b906a9035481aa40d520,0xd6006b0035801ac00bea0,0x3df035381aac6d520,0x1ac06bf43,0x13000980069c834d89a6c0d6b44c0026001330090c44ca12438988e49942485930649328090e06238265012160c190,0xf8a098254c11b54818920c1a0,0x1a920d41062392668189c0c1b0,0x359c18a40c1c0,0xf980d520,0xfb00d520,0x1f6413066d520,0x1f6593086d520]
def a1Marks170 : Array Nat := #[0x350c9a5a0c482,0x3f4835481aa40d2e0,0x6af8357c1a620b8c0,0x6b0035801a640bec0,0x6b00b5805a660bf61,0x6b1a358d1a680c004,0x359c1ace0d350,0xfdc0d520,0x1aa40d5203fa835481aa407f50,0x1aa407fa0,0x355c1aa407fc0,0x6a9020081aa40ccd0,0x6a9020101aa40cce0,0x6a9020301aa40d3c0,0x6a9020601aa40d520,0x6a9020781aa40d520,0x1aa408250,0x1a7c8d520415835481aa40d520,0x1ace07f56,0x2009972c0d9a0,0x201197da0d9b0,0x1018cd520,0x20619aa40c490,0x8256,0xd444415b35481aa40c900,0x359c1aa4082d0,0x1aa40d520418035481aa40cd30,0x1aa40d52041b835481aa40d520,0xd56042e034dc9a6e0d6d0,0x35481a7888600,0xd3906b622fb81b380d600,0x355c1a7a4d3d0]
def a1Marks171 : Array Nat := #[0xc4a2,0xd4806af82e841abe0c1d0,0xd4906b002fbc1ac00c1e0,0x6a503580d7ee6d603,0x35481aba6d5d3,0x356c1ace0d670,0x1ab80c4f4,0x1abe0b966,0x1ac00bf10,0xd670,0x1abe0d5f06af8357c1734cb9a6,0x1abe0b9e6,0xd5f06af834fc18960ba16,0x1abe0d5f06af8357c1abe0bb60,0x1ac00d6006b00358017e40bf20,0xd6006b00350c18980bf30,0x35801abe0d3f46a11b508589a8bf80,0x35801ac00d4046a29351418aa8bf90,0x1ac00d6006b0035801ac00bfb0,0xd6006a19350c189c4c4e0,0x6b18351c19226c510,0x1ace0c520,0x6b38359c1ace0d670,0x359c1ace0d4c0,0xd6706b38359c1ace0d670,0x21f99aa40ccd0,0xd7a0,0x1afe0d8206ce036701b380d9c0,0x110408821441822101b420da206d21b6915b4c68dc3,0x22c0116628ab345a1a3dd1b52093e0,0x456022d4116e2da5045b9a32d1b428dae0,0x116c08ad145c0a2e4d194ada02]
def a1Marks172 : Array Nat := #[0x45e822b8518028ae34601b6c01b6009990,0x497836ad1228893016d5024c0d29209816,0x498836b0122a894a04a6225e41b4609796,0x89a0499836b0122e894d46d5325f01b54097c6,0x89b049a036b0d268294b36d5b25f41b56097d6,0x12304926049a8a4d8d30409826,0x12320925849b8a4e4d30609846,0x12740927149d8a49cd27669936,0x57132b5995c44ad6257102b5815f00a8e899d42be0151c933a457c02a3826740ae0851842b8114608ae0051802b48267c0a76099f0,0x32c819100caee5a0a32bb16820cae25a0432b816808c8005410326094ac4c98052b031c316718c70059c0,0x77603a581dac136689b006d8a1d040eb609af03a4826bc0ee6c5afa3b4b1a198ec8c52263b9816bd0ed2068603b2014880e7c05590,0x3f499d40cfd2275013f481d40103145b6a40c416da1030c5b6640c216d9103045b6240c016d80e7e055a0,0x20f88efc483e03bf01fa8137269b916d8a1d48108ac5d9a40cc16e61032c5b9642281765103245b9240c816e40e80055c0,0x563126fc1b7c09bf0563026fc1b7c09bf0550026fc1b7c09bf0515826fc1b7c09bf0,0x5b7227041b8e09c105b7127041b8e09c105b7027041b8e09c10516827041b8e09c10,0x278813980db205639272c1b7e09bf0563027281b7c09ca0550027281b7c09ca0515827281b7c09ca0,0x110609d004e382b21539e0dc034df9ab20d39e2dc054df9aa84d3a009bf35159a7381b7c69ce0,0x443827c413b40db405b8227581b9009c105b8127585b9029c105b7027541b8e09d50516827541b8e09d50,0x444027c813b60db505db827581b9009d605b8927601b9409c205b7827581b9009d60517027581b9009d60,0x2224110c288604fa8a71513ea09c524f9827681b6809da05b92276c1b966b7224ed8b72d53b409da04ed0276813880db40,0x89004478a23c13f429e014fd0278013f209df06a6a27981bb66d4d24f30b76d53ca09e504f28279413880db40,0x22501124289204fb0a7b053ec09ec04f9827c41b6809f106caa27c81bcc0d9524f90b79853e209f104f8827c413880db40,0x11304898044b82719140e4a0506db0281c140a4db625b9a280c1b9209c105b8128101b9029d525b8028109b9069d50516828081b8e0a020,0x2dd1141c09c105b7128341b8e0a0d05b7028341b8e0a0d05178283c1b9e09c10,0x11380a2725138289814440db8056512728959409ca0550028841b7c0a210515828841b7c0a210,0x44e8289413908a2a251502de5144a09c105bc1275496f009d50516828901b8e0a240,0x56592728959609ca05508288414560a2b06df028ac14560dbe056592728959609ca05508288414560a2b06df028ac14560dbe0,0x5bca275516f249d525bc82754145a0a2d06e3828b4145a0dc705bca275516f249d525bc82754145a0a2d06e3828b4145a0dc70,0x2b3094140ac6051a836f8146a0aa20519028d8149809ca0,0x15aeaa0b456b9a82c95546a3a04df9a8e4149a09ce0,0x2e0d141a2b83250682db814820dc7052082918149c09d50,0x1140089f144f82e1117084a4605230306458320a4605230277413b40db40]
def a1Marks173 : Array Nat := #[0xb874509a2e1c94264b7905208311c588e09de052702938145a0dc70,0xa5b052a836e4159c4a1505630294c1b7c0a5305500294c1b7c0a5304518295014f009ca0,0x297414b40b8c152e8270417124a1605b7029701b8e0a5c04520297814f209d50,0x15000a802a6445318b6e854c84a6306dd0151814d00a6802a4829a014d0054a0,0x114c0a6a15350151413380b8c150b0ae30142c0b6e05358371c14d608a51452829b014f409d50,0x29c054e00dbb05c8a29d013820b91253a0a70416ee0a500539829cc54ee0a200,0x173c8a7e04e082e0494624b810518831c4151809c10,0x173e8a1e45c19290497060a41054182a0c951e0a020,0x2b3494644acd051902a80150a0dbe054282a1815160a210,0x17428a8a04e082e1894664b86051982a2415180a240,0x152e4a97045602ebd153009c1045792e2094a248af05c40294413ce89cd46d9a22b8992648ae06498324815f809c10,0x15a24a5325688294c15400aa006df02a8015400dbe05689294c95a20a53055002a801b7c0aa00550036f8116048b005508288415420a210,0x45882b4894a64ad2052982bec95f60aa1055082a801b7c08b2245902a8415420a2b06df0289814440db80,0x15ba4a35256e828d415540a85055282a9414560dbe0,0x56f9298095be0a60055502aa815400dbe055502aa814560dbe0,0xaf504df82ba014ae2ab10536822cc155c0a231,0x57a8299894ca4af505330299415660ab30550036f80aa4099f055982acc14560dbe0,0x2ad8956c0dbd056312ad41b7c0ab5056302ad41b7c0ab505680285419780abf06eb026fc1162089c0,0x2b2495680ac6055c836f815720a520568826fc116e0882265e82b001bae09bf0,0xad4045b12ae095f04acb056582b181b7c08be045192b48114e0a75052a022f419800acb0565828ac1b7c09e204e6036c811640a270,0xacf056782b189b7c0acf056782b181b7c0ab6255b036f415a60a99056a027fc15f00af82,0xad3056212b4415a20ac606df02b4415a20aa006df0296c14aa0db9056902884117c4afb0,0x56e12b0495b80ac1056f029ec15b209bf0,0x57002b0895ba0add0563036f815be0a92056e82b7414560dbe0,0x15ce4ab9257382ae4176c0af504e0826fc17224a5c25c88297015ca09ce445f922fc15f80a240,0x15d448b8255d92ba811700abb045a82bd4144a0a2105c912e4815ca0ae50515836f811804cc124600330419400a250,0x2bc815784ae7057382b181b7c0af5052e8294c15f44a5d05750280055f24afd0,0x2bb895864aee056182bd415140a85057602bb014560dbe0,0x57812b1495e00ac5057982a5015ea09bf0,0x57a82bd4158c4dbe057a82bd4158c0dbe057a82bd415400dbe057a82bd414560dbe0,0x15fa4afd046102ed813aa89d045c99297097260a5c066202741118648c3057e02bf0145a0dc70,0xb9e451a22e7894684b9e051a0332c161a09c10]
def a1Marks174 : Array Nat := #[0x8c6058382c1c16860a3d459f82a04167a0a0c0464034b016140dda058382c1c14580dc20,0x17428a4145d09290497420a41058682c34145a0dc70,0x118e6bba052422e8c94864ba205210353c16246ddb358702c38145c0dc80,0x1540d75a2a4945d68292497420a6b058b02c58145a0dc70,0x2ed814828a3a45d61298497580a61058c02c60145a0dc70,0x16402b2006e081544d76c0a5c452ca2ed814b84a5925d9029ac11960884058f82c7c145a0dc70,0xaa4055212a91aed814d68a6845db029ac94d04bb60535829a00ad40b240592028b41b8e05790,0x16dc8b2806e382ca016dc4b2806e382ca016dc0b2806e382ca00ad4099f06bd82d5c1bc209c10,0x2ce096700dc205baa2ca016dc4b3206e382cc816dc0b3206e382cc811b0088746bf82d601bc409c10,0x235016840b2d159d02ce01b840b38059c02ce016700b3805960370811c20b3904e88360016b20de30,0x239c11a46b2e15a502d201b860b76459402dc0968e0dc8159902db8168c0dc705a302398111688e404429361016920de006c182d601bc409d50,0x11a66b5015a802dd516642b75259902db8169e0dc705a7823b051d809d206c302d681bc809c10,0x479123c811dc0b5925ac8371411e20b7c4467a2ca916f24b4625bc82d1811e00d8f0446227c11b1249ef26c4827bc1b0e0b5806f102d60145a0dc70,0x17048b2b15c112cac16dc0b5b06e382d6c16cc09c10,0x2cc456c00b8545958ae0c96640b6e05af0371c16bc08f4047982d7c16ce09d50,0x46b9adac56d60b8b45990ae2c96640b6e05b50371c16d408f6147b0275016f209c10,0x17182b3215c602cc816dc0b6e06e382db816dc0dc705c60acc857180b3205b702db81b8e0b6e05b70371c11ee28f705bc8275416f209d50,0xb8f146a8acc857180b4625dd9a354566a8bb9359a12edcd6e00dc835b802db81b8e08fa047c0365416e40de505bc82808177069d90,0x47e02e30569e8b8c05a792cd9166c4b7505ba82db81b8e08fb147d82df013aa0bbf3,0x46c1ae5451c88b4645ca82390968c4bc155e09ade416f20b6e06e3823f85b2c28fe06cb02de416f20a2d06e3827c413b40db40,0xba715a722e3016bc4b3725c182e0c16dc0dc705c202e1c14040bc03,0xbb105a7a2e3017180b6e26e382e3017180b6e06e382ce096700dc205ca8280817822bc13,0xbb605990ae5016d04bc755c882e4416dc0dc705c902e4c144808ff2,0x176c0b5245aaa3711172a0b9505b71371c172a0b9505b70371c11ac0d9745ca82e54145a0dc70,0x5cf22d6d173c4b5b25cf02d6c173409c10,0x17428b5c45d092d7097420b5c05cd02e68145a0dc70,0x17488b5c45d092d7897420b5e05cd82e6c145a0dc70,0x2e9856ba8ba605ae92e78173c0b6e06e382e8413aa0bc23,0x5d68ad79175a0b5e25d082e8416dc0dc705d082e84145a0dc70,0xbb605ada2eac96d24bab05b482ea417540a240,0x5db02d8516c88dc645d682eb416dc4dc705d682eb416dc0dc705d682eb4145a0dc70,0x5d7a2da9175e4b6a25d782da8176c09c10]
def a1Marks175 : Array Nat := #[0x5d80ada917600b6a246d1aebc175e0b6e06e382ed813aa0bc33,0x17620bb105b72371c17620bb105b71371c11b66bb105d882db81b8e08db146d82ed8143a0a1906db82f1017882bc43,0x2ed816da8b6a45da82ed416dc4dc705da82ed416dc0dc7046e02ed814480bc50,0x5db02ed816dc8dc705db02ed816dc4dc705db02ed816dc0dc705db02ed8145a0dc70,0xbb905dc03720178808ea35e082f0411d22b4c15a40b70c51bc0a0915028b6d857820bc106cc9366017924de72,0x17ee0bd305f792f2c97de0bcb05eb82f5c17940dcf0,0x17f00bd805f992f3497e60bcd05ee82c35945e0dc70,0x2f9497ca0dce05fa02f8c17d44be406e782f9017d40be406e782f901202088d46bf82fa01bc40a0f0,0x17f20bf005f992fa497e60be905f902fc817940dcf0,0x90306038b01c0b3209a004810a40818120c48762433020181009de6,0x16840b4225c902e503044182205cd0,0x1210090714838173c18362c1b0604835429aa10c14060a0279593ba0db40,0x18600c04661602a9594980dbe0,0x17c018822c41061f82a96549a0dbe3,0x17c0189c2c4e060432c35949c0dc70,0x6250b12818860c010,0xc51062703138188c0c4406e882fcc97980dcf0,0xa56652b036e418b00c580,0x314818b814c4ca6206dd018b98c5e062f2,0xc6209a60,0x6310318899440ca2c65a0,0xca209a60,0x31ac18d20dd20638031c194dcca6e06dd82458121e0ced3636037600cce09af3,0xc7d063e0374c19000c800,0x18f6cc7a66e9b2a9595160dbe0,0xc87060752c3595180dc70,0x6a0035101a88992206a40586b2a3c1b8e06a80,0xc9b264d837540d8809b80,0xca60653032c81964caa46552036f41264092906740285c0d9a09af0,0xaa56552836f80dae09b50,0x687031580dbc09b81,0x2b65954a0dbe0]
def a1Marks176 : Array Nat := #[0x2f44179c0dcc0,0x2f8057aa2dcd1,0x19900cc80,0x19960ccb0,0x199a0ccd0,0xd96094834a119b2c5290294214a4025080d9666fa050db28681b6e06fc0,0x3661ac3596060dc70,0x129a094c064b9b250dba86d13062f81cc8135e6cd6666b02c19960c0dc10,0x6cd04af025440cce8cff46760376519d40cea0399234c80ec00d326583b2c1c1b8407606,0xd840668468a233b01bb28cec068da33b01bb28cec0399a26b91a2f4a1163b08345d142207616,0xcd246d21679033c819fe4cf306ec91cb0cf0207816,0x6d4036a09c6a4f440d46658632c2c1b8c07a40,0x335833d40d8c6d1d06780345019fe0dd9067f81b88d358691e968c3303d8f80091e368c0303c118807c06,0xcb489a64,0x36b81b5c4dae67f50586b2c341b8e07f56,0x365125bc12ae66db136e1b5900fec0d64658732c381b9007f66,0xd90c6dd136e99fdc162007f86,0x36201b785a226d1116eca1b78cff207f96,0x33811b145a364d1106ec934441a2a4cf303709a6acda350c10643083468982008616,0x338834555a2a8dd9433893454da2a4dd9268a8b4541bb20671443302538118a08666,0x37201b944dca686905ee82f5c1b9e086b0,0x1d80135e097c04bc835391a5e0ddc4698034b81a5c0cca0,0x25e81a640d320699034c817cc0bd606e7036081ad88de84,0x34e89a740dda04bf825e11b240c1846c69305c9b1a0c1706c602fa017ae0dcf0,0x34f01a780c020,0xd4306a18311418660dd10,0x1fd4136a0ccb0,0x7f904dc035a8dad42ddc4,0xccb0,0xccb0,0x2e69961a0dc70,0x2fc817ae0dcf0]
def a1Marks177 : Array Nat := #[0x6a302ffc17f80dd00,0xccb0,0x2bc8267c1aea0d7406ef0319918cc4c660,0x36009b000ddf04c4026191b1c0d7c06c4135fc1bc40d7f06c4035fc1bc40d7f06c3835fc1bc40d7f0,0x4cb9365c131aa99626cc8a628d3204d9604c793658132e0d9724c6a2648131c0d8926c4837881324098c26c2136149bc0499606cc9a6285324098c06c2836101bc0099106cc1b6605bce898904c803658131e0d960,0x1b18cd8c06f103678db3c2de84,0x13820df706fb837dc1bee0af50,0x4df826fc537e6e000700038001c000bb60,0x9c10712838941c4a0e250,0x27541bd20df806fb837dc1bee0af42,0x13aa09ea06fc9b7e55bee6af33,0x9ca04e50a7381bd60e0107008b8001c000bb53,0x9c904e58a73c1bd80e010701838041c020bbe0,0x9cc04e60a7341bd609fc07021b8115bd60bc53,0x4f08278453c809f8670b1b8595bd60d693,0x4f10278853ce0deb04f48388c1c462deb0,0x9d504f5038981c4c2e250,0x13fe0a000500137b41bda4e0207008b804dc000bb44,0x282814160a0b2700038001c100bb3a,0xa2406f7837dc1bee0af10,0xa2105118288c9c000baf4,0x28b41bee0df70577837dc1bee0aef0,0xa2b05158a8acdc000e0005d7038001c000bae0,0x29041bee0aed8,0x290415bd2c160,0xa35051a8a8e01c000ba89,0x146c0a36151b82ea65bd60c1c0,0x14980a4c152682e965c000c520,0xdf0052e037dc1bee0ae92,0xa53052b829601c000b915,0x299414ca2df116f8829a416466c660,0xa6605330a99c1c000b903]
def a1Marks178 : Array Nat := #[0xa6d06f9029b454de0b8c3,0x53d829f014f84ba1a,0x53f82a0015004ba0a,0x2a201bee0aeb6,0x54282a1c150e4b9ea,0xa94045582a5411564a9525bca37a91b4e4da70,0x1bee0df70571037dc1bee0ae20,0xae106fb82bf01bee0def0,0x2a94154a2df50,0x2b61961a0df70,0x56ab37dc16300df70,0x158c4ae21,0x55a037dc16480df70,0x1bec0df706fb82ac816640e100,0xaab26fb82ac496642e110,0x45982a54dbee08bf05bc836a01bee0de90,0xa6f46fb837dc1bec0b8c0,0xa5856fb837dc1be00b910,0x154acb960,0x53e4b7dc17420df70,0x55002ab055586b6e4,0x2a50116808b425bca37dc1b524da90,0x536937dc155a4b8c1,0x29ed97428df70,0x14560bae0,0x137e0df706fb837dc176c0df70,0x15420aae15571ada91c000cc50,0x55182a8c55466b9a6,0x2a9014dc8b06459e338541bf60d350,0x154a0aa515529ae599c000d670,0x2a74954c2aa735cbb3858dc020d680,0x15520aa915579adf65c000d700]
def a1Marks179 : Array Nat := #[0x15540ab015581ad6e9c000d710,0x2ac41bf40ab115591acc8dc000d770,0x15660ab315599aca01c000d7a0,0x55a02ad055686e0007000380016480e1d0,0x55a82ae45bf60ab9370003800163e8e1e0,0x2ad814e08dfb055d1b7ec16408e1f0,0xab8055d8b7f0157a6e01170002c755c380e1e0,0x15780abc155f1b80016386e200,0x22e8157e0ac016ff02b00d6348dae06d1238781c000d930,0xac105608ab54dc000b189,0xac205618ab58dc000b17b,0xac505628ab84dc000afc3,0x56302b185c000e0005711b8001c000ae23,0x8bb056382b20553cada447009b80015c66e220,0xac905648aa70dc000ae43,0x22fc159608bf15658aa58dc000ae536d80b6c01c000deb0,0xacc056b8aa46dc000ae63,0x2b3c14e48e0005738b8001bf60ae73,0xad1052e2aba05c000ae93,0x56a037f5149e8e0005750b80015d46e000,0x56c02c3595b02ad83,0xad9058032b6455b26e000,0xada057fd2b6c55b66e000,0xadc05444ab705c000aeb3,0x15ba0a7d956e8b80015d86e000,0x56f0290695da2aed3,0x570037fd14614e0005770b80015dc6e000,0x51682bbc15de2aef3,0xa24357802bc05c000af13,0x50f8380015e40e0005790b80015e46dee0,0x275515e60e00057a0b80015e86e270,0x4e08380015ea0e00057a8b80015ea6e000]
def a1Marks180 : Array Nat := #[0x53993804152e0af816fe0abe4dbda2e282,0x179c0bd505ea92fc41c100d664,0x179e0bd905ec92fb41c000d65a,0x5e802f781c0e0bde27040382017c20e1e0,0xbd105ea02f8017c04e080,0x60203010580a0c4f6,0xc0b06058b048182a0d276,0x18180c0c1609830681bd60d5e9,0x2904182c0e250,0x18720df70,0x30e418800df73,0x185e0c2f161a031241c000d5d9,0x18720c400,0x18600c2916188b82818820e080,0x315c1be00d122,0x18b40c5d06f88317598c22c613,0xc620,0xc5e062f0b19418cacd023,0xc620,0x705837c81c260cea3,0x383019020d286,0x3831990a0df70,0x19040c840642132181c000d5ba,0x19140c8b0645932401c000d5aa,0x1c1c0d090,0x196e0ccb0,0xdf40,0x32941bec0cea0,0x1bee0d040,0x19484d091,0x0,0x1bee0d5f0]
def a1Marks181 : Array Nat := #[0x1c0a0d600,0x1c0c2d601,0x154a0d670,0xcb76,0xe120,0xae20,0xd603,0xd5f0,0x19980d9a0,0x19960e250,0x16000e250,0x19420ca116509b34c1bdc0d596,0x19440ca216519b3641c000d579,0x6529b834d9d46dfa0,0x329818d08e144670234b81bf60d2e6,0x326418d28e14470a233851a5e0d2f6,0x18d44ca7170a1337cda6e0d376,0x19500ca8166ecb4f81bfe0d446,0x18d60c9c370a032bcda9c0d4e6,0xc624,0x19520ca916549b5481c000d526,0x193e4caa16559b54c1c020d536,0xc9e66560b2b0daa80d556,0x19340cad170a232b4daac0d566,0x18da4c9b170a132b8dad40d6a6,0x6378385118de4e14270a031bd1ada0d6d6,0x19600cb116589b5451c100d6e6,0x19d40e174,0x19640cc74638234ad1c0e0e294,0x32cc19682e15065a1b4a51c100d8b6,0x19032d283,0xcb506391b2d859bcae0a0]
def a1Marks182 : Array Nat := #[0xd040,0x1a120e174,0xcd8a,0xc39a,0xcb70665832dc596e6e000,0xcb80664232e459726e080,0xcba06631b2e859766e090,0xb0d0,0x16480e190,0xcbc065e8b868197a6d72470f038781c3c0d764,0x16640e1b0712838941c4a0d774,0xb6a0710838941c4a0cc53,0x12780cc004940b24c5b600db0049e8b3045c3c0e1c24941b24cdc380e2846d8036c0127a6cc13,0x5bc824f8127c2e250,0x5c6038941c4a0e1b0,0xd5f6,0xd606,0x2e581c4a0d676,0x330819928e1e0664d330c5c528cc33,0x17420e250,0x1c4a0e2505d7038941c4a0bae0,0x71282ebc1c4a0e210,0xe2505db038941c4a0e250,0xda806d38b6a45b4e6da93,0x4fd827b813ee29ed14fb827b413e82de546da838acd37c09f406f2936d45c56a9be04f9836d013880db40,0x56782ad415a24a5325688294c159649ca25658272815420a210,0xb45059782d00164e0b3a06e102cb01b840b4104e9a2cec14020b3006ef837141c5409c00,0x5c61acc8d7182b3215c602cc816f289d545bc9275496f209d50,0x2ef0166a6bb905a38ae3416660bb805020adec93ae4b7a06f30372cdc5669d60,0x5fb12f9c97ec0be705f602f9017ea09dc45f59285097d60a140,0x4d38347419ec09aa368e331d25a32cc2164dd0347018e86d19061083388160a09ba6,0x36449b026d9106c08b6281bc64de30715035fc1b200d7d46c49360c9b120d830]
def a1Marks183 : Array Nat := #[0x13c60db206d08278c5b642da016d0027a01b660e2246f6038b4dc444dec1716ab7ac1bd609fd0,0x556036f815582dbe1,0xaac055612b881b8e0aef0,0x156e0dbd06d1829c51b768dfb06fd82c791b828da5070d037f81c580b440,0x2b881b7c0ae216df0ab88db7c6bae0,0x2a7c9b784da4357b0b6fc55ee6dc0371183810dc5a6bbd0,0x2f481b980bdf06e682f7c9b9a4bfa0,0x15de0dbe0,0x63703748193a6dd5368b037701a2ccddc6,0xcbe06eb032fc5bae2e1f270f838b0197e6dd736d7836b51ae68ddd4,0x175c0dc70,0x1bd20de916f5038bcdc5eae273,0x6fa037dc1bee2e0f0,0x6fa837d49c000e120,0xdf606f9237e91c5c0e1b0,0x6fb837dc5bee6e250,0xdf326fc0b7e4dc5e6e260,0x702838181c0c4e24a,0x6fb8383c1c1e4e250,0x70583838dc2e0e176,0xe1007088b8b81c226e184,0x700038481c242e123,0x727838d81c904e392724038e41c80ce3c6720038f01f840e3d08ce038f41f584e3d08ce038f41f580e3d08ce038f41f28ce3d08ce038f41f280e3d08ce038f41f200e3d08ce038f41c6c11600,0x725a39151c964e452725839141c9e0e360725038f821068e4908e88392421660e4908e8839241c6c116008419392423a20e4908418392423a20e4907fb3392423a20e4907f98392423a20e490,0x1c644e320718839ae9cd68e736739845981d180e370741939b09d060e6c073cb39c822d20e6f673c839c9a2d2ce6f07e20394d1f5c4e5227d7039481f28ce7108ce039c41f280e7108ce039c41f220e7408cf839a01ccc11650,0x1d0c8e7e47199ba189cfc4e331743039f81c660e8c071b83a141cec0e7508b383a3d9d1c116c0846a3951216c0e8508ea839241c6e1160084693950a11a0e5407fb33a1023a20e8407f983a1023a20e840,0x745239fd1d144e7f271a1ba281cfe0e34171a03a301ceece7568b3b3a301cee0e7508b383a419d20116d087483a3023ce0e4e071b84580211c8e56484713958a11c0e5607fdb3a2423c20e8907fd83a2423c20e890,0x74f83ac41de40e38076c03ab01dae0ea4076083aac1d720ea807e2839685f5e4e5907d603ac023380eb007cb339481f280eb008ce03ac01f240eb208d003a641d2c11700,0x1c6a0eea17568bba81d5a0ef2071c03a801d8a0ebc077b83b0c22f00ec4075a83ad022e60e6b07dc2b9691f706e5a27e11bb0823386ec207cb9bb1023586e3d371c045801f332e5307ca1bb0823386ec20,0x1dbe2ed1176f83b441de60edd08bb03b301de40e38075103b701d6e0ef40849a397461680edb08e983a741d34117108499397421060eda08e883b682000ce5407f983b6823a20eda0,0x1dcc2ed2177303b481dc80ece0766845d01dc60ebd075133bc81c700ef5084a239786170cee408ebb39259c701160084a139782106cee208e8b3b881ffcce5467fb03b8823a2cee20,0x7770bb4c5ddc0ed3077903b3c1d9a1174077683af81d46cef2075b03ad022e60ef608734bbc823ce0e4d971c04580212a8e5f484a9397ca112ceec08ee4bbb02002ce5567fd1bbb023b92eec0]
def a1Marks184 : Array Nat := #[0x78403c281e460e39078d03c1c1e320f0b08c083c141e1acf06678683c181f8c0e3d07d8939881f580f0908ce03c241f2ace9967ca83a641f200f0908ce03c241e0a117f0,0x7a283d141e7e318d07a283d141e7e118d079e8bcf423180f47079d83d241e922f46679b33d181e6c0e3008549bd2023ce0e47371d045802142af4a08f49391ce1426f4a18f4a391ce1180f0407feb3be59ffa0ef90,0x3d7c1ebe0f5b08c703d809ea84f6007aa03d7c1ebe0f4e08c703aee9ec20efc477da45e921c54f6108f3839329c7611600869a3d8823d40e4ca84893a54a1220e950809b3d8c23d60e4ca7fca3d7c23b34f5f0,0x3ad51f040e3c07bb93c189eee0f0607b803dac1ede0f6d08c883da81f940e3d07d813a649f600e9907cbb39a01f280f6c08ce03db01f200f6c08ce03db01ed411900,0x7e7838f41f684f0927da03c241f2ecf6c67cb83db01f200f9008ce03e401f20119c07e7838f41f684f0927da03c241f2ecf6c67cb83db01f200f9008ce03e401f20119c0,0x7e783b091f804f2427e003c901f3a0f8367e9b39c99f2e0f9707ca04670202a0e40080513c34a0140f0d080283dc1a0080f9708d603e5c1f20119c080203dbc1eda11910,0x1f900f0f47e7838f41f8e0f0e17cd33dc5df340f7117e78b8f45f902f0f27e38bc381f362f9b08d783cd45e6a118d07cd3bdc59f342f710,0x3f3c1e528f2848c223f3c1e4e4f2628c193f3c1e4e0f2608c183e741f3a0f9468ce03e741f3a0f9408ce039cd9ce61166081c8390820644f12281903c4820560f9d08d903e741f20119c080333dc9a00c0f720,0x3e849f42119a07e183e80233a0f9e07d613e7c23380f9f07d603e7c23380f9f07ddb39659f760e5908300391020964f13282583c4c20940fb308e70398c1cc411630803b3dcda00e0f730,0xfa507d18466c1f840fa208ce03e881f5a4fa408cf03e781f580fa208ce03e881f78ce5a77de0396860c02e44182c8bc54a0b02f140784045f820b02fb408e7839105c7a1160080433dd1a0100f740,0x1f9c0fa707e883ec81f640fac28ce03f449f640fb207d6046701f424fa108cd038d69f82cf64671aa3f041ec80e3108548391c21300fb508e803e301f161197084b93c609e145180284b83c601e1411800804b3dd9a0120f760,0x3f3c1f440fb507d593f489f680fb407d6046701f80cf8567e003e1421640e48085503ed0239e0fb407c80467021560f1a285503c641e161181080533ddda0140f770,0x1f920fb607de93ea09f7a0fa807e7838f41f740f9308630392421760fbf08ee03d5c1e98118e085693c6ca15a0f1b0807b3de9a0160f780,0x3f301f6e0fc107d493ef81f7c0fac08ce03f3c1df4cfbe07df03e5023380eb108710393021b20fc008ef83e241f101195085793c74a15c0f1c080833deda0180f790,0x7e103f0823380fc207e1046701f840fc208ce03f081f84119c07e313e889f8c4fa227e303e881f8c0fa207e533b0a9f94cec2a7e503b091f940ec2484523f3c23ce0e46471e8458021148fcf08f3839191c7a116008442bc78a1108f1e0808b3df5a0220f7d0,0x1f8c0fc607e1046701f9c0fa627e803f181f8c0fac08ce03e941f46119b07e893f319ecaefcc07b28b8c821522fcf08f383c7c1e12117f08548b91c61442f2128508bf48a3d2af1f080933df9a0240f7e0,0xfca07e503f0823380fcc27d513f301f540fcf078153bf6a2f94fca07e503e5023380ef74761a45e121c48fcf08f383dfc1ed8119008712393121624f20285883c802028cf81680983f4da3d6cf7f0,0x7e783f3c1f84119c07e783f3c1f58519c07e783f3c1f58119c07e783f3c1f28d19c07e783f3c1f28119c087503f3c23ce0fcf07c80467021d40e4f085913c8ca1640f23080ab3e09a02a0f820,0x3f7d1fb68fdf27ed93f7c1fb60fe5071f03f981fbc11a307eb039d821708e9d485983f7423a20fdd07eb0468821704e9d285c03a7420660e4907f983f7423a20fdd0,0x7fc23fc51ff04ff127fc03fc41fee0fd86860d3b89218ccffc08f3839259c7e11600860c3b88a182cee20819b3a119fec0ff608e8b3fd81fec11d16860d3b89218ccffc08f3839259c7e11600860c3b88a182cee20819b3a119fec0ff608e8b3fd81fec11d16,0x101e180f046b82042301d08d7840742042101d08d7840742040101f08d80406c20c06f144788245f920c06f142788145f8a0bc6f3107950462020c0702908f383910dc82116008123396e6054cfea68120396ce0540fea0,0x102f4816046c82058102f2816046c82058102f0816046c820581041079823cb1230e9041079813cb0a30e5041079803cb0230e1041081c8479c1c860e4208b0043ac2068d1ec0721040b020580fef68d9843ada06811ec6721040b020580fef08d983a359d1a116b0,0x10354817240d4a05c50350817043181e648f2e48c524318207211e707ee83f64234410c6079913cb8a31450c6079903cb8231410390721040cc20660ff668e8843b1a06811ec67ec840cc20660ff308e883a3d9d1c116c0,0x416820981052282394148208e10612830846e02116904e08e9040f8216a104f08ea04110208411b408419413423a2104d08418413423a2104d083003910217e0e5e682803f68216e0e5d0,0x41b460cc306d0833041d420d611bb083204249208830b308348474420d2106408dd04248a088108308348474420d21074072283b39a1820e49083503f6c216c0e9d0,0x851841c9218a1062485d0427423b6109008478471c218e309b2834142642132108328e88431ce1361068084c84264210611d1083094184237010a907238430c1ed0d09a07ee042f01ece0e330,0x85c241a5216610b308e8842cc216611d1085c241a5216610b308e8842cc216611d1085c141a4a1705069285c041a421701069086303924218c0e49085b03f74216c0fdd0,0x42e520ec90ca483524324216c11d5085b042cc23a210b9283b14328a0d450b9083b0432820d410c60742043341c9410b6085b03fcc23a210c907f303f78234610ec6,0x85d0c1e121a0306d4867042e023ae10b8085984744217410782868041b4a17010b8084184744219c10750835846ec218c0ee2686a8392c219070b907f3843281fbe0ef30,0x42f060f490d1483724358217211d9085c842cc23a210bc083d14344a0dc50b9085c8420c23a210cf0836043181dfed0e20726042e421720ff308e88432c1fc00ef40,0x2180906fa860541bd2188d0c408f0840f9a07c11b30860141be2181106f2860041bda180d06f085f03f85a18cce49686303924217ccfe10,0x10c3183e5435120e290e268630479c20e0106908dd0430c20f910d42838943042182108308e884320e1a611ea38380430421820ff668e8843899c98cef5686303bf821980fe30]
def a1Marks185 : Array Nat := #[0x86304318210691d108750431823ce10c608598474421aa9074486304318210651d1086a941d0a18c10c608418474421aa10740863043181fecd1d108750393c218c10c607f984744219a0fe50,0x47bc1c8c943b08fa050ec2876143b0a1d850ec23ec0fcf0,0x71fb47e1a3e414e00a70047d829c014e00a70047dc29c010c60,0x240c11fc090c0485824041216090133958257212b9195c04ae0240412b8090134ae0242c0e8b3,0x11fd090b04864242c0e5569ad04d6866b2135909ac84d64242c0ef10,0x12210915848a024500e5f29ad84d6426b2136309ac84d6424500ef01,0x913848a824501228072d848b8245e12240a4d852682934149a0914054242934105f6,0x921048f425701241095c04905a57012b8074484ae0248212b80920b4ae025700e890,0x92d048f8257012bb090104ae024ac0e8899af04d6424a41359092b04e20242c0eef0,0x87b143d825381255a94e3495525421240095e04a09a578d2820740250f4242a91272893850ec2530143b094c3516024780fcd0,0x12be092084ae025700e84695f04904257012b80742351e82568147a095c051e825700ffb0,0x49c924e45272073e04af825700e8e095f34ae025d0124207473523c2570148f095f0523c257cd0380,0x4adc21f092ba095c04ae01cf490f2a96e0488da1e492dc691184ba8248611380877252cc23ec149a0960052682580d05d0,0x1ce070fa587d1cae025bc126c692bb4b79a4d81257097584910228e31470a6604ae0243014cc096685330259ad08e0,0x1c620e304736a43ec61f210f9095c038c861f670f9087c84ae0256e0e323970043d1a4f8ce330970343d024f812ec0922838cda29490ef48a88537c21e0122008a4143e86a043148087d1d408e1f214d8087c84b4021f214d8087c84b419c6810a70,0x1cf0d2e508f804b6da56212ed09230539023ec14e009698538025b4d0c40,0x39ba657012e5093634b79a57012ee0923853ac257014eb096b853ac25bcd0e10,0x1cd212e50958b4b95a56212ef0924053f423ec14f70970853dc25c2d0e70,0x492426b2135909ac84d641dd8135909ac84d6426b20eec0,0x1d40124b09ac84cec26b2136b077584d65a676136b69acb4f08242c0eeb6,0x134409a21493026b2135f09ac83ba066be535929ac94f7c24500ee83,0x4934220a335909ac83b84620b335989acc4ff0a3ec0ee19,0x440424a00ed41a1f048986250543b0a1d85164266a0fcb8,0x9b08494826b21359077104d8424a4135909ac83b8828f4147a09ac851e826b20ffa3,0x9a183b6426781359099c849602902d48169ac848642902d0016,0x1da0136e09a684964287673520a421c7d828766fbf9,0x134719a384d0c1d92135909b804d6424b4148f0a4784d64291e10379,0x4d5026b8135909ac83b1c66cc137109ba8496c293c149a0a5c848a02934105c8,0x4d5826b2135909ae83b1826ce1376087904970293474c108fb043b8293470549,0x4d6426b20ec209ac84d641d84137709bb84974298a13590a6284d64298a10896,0x3abc620e3359093004530a9a6535909158534ca9a650952,0x7570c42066b2135909aa04984229c94d809ac8536029b010a68]
def a1Marks186 : Array Nat := #[0x75f84d80267a1374093105388266e14e00a850486c29c010c23,0x3ae826c21359076184cfc26ee13590931853ac26b214eb09b0853ac26ee10e00,0x3aa866b2134609ac84d1024c814eb29ac853aca9d650dd3,0x3ae026ae136509bd8499429d0d1f60a7035381a6f010bb9,0x75984d6426b2133909be0499829d6d3590a75b487029d6d0df6,0xea719ac84d6026b213450933853d9a46415031a75c542c29d710d89,0x3a94220c110609ac84418220c135909ab0441026aa110808840b8d42204134b0885049a022a474f0391b0452d220e150408a59441c6a083144088305360e20c10ef088305360e20c109e9,0xe9e09ab84d3424d214fd08fb053c669e330e39,0x77d84e20271013a009c1049b829d6d388096f053ada73610de6,0x111209d2049c0222213b0078f050fc23e811292a1d850ec275a0fc82,0x1e5013b619db04f2427680f3009e104f0824ea148f09df0523c278410313,0x1e6813d009e804f3c22321116093b853f423ec15062a8324518221e10963,0x3d2c27ac13d609c3249e829fa11f60a838543429d750d6a,0x22360f36488e84f7c223a53df09ef04468220493e2087a049f422ac14d809ef843c029b010a46,0x2698928009f683df4288611f40a1d850ec27d40fc96,0x4a18289011f40a1d850ec1f84144808fa050ec28760fc20,0x512026a493f367db35131a53e143b0a42050ec27da10110,0x14120a08044902248344109d4a3eb0a540144119d49522427a00fac4,0x5120277893b929dc83e782876143b09508523c2876102f4,0xa0d850f02830143b0a1d83e7028a61453695105368246a10550,0x141e0a1d850702892143b07cd9515028a8d2a309d58537023ec10484,0x225c14470893050801e70912d2a25044b02258143b089685128a258112c0a1d8506c2207510349528454029bc11220a010453ca75e514f09d78447da23e10874,0x2890141c0787ad12ca87612a60a6e050ec276010884,0xa21050bc1f28d45009b7d5149a54e14f109eb0543027ded0834,0xa22850c01ea1343b09c2b5159a87612a80a7a84ffc27dc10864,0xa1d850ec1f20143b0a1d83e40255214fd08fb053f423ec10804,0x79a950fc2876112f0a1d85078255614fd09d68444caa0cb0814,0x3d31a886143b09c6d50ec26dc92ac0a7e84fa82a1ad0854,0x38f42890143b0a1d850ec2876143b0957053f42876108a4,0x3f6028d811f50a3684ac829c0145f0a88047dc29c010be0,0x13ba49dd14ee81fde147a0a47851e8257c148f0a47840cda91e147a095f0523c291e10336,0xf4e9a3d04e2da9d6147a09b084b5c29d614eb0860b53ac28f41361096b853ac29d610c16]
def a1Marks187 : Array Nat := #[0x1fd8147c0a7e847d825b414e06a70342cda9fa11f6096d05381a9c0d0b36,0xa44052242912148b080c04ead275653c10a7e847d8208a750f0a3c3543da8f012e70,0x13be49df14ef8291e148f081604ef9277c53be0a478523c2058148f0a478523c291e12e80,0x523c291e148f081584efd277e53bf0a7e847d8207415110a4905445a92412e90,0xa4685240291e148f080d24f05278053c00a7e848d4207615120a4d05449a93412ea0,0x79ca44d4691e11353a4785234222893c74a7e8500c278653c3081e8536029b012ec0,0x7f734f1129fa145f09e214f10207c15100a7005445a9c012ed0,0x1ea3348f09e3253f4290213c629e284100271ed4eb0a4784dc029d612ee0,0x3908291e148f0a47853f4291e13c949e494f242082148f0a7e8523c29fa12f00,0xa488524c29241492080da52682934149a0a4d05248205a15160a8e05459aa38d2f10,0x292a149c0a4d052682934149a080ea52702934149a0a4d05268203a951d0a8e85475aa3ad2f20,0x14960a4b0d268293a149a080e152746934349a1a56852482038951e0a8f0d479aa3cf2f30,0x293e149a0a4d03e88e93e149a0a4d03e88e98c14c50a6285268298a149a0810a54d42a6ad2f50,0x1139089b03cf12274149f0a4d03e8c6274549f2a4d05288292a0fa338a2a536429b0149a0a6c0527c29b0149f2813a550c2a86d2f70,0xff06a518538429c614940a700538020469554091835471aad0d2f80,0x3f52a94814e60a728526829ca14e5081224cbdaabc151d6a4d055b9a45e12f90,0x3d4e693414a50a76053ac293414eb0a75840992720d5620a4d04dc42aded2fa0,0x3e342938149a07d00529c2992949a0a7f0524c299294c94810254dd2a6f52fb0,0xf3a2a4d044e429341496089d152a029b0349a0a7f84510a9b034d81811255106a88f2fd0,0x7a935268293054980a54853b5292815000a75a53ad204a9391aab1a52682ae0d2fe0,0x3cec227c113e0a56844f8227c14ad089bac4dce92e7141089f852c4228034b208a0052c8627c14d8389f052b429fe54ff48a2044f829b0713e080b9c46e6208d545388d9c4102a8b33010,0x7f8b52d429c014b40a700403e66e4d55608fb854b1aaced3020,0x7aa3d2e4297814eb2a5c853aca00773948a5c854c9aadf13030,0xf3f4a628455029b014c50a4f8536029b00fc638aa05360298a149f0a6c053601f8c73060,0x7adcd3ac298a14eb0a7583f28e9d614c50a75853ac1f9473926a6284ddc26ee13070,0x8ac044f929b014d807a2a4560227c94d80a6c03d1529b014d80a6c05360294413110,0x8aa83fc9a9de14ce07a12456469c011593a700528c2217555809f1b5509a1fe13130,0x114247ae4d3d829a60f444a5d153ac22b674d80a75852942218d39668ad1d36027c213140,0x8a1a52fd1d2554f60a6c03d1929b014f60a6c053d8294c112069fcb536027c413150,0xf4028aa04550228894d808ac0c56029f214c908ac0c50129608f4048ac04500a960550808aa04550228854d818aa05414e2a814d8089d252a062a8150538aa05360627454a807e81c471e238d15b988e0c47022b673160,0x3d59a28894d80a7e8533c1e8694eb4a75a52a4221b539eaa6c044292ae953170,0x399022b0115808a22536022b014f908ac05360227e91414a58a3d1d22b011580a6c0456022b014f908ac0456029b0115808ac053e42276513b0a55044cda264d4746899844c828e813190]
def a1Marks188 : Array Nat := #[0x14e00a7003fd9a9c014e007fb3556c23ee155b08fb8559daaced31a0,0x7f0b539029c00ff76aad84b4c2aced4e00ab5351b42af2131b0,0x3dea69d014e007fc35380296a155b09bc35574ead6d31c0,0x1eb334eb0a7003fe5a9c0155b09cd353802ad8d31d0,0x1fe614f70a4903fcdaaa6146e6aa9b51b82af4131e0,0x7ab9d3f429680ff56a700541ceaac14e009bdb4e5c2ac2d31f0,0x7248538029fa14e007fe3538029c0155b0a70053802adad3210,0x14eb0a7583d7e69d614eb07afcd3ac29d6139b69cdb53ac29d613220,0x3d69e9ec14e507ad4d3ac297654bb0a7594e722738d5736a75855cda9d653230,0x297c8e91aa7b053ac1ec134eb0a5e153ac29ec13fa69ceb53ac29ec13240,0x3d78e9fa14cc07af4c56969d614eb68ad1d3ac2730d37c69cc053ada6f813250,0x3d6069fa14d007ac4d3ac29d714eb09ccb4e64a9d713260,0xe4c0a75853f429d60f619a75853ac29fa14eb09d0353ac29fa13280,0x10f50879a43d861ec70ff087fb56146b0a71570,0x1100088084404620611090885856182b0c31539,0x448c222a912418921c4c42262d1444,0x1116089285608e24a358408931c4d0e2b8115c6,0x4460a25a111848968c4bce2ba115d6,0x43c4225c1584488ca44c06b0611303ac0b457c2b02115f6,0x1c8e6e4437238b9105c8e0e440726538e29c990e388726338e19c988e384726138e09c980e380721038dc1c8c91c248b00562c1c6c1160072314708a2c0158b071b045801c8c11c208b00562c1c6c1160071fb469da2c0158b071b045801c7e11a708b00562c1c6c11600,0x3a08dcfa6e82173e8ba081cfa0e87a73553a1e1cd50e87673533a1d1cd48e87273513a1c1cd40e7b08b5345a82b100e690740a47151ca091614740947149ca051612740847141ca01161073c3469da2d0158b0734845a01cf011a708b40562c1cd211680,0x1dd20ecb076b0bb285dac0eca07738baa45dce0ea9077283a8422e40ee017530bb801d4c0ede08bb83a781d900e6a076a8c7291cb03162176a847289cb0116207680470822ea158b074f045d41d8011aa6728845841d7011a708ba8562c1d3c11750,0x79083c541e3e0f1408bf03c6023000f13079033ab69e3aceac878e33a919e400ead478e83ab09e380ea40789039b01e3e11cd171c845801e2e11cc27308458c1e2c11c208bf8562c1e0a117f0786346a59d2ed1706786046a41d2e11700,0x7a283cf01e802f3a17a003ce81e88eeaea7a233aba1e86cea567a20bab91e880eae27a183a941e720e6d07a08c73d1c74116007a08473c9c741160079f047101e06117d079bb46a19df0d179679b846a01df011790,0x1eb84f5327ae03d4c1eac0f5207af83aea9eb44eaa87ad03aa99ebc0eb347ac13a9c9eb00ea707a8839b81eba11d7471d845801eaa51c8274a145bc9eaa11c8074a045bc1e9e11ac671d845801e9a11a708c70562c1e96118e0,0x3df89ee84f7e07ba03dd81ee60f81075e53dec9d570f7b0755b3dfc1d68917347bc93aa09ef20ea807b9039bc1efe11d9471e045801eea51cb274c145c09eea11cb074c045c01ee011ac6733845941edc11a708c80562c1ed411900,0x7e313e889f8c0fa207d903e7c1f94cec2a7df43ac21f7cceb067e503b091f7c4eb027df03ac01f3a0e7107e78479c1c7a116007da1473c9e12517f27da0473c1e12117f07cbb46b19ed8d19067cb846b01ed811900,0x3f70dfb46fdc17ed0bf701fb40fe3475ed3f8c9d7b0fe3075eb3f811d6e8fe0275b93f801d6e0fd9073a8459c1fbe91d7474da45c51fbe51d7274d945c49fbe11d7074d845c41fb211b2071f045801fae11a708d10562c1fac11a20,0x7f91bfc0dfe42ff017f903fc01ff28ebfa7fc93afe1ff20ebf67faa47651d70917547fa947649d70517527fa847641d70117507f7046c81cf0116807f60469c234e158b07f60469c234e158b07faa47651d70917547fa947649d70517527fa847641d70117507f7046c81cf0116807f60469c234e158b07f60469c234e158b0,0x80914020a024100808048401c20280ec5a80813b0620200ec1680a8479c1d88917548069477c9e4a518228068477c1e4a11820803046c81f08d1926809847ad9d88900c275c940301d721006073c845a5a00811ac07f6846b0234e158b0,0x204e101d08110c0706044101c08148479c1e22917f48148479c1e22517f2814047901e56118908c285624204ceec7a81333b1e204acec6680cb46c59fd2d1a568130bb1d204c0ec7281283b18203211b107f48469420340e7a0,0x103038169c0c0605a30300816840e423ce0f2d48c4a46192b12903908f383cb4a31251862ac4940e423ce0f2d08c4846182b121036a764540da1d9110366764340ac23640fee68d90469dab1610364764240d89d9050360764040ac23640fee08d90469c2b16102b073d845a9a2d415880]
def a1Marks189 : Array Nat := #[0x207a703b381e8c0ec607a103b081e247092366158b081d046cc207851c228d98562c207411b3081e047082366158b081d046cc20814ec9a82043b262080cec9681fb47559c861160082023b2520804ec9282003b24207e11d507218458020580e7c0,0x105728231415c208c104908db946dc2b141045082b0470d236c158c081d846cc209051c228da8562c208a11b5082404708236a158b0822846d420b6cecba829c3b2a20a6ceca6828b47599cb8d162682d83b2d20a64eca282983b2820a211d6072e04588205a0e7d0,0x41c82098706818238c1a0208e106718e4a410c6368306708e49410c2368106508e1046e82b16106408dd041c45da550710769441c01d9ad1746838047659c8a116008370bb4520dc0ed1283603b3020d411d5074e045c4205c0e7e0,0x84384154e10231cd18240c6d4610211cd0824046d4210011c208e10562c210011c208e10562c210231cd18240c6d4610211cd0824046d4210011c208e10562c210011c208e10562c210ceed4a84333b52210ad1d96768345d5a10ad1d96768345d5a10c2ed4484303b50a10a11d90768045d4210a11d90768045d4205e0e800,0x10a808f18418d237290a028f40c15ce12c11cd0840947342384558b0850047a0e0ae309608e684204239a11c20ac584258209211b728db85628214acee9a84fb47819eccd18f684e43b5a2138ced6685283ba5213e11e007b30463c21384ed6284e03b5820600e820,0x42c823ce105818da8c288e0b270ac08e8041f4a37e50a118f4ac160615411cf08410473c2384158b084b8412c2162ceeaa8583477d9f0cd1936857b3b62215cced7685883ba9216011df07c30464c215e0ed8285703b5c20640e830,0x85c2475d20d291ba484c9c134e17051d72834946e8a132304d185c0475c20d211ba084c8413421828ee2a8630479c1c921160086093b8a21820ee2685ca3b69216c11d507ee8468821724eda285c83b6820660e840,0x432d23b2907748de24268e0a070cb28ec941dca378509a18280c32c23b2107708de0426820a010cc4771d433423ce0e8508b4043309dc710cc0771b432d1db890c908ea83fd023aa11a70ac58432c9db850cb076e040d023d8ce850,0x8690c76c60f291bd48519c168e1a411db083c946f4a136305218670475c210811d708e10562c21361052086a0bb9aa1aa11e70772345d5a1a80ee68869847a8ddc8d0d1176fa433c23b20fe808d2043441dbe50cf076e845d8206a0e860,0x10da18f00c1ed237c90a5382d9c36823c0107b28df1427060a630d608ec8421423b211c20ac58427020a610dc1773d438823ce0f0068bdb43701dcf10db0772b435c5dc090d608ec83fd423b211a70ac58435c1dc050d6076f045dc206c0e870,0x8730479c20e691ba48531c170e1ca51de283f14700a14c305c18728477820fc11c0084f0415021c14eeca8730479c1ef8d190686ec3ba221bacee8686fa3bad21c811dd07f58469821b04ee1286c03b84206e0e880,0x8742478920fe91c1487414788a0fe51c128539c174e1d011e2083f84704214e305d18538417421d211e707f234689a1c34eefa870c3bbe21c2ceef68748479c1fc811a20870a3bbd21c24eef287083bbc20700e890,0x21d411e708452479c2384958b08750479c211451e708e11562c2152706038750479c211411e708e10562c2152306018548418021d411e707fe3479c234ed58b087153bcaa1c50ef2887133bc9a1d411e707fe0479c234e158b087123bc921c44ef2287103bc820720e8c0,0x11ee68f7056341c7a11600a12947d02bfa11f40a12847d02bfa11f40a06347d02bfa11f40a06047d02bfa11f40a03847d02bfa11f40,0x1c7a0e3d171e9b92423e0d1f00ac703925a98a91f60b07047d8298a51f60b07047d8298a11f60b07047d828f4d1f60b07047d828f411f60b07047d81c9e11e70,0x392422c011f50a9a247dc2c3411f70aa4047dc2c3411f70a9a147dc2c3411f70a9a047dc2c3411f70a3d847dc2c3411f70,0x8768484063fc321008ff0483c23fa121a0902056502404120208fe05644259692030ae1047c0259652031ae10c7c0259412020ae084808256812020ae08480823f415910920848082b8212020,0x1ca410ef0877039485ca6121c072a04871a404d2020ac883951a98e92170b07847d8298e52171b078c7d8298a12160b070485828f4d2160b070485828f412160b07048581cae11e63,0x1cb20e5a072d13974244612220acb83978299092290b08047d8298a52280b07048a0298a12280b07048a028fcd22c0b0a047d828f412280b07048a01cc011e5a,0x248e923e4923948f8a48e123e0966a4809259a5202296684808256812410ae084904247a159b0920849042b821241092085704259a9202496694808a59a1202095a049042b821241091e8566c248212410ae084904248215c10,0x9320c93064c8124c093184950249212ce49110cb38a44412ca09290570424a412b409290570424a412490acf0494c24a41252091f0567824d612020,0x10f207358499c649a3267092684998249612cfa9118cb3e244612ca692b05705a4ac12b5692c0570da404d1fd0ac884dcc24ae15eb092b04958247c159e099c849b02bdc12026,0x43d4252e524f894b8493da52f124f294bb493c251cd28e0ad8048fda47e159a0946049fda518d27f0738845a0284e52142a13848502818d28b0afe84a2c247e15ad0a0604a2c2bfa128b091fb56b5a810123b0,0x25345290294d04a402558129b0add8496524a2959d495414940a5501250097284a7823e011ee0968949c4a5a21271095b04a7c2b8812810940056a425321201487b943dc253012980920056e0255e123a0,0x96ba494925ae5252296b84948256812b40ae084ad0256815c1096ba494925ae5252296b84948256812b40ae084ad0256815c1095a04ad0248215c1095a04ad0248215c10,0x1ce210f937388c3e461f20e71396f2495aa5bc5256896f049599d0812dea92b24b7a24ac52de692b04af9a57c15c60920b49042b360e846a6624859299852162a660485828f4d2b80b0704ae0248215c10a3d04ae02c1c12b80920b57059d1211e10,0x739839cc5ce672e5093a249cd25ca1274293994b9424e81273074684bb924b492ee292d14bb824b412e8095f05718257c12b40ae083a3c22d8d2be095f049042b8212be095f049082b8c0e900,0x4b04a58215c0096624afc259452c00ae084b00259412c00ae084b0025fc125c497d1496ca5f4125b097c84b542bb4122409110565c21f810ed4a8c04b102c2e11f0096004b00248615c80,0x21f872d2187ea4b0925a410fd296114b9965cc72cd096684b282b82130e192fa4c3824be530d096b8577024da126b0ad004c3424bc12530acf843f86a7030fe0a9c04b34259a12410ae08486824081594096684b34248815d30,0x12e30961a4b4025a012ca2ae084b4025a012ca0ae084b04a58215c0098b849a1262a12d90aef049f424f615a7098a14984a628126109690487825cc32e6396804b40248a15d50,0x4b59258a8e8408b4043fce5ac52c5287f8cb58258a10ff098ea4989263612d40aec84ac8256015bf098e94988a63a12620a9ca486d2a9612d408fb847c02a72521b2a9c8486c28f612d30b0d04b4c248c15d80,0x12d9196324b64258c52d7096b84b282b821323193224c8825ae15dc096b84ad02b821323093214c8824c61254096b84b5c248215c1096b84b5c248e15dc0]
def a1Marks190 : Array Nat := #[0x25ba92c7496e94b1ca5ba12c7098fd49952642d2e50af1847c9a3e0158e098fc4994a63ed2650ab384b6c2c3c11f0096d04b68248cd5d86,0x4b80659092e0096414b7825bc12ca0ae084c9924ce932869728578c24dc126b0ad004c98a4ce53250933054e925bc12de0920857042a74521c096f04b78248ed5dc6,0x25c492c9497114b24a5c412c9099584b942bc612b30958056fc264e926a4993949a8a64e126a0abc04b9423f211f00a9da48752a76521d2a9d8487428fa12e10b1084b84249015df0,0x3a7c1d3e2ea2075134cec2676134f099e357a81d46134f699e057a9a676133b09a1b4d0c2be80ea36,0x2674134a09a48493c249c159c0758045d4285052250a1284d202bfa13480a0734850281813480afe84d20281213340,0x22060ec208ba84d4426a6134c092a849442b3a14315913250c4e44c540f39a9847d0e82732150a061cd482bfa73520,0x758044181d602ec2099d83b6826ee1361092b049482b3c0ee20a69a48a069a652280a6284d642c1c13590a40b485828f413590b0704d641dd811dc9,0x1d620ebb07588cd00267c0ef409a224d8426c2134429b8049501dea136109b084d8426c20ef60,0x76d045d42212136909a704da82a7c922d1aa484ce02a7c522d0a9a04d902c3413640a3d84d902c3413640,0x2214137119bb84ddc26e20ef708bc04d08268215e909be05502a6ee13770aa044ddc26ee121c6,0x771045d42216137909b904db4267ad53fa9180d535a6f211f76a9fc48c02a68d3780b0d34de02904d21b6,0x77d044341df4310c188603bf42714338a09a0b4cf99dfc139919a2a4e64268a5398099c84e3c24d8126b0ad003bfc29ac92324a6b148c8a99813590a40b4ae024d615c10a3d04e202c1c138809c1057b81e0211da9,0x273a3394177e045e8273a139409cd84e6c272415ee078104e886736139b09c5857b82744134269a034e6c273613820af704b5da4dc15dc6,0x9d3049bda4de15a1088804eb0274e15f10784845fc285452340a1284e942bfa13a50a06b4cd1a81a13340a0384e942bfa13a50,0x3c2422260f0e09d704eac275e0f0f078d849c5a4e215a2078db5360675c11f60a6b948d4298a13ad0b0704eb42900d3356a4004cd41e4411cf5,0x1e4c0f2619e484ed9276a35f219e484ed8a76a15f207960461c277c13be09dd357d01e5c13be09df04ee82be8127369398568c1e5cd3be09df04ed02be80f2f0,0x1e4e111407938cf0c678033c309e003ca4230813c569a1b3cc8278a1343093a349d02b480f326a6c0c8d469b012350a6284f082c1c13c209da057d02902d3596a4084d641e6611ce3,0x1e6a13ce19e7057d81e6a311819e88446027a22f38088033d08220010f3093b349d82b4a0f426a6e24f4823ec14dc29e90c7d8222e14cb088704e8c28fed3816a3f84e041e8a11cd3,0x7a603d401ea0536ca9a854f68a7b40f57093c849e02b4c0f590a7424f5c23ec14d12999953442666148469ec047d828f413d60b0704f581ebe11d9a,0x3d9022384f65088e03d949ece134b49f094f8424f8127b0ad383da029d292364a6994d64a9a613590a433488028f413df0b0704f7c1ed211d8a,0x223c13e729f3849fc24fc15a809f204fa027cc15f707b604640285253342a1484cd0281ed23b0a0604f942bfa13e50a0384f942bfa13e50,0xf6c07b88447c1ee25351a7bc04fac269a93ee29f704a08250215a907bd053ad27d611f60a6a94cd4a9aa13350a42348f028f413ea0b0704fa81f0011d7a,0x89184a15a50a15ab0a1694e94a85a13a50a07b4f95a81e13e50a038501c2bfa14070a03857f41f20119c0a1694e94a85a13a50a07b4f95a81e13e50a038501c2bfa14070a03857f41f20119c0,0xa1c94ec8a87213b20a0b84fc5a7e4d5f8694634a282b5c140f0a07850302bfa140f0a078501c2bfa13e809f3057dc1f2e11ac0,0x512023e8144009d40d051a7d2f41409f48ca35a51a15af0a0a84f301f30119c1,0x144809dc14edcabe6544809dc04edc2be614170a0b85031abfa14170a0b850302bfa128e6947056c0282e14170a03857f41f3a11b20,0xa0d150682bf814252a0c857f4283214250a0c857f42832144d0a1a35800244ad44d6a1a05801a44a128f6947856c42932142c0b06848d01f3e11b50,0x284c541d0aff05060284a141c0afe85070289c14356b0084899e89cd4350b00b48986520d2900ad905284674814a11a16847d01f4411b51,0x50ac285614252afe850ac285614250afe85068a83415fc0a1d34f71a87413dc087a84a49a52415b40895850b822421401089514e98a25413a6088f344781f6411cd0,0xa1705090a85a142d0a12857f42254143969fb350e427ec12936949856d4285a142d0a03857f429b613ac09d3857c41f6811cf0,0x14362a10950d82842144808fa05145a86615ff6a0504a59a52815b60a1c04f501f7211d10,0x143a0a11150dc286e14250afe851202708d3836af6350dc286e140c0afe85155a6941349094bb4a542b6e143909ff04f9c1f7c11d90]
def a1Marks191 : Array Nat := #[0x3e40287e541c27cc050fc2838112c07cc1510da6a54fb90a2184d492530d2980adc03ee5a9fa144808fb047d029b853ad2a6e04eb42908d3ea6a4204fa81f8411c24,0x11300a2384494a83e543f0a1f850942bfa112d0a2515115a7baf1018a2284f74620250f6094d34a682b74144809d704e9429ba51122a2594eb81f8c11cd1,0xa229508ca88a14230a2404e3aa70f55edaa218510c281815fd0a2b45159a538d29b0add8512027d613e50a2634fac1f9411d94,0x14480a2405094abfa14480a24050942bfa14480a2405031abfa14480a24050302bfa129e694f056f4289014480a03857f41f9e11e70,0x1f72119c08988502c2ab611f70aa804f642a8e53b12aa384ec4290a13ec0,0x3e4c1f262f933a3524db6a8d4536d8a3504db59fba1460095884ac02b7e0fe10a7424cdd29d053372a7404cdc291e146008fb047d428f4145f0b070517c1fc411d56,0xa33251891fba11a20a3315188a8cc14620a38051942c08145d0aa6a4ce12a9014640b0d0519028ba16030aa694ce0aa9a13380a3d851902c3414640,0x7ca03e505f286ff30a75a4d6529d653592a7584d64291e12b8095a0570428f4147a0b07051e828f4160e07fb04745a9d693594a7594d64a9d613590a4784ae0256815c10a3d051e82c1c147a0a3d058381fec11d16,0x3e581f2c2f9937ff053d866fc94f609bf153ac278413bb0afa0523c2710d38c6af733ffc238d350b7a85b4dac269e15ea095db4ad42b8614810a40851e82c1c10000,0x3e5c1f342f9a3805853f426b293534a7a94ecca9ea13b30a4784fd1a7ead5f96807046eaaa1ad353495e34ad82b8814840a42051e82c1c100f0,0x3e6c2914348a0b0383e6c5f3874fd09d6a4ea929fa13ad29d5153e8278413bd0afa04074236a748c6a3bb51d9ac0cd0230a46051dc28ec1606095eb4af42b8a10236,0x1f3a0f9d17ce9d3f4278493be4afa253f4278453be2afa153f4278413be0afa040b02366148f0a47851e9ac1c10330a478523c28f4160e095f34af82b8c10336,0x1f3c0f9e17cf1d3152924160e0a4905314a924160e0a49053142924160e0a49040b0236415150a723587823ec103e0a8ab53902c3cd1f6095fb4afc2b8e103e6,0xf9f07d10d27ca93e160807d11d325293816110a4905314a934160e0a4d053142934160e0a4d04075235e951d0a72b587c2450d04d0a8eb53942c3ed228096034b002b90104d6,0x1f1c0fa41a50152802c120fa43a7f052702c22149c0a63152702c22149c0a63052702c22149c080fa46c129ccd22a6827053982454104e6,0xfa1089d844dc1e7a94a80a4b0d288293e16080a4f83e94e33674ca4a5005848693e149f0a4f8527c292a1608080f25295a6a8d52108308529426a815216960b4b042b9210616,0x7d3044f8226c6fa61a580d2bc2c1414b00a578d8285f4e74c94a5705844293434c92a570d844693414c50a5685838295a101638d69cd55aa4614e76b10048d9a0c413550a91b539c2c40d2360961b4b0c2b9610626,0x3ea01f502fb63a692525069a454940a62852d02c1c14b408074c6b26a4c13576a93053ada3ec10690a96353902c3cd3370963b4b142b9a106f0,0x3ea422840faa1a4c0d2e81f6e74d44a4a0d34ca93414c50a5c8583829721002b8d5dcd61a9d6d232683d054c5a97616196a98353942c3ed359096434b182b9c107c0,0x7d6045101f5834d81a4d0d360293414c50a6285838298a14c50b0703f08e33874d81a4d0d360293414c50a6285838298a14c50b0703f08e33874eb69acb53ada6b2d0830a7584d6429d61359096534b282ba010836,0x1f5a11450a650d3282c180fad1a6c0d2b529b014ad27c79c660e9feb49d4a7f9d274a9fc74c90b089d324298a160e07e19c674e9dad37f6a804cd75a11614ed09bf85400e6ba10f8096634b302ba4108b6,0x1f5c114a089c1beb8629234df189e252ad229214df089e152ac9f14719638a40d409629015023a6605330298a160e07e21d4e86a7414eb69c9b4e21abdcd37369af357ada11a153a7a9d353ac272613880af704dcc26bc15eb0966b4b342ba6108d6,0x7d7845381f70314d0a780c4f5295894d80a5c93e1ee329714b0a821d278a9a614d30a62858381f8a7105aa7b34df5aa0670930aa0353ac27be135f0967b4b382ba810940,0x7d90456029f2113e4a56a3d15231a91542a828d36029b014c52b0703f1862a815053a6c05360298a160e0a4f9527c2c100fc63883553d9a7bed0990883253d827be10f9096834b402baa10996,0x3ed029fa149a1a508bc8962feb4dd0a6f053089f8e35065a508d37029b814c50b070453c1f9074f569fbb42b429ea13f70968b4b442bac10ad6,0x3ee429d094b447fb3469da9d054b427dc8d3a029680fb93aab24de2aab614fd08fb847d82aac53788aab04de1a16615676a7205879a8be1510096d34b4c2bb010bd0,0xfba0a75a52dd1fc4d1a26a75952dc9f7434eb0a5b83ee8e9fa12d4095c05704216c156ca9ba255a9a9c8161e6a72051e82c1c156c89ba155b1a6e81511696db4b502bb210be6,0xfbb0a76a52dd1fab51a1aa75952e49f7834eb0a5c83ef0e9fa1330699635799a16e157069bb255b9a9ca161f6a72851e82c1c156f89ba955bda6ea1512696e34b542bb410bf6,0xfbd0a778d2e11f01319098aa9d3bc29704fbd1a74053a0298a160e07e49d58069fa137969acb55802a0e7379685c053ac28e21360096eb4b582bb610c06,0x1f7c14f61a5ca3d7e631d34f60a5c93ef869d614eb0a62858381f9474fd09cdb4e21abdcd0b90ab9bd3ac29d6147a0b07055cda6ee1361096f34b5c2bb810c16,0x1f7e14fd0a5a252d91dd95175aa7a1530c9f9634f40a618454c1f9675660a79053f427e0d3ea685d84d8929e61479096fb4b602bba10c26,0x3f0429fa14bd4a602582d1d27516eaa7b053d8298a560e07e60d3d829ec14c50b0703f30e9fa13fb69fc357e9a1781574aa7b053d828f4160e097034b642bbc10c36]
def a1Marks192 : Array Nat := #[0x1d1211680a7c253111f9a14f82a621455cdf9a34f80a620455c62ae0fcd3abc053f428ded45f6abaa4deaaaea537a8aba84de9a18815786a7e851bc28be1575a9bd255d626f4557569bd0544daa2616220970b4b842bbe10c46,0x7328459029f214f90a62a58381f9c14f90a7c85314ac1c1158389c9bf3869f214f90a628583822b0313918ac044e41f9c74fd0a3ab51cdac0ad0c50a7e851d428e616050971b4b8c2bc210c56,0x1c9e11600a7e853f4298a960e07e7853f429fa14c52b0703f3c69fa14fd0a62858381f9e74fd0a7e851e9ac1c10c60a7e853f428f4160e0972b4b942bc610c66,0x7a4853fca9fe161107a4954142a0a14b22a57958289fa234b20a57858282a0a15050a84154202c260fd1388ecc475e2111108686384474e23a31082884044d421f610c76,0x819846c82ab613cb49e5257d52ab614640a300580c2ab613cb29e5157d4aab613cb09e5057d42af214600a880544028f6161a0,0x826846d42a4055200b0a854d92a34161b0a8a055282a36161c0a8b854d0aa32161a0a8c854d02a32161a0a8c851842a98122d0,0xa90954842c2c15374a8b055b82a3a161f0a8e854d4aa3a161f0a8e854d42a3a161f0a8e84cc4265a15e70abd855782c4a122e0,0x834846e82a4e15250b0c054f52a2e35480a92058682a48153d2a8b854d02a48161a0a92051882a9613380,0x8af04264239a115f0aad045712a44954f0a9e04574aab835410aa0854d0ac34115d0aae1d5042a8215340b0d05480aa4016150884a518c2aa213e00,0xaa6a54912a9015480b0d055202a90161a0859847442a9a95244aa4055202c3415480aa405868216611d10aa695490aa9a55242aa6854902a9a15240aa5851902a9614640,0x55392a50954b0aa5855202c3410b608ea85538aa50554e0a940552c2a96147b0b0d051c028ca16040,0xaa78d4a52abe354d0aa6855202c3410b808eb84578ea9e15292aaf855342a9a15340b0d0549c2a4a16180aa7051c828cc13690,0xaa88d4a92a9c154e0aa405868217211d90aa8854a8aa9c154e0a9a058682a9c154e0a3d8586828ce136a0,0x55552a5695690aac858842a2810bd08e8b5554aa5655550a958556c23ee14680,0x2ab0352f4ab02556c2a4c1524086084765aab0152f2ab0155582aac15340b0d05574ea4c155b09d084e242bde146a0,0x556c2ab615344b0d0556c2ab615480b0d0431823ce155b0aad854d0ac34155b0aad854d02c34155b0aad851ec2c34146c0,0x55ad2a58956a0ab3858782ace156b2a96155ac2a58131b696d05761aada11f80,0x15740aba155bcaade161f0ab9855cc2a6455312b0c954c82a6216190ab9855cc2744538a2af814e88271415f00,0xb13047d82d38169c0b4e05a702d3814480,0x8fa047d063e871f70b13847ddad6816b40b5a05ad02d6814fd0,0x47d82d8016c00b6005b002d80155b0,0x23fe11ff190084839ac5c162b090e859782cbc365d0b2e858ac2cba12e43,0x90a04850642a121b0b158486dad6a16b51b5a05ad02d6814fc3,0x91284898244c522d0b19048c02d6c16b40b5a05ae82d6814fba,0x247e123f191f9c919acba16360b2e8597425c2165d0b1b059742cba12e10,0x249c124e1928849942cba165d0b1c84b7cec7213680,0x9278493c64aa12620b2eb597dac5612d89b43858e42d16137a0,0x2528164c0b1a84a51a570169c0b2485a702c92d4460,0x4a14251a328d3b2b858e1254ed6600b2204b292ca814570,0x94484a246512765d0b2e84b682cba165d096d059742cba147d0,0x94584a2c651672d30b31058d825a6d6b40b2e85ad02cbad4f70,0x251c128e19471cafc2cc4165d0976b59742cc415130]
def a1Marks193 : Array Nat := #[0x128f09480d9702520765d0b2e84af52cec1632097c35af42cc8151f0,0x10f70948843dc652232833b2e84a64ecf0163b0b1d04c31ab0e35870b2e858b82cde153b0,0x949049d92cba129a1b2e859702534767a0b2104c4dace215460,0x252812b8094a0ca50ecea165b098f05b002ce815590,0x4a5424f332951b2e84a6cecf0165d098fb59742cf015650,0x252c12b4094b0ca58ecfe1627098d35b102ce8d5690,0x4a5c24f072971b2e84a70ecfe163b098eb59742cf0d5750,0x2482129d094e8ca74ecfe165b099035b1c2cf615760,0x133a099d0ccf4267ad68609b105a19ad2213626,0x163709ac85a702d3814448,0x13590b1c04dbc2d3874389,0x134809a40cd4826c8163909bc05ad02d6814f19,0x2692135009a48cda826f614f29,0x9ac85b002d8015573,0x2694136c09a50cdb82d0a15669,0x9ac84dbc2d80d5509,0x2706138319c384e242c76139a0b2e85ad02d1614ee9,0x2708138609c20da2c271c168b09d085a2c2cf0d5646,0x2c78168e09d685a702d3814412,0x9d284ea0275213b10b1e84ec5ad6814dc5,0x9db84edc6d1e368f09df85a44279416910b1f04f29ad22148e3,0x13b809dc0cef02796163f09e5b5ad02d2214da3,0x13cc0b4984f30622a13cd09e98590027a6d4d83,0x9ea04f5427aa53d90b2084f6c2d6814eba,0x9ee04f7427ba53e00b2104f8c2d6814eaa,0x2c86169409f505a702d3814426,0x9f284fa427d253ec0b2204fbc2d6814e8a,0x59182d38169c0a1d85a702d38143b0,0x5a55a85ed64a0b4e05a702d2814840,0x5094ac96143b1,0xb4815a402830169c0b4e059302d38148f0,0x169b0b4e05a70282c16a00b50359342d66149a0]
def a1Marks194 : Array Nat := #[0xa0815a742d3814152b5085a85ac9c149a1,0x4f352d38169c0b4d85940225814d80,0x2752b69c0b2885a702d1c14dc0,0xa0635a7daca414e00,0x27ab369c0b44b5a702ca614eb0,0x501c282234113a2785950289ed4c54,0x279851240b4e05048acac14d81,0x27a8d68aab4e0595c28a0d4eb4,0x8fa05a702d38169c0b4e059642d3814fd0,0x287615344,0xa0505028681474640b2d851b82d6814e46,0x28be16a80b6005a9c2d8015530,0xa06050306818747b0b2e85ad02d6814e06b2e85ad02d6814e06,0x5038281c34133a4105a442d16d4cd9b430597c2d68150a6,0x140f0a0a0d050e90a16966a5a559802d68150c6,0x50542d5a14151a0b1da44293476ac6a8705ab02cc2150e6,0xa0b8505c682e76914b4895a44292416b40a8805ad02cc415106,0xa0c05060683076b40b5a05ad0291e16c40a8a05b11acc615146,0x14190a0e0dab8283876b70b5a05ad0291296c50a8c85b15acc815196,0x2808141d1b5785074ed6e16b70b5b8522d2a34151a6,0x283413ce4b5705078ed7036ae0a45254802cca15206,0x283e141f1b5805ac0684076b70b5b8dad0290e76c60a9105b19acce15226,0x14210a108d0bced6814849a9205b11acd2152b6,0x284414231a181dad02907752a0b5fb5b15acd4152f6,0x5094284a36b40b5a050eced6816b40a1d9d4d02cd815346,0x284c16b20a130d014ed6e76b40a1e1d4d82cdc15366,0x8938509c224e34271a001d6156b0a76b40a1e9da2dad0ed5390b4585a1c2cde15396,0x225014280a188cff6eb0c76b40a1f1d4f82ce0153f6,0x44b0285613d04b5a050fc6d6816ae0a1f9d5042ce215416,0xa1684eb5688036b40a209d51c2ce415476,0xa19051e9a86434323aa405b11ace815526,0x2866145f6a198d0ccecba154b0b6235ad02cea15536]
def a1Marks195 : Array Nat := #[0x2868145aaa1a8d0d4ed04d54c0b62b5ad02cec15546,0xa1b04faa686c36b40a211d5342cee15556,0x286e13d69a1b8dad02886768b6aa705ad02cf015566,0x50e026b354441a221d5402cf215576,0xa1d05ac5266556b40a228dad0288a76976aa885ad02cf415586,0x95c05118288c34463aac85b202cf615596,0x91b85ad0288e16b40a238dad0288e76ab6aad05aac2cfa155a6,0x8fb05ad0289016b40a240dad0289076b40aad85ad02cfe155b6,0x9e885adc27a256b02a250dac02d72144a38ac8557022b2d55c6,0xa4785a492d4e16922b49054502d80157a0,0xa4d05aec2d8216c20b6005b002a1c96d00,0x513428b6944e1b5e05138ed8a16c50b628543d2d0616d20,0x296816be0b6005b002a1876cf0,0x226214d809e9a5b002d8016bb0,0xb6005b0029c016c00b60053802d9e16cf0,0x28dcd6c00a7205b3c2d8016a80,0x13ef9b60053a02d8016be0,0x13db9b60053ac2d8016c00,0xa3d85b1c29c0d6a90,0x13d93a75b5b0028a0768c0,0x47dc2d8016c00a7e85b002d8016c00,0x514428d016c40a3e0514468a276746,0x28aa13da1b6284f68ed7e54561b5f85158ed1a568d0,0x8e69c6d4e39a31b518e6846d423b35175a8ecc45d623b2d17568eca45d523b2517528ec845d4236411680,0x48442410120d19038c834240e120c18fd8c83023f6120a0aca8564c2db011fa09058d7452b2416dc08f685638241615d12ac90db7063da158e0904857402b2216db08fd0564423f8159b0ac885b6c23f415910,0x248a724339228c90c648a124309222574d23f8959149221574ca3f8559129220574c23f81591091e8566c2b3616db091e8566c2b3616db09222574d23f8959149221574ca3f8559129220574c23f81591091e8566c2b3616db091e8566c2b3616db0,0x49a024b81261192d8c98424b612601aea248846b2e32600aea148842b2e125d0ae8056782db612490acf0497c63fc925f08ff149782b3e11fd09250568023fa15910,0x2524128f094a956dca49c559c294a856dc249c159c0949949bca526126f0945056b824fc15a80948947fca52211ff0944856b4247e15ad0acd05b64250e12380,0x955956e8a54655b22955856e8254615b2095284a88255c15e30ade847bc2b1c158d095315758a4e055a229530575824e015a20955056e4240a9590495214800a54812000944056f8247215990,0x25a072c039680cb0065a012c0096ba577124a4959e496b95770a4a4559e296b8577024a4159e0966a4809259a5202296684808256815c10920857042b3616db0,0x22cc12ec39751c59865d832ea197604ba822cc72f00af1849d52b4895a349780578c24ea55a42ad194bc02bc612750ad20568c22d612eb490324baca40c52eb090304ba02b8c12420ae30566c2db6116d0,0x12fd297994bf425e612f70ae4957242db412f2097d8574925e215c7097a95740ab9016db09790572025ea15d00ae405b6c25e415c8097e0482125ec5207297b0481c25e816230ae605b7c23e2158e0]
def a1Marks196 : Array Nat := #[0x4c3c25f8730b1aeb8cc012b94930b0aeb84c00ab94530a1af22cbd8661415e4397b04c202ba613050ae9857402db613091b120c83126121624090614c202ba612440ae98566c2db613080905056542b2616d80,0x13190af084c052b969316297e9cc442baa13062aea85740adb61316097e8cc442baa13060aea857402db61311097b85724ab9216da0987a4845262415d7090f85658261455e4190694c282bc8720d0,0x98e2576d260495cd49899cbe0e63855db298115734a62632f8198e0576c260415cd098984be02618920e498d8576423e4158e098614838a618120e0,0x9920d778660695ce498b9cbf8e64815de098195738a62832fa199105770260e15dc0ae805b6c262812fa098724841264415dc0923857702b3616db098714840a61a120f0,0x99525781260895cf499515780a60855cf298c1cbfce65415e009820573c263032ff198c04bfc265615e308f98563826209212498814848a62012120,0x4e782722139619c80ce582720117c09ce0d7c0668d539c0af804d1a2736133f6af4b4e5464629395091894e4c2672138c093605705ab4016db0,0x118309e384f04230633c679a3d4f19a68f118a09e30cd1d278c134729df049c82314d3c319198cf0c246613bb69a1b4eec2686118b0,0x28c674613a318d18468c614610a33a4d3928ce534e2a3384d3828cc93364a3314cd8a8cc13360a2f0580c28ba16030,0x46682954149708c62529c2c1896090b6f25244294416080a4a85820235c94a969ab55299a7bcd4a46b0b0489da37014a909ab2529827bc14a40b0b3489c291a12b70ae0357002db411b86,0x8ce05360e934719c1a6c0d26869b0149a08ce1d3aea6b354eb89acc53ada6b2d1d10a75a4d6529d653592a7584d64291e12b80ae0b57042db611d16,0x8cc853fca95c519e1a7f852b829b216123b090db792938119e3a80b4e02a9d9135c8a7634d71a3a4150109c0253b0a6b854ec09ae05240257411d26,0x55b12a5a95423a8e1d5b0aa5a55421a8e0d5b02a5a15420a8e0558526ca956d096d85765ab8216db0ab094d94aac213650,0x55c42a5c95443a8f1d5bcaa6055441a8f0d5bc2a6015430a8e8558d26ce95720997057a02bca16dd0ab114d98aac413660,0x15774a99a55dcaa6655463a8f9d5dc2a6615461a8f8d5182a3e15780a358580c2aca93684ab294da0aaca13680,0x12000ac7855f02400358f1902856402c5e162d0b70048482cda962c0b728589c2cda562c1b728d89c2cd8162b0b72058ac2c6c162b0b72058ac242615e23,0x2480159a09200d6686480759a3b37a58ad2cde562b2b37858ac2c6c16360b72058d82c6c16e409240577c2cde962b4b37958acacde162b0b1b058d82dc816360b1b05b90249015df0,0x9280567024a0359c192c856742ce096321b38158c82cd816390b72058e424d215dd9b1d058ec2c56126a0,0x128d09469594cac6e56530b1b84a582b6cd64a0b2184a602b8216490b24858d42dc4129d0,0x4a182b5616562b2714a802b5e36560b2704a80ab5e767f0b2c8589c2c4c16722b1e959c82c7a12a90ae8259542c54957d2abe859682c6812ad0,0x94c056b4253035ad194c1d6b4ecf096394b3c158e4acf01639096d05761acba165d0b1b05b9025c216210,0x4a842b6012a11ad80ca84eb60767f0b1fa58f92cfe163f2b1f159fc2c7e163e09748571c2cc416620b1b05b9025de16220,0x951056c4254635b21b32959942dc612a33ad91d9b92cc6166c2b3205b902cc8166c0b3205b902cc812e74ae2a55f82af896c90b3405ba42c4e12ff0,0x12a40ad9855f8e54835b31b398d5fd2ccc96730abf95998a50875aa3b402da00ecde166f0b3605b90255475b93ac00db306b0016cc0b37859bc2c6c16e40b17858b42dc013100,0x254a15b40b3e8599d24ee95a54b38859c42cd856e409558d6e86ce216710b3605b902cca56650b7184aaceb7476730b1885a006d0073180,0x254e15b60b3ba59a525b4d5c16b3b959a4a54e35b61b3b859a4254e75b63b67859d42c4e13200,0x12a80adb859e86cd4927a9ad34d9e82cd452a81adb8d9e02cf0166c0b7204ab0eb7676780b3c058d82dc813270,0x12480acd859f12cd692ad0ade059f0acd652ad1ade0d9f02cd612ad3ade1db582cfe16280b1385b352c6096cd2b1815b342c6013290,0x9c2857b0270a35ec19c6857b42d1a368d0b42b4e5c2bde165d6b1d85b90273e161d9,0x277215f309dc8d7cc678815f509e2357d5a790160d3,0x50442bfa16486b2405b84282235fd1,0x286415fd0b5185a64289e161a0,0xa058502c681674680b5385a9c28d2161e0]
def a1Marks197 : Array Nat := #[0x283615fc0ac185608279e95f64b5925abc2dd096ae0b57052212c0e96bc0a51858542d78d65c6b2e05b8c2946d6156,0x143b0afe850ec6bfa343b3afe9d3802c34165d6b2e85b9029c0d61a6,0x14060afd851246bfc36b83b5c0dba1289275fe3a708586c29c2d61b6,0xa29057fc28d216030a290d7fc68a475ff3b3ab59742dc815670,0xa298580028b896024a2a0d80468a876013b4205a042dcc15680,0x4b842b8214570a2b8d15cedac16aa0b5385b4d2d1096d32b4415b4c2d1015690,0xb6785b3c2aced61e6,0x55482c3416d16b6885ba82aa4d61a6,0x2c5216291b1505bac2c6016f00b780dbbc2dde167e3,0x16350b1a8d8d4edde16ef0b3d85bbc2dde167b0,0x2c6e16371b1c05bbc2cf336880,0x2c9016482b29359742dda16a20,0x16460b258d92cecd896a50,0x2c9216491b249d9d1adde16c70,0x2c98164c1b261d98c2dde16c80,0x164d0b270dbb82c9c76ef0b77859852de816ca0,0xabe8593c2afa364f1b229dbbc2caa76d71b6b85bbc2dd616cd0,0xb28059012dde16561b7785bb82cac76ce0,0x16520b2eb59486ca476d10,0x594c2c8336531b778595cedde16d30,0x16360b2c059606cb076d40,0x2d1216891b4505a302dde16c39,0x16900b480da482d24d6b33,0x2d34169c0b4f05bb02d3cd69c1,0x169c0b4f05a78ad4816c00,0x16990b4c8da64ed5216c40,0x5a6c2d2696f34b56a5aec2ddc16bb6,0x2d38169c1b4e1db002dde16c06,0x2d30169d1b79a5a74ed8216c16,0x2d3e16a70b4f8da7cedde16cf6,0x2d4016a64b508da84ede216d06,0x165d0b5105a886d4476d16]
def a1Marks198 : Array Nat := #[0x16a30b54b5b11ad4636a33,0x2d4816c00b7a85b01ad4836a43,0xada056c42b6a55a12ada856842b66558f2ad98563c2b5815980,0xaea9d720ebaa35c81aea857202ba695914ae995644aba615910,0x15af0b28059342b5e56512b1e159442c7815b80b6d8593cac52564f0b148591c2c6615bc0,0x56e02db216713b321d6e06db236711b320d9c42cc815b83b6c9d9bd2c56966f2b15959bc2c5615df0,0x2bbe16db0b6aa5b2d2daa56cb2b671db28edaa16cb0b670db286d9c16ca0,0xb2585b842c9656e12b2a05b902cb016e70,0xb2a05b882ca836e21b2a1db88ecf616ea0,0xb3d85b902d4a16e70b528db9c6d4a76e73,0xb7605bb0adde16f20,0xb7685bb46dda76f50,0xb7785bc82de436f23,0xb8795c24ae1e17090b8505c202e20d6fcab86c5bee2e1ad6fb6b8805bf12e1a56fb2b8685bec2e0e16f80b8885eb02dec17930b8595e94ae0057962b8585e942e0017960b82b5e75ae06d7996b8285e742e0617990,0xb8e25ea12e3097a24b8c9dc5cee3857a82b8c15e88ae3237171b8e05ea02e3017a20b8c85c5c2e3e96feab9005eb02dee17930b8f95bfa2e3e16fe6b8ea5bf52e3617a70b8905e6c2e3a56fd2b8e85bf42e2c16f90,0x16f80b971dcb0edf0372e1b960dcb82e5816f83b9855f052e5157b5ab9845f04ae5117b58b9835f042e50d7b56b7c85cc12f8357284bdaa5cc0af8317282bda95cc02f82d7280bda85cac2f74d7ba0c3f05c9c2f66d7b30c3c85be5ae5a97f54b91a5ec52e5a57f52b9195ec4ae5a17f50b9185ec42e54d7e76bdc862242e4e17b90bd9861f42e5417e70bdc862242e4e17b90bd9b61f5adf417ab0,0x16fb0ba305cf02df6373f1b9d8dcfc2e7616fc0ba28dcd46e8a17350ba205ccc2f8616fd0ba10dcd06e8417340ba085f242f8e17320b9d05ca02f6a17b40c3d05bf82e7c37f64b928dec86e7c17f62b9285ec82e7a17f30be3062242e6417c60b9c05fa1ae4817b10b9b85f9c2f8c18890b9905f182dfe17aa9,0xb8205d68afc257542bed95c182eb417e10baa05f6c2eaa17530b8315d6dafc4d739abe2d5d622e6d17586b9b35c302eb617e20b9ca5f152eb057362bac05cd82ea417290bdbb5edc30f8170c6bae060082fc617210bd705eb42eac57f82ba495f38aeac17f80ba485f382ea0d7e96ba735f55aea017e90ba705f542e1c17a34,0xb8385d94eec877071bb28dd906eca17640b839dda03004174a4be825f3d310c97680c0105d28afa057cf2c4315da03004174a0be805f3c310c17150bd005d9eae7557678b9d45d9dae74d7620bf585d79afd617e76c4485c582ece973a4bb395ce8aece173a0bb105fac2ebc17eb0bf3862242ec4172b0bdd35ee830fc17166,0x5c202ee4576b2b848ddc82ed6176d0bf795fbc3110176a0b849ddc42fe897ee0c4505da42fd8176c2bf995fb43112176a0bf685db02fe617ed0c4485da82fda17144bcf25dcdae7957708b9dc5dc1ae76d76f6c0305fedb11817266bd935c5c2ee6173c4bb815cecaee0173b0bb786019aff6188c6b9305ec82ec8172c0bddb5eec30fe17176,0x5c282efe18010bba25fc12e0297974bbe9600c6ee477790bfb85ddcafee17f32c4485c3c6efa18033bb90dde42fee17770bfb85fcc311217790bb685fbcafde18880b879ddf9ae8d577c6bffb5d35afa6d77b8b9fc5dedae7ed7190bbf05d192ef817ff0ba685f4c2ef6573f2bbd85cfc2eca172e0bdeb5ef4310217196,0x170c0bc125ff12eea97f14b89b5e71aef4776e3bc115ff0aeea57f12b860dde86edc37820bfe05dd42fe2177a0bb705c30ef0a980e4ba1d5f2aaf0c180f0c0105c882f5e17ae0bc296038ae8717ca8bc2860382e86d7ca6b8d05e0d2e8097810c0835fe83116d75d0bf285e0cae8057830ba005d983008172f0be035ef83104171e0,0xb8685e246ffe37764bf925c0a6f31377e3bb99de242ffe17762bf915c346ef637701bc385ff42ef017fd0bf9862242ef617700b881de2c6e8b578c0c0105d21af98d7cb6c42b5e2c2e8b178a0ba235c742f1038117ba125e1c2ffa175f0bfe85f9c311217880c08b5d08af0e17410be485f1c2ece17300be0b5efc3106171f6,0x5ca42f6c178d3b948ded86f1a378d0b949ded8f04c981aac131606a304c181a6b9785ef8304d581a4c1346068b04cd81a0c0fb607c312818186c0c0623c2e5ed7be6c2d2605930b458162c2d060583098d81e0c5086078303018930c26060783142181e0c0c3624dae6218000,0x17360be205e382e6c37c41b9c85f14305017400be4060b83058181a0c0c862402e8617ca0c2da605c70b658170c2c060ac3142182b0c26b60583098182b0c50860ac2e8e17fe9,0xba785f58308c58402ba885f60708c18400bc785d44afb078476c1555d5c2fc818470c1526071b03818920babb5f91b0ce18480c098604830ba58332c2e860cc309cd83a6c27060e82eb217f34,0x5d482fb217521bec8dd48efb278670c1aa60d1313898670c1a960d0b13858670c1a860d0313817630bf60614030a0184c6c5085d98300818500c28061303142181f6c0f862502eccd8046,0x2ea617da0baa0df6c70a858540c5005d50efb678594c298628830a218582c290628430a418580c290628430a417614bf5261ac30c0d8a40c0bb5db8300a186b6c3006291b02e18206c10062542edcd8056,0x17550bee05e4830cc17904c2aa5d2d2fa297912c340e17030b818582c5085d686fc237910c341e17030b818580c5086150b0a818a00bad1df84ef1d58646c1c35de83010178e4c32060e02f1a18226c110625c2ef4d8086,0xbab85f7830c298564bb035f9db0c258562bab8df7870c218560bab9df78f0e6982fac3a0619c302818130c39960be30e6182f6bc00602430ead85f0c51b612830d218256c11862602f08180d6,0x5d602fbe18641c2ba5d326fa538640c2b95d606fbe38620c31061603142175b3bf11e19c3062d8306c4db5e0c301818767c3106188309818a10c3b360b8305818266c12062642f0ad80e6,0xc0d8606c703678230c57062a43046d8bb0c56862ec315ad8650]
def a1Marks199 : Array Nat := #[0x18290c148e0a8305a18aa0c17862ec317618639,0x60ec307a383d3c24862b03092d8584,0xc1f060f8707c78b64c5b162d830a218bb0c34862ec315c18696,0x183f0c200e2e8308078bc0c5d862ec309e98be0c35062f9b15e186a6,0x5e3c308218364c5d86118717618ba0c231e1b43162186d6,0xc2186131b08638433c37062f5b16418726,0x308818379c220e2ec308e78b56c38862ec316618736,0xbd21de84ef4837a11bd205e842f535795abd4c5e562f52d7956bd4a5e552f5257952bd485e542f3e17940,0x2f7a77bb3bde8deec6f7a17bb0bdfa620d2f68987a4bdf9620caf68587a2bdf8620c2f68187a0bde25ec12f7857b02bde05ec02f70187d0bd9861f430f218c30,0x17dc0bed05f7e2f8917df6be235f7caf8857df0be205f642f6c187b6c3d863082fba57cd2bee85f342faed7d46beb85f502f3418770,0x602d300e97a60c3b86020f00a780b2c0396020700a380b0c0386020300a180c4be4260282fcc18870c0615f20b01817c80,0xbdb861ec304478203bdb8e1ec704438201c11060802f6e787b3c1226265303298904c1216264b03258902c1206264303218900be006209b04298154c1096054b04218150c0e8624c303018930c47863142f84188d0,0x17d80c20860fc2fb058448c14c6111b052d7de0c22160a4b08818290c1f0606c3122d8910c6205f79b08458322c21060c83078d8396c1e060e42fc018890,0xbf2061c130d897f90c44861b4f0d478702c3615f9070da386a1c38061b030da186a0bf21e1c5305a986f0c530612c313e18712c16961c4305a180d0,0xc0e06244303838911c0e1e244f16698aa4c59962a8b16618aa0c1286261b15a18ad0c5486320304e18a50,0x183d0c4e860f4b13a58430c4f062adb15618c70c21b6279b08a18a10,0xc248627830bc18a10c248e2787092789e3c60062e430e418a70,0x315618ab1c559e2c9b19618bf0,0x316e18b72c5c063283170d8bb0,0x18b80c5d862e0717078c10,0xc409e1fcf102387f1c40861fc310098784c40161e0b10018780,0x61f0318418973c4a9e1f0718438971c4a8e25c312a187c3c611e259311c98962c4716258311c18840,0xc4906310316278af3c490e310716238af1c58862bc312478c43c58262a1316058a82c58062a0313418c60,0xc560631c315838c71c561e31cf16818c90,0xc6506328719478cc0,0xc6686350f1a678cd1c6a0e34c71a818d30c669e35ab1a158d68c6846359b1a0d8ce0c6b2634131ac58d02c6b0634031a418cf0c74363a031e818ce6,0x18d10c7486370f1b678d11c748e37071b638dc0c6d86344f1d278deac6c5637a31b118de6c6c3635431d418de4c6c26378b1b058de0c6c0636831ae18eb6c75863d431aad8ea6,0x18d90c7606390f1c678d91c760e39071c638e40c7186364f1d878e6ac705639a31c118e66c703637431da18e64c7026398b1c058e60c700638831be18ee6c77063d831bad8ed6,0x18e10c778638471de38e13c779e39431e018f16c78863dc31cad8f06,0x31e418f21c791e3cc31f018f36,0x0]
def a1MarksA : Array (Array Nat) := #[a1Marks0,a1Marks1,a1Marks2,a1Marks3,a1Marks4,a1Marks5,a1Marks6,a1Marks7,a1Marks8,a1Marks9,a1Marks10,a1Marks11,a1Marks12,a1Marks13,a1Marks14,a1Marks15,a1Marks16,a1Marks17,a1Marks18,a1Marks19,a1Marks20,a1Marks21,a1Marks22,a1Marks23,a1Marks24,a1Marks25,a1Marks26,a1Marks27,a1Marks28,a1Marks29,a1Marks30,a1Marks31,a1Marks32,a1Marks33,a1Marks34,a1Marks35,a1Marks36,a1Marks37,a1Marks38,a1Marks39,a1Marks40,a1Marks41,a1Marks42,a1Marks43,a1Marks44,a1Marks45,a1Marks46,a1Marks47,a1Marks48,a1Marks49,a1Marks50,a1Marks51,a1Marks52,a1Marks53,a1Marks54,a1Marks55,a1Marks56,a1Marks57,a1Marks58,a1Marks59,a1Marks60,a1Marks61,a1Marks62,a1Marks63,a1Marks64,a1Marks65,a1Marks66,a1Marks67,a1Marks68,a1Marks69,a1Marks70,a1Marks71,a1Marks72,a1Marks73,a1Marks74,a1Marks75,a1Marks76,a1Marks77,a1Marks78,a1Marks79,a1Marks80,a1Marks81,a1Marks82,a1Marks83,a1Marks84,a1Marks85,a1Marks86,a1Marks87,a1Marks88,a1Marks89,a1Marks90,a1Marks91,a1Marks92,a1Marks93,a1Marks94,a1Marks95,a1Marks96,a1Marks97,a1Marks98,a1Marks99,a1Marks100,a1Marks101,a1Marks102,a1Marks103,a1Marks104,a1Marks105,a1Marks106,a1Marks107,a1Marks108,a1Marks109,a1Marks110,a1Marks111,a1Marks112,a1Marks113,a1Marks114,a1Marks115,a1Marks116,a1Marks117,a1Marks118,a1Marks119,a1Marks120,a1Marks121,a1Marks122,a1Marks123,a1Marks124,a1Marks125,a1Marks126,a1Marks127,a1Marks128,a1Marks129,a1Marks130,a1Marks131,a1Marks132,a1Marks133,a1Marks134,a1Marks135,a1Marks136,a1Marks137,a1Marks138,a1Marks139,a1Marks140,a1Marks141,a1Marks142,a1Marks143,a1Marks144,a1Marks145,a1Marks146,a1Marks147,a1Marks148,a1Marks149,a1Marks150,a1Marks151,a1Marks152,a1Marks153,a1Marks154,a1Marks155,a1Marks156,a1Marks157,a1Marks158,a1Marks159,a1Marks160,a1Marks161,a1Marks162,a1Marks163,a1Marks164,a1Marks165,a1Marks166,a1Marks167,a1Marks168,a1Marks169,a1Marks170,a1Marks171,a1Marks172,a1Marks173,a1Marks174,a1Marks175,a1Marks176,a1Marks177,a1Marks178,a1Marks179,a1Marks180,a1Marks181,a1Marks182,a1Marks183,a1Marks184,a1Marks185,a1Marks186,a1Marks187,a1Marks188,a1Marks189,a1Marks190,a1Marks191,a1Marks192,a1Marks193,a1Marks194,a1Marks195,a1Marks196,a1Marks197,a1Marks198,a1Marks199]
def a1Marks (i : Nat) := (a1MarksA[i/32]?.getD #[])[i%32]?.getD 0
def a1Chk := SixSigned.closedRow 9 8 4 17 a1Tags SixRowsData.a1RowAt a1Marks
def b0Tags0 : Array Nat := #[0x987654321043210,0x987321654043201,0x965874320143120,0x965320874143102,0x932871650443021,0x932650871443012,0x897645312042310,0x897312645042301,0x864975310242130,0x864310975242103,0x831972640542031,0x831640972542013,0x695847302141320,0x695302847141302,0x684957301241230,0x684301957241203,0x630952841741032,0x630841952741023,0x392817605440321,0x392605817440312,0x381927604540231,0x381604927540213,0x360925814740132,0x360814925740123,0x978564231034210,0x978231564034201,0x956784230134120,0x956230784134102,0x923781560434021,0x923560781434012,0x798546213032410,0x798213546032401]
def b0Tags1 : Array Nat := #[0x754986210332140,0x754210986332104,0x721983540632041,0x721540983632014,0x596748203131420,0x596203748131402,0x574968201331240,0x574201968331204,0x520963741831042,0x520741963831024,0x293718506430421,0x293506718430412,0x271938504630241,0x271504938630214,0x250936714830142,0x250714936830124,0x879465132024310,0x879132465024301,0x846795130224130,0x846130795224103,0x813792460524031,0x813460792524013,0x789456123023410,0x789123456023401,0x745896120323140,0x745120896323104,0x712893450623041,0x712450893623014,0x486759103221430,0x486103759221403,0x475869102321340,0x475102869321304]
def b0Tags2 : Array Nat := #[0x410863752921043,0x410752863921034,0x183729406520431,0x183406729520413,0x172839405620341,0x172405839620314,0x140836725920143,0x140725836920134,0x659487032114320,0x659032487114302,0x648597031214230,0x648031597214203,0x603592481714032,0x603481592714023,0x569478023113420,0x569023478113402,0x547698021313240,0x547021698313204,0x502693471813042,0x502471693813024,0x468579013212430,0x468013579212403,0x457689012312340,0x457012689312304,0x401683572912043,0x401572683912034,0x63529418710432,0x63418529710423,0x52639417810342,0x52417639810324,0x41638527910243,0x41527638910234]
def b0Tags3 : Array Nat := #[0x329187065404321,0x329065187404312,0x318297064504231,0x318064297504213,0x306295184704132,0x306184295704123,0x239178056403421,0x239056178403412,0x217398054603241,0x217054398603214,0x205396174803142,0x205174396803124,0x138279046502431,0x138046279502413,0x127389045602341,0x127045389602314,0x104386275902143,0x104275386902134,0x36259148701432,0x36148259701423,0x25369147801342,0x25147369801324,0x14368257901243,0x14257368901234]
def b0TagsA : Array (Array Nat) := #[b0Tags0,b0Tags1,b0Tags2,b0Tags3]
def b0Tags (i : Nat) := (b0TagsA[i/32]?.getD #[])[i%32]?.getD 0
def b0Marks0 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80,0x2000000,0x1e,0x1e,0x0,0x81,0x100,0x100,0x100,0x0,0x0,0x0,0x0,0x6040180,0x8000180,0x8040180,0x280,0x300,0xc000280,0x1a0,0x1a0,0x0]
def b0Marks1 : Array Nat := #[0x380,0x0,0x0,0x0,0x0,0x400,0x0,0x0,0x0,0x0,0x10000303,0x261,0x0,0x342,0x0,0x384,0x404,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x580,0x16000500012080480,0x0]
def b0Marks2 : Array Nat := #[0x70001ac00482,0x1e04070001ac00580,0x22000800,0x24000800,0x980,0x0,0x0,0x0,0x0,0xa00,0x0,0x0,0x0,0x0,0x280009a1026240983,0x2a000a80,0x0,0x0,0xa80,0xa80,0xb00,0xb00,0xb06,0x9a1,0xa00,0xb1a,0xb68,0x0,0x5c00170005c001700,0x5c001700,0x5c081702,0x5c30170c]
def b0Marks3 : Array Nat := #[0x5c401710,0x644013da05d68175c,0x5d68175a,0x6b101ac00481012000b8005c001700,0x780018c00501032c0048205c081702,0x472011ce,0xc00,0xc81032000c01030000b80,0x5cf0173c,0x49b411ed,0x5d001740,0x5d181746,0x1700,0x1704,0x5c48172a,0x1712,0x90001880088001a200e0005cf0173c,0x6a001a200e00,0x38000d80034080d00,0x0,0x0,0x171e,0x1720,0x1722,0x0,0x0,0x172c,0x0,0x0,0x0,0x0,0x0]
def b0Marks4 : Array Nat := #[0x0,0x0,0x0,0x1260,0x0,0x0,0x5d001740,0x5c00170005c001700,0x1700,0x1704,0x170005c18171e,0x1706,0x0,0x1706,0x5e081788,0x119a,0x1708,0x1180,0x1180,0x44001080046001180,0x1180,0x0,0x0,0x0,0x1700,0x0,0x5c00170005c001700,0x1700,0x0,0xee003b20170005c000b80,0x1380,0x1700]
def b0Marks5 : Array Nat := #[0x1700,0x4210108205c001700,0x4c00138004e001380,0x5c081380,0x0,0x0,0x0,0x1700,0x0,0x4e04138005c001700,0x5c000702,0x0,0x1700,0x0,0x1700,0x1700,0x5004140005c001700,0x0,0x1700,0x1700,0x5204148005c001700,0x150005c00170002508093c01e100782,0x1700,0x1700,0x5c00170005c001700,0x1700,0x0,0x1700,0x1700,0x0,0x158105c000f3005c000cc8,0x1700]
def b0Marks6 : Array Nat := #[0x0,0x1700,0x58041700046001700,0x0,0x1700,0x1700,0x0,0x168105c001700038f00d00,0x0,0x170005c00150004a000d83,0x5c00170005c001700,0x1700,0x3d800f4805c000b80,0xf84046081180,0x5e001004046081198,0x0,0x1700,0x1184046081700,0x1204048081700,0x0,0x1700,0x0,0x6000128405c081700,0x1540054101800038f00e00,0x5610140203cc00c48,0x1604052081180,0x5578168405a081280,0x170405c081700,0xfaa03e900f9e,0x4168104204090101e,0x1700,0x1704]
def b0Marks7 : Array Nat := #[0x62081880,0x4290119e,0x4490111e,0x4690119e,0x4690121e,0x469018b7,0x633c18b7,0x4b68129e,0x5c781706,0x171e,0x190106400171e,0x34780d0c,0x52f8171e,0x5b700da1,0x131e,0x139e,0x58b8161e,0x171e,0x139e,0x171e,0x0,0x0,0x0,0x0,0x1980,0x1a00,0x68001980,0x199e,0x199e,0x0,0x1a01,0x1a80]
def b0Marks8 : Array Nat := #[0x1a80,0x1a80,0x1b00,0x1b00,0xa80,0x1b2106c241b03,0xa80,0x0,0x1b21,0x0,0x0,0x0,0x6e041b80,0x70001b80,0x70041b80,0x1c80,0x1d00,0x74001c80,0x1ba0,0x1ba0,0x1180,0x1181,0x1380,0x1700,0x0,0x0,0x1d80,0x0,0x0,0x0,0x1e00,0x0]
def b0Marks9 : Array Nat := #[0x0,0x0,0x1381,0x0,0x78001d03,0x1c61,0x0,0x1d42,0x0,0x1d84,0x1e04,0x1704,0x119d,0x11a4,0x139e,0x171e,0x0,0x0,0x7a001f00,0x1f80,0x82001e80,0x2280,0x2300,0x8e00299c,0x8e602a62,0x2408090082400,0x9e0024020a4002900,0xa0182a9a,0x283c,0xb00028b40a2c8289c0a2682480,0x29060a41829000a4002500,0x2580]
def b0Marks10 : Array Nat := #[0x29060a6002600,0x2b060a8182b000a800261e,0x2b060aa002698,0xb0002b860ae002700088242203,0xa490291e0a4302906,0x0,0xa4902a1e0b5542986,0xb55c2a9e0b5542a86,0xac782c82,0x0,0x2dde0ae7822210ae182209,0xb8102e020b8006d801b6006d801b6006d80,0xb87878801e20078801e2007880,0x7b001ec007b001ec007b00,0x7b801ec007b001ec007b00,0xbc042f000ba006d801b6006d80,0xba7878801e2007880,0xc0002f860be006d8c1b6306d8c,0xbe6078821e2087882,0x310015d68575a15d683100,0xc20079101e45877901e24078a8,0xc400595a0b968749013f684fda,0xc40030860c2003100195682e5a1d44054da153686dda,0xc40079901e65878901e2407b00,0xc40079901e6407990,0xbc0078c81e32078c8,0x31300c46031001e8406dda1b7686dda,0x1e8407a101e8407a10,0xc00478cc1e33078cc,0x7b001ec007b00,0x7b001ec007b00,0x20810820020010c80420000c800318007c041f000cec06d801b6006d80]
def b0Marks11 : Array Nat := #[0xca18328019b20718c,0x7b00,0x7b001ec007b00,0x0,0x33310ccc033b0,0x34820d20073151c85472171c6547b00,0xd40034180d0006dbc1b6f06dbc,0x35800d26034801a5c07a8a1a3c068f0,0xd60879c61e30078c0,0x1ec007b00,0x36800d80836001b6006d80,0x37001a3807884,0x37981e2107884,0x1ec007b00,0x0,0x1ec007b00,0xe00021800840039001e2207888,0xe20022180880039001ec007b00,0x7b00,0xe80039820e6006d80,0xea007880,0x3b800ec003a801b6786d9e,0xe6187898,0xdc006812,0x6992,0x1b6487b00,0xf0303c060f0006d92,0x3c801e6487b00,0xec2078a0,0xf4083d000f2006daa,0xf000789c,0x3d061e6b078a2]
def b0Marks12 : Array Nat := #[0xe80078e0,0xee0078e8,0x7b00,0x0,0x7b00,0xfe003f860fe78258008b204600118604630,0x3f80140003980,0xfc003e800fe003f80152003f80,0xfe0057800eac06580,0x10200428010a602605098103700,0x408014e103a00,0x100003d820fe006880,0xfc083f00102004080152104080,0x1020065040b8106d80,0x102003e020f8006d80,0x102003f820fe006d80,0xf6903d9e,0x41000f8787281,0x3e9e,0x3f1e,0x3f9e,0x4280164483c00,0x4280166483c98,0x10a0065120b84879aa,0x10808420010a004280194483c00,0x4148104c04280,0x10630418610a006960,0x428c10a184280,0x106c041981c8487214,0x108607912,0x10a607992,0x10a607992]
def b0Marks13 : Array Nat := #[0x100184000,0x4080,0x0,0x0,0x1ec007b00,0x438410e0843801b6006d801b6006d801b6006d80,0x44801100844001b6006d80,0x240109000450013e00450013e18571e,0x268109a00370918000370318018619e,0xa268288009f4027b211c0029000a40032a00ca3829000a4006702,0xdc846898,0xa41c29060a40429001140068981a2c07880,0xa41c299c1160068b0,0x478711e1846801a2c068b0,0xb2042c800a8702a1a1140069181b6187980,0x48011200046801b6186d86,0x45981a2607880,0xb4002caa116786898,0x118606898,0x11a6068981e2007880,0x1520043801e2c04f801e2c04f98,0x4f0113c00548013e004f8013e005480,0x5a0011a184f801a2005700,0x60800e80c5d00,0x65000f0246180,0x5181146006500134006d80152006d8015c005700,0x1481065001020c5202174005d00,0x14a046500150005280186006180,0x65000c5005d00,0x188005680132006180,0x14c105302138006d80,0x2d430b4f42b1c0ac686d801c0247b00]
def b0Marks14 : Array Nat := #[0x1b6007b00,0x154f02b9c088546d801e2207b00,0x4884122084f801a2006880,0xb7005ac00b070553e082f82c04154f020bc1ae0038801b6f06dbc,0x11e90478c1b00033481c6f071bc,0x120086c801e2c878b2,0x16b7821b9086cc6d001e30078c0,0x6d801ec007b00,0x6d80,0x6d80,0x491c124684f801b6006898,0x1b6006980,0x4f8413e084f801b6006d80,0x6d80,0x53841400850001b6006d80,0x4a8412a086000,0x12e10678012e086180,0x150105402150006d801a6006980,0x6980,0x152105482152006d801b60054841520854801b6006d801b6006d80,0x5d04156085580,0x158105602158007a301b6007a30,0x6d8016e105b8215a004c80,0x1b6006d801b6006d80170105c0215c005700,0x6d80178105c82196005780,0x6c041b0086d8017c105f021980058001b60033b0,0x6004162085880,0x164105902164006d80,0x6d8017e105f821a0005980,0x1b2106c821b6006104184086880168006d80,0x186106980186086180,0x6d8018a106a0018a086200]
def b0Marks15 : Array Nat := #[0x190106a8018c086300,0x6d041b6006d801ae0064841ac00638218e003900,0x1b6006d801b6006d80194106502194006d80,0x7b00,0x16d0078f0,0x7b00,0x7b00,0x0,0x1be006f021bc006d80,0x128904a1e1ec007180,0x4aa412a787300,0x71001c2087080126907180126787180,0x12c904b1e,0x523d,0x55bc,0x5d40,0x0,0x0,0x7b00,0x7b00,0x0,0x7b00,0x4d1e1e20078801e2007880,0x136787880,0x4e1e,0x519e1e3407780,0x571e1ec007880,0x15c787980,0x15e787880,0x13e7878801e2004f9e1e2007880,0x6f36140787880,0x70e61c33874061427878801e2006898]
def b0Marks16 : Array Nat := #[0x589e,0x166787880,0x13e78591e1e6187880,0x76601d92074061687878801e2006d80,0x1dc0077801de007780144787780,0x531e,0x6fb91e200539e,0x1de0477801e2007880152787880,0x78801e20078801e2005c1e,0x1e2005c9e,0x1e2005f9e,0x619e,0x76e41e20075861d600639e1e200390c,0x1e2005e1e,0x5e9e,0x601e,0x6fb91e200609e,0x78011e20076061e2006ca4184787180,0x78801e2006d5a1da187680192787380,0x1e20078801e2007880194787880,0x1e40479001e2007980152787980,0x0,0x0,0x196787880,0x69da,0x0,0x0,0x7b00,0x1ec007b001ec007b00,0x7a1c,0x74cc1d2d0749c1e8706d92,0x1a0a87884]
def b0Marks17 : Array Nat := #[0x7b00,0x1b98071c81c6c0719819a30668619a007b00,0x673c19c906ee01c72071b61c678670619c00718c,0x0,0x7b00,0x71e01c72078b01e26068861a2007b00,0x1c98072481e2c079981a2186900,0x6b3c1cf8078c81e2c078a01e2206b00,0x0,0x7b00,0x1e38078c81e2c07b001ec006d80,0x7b00,0x7b001ec007b001ec007b00,0x7b00,0x1ec0068f21cb0c72ab1e6407012,0x7b001b76879c01e6a07990,0x7b001c16870421ccb47315,0x7a10,0x7d00,0x1f4007c801f0087c00,0x0,0x0,0x7e801f8c07c02,0x1fc047e801f8c07d00,0x200007f80,0x202007f80,0x206008100,0x2501,0x208002900,0x2901,0x0,0x8280]
def b0Marks18 : Array Nat := #[0x20a008121204248103,0x23d120e008380,0x0,0x8380,0x210008121,0xa41c8301,0x8406210008280206248183,0x211c08458207b081d4,0xa4908306,0x159682e5a1716c310021768310017168310021768310015d682e5a,0x194002e00172003b48136003ab0110003600,0x178143bc8178103bb0152102e04112003680,0x17e4c3d4817e483d30166483780164482e12,0x2700092001fa20ca881fa00ca801f8a0ca281f880ca20469e11a18858007e10328407e08328211ad846802161846b011a60859e,0x18404481218400480c14200468613e004f8010e008580,0x19400518414404850119400518214400850015200548013400858015200548010e008580,0xb60063811540463801540038c20e2f0570015c004d002160020040800858000c6006600,0x178045b01178005b00194002e00176003683,0x18a045b8118a005b80188004c00194002e00,0x4a041261084841280849822120857001420085801a2006880,0x132104c82132006d80,0x570415210858415c0854822160857001520085801b6006d80,0x1249048a421290491e12278849e,0x4f3613c78851e,0x4fb613e78859e,0x593613e78859e,0x1d5a075501b6787500,0x0,0x945a2516854da,0x2304095da,0x262406dda,0x9890262409890262407a10]
def b0Marks19 : Array Nat := #[0x1f8c47e301f0047c00218009400250006400,0x1fc007db01f20487301f0089402250086303,0x23b208ece,0x8680,0x870121c00868121a008600,0x68f0,0x202007da0200007e0822200943c250f05ebd,0x81981f88081801f8208880,0x22200880021e088780,0x799c,0x0,0x9820,0x22e008b8622e784500,0x22e004f80,0x8b0022e008b8022e005480,0x22e005700,0x5c01,0x8a0222e006880,0x5704,0x8a8222a006884,0x8b8222e006d80,0x8a24228787180,0x22a787181,0x22c787780,0x22e787880,0x9790,0x4fe0,0x7192,0x7784,0x7884,0x7992,0x7b00]
def b0Marks20 : Array Nat := #[0x250009400186009400250006180,0x940025018941e,0x250186030,0x23000a000280625208282425220283c,0x23a684a9a,0x2502058b3,0x114009780,0x106848e80,0x104cc8e80,0x8e002360034c523a008e80,0x1000c8e80,0x250009400174009400250005d00,0x22580894810d689400250008600,0x108849000,0x10a849400,0x8d842360835dd250009400,0x8f800c3009000240009000,0xfc0c9402240005583,0x9001240003140250009400,0x8458250005301207087e82,0x1020c9400,0x908124200355a250009400,0x9181246003028250009400,0x248009400250004e002030880bc1fc107f02,0x4d00,0x24a0434422500089b0250008748,0x93010be88940023a009400,0x4380,0x24e042f04250009400222f08780,0xba00940025000920023c008803,0x2e00250009400250009400,0x2278089c8250008600]
def b0Marks21 : Array Nat := #[0x13e109580,0x8c8423a088e80,0x252008d0423a088e98,0x8e8423a089400,0x0,0x254008f04250089400,0x9240248109500222f08880,0x24a109082226c086c8,0x152109102244009580,0x9304246088e80,0x24978938424e088f00,0x9404250089400,0x5704,0x1a60098b0,0x8caa232908c9e,0x235688d42234908d1e,0x236908e9e,0x238908e1e,0x23a908e9e,0x244f07789,0x256f078f0,0x23d688f1e,0x250789406,0x15c789780,0x21e78878c,0x246f8941e,0x24f708821,0x8f9e,0x901e,0x24cb8931e,0x941e,0x941e]
def b0Marks22 : Array Nat := #[0x4f9e,0x15278970125c009780,0x963c2589071f5,0x1a7689800,0x0,0x260007a10,0x25af496a525e4068da,0x97c025ea09790260006dda,0x0,0x0,0x0,0x0,0x9890,0x820020c00830620c90833c,0x192005a8018e04384218e00383c17c04320417c00320213a003180,0xfe008580,0xf6003e0112c004b80,0xfa005200148085280,0xfe003f81174006180,0x174108584,0x18678859e,0x0,0x0,0x9400,0x228008a812587496b2,0x22c0091012440c9730,0x22e008b812560c97b0,0x9404,0x941e,0x9890,0x230008c01260408c51,0x26c909b1e26c309b0628a00a28228af0a2be]
def b0Marks23 : Array Nat := #[0x270609b9e270009b8628d08a344,0x276ac9da52764c9d8d28f68a3dc,0x29a00a68029a00a68029a00a68029a00a68029a00a68029a00a68029a00a680,0x29a00a68029a00ae802ba00ae802ba00ae802ba00a680,0x29a00c10030400c10030400c10030400a680,0xd10034400d10034400d10034400a680,0x29600a68029a00e38038e00e38038e00e38038e00a680,0x10c80432010c80432010c8043200a680,0x29a00a68029a00a680438010e00438010e0043800a68043800a680,0x29a01100044001100044001100029a011000,0xa66029920a63029a00a68029601150045401150045400a680454011500,0x29a00a68029a00a68029a01160029a011600458011600458011600,0x2ba00ae802ba00ae802ba00ae802ba00ae802ba00ae80,0xd10034400d10034400ae80,0x29e00ae802ba00e38038e00e38038e00ae80,0xa8802ba00ae8039030e38c38e30e38c3cc30a680,0xa9802ba00ab803f640fd963f440fd103f440ab8043800a680,0xab802ae00ab002a818aa002ae010990298410a1042859039040e41155a,0x2ba00ae802ba00ae80438010e0043800ae8043800ae80,0xd1033e00ca6803440cd103,0xac812b200a8302ba00ae8029e01150045400ae80454011500,0x2b400ae802ba010ec829a00e3da38f68e3da,0xad002b400aab02aa60aa803b768a5da43d20e65a39968e65a,0xae802ba00ae802ba01104829a01104829a010e48439210e48,0x2ba0110482ba011048441211048,0xae012ba00a9302a460ae802a201150c2ba01150c45431150c,0xae802ba00ad002aec0ab982ae01160029a01178045e05155a45569155a,0x2ba00ae802ba00ae802ba0116002ba011600458011600,0x2ba00ad002b0c0ac182b001178046201178045e011780,0x2c600b1862c678d10034400d10034600af00,0x9a0126800999926660998126600af802640499002c800b1002c400e38038e00e38038e00b100,0xd1033e20ca6803440cd103]
def b0Marks24 : Array Nat := #[0x2c201121029a010c90432410c90,0x2c2c0b0982c201160029a01145a45169145a,0xb3002d200b480390f0e4543e2f0a68038ef0e3bc,0x2d200b4022ce08b4002ce00b2982ca01160029a01180044dc1137644bc112f0,0x2dc00b68030400c10030400b680,0x2dc00b71834400d10034400b680,0xb5002da00b68038e00e38038e00b680,0x30400c10030400c10030400c100,0x30400c18030660c11834400b680,0x30600cd8034400bc80,0x30600d10034400c100,0x30600c180,0xb98030400c10039000e3803cc00b680,0x26a189a802ea00c10030400e41e390d8e39e3e278af00,0xd10142c04ae80,0xbd0030400c1002f200e61238e48bc8043800a680,0x2f000ef122f2010ca0,0x30400c10030400c10043800c10043800c100,0x30600c10044000c10044000c180,0x2fa00c10030400bb802d6610f9829a00e3aa,0xc10044060c1002dc011018,0xc0002ec30bb0630400c1002e6011500304011500,0x10ca029a00d121,0x10ca0304010ca0,0xc0802f830c10030400ba802e801151e30401151e,0xc10030400c10030400bc802f201151229a01151229a010e60,0xc1002fc30bf062fc00c1002f4011512304011512,0x30400bc8045800a68045e811069,0x30400bf8c2fe18c1002fa00bd8045800b68045e25152a,0x30400c10030400c100304011600304011600,0x34400d10034400d100,0x26e189b0626e009b0030a00c598316c0ca0027e009ac835800d60636400d906]
def b0Marks25 : Array Nat := #[0x9c0227000c48026e689b9831c60cd0033c00a00528010d71239060b580,0xc78034400d10039000e4183e200b680,0x31e00e40039a00b700,0x31400c30230c00c78031e00e60039c00b980,0x34400f3803e200c100,0x3e200d100,0xc41e34400ca003f800ba0042e00c100,0x32600c90032800ca0030e78ca0040e00ca00,0x43200ae80,0x43200d100,0x270909c1e270309c0631200cc8033260d08028384a0e02ee60bb80,0x33600d10034400bc8044000a680,0xca8c32a18ca8033600cd803b648bd00,0xcd8032e30cb8632e00cd802f200f1122964917a1,0x32c60d10033c00fd9240210bd8044000b680,0xcf0033a08ce8033c00cc1833c0109842fc610a12,0x34400d10034400d10044000c10044000c100,0x34401100034400c180,0x3440112003040116a1,0xd00032120ca3032860c58631600d10044a00d100,0x32720c9b034200d08034200c60040f80d080,0xd10034200c68042780a66045400a680,0x45000b480,0x34200c8c8322c0cf1833200d10031c011500304011721,0x34200ca48328c0d10034400c78045400d100,0x34400d10034400d10045800a68045800a680,0xd10045800ae80,0xd10033920ce3033c60cd1833c00cd0045800b68044d811366,0xd10033d20cf3033c60d1003360116003040117a1,0xd10034400d10034400d10045800d100,0xd10033720cfbc33e90cf8c307211781,0xd28038e00e38038e00e38038e00e38038e00e380]
def b0Marks26 : Array Nat := #[0xd30039000e4183e200f8803e200e380,0x9d07274189d0127400d380272049c8035e00d78638e00e50038e00d58039418e38638e18d5803f400b100,0xa101284009e072eee49e0627670d50027668d41839e60b5833a0c10780,0xdf0039200e498432010c8043400d200,0xe60038e00e38039800e38038e010e0043800e38043800e380,0xe60039c00e41838e01100044000e38044000e418,0xda0436808da0039800e38039860e3803a600d28045400e38045400e60045400e618,0x27b609ec038600a20038e00a20028800e380288009e9c275409d24352909d3827478d49e268f8b02027a109d4a27430d48c274c89d06352189a3c2c020e1bc26808b04826800b03044420a70028800e3bc28800a20038ef0a200,0xe38035478b5a135418b5893ac00b0b044ac0a6803e700f9c0,0xa20128800e38038e00a20128800e38038e009f1c27c68d598356609f0427c08d58035600eb8044ac0b10044ac0b100438c10e30,0xa20128a08e380280709f9a36060d618280109f8236000d6003b00112b02de00b180440c11030,0xe20438808e38036660d69836600d6803b20112b038e00b20044ac112b0,0x38000ed0044820b680432210c88,0x38e00ed8044024e380440251009,0x29010a40228c10a30238e00a09c28268d59828048a00c37e00d7003b80115062c4011710440cd1033,0xe28438a08e38036660e38035e00ee8045418e380454191506,0xbca12f224ef0045800a680433010cc0,0xa48429208a38438e00a382284a8df9828490a11237e00a10c3be0116002c401185a449011240,0xe01838000f00045800b680450f1143c,0x29410e30438e00e38038600a19c38260a18438200f08045800b880454f1153c,0x38e00e38038e00e38038e00f10045800e380458011600,0x37010e58037008dc003c400bd093bc00ef00,0x3cc00f40044060f300390011018,0x3de00f7803de00dd403da60f680427c0d0bc,0xf8003de00de40427c0abe045800a680,0x3de00f8003e000ea3c3dc60f70045800d100,0x3e8010c8043200f980,0xfc813f200fd003f400dc9e42600fb0045478fd00454790380,0x432010c80432010c80,0x43201120043200fa00,0x40b8102c83f0c10c8043200df00454010c80,0x432010c80432010c8045800c14845800c148]
def b0Marks27 : Array Nat := #[0x41f9107cc3d4ccf51b39e590c8039e4116003e6011821,0x41f910c80400c9001a43200ed0c458010b00,0x432010c803bd6905c0416a10590458010c00,0x10c80432010c80432010c80458010c80,0x438010e00438010e00438010e00438010e00438010e00438010e00,0x440010e00440011000440010e00440011000,0x3fb80fec83fac10e00454010e0039801150045401150043800e600454011500,0x10e0045800e38045f01102144085160038e0117c0440851021,0x10468411410e0043800eb9e45800fd0045479151e45800fd0045479151e,0x438010e00438010e00458010e00458011600458010e00458011600,0x440011000440011000440011000,0x1100045400f8803ce60f38039a011018,0x40d80ff483fcc110004540110003d061100039c011500,0x106e841341100044000ec1e458010b803f801151e,0x44001014c404d1011c458010e003984917a144000ed9245e851512,0x1100041549053a44000ee2a458010f8040211152a,0x440011000440011000458011000440011600,0x103e040f2103b045401150040f8103c840ec1150045401150045401150045400e980,0x4238908ca4540108e042321160044a0101b040661150645400ee8645418ee80,0x425c1150045400f0bc42581160044e010648418c10620454f10608454f0f080,0x115004540115004580115004278109c8426c1150045801150045800f100,0x458011600458011600458011600458011600458011600458011600458011600,0x464011980,0x46a011a00,0x46a611a8046e011900,0x47a191e80476009f01,0x11e24478791e0c47818a200,0x11e9e47a18a201,0x11f0847c091f00,0x1208047c089c27486012180,0x48c012134484c9211c484691f80,0x48c012206488012000474251d03]
def b0Marks28 : Array Nat := #[0x1229c48a69228448a08a203,0x48691219e486312186,0x123de488791d21488191d09,0x43980a6804b600a68043920a6804b600a680438c0a6804b600a68043860a6804b600a68043800a6804b600a680,0xaa812aa01248040458ac004b240a61040440ac014b258a61041044ab804b040ab8041040ab804b040ab803f440ae804b600a610,0xad002b400ab302a6c124b02ac60a99849260ab002a60124803c568a5da3ab68ad804b440a5da3af78ad004ab68ad003af70ad004ab68ad003af68ad004ab68ad00,0x44180a68044120a680438c0ae804b600ae8043860ae804b600ae8043800ae804b600ae80,0x2c0c4b0302c064b0182c004b00044380a70144320a700438c0b1004b600b10043860b1004b600b10043800b1004b600b100,0x44980a68044120ae82440c0ae8043860b4804b600b48043800b4804b600b480,0x2d660b58044b80a68044120af02440c0af0043860b6804b600b68043800b6804b600b680,0x2ee30bb862ee00bc802f200e6602f4012a922d630b5862d600e392304012d80,0xbc8045448a68044120b68c440c0b68644060b68043800c1004b600c100,0xbc8045e84b7482dcc0b71830600c180,0xc68031801258031008c38249408c40030e01250031e00c7803c400a5803b008bac83b000bab03a600c7804aa00c78034c00b500,0xc33630c79251e42600a60041200be483fc18bb303fc00bb183ee00ba00,0xcc0c32c31260c33018cb0649818cc0032c01260033600cd803c448bd003b858bec83b850beb03b848be983b648a592,0xcb9832a61261842610a60441414bfc841410bfb040410cf804b248bf1840210b600,0xc51831401258041b84c0c841b80c0b040f80a66040d98c01840d80c000,0x45800a68044120c148440c0c13044060c11844000c100,0x286009e80274d0d487274c8d48627470d48127468d48034ec0d39849a00998a2c02899882c020d58035600e11835a19299826610b00426608b002384c0d6804a6c0d58035600d986366012c00,0x2880ca20128800d59c35668d59835610d58235600e618398012a8044b80b10444b20b10244ac0b10043860e3804b600e38043800e3804b600e380,0xa35a28d08a2bc35670d89a36260d71235830d60639c60e6004aa0113602c630b18639000e40039000e400,0xdb0436a11270436c08da8249c08db0036a0127003ba10d7923ba08d78c3ba00d7863a600e6004aa00e60039800e60039800e60034a012a80,0xef843ac10ef823ac08ef803ac00de843761129043c400e9003a2012a0037a08dd824a408de803760129003c400a5803bc00ef00,0x29168a44236290d89e37e48d80c36018f40045448b10444b20b78c44ac0b78644060e38043800f3004b600f300,0xdbd836f0128c0427c0a670421d8c054421c0c03c41bc4f21841bc0f200,0x45800ae8444920c148448c0c13044060f29844000f280,0x36490d91e36430d90645800b10444b20c24844ac0c23044060f31844000f300,0x38048e00c45448b69245430b68c448c0d20644860d20043800f9804b600f980,0x29568db3636c79281e41804e09241800e08c40618d98640600d98045448b89245430b88c44ac0e38644a60e38043800fd004b600fd003ec012c00,0x109803f3a102014ae0509803f34102004ae01038040e00fe864b001038040e00fe804b000dab636a79279e40e0103803ec012c00,0x45800c16045800c148448c0f9b044860f99844800f980]
def b0Marks29 : Array Nat := #[0x45448e39245430e38c45418e38645400e380438010e004b6010e00438012d8045448e39245430e38c45418e38645400e380438010e004b6010e00438012d80,0x45800e39245430f34845418f33045400f31845e84e448390c0e418440011000438012d80,0x45800f36045800f34845418fab045400fa98392c0e498448011200438012d80,0x45800f4e03d7812b6045800f4c83d7212b4845418fd303fec12c3045400fd183fe612c18394c0e1064a618e51838401298044a011280438012d80,0x45800f9e045800f9c845800f9b0452610d98452010d80,0x116003f58103e04b18116003f52103c84b12116003f4c103b04b0c11500454010e184b6011500454010e004b600e618398012a80,0x458011600439812d80458011600439212d80458011600438c12d80458011600438612d80458011600438012d80,0x1155a441812d8045e0117803b7c8e65a4ab690a403f7012cc0428a0fda84b2a10a103f6412c90,0x29a013f804fe013f804fe013f80,0x594016500594016500594011600,0x5960165005940165005940115e0,0xae804fe013f804fe013f80,0x12e0057e415f9657c415f10594010390,0x12e802ba015a034fe0d3f83,0x12f0059120e65a,0x12f004b8c12e184b80164905576955da55768e9da,0x12f0059401650059401155a,0x12f00598011780,0x2c4013f804fe013f80,0x46e051b8046c05308146c0130804c001198146601323055601558055600f003,0x4c419310054321590c,0xb1004fe0d3f83,0x59401650059401145a,0x131b14c6c13230,0x132824ca0165005940112f0,0x2da013f804fe013f80,0x16500594011270,0x13300472011c004d0015f0857c210709,0x13380474611d004d00165005940111f0,0x135004d4613f80,0x135002f2013f80,0x4d400c1004fe013f80]
def b0Marks30 : Array Nat := #[0x13500306013500,0x304013f81,0x556496500,0x4d4013500,0xe42d,0x594011069,0x4d23134864d20117a0,0x0,0x4d600c100,0x135802f20163a0,0x4fe013f80344013f804fe00d100,0x11e064780136004e26138b04f000d580,0x11e9a47a6139984fa00d584,0x4e8013f804fe00e380,0x4e800e400,0x136824da013a004e800e600,0x139004e009380055600eb84,0x4fe00f300,0x4fe00f880,0x4de793f804f000fd00,0x13b804f0013c004dc793c004f0010380,0x4e0790401,0x12f00,0xd101,0x4f2c13c984f2016380,0x4fe010c80,0x4fe00e392,0x4f4313d064f400e660,0x13f804fa00fd04,0x13d1857e48fe92,0x4f8093e004fa013e804d2610384,0x13f804fe013f804fe010e00]
def b0Marks31 : Array Nat := #[0x4fe013f804d4011000,0x4fe011001,0x4eb213c304f06138864e2013f804fe011280,0x4e400fd60,0x10c84,0x4ed213b304fa613f804e6011284,0x13c484f0c13f804fe013a004fe011500,0x10e60,0x598011060,0x13dc84f6c13e984fa0112e0,0x13ec84fac13e984fe011512,0x4fe013f804fe013f804fe011600,0x4fe013f3c4fc913f0c4d5211781,0x1400450009400055601558055600ef0055601558055600ef00,0x47c051f0031285408051c01408051c194a1e,0x26c01211a26e0521004834120b2506009b9b48601218046a993120276011a884c4392180486015102276689e00,0x4861d2186486052180502015198546c15f00,0x5081d42065040151b0546c0e7b0,0x50a05428050401558655618ed33,0x14118546615f0057c010786,0xca8952401400032a855f3051c015f3051c6105b0,0x1468151a00aac052401470033085470051c014900,0xc50352c01410632c854700546014a00,0x3180d4881522014f0051600a9c0556014900556014a003a80d4a00,0x149bc488711d15556015f08594010289,0x50e11438251c015180334855180,0x123c052f01231c526f91bbe48c1149bc46ef153004ce0155bc556f0df40,0x142245083153804c721593c564f0f53c,0x14282552015f3257cc9003d,0x14bde472e51cb3554015f4057d00fc40,0x556016500594010cc0,0x15580]
def b0Marks32 : Array Nat := #[0x51071441a51c015580332855198,0x51c11470251c015580336855580,0x1240335671240150c11228c48a196309,0xbca1,0x52411490252401558055600ad4052411490252401558055600ad40556015580,0x54e1153822cd695580532114c8253e014a80556013230,0x1548455208a8a8556014d0453409518052c015580,0x34a014d84548014d825360163c0,0x55410a78455601558054c014e8454a014e02538013400,0xa58055601558055601558053c114f0253c015580,0x594010b71,0x51491451e340856500564010af1,0x5620158022ca555800512915900512795900,0x53100fb70,0x15a0056801543c5666159804fe0103f0,0x558f0fd70,0xf9f0,0x59400f8dd,0x1459e57c015f003df755f0057c00f7dd,0x1489e327455f5057800f75d,0x14a1e34285650057c00f85d,0x51c795f0057c00cf0951c795f0057c00cf09,0x56199584e56c18b45b51e795f0057c015198,0x573815cc856c18ae4052c795f0057c015580,0x15d802a8415e00578015e00520795e00,0x15e0157800ab9057c015f00524795f00,0x57590aca257c015c06570014e1e57c01340c,0x57a04a90a57c015c8657c0154a4534795900,0x2a0015f0057c01555a574195d0053a795a80,0xa60057c015f0057c015f0053c795f00,0x58e00e3da,0x58e016040580a1601058800e65a]
def b0Marks33 : Array Nat := #[0x59401650034485650059400d121,0x305a56500,0x1576056521593056460b969542315086542016500,0x544f1512455f815948564d9591e3e591510654401590c,0x2db756500,0x56581594857cc15f182d3755186546016500,0x54af15ae057d215f303c78d5f2057c215280,0xb140,0x15f6057d215f302bb016500594015580,0x29a016500594016500594016500,0x16500557695fc057ea15f90,0x11e0047a05668047a6d228748a952432,0xf08338768f08138708f080386f0f10037211280449e1167043c400dc824a009278259c08f10037201280049e0167003b210af843b208af823b200af803a6012a8034a012a80,0x1090038d69088738b09088638af1088138aa9088038a91038036879273649c79671e41804b81241800b80c3fe18d9863fe00d980,0x45568e3da45508e3c2454f0e3bc454a8e3aa45490e3a445478e39e45448e39245430e38c45418e38645400e380,0x156da4be016b104bc012f004bc012f004bc012f002b4012ada,0x4d4013500,0x4de09370259e0937804dc0167804e8013a004e8013a0031e012a80,0x136b64da79679e328012c00,0x4fc01349833c012c04,0x344012d80,0x30a01200047e00c281468893122468813120350011a0a4c4291a084c421411e504196900350611a044c4111a024c4094136504016906504c141185a478d430,0x30c00c30153405429253401428c32e85262151e01410636e01470051c0140005a400dc00,0x30e00c38153c01488452005688153c0148825200168802ad0124c05240149005160169003740149005240140005a400dd80,0x310012380310054e01526054e0052600c6834960d33c24cef14a005280145805a400de0046c111b0252a01300053e00de80,0x31600c58131c0d45045121168045140944825a0094a0051e0169002cf75518054600e800,0x31e00c78131e0d4a045241169045280949025a4094a005240169002b501558055600ef00,0xc80032204c8835109143a45a091441e50e79681e33824f600,0x15054540f169bc3de012c70,0x32400f69233a0d46b651a79689e33a24f6dd,0x32800ca0133c0d473651c79691e33c24f7dd,0x583015bc05a90160a856ea16a28582415b905a8416280586016a803bd692ada]
def b0Marks34 : Array Nat := #[0xd10034404d10334424d121,0x12e804ba192e9e5bc4155da,0x4d6016620,0x5ae096b804bb015580,0x5ae795f00,0x0,0x4f2215f04,0x16500,0x47601360047605360150c016d0050c616d065b4794330,0x4da0136814f48550035b4016030,0x137004dc056c815b2012e405b40154035b40160b0,0x4de0137814e40d6d005580d5bb0,0x4e20138814e60d6c045b0096d004cb756340,0x4e8013a014e80d6d045b4096d004bd0163c0,0x13a804ec053b035b0916c1e4f6256171,0x5b6f15f70,0x4ee0159924f80d6c9e4f82559dd,0x4f0013c014fa0d6d1e4fa255a5d,0x16e405b8a16e105ba0155da,0x13f804fe053f834fe253fa1,0x494014e8052e01250153805334253801333c4a2014c814c2114c804c20946004c0012900,0x4e00167804e0056781530016983536016a30,0x5ae016b815b60d6e30,0x5d60171005d32172485d2c172305d26172185d2017200672017280724017280661217280724017280660c1728072401728066061728072401728066001728072401728063c0172807240172805c401c180,0x17d005f4017b8170c017d005f4017b8070c017b015ec01c2805f60178b05e0c1c2305f60178985e061c2185f60178805e001c2006e9697d8074c01755a5c601c1806dd817e0074e01755a6dd217e0174e05755a6d1017d0074b697d006d0a17d0074b697d006d0417d0074b697d00,0x1848063a01720062831840c62819840662801840062401858071801838067801728066321828c662c1828666261828066001850072401850063c01850072401850060e01c580,0x67a017280663218548662c1853066261851866201850063c018f00724018f0063c01c90067a017280663218548662c1853066261851866201850063c018f00724018f0063c01c900,0x5c00970005be01901863e698f98640018f8263e01919864601c680676017f84667217e82666c17e806606190807240190806600190807240190806a80173006940986c86940186b068a61910072a01861868a01911872a61860068001928073601830060a01c480,0x674018b6067a017280664c1873166461871966401870167a057281674058b48664c5873066465871866405870065205948073e0176815da01c300,0x6543195065c0f195005c091701e65a01960071e01900c64019900067201958072401958066f217f9066ec17f8a66e617f846600195807240195806a849731269c5989c869c5189b069c49899869a49878061201c50069a4998807420173125ca01c180,0x67a01958067031924867019923067001921867c819148644c1911866201988066001c9006e00174806d6318a486d6198a306d6018a186d401988074201988063c01c9006d401890061601c600,0x19e8066a019a00722019e8064d2193c871d219e8064cc193b071cc19c00670019818724019c0067001980072401919864601c6806e80175006db218c486dac18c306e2019c0074a019c0063c01c9006d8618a986d8018a80]
def b0Marks35 : Array Nat := #[0x672019c80724019c8067201c900672019c80724019c8067201c9006792195c86792195c8678c195b0678c195b06786195986786195986780195806780195806d3819e8074c0174605ca01c1806d3819e8074c0174605ca01c1806cfc98cc86cfb18cb06cf998c986cf818c80,0x19e00678019c80724019e8065f219748721219e8065ec19730720c19e8065e619718720619e0067801980072401968065801c7806e8499e8074c018d0061401c5806e84975126df218e486dec18e306de618e186dc019f2074e858d00,0x67a019e8067201c90067a019e8066121c90067a019e80660c1c90067a019e8066061c90067a019e8066001c9006ea019e8074c019e8063c01c9006ea0175806e1218ec86e0c18eb06e0618e986e0018e80,0x6a211a4045c379a8826900970c66a201a4005c301a12a6a801882161e85c52168491a11e68449aa0062025878971425a10c68419aa986aa01cb806c1c180606c701aa0074c0173c05cc01c1806c16180486c10180306bf05a80073f01a8006bf01a80073f01a800,0x5d181f38075001f3807ce01f3807ce01f380752019e80,0x1760076001d80075e01d63075861d60085201d4808540215018516a145a85169b8da,0x1bc016f001bb996ee61bb816ee01d9806ec05bb0076e01db0076c0180307fc01ff007fc01ff0076c01a903,0x1df0078e018c807d401d4007ce01f38078a019d20,0x7d601d4007ce01f38067201f58075001f3807ce019c80,0x1bd826f601e6186f269bc9879801bc826f201e8007d201da847ce01f38066cf1ff807fe62080077401a484,0x7b001eb007d001e46066121f401791220f00760019860,0x1ed807ce01ed007ce0194a078402108075201a260,0x1f5807b4018b697d881f38084201f38078e01b3e0,0x1f5807c601eac87aac179c07ce01f3807a00214007ce01b460,0x1f3807ce018f007ce01f38063c02148075202148075201b260,0x5da81f5007ce01eec87bac1ee987ce01ed8085201e28085485b360,0x5ca01f5807ce01f3807ce01f3807ce0214807ce01b4e0,0x1f6807fc01ff007fc01ff006a001ff007fc01ff007fc01a800,0x6fa1dbe866fa05be807dc01be016f801f9007e41995217fc0200007fc01f8006986e00067fc19ff067e0020a0076c01a633,0x80201ff007fc0195a180201ff007fc0195a18400210007fc0210007fc01afc0,0x1fa047e809fa005eb0200807fc01960980261ff0080801f6806588614007fc02140080202140080261b140,0x16f806fd6170016fd01fd005c00dc0807fc01c08070201ff0070201708468611bf1c6fb41bea47de91beb86fa79f79e6f0f9da205c0f5bf046fb29be8c7de31beb26fa19f7866f0f1da087f4f1703f6f009da486f001da3084621d50070201ff3c70201c0807fcf1c0805c301a1c0,0x1fd847f609815a7fc01f9987e261f9807e202028084ac1ff0076e0212b084ac1b040,0x1fe047f80977a87fc01f9987fc01f90080c0214067fc02140685019b0c0,0x19f8078485e10980e021480752020f4083d01ae40,0x70411fe845dc11ff007fc01fd006fe71fc186fe11fc0081002148077802143c850f1af40,0x8260609805e0420a0082801fb9e83a02090066886141e82802141e83201acdd,0x20ae082b220ab05ef021000850021000802021400850019e21850021000802021400850019e21,0x20ce0833220cb08500214005f5020ce0833220cb08500214005f5021400850021400850020200,0x8378a0dca5f2a21400837820dc885202128082ec17cc082e6214068500203068501a0300,0x839c17a04850021400810f20e60852021300835220d305e9020d20850f20d08850f20400,0x17500850021400850021480850020ee083b220eb05f7021400852021400852020480]
def b0Marks36 : Array Nat := #[0x1bd006f605bd837001215a485679bdbd8563215866f6fdc040,0x5d569735a5d50973425d4f1733c5d4a9732a5d49173245d479731e5d44973125d431730c5d41973065d40173005d181d0607060217005c401c1805d121d0487060217005c401c1805d0c1d0307060217005c401c1805d061d0187060217005c401c1805d001d0007060217005c401c180,0x5f4017a805f2c577b15f2c177b05f26577995f26177985e879771e5f20577815f20177805e81977065e80177005f005d0e05c601c1805f001d0c85c601c1805e4c1d03070c0217005d801c3005e461d01870c0217005d801c3005e401d00070c0217005d801c300,0x18e0c626318e06626198c0861a218e00626018c0261a098c0061a018d0061e01c50062a31860c62a19860662a01860063401d2925c801c18062831d0c860831c48c62819d0b060819c48662801d09860801c48062201d00071602170060e01c580,0x6792195c8678c195b0670f190bc6786195986709190a467079909e67801958067031908c67019908667001908067a01d3005ca01c18066321d0c861521c5c8662c1d0b0614c1c5b066261d09861461c59866201d08061401c580,0x1a98368e0da98168e05a98068e01a79c68271c99c69e69a09a72669a79868261c99869e11a08472611a78268209c98269e01a08072601a30072c61cb00858019f8069611d1e05fc11c38469609d1c85fc09c38269601d1b05fc01c38068861d01872802170067e01ca0068801d00072802170067e01ca00,0x6c401a85a6c2c5a6426c2c1a63c6c265a62a6c261a6246bc79a19e6c205a6126c201a60c6bc19a1866bc01a1806c601d30062f81c5e06c601d30062f21c5c86bac1d1306b4c1ce306ba61d1186b461ce186ba01d1006b401ce00,0x6d041a4da6d029a4c26d021a4bc6d011a4aa6d009a4a46d001a49e6cc49d29268849ca126cc31d28c68831ca0c6cc19d28668819ca066cc01d28068801ca006c801d0007400217006c801d0007400217006cc49d29268849ca126cc31d28c68831ca0c6cc19d28668819ca066cc01d28068801ca006c801d0007400217006c801d000740021700,0x6de31a75a6de19a7426da21a53c6de01a72a6da09a5246da01a51e6e001d30069a49ca126d831d28c6ad21cc486d819d2866acc1cc306d801d2806ac61cc186dc01d3a169a49b60c68a31cac86d819a28672ac1b60068a01ca986d401d0806ca01d080740021700,0x1b9836a769b9816a709b9806a6f1ba0074c01ade073b81cf6085b81ba0074c01adc873b21cf4885b21ba0074c01adb073ac1cf3085ac1b91c69ea9b91a69e91b91869e79b88074a01b31874a01d01885c01b90469e49b90269e31b90069e19b88074a01b30074a01d00085c01b88068c01cb1872c021600,0x6ea01d3006d381d3007418217006ea01d3006d321d3007412217006e969aa5a6ea01d3006d2c1d300740c217006e909aa426e8f1aa3c6ea01d3006d261d3007406217006e8a9aa2a6e891aa246e879aa1e6ea01d3006d201d3007400217006e849aa126e831aa0c6e819aa066e801aa00,0x5ca01c1807bf21d40086801d4007bec1d40086801d4007be61d40086801d4007be01d40086801d40079401d40086801d400,0x172805ca0572835ca2572a184181d48088001d48084121d48088001d480840c1d48088001d48084061d48088001d48084001d48088001d4805d601d300,0x5da01d70175c0217805da0579805e619799e84381d8807520210c876205d480840c1d80088001d80084061d80088001d80084001d80088001d8005f401d2da,0x17e805fa05da31768c17f8076865da185fe19da01768017f9e84581d50184521d500840c1db0088001db0084061db0088001db0084001db0088001db0060201d25a,0x77a31de8677a01e18078002180061401c5807c121dc8c7c0c1dc867c061dc807be01df8086801df8079401df8086801df80,0x1850078831870078819870278801870878c01e10062c02141278c01d48084321dd0c842c1dd0684261dd0084001e28088001e28063601d0e9,0x7c121dfc87c0c1dfb07c061df987c001df8079401e50086801e500794021a0063c01c9007c121dfc87c0c1dfb07c061df987c001df8079401e50086801e500794021a0063c01c900,0x6f401e59a79661e58279601e79879e0218807c521d9027c4c1d9007be61e68086801e6807be01e68086801e68079c01e7187a401dc8064201ca00,0x7d601d4007c2c1e0b17c261e0997c201e0817b201d58065001c901,0x6f6f1bda46f679e60c79819e6007cb21da907cac1da8a7ca61da847be01ed0086801ed0078921e23078862019277c0201927c001d40065601ca12,0x7cc31e8c87cc19e8b07cc01e89879d21e73079c61f0007c001ef8086801f0007c001e50086801e18078002180066201d080,0x1f5807a721ea4886521f5807a6c1ea30864c1f3007cc01ef9886801f3007cc01ef8086801e79879e0218807cc01f300794021a0067001d280,0x18f007d521ed4865001f5307b4c194027d461ed1865021f5007b401942085201f58075201d40084321e2c8842c1e2b084261e29884201e28067201d060,0x1f5807bd21ee4886721f5807bcc1ee30866c1f5807bc61ee1886661f5007d401ef8086801f58078c01df807d881e30067801d292,0x7d601f5807bf221a007d601f5807bec21a007d601f5807be621a007d601f5807be021a007d601f580794021a0067a01d300,0x63e01bf806fc018f816fad1f7876fac9f7866400dbe9c7de05be9a7de01f7307dc621a8064025bb8a76829bb8876821f8007e001fc987e21a1c9868401bb8476811bb8276809fcb07e2021cb07e001f8007e619f98087c01a106,0x190807020d908170205c0806420df81c7e069f81865625f8047e009f8008026200808740195a184b81db0484b21db0284ac1db0084061ff0088001ff0084001ff0088001ff006a001cfc0,0x6460191816460dfb047ea121b047ec09fa8286c09fb007ea021b005ed0203047e44a03027e43203007e41a0200802021d008020196a171e86008080202008080201f68087401aa80,0x64c01c15a64c0597037ecd9fb1e87079970983405fc1283401fc0c82e19f98682e01f98066a85c8a185049de1285031de0c84ac1ff0684a61ff00840020a00880020a00824021f006b175cd5d,0x64e01938183a0209e8830061e8183a0209d0830021e805e241c210832020c8082a1a1f0065e0e0c80832020a8087c01fab67ea7a1b9e65e260c8083202090087c01abdd,0x1948083e060f8087e0194818050a013c66c0e012a80491c01e66c26011280431c006700019b2185201e2e079382148078b21e4c8848c208b08486208988480208806a169ca5a]
def b0Marks37 : Array Nat := #[0x6600198016600d980985049ff1285031ff0c85019ff0685001ff0084002100088002100084002200067285c92185049ff1285031ff0c85019ff0685001ff0084002100088002100084002200067285c921,0x198806640599036642614807fc4a01928503205488501a0530850020518637a5c5e98548601927ff21ffb07fe621080842021000880019d21,0x19980666059b8366e261480817820660877821480817220648877221406828c20b3087cc21400828620b1887c6181dd7117600307f21a1c8680061fc8087202128084a021000880019da1,0x670019c016700e1480829820ce087d821480829220cc887d221480828c20cb087cc17d4070d021400850021018880019e09850021400840022000802620080874019e21,0x17580706021480852021060880019e8085202148084122200067a061480852021030880019e8385202148084062200067a261480852021000880019ea1,0x1d48088e02238088e02238088e01f580,0x1d40075005d40375025d4218a60229808a60229808a6021480,0x75602208075605d68075a19d69e8a60229808a602145a,0x1d90076405da8076a19da9e8a60229808a60213da,0x2210078a02238088e01f420,0x1df8078201e08278221e4008a60210e9,0x88e0223807ce02238088e01f380,0x2218088e0223807c8f1ff00,0x7bf21f381,0x7ac8223807b281ff12,0x1e46988e022380884021080,0x88922223075b02238088e02218088e021400,0x79401eb817ae0deb897ae861060,0x1d5a088d22233088c6223807b0821412,0x1d40088e02238088e02238088e021480,0x6f201e5806f205e5818561e15867980e15818560224007982626188046e26308a2020133,0x1e68079a05e6837b42626807b48629808a6020f40,0x1e78079e05e78389212248289201d74089a01eda189a020fc0,0x1e9807a605ee0389679ee097c68629808a20207dd,0x7a801ea018a00628007584228807bc0e288089479ef098a202075d,0x1ec808a401ec817c80df2097c885ff5a,0x7be01ef817be0def898a60229807ce8629808a601f3a1,0x1f0007c205f0837c225e2e98a601f421,0x1f1007c405f2837ca26276089d2228b08a261dc5d8981a26008a601f4a1,0x7cc01f3017cc0e28e08a32228b07610229807d426298089a01f521,0x1d4808a601f5808a601f5818a601f5838a601f5898a601f5a1,0x74b69ca5a74b09ca4274af1ca3c74aa9ca2a74a91ca2474a79ca1e74a49ca1274a31ca0c74a19ca0674a01ca00]
def b0Marks38 : Array Nat := #[0x71a0204037f569c68181005fd4281001fd3c71a0e04807ee121c0486e122a0481201fb828700a1b828a80a04807ee021c0086e022a0070b0202847661202827660a028076602020087401f68087401cb80,0x71c020e007fb69c7018361dfe4283619fe3c7200e0d817f8aa0d807f8920c807e87a1b3686c7a2a1e720260d017764a0d00776320b067e61a0b007e601ccdd,0x1c90085169ff5a7240614427fd0a143c7fcf1c903850a9ff2a85091ff2485079ff1e7242614127fc4a140c7fc3214067fc1a14007fc01c921,0x7ae021a007ae061a01,0x1e80086201e80186205e8038620e2584894122a848960a25028aa0a2580894022a8075f0217c089a02268080e021fc0,0x1ea8086401ea8186405ee838660e24b68927a2a9e7ba26198981b761e5d,0x7ce021a007ce061a017ce0e1a037ce261a097ce861a21,0x2228088a1a229e88e022381,0x8860221818860e2b048ac0a2b00883022940,0x88802220188c0e2b1e88c2627dd,0x2238088e06238388e2623a1,0x8c3222ec88c2c22eb08bef22dbc8c2622e988be922da48be7a2d9e8c2022e808be322d8c8be1a2d868be022d808c40245008ae0240808bd2244488b32241c88bcc244308b2c241b08bc6244188b26241988bc0244008b2024180,0x22d008df224c488d7224a488b80237b0930c235b0928c236bc8d2f22e028de624c188d6624a188da9234a48da7a349e8b822378093002358092802368c8d23236868d21a36808d2022e208e00252009320232009180245808d92250c88cf2248488d8c250b08cec248308d86250988ce6248188d80250808ce0248008c00243e0,0x8b6023c838ea0e2d818f2063a818f2023a808b60e3b9c8e4724d1c8ee6a391a9346a3b988e4624d188ba263b848e4124d048ee0a39029340a3b808e4024d008e8024e189380260008e2022ea18ec1251608cc1247048ec0a51488cc0a47028ec0251308cc0247008e66250189360261008e2024d808e60250009360261008e2024d808c6024340,0x8be023f038f36a2f818fc063cc28fc023cbc8be0e3f80948023d6093b824f60983823f80948023d4893b224f48983223f80948023d3093ac24f30982c22c40905023e9c8eeaa3e9a8ee923e988ee7a3e00946023d989460250189840230898fa123b928fa0a3b8c8fa023b868f80251808f60251809400261008f8023a00938624e009800230a1,0x8d00248809652257488d4024981964c257308d40a49839646257188d42249899640257008d48249a197c02598094c025280977225548976c255309766255189760255008dc025060,0x8d20249009000e34819240640019000234839240e5a1c9686a5a188d6264a09968125a02968025b1896c0262008d6864a21979825404979225402978c25400974625a8098c025a80974025a8098c025a808f0024fc0,0x2368092c02368192c06368392c0e5f0096f825c6098b825f0096f225c4898b225f0096ec25c3098ac232c091b025e8097a025d1898c023789930265e8097a025d0098c025b1896c0262008de864c21,0x95602568195a0e568995a865d60,0x2560095806560395c26640095c866500994025cc0,0x9600258019600e64e09932264b094f026500964266500990025921,0x9136a42da9130a42c2912f242bc912aa42aa9129242a49127a429e9124a429291232428c9121a4286912024280,0x92cf2493c92c92492492c7a491e92c32490c92c1a490692c02490092b2247c892ac247b092a62479892a024780908025f80,0x92602583c958f249829609256249607a561e92622580c9583258069581a58009580249a095f2254c895ec254b095e62549895e02548092e026100,0x95a02618095a0a618295a22618895a8261a0962026300,0x2638098e0a638898e826500,0x2658099d6a66da99606674299b0a673c99af2658399caa66aa99c9266a499c7a669e99626671299a4a670c99a32670699a1a670099a0265a1,0x998026b009a36a685a998066b019a30a68429a2f2683c9980e6b039a2aa682a9a29268249a27a681e998266b099a24a68129a232680c9a21a68069a2026800998866b21,0x99e026b809a96a69da99e066b819a90a69c29a8f269bc99e0e6b839a8aa69aa9a89269a49a87a699e99e266b899a84a69929a832698c9a81a69869a802698099e866ba1,0x9a4026c009a4066c019a40e6c039a4266c099a4866c21,0x26c809b2066c839b2266ca1,0x0]
def b0MarksA : Array (Array Nat) := #[b0Marks0,b0Marks1,b0Marks2,b0Marks3,b0Marks4,b0Marks5,b0Marks6,b0Marks7,b0Marks8,b0Marks9,b0Marks10,b0Marks11,b0Marks12,b0Marks13,b0Marks14,b0Marks15,b0Marks16,b0Marks17,b0Marks18,b0Marks19,b0Marks20,b0Marks21,b0Marks22,b0Marks23,b0Marks24,b0Marks25,b0Marks26,b0Marks27,b0Marks28,b0Marks29,b0Marks30,b0Marks31,b0Marks32,b0Marks33,b0Marks34,b0Marks35,b0Marks36,b0Marks37,b0Marks38]
def b0Marks (i : Nat) := (b0MarksA[i/32]?.getD #[])[i%32]?.getD 0
def b0Chk := SixSigned.closedRow 5 10 7 18 b0Tags SixRowsData.b0RowAt b0Marks
end SemiData
end Source38

section Source39
namespace SemiData
def segment (fn : Nat→Bool) (bound chunk idx : Nat) : Bool :=
  (List.range chunk).all fun k=>let i:=idx*chunk+k;decide (bound ≤ i) || fn i
theorem segment_sound {fn bound chunk idx i} (good : segment fn bound chunk idx=true)
    (valid : i < bound) (c : idx*chunk ≤ i) (d : i < idx*chunk+chunk) : fn i=true := by
  obtain ⟨v,hv,eq⟩ : ∃ v < chunk,idx*chunk+v=i := ⟨i-idx*chunk,by omega,by omega⟩
  have s := List.all_eq_true.mp good v (List.mem_range.mpr hv)
  simp [eq,Nat.not_le.mpr valid] at s
  exact s
def ac := segment a1Chk 6399 8
def bc := segment b0Chk 1248 8
end SemiData
end Source39

section Source40
namespace SemiData
open SixSigned SixRowsData
theorem aRoot (all : ∀i : Fin 800,ac i.val=true) :
 (¬Run 131071 511 5 0 (↑([22199, 43867, 68717, 78222, 115184] : List Nat))) ∧
 (∀ r, 0 < r → r ≤ 6 → ¬Run 131071 511 6 r (↑([22199, 43867, 68717, 78222, 115184] : List Nat))) := by
  have cert : ∀ i < 6399,a1Chk i=true := by
    intro i lt
    exact segment_sound (idx:=i/8) (all ⟨i/8,by omega⟩) lt (by omega) (by omega)
  have closed (j : Nat) (hj : j < 6399) := avoid_closed 9 8 4 17 a1Tags a1RowAt a1Marks 6399 cert j hj
  have h0 : ¬Run 131071 511 5 0 (↑([22199, 43867, 68717, 78222, 115184] : List Nat)) := by
    have eq : a1RowAt 6375=(5,0,[22199, 43867, 68717, 78222, 115184]) := by decide +kernel
    have z:=closed 6375 (by decide)
    rw [eq] at z
    exact z
  have h1 : ¬Run 131071 511 6 1 (↑([22199, 43867, 68717, 78222, 115184] : List Nat)) := by
    have eq : a1RowAt 6393=(6,1,[22199, 43867, 68717, 78222, 115184]) := by decide +kernel
    have z:=closed 6393 (by decide)
    rw [eq] at z
    exact z
  have h2 : ¬Run 131071 511 6 2 (↑([22199, 43867, 68717, 78222, 115184] : List Nat)) := by
    have eq : a1RowAt 6394=(6,2,[22199, 43867, 68717, 78222, 115184]) := by decide +kernel
    have z:=closed 6394 (by decide)
    rw [eq] at z
    exact z
  have h3 : ¬Run 131071 511 6 3 (↑([22199, 43867, 68717, 78222, 115184] : List Nat)) := by
    have eq : a1RowAt 6395=(6,3,[22199, 43867, 68717, 78222, 115184]) := by decide +kernel
    have z:=closed 6395 (by decide)
    rw [eq] at z
    exact z
  have h4 : ¬Run 131071 511 6 4 (↑([22199, 43867, 68717, 78222, 115184] : List Nat)) := by
    have eq : a1RowAt 6396=(6,4,[22199, 43867, 68717, 78222, 115184]) := by decide +kernel
    have z:=closed 6396 (by decide)
    rw [eq] at z
    exact z
  have h5 : ¬Run 131071 511 6 5 (↑([22199, 43867, 68717, 78222, 115184] : List Nat)) := by
    have eq : a1RowAt 6397=(6,5,[22199, 43867, 68717, 78222, 115184]) := by decide +kernel
    have z:=closed 6397 (by decide)
    rw [eq] at z
    exact z
  have h6 : ¬Run 131071 511 6 6 (↑([22199, 43867, 68717, 78222, 115184] : List Nat)) := by
    have eq : a1RowAt 6398=(6,6,[22199, 43867, 68717, 78222, 115184]) := by decide +kernel
    have z:=closed 6398 (by decide)
    rw [eq] at z
    exact z
  refine ⟨h0,?_⟩
  intro r pos top
  interval_cases r <;> assumption
theorem bRoot (all : ∀i : Fin 156,bc i.val=true) :
 (¬Run 32767 31 5 0 (↑([5871, 11127, 19899, 29149, 32286] : List Nat))) ∧
 (∀ r, 0 < r → r ≤ 6 → ¬Run 32767 31 6 r (↑([5871, 11127, 19899, 29149, 32286] : List Nat))) := by
  have cert : ∀ i < 1248,b0Chk i=true := by
    intro i lt
    exact segment_sound (idx:=i/8) (all ⟨i/8,by omega⟩) lt (by omega) (by omega)
  have closed (j : Nat) (hj : j < 1248) := avoid_closed 5 10 7 18 b0Tags b0RowAt b0Marks 1248 cert j hj
  have h0 : ¬Run 32767 31 5 0 (↑([5871, 11127, 19899, 29149, 32286] : List Nat)) := by
    have eq : b0RowAt 1237=(5,0,[5871, 11127, 19899, 29149, 32286]) := by decide +kernel
    have z:=closed 1237 (by decide)
    rw [eq] at z
    exact z
  have h1 : ¬Run 32767 31 6 1 (↑([5871, 11127, 19899, 29149, 32286] : List Nat)) := by
    have eq : b0RowAt 1242=(6,1,[5871, 11127, 19899, 29149, 32286]) := by decide +kernel
    have z:=closed 1242 (by decide)
    rw [eq] at z
    exact z
  have h2 : ¬Run 32767 31 6 2 (↑([5871, 11127, 19899, 29149, 32286] : List Nat)) := by
    have eq : b0RowAt 1243=(6,2,[5871, 11127, 19899, 29149, 32286]) := by decide +kernel
    have z:=closed 1243 (by decide)
    rw [eq] at z
    exact z
  have h3 : ¬Run 32767 31 6 3 (↑([5871, 11127, 19899, 29149, 32286] : List Nat)) := by
    have eq : b0RowAt 1244=(6,3,[5871, 11127, 19899, 29149, 32286]) := by decide +kernel
    have z:=closed 1244 (by decide)
    rw [eq] at z
    exact z
  have h4 : ¬Run 32767 31 6 4 (↑([5871, 11127, 19899, 29149, 32286] : List Nat)) := by
    have eq : b0RowAt 1245=(6,4,[5871, 11127, 19899, 29149, 32286]) := by decide +kernel
    have z:=closed 1245 (by decide)
    rw [eq] at z
    exact z
  have h5 : ¬Run 32767 31 6 5 (↑([5871, 11127, 19899, 29149, 32286] : List Nat)) := by
    have eq : b0RowAt 1246=(6,5,[5871, 11127, 19899, 29149, 32286]) := by decide +kernel
    have z:=closed 1246 (by decide)
    rw [eq] at z
    exact z
  have h6 : ¬Run 32767 31 6 6 (↑([5871, 11127, 19899, 29149, 32286] : List Nat)) := by
    have eq : b0RowAt 1247=(6,6,[5871, 11127, 19899, 29149, 32286]) := by decide +kernel
    have z:=closed 1247 (by decide)
    rw [eq] at z
    exact z
  refine ⟨h0,?_⟩
  intro r pos top
  interval_cases r <;> assumption
end SemiData
end Source40
namespace SemiData
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag0 (i : Fin 25) : ac (0+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (0+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag1 (i : Fin 25) : ac (25+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (25+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag2 (i : Fin 25) : ac (50+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (50+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag3 (i : Fin 25) : ac (75+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (75+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag4 (i : Fin 25) : ac (100+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (100+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag5 (i : Fin 25) : ac (125+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (125+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag6 (i : Fin 25) : ac (150+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (150+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag7 (i : Fin 25) : ac (175+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (175+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag8 (i : Fin 25) : ac (200+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (200+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag9 (i : Fin 25) : ac (225+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (225+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag10 (i : Fin 25) : ac (250+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (250+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag11 (i : Fin 25) : ac (275+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (275+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag12 (i : Fin 25) : ac (300+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (300+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag13 (i : Fin 25) : ac (325+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (325+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag14 (i : Fin 25) : ac (350+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (350+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag15 (i : Fin 25) : ac (375+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (375+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag16 (i : Fin 25) : ac (400+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (400+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag17 (i : Fin 25) : ac (425+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (425+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag18 (i : Fin 25) : ac (450+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (450+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag19 (i : Fin 25) : ac (475+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (475+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag20 (i : Fin 25) : ac (500+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (500+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag21 (i : Fin 25) : ac (525+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (525+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag22 (i : Fin 25) : ac (550+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (550+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag23 (i : Fin 25) : ac (575+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (575+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag24 (i : Fin 25) : ac (600+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (600+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag25 (i : Fin 25) : ac (625+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (625+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag26 (i : Fin 25) : ac (650+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (650+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag27 (i : Fin 25) : ac (675+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (675+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag28 (i : Fin 25) : ac (700+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (700+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag29 (i : Fin 25) : ac (725+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (725+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag30 (i : Fin 25) : ac (750+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (750+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem ag31 (i : Fin 25) : ac (775+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change ac (775+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem aAll (i : Fin 800) : ac i.val=true := by
  have cover (g : Fin 32) (a : Fin 25) : ac (25*g.val+a.val)=true := by
    obtain ⟨j,h⟩:=g
    change ac (25*j+a.val)=true
    match j,h with
    | 0, _ => exact ag0 a
    | 1, _ => exact ag1 a
    | 2, _ => exact ag2 a
    | 3, _ => exact ag3 a
    | 4, _ => exact ag4 a
    | 5, _ => exact ag5 a
    | 6, _ => exact ag6 a
    | 7, _ => exact ag7 a
    | 8, _ => exact ag8 a
    | 9, _ => exact ag9 a
    | 10, _ => exact ag10 a
    | 11, _ => exact ag11 a
    | 12, _ => exact ag12 a
    | 13, _ => exact ag13 a
    | 14, _ => exact ag14 a
    | 15, _ => exact ag15 a
    | 16, _ => exact ag16 a
    | 17, _ => exact ag17 a
    | 18, _ => exact ag18 a
    | 19, _ => exact ag19 a
    | 20, _ => exact ag20 a
    | 21, _ => exact ag21 a
    | 22, _ => exact ag22 a
    | 23, _ => exact ag23 a
    | 24, _ => exact ag24 a
    | 25, _ => exact ag25 a
    | 26, _ => exact ag26 a
    | 27, _ => exact ag27 a
    | 28, _ => exact ag28 a
    | 29, _ => exact ag29 a
    | 30, _ => exact ag30 a
    | 31, _ => exact ag31 a
    | j+32, hj => omega
  have part:=cover ⟨i.val/25,by have:=i.isLt;omega⟩ ⟨i.val%25,by omega⟩
  change ac (25*(i.val/25)+i.val%25)=true at part
  rwa [Nat.div_add_mod] at part
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem bg0 (i : Fin 20) : bc (0+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change bc (0+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem bg1 (i : Fin 20) : bc (20+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change bc (20+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem bg2 (i : Fin 20) : bc (40+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change bc (40+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem bg3 (i : Fin 20) : bc (60+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change bc (60+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem bg4 (i : Fin 20) : bc (80+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change bc (80+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem bg5 (i : Fin 20) : bc (100+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change bc (100+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem bg6 (i : Fin 20) : bc (120+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change bc (120+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem bg7 (i : Fin 20) : bc (140+i.val)=true := by
  obtain ⟨i,h⟩:=i
  change bc (140+i)=true
  interval_cases i <;> decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem bAll (i : Fin 156) : bc i.val=true := by
  have cover (g : Fin 8) (a : Fin 20) : bc (20*g.val+a.val)=true := by
    obtain ⟨j,h⟩:=g
    change bc (20*j+a.val)=true
    match j,h with
    | 0, _ => exact bg0 a
    | 1, _ => exact bg1 a
    | 2, _ => exact bg2 a
    | 3, _ => exact bg3 a
    | 4, _ => exact bg4 a
    | 5, _ => exact bg5 a
    | 6, _ => exact bg6 a
    | 7, _ => exact bg7 a
  have part:=cover ⟨i.val/20,by have:=i.isLt;omega⟩ ⟨i.val%20,by omega⟩
  change bc (20*(i.val/20)+i.val%20)=true at part
  rwa [Nat.div_add_mod] at part

end SemiData

end PEqualNP.Outside.L_meta_12226

open PEqualNP.Outside.L_meta_12226 in
theorem PEqualNP.Outside.L_meta_12226 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3907577984 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3907577984 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact TableClaim.from_tables (SemiData.aRoot SemiData.aAll) (SemiData.bRoot SemiData.bAll)
