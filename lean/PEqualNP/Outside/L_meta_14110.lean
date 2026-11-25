import PEqualNP.Defs

-- The restriction proof below is adapted from L-meta-2958 by Lior Dagan Mantinband.
-- The signed search and circuit evaluation are adapted from L-meta-10638 by Jonathan Nanhu.
-- Both source files are part of this repository and licensed under Apache-2.0.
namespace PEqualNP.Outside.L_meta_14110_aux

open PEqualNP.MetaComplexity
namespace Reduction
open PEqualNP.CircuitLowerBounds
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

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

noncomputable def charged (g : Gate) : Bool :=
  GateOp.rec true true false (fun _ => true) true g.op

noncomputable def cost (gs : List Gate) : ℕ := gs.countP charged



-- A surviving charged gate has two live operands. A surviving NOT has one.
-- Hence if no charged gate is lost, probes agreeing on live wires still agree.
theorem step_account (op : GateOp) (m : ℕ) (ins : List ℕ)
    (M : ℕ → Stat) (u v : ℕ → Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hlen : ins.length ≤ 2) (hag : ∀ i j, M i = Sum.inr j → u i = v i) :
    let r := simplify op m (ins.map M)
    let original := cost [⟨op, ins⟩]
    cost r.1.toList ≤ original ∧
      (cost r.1.toList = original → ∀ j, r.2 = Sum.inr j →
        op.eval (ins.map u) = op.eval (ins.map v)) := by
  rcases hop with rfl | rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    (try have ha := hag a; cases hma : M a) <;>
    (try have hb := hag b; cases hmb : M b) <;>
    simp_all [simplify, simpAnd, simpOr, simpNot, cost, charged, GateOp.eval]

theorem weakCost (n : ℕ) (gs : List Gate) : ∀ (acc : List Stat × List Gate),
    (∀ g ∈ gs, Ok g) → cost (elim n gs acc).2 ≤ cost acc.2 + cost gs := by
  induction gs with
  | nil => intros; simp [elim,cost]
  | cons g gs ih =>
    intro acc hok
    have hg := hok g List.mem_cons_self
    have h := (step_account g.op (n + acc.2.length) g.inputs
        (fun i => acc.1.getD i (Sum.inl false)) (fun _ => false) (fun _ => false)
        hg.1 hg.2 (fun _ _ _ => rfl)).1
    change cost (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList ≤ cost [g] at h
    have ht := ih (elimStep n acc g) (fun g' h' => hok g' (List.mem_cons_of_mem _ h'))
    show cost (elim n gs (elimStep n acc g)).2 ≤ _
    have hcons : cost (g::gs) = cost [g] + cost gs := List.countP_append
      (p := charged) (l₁ := [g]) (l₂ := gs)
    rw [hcons]
    have hadd : cost (elimStep n acc g).2 = cost acc.2 +
        cost (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList :=
      List.countP_append
    rw [hadd] at ht
    omega

theorem strictCost (n : ℕ) (gs : List Gate) (out j : ℕ) :
    ∀ (acc : List Stat × List Gate) (u v : List Bool),
      (∀ g ∈ gs, Ok g) → u.length = acc.1.length → v.length = acc.1.length →
      (∀ i k, acc.1.getD i (Sum.inl false) = Sum.inr k → u.getD i false = v.getD i false) →
      (elim n gs acc).1.getD out (Sum.inl false) = Sum.inr j →
      (wiresFrom gs u).getD out false ≠ (wiresFrom gs v).getD out false →
      cost (elim n gs acc).2 + 1 ≤ cost acc.2 + cost gs := by
  induction gs with
  | nil =>
    intro acc u v _ _ _ hag hj hdiff
    exact (hdiff (hag out j hj)).elim
  | cons g gs ih =>
    intro acc u v hok hu hv hag hj hdiff
    let M := fun i => acc.1.getD i (Sum.inl false)
    let r := simplify g.op (n + acc.2.length) (g.inputs.map M)
    have hg := hok g List.mem_cons_self
    have ha := step_account g.op (n + acc.2.length) g.inputs M
      (fun i => u.getD i false) (fun i => v.getD i false) hg.1 hg.2 hag
    change cost r.1.toList ≤ cost [g] ∧ _ at ha
    have hcost : cost (elimStep n acc g).2 = cost acc.2 + cost r.1.toList := by
      apply List.countP_append
    have hcons : cost (g::gs) = cost [g] + cost gs := List.countP_append
      (p := charged) (l₁ := [g]) (l₂ := gs)
    have htail (g' : Gate) (h' : g' ∈ gs) := hok g' (List.mem_cons_of_mem _ h')
    change cost (elim n gs (elimStep n acc g)).2 + 1 ≤ _
    rw [hcons]
    by_cases heq : cost r.1.toList = cost [g]
    · let U := g.op.eval (g.inputs.map fun i => u.getD i false)
      let V := g.op.eval (g.inputs.map fun i => v.getD i false)
      have hnext := ih (elimStep n acc g) (u ++ [U]) (v ++ [V]) htail
        (by simp [elimStep,hu]) (by simp [elimStep,hv]) (by
          intro i k h
          change (acc.1 ++ [r.2]).getD i (Sum.inl false) = Sum.inr k at h
          by_cases hi : i = acc.1.length
          · subst i
            rw [getD_snoc_eq] at h
            rw [← hu, getD_snoc_eq, hu, ← hv, getD_snoc_eq]
            exact ha.2 heq k h
          · rw [getD_snoc_ne _ _ _ _ hi] at h
            rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
            exact hag i k h) hj hdiff
      omega
    · have hweak := weakCost n gs (elimStep n acc g) htail
      omega

-- Track the surviving input wire for each occurrence in the original input list.
def pinStat {n : ℕ} (p : Fin (n+1)) : Fin (n+1) → Stat :=
  Fin.insertNth (α := fun _ => Stat) p (Sum.inl false) (fun j => Sum.inr j.val)

theorem pinStat_valid {n : ℕ} (p i : Fin (n+1)) : (pinStat p i).Valid n := by
  cases i using Fin.succAboveCases p
  · simp [pinStat, Stat.Valid]
  · rename_i j
    simpa [pinStat, Stat.Valid] using j.isLt

theorem pinStat_val {n : ℕ} (p i : Fin (n+1)) (y : Fin n → Bool) :
    (pinStat p i).val (List.ofFn y) = Fin.insertNth (α := fun _ => Bool) p false y i := by
  cases i using Fin.succAboveCases p
  · simp [pinStat, Stat.val]
  · rename_i j
    simp only [pinStat, Fin.insertNth_apply_succAbove, Stat.val]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt),List.getElem_ofFn]

theorem getMap {α β : Type*} (f : α → β) (l : List α) (i : ℕ) (d : β) :
    (l.map f).getD i d = if h : i < l.length then f l[i] else d := by
  by_cases h : i < l.length
  · rw [dite_eq_left h,List.getD_eq_getElem _ _ (by simpa using h),List.getElem_map]
  · rw [dite_eq_right h,List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]

theorem pinValid {n : ℕ} (p : Fin (n+1)) (l : List (Fin (n+1))) (k : ℕ) :
    ((l.map (pinStat p)).getD k (Sum.inl false)).Valid n := by
  rw [getMap]; split
  · exact pinStat_valid _ _
  · trivial

theorem pinMap {n : ℕ} (p : Fin (n+1)) (l : List (Fin (n+1))) (y : Fin n → Bool) (k : ℕ) :
    ((l.map (pinStat p)).getD k (Sum.inl false)).val (List.ofFn y) =
      (l.map (Fin.insertNth (α := fun _ => Bool) p false y)).getD k false := by
  rw [getMap,getMap]; split
  · exact pinStat_val _ _ _
  · rfl

theorem pinAgree {n : ℕ} (p : Fin (n+1)) (l : List (Fin (n+1))) (x : Fin (n+1) → Bool) (k j : ℕ)
    (h : (l.map (pinStat p)).getD k (Sum.inl false) = Sum.inr j) :
    (l.map (Function.update x p true)).getD k false = (l.map (Function.update x p false)).getD k false := by
  rw [getMap] at h
  rw [getMap,getMap]
  by_cases hk : k < l.length
  · simp only [dite_eq_left hk] at h ⊢
    have e : l[k] ≠ p := by
      intro e
      simp [e,pinStat] at h
    simp [Function.update_of_ne e]
  · simp [hk]


theorem restrict2958 : have x1 : List PEqualNP.CircuitLowerBounds.Gate → ℕ := fun (x1 : List PEqualNP.CircuitLowerBounds.Gate) => List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x3 : ℕ) => Bool.true) Bool.true x2.op) x1; ∀ (x2 : ℕ) (x3 : Fin (x2 + (1 : ℕ))) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List (Fin (x2 + (1 : ℕ)))),   PEqualNP.MetaComplexity.FanInTwo x4 →     have x7 : (Fin (x2 + (1 : ℕ)) → Bool) → Bool := fun (x7 : Fin (x2 + (1 : ℕ)) → Bool) => x4.eval (List.map x7 x5);     (∃ (x8 : Fin (x2 + (1 : ℕ)) → Bool), x7 (Function.update x8 x3 Bool.true) ≠ x7 (Function.update x8 x3 Bool.false)) → (∃ (x9 : Fin x2 → Bool) (x10 : Fin x2 → Bool), x7 (x3.insertNth Bool.false x9) ≠ x7 (x3.insertNth Bool.false x10)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x10 ∧ x1 x10.gates + (1 : ℕ) ≤ x1 x4.gates ∧ PEqualNP.MetaComplexity.circuitFun x2 x10 = fun (x11 : Fin x2 → Bool) => x7 (x3.insertNth Bool.false x11) := by
  dsimp only
  intro n p C l hfan
  intro hprobe hnc
  obtain ⟨x, hx⟩ := hprobe
  let M := l.map (pinStat p)
  let gs := C.gates
  let acc := elim n gs (M,[])
  have hok (g) (hg : g ∈ gs) : Ok g := hfan g hg
  have hval (y : Fin n → Bool) : (acc.1.getD C.output (Sum.inl false)).val
      (wiresFrom acc.2 (List.ofFn y)) = C.eval (l.map (p.insertNth false y)) := by
    let z := l.map (p.insertNth false y)
    have hi : Inv n (List.ofFn y) z (M,[]) := by
      refine ⟨by simp [M,z],?_⟩
      intro k
      exact ⟨pinValid p l k,pinMap p l y k⟩
    have he := ((inv_elim n (List.ofFn y) (by simp) gs z (M,[]) hok hi).2 C.output).2
    exact he
  cases ho : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨a,c,hac⟩ := hnc
    exact (hac (by rw [← hval a, ← hval c, ho]; rfl)).elim
  | inr j =>
    let u := l.map (Function.update x p true)
    let v := l.map (Function.update x p false)
    have hdiff : (wiresFrom gs u).getD C.output false ≠ (wiresFrom gs v).getD C.output false := by
      exact hx
    have hs := strictCost n gs C.output j (M,[]) u v hok
      (by simp [u,M]) (by simp [v,M]) (pinAgree p l x) ho hdiff
    refine ⟨⟨acc.2,j⟩, elim_ok n gs (M,[]) (by simp), ?_, ?_⟩
    · change cost acc.2 + 1 ≤ cost gs
      simpa only [show cost [] = 0 from rfl, Nat.zero_add] using hs
    · funext y
      have h := hval y
      rw [ho] at h
      exact h

end Reduction

namespace Search
open PEqualNP.CircuitLowerBounds

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

section FreeNot

def ops {n : ℕ} (x y : BitVec n) : List (BitVec n) :=
  [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]

abbrev basicOps {n : ℕ} (a b : BitVec n) : Finset (BitVec n) := (ops a b).toFinset

theorem ops_swap {n : ℕ} (a b : BitVec n) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

theorem index_of_op {n : ℕ} (a b z : BitVec n) (hz : z ∈ basicOps a b) :
    ∃ o : Fin 4, (ops a b).getD o.val 0 = z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩

def holds {n : ℕ} (av : Finset (BitVec n)) (z : BitVec n) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {n : ℕ} {av : Finset (BitVec n)} {z a : BitVec n} (h : holds av z) :
    holds (insert a av) z := by
  rcases h with h | h | ⟨u, hu, he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u, Finset.mem_insert_of_mem hu, he⟩)

theorem holds_mono {n : ℕ} {av av' : Finset (BitVec n)} (sub : av ⊆ av') {x : BitVec n}
    (h : holds av x) : holds av' x := by
  rcases h with h | h | ⟨a, ha, e⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨a, sub ha, e⟩)

theorem holds_not {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} (h : holds av z) :
    holds av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable {n : ℕ} (av : Finset (BitVec n)) (z : BitVec n) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} (h : reachable av z) :
    reachable av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds_not hw⟩

theorem bv_zero_and {n : ℕ} (x : BitVec n) : (0 : BitVec n) &&& x = 0 := BitVec.zero_and
theorem bv_and_zero {n : ℕ} (x : BitVec n) : x &&& (0 : BitVec n) = 0 := BitVec.and_zero
theorem bv_zero_or {n : ℕ} (x : BitVec n) : (0 : BitVec n) ||| x = x := BitVec.zero_or
theorem bv_or_zero {n : ℕ} (x : BitVec n) : x ||| (0 : BitVec n) = x := BitVec.or_zero
theorem bv_not_zero_and {n : ℕ} (x : BitVec n) : ~~~(0 : BitVec n) &&& x = x := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
theorem bv_and_not_zero {n : ℕ} (x : BitVec n) : x &&& ~~~(0 : BitVec n) = x := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
theorem bv_not_zero_or {n : ℕ} (x : BitVec n) : ~~~(0 : BitVec n) ||| x = ~~~0 := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
theorem bv_or_not_zero {n : ℕ} (x : BitVec n) : x ||| ~~~(0 : BitVec n) = ~~~0 := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp

set_option maxRecDepth 5000 in
theorem and_reach {n : ℕ} {av : Finset (BitVec n)} {x y : BitVec n}
    (hx : holds av x) (hy : holds av y) : reachable av (x &&& y) := by
  have const0 : holds av (0 : BitVec n) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [bv_zero_and]; exact .inl const0
  · rw [bv_not_zero_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [bv_and_zero]; exact .inl const0
  · rw [bv_and_not_zero]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const0 | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : BitVec n) (hw : w ∈ basicOps a b) (z : BitVec n) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a, ha, b, hb, h, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps, ops]) _ (.inl rfl)
  · exact add _ (by simp [basicOps, ops]) _ (.inl rfl)
  · exact add _ (by simp [basicOps, ops]) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps, ops]) _ (.inr BitVec.not_or.symm)

theorem or_reach {n : ℕ} {av : Finset (BitVec n)} {x y : BitVec n}
    (hx : holds av x) (hy : holds av y) : reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using
    reachable_not (and_reach (holds_not hx) (holds_not hy))

theorem mem_ops_reach {n : ℕ} {av : Finset (BitVec n)} {x y z : BitVec n}
    (hx : holds av x) (hy : holds av y) (hz : z ∈ basicOps x y) : reachable av z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact and_reach hx hy
  · exact or_reach hx hy
  · exact and_reach hx (holds_not hy)
  · exact and_reach hy (holds_not hx)

theorem mem_ops_const {n : ℕ} {av : Finset (BitVec n)} {x y z : BitVec n}
    (hx : holds av x) (hy : holds av y)
    (hconst : (x = 0 ∨ x = ~~~0) ∨ (y = 0 ∨ y = ~~~0))
    (hz : z ∈ basicOps x y) : holds av z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  have h0 : holds av (0 : BitVec n) := .inl rfl
  have h1 : holds av (~~~(0 : BitVec n)) := .inr (.inl rfl)
  have hnx : holds av (~~~x) := holds_not hx
  have hny : holds av (~~~y) := holds_not hy
  rcases hconst with (rfl | rfl) | (rfl | rfl) <;> rcases hz with rfl | rfl | rfl | rfl
  · rw [bv_zero_and]; exact h0
  · rw [bv_zero_or]; exact hy
  · rw [bv_zero_and]; exact h0
  · rw [bv_and_not_zero]; exact hy
  · rw [bv_not_zero_and]; exact hy
  · rw [bv_not_zero_or]; exact h1
  · rw [bv_not_zero_and]; exact hny
  · rw [BitVec.not_not, bv_and_zero]; exact h0
  · rw [bv_and_zero]; exact h0
  · rw [bv_or_zero]; exact hx
  · rw [bv_and_not_zero]; exact hx
  · rw [bv_zero_and]; exact h0
  · rw [bv_and_not_zero]; exact hx
  · rw [bv_or_not_zero]; exact h1
  · rw [BitVec.not_not, bv_and_zero]; exact h0
  · rw [bv_not_zero_and]; exact hnx

def SignedBuild {n : ℕ} (k : ℕ) (av : Finset (BitVec n)) (z : BitVec n) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps z k av ∨ build basicOps (~~~z) k av

theorem sb_zero {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} (h : holds av z) :
    SignedBuild 0 av z := by
  rcases h with h | h | ⟨a, ha, e | e⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · subst z; exact Or.inr (Or.inr (Or.inl ha))
  · subst z; exact Or.inr (Or.inr (Or.inr (by simpa only [BitVec.not_not, build] using ha)))

theorem sb_wait {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} {k : ℕ}
    (h : SignedBuild k av z) : SignedBuild (k + 1) av z := by
  rcases h with h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl (.inl h)))
  · exact .inr (.inr (.inr (.inl h)))

theorem sb_le {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} {k l : ℕ} (hkl : k ≤ l)
    (h : SignedBuild k av z) : SignedBuild l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb_wait ih

theorem sb_step {n : ℕ} {av : Finset (BitVec n)} {t a b z : BitVec n} {k : ℕ}
    (ha : a ∈ av) (hb : b ∈ av) (hne : a ≠ b) (hz : z ∈ basicOps a b)
    (h : SignedBuild k (insert z av) t) : SignedBuild (k + 1) av t := by
  rcases h with h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl (.inr ⟨a, ha, b, hb, hne, z, hz, h⟩)))
  · exact .inr (.inr (.inr (.inr ⟨a, ha, b, hb, hne, z, hz, h⟩)))

theorem sb_advance {n : ℕ} {av : Finset (BitVec n)} {z t : BitVec n} {k : ℕ}
    (hz : reachable av z)
    (next : ∀ av' : Finset (BitVec n), av ⊆ av' → holds av' z → SignedBuild k av' t) :
    SignedBuild (k + 1) av t := by
  rcases hz with h | ⟨a, ha, b, hb, hn, w, hw, ok⟩
  · exact sb_wait (next av (fun _ h => h) h)
  · exact sb_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

theorem ops_map_of {n m : ℕ} {f : BitVec n → BitVec m}
    (hAnd : ∀ a b, f (a &&& b) = (f a &&& f b))
    (hOr : ∀ a b, f (a ||| b) = (f a ||| f b))
    (hNot : ∀ a, f (~~~a) = ~~~(f a)) :
    ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b) := by
  intro a b z hz
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hAnd, hOr, hNot]

theorem live_transport {n m : ℕ} {f : BitVec n → BitVec m}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : BitVec n} {k : ℕ} {s : Finset (BitVec n)} {av : Finset (BitVec m)}
    (run : live basicOps g k s)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild k av (f g) := by
  induction k generalizing s av with
  | zero =>
    change s = {g} at run
    exact sb_zero (hav g (by simp [run]))
  | succ k ih =>
    rcases run with skip | ⟨a, ha, b, hb, hn, z, hz, hout, r, he, tail⟩
    · exact sb_wait (ih skip hav)
    · apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) (hm a b z hz))
      intro av' sub ok
      apply ih tail
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hr
      · exact ok
      · exact holds_mono sub (hav u (by simp [he, hr]))

theorem live_transport_save_const {n m : ℕ} {f : BitVec n → BitVec m}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g p : BitVec n} {k : ℕ} {s : Finset (BitVec n)} {av : Finset (BitVec m)}
    (run : live basicOps g k s)
    (hp : p ∈ s) (hconst : f p = 0 ∨ f p = ~~~0)
    (hng : f g ≠ 0 ∧ f g ≠ ~~~0)
    (hav : ∀ w ∈ s, holds av (f w)) :
    1 ≤ k ∧ SignedBuild (k - 1) av (f g) := by
  induction k generalizing s av with
  | zero =>
    change s = {g} at run
    have hpg : p = g := by simpa [run] using hp
    subst hpg
    rcases hconst with h | h
    · exact (hng.1 h).elim
    · exact (hng.2 h).elim
  | succ k ih =>
    simp only [Nat.add_sub_cancel]
    rcases run with skip | ⟨a, ha, b, hb, hn, z, hz, hout, r, he, tail⟩
    · obtain ⟨hk, hsb⟩ := ih skip hp hav
      exact ⟨by omega, sb_le (by omega) hsb⟩
    · have mapped := hm a b z hz
      have inOld : ∀ u ∈ r, holds av (f u) := fun u hu => hav u (by simp [he, hu])
      by_cases touches : p = a ∨ p = b
      · have hc : (f a = 0 ∨ f a = ~~~0) ∨ (f b = 0 ∨ f b = ~~~0) :=
          touches.elim (fun h => .inl (h ▸ hconst)) (fun h => .inr (h ▸ hconst))
        have collapsed := mem_ops_const (hav a ha) (hav b hb) hc mapped
        refine ⟨by omega, live_transport hm tail ?_⟩
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hr
        · exact collapsed
        · exact inOld u hr
      · have pr : p ∈ r := by
          rw [he] at hp
          simpa [Finset.mem_insert, not_or.mp touches |>.1, not_or.mp touches |>.2] using hp
        have pt : p ∈ insert z r := Finset.mem_insert_of_mem pr
        refine ⟨by omega, ?_⟩
        rcases mem_ops_reach (hav a ha) (hav b hb) mapped with hok | ⟨x, hx, y, hy, hxy, w, hw, hok⟩
        · obtain ⟨hk, hsb⟩ := ih tail pt (fun u hu => by
            rcases Finset.mem_insert.mp hu with rfl | hr
            · exact hok
            · exact inOld u hr)
          exact sb_le (by omega) hsb
        · obtain ⟨hk, hsb⟩ := ih tail pt (av := insert w av) (fun u hu => by
            rcases Finset.mem_insert.mp hu with rfl | hr
            · exact hok
            · exact holds_insert (inOld u hr))
          have hstep := sb_step hx hy hxy hw hsb
          exact sb_le (by omega) hstep

def selectRows {n m : ℕ} (rows : Fin m → Fin n) (w : BitVec n) : BitVec m :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin m => w[(rows k).val]))).cast List.length_ofFn

theorem selectRows_bit {n m : ℕ} (rows : Fin m → Fin n) (w : BitVec n) (j : Fin m) :
    (selectRows rows w)[j.val] = w[(rows j).val] := by
  rw [← BitVec.getLsbD_eq_getElem j.isLt]
  simp only [selectRows, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, dite_eq_left, Option.getD_some]

theorem selectRows_land {n m : ℕ} (rows : Fin m → Fin n) (u v : BitVec n) :
    selectRows rows (u &&& v) = (selectRows rows u &&& selectRows rows v) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin m := ⟨j, hj⟩
  change (selectRows rows (u &&& v))[k.val] = (selectRows rows u &&& selectRows rows v)[k.val]
  simp only [selectRows_bit, BitVec.getElem_and]

theorem selectRows_lor {n m : ℕ} (rows : Fin m → Fin n) (u v : BitVec n) :
    selectRows rows (u ||| v) = (selectRows rows u ||| selectRows rows v) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin m := ⟨j, hj⟩
  change (selectRows rows (u ||| v))[k.val] = (selectRows rows u ||| selectRows rows v)[k.val]
  simp only [selectRows_bit, BitVec.getElem_or]

theorem selectRows_neg {n m : ℕ} (rows : Fin m → Fin n) (u : BitVec n) :
    selectRows rows (~~~u) = ~~~selectRows rows u := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin m := ⟨j, hj⟩
  change (selectRows rows (~~~u))[k.val] = (~~~selectRows rows u)[k.val]
  simp only [selectRows_bit, BitVec.getElem_not]

def bitDiff {n : ℕ} (a b : Fin n) (w : BitVec n) : Prop :=
  w[a.val] ≠ w[b.val]

theorem ops_bitDiff {n : ℕ} (a b : Fin n) (x y z : BitVec n) (hz : z ∈ basicOps x y)
    (hd : bitDiff a b z) : bitDiff a b x ∨ bitDiff a b y := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨hx, hy⟩ := fail
  apply hd
  unfold bitDiff at hx hy
  simp only [not_not] at hx hy
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, hx, hy]

theorem bitDiff_not {n : ℕ} {a b : Fin n} {w : BitVec n} (h : bitDiff a b w) :
    bitDiff a b (~~~w) := by
  intro heq
  apply h
  simp only [BitVec.getElem_not] at heq
  cases ha : w[a.val] <;> cases hb : w[b.val] <;> simp_all

theorem live_has_unique_sep {n : ℕ} {g p : BitVec n} {k : ℕ}
    {s : Finset (BitVec n)} {ls : List (BitVec n)}
    (hs : s ⊆ ls.toFinset) (hl : live basicOps g k s)
    (a b : Fin n) (hd : bitDiff a b g)
    (huniq : ∀ w ∈ ls, bitDiff a b w → w = p) : p ∈ s := by
  obtain ⟨w, hw, hdw⟩ := live_separates (bitDiff a b) hd (ops_bitDiff a b) hl
  have hwp : w = p := huniq w (List.mem_toFinset.mp (hs hw)) hdw
  exact hwp ▸ hw

theorem sep_of_all {n : ℕ} (a b : Fin n) (ls : List (BitVec n)) (p : BitVec n)
    (h : ls.all (fun w => !(w[a.val] != w[b.val]) || w == p) = true) :
    ∀ w ∈ ls, bitDiff a b w → w = p := by
  intro w hw hdiff
  have h1 := List.all_eq_true.mp h w hw
  simp only [Bool.or_eq_true, Bool.not_eq_true', bne_eq_false_iff_eq, beq_iff_eq] at h1
  exact h1.resolve_left hdiff

theorem map_holds_list {n m : ℕ} (f : BitVec n → BitVec m) (src : List (BitVec n)) (dst : List (BitVec m))
    (h : src.all (fun w => f w == 0 || f w == ~~~0 || dst.any (fun d => f w == d)) = true) :
    ∀ w ∈ src, holds dst.toFinset (f w) := by
  intro w hw
  have h1 := List.all_eq_true.mp h w hw
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h1
  rcases h1 with (h0 | h1) | ⟨d, hd, hwd⟩
  · exact .inl h0
  · exact .inr (.inl h1)
  · exact .inr (.inr ⟨d, List.mem_toFinset.mpr hd, .inl hwd⟩)

theorem unwrap_sb {n : ℕ} {k : ℕ} {av : Finset (BitVec n)} {z : BitVec n}
    (h0 : z ≠ 0) (h1 : z ≠ ~~~0) (h : SignedBuild k av z) :
    ∃ t, (t = z ∨ t = ~~~z) ∧ build basicOps t k av := by
  rcases h with hz | hz | hb | hb
  · exact (h0 hz).elim
  · exact (h1 hz).elim
  · exact ⟨z, .inl rfl, hb⟩
  · exact ⟨~~~z, .inr rfl, hb⟩

theorem not_const_of_neg {n : ℕ} {w : BitVec n} (h : w ≠ 0 ∧ w ≠ ~~~0) :
    ~~~w ≠ 0 ∧ ~~~w ≠ ~~~0 := by
  refine ⟨fun heq => h.2 ?_, fun heq => h.1 ?_⟩
  · simpa only [BitVec.not_not] using congrArg (fun u : BitVec n => ~~~u) heq
  · simpa only [BitVec.not_not] using congrArg (fun u : BitVec n => ~~~u) heq

theorem img_sign {n m : ℕ} {f : BitVec n → BitVec m} (hNot : ∀ a, f (~~~a) = ~~~(f a))
    {T t : BitVec n} {T' : BitVec m} (hT : f T = T') (ht : t = T ∨ t = ~~~T) :
    f t = T' ∨ f t = ~~~T' := by
  rcases ht with rfl | rfl
  · exact .inl hT
  · exact .inr (by rw [hNot, hT])

theorem sign_nc {n : ℕ} {T x : BitVec n} (hx : x = T ∨ x = ~~~T) (hT : T ≠ 0 ∧ T ≠ ~~~0) :
    x ≠ 0 ∧ x ≠ ~~~0 := by
  rcases hx with rfl | rfl
  · exact hT
  · exact not_const_of_neg hT

theorem sb_out {n k : ℕ} {av : Finset (BitVec n)} {T x : BitVec n} (hx : x = T ∨ x = ~~~T)
    (hT : T ≠ 0 ∧ T ≠ ~~~0) (h : SignedBuild k av x) :
    ∃ t, (t = T ∨ t = ~~~T) ∧ build basicOps t k av := by
  obtain ⟨t, ht, hb⟩ := unwrap_sb (sign_nc hx hT).1 (sign_nc hx hT).2 h
  refine ⟨t, ?_, hb⟩
  rcases hx with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [BitVec.not_not]

theorem elim_one {n m : ℕ} (rm : Fin m → Fin n)
    {rows : List (BitVec n)} {rows' : List (BitVec m)} {T p : BitVec n} {T' : BitVec m}
    {i j : Fin n} (hsep : bitDiff i j T ∧ ∀ w ∈ rows, bitDiff i j w → w = p)
    (hp : selectRows rm p = 0 ∨ selectRows rm p = ~~~0) (hT : selectRows rm T = T')
    (hT' : T' ≠ 0 ∧ T' ≠ ~~~0) (hrows : ∀ w ∈ rows, holds rows'.toFinset (selectRows rm w))
    {k : ℕ} {t : BitVec n} (ht : t = T ∨ t = ~~~T) (hb : build basicOps t k rows.toFinset) :
    ∃ t', (t' = T' ∨ t' = ~~~T') ∧ build basicOps t' (k - 1) rows'.toFinset := by
  obtain ⟨s, hs, hl⟩ := compress hb
  have hd : bitDiff i j t := by
    rcases ht with rfl | rfl
    · exact hsep.1
    · exact bitDiff_not hsep.1
  have hft := img_sign (selectRows_neg rm) hT ht
  obtain ⟨_, hsb⟩ := live_transport_save_const
    (ops_map_of (selectRows_land rm) (selectRows_lor rm) (selectRows_neg rm)) hl
    (live_has_unique_sep hs hl i j hd hsep.2) hp (sign_nc hft hT')
    (fun w hw => hrows w (List.mem_toFinset.mp (hs hw)))
  exact sb_out hft hT' hsb

theorem proj_false {n m : ℕ} (rm : Fin m → Fin n) {rs : List (BitVec n)} {base : List (BitVec m)}
    {tgt : BitVec n} {T : BitVec m} (hT : T ≠ 0 ∧ T ≠ ~~~0) (hproj : selectRows rm tgt = T)
    (hhold : ∀ w ∈ rs, holds base.toFinset (selectRows rm w)) {k : ℕ}
    (hbase : ∀ t, (t = T ∨ t = ~~~T) → build basicOps t k base.toFinset → False)
    (t : BitVec n) (ht : t = tgt ∨ t = ~~~tgt) (hb : build basicOps t k rs.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress hb
  have hft := img_sign (selectRows_neg rm) hproj ht
  obtain ⟨t', ht', hb'⟩ := sb_out hft hT (live_transport
    (ops_map_of (selectRows_land rm) (selectRows_lor rm) (selectRows_neg rm)) hl
    (fun w hw => hhold w (List.mem_toFinset.mp (hs hw))))
  exact hbase t' ht' hb'

end FreeNot

section SearchP

abbrev WP (P : ℕ) := BitVec (P + P)
def sepP {P : ℕ} (x : WP P) : BitVec P := ((x >>> P) ^^^ x).setWidth P
def cutsP {P : ℕ} (ws : List (WP P)) : BitVec P := ws.foldr (fun w v => sepP w ||| v) 0
def goalP (P : ℕ) : WP P := BitVec.allOnes P ++ (0 : BitVec P)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def differsP {P : ℕ} (i : Fin P) (w : WP P) : Prop :=
  w.getLsbD (P + i.val) ≠ w.getLsbD i.val

theorem goalP_differs {P : ℕ} (i : Fin P) : differsP i (goalP P) := by
  unfold differsP goalP
  have hi : i.val < P := i.isLt
  have hlo : (BitVec.allOnes P ++ (0 : BitVec P)).getLsbD i.val = false := by
    rw [BitVec.getLsbD_append]
    simp [hi]
  have hhi : (BitVec.allOnes P ++ (0 : BitVec P)).getLsbD (P + i.val) = true := by
    rw [BitVec.getLsbD_append]
    have hnot : ¬ (P + i.val < P) := by omega
    simp only [hnot, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel_left]
    rw [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_allOnes]
  rw [hlo, hhi]
  decide

theorem ngoalP_differs {P : ℕ} (i : Fin P) : differsP i (~~~goalP P) := by
  have h := goalP_differs i
  unfold differsP at h ⊢
  have h1 : P + i.val < P + P := by omega
  have h2 : i.val < P + P := by omega
  simp only [BitVec.getLsbD_not, h1, h2, decide_true, Bool.true_and]
  intro heq
  apply h
  cases a : (goalP P).getLsbD (P + i.val) <;> cases b : (goalP P).getLsbD i.val <;> simp_all

theorem ops_differsP {P : ℕ} (i : Fin P) (a b z : WP P) (hz : z ∈ basicOps a b)
    (hd : differsP i z) : differsP i a ∨ differsP i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differsP at ha hb
  simp only [not_not] at ha hb
  have hi : P + i.val < P + P := by omega
  have hi' : i.val < P + P := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cutsP_spec {P : ℕ} (ws : List (WP P)) (i : Fin P) :
    (cutsP ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differsP i w := by
  induction ws with
  | nil => simp [cutsP]
  | cons a rest ih =>
    change (sepP a ||| cutsP rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sepP, i.isLt, differsP, Nat.add_comm, bx]

theorem cutsP_full {P : ℕ} {g : WP P} (hg : g = goalP P ∨ g = ~~~goalP P) {k : ℕ} {ws : List (WP P)}
    (h : live basicOps g k ws.toFinset) : cutsP ws = BitVec.allOnes P := by
  have hd : ∀ i, differsP i g := by
    intro i; rcases hg with rfl | rfl
    · exact goalP_differs i
    · exact ngoalP_differs i
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differsP ⟨j, hj⟩) (hd ⟨j, hj⟩) (ops_differsP ⟨j, hj⟩) h
  have hbit := (cutsP_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

def keepChoices {α : Type} (a b : α) (r : List α) : List (List α) :=
  [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {α : Type} [DecidableEq α] {ws r : List α} {a b : α} {needed : Finset α}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {α : Type} [DecidableEq α] {goal : α} {ws : List α} (hn : ws.Nodup)
    (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatchP (P : ℕ) (extra : ℕ) (next : ℕ → List (WP P) → Bool) (a b : WP P) (r : List (WP P)) : Bool :=
  let base := cutsP r
  let full := BitVec.allOnes P
  (ops a b).any fun w =>
    let v := sepP w ||| base
    ((v == full) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sepP a == full) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sepP b == full) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sepP a ||| sepP b == full) && next (extra - 2) (w :: a :: b :: r))

def optimizedP (P : ℕ) : ℕ → ℕ → List (WP P) → Bool
  | 0, _, ws => (ws == [goalP P] || ws == [~~~goalP P])
  | k + 1, extra, ws => (ws == [goalP P] || ws == [~~~goalP P]) ||
    (pairs ws).any (fun (a, b, r) => dispatchP P extra (optimizedP P k) a b r)

theorem dispatchP_complete {P k extra : ℕ} {a b z : WP P} {r kept : List (WP P)}
    (next : ℕ → List (WP P) → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cutsP (z :: kept) = BitVec.allOnes P) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatchP P extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cutsP, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimizedP_complete {P : ℕ} {g : WP P} (hg : g = goalP P ∨ g = ~~~goalP P) (n : ℕ)
    (ws : List (WP P)) (extra : ℕ) (hn : ws.Nodup) (room : extra + ws.length = n + 1)
    (h : live basicOps g n ws.toFinset) : optimizedP P n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimizedP, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimizedP, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : WP P} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatchP P extra (optimizedP P k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatchP_complete (k := k) (extra := extra) (optimizedP P k) hop hk (by omega)
          (by omega) (cutsP_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimizedP, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap,
          go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def searchP (P : ℕ) (n : ℕ) (inputs : List (WP P)) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n + 1) && (cutsP ws == BitVec.allOnes P) && optimizedP P n (n + 1 - ws.length) ws

theorem searchP_complete {P : ℕ} {g : WP P} (hg : g = goalP P ∨ g = ~~~goalP P) (n : ℕ)
    (inputs : List (WP P)) (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) :
    searchP P n inputs = true := by
  classical
  obtain ⟨s, hs, hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws, List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cutsP_full hg hl',
      optimizedP_complete hg n ws _ hnd (by omega : n + 1 - ws.length + ws.length = n + 1) hl']⟩

theorem goalP_ne_const {P : ℕ} (hP : 0 < P) :
    goalP P ≠ 0 ∧ goalP P ≠ ~~~0 ∧ ~~~goalP P ≠ 0 ∧ ~~~goalP P ≠ ~~~0 := by
  have hd := goalP_differs ⟨0, hP⟩
  have hdn := ngoalP_differs ⟨0, hP⟩
  have h0 : ¬ differsP ⟨0, hP⟩ (0 : WP P) := by unfold differsP; simp
  have h1 : ¬ differsP ⟨0, hP⟩ (~~~(0 : WP P)) := by
    unfold differsP
    have hb : 0 < P + P := by omega
    simp [hb]
    omega
  exact ⟨fun e => h0 (e ▸ hd), fun e => h1 (e ▸ hd), fun e => h0 (e ▸ hdn), fun e => h1 (e ▸ hdn)⟩

theorem signed_rejectP {P k : ℕ} (hP : 0 < P) {ws : List (WP P)} (hn : ws.Nodup)
    (hf : searchP P k ws = false) {t : WP P} (ht : t = goalP P ∨ t = ~~~goalP P)
    (h : SignedBuild k ws.toFinset t) : False := by
  have nt := goalP_ne_const hP
  rcases ht with rfl | rfl
  all_goals
    rcases h with h | h | h | h
    · first | exact nt.1 h | exact nt.2.2.1 h
    · first | exact nt.2.1 h | exact nt.2.2.2 h
    · exact Bool.noConfusion (hf.symm.trans (searchP_complete (by simp) k ws hn h))
    · exact Bool.noConfusion (hf.symm.trans (searchP_complete (by simp) k ws hn h))

end SearchP

section Compile128

abbrev W128 := BitVec 128

def bit128 (k : Fin 128) (z : W128) : Bool := z[k.val]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem read_bit128 (w : List W128) (i : ℕ) (k : Fin 128) :
    (w.map (bit128 k)).getD i false = bit128 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit128]

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W128) (g : Gate) : W128 := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W128) (g : Gate) (hg : legal g) (k : Fin 128) :
    step (w.map (bit128 k)) g = (w ++ [action w g]).map (bit128 k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W128)[k.val] = false := by change (0#128)[k.val] = false; simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step, List.map_cons, List.map_nil, read_bit128, List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit128, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      bit0, Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def binaryCost (gs : List Gate) : ℕ := (gs.filter isBinary).length

theorem available_read {av : Finset W128} {w : List W128} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W128) (av : Finset W128) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
    action, List.head?_nil, List.head?_cons, List.map_nil, List.map_cons, List.foldr_nil, List.foldr_cons,
    Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
    show ∀ x : W128, x ||| (0 : W128) = x from fun x => BitVec.or_zero,
    show ∀ x : W128, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (target : W128) (hnt0 : target ≠ 0) (hnt1 : target ≠ ~~~0)
    (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W128) (av : Finset W128) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit128 k))).getD out false = bit128 k target) :
    ∃ t, (t = target ∨ t = ~~~target) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = target := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit128, bit128] using he ⟨i, hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim (hnt0 zero)
    · exact False.elim (hnt1 ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun u : W128 => ~~~u) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit128 k))).getD out false = bit128 k target := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W128) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg, Bool.false_eq_true, ite_false] at stepClass
      simpa [binaryCost, neg] using cont av hw stepClass
    · simp only [neg, ite_true] at stepClass
      have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, neg]
      rw [len]
      rcases stepClass with existing | ⟨a, ha, b, hb, ne, new, op, rep⟩
      · obtain ⟨t, ht, run⟩ := cont av hw existing
        exact ⟨t, ht, Or.inl run⟩
      · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

end Compile128

end Search

open Search
-- Each column below specifies one input on the same 128 assignments.
-- The goal is false on the first 64 rows and true on the final 64.
-- The sample lemma checks every row against the reduced graph.
def coreRows : List W128 := [
  0x67be44c35065f54c059205404025d00c,
  0x99a4ef7f9a3a5b1b00e2a17110025919,
  0xe7f312f72dc3a1ab4a6082832d422183,
  0xd814be597b749e239c0d0c808d748622,
  0x32ed752ced9e44f4200d580c80980460]
def coreT : W128 := goalP 64
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem search_reject : searchP 64 6 coreRows=false := by decide +kernel
theorem reject_six {T : W128} (goal : T=coreT ∨ T = ~~~coreT) (run : build basicOps T 6 coreRows.toFinset) : False := by
  have yes := searchP_complete (P:=64) (g:=T) goal 6 coreRows (by decide : coreRows.Nodup) run
  rw [search_reject] at yes
  contradiction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Search

noncomputable def counted (g : Gate) : Bool := GateOp.rec (motive:=fun _=>Bool) true true false (fun _=>true) true g.op

def graph8 (x : Fin 8→Bool) : Bool :=
  (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) ||
  (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7)
def graph7 (x : Fin 7→Bool) := graph8 ((2 : Fin 8).insertNth false x)
def graph6 (x : Fin 6→Bool) := graph7 ((2 : Fin 7).insertNth false x)
def graph5 (x : Fin 5→Bool) := graph6 ((3 : Fin 6).insertNth false x)

private theorem restrict_cost {n k : ℕ} (p : Fin (n+1)) (f : (Fin (n+1)→Bool)→Bool)
    (sensitive : ∃x,f (Function.update x p true)≠f (Function.update x p false))
    (nonconstant : ∃x y,f (p.insertNth false x)≠f (p.insertNth false y))
    (lower : ∀D : Circuit,FanInTwo D → circuitFun n D=(fun x=>f (p.insertNth false x)) → k≤D.gates.countP counted)
    (C : Circuit) (fan : FanInTwo C) (correct : circuitFun (n+1) C=f) : k+1≤C.gates.countP counted := by
  have val (x : Fin (n+1)→Bool) : C.eval ((List.ofFn (id : Fin (n+1)→Fin (n+1))).map x)=f x := by
    rw [List.map_ofFn];exact congrFun correct x
  obtain ⟨D,fd,cost,read⟩ := Reduction.restrict2958 n p C (List.ofFn id) fan
    (by simpa only [val] using sensitive) (by simpa only [val] using nonconstant)
  change D.gates.countP counted+1≤C.gates.countP counted at cost
  have le := lower D fd (funext (fun x=>(congrFun read x).trans (val _)))
  omega

set_option maxRecDepth 20000 in
private theorem sample : ∀k : Fin 128, graph5 (fun i=>bit128 k (coreRows.getD i.val 0))=bit128 k coreT := by decide +kernel

theorem lower5 (C : Circuit) (fan : FanInTwo C) (correct : circuitFun 5 C=graph5) : 7≤C.gates.countP counted := by
  by_contra! low
  have normal (g : Gate) : isBinary g=counted g := by cases g with | mk op args => cases op <;> rfl
  have cap : binaryCost C.gates≤6 := by
    change (C.gates.filter isBinary).length≤6
    rw [←List.countP_eq_length_filter,funext normal];omega
  have init (v : W128) (hv : v∈coreRows) : holds coreRows.toFinset v :=
    Or.inr (Or.inr ⟨v,List.mem_toFinset.mpr hv,Or.inl rfl⟩)
  have eval (k : Fin 128) : (C.gates.foldl step (coreRows.map (bit128 k))).getD C.output false=bit128 k coreT := by
    let x (i : Fin 5) := bit128 k (coreRows.getD i.val 0)
    have width : coreRows.length=5 := rfl
    have same : List.ofFn x=coreRows.map (bit128 k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i<coreRows.length := by simpa using hj
        simp only [List.getElem_ofFn,List.getElem_map,x,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hlt,Option.getD_some]
    change C.eval (coreRows.map (bit128 k))=bit128 k coreT
    rw [←same];exact (congrFun correct x).trans (sample k)
  obtain ⟨T,ht,h⟩:=compile coreT (by decide) (by decide) C.gates C.output (fun g hg=>fan g hg) coreRows coreRows.toFinset init eval
  have extend {a b : ℕ} (le : a≤b) (run : build basicOps T a coreRows.toFinset) : build basicOps T b coreRows.toFinset := by
    induction le with
    | refl => exact run
    | step _ ih => exact Or.inl ih
  exact reject_six ht (extend cap h)

-- Fix the original vertices 2, 3, and 5 to false. The five remaining coordinates
-- correspond to the original vertices 0, 1, 4, 6, and 7, in that order.
theorem lower8 (C : Circuit) (fan : FanInTwo C) (correct : circuitFun 8 C=graph8) : 10≤C.gates.countP counted := by
  have six (D : Circuit) (fd : FanInTwo D) (read : circuitFun 6 D=graph6) : 8≤D.gates.countP counted := by
    apply restrict_cost (3 : Fin 6) graph6 _ _ lower5 D fd read
    · exact ⟨fun i=>decide (i=0),by decide⟩
    · exact ⟨fun _=>true,fun _=>false,by decide⟩
  have seven (D : Circuit) (fd : FanInTwo D) (read : circuitFun 7 D=graph7) : 9≤D.gates.countP counted := by
    apply restrict_cost (2 : Fin 7) graph7 _ _ six D fd read
    · exact ⟨fun i=>decide (i=6),by decide⟩
    · exact ⟨fun _=>true,fun _=>false,by decide⟩
  apply restrict_cost (2 : Fin 8) graph8 _ _ seven C fan correct
  · exact ⟨fun i=>decide (i=6),by decide⟩
  · exact ⟨fun _=>true,fun _=>false,by decide⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The four terms are (x₀ ∨ x₁)(x₅ ∨ x₇), x₄(x₀ ∨ x₇), x₆(x₁ ∨ x₂), and x₃x₇.
def witness : Circuit :=
  ⟨[⟨.or,[0,1]⟩,⟨.or,[5,7]⟩,⟨.and,[8,9]⟩,
    ⟨.or,[0,7]⟩,⟨.and,[4,11]⟩,⟨.or,[1,2]⟩,⟨.and,[6,13]⟩,
    ⟨.and,[3,7]⟩,⟨.or,[10,12]⟩,⟨.or,[14,15]⟩,⟨.or,[16,17]⟩],18⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀x : Fin 8→Bool,witness.eval (List.ofFn x)=graph8 x := by decide +kernel

theorem witnessBasis : ∀g∈witness.gates,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

def edges : List ℕ := [0,4,0,5,1,5,1,6,2,6,0,7,1,7,3,7,4,7]
def targetFn (x : Fin 8→Bool) := decide (∃i<edges.length/2,(List.ofFn x).getD (edges.getD (2*i) 0) false=true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false=true)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem explicitTarget : ∀x : Fin 8→Bool,graph8 x=targetFn x := by decide +kernel

end PEqualNP.Outside.L_meta_14110_aux

open PEqualNP.Outside.L_meta_14110_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_14110 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 1, 6, 2, 6, 0, 7, 1, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 1, 6, 2, 6, 0, 7, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 1, 6, 2, 6, 0, 7, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 1, 6, 2, 6, 0, 7, 1, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 1, 6, 2, 6, 0, 7, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 1, 6, 2, 6, 0, 7, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ graph
  change ∀x,Circuit.eval ⟨gates,o⟩ (List.ofFn x)=targetFn x at graph
  by_cases uses : ∃g∈gates,g.op=.not
  · have fan : FanInTwo ⟨gates,o⟩ := fun g hg=>legal g hg
    have correct : circuitFun 8 ⟨gates,o⟩=graph8 := funext (fun x=>(graph x).trans (explicitTarget x).symm)
    have lower := lower8 ⟨gates,o⟩ fan correct
    obtain ⟨g,hg,neg⟩ := uses
    have loss : gates.countP counted < gates.length := by
      have off : counted g=false := by simp [counted,neg]
      exact List.countP_lt_length_iff.mpr ⟨g,hg,by simp [off]⟩
    exact ⟨witness.gates,witness.output,witnessBasis,by change 11≤gates.length; change 10≤gates.countP counted at lower;omega,
      fun x=>(witnessCorrect x).trans (explicitTarget x)⟩
  · refine ⟨gates,o,?_,le_rfl,graph⟩
    intro g hg
    obtain ⟨basis,arity⟩:=legal g hg
    exact ⟨basis.elim Or.inl (fun h=>h.elim Or.inr (fun hn=>(uses ⟨g,hg,hn⟩).elim)),arity⟩
