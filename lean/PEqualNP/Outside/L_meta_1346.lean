import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1346

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

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

abbrev Stat := Bool ⊕ ℕ

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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g' := hp
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

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Sum.inr i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

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

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)

theorem simplify_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

noncomputable def gateCost (notCost : Bool) (g : Gate) : ℕ := by
  classical
  exact if notCost then (if g.op = GateOp.not then 1 else 0)
    else (if (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 then 1 else 0)

noncomputable def cost (notCost : Bool) (gs : List Gate) : ℕ :=
  (gs.map (gateCost notCost)).sum

theorem cost_nil (b : Bool) : cost b [] = 0 := by
  simp [cost]

theorem cost_cons (b : Bool) (g : Gate) (gs : List Gate) :
    cost b (g :: gs) = gateCost b g + cost b gs := by
  simp [cost]

theorem cost_append (b : Bool) (gs hs : List Gate) :
    cost b (gs ++ hs) = cost b gs + cost b hs := by
  simp [cost]

theorem simplify_cost (b : Bool) (g : Gate) (m : ℕ) (ss : List Stat)
    (hlen : ss.length = g.inputs.length) :
    cost b (simplify g.op m ss).1.toList ≤ gateCost b g := by
  classical
  obtain ⟨op, inputs⟩ := g
  cases op <;> cases b <;>
    rcases ss with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;>
    (try cases a) <;> (try cases d) <;>
    simp_all [simplify, simpAnd, simpOr, simpNot, cost, gateCost] <;> omega

theorem elim_cost (b : Bool) (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      cost b (elim n gs acc).2 ≤ cost b acc.2 + cost b gs := by
  induction gs with
  | nil => intro acc; simp [elim, cost]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 := simplify_cost b g (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) (by simp)
    have h3 : cost b (elimStep n acc g).2 ≤ cost b acc.2 + gateCost b g := by
      change cost b (acc.2 ++ _) ≤ _
      rw [cost_append]
      exact Nat.add_le_add_left h2 _
    change cost b (elim n gs (elimStep n acc g)).2 ≤ _
    rw [cost_cons]
    omega

open PEqualNP.CircuitLowerBounds

theorem drop_core_many (k m : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (out : Fin m → ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∀ o : Fin m, ∃ y y' : Fin k → Bool,
      vl (pre ++ g :: post) y (out o) ≠ vl (pre ++ g :: post) y' (out o)) :
    ∃ (gs' : List Gate) (out' : Fin m → ℕ),
      CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      (∀ b, cost b gs' + gateCost b g ≤ cost b (pre ++ g :: post)) ∧
      ∀ (o : Fin m) (y : Fin k → Bool),
        vl gs' y (out' o) = vl (pre ++ g :: post) y (out o) := by
  classical

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
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)).val
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
  let acc := elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)
  have hval : ∀ (o : Fin m) (y : Fin k → Bool),
      (acc.1.getD (out o) (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
      = vl (pre ++ g :: post) y (out o) := fun o y => ((inv3 y).2 (out o)).2
  have hw : ∀ o : Fin m, ∃ j : ℕ, acc.1.getD (out o) (Sum.inl false) = Sum.inr j := by
    intro o
    cases hst : acc.1.getD (out o) (Sum.inl false) with
    | inl c =>
      exfalso
      obtain ⟨y, y', hne⟩ := hnc o
      apply hne
      rw [← hval o y, ← hval o y', hst]
      rfl
    | inr j => exact ⟨j, rfl⟩
  choose out' hout' using hw
  refine ⟨acc.2, out', hc3, hlen, ?_, ?_⟩
  · intro b
    have h1 := elim_cost b k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)
    have h2 := elim_cost b k pre (idStats k, [])
    change cost b acc.2 ≤ cost b (elim k pre (idStats k, [])).2 + cost b post at h1
    simp only [cost_nil, zero_add] at h2
    rw [cost_append, cost_cons]
    omega
  · intro o y
    have h := hval o y
    rw [hout' o] at h
    exact h

theorem drop_alias_many (k m : ℕ) (gs : List Gate) (hcl : CleanL k gs)
    (out : Fin m → ℕ) (p j : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∀ o : Fin m, ∃ y y' : Fin k → Bool, vl gs y (out o) ≠ vl gs y' (out o)) :
    ∃ (gs' : List Gate) (out' : Fin m → ℕ),
      CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      (∀ b, cost b gs' + gateCost b g ≤ cost b gs) ∧
      ∀ (o : Fin m) (y : Fin k → Bool), vl gs' y (out' o) = vl gs y (out o) := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  apply drop_core_many k m pre g post hcl out
    ((elim k pre (idStats k, [])).1.getD j (Sum.inl false)) ?_ hnc
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

theorem drop_const_many (k m : ℕ) (gs : List Gate) (hcl : CleanL k gs)
    (out : Fin m → ℕ) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (c : Bool)
    (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∀ o : Fin m, ∃ y y' : Fin k → Bool, vl gs y (out o) ≠ vl gs y' (out o)) :
    ∃ (gs' : List Gate) (out' : Fin m → ℕ),
      CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      (∀ b, cost b gs' + gateCost b g ≤ cost b gs) ∧
      ∀ (o : Fin m) (y : Fin k → Bool), vl gs' y (out' o) = vl gs y (out o) := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  exact drop_core_many k m pre g post hcl out (Sum.inl c)
    (fun y => ⟨trivial, (heq y).symm⟩) hnc

theorem cost_set_eq (b : Bool) (gs : List Gate) (p : ℕ) (g g' : Gate)
    (hp : gs[p]? = some g) :
    cost b (gs.set p g') + gateCost b g = cost b gs + gateCost b g' := by
  induction gs generalizing p with
  | nil => simp at hp
  | cons h gs ih =>
    cases p with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
      subst h
      simp only [List.set_cons_zero, cost_cons]
      omega
    | succ p =>
      simp only [List.getElem?_cons_succ] at hp
      have hc := ih p hp
      simp only [List.set_cons_succ, cost_cons]
      omega

theorem drop_dead_many (k m : ℕ) (gs : List Gate) (hcl : CleanL k gs)
    (out : Fin m → ℕ) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (ho : ∀ o : Fin m, out o ≠ k + p)
    (hno : ∀ (q : ℕ) (g' : Gate), gs[q]? = some g' → k + p ∉ g'.inputs)
    (hnc : ∀ o : Fin m, ∃ y y' : Fin k → Bool, vl gs y (out o) ≠ vl gs y' (out o)) :
    ∃ (gs' : List Gate) (out' : Fin m → ℕ),
      CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      (∀ b, cost b gs' + gateCost b g ≤ cost b gs) ∧
      ∀ (o : Fin m) (y : Fin k → Bool), vl gs' y (out' o) = vl gs y (out o) := by
  have hpl : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hpos : 0 < k + p := by
    rcases hcl p g hp with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hpl]
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
          exact ih a hlt (fun e => hno r g' hr (e ▸ ha))
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∀ o : Fin m, ∃ y y' : Fin k → Bool,
      vl gs' y (out o) ≠ vl gs' y' (out o) := by
    intro o
    obtain ⟨y, y', h⟩ := hnc o
    exact ⟨y, y', by rw [hagree y (out o) (ho o), hagree y' (out o) (ho o)]; exact h⟩
  obtain ⟨gs'', out'', hc'', hl'', hb'', he''⟩ :=
    drop_alias_many k m gs' hcl' out p 0 g0 hget_p hpos halias hnc'
  refine ⟨gs'', out'', hc'', by omega, ?_, ?_⟩
  · intro b
    have h1 := hb'' b
    have h2 := cost_set_eq b gs p g g0 hp
    change cost b gs' + gateCost b g = cost b gs + gateCost b g0 at h2
    omega
  · intro o y
    rw [he'' o y, hagree y (out o) (ho o)]

theorem clean_many (n m : ℕ) (F : Fin m → (Fin n → Bool) → Bool)
    (gs : List Gate) (out : Fin m → ℕ) (hok : ∀ g ∈ gs, Ok g)
    (hev : ∀ o x, vl gs x (out o) = F o x)
    (hnc : ∀ o, ∃ x y, F o x ≠ F o y) :
    ∃ (gl : List Gate) (ol : Fin m → ℕ), CleanL n gl ∧
      (∀ b, cost b gl ≤ cost b gs) ∧ (∀ o x, vl gl x (ol o) = F o x) := by
  classical
  let acc := elim n gs (idStats n, [])
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) gs _ _ hok (inv_id n y)
  have hval : ∀ o (y : Fin n → Bool),
      (acc.1.getD (out o) (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) = F o y := by
    intro o y
    rw [((hinv y).2 (out o)).2]
    exact hev o y
  have houts : ∀ o, ∃ j, ∀ x : Fin n → Bool, vl acc.2 x j = F o x := by
    intro o
    cases hst : acc.1.getD (out o) (Sum.inl false) with
    | inl c =>
      exfalso
      obtain ⟨x, y, hne⟩ := hnc o
      apply hne
      rw [← hval o x, ← hval o y, hst]
      rfl
    | inr j =>
      refine ⟨j, ?_⟩
      intro x
      have h := hval o x
      rw [hst] at h
      exact h
  choose ol hol using houts
  refine ⟨acc.2, ol, ?_, ?_, hol⟩
  · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _ hok
      (inv_id n _) (by intro p g hp; simp at hp)
  · intro b
    have h := elim_cost b n gs (idStats n, [])
    simpa [cost_nil] using h

noncomputable def GoodRep (n m B : ℕ) (F : Fin m → (Fin n → Bool) → Bool)
    (gs : List Gate) (out : Fin m → ℕ) : Prop :=
  CleanL n gs ∧ cost true gs ≤ 1 ∧ cost false gs ≤ B ∧ ∀ o x, vl gs x (out o) = F o x

theorem least_many (n m B : ℕ) (F : Fin m → (Fin n → Bool) → Bool)
    (gs : List Gate) (out : Fin m → ℕ) (hok : ∀ g ∈ gs, Ok g)
    (hev : ∀ o x, vl gs x (out o) = F o x)
    (hnc : ∀ o, ∃ x y, F o x ≠ F o y)
    (hnot : cost true gs ≤ 1) (hbin : cost false gs ≤ B) :
    ∃ (gl : List Gate) (ol : Fin m → ℕ), GoodRep n m B F gl ol ∧
      ∀ (gl' : List Gate) (ol' : Fin m → ℕ), GoodRep n m B F gl' ol' →
        gl.length ≤ gl'.length := by
  classical
  obtain ⟨gl, ol, hcl, hcost, he⟩ := clean_many n m F gs out hok hev hnc
  have hrep : GoodRep n m B F gl ol :=
    ⟨hcl, (hcost true).trans hnot, (hcost false).trans hbin, he⟩
  have hex : ∃ t, ∃ (gl : List Gate) (ol : Fin m → ℕ),
      GoodRep n m B F gl ol ∧ gl.length = t := ⟨gl.length, gl, ol, hrep, rfl⟩
  obtain ⟨gl, ol, hrep, hlen⟩ := Nat.find_spec hex
  refine ⟨gl, ol, hrep, ?_⟩
  intro gl' ol' hrep'
  rw [hlen]
  exact Nat.find_min' hex ⟨gl', ol', hrep', rfl⟩

theorem GoodRep.output_nc {n m B : ℕ} {F : Fin m → (Fin n → Bool) → Bool}
    {gs : List Gate} {out : Fin m → ℕ} (hrep : GoodRep n m B F gs out)
    (hnc : ∀ o, ∃ x y, F o x ≠ F o y) :
    ∀ o, ∃ x y : Fin n → Bool, vl gs x (out o) ≠ vl gs y (out o) := by
  intro o
  obtain ⟨x, y, hxy⟩ := hnc o
  exact ⟨x, y, by rw [hrep.2.2.2 o x, hrep.2.2.2 o y]; exact hxy⟩

theorem GoodRep.replace {n m B : ℕ} {F : Fin m → (Fin n → Bool) → Bool}
    {gs : List Gate} {out : Fin m → ℕ} (hrep : GoodRep n m B F gs out)
    (gl : List Gate) (ol : Fin m → ℕ) (hcl : CleanL n gl)
    (hcost : ∀ b, cost b gl ≤ cost b gs)
    (heval : ∀ o (x : Fin n → Bool), vl gl x (ol o) = vl gs x (out o)) : GoodRep n m B F gl ol :=
  ⟨hcl, (hcost true).trans hrep.2.1, (hcost false).trans hrep.2.2.1,
    fun o x => (heval o x).trans (hrep.2.2.2 o x)⟩

theorem least_no_const {n m B : ℕ} {F : Fin m → (Fin n → Bool) → Bool}
    {gs : List Gate} {out : Fin m → ℕ} (hrep : GoodRep n m B F gs out)
    (hmin : ∀ gl ol, GoodRep n m B F gl ol → gs.length ≤ gl.length)
    (hnc : ∀ o, ∃ x y, F o x ≠ F o y) :
    ∀ p, p < gs.length → ∀ c, ¬ ∀ x : Fin n → Bool, vl gs x (n + p) = c := by
  intro p hp c hall
  obtain ⟨gl, ol, hcl, hlen, hcost, heval⟩ := drop_const_many n m gs hrep.1 out p gs[p]
    (List.getElem?_eq_getElem hp) c hall (hrep.output_nc hnc)
  have hrep' := hrep.replace gl ol hcl (fun b => by have h := hcost b; omega) heval
  have h := hmin gl ol hrep'
  omega

theorem least_no_alias {n m B : ℕ} {F : Fin m → (Fin n → Bool) → Bool}
    {gs : List Gate} {out : Fin m → ℕ} (hrep : GoodRep n m B F gs out)
    (hmin : ∀ gl ol, GoodRep n m B F gl ol → gs.length ≤ gl.length)
    (hnc : ∀ o, ∃ x y, F o x ≠ F o y) :
    ∀ p, p < gs.length → ∀ w, w < n + p →
      ¬ ∀ x : Fin n → Bool, vl gs x (n + p) = vl gs x w := by
  intro p hp w hw hall
  obtain ⟨gl, ol, hcl, hlen, hcost, heval⟩ := drop_alias_many n m gs hrep.1 out p w gs[p]
    (List.getElem?_eq_getElem hp) hw hall (hrep.output_nc hnc)
  have hrep' := hrep.replace gl ol hcl (fun b => by have h := hcost b; omega) heval
  have h := hmin gl ol hrep'
  omega

theorem least_live {n m B : ℕ} {F : Fin m → (Fin n → Bool) → Bool}
    {gs : List Gate} {out : Fin m → ℕ} (hrep : GoodRep n m B F gs out)
    (hmin : ∀ gl ol, GoodRep n m B F gl ol → gs.length ≤ gl.length)
    (hnc : ∀ o, ∃ x y, F o x ≠ F o y) :
    ∀ p, p < gs.length → (∃ o, out o = n + p) ∨
      ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
  intro p hp
  by_contra! h
  obtain ⟨ho, hno⟩ := h
  obtain ⟨gl, ol, hcl, hlen, hcost, heval⟩ := drop_dead_many n m gs hrep.1 out p gs[p]
    (List.getElem?_eq_getElem hp) ho hno (hrep.output_nc hnc)
  have hrep' := hrep.replace gl ol hcl (fun b => by have h := hcost b; omega) heval
  have h := hmin gl ol hrep'
  omega

open PEqualNP.CircuitLowerBounds

def setOr {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ v ∈ S, x v = true)

lemma setOr_nonconstant {n : ℕ} (S : Finset (Fin n)) (hcard : 2 ≤ S.card) :
    ∃ x y : Fin n → Bool, setOr S x ≠ setOr S y := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  have ht : setOr S (fun _ => true) = true := by
    apply decide_eq_true
    exact ⟨v, hv, rfl⟩
  rw [ht]
  simp [setOr]

lemma setOr_ne_input {n : ℕ} (S : Finset (Fin n)) (hcard : 2 ≤ S.card) (i : Fin n) :
    ∃ x : Fin n → Bool, setOr S x ≠ x i := by
  obtain ⟨v, hv, hvi⟩ := Finset.exists_mem_ne (show 1 < S.card by omega) i
  refine ⟨fun j => decide (j = v), ?_⟩
  simp [setOr, hv, Ne.symm hvi]

lemma eval_nil_of_lt {n : ℕ} (x : Fin n → Bool) (out : ℕ) (h : out < n) :
    Circuit.eval ⟨[], out⟩ (List.ofFn x) = x ⟨out, h⟩ := by
  simp only [Circuit.eval, Circuit.wires, List.foldl_nil]
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

lemma eval_nil_of_le {n : ℕ} (x : Fin n → Bool) (out : ℕ) (h : n ≤ out) :
    Circuit.eval ⟨[], out⟩ (List.ofFn x) = false := by
  simp only [Circuit.eval, Circuit.wires, List.foldl_nil]
  exact List.getD_eq_default _ _ (by simpa using h)

lemma nonempty_of_computes_setOr {n : ℕ} (S : Finset (Fin n)) (hcard : 2 ≤ S.card)
    (gates : List Gate) (out : ℕ)
    (heval : ∀ x : Fin n → Bool, Circuit.eval ⟨gates, out⟩ (List.ofFn x) = setOr S x) :
    gates ≠ [] := by
  intro hg
  subst gates
  by_cases hout : out < n
  · obtain ⟨x, hx⟩ := setOr_ne_input S hcard ⟨out, hout⟩
    apply hx
    exact (heval x).symm.trans (eval_nil_of_lt x out hout)
  · obtain ⟨x, y, hxy⟩ := setOr_nonconstant S hcard
    apply hxy
    have hx := (heval x).symm.trans (eval_nil_of_le x out (by omega))
    have hy := (heval y).symm.trans (eval_nil_of_le y out (by omega))
    exact hx.trans hy.symm

lemma not_unique_of_cover (gates : List Gate) (ι : Fin 1 → Fin gates.length)
    (hcover : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not →
      ∃ r : Fin 1, ι r = q) :
    ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j := by
  intro i j hi hj
  obtain ⟨ri, hri⟩ := hcover i hi
  obtain ⟨rj, hrj⟩ := hcover j hj
  exact hri.symm.trans ((congrArg ι (Subsingleton.elim ri rj)).trans hrj)

lemma not_cover_of_unique (gates : List Gate) (hne : gates ≠ [])
    (hunique : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j) :
    ∃ κ : Fin 1 → Fin gates.length, ∀ q : Fin gates.length,
      (gates.get q).op = GateOp.not → ∃ r : Fin 1, κ r = q := by
  classical
  by_cases hnot : ∃ q : Fin gates.length, (gates.get q).op = GateOp.not
  · obtain ⟨q, hq⟩ := hnot
    refine ⟨fun _ => q, ?_⟩
    intro j hj
    exact ⟨0, hunique q j hq hj⟩
  · have hlen : 0 < gates.length := by
      cases gates with
      | nil => contradiction
      | cons g gs => simp
    refine ⟨fun _ => ⟨0, hlen⟩, ?_⟩
    intro q hq
    exact False.elim (hnot ⟨q, hq⟩)

noncomputable def binaryPositions (gates : List Gate) : Finset (Fin gates.length) := by
  classical
  exact Finset.univ.filter fun q =>
    ((gates.get q).op = GateOp.and ∨ (gates.get q).op = GateOp.or) ∧
      (gates.get q).inputs.length = 2

lemma mem_binaryPositions (gates : List Gate) (q : Fin gates.length) :
    q ∈ binaryPositions gates ↔
      ((gates.get q).op = GateOp.and ∨ (gates.get q).op = GateOp.or) ∧
        (gates.get q).inputs.length = 2 := by
  classical
  simp [binaryPositions]

lemma binaryPositions_card_le (gates : List Gate) (I : Finset (Fin gates.length))
    (hcover : ∀ q : Fin gates.length,
      ((gates.get q).op = GateOp.and ∨ (gates.get q).op = GateOp.or) ∧
        (gates.get q).inputs.length = 2 → q ∈ I) :
    (binaryPositions gates).card ≤ I.card := by
  apply Finset.card_le_card
  intro q hq
  exact hcover q ((mem_binaryPositions gates q).mp hq)

lemma cost_eq_sum (b : Bool) (gates : List Gate) :
    cost b gates = ∑ q : Fin gates.length, gateCost b (gates.get q) := by
  have hm : List.ofFn (fun q : Fin gates.length => gateCost b (gates.get q)) =
      gates.map (gateCost b) := by
    change List.ofFn ((gateCost b) ∘ gates.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  rw [cost, ← hm, List.sum_ofFn]

lemma cost_false_eq_binaryPositions_card (gates : List Gate) :
    cost false gates = (binaryPositions gates).card := by
  classical
  rw [cost_eq_sum]
  simp [gateCost, binaryPositions]

noncomputable def notPositions (gates : List Gate) : Finset (Fin gates.length) := by
  classical
  exact Finset.univ.filter fun q => (gates.get q).op = GateOp.not

lemma mem_notPositions (gates : List Gate) (q : Fin gates.length) :
    q ∈ notPositions gates ↔ (gates.get q).op = GateOp.not := by
  classical
  simp [notPositions]

lemma cost_true_eq_notPositions_card (gates : List Gate) :
    cost true gates = (notPositions gates).card := by
  classical
  rw [cost_eq_sum]
  simp [gateCost, notPositions]

lemma cost_true_le_one_of_cover (gates : List Gate) (ι : Fin 1 → Fin gates.length)
    (hcover : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not →
      ∃ r : Fin 1, ι r = q) :
    cost true gates ≤ 1 := by
  rw [cost_true_eq_notPositions_card]
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact not_unique_of_cover gates ι hcover i j
    ((mem_notPositions gates i).mp hi) ((mem_notPositions gates j).mp hj)

lemma not_unique_of_cost_true_le_one (gates : List Gate) (hcost : cost true gates ≤ 1) :
    ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j := by
  rw [cost_true_eq_notPositions_card] at hcost
  intro i j hi hj
  exact Finset.card_le_one.mp hcost i ((mem_notPositions gates i).mpr hi)
    j ((mem_notPositions gates j).mpr hj)

lemma cost_false_le_of_cover (gates : List Gate) (I : Finset (Fin gates.length))
    (hcover : ∀ q : Fin gates.length,
      ((gates.get q).op = GateOp.and ∨ (gates.get q).op = GateOp.or) ∧
        (gates.get q).inputs.length = 2 → q ∈ I) :
    cost false gates ≤ I.card := by
  rw [cost_false_eq_binaryPositions_card]
  exact binaryPositions_card_le gates I hcover

lemma not_cover_of_cost_true_le_one (gates : List Gate) (hne : gates ≠ [])
    (hcost : cost true gates ≤ 1) :
    ∃ κ : Fin 1 → Fin gates.length, ∀ q : Fin gates.length,
      (gates.get q).op = GateOp.not → ∃ r : Fin 1, κ r = q :=
  not_cover_of_unique gates hne (not_unique_of_cost_true_le_one gates hcost)

lemma nonconstant_of_no_const {n : ℕ} (gs : List Gate)
    (hno : ∀ p : ℕ, p < gs.length → ∀ c : Bool,
      ¬ ∀ x : Fin n → Bool, vl gs x (n + p) = c) :
    ∀ jr : Fin gs.length, ∃ x y : Fin n → Bool,
      vl gs x (n + jr.val) ≠ vl gs y (n + jr.val) := by
  classical
  intro jr
  by_contra h
  push_neg at h
  exact hno jr.val jr.isLt (vl gs (fun _ => false) (n + jr.val))
    (fun x => h x (fun _ => false))

lemma distinct_of_no_alias {n : ℕ} (gs : List Gate)
    (hno : ∀ p : ℕ, p < gs.length → ∀ w : ℕ, w < n + p →
      ¬ ∀ x : Fin n → Bool, vl gs x (n + p) = vl gs x w) :
    ∀ jr : Fin gs.length, ∀ w : ℕ, w < n + jr.val →
      ∃ x : Fin n → Bool, vl gs x (n + jr.val) ≠ vl gs x w := by
  classical
  intro jr w hw
  exact not_forall.mp (hno jr.val jr.isLt w hw)

lemma clean_binary_distinct_of_no_alias {n : ℕ} (gs : List Gate) (hclean : CleanL n gs)
    (hno : ∀ p : ℕ, p < gs.length → ∀ w : ℕ, w < n + p →
      ¬ ∀ x : Fin n → Bool, vl gs x (n + p) = vl gs x w) :
    ∀ jr : Fin gs.length,
      ((gs.get jr).op = GateOp.and ∨ (gs.get jr).op = GateOp.or) →
      ∃ a b : ℕ, a ≠ b ∧ (gs.get jr).inputs = [a, b] := by
  intro jr hbin
  have hj : gs[jr.val]? = some (gs.get jr) := by simp
  rcases hclean jr.val (gs.get jr) hj with hc | hc
  · rcases hbin with hh | hh
    · have bad : GateOp.and = GateOp.not := hh.symm.trans hc.1
      cases bad
    · have bad : GateOp.or = GateOp.not := hh.symm.trans hc.1
      cases bad
  · obtain ⟨hop, a, b, ha, hb, hin⟩ := hc
    refine ⟨a, b, ?_, hin⟩
    intro hab
    subst b
    apply hno jr.val jr.isLt a ha
    intro x
    rw [vl_gate gs hclean x jr.val (gs.get jr) hj, hin]
    rcases hop with hh | hh <;> rw [hh] <;> simp [GateOp.eval]

lemma clean_liveness_of_raw {n m : ℕ} (gs : List Gate) (out : Fin m → ℕ)
    (hclean : CleanL n gs)
    (hlive : ∀ p : ℕ, p < gs.length →
      (∃ o : Fin m, out o = n + p) ∨
        ∃ q : ℕ, ∃ g : Gate, gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ jr : Fin gs.length, (∃ o : Fin m, out o = n + jr.val) ∨
      ∃ kr : Fin gs.length,
        ((gs.get kr).op = GateOp.not ∧ (gs.get kr).inputs.head? = some (n + jr.val)) ∨
          (((gs.get kr).op = GateOp.and ∨ (gs.get kr).op = GateOp.or) ∧
            n + jr.val ∈ (gs.get kr).inputs) := by
  intro jr
  rcases hlive jr.val jr.isLt with ho | ⟨q, g, hq, hread⟩
  · exact Or.inl ho
  · obtain ⟨hqbound, hget⟩ := List.getElem?_eq_some_iff.mp hq
    refine Or.inr ⟨⟨q, hqbound⟩, ?_⟩
    have hg : gs.get ⟨q, hqbound⟩ = g := hget
    rw [hg]
    rcases hclean q g hq with ⟨hop, w, _, hin⟩ | ⟨hop, _⟩
    · have hw : n + jr.val = w := by simpa [hin] using hread
      exact Or.inl ⟨hop, by simp [hin, hw]⟩
    · exact Or.inr ⟨hop, hread⟩

end PEqualNP.Outside.L_meta_1346

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1346

theorem PEqualNP.Outside.L_meta_1346 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ ic : Fin m, 2 ≤ (S ic).card) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ ι : Fin 1 → Fin gates.length, (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin 1, ι r = q) → ∀ I : Finset (Fin gates.length), (∀ q2 : Fin gates.length, ((gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) → (∃ c : PEqualNP.CircuitLowerBounds.GateOp, (c = PEqualNP.CircuitLowerBounds.GateOp.and ∨ c = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (o1 : Fin m) (x1 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set (ι 0).val ⟨c, []⟩, out o1⟩ (List.ofFn x1) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o1⟩ (List.ofFn x1)) ∨ ∃ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin m → ℕ) (κ : Fin 1 → Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r2 : Fin 1, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧ J.card ≤ I.card ∧ (∀ (o2 : Fin m) (x2 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, x2 v2 = true)) ∧ (∀ jr : Fin gl.length, ∃ xr yr : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, n + jr.val⟩ (List.ofFn xr) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, n + jr.val⟩ (List.ofFn yr)) ∧ (∀ jr2 : Fin gl.length, ∀ wr : ℕ, wr < n + jr2.val → ∃ xr2 : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, n + jr2.val⟩ (List.ofFn xr2) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, wr⟩ (List.ofFn xr2)) ∧ (∀ jr3 : Fin gl.length, (∃ oq : Fin m, ol oq = n + jr3.val) ∨ ∃ kr : Fin gl.length, ((gl.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (gl.get kr).inputs.head? = some (n + jr3.val)) ∨ (((gl.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ n + jr3.val ∈ (gl.get kr).inputs)) ∧ (∀ jr4 : Fin gl.length, ((gl.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ ar br : ℕ, ar ≠ br ∧ (gl.get jr4).inputs = [ar, br]) := by
  classical
  intro n m S hS gates out hok hev ι hι I hI
  by_cases hm : m = 0
  · subst m
    left
    refine ⟨GateOp.and, Or.inl rfl, ?_⟩
    intro o
    exact o.elim0
  · right
    have hnc : ∀ o : Fin m, ∃ x y : Fin n → Bool, setOr (S o) x ≠ setOr (S o) y :=
      fun o => setOr_nonconstant (S o) (hS o)
    have hok' : ∀ g ∈ gates, Ok g := by simpa [Ok] using hok
    obtain ⟨gl, ol, hrep, hmin⟩ := least_many n m I.card (fun o => setOr (S o))
      gates out hok' (fun o x => hev o x) hnc
      (cost_true_le_one_of_cover gates ι hι) (cost_false_le_of_cover gates I hI)
    have hne : gl ≠ [] := nonempty_of_computes_setOr (S ⟨0, Nat.pos_of_ne_zero hm⟩)
      (hS _) gl (ol ⟨0, Nat.pos_of_ne_zero hm⟩) (hrep.2.2.2 _)
    obtain ⟨κ, hκ⟩ := not_cover_of_cost_true_le_one gl hne hrep.2.1
    refine ⟨gl, ol, κ, binaryPositions gl, ?_, hκ, ?_, ?_, hrep.2.2.2, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simpa [Ok] using (clean_nok n gl hrep.1 g hg).1
    · intro q hq
      exact (mem_binaryPositions gl q).mpr hq
    · rw [← cost_false_eq_binaryPositions_card]
      exact hrep.2.2.1
    · exact nonconstant_of_no_const gl (least_no_const hrep hmin hnc)
    · exact distinct_of_no_alias gl (least_no_alias hrep hmin hnc)
    · exact clean_liveness_of_raw gl ol hrep.1 (least_live hrep hmin hnc)
    · exact clean_binary_distinct_of_no_alias gl hrep.1 (least_no_alias hrep hmin hnc)
