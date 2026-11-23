import Mathlib
import PEqualNP.Defs

namespace Live516
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

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

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

abbrev Stat := Bool ⊕ ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
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

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

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
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem cleanGate_nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
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

theorem cleanGate_lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha; simp at ha; subst ha; exact hj
  · rw [h2] at ha; simp at ha; rcases ha with rfl | rfl; exact hj; exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact cleanGate_nok (h p g hp)

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv _ List.mem_cons_self, hv _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv _ List.mem_cons_self, hv _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv _ List.mem_cons_self, rfl⟩
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

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Sum.inr i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, statValid, statVal, wiresFrom]
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
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
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

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero => simp at h; subst h; exact ⟨[], l, rfl, rfl⟩
    | succ p => simp at h; obtain ⟨pre, post, rfl, rfl⟩ := ih p g h; exact ⟨x :: pre, post, rfl, rfl⟩

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) : ℕ → List α → Prop
  | 0, xs => xs = [y]
  | s + 1, xs =>
    (∃ (a : α) (rest : List α) (neg save : Bool), xs.Perm (a :: rest) ∧
      Run inv meet join y s ((if neg then inv a else a) :: kept save a rest)) ∨
    (∃ (a b : α) (rest : List α) (conj ka kb : Bool), xs.Perm (a :: b :: rest) ∧
      Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)))

theorem run_done {α : Type} {inv : α → α} {meet join : α → α → α} {y : α} :
    Run inv meet join y 0 [y] := rfl

theorem run_perm {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}
    {s : ℕ} {xs zs : List α} (p : xs.Perm zs) (h : Run inv meet join y s xs) :
    Run inv meet join y s zs := by
  cases s with
  | zero =>
    change xs = [y] at h
    subst h
    exact List.perm_singleton.1 p.symm
  | succ s =>
    rcases h with ⟨a, rest, neg, save, hp, hr⟩ | ⟨a, b, rest, conj, ka, kb, hp, hr⟩
    · exact Or.inl ⟨a, rest, neg, save, p.symm.trans hp, hr⟩
    · exact Or.inr ⟨a, b, rest, conj, ka, kb, p.symm.trans hp, hr⟩

theorem run_one {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}
    {s : ℕ} {a : α} {rest : List α} (neg save : Bool)
    (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a rest)) :
    Run inv meet join y (s + 1) (a :: rest) :=
  Or.inl ⟨a, rest, neg, save, List.Perm.refl _, h⟩

theorem run_two {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}
    {s : ℕ} {a b : α} {rest : List α} (conj ka kb : Bool)
    (h : Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest))) :
    Run inv meet join y (s + 1) (a :: b :: rest) :=
  Or.inr ⟨a, b, rest, conj, ka, kb, List.Perm.refl _, h⟩

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem run_map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} : ∀ {ws : List α}, Run inv meet join y s ws →
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction s with
  | zero =>
    intro ws h; change ws = [y] at h; subst h; rfl
  | succ s ih =>
    intro ws h
    rcases h with ⟨a, rest, neg, save, hp, hr⟩ | ⟨a, b, rest, conj, ka, kb, hp, hr⟩
    · refine Or.inl ⟨e a, rest.map e, neg, save, ?_, ?_⟩
      · simpa using hp.map e
      · have ih' := ih hr
        have e1 : ((if neg then inv a else a) :: kept save a rest).map e
            = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
          cases neg <;> simp [kept_map, hi]
        rwa [e1] at ih'
    · refine Or.inr ⟨e a, e b, rest.map e, conj, ka, kb, ?_, ?_⟩
      · simpa using hp.map e
      · have ih' := ih hr
        have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
            = (if conj then meet' (e a) (e b) else join' (e a) (e b))
                :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
          cases conj <;> simp [kept_map, hm, hj]
        rwa [e1] at ih'

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def shift (K a : ℕ) : ℕ := if a < K then a else a - 1

def shGate (K : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift K)⟩

def RelD (K : ℕ) (W W' : List Bool) : Prop :=
  W.length = W'.length + 1 ∧ K ≤ W'.length ∧
    ∀ a, a ≠ K → W'.getD (shift K a) false = W.getD a false

theorem relD_wires (K : ℕ) (post : List Gate) : ∀ W W' : List Bool,
    (∀ g ∈ post, K ∉ g.inputs) → RelD K W W' →
    RelD K (wiresFrom post W) (wiresFrom (post.map (shGate K)) W') := by
  induction post with
  | nil => intro W W' _ h; exact h
  | cons g post ih =>
    intro W W' hno h
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [shGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun e => hno g List.mem_cons_self (e ▸ ha))
    have s1 : wiresFrom (g :: post) W
        = wiresFrom post (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl
    have s2 : wiresFrom ((g :: post).map (shGate K)) W'
        = wiresFrom (post.map (shGate K))
          (W' ++ [(shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)]) := rfl
    rw [s1, s2, hv]
    apply ih _ _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    intro a haK
    rcases Nat.lt_trichotomy a W.length with hw | hw | hw
    · have hlt : shift K a < W'.length := by unfold shift; split <;> omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 a haK
    · have he : shift K a = W'.length := by unfold shift; split <;> omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ shift K a := by unfold shift; split <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem del_gate (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ) (f : BFn n)
    (hok : ∀ g' ∈ pre ++ g :: post, Ok g')
    (hno : ∀ g' ∈ post, n + pre.length ∉ g'.inputs) (ho : o ≠ n + pre.length)
    (hev : ∀ x, val (pre ++ g :: post) n o x = f x) :
    HasCircuitSize n f (pre.length + post.length) := by
  refine ⟨⟨pre ++ post.map (shGate (n + pre.length)), shift (n + pre.length) o⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hok g' (List.mem_append_left _ h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hok g0 (List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨this.1, by simpa [shGate] using this.2⟩
  · simp [Circuit.size]
  · intro x
    rw [← hev x]
    show (wiresFrom (pre ++ post.map (shGate (n + pre.length))) (List.ofFn x)).getD
      (shift (n + pre.length) o) false = _
    unfold val
    have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
        (wiresFrom pre (List.ofFn x) ++
          [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
      rw [wiresFrom_append]; rfl
    have hl : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
      rw [length_wiresFrom]; simp
    rw [h1, wiresFrom_append]
    refine (relD_wires (n + pre.length) post _ _ hno ⟨by simp, by omega, ?_⟩).2.2 o ho
    intro a ha
    by_cases hlt : a < n + pre.length
    · have : shift (n + pre.length) a = a := by simp [shift, hlt]
      rw [this, List.getD_append _ _ _ _ (by omega)]
    · have : shift (n + pre.length) a = a - 1 := by simp [shift, hlt]
      rw [this, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩
        have := cleanGate_lt (hcl q g' hg') _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp; rw [hg] at hg'; cases hg'; exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (invF (n := n)) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1; omega
    exact run_perm (hperm.map (val gs n)) run_done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨cleanGate_lt (hcl p g hg) a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (cleanGate_lt (hcl p g hg))
    have hnd0 := nodup_liveList gs n o p
    have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
        val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
        Run (invF (n := n)) meetF joinF (val gs n o) (d + 1)
          ((liveList gs n o p).map (val gs n)) := by
      intro j neg hmem hval
      have hj := hin j ((hmem j).2 rfl)
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hj
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hj h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
          simp only [decide_eq_true_eq]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hj, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have IH' := run_perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact run_perm (hp1.map (val gs n)).symm (run_one neg _ IH')
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
    · apply single j true
      · intro a; simp [hinp]
      · funext x; rw [hvg x, hop, hinp]; simp [GateOp.eval]
    · by_cases hjk : j = k
      · subst hjk
        apply single j false
        · intro a; simp [hinp]
        · funext x; rw [hvg x, hinp]; rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
      · have hjm := hin j (by simp [hinp])
        have hkm := hin k (by simp [hinp])
        have hke : k ∈ (liveList gs n o p).erase j :=
          (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
        have hp1 : (liveList gs n o p).Perm
            (j :: k :: ((liveList gs n o p).erase j).erase k) :=
          (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
        have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
            a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
          intro a; rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
              (kept (decide (Live gs o (p + 1) k)) k
                (((liveList gs n o p).erase j).erase k))) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
            · rw [mem_kept, mem_kept]
              rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
              · exact hnew j hjm h.symm
              · exact hnew k hkm h.symm
              · exact hnew _ ((hmr _).1 h).2.2 rfl
            · rw [hmr]; simp
            · rw [mem_kept, hmr]
              rintro (⟨_, h⟩ | h)
              · exact hjk h
              · exact h.2.1 rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
            simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                · by_cases hak : a = k
                  · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                  · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hjm, fun _ => h1⟩
              · exact Or.inr ⟨hkm, fun _ => h1⟩
              · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
        have IH' := run_perm (hp2.map (val gs n)) IH
        have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
            then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
          funext x; rw [hvg x, hinp]; rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        rw [List.map_cons, kept_map, kept_map, hval] at IH'
        exact run_perm (hp1.map (val gs n)).symm (run_two _ _ _ IH')

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  classical
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length = t ∧
    ∀ x, val gs n o x = f x
  have hP : ∀ t, HasCircuitSize n f t → ∃ t', t' ≤ t ∧ P t' := by
    intro t ht
    obtain ⟨gs, o, hcl, hsz, hev⟩ := clean_of n f t hnc ht
    exact ⟨gs.length, hsz, gs, o, hcl, rfl, hev⟩
  obtain ⟨t0, ht0, hPt0⟩ := hP s h
  have hex : ∃ t, P t := ⟨t0, hPt0⟩
  have hmin : Nat.find hex ≤ t0 := Nat.find_min' hex hPt0
  obtain ⟨gs, o, hcl, hlen, hev⟩ := Nat.find_spec hex
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have ho : o < n + gs.length := by
    by_contra hge
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hev y, ← hev y']
    unfold val
    rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
      List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)]
  have hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra hcon
    push Not at hcon
    obtain ⟨hpo, hno⟩ := hcon
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
    obtain ⟨pre, post, rfl, hpl⟩ := split_at gs p g hg
    have hsz := del_gate n pre g post o f hok (by
      intro g' hg'
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg'
      have := hno (pre.length + 1 + q) g' (by
        rw [List.getElem?_append_right (by omega)]
        have e : pre.length + 1 + q - pre.length = q + 1 := by omega
        rw [e]; simpa using hq)
      rw [hpl]; exact this) (by rw [hpl]; exact fun e => hpo e.symm) hev
    obtain ⟨t', ht', hPt'⟩ := hP _ hsz
    have := Nat.find_min' hex hPt'
    simp at hlen
    omega
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact run_live n gs o hcl ho hnd gs.length 0 (by omega)

theorem run_len {α : Type} {inv : α → α} {meet join : α → α → α} {y : α} :
    ∀ {s : ℕ} {xs : List α}, Run inv meet join y s xs → xs.length ≤ s + 1 := by
  intro s
  induction s with
  | zero => intro xs h; change xs = [y] at h; subst h; simp
  | succ s ih =>
    intro xs h
    rcases h with ⟨a, rest, neg, save, hp, hr⟩ | ⟨a, b, rest, conj, ka, kb, hp, hr⟩
    · have hh := ih hr
      have hl := hp.length_eq
      cases save <;> simp_all [kept] <;> omega
    · have hh := ih hr
      have hl := hp.length_eq
      cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y : Nat} : ∀ {s : Nat} {xs : List Nat}, NatRun m y s xs →
    ∀ (i j : Nat), m.testBit i = m.testBit j →
    (∀ w ∈ xs, w.testBit i = w.testBit j) → y.testBit i = y.testBit j := by
  intro s
  induction s with
  | zero =>
    intro xs h i j _ hw; change xs = [y] at h; subst h; exact hw y (by simp)
  | succ s ih =>
    intro xs h i j hm hw
    rcases h with ⟨a, rest, neg, save, hp, hr⟩ | ⟨a, b, rest, conj, ka, kb, hp, hr⟩
    · apply ih hr i j hm
      have ha : a.testBit i = a.testBit j := hw a (hp.mem_iff.2 List.mem_cons_self)
      intro w hmem
      rw [List.mem_cons, mem_kept] at hmem
      rcases hmem with rfl | ⟨_, rfl⟩ | hr'
      · cases neg <;> simp [ha, hm]
      · exact ha
      · exact hw w (hp.mem_iff.2 (List.mem_cons_of_mem _ hr'))
    · apply ih hr i j hm
      have ha : a.testBit i = a.testBit j := hw a (hp.mem_iff.2 List.mem_cons_self)
      have hb : b.testBit i = b.testBit j := hw b (hp.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self))
      intro w hmem
      rw [List.mem_cons, mem_kept, mem_kept] at hmem
      rcases hmem with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | hr'
      · cases conj <;> simp [ha, hb]
      · exact ha
      · exact hb
      · exact hw w (hp.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr')))

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask,lo,Nat.testBit_two_pow_sub_one,show i < k+k by omega,show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (run_perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (run_perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply run_perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem next_complete {k s ws} (h : NatRun (mask k) (goal k) (s + 1) ws)
    (zs : List Nat) (p : ws.Perm zs) (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-zs.length) zs f = true := by
  rcases h with ⟨a, rest, neg, save, hp, hr⟩ | ⟨a, b, rest, conj, ka, kb, hp, hr⟩
  · exact next_one (hp.symm.trans p) hr f hf
  · exact next_two (hp.symm.trans p) hr f hf

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

def blockWord (d : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | q::r, w => ((w >>> (d*q)) &&& lo d) ||| (blockWord d r w <<< d)

theorem block_hom (d : Nat) (qs : List Nat) (a b : Nat) :
    blockWord d qs (a &&& b) = (blockWord d qs a &&& blockWord d qs b) ∧
    blockWord d qs (a ||| b) = (blockWord d qs a ||| blockWord d qs b) ∧
    blockWord d qs (a ^^^ b) = (blockWord d qs a ^^^ blockWord d qs b) := by
  induction qs with
  | nil => simp [blockWord]
  | cons q qs ih =>
    refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro j <;>
      by_cases hj : d ≤ j <;>
      simp [blockWord, lo, Nat.testBit_shiftLeft, hj, ih, Nat.not_lt_of_ge, Nat.lt_of_not_ge]

theorem block_run {s ws k} (h : NatRun (mask k) (goal k) s ws)
    (d : Nat) (qs : List Nat) (hm : blockWord d qs (mask k) = mask k)
    (hg : blockWord d qs (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (blockWord d qs)) := by
  rw [← hg]
  exact run_map _ (fun a => (block_hom d qs a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (block_hom d qs a b).1) (fun a b => (block_hom d qs a b).2.1) h

theorem bits_le {m y : Nat} : ∀ {s : Nat} {ws : List Nat}, NatRun m y s ws →
    ws.length = s + 1 → ∀ (i j : Nat),
    (∀ a ∈ ws, a.testBit i ≤ a.testBit j) → y.testBit i ≤ y.testBit j := by
  intro s
  induction s with
  | zero =>
    intro ws h _ i j hw; change ws = [y] at h; subst h; exact hw y (by simp)
  | succ s ih =>
    intro ws h hl i j hw
    rcases h with ⟨a, rest, neg, save, hp, hr⟩ | ⟨a, b, rest, conj, ka, kb, hp, hr⟩
    · have hh := run_len hr
      have hpl := hp.length_eq
      cases save <;> simp [kept] at hh hpl hl <;> omega
    · have hh := run_len hr
      have hpl := hp.length_eq
      cases ka <;> cases kb <;> simp [kept] at hh hpl hl <;> try omega
      apply ih hr (by simp [kept]; omega) i j
      have ha : a.testBit i ≤ a.testBit j := hw a (hp.mem_iff.2 List.mem_cons_self)
      have hb : b.testBit i ≤ b.testBit j := hw b (hp.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self))
      intro w hmem
      simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at hmem
      rcases hmem with rfl | ht
      · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;> grind
      · exact hw w (hp.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)))

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers,he,required_up h he]
  · simp [covers,he,required h]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y : Nat} (v : Nat → Nat)
    (hand : ∀ a b, v (a &&& b) ≤ v a + v b) (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    ∀ {s : Nat} {ws : List Nat}, NatRun m y s ws → ws.length = s + 1 →
    v y ≤ (ws.map v).sum := by
  intro s
  induction s with
  | zero =>
    intro ws h _; change ws = [y] at h; subst h; simp
  | succ s ih =>
    intro ws h hl
    rcases h with ⟨a, rest, neg, save, hp, hr⟩ | ⟨a, b, rest, conj, ka, kb, hp, hr⟩
    · have hh := run_len hr
      have hpl := hp.length_eq
      cases save <;> simp [kept] at hh hpl hl <;> omega
    · have hh := run_len hr
      have hpl := hp.length_eq
      cases ka <;> cases kb <;> simp [kept] at hh hpl hl <;> try omega
      have ih' := ih hr (by simp [kept]; omega)
      rw [(hp.map v).sum_eq]
      simp only [List.map_cons, List.sum_cons]
      cases conj <;> simp [kept] at ih' ⊢
      · have := hor a b; omega
      · have := hand a b; omega

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound (eval6 a b c d e f) _ _ h hl
  · intro v w
    simpa only [eval6,Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact run_one false false ih

def barrier (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (act : Nat → Nat → Nat → Nat) (wits : Nat → Nat)
    (rot : Nat → List Nat → List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s+1, i =>
    let ws := S (s+1) i
    !(next (mask k) (s+2-ws.length) ws fun tag zs =>
        covers k s zs && (
          let v := act (s+1) i tag
          if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
          else !(v/24 < N s && (rot (v/2 % 12) zs).isPerm (S s (v/24)))))

theorem barrier_sound {k S N act wits rot} {s i} (hb : barrier k S N act wits rot s i = true)
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero =>
    change S 0 i = [goal k] at h
    simp [barrier, h] at hb
  | succ s =>
    by_contra! hn
    let F (tag : Nat) (zs : List Nat) := covers k s zs && (
      let v := act (s+1) i tag
      if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
      else !(v/24 < N s && (rot (v/2 % 12) zs).isPerm (S s (v/24))))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F, covers_ok hz, Bool.true_and]
      split
      · simp [scoreCheck_no hz]
      · simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
        intro hj
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact hn s (by omega) _ hj (run_perm p (hr _ hz))
    have hN := next_complete h _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem barrier_all {k S N act wits rot} {cap : Nat}
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, barrier k S N act wits rot s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := barrier_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h


def rows516 : List ℕ := [3, 86, 86, 88, 88, 88, 88, 1, 4, 8, 22, 22, 3, 169, 169, 164, 164, 164, 164, 2, 8, 4, 41, 41, 3, 86, 86, 88, 88, 88, 88, 1, 4, 8, 70, 70, 3, 169, 169, 164, 164, 164, 164, 2, 8, 4, 137, 137, 3, 86, 86, 100, 100, 100, 100, 1, 16, 32, 22, 22, 3, 169, 169, 152, 152, 152, 152, 2, 32, 16, 41, 41, 3, 86, 86, 100, 100, 100, 100, 1, 16, 32, 82, 82, 3, 169, 169, 152, 152, 152, 152, 2, 32, 16, 161, 161, 3, 86, 86, 148, 148, 148, 148, 1, 64, 128, 70, 70, 3, 169, 169, 104, 104, 104, 104, 2, 128, 64, 137, 137, 3, 86, 86, 148, 148, 148, 148, 1, 64, 128, 82, 82, 3, 169, 169, 104, 104, 104, 104, 2, 128, 64, 161, 161, 7, 87, 94, 89, 90, 92, 120, 5, 12, 10, 23, 30, 11, 171, 173, 166, 165, 172, 180, 10, 12, 5, 43, 45, 7, 87, 94, 89, 90, 92, 216, 5, 12, 10, 71, 78, 11, 171, 173, 166, 165, 172, 228, 10, 12, 5, 139, 141, 19, 87, 118, 101, 102, 116, 108, 17, 48, 34, 23, 54, 35, 171, 185, 154, 153, 184, 156, 34, 48, 17, 43, 57, 19, 87, 118, 101, 102, 116, 228, 17, 48, 34, 83, 114, 35, 171, 185, 154, 153, 184, 216, 34, 48, 17, 163, 177, 67, 87, 214, 149, 150, 212, 156, 65, 192, 130, 71, 198, 131, 171, 233, 106, 105, 232, 108, 130, 192, 65, 139, 201, 67, 87, 214, 149, 150, 212, 180, 65, 192, 130, 83, 210, 131, 171, 233, 106, 105, 232, 120, 130, 192, 65, 163, 225]

def xs516 : List ℕ := [0xe1748be1748be1748be1748be1748be1748bc07081c07081c07081c07081c07081c07081, 0x48be1748be1748be1748be1748be1748be17081c07081c07081c07081c07081c07081c07, 0x7e040c7e00007e040c7eb7cda7b7cda700007e000c7e00007e000c7e278d06278d06, 0x7e000c7e04007e000c7e040da7b7cda7b7c07e000c7e00007e000c7e000d06278d06278, 0x40c7e00007eb7cda7b7cda700007e040c7e000c7e00007e278d06278d0600007e000c7e, 0xc7e04007e000da7b7cda7b7c07e000c7e040c7e00007e000d06278d0627807e000c7e000, 0xb7cda7b7cda7040c7e00007e040c7e00007e278d06278d06000c7e00007e000c7e00007e, 0xda7b7cda7b7cc7e04007e000c7e04007e000d06278d06278c7e00007e000c7e00007e000]

abbrev f516 : BFn 8 := (fun x : Fin 8 → Bool => (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 1) || (x 0 && x 4) || (x 4 && x 5) || (x 5 && x 1) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 1))

theorem rows516_len : rows516.length = 288 := by decide +kernel

theorem enc_inputs516 :
    (List.ofFn fun (i : Fin 8) => (fun x : Fin 8 → Bool => x i)).map (fun a => encL a rows516)
      = xs516 := by decide +kernel

theorem enc_goal516 : encL f516 rows516 = goal 144 := by decide +kernel

theorem mask516 : mask 144 = 2 ^ rows516.length - 1 := by decide +kernel

theorem proper_fail516 : ∀ zs ∈ xs516.sublists, zs ≠ xs516 →
    (cov 144 zs &&& lo 144) ≠ lo 144 := by decide +kernel

theorem no_sub516 (noRunFull : ∀ s ≤ 11, ¬ NatRun (mask 144) (goal 144) s xs516) :
    ∀ s ≤ 11, ∀ zs : List ℕ, zs.Sublist xs516 → NatRun (mask 144) (goal 144) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xs516
  · subst e; exact noRunFull s hs h
  · exact proper_fail516 zs (List.mem_sublists.2 hz) e (required h)


theorem main516 (noRunFull : ∀ s ≤ 11, ¬ NatRun (mask 144) (goal 144) s xs516) :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 1) || (x 0 && x 4) || (x 4 && x 5) || (x 5 && x 1) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 1)) s → 12 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run f516 ⟨fun _ => false, fun _ => true, by decide⟩ s h
  have hr : NatRun (mask 144) (encL f516 rows516) s' (ws.map fun a => encL a rows516) :=
    run_map (fun a : BFn 8 => encL a rows516)
      (fun a => by rw [mask516]; exact encL_inv a rows516)
      (fun a b => encL_and a b rows516) (fun a b => encL_or a b rows516) hrun
  rw [enc_goal516] at hr
  refine no_sub516 noRunFull s' (by omega) _ ?_ hr
  rw [← enc_inputs516]
  exact hsub.map _


def t0 : Nat := 0x7e040c7e00007e040c7eb7cda7b7cda700007e000c7e00007e000c7e278d06278d06

def t1 : Nat := 0x40c7e00007eb7cda7b7cda700007e040c7e000c7e00007e278d06278d0600007e000c7e

def t2 : Nat := 0x7e000c7e04007e000c7e040da7b7cda7b7c07e000c7e00007e000c7e000d06278d06278

def t3 : Nat := 0x1d9b3cdd9b7c1d9b3cdd9b7cc00040c00040178278d78278178278d78278c00000c00000

def t4 : Nat := 0x48be1748be1748be1748be1748be1748be17081c07081c07081c07081c07081c07081c07

def t5 : Nat := 0xb7cda7b7cda7040c7e00007e040c7e00007e278d06278d06000c7e00007e000c7e00007e

def t6 : Nat := 0xe1748be1748be1748be1748be1748be1748bc07081c07081c07081c07081c07081c07081

def t7 : Nat := 0xe264c3226483e264c32264833fffbf3fffbfe87d87287d87e87d87287d873fffff3fffff

def t8 : Nat := 0x964d7e92497eb7cde7b7cda704007e040c7e000c7e00007e278d06278d0600007e000c7e

def t9 : Nat := 0xdffb7cdffb7cdffb7cdffb7cc7e040c7e040d7e278d7e278d7e278d7e278c7e000c7e000

def t10 : Nat := 0xf7ede7b7eda7de7f7eda7b7e07ec7ec7e07ee7ed0627ed06d06e7ed0627e07ec7ec7e07e

def t11 : Nat := 0xdaff37daff374cbe5748be174cbe5748be17081c07081c07081c07081c07081c07081c07

def t12 : Nat := 0x6db6db6db6dbc3ec3e07e07ec3ec3e07e07ef7ef7ef7ef7ec7ec7e07e07ec7ec7e07e07e

def t13 : Nat := 0xc7e04007e000da7b7cda7b7c07e000c7e040c7e00007e000d06278d0627807e000c7e000

def t14 : Nat := 0xd7e96497e924de7b7cda7b7c07e040c7e040c7e00007e000d06278d0627807e000c7e000

def t15 : Nat := 0xffffffffffffc7ec7e07e07ec7ec7e07e07ef7ef7ef7ef7ec7ec7e07e07ec7ec7e07e07e

def t16 : Nat := 0xf37daff37dafe574cbe1748be574cbe1748bc07081c07081c07081c07081c07081c07081

def t17 : Nat := 0x9249249249243c13c1f81f813c13c1f81f81081081081081381381f81f81381381f81f81

def t18 : Nat := 0x4cbe5748be17daff37daff3748be174cbe57081c07081c07081c07081c07081c07081c07

def t19 : Nat := 0xdefb7cdafb7cdffb74dffb34c7e04047e040d06278d06278c7e00007e000c7e00007e000

def t20 : Nat := 0xcffa544ffa14dafb7cdafb7c47e000c7e040c7e00007e000d06278d0627807e000c7e000

def t21 : Nat := 0xffffb7ffffb744ac7e00a07e44ac7e00a07e278d06278d06000c7e00007e000c7e00007e

def t22 : Nat := 0xda7b7cda7b7cc7e04007e000c7e04007e000d06278d06278c7e00007e000c7e00007e000

def t23 : Nat := 0xe574cbe1748bf37daff37dafe1748be574cbc07081c07081c07081c07081c07081c07081

def t24 : Nat := 0xf7eda7b7eda74c3e7e483a7e04ac7e40a07e278d06278d06000c7e00007e000c7e00007e

def t25 : Nat := 0xdafb7cdafb7ccffa544ffa14c7e04047e000d06278d06278c7e00007e000c7e00007e000

def t26 : Nat := 0x2694cbe6948b3b0ff73b0ff7e6948b2694cb079081c790811012f91012f9c79081079081

def t27 : Nat := 0xc7e000c7e040c7f008c7f048db7b7cdb7b7cc7e000c7e000c7e000c7e000d06278d06278

def t28 : Nat := 0xdb7b7cdb7b7cc7f048c7f008c7e040c7e000d06278d06278c7e000c7e000c7e000c7e000

def t29 : Nat := 0xe7f4cbe7f48bfb7ffffb7fffe7f48be7f4cbc7f081c7f081d072f9d072f9c7f081c7f081

def t30 : Nat := 0x8c4f008c4fb34d96b74196b34d96b74196d06efed06efef7ef86f7e386f7ef86f7e386

def t31 : Nat := 0xa04044a00000a04044ab34da7b34da7000000000000000000000000000000000000

def t32 : Nat := 0xdafb7cdafb7cc7e04047e000cffa544ffa14d06278d06278c7e00007e000c7e00007e000

def t33 : Nat := 0xfb7fb7fb7fb744a44a00a00a44a44a00a00a000000000000000000000000000000000000

def t34 : Nat := 0xb7eda7f7eda704ac7e40a07e4c3e7e483a7e278d06278d06000c7e00007e000c7e00007e

def t35 : Nat := 0xe5f4cbe1f48bfb7fbffb7fbfe1f48be5f4cbc07081c07081c07081c07081c07081c07081

def t36 : Nat := 0xf7ede7b7eda7de7f7eda7b7e04ac7e44a07e278d06278d06000c7e00007e000c7e00007e

def t37 : Nat := 0xfb7fbffb7fbfe5f4cbe1f48be5f4cbe1f48bc07081c07081c07081c07081c07081c07081

def t38 : Nat := 0x3ec7ec7e03eb02da7702de7da7b02de770207ec7ec7e07e206d06e06d06d06206d06e06

def t39 : Nat := 0x8fd2184fd2582188fd2584fdfc1381381fc11f92f9df92f92f91f92f9df9f81381381f81

def t40 : Nat := 0x56b92c56b92ce578f5e174f5e578f5e174f5e7fd87e7fd87c07cffc070ffc07cffc070ff

def t41 : Nat := 0xdaff7fdaff7fcffe574ffe17cffe574ffe17d87e7fd87e7fcffc070ffc07cffc070ffc07

def t42 : Nat := 0xcffe574ffe17daff7fdaff7f4ffe17cffe57cffc070ffc07d87e7fd87e7f0ffc07cffc07

def t43 : Nat := 0xe97e9fe97e9fe1f48be1f48be1f48be1f48bc07081c07081c07081c07081c07081c07081

def t44 : Nat := 0xe1f48be1f48be97e9fe97e9fe1f48be1f48bc07081c07081c07081c07081c07081c07081

def t45 : Nat := 0xa946d3a946d31a870a1e8b0a1a870a1e8b0a1802781802783f83003f8f003f83003f8f00

def t46 : Nat := 0xa9ca9ca9ca9ca9ca9ca9ca9ca9ca9ca9ca9cc86c86c86c86c86c86c86c86c86c86c86c86

def t47 : Nat := 0x563563563563563563563563563563563563379379379379379379379379379379379379

def t48 : Nat := 0x258483258483381fbff81fff381fbff81fff2f9d872f9d87381ffff81fff381ffff81fff

def t49 : Nat := 0x1e8b741e8b741e8b741e8b741e8b741e8b743f8f7e3f8f7e3f8f7e3f8f7e3f8f7e3f8f7e

def t50 : Nat := 0x381fbff81fff258483258483f81fff381fbf381ffff81fff2f9d872f9d87f81fff381fff

def t51 : Nat := 0x483258483258fbf381ffff81fbf381ffff81d872f9d872f9fff381ffff81fff381ffff81

def t52 : Nat := 0x26040c2600007e00007e040c26000026000006000c0600007e00007e000c06000006

def t53 : Nat := 0xb7cdffb7cdff040c7e040c7eb7cdffb7cdff278d7e278d7e000c7e000c7e278d7e278d7e

def t54 : Nat := 0x40040000000040040924924924924000000000000000000000000000000000000

def t55 : Nat := 0x7e07ec7ec7e07e07ec7ec7effffffffffff07e07ec7ec7e07e07ec7ec7ef7ef7ef7ef7e

def t56 : Nat := 0xda7b7cde7b7cc7e04007e040d7e96497e924d06278d06278c7e00007e000c7e00007e000

def t57 : Nat := 0xe1748be574cbe1748be574cbf37daff37dafc07081c07081c07081c07081c07081c07081

def t58 : Nat := 0x16000c16000016000c16008c07008c07000006000c06000006000c06000c06000c06

def t59 : Nat := 0x48be7f4cbe7f48be7f4cbe7fffffb7ffffb7081c7f081c7f081c7f081c7f2f9d072f9d07

def t60 : Nat := 0xdb7b7cdb7b7cc7e040c7e000c7f048c7f008d06278d06278c7e000c7e000c7e000c7e000

def t61 : Nat := 0x4004000000007c00087c07c00087c000000000000000000078000078078000078000

def t62 : Nat := 0xc7e07e07ec7eda7b7ede7f7eb7eda7f7ede7c7e07e07ec7ed0627ed06e7e27ed06e7ed06

def t63 : Nat := 0xa00040a00000a00040aa14483a14483000000000000000000000000000000000000

def t64 : Nat := 0xe174ffe57cffe174ffe57cfff7fdaff7fdafc070ffc07cffc070ffc07cffe7fd87e7fd87

def t65 : Nat := 0xfb7ffffb7fffc7e44a07e00ac7e44a07e00ad06278d06278c7e00007e000c7e00007e000

def t66 : Nat := 0xe1f48be1f48be1f48be1f48be97e9fe97e9fc07081c07081c07081c07081c07081c07081

def t67 : Nat := 0xda7b7eda7f7ec7e04a07e40ae7e4c3a7e483d06278d06278c7e00007e000c7e00007e000

def t68 : Nat := 0xb741e8b741e8b741e8b741e8b741e8b741e8f7e3f8f7e3f8f7e3f8f7e3f8f7e3f8f7e3f8

def t69 : Nat := 0x403403403403403403403403403403403403001001001001001001001001001001001001

def t70 : Nat := 0xe9fe9fe9fe9fe9fe9fe9fe9fe9fe9fe9fe9fc87c87c87c87c87c87c87c87c87c87c87c87

def t71 : Nat := 0xf81fff381fbff81fff381fbf258483258483f81fff381ffff81fff381fff2f9d872f9d87

def t72 : Nat := 0xb7cda7b7cde7040c7e04007e964d7e92497e278d06278d06000c7e00007e000c7e00007e

def t73 : Nat := 0x2584832584c3381fbffc1fffba5fbffa5fff2f9d872f9d87381ffff81fff381ffff81fff

def t74 : Nat := 0x48be174cbe5748be174cbe57daff37daff37081c07081c07081c07081c07081c07081c07

def t75 : Nat := 0xc7e04007e040da7b7cde7b7c97e924d7e964c7e00007e000d06278d0627807e000c7e000

def t76 : Nat := 0x204040200003e000c7e300da7b00da7000006000c0600007e000c7e200d06200d06

def t77 : Nat := 0x2584ff258cff381ffffc1fffbfdfbfffdfff2f9dff2f9dff381ffff81fff3f9fffff9fff

def t78 : Nat := 0x40c40000058040058b7cda5b3c9a5000000000c00000078000078278d00278100

def t79 : Nat := 0xfbf381ffff81483258483258ffff81fbf381fff381ffff81d872f9d872f9ffff81fff381

def t80 : Nat := 0xb7cda7b7cda7040c7e000c7e340dffb00dff278d06278d06000c7e000c7e200d7e200d7e

def t81 : Nat := 0xb7cdb7b7cdb7040c7e000c7e048c7f008c7f278d06278d06000c7e000c7e000c7e000c7e

def t82 : Nat := 0xb7cdafb7cdaf040c7e00047ea54cffa144ff278d06278d06000c7e00007e000c7e00007e

def t83 : Nat := 0xc7e44a07e00afb7ffffb7fff07e00ac7e44ac7e00007e000d06278d0627807e000c7e000

def t84 : Nat := 0x25848b25848b381fbff81fffb95fbff95fff2f9d872f9d87381ffff81fff381ffff81fff

def t85 : Nat := 0x48be1f48be1f48be1f48be1fe9fe97e9fe97081c07081c07081c07081c07081c07081c07

def t86 : Nat := 0xc7e04a07e40ada7b7eda7f7ea7e483e7e4c3c7e00007e000d06278d0627807e000c7e000

def t87 : Nat := 0x204044200003e040c7eb24da7b24da7000006000c0600007e000c7e200d06200d06

def t88 : Nat := 0x40c00000058000058b7cd81b3c181000000000c00000078000078278d00278100

def t89 : Nat := 0xfbf3ffffffff48327e4c3e7effffa7ffffa7fff3ffffffffd872ffd87effffff87ffff87

def t90 : Nat := 0xb7cda7b7cda7040c7ec0007e1c1f7ed81b7e278d06278d06000c7ec0007e100e7ed0027e

def t91 : Nat := 0xc7e04047e000dafb7cdafb7c4ffa14cffa54c7e00007e000d06278d0627807e000c7e000

def t92 : Nat := 0x25a48365a48338bfbff8bfff783fbff83fff2f9d872f9d87381ffff81fff381ffff81fff

def t93 : Nat := 0xc7e040c7e000db7b7cdb7b7cc7f008c7f048c7e000c7e000d06278d06278c7e000c7e000

def t94 : Nat := 0x25e483e5e483397fbff97ffff87fbff87fff2ffd87effd87387ffff87ffff87ffff87fff

def t95 : Nat := 0x8403008403081e17481e17081e17481e17081c07081c07081c07081c07081c07081c07

def t96 : Nat := 0x6dbe976dbe9778bfbff8bfff78bfbff8bfff2f9d872f9d87381ffff81fff381ffff81fff

def t97 : Nat := 0x7e000c3e00007e000c3e25848325848300007e000c7e00007e000c7e278d06278d06

def t98 : Nat := 0xf81fff3c1ffff81fff3c1fffb7cda7b7cda7f81fff381ffff81fff381fff2f9d872f9d87

def t99 : Nat := 0x20148be0148b210483210483e0148b20148b001081c01081001081001081c01081001081

def t100 : Nat := 0xf97fbff97fffe5f48be5f48bf97ffff97fbff87ffff87fffeffd87effd87f87ffff87fff

def t101 : Nat := 0x81e3f481e7f258483258483481e7f081e3f081c7f081c7f2f9d072f9d07081c7f081c7f

def t102 : Nat := 0xb7cdb7b7cdb7048c7f008c7f040c7e000c7e278d06278d06000c7e000c7e000c7e000c7e

def t103 : Nat := 0xb7cdafb7cdafa54cffa144ff040c7e00047e278d06278d06000c7e00007e000c7e00007e

def t104 : Nat := 0xe9fe97e9fe9748be1f48be1f48be1f48be1f081c07081c07081c07081c07081c07081c07

def t105 : Nat := 0xe7e4c3a7e483da7f7eda7b7e07e40ac7e04ac7e00007e000d06278d0627807e000c7e000

def t106 : Nat := 0x381fbff81fffa5c483a5c483f81fff381fbf381ffff81fff2f9d872f9d87f81fff381fff

def t107 : Nat := 0xda7b7cda7b7cc7e040c7e000dff340dffb00d06278d06278c7e000c7e000d7e200d7e200

def t108 : Nat := 0xda7b7cda7b7cc7e04007ec00f7e1c1b7ed81d06278d06278c7e00007ec00e7e10027ed00

def t109 : Nat := 0xb7cde7b7cda7964d7e92497e040c7e04007e278d06278d06000c7e00007e000c7e00007e

def t110 : Nat := 0xc7f048c7f008db7b7cdb7b7cc7e000c7e040c7e000c7e000d06278d06278c7e000c7e000

def t111 : Nat := 0x3d9fbffd9fff3d9fbffd9ffff81ffff81fff3f9fffff9fff3f9fffff9ffff81ffff81fff

def t112 : Nat := 0xe374cbe3748be374cbe3748be7f48be7f48bc07081c07081c07081c07081c7f081c7f081

def t113 : Nat := 0xcafe574afe17cafe574afe174ffe174ffe17c87c07087c07c87c07087c070ffc070ffc07

def t114 : Nat := 0x483200483200fbf381fbf381483200483200d87281d87281fff381fff381d87281d87281

def t115 : Nat := 0xdffb7cdffb7cc7e040c7e040dffb7cdffb7cd7e278d7e278c7e000c7e000d7e278d7e278

def t116 : Nat := 0xda7b7ede7f7ec7e07e07ec7ef7ede7b7eda7d0627ed06e7ec7e07e07ec7ee7ed0627ed06

def t117 : Nat := 0x7ec7ec7ec7eb7edfff7edffffffffffffff07ec7ec7ec7e27ed7ee7ed7ef7ef7ef7ef7e

def t118 : Nat := 0x36040c3600007e000c7e048c27008c27000006000c0600007e000c7e000c06000c06

def t119 : Nat := 0xc7e040c7e040dffb7cdffb7cdffb7cdffb7cc7e000c7e000d7e278d7e278d7e278d7e278

def t120 : Nat := 0xc16000c16008c17008c17008c17008c17000c06000c06000c06000c06000c06000c06

def t121 : Nat := 0x4cbe7f48be7fffffb7ffffb748be7f4cbe7f081c7f081c7f2f9d072f9d07081c7f081c7f

def t122 : Nat := 0x4004004000007c04087c97c92497c924000000000000000078000078078000078000

def t123 : Nat := 0x26040c6600007e04007e964d26924926000006000c0600007e00007e000c06000006

def t124 : Nat := 0x2e040c2e00007e00047ea54ca7a144a7000006000c0600007e00007e000c06000006

def t125 : Nat := 0x40a00040aa1448ba1448ba1448ba1448b000000000000000000000000000000000000

def t126 : Nat := 0xe57cffe174fff7fdaff7fdafe174ffe57cffc07cffc070ffe7fd87e7fd87c070ffc07cff

def t127 : Nat := 0x4a04044a00007e040c7eb7cda7b7cda7000000000000000078000078078000078000

def t128 : Nat := 0xdb7b7cdb7b7cc7f048c7f008c7f048c7f008d06278d06278c7e000c7e000c7e000c7e000

def t129 : Nat := 0x48ba1448ba1448ba1448ba1448ba1448ba14000000000000000000000000000000000000

def t130 : Nat := 0xfb7ffffb7fffc7e44a07e40ae7e4cba7e48bd06278d06278c7e00007e000c7e00007e000

def t131 : Nat := 0xe1f48be1f48be9fe9fe9fe9fe9fe9fe9fe9fc07081c07081c07081c07081c07081c07081

def t132 : Nat := 0xdafb7cdafb7ccffa544ffa14cffa544ffa14d06278d06278c7e00007e000c7e00007e000

def t133 : Nat := 0xda7f7eda7f7ee7e4cba7e48be7e4cba7e48bd06278d06278c7e00007e000c7e00007e000

def t134 : Nat := 0xe3748be3748be3748be3748be3748be3748bc07081c07081c07081c07081c07081c07081

def t135 : Nat := 0xe1748be174cbe1748be5748be3748be3748bc07081c07081c07081c07081c07081c07081

def t136 : Nat := 0xda7b7cde7b7cc7e04007e040c7e04087e000d06278d06278c7e00007e000c7e00007e000

def t137 : Nat := 0xda7b7cde7b7cc7e04007e040c7e86407e024d06278d06278c7e00007e000c7e00007e000

def t138 : Nat := 0xda7b7cda7b7cc7e04007e000c7e06407e824d06278d06278c7e00007e000c7e00007e000

def t139 : Nat := 0xe1748be174cbe1748be5748be174afe17cafc07081c07081c07081c07081c07081c07081

def t140 : Nat := 0xdb7b7cdb7b7cc7e040c7e000c7e040c7e000d06278d06278c7e000c7e000c7e000c7e000

def t141 : Nat := 0xdafb7cdafb7cc7e04047e000c7e04047e000d06278d06278c7e00007e000c7e00007e000

def t142 : Nat := 0xda7b7eda7f7ec7e04a07e00ac7e44207e002d06278d06278c7e00007e000c7e00007e000

def t143 : Nat := 0xe1748be1748be1748be1748be1f48be1f48bc07081c07081c07081c07081c07081c07081

def t144 : Nat := 0xda7b7eda7b7ec7e04207e402c7e04207e402d06278d06278c7e00007e000c7e00007e000

def t145 : Nat := 0x6db6db6db6dbfbffbffffffffbffbfffffffffffffffffffffffffffffffffffffffffff

def t146 : Nat := 0x381381f81f81381381f81f81081081081081381381f81f81381381f81f81

def t147 : Nat := 0x924924924924040040000000040040000000000000000000000000000000000000000000

def t148 : Nat := 0x1600ac1640a01600ac1640ae1748be1748b006000c06000006000c06000c06000c06000

def t149 : Nat := 0xe7f48be7f4cbe7f48be7f4cbfb7ffffb7fffc7f081c7f081c7f081c7f081d072f9d072f9

def t150 : Nat := 0xdb7b7edb7f7ec7e04ac7e40ae7f4cbe7f48bd06278d06278c7e000c7e000c7e000c7e000

def t151 : Nat := 0x3e040c7e00005a04045ab7cda7b3cda700007e000c7e00007e000c7e278d06278d06

def t152 : Nat := 0x48b61348b61348be1748be1748be1748be17081c07081c07081c07081c07081c07081c07

def t153 : Nat := 0xde7f7eda7b7ef7ede7b7eda7c7e07e07ec7ed06e7ed0627ee7ed0627ed06c7e07e07ec7e

def t154 : Nat := 0x21848325848328169b6816db381fbff81fbf2f9d872f9d87381ffff81fff381ffff81fff

def t155 : Nat := 0xc82500c82501a8b341e8b741a8b341e8b743f8f7e3f8f7e3f8f7e3f8f7e3f8f7e3f8f7e

def t156 : Nat := 0xda7b7cda7b7cc7e04007e000c7e04087e000d06278d06278c7e00007e000c7e00007e000

def t157 : Nat := 0xda7b7cda7b7cc7e04007e000c7e84407e804d06278d06278c7e00007e000c7e00007e000

def t158 : Nat := 0xe1748be1748be1748be1748be17c8fe17c8fc07081c07081c07081c07081c07081c07081

def t159 : Nat := 0xa07e44ac7e00a07e44ac7effffb7ffffb700007e000c7e00007e000c7e278d06278d06

def t160 : Nat := 0x1e8b741e8b741e8b741e8b749ecb749ecb743f8f7e3f8f7e3f8f7e3f8f7e3f8f7e3f8f7e

def t161 : Nat := 0x3e9ffffe9fff3f8ff73f8ff7fe9fff3e9fff3f9fffff9fff3f9fff3f9fffff9fff3f9fff

def t162 : Nat := 0x1607ec56c7e01607ec56c7ef7fdaff7fdaf00607ec06c7e00607ec06c7ee7ed06e7ed06

def t163 : Nat := 0x16000c16000016000c16000c07008c07008006000c06000006000c06000c06000c06000

def t164 : Nat := 0xb74180b34180b74180b34180000048000048f7e380f7e380f7e380f7e380d062f8d062f8

def t165 : Nat := 0xfb7ffffb7fffe7f4cbe7f48be7f4cbe7f48bd072f9d072f9c7f081c7f081c7f081c7f081

def t166 : Nat := 0x4a04040a00007e000c7ea7c483a7c483000000000000000078000078078000078000

def t167 : Nat := 0x7ec7ec7e07eb7eda7f7ede7da7b7ede7f7e07ec7ec7e07e27ed06e7ed06d0627ed06e7e

def t168 : Nat := 0xac0740ac0700ac1640a016483e16483a16000c06000c06000c06000006000c06000006

def t169 : Nat := 0xffffb7ffffb74cbe7f48be7f4cbe7f48be7f2f9d072f9d07081c7f081c7f081c7f081c7f

def t170 : Nat := 0xa00044a04000a00044a040da7b34da7b34000000000000000000000000000000000000

def t171 : Nat := 0x16040c56000016040c5692cd2792cd27000006000c06000006000c06000c06000c06

def t172 : Nat := 0x2584cb2584cbbb5fbfff5fffbb5fbfff5fffffffffffffffffffffffffffffffffffffff

def t173 : Nat := 0xb7cdafb7cdef040c7e04047eb74dffb34dff278d06278d06000c7e00007e000c7e00007e

def t174 : Nat := 0x7e00ac7e44a07e00ac7e44afb7ffffb7fff07e000c7e00007e000c7e000d06278d06278

def t175 : Nat := 0x48be1f4cbe5f48be1f4cbe5ffbffb7fbffb7081c07081c07081c07081c07081c07081c07

def t176 : Nat := 0xda7b7ede7f7ec7e04a07e44af7ede7b7eda7d06278d06278c7e00007e000c7e00007e000

def t177 : Nat := 0xdafb7cdefb7cc7e04047e040dffb74dffb34d06278d06278c7e00007e000c7e00007e000

def t178 : Nat := 0xe1f48be5f4cbe1f48be5f4cbfb7fbffb7fbfc07081c07081c07081c07081c07081c07081

def t179 : Nat := 0x1e000c1e00001e000c1ea1cc87a1cc87000006000c06000006000c06000c06000c06

def t180 : Nat := 0x40340b40340b40340b40340be17483e17483001001001001001001001001001001001001

def t181 : Nat := 0xda7b7cda7b7cf7e1c0b7e180f7e1c0b7e180d062f8d062f8f7e380f7e380f7e380f7e380

def t182 : Nat := 0x2e040c6e00007e04047eb74da7b34da7000006000c0600007e00007e000c06000006

def t183 : Nat := 0x1e040c5e00001e040c5eb3cda7b3cda7000006000c06000006000c06000c06000c06

def t184 : Nat := 0x68040c68000078040078b7cda1b7c1a1000078000c78000078000078278d00278100

def t185 : Nat := 0x248483248483380fb7380ff7381fbf381fff2f9d872f9d87381fff381fff381fff381fff

def t186 : Nat := 0xdafb7cdafb7cc7e04007e000c7e85407e014d06278d06278c7e00007e000c7e00007e000

def t187 : Nat := 0xdb7b7cdb7b7cc7e04007e000c7e04807e008d06278d06278c7e00007e000c7e00007e000

def t188 : Nat := 0xe1748be1748be1749fe17c9fe1f48be1f48bc07081c07081c07081c07081c07081c07081

def t189 : Nat := 0xda7b7cda7b7cc7e04007e000c7e05407e814d06278d06278c7e00007e000c7e00007e000

def t190 : Nat := 0xda7b7cda7b7cc7e04087e000c7e04807e008d06278d06278c7e00007e000c7e00007e000

def t191 : Nat := 0xda7b7cda7b7cc7e04047e000c7f04047f000d06278d06278c7e00007e000c7e00007e000

def t192 : Nat := 0xda7f7fda7f7fc7e44207e002c7e44207e002d06278d06278c7e00007e000c7e00007e000

def t193 : Nat := 0xda7b7eda7f7ec7e04207e402c7e44307e403d06278d06278c7e00007e000c7e00007e000

def t194 : Nat := 0x783ffff83ffffff783ffff83fbffffffffbff87ffff87fffffff87ffff87ffffffffffff

def t195 : Nat := 0x381f81f81381258481218081481258081218381f81f813812f9d812f9181d812f91812f9

def t196 : Nat := 0xfb7ffffb7fffc7e44ac7e00ac7f44ac7f00ad06278d06278c7e000c7e000c7e000c7e000

def t197 : Nat := 0xdb7b7edb7f7ec7f04ac7f40ae7e4c3e7e483d06278d06278c7e000c7e000c7e000c7e000

def t198 : Nat := 0xdb7b7cdf7b7cc7e040c7e040d7f96cd7f92cd06278d06278c7e000c7e000c7e000c7e000

def t199 : Nat := 0x5ebb7c5ebb7cfffbf5fffff5fffbf5fffff5ffffffffffffffffffffffffffffffffffff

def t200 : Nat := 0xf7fdaff7fdafe57cffe174ffe57cffe174ffe7fd87e7fd87c07cffc070ffc07cffc070ff

def t201 : Nat := 0x1e8b001a83001e8b001a83000802500802503f8f003f83003f8f003f8300180278180278

def t202 : Nat := 0x74040c7400007c04087cb7cda5b7c9a500007e000c7e00007e000c7e278d06278d06

def t203 : Nat := 0x6a04046a00007e040c7eb74da7b74da700007e000c7e00007e000c7e278d06278d06

def t204 : Nat := 0x48ba1448ba1448ba1548be1548ba1548be15081c07081c07081c07081c07081c07081c07

def t205 : Nat := 0x7e040c7e00007e040c7eb7c5a3b7c5a300007e000c7e00007e000c7e278d06278d06

def t206 : Nat := 0x2504832504833005abb005eb381fbfb81fff2f9d872f9d87381ffff81fff381ffff81fff

def t207 : Nat := 0x48000048bb5381ff5f81bb5381ff5f81d872f9d872f9fff381ffff81fff381ffff81

def t208 : Nat := 0xda7f7eda7b7ee7e4c3a7e483c7e04a07e40ad06278d06278c7e00007e000c7e00007e000

def t209 : Nat := 0x160168160168b741e0b741e0b741e0b741e0f7e3f8f7e3f8f7e3f8f7e3f8f7e3f8f7e3f8

def t210 : Nat := 0x81258481258b3c181b7c581fb5381bf5f81d872f9d872f9fff381ffff81fff381ffff81

def t211 : Nat := 0x1eab745eab741eab745eab745ebb745ebb743f8f7e3f8f7e3f8f7e3f8f7e3f8f7e3f8f7e

def t212 : Nat := 0x7404087400007404087416892416892400007e000c7e00007e000c7e278d06278d06

def t213 : Nat := 0x1e8b7e1e8f7e1e8b7e1e8f7ebfcff7bfcff73f8f7e3f8f7e3f8f7e3f8f7e3f8f7e3f8f7e

def t214 : Nat := 0x68040068000068040068b741a0b741a0000078000078000078000078278100278100

def t215 : Nat := 0xb741feb74dfeb741feb74dfeb7cdefb7cdeff7e3fef7effef7e3fef7effef7effef7effe

def t216 : Nat := 0x6a04046a00006a04046ab745a3b745a3000078000078000078000078278100278100

def t217 : Nat := 0x88a14088a14088a14088a14088a14088a14080c06080c06080c06080c06080c06080c06

def t218 : Nat := 0x5ebf775ebf775ebf775ebf775ebf775ebf773f9f7f3f9f7f3f9f7f3f9f7f3f9f7f3f9f7f

def t219 : Nat := 0xbfcfb7bfcfb70c8e7e088a7e0c8e7e088a7e2f8d062f8d06080c7e080c7e080c7e080c7e

def t220 : Nat := 0xfb7bfcfb7bfce7e0c8a7e088e7e0c8a7e088d062f8d062f8c7e080c7e080c7e080c7e080

def t221 : Nat := 0xdbfb7cdbfb7cc7e040c7e000cffa5ccffa1cd06278d06278c7e000c7e000c7e000c7e000

def t222 : Nat := 0xbfcbfcbfcbfcbfcbfcbfcbfcbfcbfcbfcbfcffeffeffeffeffeffeffeffeffeffeffeffe

def t223 : Nat := 0x160160160160160160160160160160160160378378378378378378378378378378378378

def t224 : Nat := 0x40c7e040c7eb7cdffb7cdffb7cdffb7cdff000c7e000c7e278d7e278d7e278d7e278d7e

def t225 : Nat := 0x4ffe17cffe574ffe17cffe57daff7fdaff7f0ffc07cffc070ffc07cffc07d87e7fd87e7f

def t226 : Nat := 0x27e483e7e4c33fffbffffffffa7ffffa7fff2ffd87effd873ffffffffffff87ffff87fff

def t227 : Nat := 0xb7cda7b7cda73c1ffff81fff3c1ffff81fff2f9d872f9d87381ffff81fff381ffff81fff

def t228 : Nat := 0xe5f48be5f48bf97fbff97ffff97fbff97fffeffd87effd87f87ffff87ffff87ffff87fff

def t229 : Nat := 0x3c1ffff81fffb7cda7b7cda7f81fff3c1fff381ffff81fff2f9d872f9d87f81fff381fff

def t230 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def t231 : Nat := 0x0

def t232 : Nat := 0x48be5f48be5ffbff97ffff97fbff97ffff97d87effd87effffff87ffff87ffff87ffff87

def t233 : Nat := 0xffff81fbf381ffff81fbf381483258483258ffff81fff381ffff81fff381d872f9d872f9

def t234 : Nat := 0x200483200483200483200483381fbf381fbf281d87281d87281d87281d87381fff381fff

def t235 : Nat := 0x4cbe7f4cbe7fffffffffffffffffffffffff081c7f081c7f2f9d7f2f9d7f2f9d7f2f9d7f

def t236 : Nat := 0xb7cdffb7cdffb7cdffb7cdffb7cdffb7cdff278d7e278d7e278d7e278d7e278d7e278d7e

def t237 : Nat := 0x7e040c7e00007e040c7e040c26040c2600007e000c7e00007e000c7e000c06000c06

def t238 : Nat := 0xb7edfff7edffb7edfff7edffde7f7ede7f7e27ed7ee7ed7e27ed7ee7ed7ed06e7ed06e7e

def t239 : Nat := 0x7c04087c00007c04087c87c00087c000000078000078000078000078078000078000

def t240 : Nat := 0xcffe57cffe57dfff7fdfff7fdfff7fdfff7fcffc07cffc07dffe7fdffe7fdffe7fdffe7f

def t241 : Nat := 0x40c7e040c7e040c7e040c7eb7cdffb7cdff000c7e000c7e000c7e000c7e278d7e278d7e

def t242 : Nat := 0x26000026000026000026000026000026000006000006000006000006000006000006

def t243 : Nat := 0x2607ec66c7e07e07e07ec7ef7ede7b7eda700607ec06c7e07e07e07ec7ee7ed0627ed06

def t244 : Nat := 0x40000000040000000024000824000000000000000000000000000000000000

def t245 : Nat := 0x48be374cbe3748be7f48be7f4cbe3748be37081c07081c07081c7f081c7f081c07081c07

def t246 : Nat := 0x6000c06000016000016000c06000006000006000c06000006000006000c06000006

def t247 : Nat := 0x66c7ec2607eb7eda7b7eda7c2607e066c7e006c7ec0607e27ed0627ed06c0607e006c7e

def t248 : Nat := 0x4007c00007c000000040000000000000000000078000078000000000000000

def t249 : Nat := 0x4afe17cafe574ffe174ffe17cafe574afe17087c07c87c070ffc070ffc07c87c07087c07

def t250 : Nat := 0x200040200000a00000a000402000002000000000000000000000000000000000000

def t251 : Nat := 0x7e04007e00007e040c7e07c02687cc2600007e00007e00007e000c7e078006078c06

def t252 : Nat := 0x4ffe7fcffe7f4ffe7fcffe7fffffffffffff0ffc7fcffc7f0ffc7fcffc7fffff7fffff7f

def t253 : Nat := 0xa01640ac1600a01640ac1648be1748be17000006000c06000006000c06000c06000c06

def t254 : Nat := 0x4007e040c7e92497e964d7eb7cda7b7cde700007e000c7e00007e000c7e278d06278d06

def t255 : Nat := 0x804000804000000000000000000000000000000000000

def t256 : Nat := 0x48000048b34180b74180b34180b74180d062f8d062f8f7e380f7e380f7e380f7e380

def t257 : Nat := 0x4ffe7fcffe7fffffb7fffff7daff7fdeff7f0ffc7fcffc7f2ffd07effd07d87e7fd87e7f

def t258 : Nat := 0xe9feffedfeffe9feffedfeffffffbfffffbfc87cffc87cffc87cffc87cffeffd87effd87

def t259 : Nat := 0xc7e040c7e008c7f048c7fb7cdb7b7cdb7000c7e000c7e000c7e000c7e278d06278d06

def t260 : Nat := 0x56c7ec1607eb7eda7f7eda7c0707ec47c7e006c7ec0607e27ed06e7ed06c0607ec06c7e

def t261 : Nat := 0x8000008014000814000000000000000000000000000000000000000

def t262 : Nat := 0x49fe17c9fe1749fe17c9fe17c8fe1fc8fe1f087c07c87c07087c07c87c07c87c07c87c07

def t263 : Nat := 0x2000402000002000402000403000403000000000000000000000000000000000000

def t264 : Nat := 0x81218481258218081258481f81381381f811812f9d812f92f91812f9d81f81381381f81

def t265 : Nat := 0x66040c2600007e00087e07cc2687c026000006000c0600007e00007e078c06078006

def t266 : Nat := 0x4007e040c7e07c07e87cc7eb7cdffb7cdff00007e000c7e07807e078c7e278d7e278d7e

def t267 : Nat := 0x48be574cbe1748be7f48be7f4ffe17cffe17081c07081c07081c7f081c7f0f9c070f9c07

def t268 : Nat := 0x87e040c7e87c07e07cc7eb7cde7b7cda700007e000c7e07807e078c7e278d06278d06

def t269 : Nat := 0x56040c1600007e000c7e07cc0787cc07000006000c0600007e000c7e078c06078c06

def t270 : Nat := 0x802500802501a83001e8b001a83001e8b001802781802783f83003f8f003f83003f8f00

def t271 : Nat := 0x403417403c17403417403c1740bc0740bc07001007001c07001007001c07001c07001c07

def t272 : Nat := 0x47e040c7ea144ffa54cffb7cdafb7cdaf00007e000c7e00007e000c7e278d06278d06

def t273 : Nat := 0x4ac7e40a07eb7eda7f7eda7483a7e4c3e7e000c7e00007e278d06278d0600007e000c7e

def t274 : Nat := 0x1feb74dfeb741feb74dfeb74defb7cdefb7c3fef7effef7e3fef7effef7effef7effef7e

def t275 : Nat := 0x40347f443c7f40347f443c7ff7fda7f7fda700107f001c7f00107f001c7f279d07279d07

def rowsE (i : Nat) : List Nat :=
  (if i < 512 then (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then [t0,t1,t2,t3,t4,t5,t6] else [t0,t1,t2,t4,t5,t6,t7]) else (if i < 3 then [t0,t2,t4,t8,t9,t6,t10] else [t0,t1,t2,t11,t9,t6,t10])) else (if i < 6 then (if i < 5 then [t0,t1,t2,t4,t12,t13,t6] else [t0,t1,t2,t14,t11,t6,t15]) else (if i < 7 then [t0,t2,t4,t8,t14,t6,t15] else [t0,t1,t2,t13,t11,t16,t15]))) else (if i < 12 then (if i < 10 then (if i < 9 then [t0,t1,t2,t4,t17,t13,t6] else [t0,t1,t2,t18,t5,t19,t6]) else (if i < 11 then [t0,t1,t2,t4,t5,t20,t16] else [t0,t1,t2,t4,t13,t16,t21])) else (if i < 14 then (if i < 13 then [t0,t1,t2,t4,t22,t23,t24] else [t0,t1,t2,t18,t5,t25,t6]) else (if i < 15 then [t0,t1,t2,t26,t4,t5,t22] else [t0,t1,t4,t5,t27,t28,t29])))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then [t0,t30,t1,t2,t13,t22,t6] else [t31,t1,t4,t5,t13,t32,t6]) else (if i < 19 then [t0,t1,t2,t4,t13,t6,t33] else [t31,t1,t4,t34,t13,t22,t6])) else (if i < 22 then (if i < 21 then [t0,t1,t2,t4,t5,t19,t35] else [t0,t1,t2,t4,t19,t6,t36]) else (if i < 23 then [t0,t1,t2,t4,t13,t37,t21] else [t0,t1,t2,t4,t22,t35,t36]))) else (if i < 28 then (if i < 26 then (if i < 25 then [t0,t38,t4,t5,t13,t22,t6] else [t0,t1,t2,t4,t39,t22,t6]) else (if i < 27 then [t0,t1,t2,t4,t40,t13,t22] else [t0,t1,t2,t20,t41,t6,t21])) else (if i < 30 then (if i < 29 then [t0,t1,t2,t42,t25,t6,t24] else [t0,t1,t2,t13,t41,t43,t21]) else (if i < 31 then [t0,t1,t2,t42,t22,t44,t24] else [t0,t1,t2,t4,t45,t13,t22]))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then [t0,t1,t2,t46,t5,t13,t22] else [t0,t1,t2,t47,t5,t13,t22]) else (if i < 35 then [t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t48,t4,t5,t13,t6])) else (if i < 38 then (if i < 37 then [t0,t1,t2,t49,t4,t5,t13,t22] else [t0,t1,t2,t50,t51,t4,t22,t6]) else (if i < 39 then [t0,t1,t2,t48,t50,t4,t5,t6] else [t0,t1,t2,t49,t51,t4,t13,t22]))) else (if i < 44 then (if i < 42 then (if i < 41 then [t0,t1,t2,t48,t51,t4,t13,t6] else [t0,t1,t2,t49,t48,t4,t5,t13]) else (if i < 43 then [t52,t1,t2,t4,t53,t13,t22,t6] else [t54,t1,t55,t4,t5,t13,t22,t6])) else (if i < 46 then (if i < 45 then [t0,t1,t2,t4,t5,t13,t56,t6] else [t0,t1,t2,t4,t5,t13,t22,t57]) else (if i < 47 then [t58,t1,t2,t59,t5,t13,t22,t6] else [t31,t1,t2,t4,t5,t13,t22,t6])))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then [t0,t1,t2,t4,t5,t13,t60,t6] else [t61,t1,t2,t4,t5,t62,t22,t6]) else (if i < 51 then [t63,t1,t2,t4,t5,t13,t22,t64] else [t0,t1,t2,t4,t5,t13,t32,t6])) else (if i < 54 then (if i < 53 then [t0,t1,t2,t4,t5,t13,t6,t65] else [t0,t1,t2,t4,t5,t13,t22,t66]) else (if i < 55 then [t0,t1,t2,t4,t5,t13,t67,t6] else [t0,t1,t2,t49,t68,t5,t13,t22]))) else (if i < 60 then (if i < 58 then (if i < 57 then [t0,t1,t2,t69,t5,t13,t22,t70] else [t0,t1,t50,t51,t4,t22,t6,t71]) else (if i < 59 then [t0,t1,t2,t48,t50,t51,t4,t6] else [t0,t1,t2,t49,t50,t51,t4,t22])) else (if i < 62 then (if i < 61 then [t52,t1,t2,t50,t4,t53,t22,t6] else [t54,t1,t55,t48,t4,t5,t13,t6]) else (if i < 63 then [t0,t1,t2,t50,t4,t72,t22,t6] else [t0,t1,t2,t73,t4,t5,t13,t6])))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then [t0,t1,t2,t48,t74,t5,t13,t6] else [t0,t1,t2,t48,t4,t72,t13,t6]) else (if i < 67 then [t0,t1,t2,t48,t4,t5,t75,t6] else [t0,t1,t2,t48,t4,t5,t13,t57])) else (if i < 70 then (if i < 69 then [t76,t1,t2,t77,t4,t5,t13,t6] else [t78,t2,t4,t5,t13,t22,t6,t79]) else (if i < 71 then [t0,t1,t2,t48,t4,t80,t13,t6] else [t58,t1,t2,t48,t59,t5,t13,t6]))) else (if i < 76 then (if i < 74 then (if i < 73 then [t31,t1,t2,t51,t4,t13,t22,t6] else [t0,t1,t2,t50,t4,t81,t22,t6]) else (if i < 75 then [t0,t1,t2,t48,t4,t81,t13,t6] else [t52,t1,t2,t48,t4,t53,t13,t6])) else (if i < 78 then (if i < 77 then [t61,t1,t2,t48,t4,t5,t62,t6] else [t63,t1,t2,t48,t4,t5,t13,t64]) else (if i < 79 then [t0,t1,t2,t50,t4,t82,t22,t6] else [t0,t1,t2,t48,t4,t5,t83,t6])))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then [t0,t1,t2,t84,t4,t5,t13,t6] else [t0,t1,t2,t48,t85,t5,t13,t6]) else (if i < 83 then [t0,t1,t2,t48,t4,t82,t13,t6] else [t0,t1,t2,t48,t4,t5,t86,t6])) else (if i < 86 then (if i < 85 then [t0,t1,t48,t50,t4,t5,t6,t71] else [t0,t1,t2,t48,t50,t68,t5,t6]) else (if i < 87 then [t0,t1,t2,t49,t48,t50,t4,t5] else [t87,t1,t2,t48,t4,t5,t13,t6]))) else (if i < 92 then (if i < 90 then (if i < 89 then [t88,t2,t4,t5,t13,t22,t6,t89] else [t0,t1,t2,t48,t4,t90,t13,t6]) else (if i < 91 then [t63,t1,t2,t51,t4,t13,t22,t64] else [t0,t1,t2,t48,t4,t5,t91,t6])) else (if i < 94 then (if i < 93 then [t0,t1,t2,t50,t4,t22,t6,t21] else [t0,t1,t2,t92,t4,t5,t13,t6]) else (if i < 95 then [t0,t1,t2,t48,t4,t5,t13,t66] else [t0,t1,t2,t50,t4,t34,t22,t6]))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then [t0,t1,t2,t48,t4,t34,t13,t6] else [t61,t1,t4,t5,t62,t22,t6,t71]) else (if i < 99 then [t52,t2,t4,t53,t13,t22,t6,t79] else [t31,t1,t2,t48,t4,t5,t13,t6])) else (if i < 102 then (if i < 101 then [t58,t1,t2,t51,t59,t13,t22,t6] else [t0,t1,t2,t48,t4,t5,t93,t6]) else (if i < 103 then [t0,t1,t2,t94,t4,t5,t13,t6] else [t0,t95,t1,t2,t96,t5,t13,t6]))) else (if i < 108 then (if i < 106 then (if i < 105 then [t97,t1,t4,t5,t13,t22,t6,t98] else [t0,t1,t2,t99,t4,t5,t22,t100]) else (if i < 107 then [t0,t1,t2,t49,t48,t68,t5,t13] else [t0,t1,t2,t49,t48,t51,t4,t13])) else (if i < 110 then (if i < 109 then [t0,t1,t2,t101,t4,t5,t22,t6] else [t58,t1,t59,t5,t13,t22,t6,t71]) else (if i < 111 then [t0,t1,t2,t50,t4,t102,t22,t6] else [t0,t1,t2,t48,t69,t5,t13,t70])))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then [t63,t1,t4,t5,t13,t22,t64,t71] else [t0,t1,t2,t50,t4,t103,t22,t6]) else (if i < 115 then [t0,t1,t2,t48,t5,t13,t6,t104] else [t0,t1,t2,t48,t4,t5,t6,t105])) else (if i < 118 then (if i < 117 then [t0,t1,t2,t106,t4,t5,t22,t6] else [t78,t1,t2,t4,t5,t13,t22,t6]) else (if i < 119 then [t0,t1,t2,t4,t5,t13,t107,t6] else [t87,t1,t2,t4,t5,t13,t22,t6]))) else (if i < 124 then (if i < 122 then (if i < 121 then [t0,t1,t2,t4,t5,t13,t108,t6] else [t0,t1,t2,t48,t4,t5,t20,t6]) else (if i < 123 then [t0,t1,t2,t48,t4,t13,t6,t21] else [t0,t1,t2,t48,t4,t5,t13,t43])) else (if i < 126 then (if i < 125 then [t0,t1,t2,t50,t4,t22,t6,t24] else [t0,t1,t2,t50,t4,t109,t22,t6]) else (if i < 127 then [t0,t1,t2,t48,t5,t13,t11,t6] else [t0,t1,t2,t48,t4,t5,t14,t6]))))))) else (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then [t0,t1,t2,t48,t4,t5,t13,t16] else [t31,t1,t4,t5,t13,t22,t6,t71]) else (if i < 131 then [t0,t1,t2,t48,t4,t5,t110,t6] else [t0,t1,t2,t111,t4,t5,t9,t6])) else (if i < 134 then (if i < 133 then [t0,t1,t2,t4,t5,t9,t6,t112] else [t0,t1,t2,t4,t5,t113,t9,t6]) else (if i < 135 then [t52,t1,t2,t68,t53,t13,t22,t6] else [t52,t1,t2,t114,t4,t13,t22,t6]))) else (if i < 140 then (if i < 138 then (if i < 137 then [t52,t1,t2,t49,t4,t53,t13,t22] else [t0,t1,t2,t4,t109,t22,t9,t6]) else (if i < 139 then [t0,t1,t2,t4,t53,t13,t22,t16] else [t0,t1,t2,t4,t5,t13,t115,t16])) else (if i < 142 then (if i < 141 then [t54,t1,t4,t5,t13,t116,t115,t6] else [t54,t1,t117,t4,t5,t13,t22,t6]) else (if i < 143 then [t118,t1,t2,t4,t53,t13,t22,t6] else [t31,t1,t4,t5,t13,t119,t22,t6])))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then [t0,t120,t2,t121,t5,t13,t22,t6] else [t122,t1,t2,t4,t5,t62,t22,t6]) else (if i < 147 then [t123,t1,t2,t4,t53,t13,t22,t6] else [t124,t1,t2,t4,t53,t13,t22,t6])) else (if i < 150 then (if i < 149 then [t0,t125,t2,t4,t5,t13,t22,t126] else [t127,t1,t2,t4,t5,t13,t22,t6]) else (if i < 151 then [t0,t1,t2,t4,t5,t13,t128,t6] else [t0,t1,t2,t129,t5,t13,t22,t6]))) else (if i < 156 then (if i < 154 then (if i < 153 then [t0,t1,t2,t4,t5,t13,t6,t130] else [t0,t1,t2,t4,t5,t13,t22,t131]) else (if i < 155 then [t0,t1,t2,t4,t5,t13,t132,t6] else [t0,t1,t2,t4,t5,t13,t133,t6])) else (if i < 158 then (if i < 157 then [t0,t1,t2,t4,t5,t13,t22,t134] else [t0,t1,t2,t4,t5,t13,t22,t135]) else (if i < 159 then [t0,t1,t2,t4,t5,t13,t136,t6] else [t0,t1,t2,t4,t5,t13,t137,t6]))))) else (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then [t0,t1,t2,t4,t5,t13,t138,t6] else [t0,t1,t2,t4,t5,t13,t22,t139]) else (if i < 163 then [t0,t1,t2,t4,t5,t13,t140,t6] else [t0,t1,t2,t4,t5,t13,t141,t6])) else (if i < 166 then (if i < 165 then [t0,t1,t2,t4,t5,t13,t142,t6] else [t0,t1,t2,t4,t5,t13,t22,t143]) else (if i < 167 then [t0,t1,t2,t4,t5,t13,t144,t6] else [t0,t1,t2,t4,t145,t13,t6,t15]))) else (if i < 172 then (if i < 170 then (if i < 169 then [t54,t1,t55,t4,t5,t13,t56,t6] else [t54,t1,t55,t4,t5,t13,t22,t57]) else (if i < 171 then [t146,t0,t1,t2,t4,t147,t13,t6] else [t54,t1,t55,t49,t4,t5,t13,t22])) else (if i < 174 then (if i < 173 then [t0,t1,t2,t4,t5,t13,t16,t15] else [t31,t1,t55,t4,t5,t13,t22,t6]) else (if i < 175 then [t0,t148,t1,t4,t5,t13,t22,t149] else [t0,t1,t2,t4,t5,t13,t150,t6])))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then [t151,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t152,t5,t13,t22,t6]) else (if i < 179 then [t0,t1,t2,t4,t5,t14,t153,t6] else [t0,t1,t2,t49,t4,t72,t13,t22])) else (if i < 182 then (if i < 181 then [t0,t1,t2,t154,t4,t5,t13,t6] else [t0,t1,t2,t49,t4,t5,t13,t56]) else (if i < 183 then [t0,t1,t2,t4,t72,t75,t22,t6] else [t0,t1,t2,t4,t72,t13,t22,t57]))) else (if i < 188 then (if i < 186 then (if i < 185 then [t0,t1,t2,t4,t72,t13,t56,t6] else [t0,t1,t2,t4,t5,t75,t56,t6]) else (if i < 187 then [t0,t1,t2,t4,t5,t13,t56,t57] else [t31,t1,t2,t4,t5,t13,t22,t57])) else (if i < 190 then (if i < 189 then [t0,t1,t2,t4,t5,t13,t116,t16] else [t63,t1,t2,t74,t5,t13,t22,t6]) else (if i < 191 then [t0,t1,t2,t49,t74,t5,t13,t22] else [t0,t1,t2,t155,t4,t5,t13,t22])))))) else (if i < 224 then (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then [t0,t1,t2,t74,t5,t13,t22,t57] else [t63,t1,t2,t4,t5,t13,t22,t57]) else (if i < 195 then [t0,t1,t2,t4,t5,t13,t156,t6] else [t0,t1,t2,t4,t5,t13,t157,t6])) else (if i < 198 then (if i < 197 then [t0,t1,t2,t4,t5,t13,t22,t158] else [t54,t0,t1,t4,t5,t13,t32,t6]) else (if i < 199 then [t54,t159,t1,t4,t5,t13,t22,t6] else [t54,t0,t1,t4,t34,t13,t22,t6]))) else (if i < 204 then (if i < 202 then (if i < 201 then [t0,t1,t2,t160,t4,t5,t13,t22] else [t0,t1,t2,t161,t4,t5,t22,t29]) else (if i < 203 then [t58,t1,t2,t59,t81,t13,t22,t6] else [t0,t162,t1,t4,t5,t13,t22,t149])) else (if i < 206 then (if i < 205 then [t31,t163,t1,t4,t5,t13,t22,t149] else [t58,t1,t2,t164,t5,t13,t22,t6]) else (if i < 207 then [t58,t1,t2,t49,t59,t5,t13,t22] else [t0,t1,t2,t4,t5,t110,t6,t165])))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then [t166,t1,t2,t4,t5,t62,t22,t6] else [t31,t1,t167,t4,t5,t13,t22,t6]) else (if i < 211 then [t0,t168,t1,t2,t13,t22,t6,t169] else [t0,t1,t2,t4,t5,t20,t6,t165])) else (if i < 214 then (if i < 213 then [t0,t1,t2,t4,t13,t6,t65,t169] else [t0,t1,t2,t4,t22,t6,t105,t169]) else (if i < 215 then [t63,t170,t1,t4,t5,t13,t22,t6] else [t31,t1,t2,t4,t5,t13,t22,t64]))) else (if i < 220 then (if i < 218 then (if i < 217 then [t171,t1,t2,t59,t5,t13,t22,t6] else [t0,t1,t2,t172,t4,t5,t13,t6]) else (if i < 219 then [t31,t1,t2,t4,t173,t13,t22,t6] else [t31,t1,t174,t4,t5,t13,t22,t6])) else (if i < 222 then (if i < 221 then [t31,t1,t2,t175,t5,t13,t22,t6] else [t31,t1,t2,t4,t5,t13,t176,t6]) else (if i < 223 then [t31,t1,t2,t68,t5,t13,t22,t6] else [t31,t1,t2,t49,t4,t5,t13,t22]))))) else (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then [t0,t1,t2,t4,t5,t13,t177,t6] else [t0,t1,t2,t4,t5,t13,t22,t178]) else (if i < 227 then [t0,t1,t2,t4,t5,t13,t176,t6] else [t179,t1,t2,t59,t5,t13,t22,t6])) else (if i < 230 then (if i < 229 then [t0,t1,t2,t180,t5,t13,t22,t70] else [t0,t1,t2,t4,t5,t13,t181,t6]) else (if i < 231 then [t182,t1,t2,t4,t5,t13,t22,t6] else [t183,t1,t2,t4,t5,t13,t22,t6]))) else (if i < 236 then (if i < 234 then (if i < 233 then [t184,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t49,t4,t81,t13,t22]) else (if i < 235 then [t0,t1,t2,t185,t4,t5,t13,t6] else [t0,t1,t2,t49,t4,t5,t13,t60])) else (if i < 238 then (if i < 237 then [t0,t1,t2,t4,t5,t93,t60,t6] else [t0,t1,t2,t4,t5,t13,t186,t6]) else (if i < 239 then [t0,t1,t2,t4,t5,t13,t187,t6] else [t0,t1,t2,t4,t5,t13,t22,t188])))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then [t0,t1,t2,t4,t5,t13,t189,t6] else [t0,t1,t2,t4,t5,t13,t190,t6]) else (if i < 243 then [t0,t1,t2,t4,t5,t13,t191,t6] else [t0,t1,t2,t4,t5,t13,t192,t6])) else (if i < 246 then (if i < 245 then [t0,t1,t2,t4,t5,t13,t193,t6] else [t0,t1,t2,t4,t194,t22,t6,t10]) else (if i < 247 then [t61,t1,t2,t49,t4,t5,t62,t22] else [t61,t1,t2,t195,t4,t5,t22,t6]))) else (if i < 252 then (if i < 250 then (if i < 249 then [t0,t1,t2,t4,t5,t13,t6,t196] else [t0,t1,t2,t4,t5,t13,t197,t6]) else (if i < 251 then [t0,t1,t2,t4,t5,t13,t198,t6] else [t0,t1,t2,t4,t199,t13,t22,t200])) else (if i < 254 then (if i < 253 then [t63,t1,t2,t4,t82,t13,t22,t64] else [t63,t1,t174,t4,t5,t13,t22,t64]) else (if i < 255 then [t63,t1,t2,t85,t5,t13,t22,t64] else [t63,t1,t2,t4,t5,t13,t67,t64])))))))) else (if i < 384 then (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then [t63,t1,t2,t68,t5,t13,t22,t64] else [t63,t1,t2,t201,t4,t5,t13,t22]) else (if i < 259 then [t0,t1,t2,t4,t5,t13,t200,t65] else [t0,t1,t2,t4,t5,t20,t41,t6])) else (if i < 262 then (if i < 261 then [t202,t1,t2,t4,t5,t13,t22,t6] else [t203,t1,t2,t4,t5,t13,t22,t6]) else (if i < 263 then [t0,t1,t2,t204,t5,t13,t22,t6] else [t205,t1,t2,t4,t5,t13,t22,t6]))) else (if i < 268 then (if i < 266 then (if i < 265 then [t0,t1,t2,t49,t4,t82,t13,t22] else [t0,t1,t2,t206,t4,t5,t13,t6]) else (if i < 267 then [t0,t1,t2,t49,t4,t5,t13,t32] else [t0,t1,t2,t4,t5,t91,t32,t6])) else (if i < 270 then (if i < 269 then [t0,t1,t2,t4,t103,t83,t22,t6] else [t0,t1,t2,t4,t5,t13,t32,t66]) else (if i < 271 then [t0,t1,t2,t4,t82,t86,t22,t6] else [t0,t1,t2,t4,t82,t13,t67,t6])))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then [t0,t1,t2,t49,t4,t13,t22,t21] else [t0,t1,t2,t49,t4,t5,t13,t65]) else (if i < 275 then [t207,t0,t1,t2,t4,t13,t22,t6] else [t0,t1,t2,t4,t13,t22,t43,t21])) else (if i < 278 then (if i < 277 then [t0,t1,t2,t4,t5,t83,t208,t6] else [t0,t1,t2,t49,t85,t5,t13,t22]) else (if i < 279 then [t0,t1,t2,t209,t5,t13,t22,t6] else [t0,t1,t2,t4,t34,t13,t22,t66]))) else (if i < 284 then (if i < 282 then (if i < 281 then [t0,t1,t2,t49,t4,t34,t13,t22] else [t0,t1,t2,t210,t4,t13,t22,t6]) else (if i < 283 then [t0,t1,t2,t49,t4,t5,t13,t67] else [t0,t1,t2,t4,t5,t86,t67,t6])) else (if i < 286 then (if i < 285 then [t0,t1,t2,t211,t4,t5,t13,t22] else [t212,t1,t2,t213,t4,t5,t13,t22]) else (if i < 287 then [t214,t1,t2,t215,t5,t13,t22,t6] else [t216,t1,t2,t68,t5,t13,t22,t6]))))) else (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then [t0,t1,t2,t217,t218,t5,t13,t22] else [t0,t1,t2,t49,t4,t219,t13,t22]) else (if i < 291 then [t216,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t4,t5,t13,t6,t220])) else (if i < 294 then (if i < 293 then [t0,t1,t2,t4,t5,t13,t221,t6] else [t0,t1,t2,t5,t222,t13,t22,t70]) else (if i < 295 then [t0,t1,t2,t223,t69,t5,t13,t22] else [t0,t1,t2,t4,t5,t13,t22,t6]))) else (if i < 300 then (if i < 298 then (if i < 297 then [t0,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t48,t4,t5,t13,t6]) else (if i < 299 then [t0,t1,t2,t48,t4,t5,t13,t22,t6] else [t0,t1,t224,t2,t4,t5,t13,t22,t6])) else (if i < 302 then (if i < 301 then [t52,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t55,t4,t5,t13,t22,t6]) else (if i < 303 then [t54,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t4,t59,t5,t13,t22,t6])))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then [t58,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t167,t4,t5,t13,t22,t6]) else (if i < 307 then [t61,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t4,t225,t5,t13,t22,t6])) else (if i < 310 then (if i < 309 then [t63,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t4,t4,t5,t13,t22,t6]) else (if i < 311 then [t0,t1,t2,t49,t4,t5,t13,t22] else [t0,t1,t2,t49,t4,t5,t13,t22,t6]))) else (if i < 316 then (if i < 314 then (if i < 313 then [t0,t1,t2,t4,t5,t13,t22,t6,t70] else [t0,t1,t2,t69,t4,t5,t13,t22,t6]) else (if i < 315 then [t0,t0,t1,t2,t51,t4,t13,t22,t6] else [t0,t0,t1,t4,t5,t13,t22,t6,t71])) else (if i < 318 then (if i < 317 then [t0,t0,t1,t2,t68,t5,t13,t22,t6] else [t0,t0,t1,t2,t48,t4,t5,t13,t6]) else (if i < 319 then [t0,t0,t1,t2,t49,t4,t5,t13,t22] else [t0,t1,t2,t50,t51,t4,t22,t6])))))) else (if i < 352 then (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then [t0,t1,t2,t48,t4,t5,t13,t6,t79] else [t0,t1,t224,t2,t48,t4,t5,t13,t6]) else (if i < 323 then [t52,t0,t1,t2,t50,t4,t5,t22,t6] else [t0,t1,t2,t55,t48,t4,t5,t13,t6])) else (if i < 326 then (if i < 325 then [t54,t0,t1,t2,t48,t4,t5,t13,t6] else [t0,t1,t2,t48,t77,t4,t5,t13,t6]) else (if i < 327 then [t76,t0,t1,t2,t48,t4,t5,t13,t6] else [t0,t1,t2,t48,t4,t59,t5,t13,t6]))) else (if i < 332 then (if i < 330 then (if i < 329 then [t58,t0,t1,t2,t48,t4,t5,t13,t6] else [t0,t1,t224,t2,t50,t4,t5,t22,t6]) else (if i < 331 then [t52,t0,t1,t2,t48,t4,t5,t13,t6] else [t0,t1,t2,t167,t48,t4,t5,t13,t6])) else (if i < 334 then (if i < 333 then [t61,t0,t1,t2,t48,t4,t5,t13,t6] else [t0,t1,t2,t48,t4,t5,t13,t6,t64]) else (if i < 335 then [t63,t0,t1,t2,t48,t4,t5,t13,t6] else [t0,t1,t2,t48,t50,t4,t5,t6])))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then [t0,t1,t2,t48,t50,t4,t5,t13,t6] else [t0,t1,t2,t48,t226,t4,t5,t13,t6]) else (if i < 339 then [t88,t0,t2,t4,t5,t13,t22,t6,t79] else [t0,t1,t2,t48,t4,t225,t5,t13,t6])) else (if i < 342 then (if i < 341 then [t63,t0,t1,t2,t51,t4,t13,t22,t6] else [t0,t1,t2,t167,t50,t4,t5,t22,t6]) else (if i < 343 then [t61,t0,t1,t4,t5,t13,t22,t6,t71] else [t0,t1,t224,t2,t51,t4,t13,t22,t6]))) else (if i < 348 then (if i < 346 then (if i < 345 then [t52,t0,t2,t4,t5,t13,t22,t6,t79] else [t0,t1,t2,t48,t4,t5,t13,t6,t149]) else (if i < 347 then [t58,t0,t1,t2,t51,t4,t13,t22,t6] else [t0,t1,t2,t48,t48,t4,t5,t13,t6])) else (if i < 350 then (if i < 349 then [t0,t1,t2,t48,t4,t96,t5,t13,t6] else [t0,t95,t1,t2,t48,t4,t5,t13,t6]) else (if i < 351 then [t0,t1,t2,t48,t4,t5,t227,t13,t6] else [t97,t0,t1,t4,t5,t13,t22,t6,t71]))))) else (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then [t0,t1,t2,t48,t4,t5,t13,t6,t228] else [t0,t1,t2,t99,t50,t4,t5,t22,t6]) else (if i < 355 then [t0,t1,t2,t48,t4,t4,t5,t13,t6] else [t0,t1,t2,t49,t51,t4,t13,t22])) else (if i < 358 then (if i < 357 then [t0,t1,t2,t49,t51,t4,t13,t22,t6] else [t0,t1,t2,t48,t4,t5,t13,t6,t169]) else (if i < 359 then [t58,t0,t1,t4,t5,t13,t22,t6,t71] else [t0,t1,t2,t48,t4,t5,t13,t6,t70]))) else (if i < 364 then (if i < 362 then (if i < 361 then [t0,t1,t2,t48,t69,t4,t5,t13,t6] else [t0,t1,t2,t48,t51,t4,t13,t6]) else (if i < 363 then [t0,t1,t2,t48,t51,t4,t5,t13,t6] else [t0,t1,t2,t48,t4,t5,t13,t6,t200])) else (if i < 366 then (if i < 365 then [t63,t0,t1,t4,t5,t13,t22,t6,t71] else [t0,t1,t2,t48,t4,t5,t13,t6,t6]) else (if i < 367 then [t0,t1,t2,t49,t48,t4,t5,t13] else [t0,t1,t2,t49,t48,t4,t5,t13,t6])))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then [t0,t1,t2,t77,t4,t5,t13,t22,t6] else [t76,t0,t1,t2,t4,t5,t13,t22,t6]) else (if i < 371 then [t0,t1,t2,t48,t4,t5,t13,t116,t6] else [t61,t0,t1,t2,t50,t4,t5,t22,t6])) else (if i < 374 then (if i < 373 then [t0,t1,t2,t226,t4,t5,t13,t22,t6] else [t88,t0,t1,t2,t4,t5,t13,t22,t6]) else (if i < 375 then [t0,t1,t2,t48,t4,t5,t13,t115,t6] else [t52,t0,t1,t2,t51,t4,t13,t22,t6]))) else (if i < 380 then (if i < 378 then (if i < 377 then [t0,t1,t2,t4,t96,t5,t13,t22,t6] else [t0,t95,t1,t2,t4,t5,t13,t22,t6]) else (if i < 379 then [t0,t1,t2,t229,t4,t5,t13,t22,t6] else [t97,t0,t1,t2,t4,t5,t13,t22,t6])) else (if i < 382 then (if i < 381 then [t0,t1,t2,t48,t4,t5,t13,t6,t230] else [t0,t1,t2,t4,t5,t13,t22,t6,t230]) else (if i < 383 then [t231,t0,t1,t2,t48,t4,t5,t13,t6] else [t231,t0,t1,t2,t4,t5,t13,t22,t6]))))))) else (if i < 448 then (if i < 416 then (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then [t0,t1,t2,t4,t232,t5,t13,t22,t6] else [t0,t1,t2,t99,t4,t5,t13,t22,t6]) else (if i < 387 then [t0,t1,t2,t49,t51,t4,t5,t13,t22] else [t0,t1,t2,t48,t4,t5,t13,t41,t6])) else (if i < 390 then (if i < 389 then [t63,t1,t2,t4,t5,t13,t22,t6,t233] else [t0,t1,t2,t48,t4,t5,t13,t6,t15]) else (if i < 391 then [t54,t0,t1,t4,t5,t13,t22,t6,t71] else [t0,t1,t2,t48,t4,t5,t13,t6,t165]))) else (if i < 396 then (if i < 394 then (if i < 393 then [t58,t1,t2,t4,t5,t13,t22,t6,t233] else [t0,t1,t2,t49,t48,t4,t5,t13,t22]) else (if i < 395 then [t52,t1,t2,t4,t53,t13,t22,t6] else [t52,t0,t1,t2,t4,t53,t13,t22,t6])) else (if i < 398 then (if i < 397 then [t54,t0,t1,t4,t5,t13,t119,t22,t6] else [t0,t1,t2,t4,t5,t13,t115,t6,t165]) else (if i < 399 then [t0,t1,t2,t4,t5,t13,t116,t115,t6] else [t0,t1,t2,t4,t5,t13,t41,t115,t6])))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then [t0,t1,t2,t234,t4,t5,t13,t22,t6] else [t0,t1,t2,t117,t4,t5,t13,t22,t6]) else (if i < 403 then [t122,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t4,t235,t5,t13,t22,t6])) else (if i < 406 then (if i < 405 then [t0,t120,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t4,t5,t236,t13,t22,t6]) else (if i < 407 then [t237,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t4,t5,t238,t13,t22,t6]))) else (if i < 412 then (if i < 410 then (if i < 409 then [t239,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t4,t5,t13,t240,t22,t6]) else (if i < 411 then [t0,t125,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t224,t2,t68,t5,t13,t22,t6])) else (if i < 414 then (if i < 413 then [t0,t1,t224,t2,t49,t4,t5,t13,t22] else [t0,t1,t2,t111,t4,t5,t13,t22,t6]) else (if i < 415 then [t0,t1,t241,t2,t4,t5,t13,t22,t6] else [t242,t0,t1,t2,t4,t5,t13,t22,t6]))))) else (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then [t0,t243,t1,t2,t4,t5,t13,t22,t6] else [t244,t0,t1,t2,t4,t5,t13,t22,t6]) else (if i < 419 then [t0,t1,t2,t4,t245,t5,t13,t22,t6] else [t246,t0,t1,t2,t4,t5,t13,t22,t6])) else (if i < 422 then (if i < 421 then [t0,t1,t247,t2,t4,t5,t13,t22,t6] else [t248,t0,t1,t2,t4,t5,t13,t22,t6]) else (if i < 423 then [t0,t1,t2,t4,t249,t5,t13,t22,t6] else [t250,t0,t1,t2,t4,t5,t13,t22,t6]))) else (if i < 428 then (if i < 426 then (if i < 425 then [t52,t0,t1,t2,t68,t5,t13,t22,t6] else [t52,t0,t1,t2,t49,t4,t5,t13,t22]) else (if i < 427 then [t54,t1,t55,t4,t5,t13,t22,t6] else [t54,t0,t1,t55,t4,t5,t13,t22,t6])) else (if i < 430 then (if i < 429 then [t0,t1,t2,t4,t5,t13,t6,t165,t15] else [t251,t0,t1,t2,t4,t5,t13,t22,t6]) else (if i < 431 then [t146,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t4,t252,t5,t13,t22,t6])))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then [t0,t253,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t55,t49,t4,t5,t13,t22]) else (if i < 435 then [t0,t1,t2,t4,t145,t5,t13,t22,t6] else [t0,t1,t2,t4,t5,t13,t56,t6])) else (if i < 438 then (if i < 437 then [t54,t0,t1,t2,t4,t5,t13,t56,t6] else [t0,t254,t1,t2,t4,t5,t13,t22,t6]) else (if i < 439 then [t0,t1,t2,t4,t5,t13,t22,t57] else [t54,t0,t1,t2,t4,t5,t13,t22,t57]))) else (if i < 444 then (if i < 442 then (if i < 441 then [t0,t1,t2,t4,t74,t5,t13,t22,t6] else [t255,t0,t1,t2,t4,t5,t13,t22,t6]) else (if i < 443 then [t54,t0,t1,t167,t4,t5,t13,t22,t6] else [t54,t63,t1,t2,t4,t5,t13,t22,t6])) else (if i < 446 then (if i < 445 then [t54,t0,t1,t2,t49,t4,t5,t13,t22] else [t58,t1,t2,t59,t5,t13,t22,t6]) else (if i < 447 then [t58,t0,t1,t2,t59,t5,t13,t22,t6] else [t58,t1,t2,t4,t59,t5,t13,t22,t6])))))) else (if i < 480 then (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then [t0,t1,t2,t4,t5,t13,t116,t6,t165] else [t63,t1,t2,t4,t59,t5,t13,t22,t6]) else (if i < 451 then [t118,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t4,t5,t13,t22,t64,t149])) else (if i < 454 then (if i < 453 then [t31,t1,t2,t4,t5,t13,t22,t6] else [t31,t0,t1,t2,t4,t5,t13,t22,t6]) else (if i < 455 then [t31,t1,t2,t4,t5,t13,t22,t6,t149] else [t0,t1,t2,t49,t4,t5,t13,t22,t149]))) else (if i < 460 then (if i < 458 then (if i < 457 then [t0,t1,t2,t4,t5,t13,t22,t149,t70] else [t256,t0,t1,t2,t4,t5,t13,t22,t6]) else (if i < 459 then [t0,t1,t2,t4,t257,t5,t13,t22,t6] else [t166,t0,t1,t2,t4,t5,t13,t22,t6])) else (if i < 462 then (if i < 461 then [t0,t1,t2,t4,t5,t13,t22,t6,t258] else [t0,t1,t2,t180,t4,t5,t13,t22,t6]) else (if i < 463 then [t0,t1,t2,t49,t4,t59,t5,t13,t22] else [t0,t1,t2,t161,t4,t5,t13,t22,t6])))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then [t0,t1,t2,t4,t5,t13,t60,t6] else [t58,t0,t1,t2,t4,t81,t13,t22,t6]) else (if i < 467 then [t0,t259,t1,t2,t4,t5,t13,t22,t6] else [t0,t162,t1,t2,t4,t5,t13,t22,t6])) else (if i < 470 then (if i < 469 then [t0,t1,t260,t2,t4,t5,t13,t22,t6] else [t261,t0,t1,t2,t4,t5,t13,t22,t6]) else (if i < 471 then [t0,t1,t2,t4,t262,t5,t13,t22,t6] else [t263,t0,t1,t2,t4,t5,t13,t22,t6]))) else (if i < 476 then (if i < 474 then (if i < 473 then [t58,t0,t1,t2,t68,t5,t13,t22,t6] else [t58,t0,t1,t2,t49,t4,t5,t13,t22]) else (if i < 475 then [t123,t0,t1,t2,t4,t5,t13,t22,t6] else [t61,t1,t2,t4,t5,t62,t22,t6])) else (if i < 478 then (if i < 477 then [t61,t0,t1,t2,t4,t5,t62,t22,t6] else [t0,t1,t2,t264,t4,t5,t13,t22,t6]) else (if i < 479 then [t0,t168,t1,t2,t4,t5,t13,t22,t6] else [t265,t0,t1,t2,t4,t5,t13,t22,t6]))))) else (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then [t0,t1,t2,t167,t49,t4,t5,t13,t22] else [t0,t1,t2,t4,t194,t5,t13,t22,t6]) else (if i < 483 then [t0,t266,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t4,t267,t5,t13,t22,t6])) else (if i < 486 then (if i < 485 then [t0,t268,t1,t2,t4,t5,t13,t22,t6] else [t61,t0,t1,t2,t49,t4,t5,t13,t22]) else (if i < 487 then [t171,t0,t1,t2,t4,t5,t13,t22,t6] else [t269,t0,t1,t2,t4,t5,t13,t22,t6]))) else (if i < 492 then (if i < 490 then (if i < 489 then [t63,t1,t2,t4,t5,t13,t22,t64] else [t63,t0,t1,t2,t4,t5,t13,t22,t64]) else (if i < 491 then [t63,t1,t2,t4,t5,t13,t22,t6,t64] else [t0,t1,t2,t49,t4,t5,t13,t22,t64])) else (if i < 494 then (if i < 493 then [t0,t1,t2,t270,t4,t5,t13,t22,t6] else [t124,t0,t1,t2,t4,t5,t13,t22,t6]) else (if i < 495 then [t0,t1,t2,t271,t4,t5,t13,t22,t6] else [t0,t1,t2,t49,t4,t225,t5,t13,t22])))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then [t0,t1,t2,t4,t199,t5,t13,t22,t6] else [t0,t1,t2,t4,t5,t13,t32,t6]) else (if i < 499 then [t63,t0,t1,t2,t4,t82,t13,t22,t6] else [t0,t272,t1,t2,t4,t5,t13,t22,t6])) else (if i < 502 then (if i < 501 then [t0,t1,t2,t4,t5,t13,t6,t65] else [t63,t0,t1,t174,t4,t5,t13,t22,t6]) else (if i < 503 then [t0,t159,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t4,t5,t13,t22,t66]))) else (if i < 508 then (if i < 506 then (if i < 505 then [t63,t0,t1,t2,t85,t5,t13,t22,t6] else [t0,t1,t2,t4,t85,t5,t13,t22,t6]) else (if i < 507 then [t0,t1,t2,t4,t5,t13,t67,t6] else [t63,t0,t1,t2,t4,t5,t13,t67,t6])) else (if i < 510 then (if i < 509 then [t0,t1,t273,t2,t4,t5,t13,t22,t6] else [t63,t0,t1,t2,t68,t5,t13,t22,t6]) else (if i < 511 then [t63,t0,t1,t2,t49,t4,t5,t13,t22] else [t0,t1,t2,t49,t4,t4,t5,t13,t22]))))))))) else (if i < 544 then (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then [t0,t1,t2,t49,t213,t4,t5,t13,t22] else [t212,t0,t1,t2,t49,t4,t5,t13,t22]) else (if i < 515 then [t0,t1,t2,t49,t274,t4,t5,t13,t22] else [t214,t0,t1,t2,t68,t5,t13,t22,t6])) else (if i < 518 then (if i < 517 then [t0,t1,t2,t49,t49,t4,t5,t13,t22] else [t0,t1,t2,t49,t4,t218,t5,t13,t22]) else (if i < 519 then [t0,t1,t2,t217,t49,t4,t5,t13,t22] else [t0,t1,t2,t49,t68,t5,t13,t22]))) else (if i < 524 then (if i < 522 then (if i < 521 then [t0,t1,t2,t49,t4,t68,t5,t13,t22] else [t0,t1,t2,t213,t4,t5,t13,t22,t6]) else (if i < 523 then [t212,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t274,t4,t5,t13,t22,t6])) else (if i < 526 then (if i < 525 then [t214,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t4,t218,t5,t13,t22,t6]) else (if i < 527 then [t0,t1,t2,t217,t4,t5,t13,t22,t6] else [t0,t1,t2,t49,t4,t5,t13,t22,t230])))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then [t231,t0,t1,t2,t49,t4,t5,t13,t22] else [t0,t1,t2,t49,t4,t5,t13,t22,t70]) else (if i < 531 then [t0,t1,t2,t49,t69,t4,t5,t13,t22] else [t179,t0,t1,t2,t4,t5,t13,t22,t6])) else (if i < 534 then (if i < 533 then [t0,t1,t2,t69,t5,t13,t22,t70] else [t0,t1,t2,t69,t4,t5,t13,t22,t70]) else (if i < 535 then [t0,t1,t2,t223,t4,t5,t13,t22,t6] else [t0,t1,t2,t275,t4,t5,t13,t22,t6]))) else (if i < 540 then (if i < 538 then (if i < 537 then [t0,t1,t2,t4,t5,t222,t13,t22,t6] else [t0,t1,t2,t4,t5,t13,t22,t6]) else (if i < 539 then [t0,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t48,t4,t5,t13,t6])) else (if i < 542 then (if i < 541 then [t0,t1,t2,t48,t4,t5,t13,t22,t6] else [t0,t1,t224,t2,t4,t5,t13,t22,t6]) else (if i < 543 then [t52,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t55,t4,t5,t13,t22,t6]))))) else (if i < 552 then (if i < 548 then (if i < 546 then (if i < 545 then [t54,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t4,t59,t5,t13,t22,t6]) else (if i < 547 then [t58,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t167,t4,t5,t13,t22,t6])) else (if i < 550 then (if i < 549 then [t61,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t4,t225,t5,t13,t22,t6]) else (if i < 551 then [t63,t0,t1,t2,t4,t5,t13,t22,t6] else [t0,t1,t2,t4,t4,t5,t13,t22,t6]))) else (if i < 556 then (if i < 554 then (if i < 553 then [t0,t1,t2,t49,t4,t5,t13,t22] else [t0,t1,t2,t49,t4,t5,t13,t22,t6]) else (if i < 555 then [t0,t1,t2,t4,t5,t13,t22,t6,t70] else [t0,t1,t2,t69,t4,t5,t13,t22,t6])) else [t0,t1,t2,t4,t5,t13,t22,t6]))))

def sixE (i : Nat) : Nat :=
  let w : Nat := (if (i / 32) < 8 then (if (i / 32) < 4 then (if (i / 32) < 2 then (if (i / 32) < 1 then 0xa00cf7254900002200cc72549000c5203cf92849400c0103ca13e4940002200c9831c900002200cf72549000c5203ca13e49400c5203cc9284940040303cc9284941bc2203c9827c99004030ccc43189400c6f000c03249600c0103cf92609400c3f000f93c0ae00c520ccc4318941bc03000cc31c9600c6f000c73249600c0103cf92849400c0103cc92609400c0103cc9284941bc03000c73309604c0903c9f2609900c0118cd23d09400c0103c9f2849400c0103ca127c941bc03000c0324961bc03000cc300960040303ca13249400c0103c983249400c5203ca1324941480303c9827c9400c0103ca132494 else 0xc6f000cc300960880000c93260900880000c983dc90088000fcd0348901bc03000c931c960040303ca127c940280000c9831c900000a00c9831c900880000c9831c901480303cc9284941480303ca1324940002e03c9827c9900c010ccc43189400c3f000f03e4ae00c5203cf9260940cc2200c96250c4148030ccc4318940fc03000fc3dcae1480303c9f2849404c0903cf9284990fc03000fc3c0ae00c5203c9f2609400c5203cc92609404c0903c983e49900c5218cd23d09400c5203c9f2849400c5203ca127c940fc03000f03e4ae00c5203c98324940880000cf7254900040300099240950002200c9325490) else (if (i / 32) < 3 then 0x18c0f000c9300a218c0f000c931ca200c3f000fc3c0ae0fc03000f93c0ae0cc0118cc83e4c418c0f000c7324a20043318cc83e4c403c63000c9300a218c0f000c7330a200c6f000cc31c960000a03ca225cc01bc03000c03309600c6f000c03309603c63000c0324a20883300c96264c40fc03000f73e4ae03c63000c7324a20fc03000f03f0ae0fc03000f93dcae0202e00cc7254971bc03000c9300960040303c9f260940040303cf92609400c6f000c931c960040303cf9284940040303cc9260940040303c9f284941bc03000c7324960202e00cf7254970040303c98324940880000cc726090028000fc9831c90 else 0x882203cc8320900880000cf72549700403000902709500c010009924095004030009026495020090009924098004030009c240950280000c953dc900280000cc7254900280000c9326090178221bd00260971bc2203ca127c9900c3f000fc3dcae04c0903cc92609900c0103c9827c9400c0103c9f260940000a00c93254900040000cf7254900000a00cc725490178221bcc64009700c3f000f03f0ae0880000c93254900280000cf7254900880000cc725490004030cc983249400c520cc983249400c0103c983e4940880000cc72549700c0118cf9260940040300097264951480303c98324940280003ca0288c0)) else (if (i / 32) < 6 then (if (i / 32) < 5 then 0x100cf7254901bc030009a324961bc03000c92689608822088c43109000000034a028090088000fcc734890088000fcd234090004000fc9831c90004001bc984009000000034f93e4900280a004c731c900000003498260900280a004f03c0900280a00495254900582200ce2254901780000c942549000401004c83209000c0118c983d094088220049826090020161bcc63dc97000000009725c900280a03cf93e4900042e00c9424c900285e00c9424c90088000fc9831c90088001bc98400900580100cf7264900882200494250900882203cf83e0900280000c983dc9000c5203ca13d0940280a00c9826090 else 0x280000cd234090088000fcd026090148030ccf83109400c520cd013249400401004f93e4900880000cf72b8900b80000c942b890148030ccc42e89400000000f93e49003c0000c942549003c000fcd2340970280000cd0254900000100cf8254900280000cf8254900000003c98260900000000cf83e090028000fcd0260900000a03ca0344c00fc03000f73f0ae18c03000fc3dcae148330009931c960580100c9424c9000c5218cc83e4940280003ca0344c00280a03cf83e0900040103cf83e0900040100c98260920000000c98260900040100c98260900882200c9826090004001bd00260900880000c953dc90) else (if (i / 32) < 7 then 0x100d07254900040000cf8254900040100494250920882200499264900000000494250900040100494250900340d00494250900280a004942509000c5203c983e4940280a0ccc9324900882200cf83e09018c0f000c0330a203c63000cc31ca200c0103cee2849408822004f03c09000401034d1344920040303ca13d0940280000cf7260900b80000c942549000c5203c9827c941480303cc9318941480303ca13d0940cc2218cf9320c40886f00c94314c40280a000c731c900280a00c99264900040300097270950880000d002549000401004e338c900280a034d0340900202e00c953dc970280a004f83e090 else 0x401000f93e492004010fcc731c9200401034982609200401004f93e4920340d0349725c900000003cf93e490088220009725c900040103cf93e4920882203cf93e4900040103cc932490004010009725c920280a0009725c900cc01000cc300961785e0349725c90058160349725c900b82e0349725c900000000495254900280a034a0280900000a03ca0288c003c63000c7330a203c63000c931ca2000220fcd034890088000fcc726090088000fcd231c900000a0fc9831c900280a034cc33090088220fcf93e4900280a03cc9324900040000c953dc900285e00c9431c9018c0000c942549008822004f93e490))) else (if (i / 32) < 12 then (if (i / 32) < 10 then (if (i / 32) < 9 then 0x42e00c9431c900580100c9431c900040100099264920040100cc731c910282e00c943dc900880000c9531c9000c5200097270950880000cf72609004c0903cf9260990040303c983e4941480303c983e4940000003499264900280a004f73dc9008822004f73dc90020160009c25c9800401004c93249200c6f000c9300960000000cf73dc9018c0f000c0324a2028000ccf7320c01783f000c7330a20883300c94314c40000000099264900000000cc731c901480303c9727c9400c0103ca027c940040303cc92789400c3f000f93dcae00000034a1284900cc03000c03249603c5e00c9531c9700c6f000c733096 else 0x880000cf0254900882203498260900280000cc72609000000004c731c9000401004c731c9200401004e2388900280a004e2388900280a004c03009000401004f03c09008822004c731c9000000004f03c09000c03004c03009300401004c0300920280a03498260900040100495254900cc0000cf72549008822034ef3bc9003c63000c0330a218c0f000cc31ca20880000cc02549000000000f73dc900582200cc02549000401004e338c920280a004c83209000401004c4310900280a004e338c9000000004e338c9008822004c83209005816004c93249008822004c9324900280a004c93249000401004c932490) else (if (i / 32) < 11 then 0x8822004f43d09000401004f43d09000c0103cc9318940280a0ccf83e090004010ccf83e092000000ccf83e09002800004c73d49002800004f83dc900280a028f93e49008822034a0280900280000c93254900280000d07254900040303ca13e4941780000c942b890004010009725c90004010049725c9200401004c731c900280a0049725c900000a00d07254900000a00d00254900040303cf9284920580100c9b31c9000c0103cf9284921780f00cf725497178221bcf7260970001603c9827c990880000c9524c90178221bcc63dc970280a034d13449003c001bc983dc97178221bc983dc970880000d0725490 else 0x4010049425093088220049b26c9000401034d03409200063004f03e49703c001bc984009708822004c5314900880000ce22549000c3f000f7264ae18c03000f0264ae0880000c953889008822004c03009018c5e0fcd034890000331bcc63c090000031bd00320c00000a00ce2254900000a00c95388900b80a03c90344c00000a00cf02549000000000c93249000401004f03c09200401004f73dc900882203d014049000401004992649000401000c731c90028000cd00258c00fc01000fc3c0ae00433000c0264960040000cc72b8900002200cd0254900280a004f93e4900002200cf82549000c0103c9831094)) else (if (i / 32) < 13 then 0x401000c9324920040103cf93e4900580100cc7260900000003cc9324900042e03ca027c990000a0fcd0348900cc01000c0324960cc01000c733096088000fcd03d490088000fcae31c900280a0049324c9000401004c731c9300401004f73dc930cc01000cc31c960cc03000c7324960fc01000f93c0ae0cc01000c931c960cc01000c93009600c33000cc300960002e0ccc44049900000000982609000c03034a1284930042e00cf7264900285e00cf7264900000000499264900cc0f000f03e49800463000f73f0950fc03000f03e495088001bc983dc900002e00c942b89000c0300099264930280a0009926490 else 0xc0300494250930cc01000c73249600000000c8320900280a004c43109008822004c4310900002200d07254900cc03000c7330960582200c953889000401034a12849208822004f83e09008822000902409008822000cc3309000401004c030090)))
  (w >>> (60 * (i % 32))) &&& 0xfffffffffffffff

def segE (i : Nat) : Nat :=
  (if i < 512 then (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x101 else 0x101) else (if i < 3 then 0xd3000101 else 0xd3000101)) else (if i < 6 then (if i < 5 then 0x101 else 0x1c1000002bf02c501c100040302000505) else (if i < 7 then 0x2c501c101c102bf0000010403 else 0x1c1000002bf02c501c100040302000505))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x101 else 0x3f00050189029901890045018900010006000705) else (if i < 11 then 0x700d3034f00d302c700d301000602 else 0x2bf02bd02c502c50200000403)) else (if i < 14 then (if i < 13 then 0x35303510243035101000402 else 0x25102f5035502f502f502f503000602) else (if i < 15 then 0x101 else 0x2db000101)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0x101 else 0x325031f00000000031f035701e701e701e70000000001000000010a07) else (if i < 19 then 0x2c7000101 else 0x35901bb0000000001bb035901b701b701b70000000001000000010a07)) else (if i < 22 then (if i < 21 then 0x630189003f01890299018901000602 else 0x2990189003f01890045003b0189018900070603000805) else (if i < 23 then 0xd302c7034f02c100d300d300d3000000030000000707 else 0x299004500db004500d1003b0045004500070603000805))) else (if i < 28 then (if i < 26 then (if i < 25 then 0x101 else 0x101) else (if i < 27 then 0x101 else 0x181000101)) else (if i < 30 then (if i < 29 then 0x251000101 else 0x181000101) else (if i < 31 then 0x251000101 else 0x101))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 0x101 else 0x101) else (if i < 35 then 0x45000101 else 0x45000101)) else (if i < 38 then (if i < 37 then 0x45000101 else 0x101) else (if i < 39 then 0x101 else 0x101))) else (if i < 44 then (if i < 42 then (if i < 41 then 0x101 else 0x101) else (if i < 43 then 0x14501450147014501450200000503 else 0x10901b901090109010900040001000505)) else (if i < 46 then (if i < 45 then 0x10f010f0109010f0001000403 else 0xb01b9009b007701b901090057000b000b000b00000509000500090a08) else (if i < 47 then 0x2a3011701e9000001170117011701000002010705 else 0x1b7005700a901e7000b008901b70017000d000d000b000b000b000d0001010100000b01000001010e0c)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 0x21300d3000401 else 0x241000101) else (if i < 51 then 0x2270267026700000127026701270127012701a301000100000001000000010b0b else 0x910045009700450125004505000602)) else (if i < 54 then (if i < 53 then 0x1f300d1003d00d1003d00d10000000100000606 else 0xd1000101) else (if i < 55 then 0x2a500010077000101000402 else 0x101))) else (if i < 60 then (if i < 58 then (if i < 57 then 0x12b000101 else 0x101) else (if i < 59 then 0x101 else 0x101)) else (if i < 62 then (if i < 61 then 0x145000101 else 0x109000101) else (if i < 63 then 0x45000101 else 0x45000101)))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 0x21000101 else 0x45000101) else (if i < 67 then 0x10d000101 else 0xb000101)) else (if i < 70 then (if i < 69 then 0x101 else 0x45000101) else (if i < 71 then 0x2a7000101 else 0x117000101))) else (if i < 76 then (if i < 74 then (if i < 73 then 0xb000101 else 0x22d000101) else (if i < 75 then 0x22d000101 else 0x145000101)) else (if i < 78 then (if i < 77 then 0x241000101 else 0x127000101) else (if i < 79 then 0x1000101 else 0x45000101)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 0x45000101 else 0xd1000101) else (if i < 83 then 0x1000101 else 0x1000101)) else (if i < 86 then (if i < 85 then 0x101 else 0x101) else (if i < 87 then 0x101 else 0x35000101))) else (if i < 92 then (if i < 90 then (if i < 89 then 0x101 else 0x45000101) else (if i < 91 then 0x127000101 else 0x45000101)) else (if i < 94 then (if i < 93 then 0x45000101 else 0x45000101) else (if i < 95 then 0xd1000101 else 0x45000101))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 0x45000101 else 0x241000101) else (if i < 99 then 0x145000101 else 0xb000101)) else (if i < 102 then (if i < 101 then 0x117000101 else 0x45000101) else (if i < 103 then 0x2a9000101 else 0x101))) else (if i < 108 then (if i < 106 then (if i < 105 then 0x101 else 0x101) else (if i < 107 then 0x101 else 0x101)) else (if i < 110 then (if i < 109 then 0xd1000101 else 0x117000101) else (if i < 111 then 0x35000101 else 0x12b000101)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 0x127000101 else 0x45000101) else (if i < 115 then 0xd1000101 else 0xd1000101)) else (if i < 118 then (if i < 117 then 0x45000101 else 0x1090139004500450200000403) else (if i < 119 then 0x1b1000502ab000401 else 0x2ad00350035000401))) else (if i < 124 then (if i < 122 then (if i < 121 then 0x2b102af02b302af01000402 else 0x45000101) else (if i < 123 then 0x45000101 else 0x45000101)) else (if i < 126 then (if i < 125 then 0x45000101 else 0x45000101) else (if i < 127 then 0x45000101 else 0x45000101))))))) else (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 0x45000101 else 0xb000101) else (if i < 131 then 0x45000101 else 0x45000000000202)) else (if i < 134 then (if i < 133 then 0x2b702b902b502b500d3016d013f02b502b500dd02b507010a0000070000000c09 else 0x2b900450045004500d30045004500000102000705) else (if i < 135 then 0x145000101 else 0x145002200000202))) else (if i < 140 then (if i < 138 then (if i < 137 then 0x145000101 else 0x390045003400d300450045004505000004010705) else (if i < 139 then 0xb000b02c1019702bb02bb00cb02bf02bb02bb02bd000d005202bb02bb090403000100060500000300000f0d else 0x2c3021f01690169000d02c702c50169000b016900ef016901c10169000400090600000a0000000500000e0e)) else (if i < 142 then (if i < 141 then 0x173003c0173019b00000173017302c900540173017301000a01000b05 else 0x1b101b9010901090109010901090109060000000001000807) else (if i < 143 then 0x147000101 else 0x1b700a1005d02cb009d0000005d0057005702cf0000005d005701b70057005702cd0203020300000100000001110b)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 0x18f018f02d1018f018f00000100000505 else 0x2d30187018701870000000403) else (if i < 147 then 0x1070107014d00000107010702d50000010703 else 0x14501450147014501450200000503)) else (if i < 150 then (if i < 149 then 0x127026b02d902d90000022702d902270227022702d700040101000001000000020c0b else 0x1b70009000900090000000403) else (if i < 151 then 0xd3021302db00d300d301000201000505 else 0x2df02dd02e102e702e502dd02e902dd02dd02e302dd02dd080000000200000c07))) else (if i < 156 then (if i < 154 then (if i < 153 then 0x970023019702eb000102a50001000000010000000101000906 else 0x2ed00d1000401) else (if i < 155 then 0x2dd004502f302f702f5004502ef02f101890045012501000a02050b05 else 0x2a501a30013000102f9000102fb000100030005000805)) else (if i < 158 then (if i < 157 then 0x45000101 else 0x45000101) else (if i < 159 then 0x45000101 else 0x145006f02fd006f0001000403))))) else (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 0x6f000101 else 0x1b90145007b000401) else (if i < 163 then 0xd3000101 else 0x45000101)) else (if i < 166 then (if i < 165 then 0x45000101 else 0x45000101) else (if i < 167 then 0x45000101 else 0x1c1006000000202))) else (if i < 172 then (if i < 170 then (if i < 169 then 0x10901b90109010901b90109008401090109009c0109010001060000010200000b0a else 0x109008e01b9010900b401090109008601090109010901000009000b05) else (if i < 171 then 0x1c100c000000202 else 0x109000101)) else (if i < 174 then (if i < 173 then 0x2c501c101c102c502c501c101c100060502010705 else 0x1bb0000000001bb01bb01bb01bb01bb01bb02ff01bb02020100000b05) else (if i < 175 then 0x303030100000213023b023b023b023b023b023b030000000000000a07 else 0x103050001000d0001023b0300010603)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 0x45000101 else 0x45000101) else (if i < 179 then 0x32000001c102c502bf01c101c101c101c100000200000501000908 else 0x45000101)) else (if i < 182 then (if i < 181 then 0x45000101 else 0x10f000101) else (if i < 183 then 0x307010d0113010d0109010d0000020103000606 else 0x86023d005701b90089023f000b0000000b000b000b01b9000b01c50903020400010e06))) else (if i < 188 then (if i < 186 then (if i < 185 then 0x30d01090021030b03090109009c010b03090113000b000b000b01110002010100000c01000200010e0c else 0x70109000700070129008505040000050605) else (if i < 187 then 0x970109009d0021000b000b0057000b01090300010001000100040909 else 0x9b000d0077000d00a9030f00e201e700970089000b000d00ea000b000b0057000b0006000101000001010305010c00110e)) else (if i < 190 then (if i < 189 then 0x17702bd01770177017702bd01c10177005201c101770177070300080900000c07 else 0x12a01e1000b007700770132007700970057009701e30106000b00fe01e7000b0077011600a1007701e50077081000070101000907010005000100160f) else (if i < 191 then 0x21000101 else 0x45000101)))))) else (if i < 224 then (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 0xb901090077000b008901b900b4010b009b031300210021002103110006010100000c01000200010e0c else 0x3150315020701420315030f012903170315014a020702070207020700030600000b00000c00020107000e0e) else (if i < 195 then 0x45000101 else 0xd1000101)) else (if i < 198 then (if i < 197 then 0xd1000101 else 0x1e3001701df0140031b00970319009701e700fc007700970097009701e1009702010e0e020106050003000300100d) else (if i < 199 then 0x10901b9010901090109010901b701b50109011401090000080103000a0700000b0a else 0x109010901b701b701090109010901b50000012801b901b501090002000700000006000701060d0c))) else (if i < 204 then (if i < 202 then (if i < 201 then 0x45000101 else 0x2db015000000202) else (if i < 203 then 0x17202a302a302a302a3011701f302a302a3020600010205000907 else 0x3030301030303010213030100000001010000010706)) else (if i < 206 then (if i < 205 then 0x2130303030302130303030303030213021301000705050905 else 0x117018c00000202) else (if i < 207 then 0x117000101 else 0x16f016f01ff016f016f016f0000010100020606)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 0x253000101 else 0x1b701bb02ff01b7030f01b702ff01b701b701b701bb04000300010001040000010b0b) else (if i < 211 then 0x257000101 else 0x19701bf01650001016901a80181000100010001000100010500000000000b08)) else (if i < 214 then (if i < 213 then 0x2302c7003d003d01b0003d003d010000010500000707 else 0x2c70023003d01da003d003d003d0000040101000706) else (if i < 215 then 0x1bc032101f70325000001e7032301ca031f031d019a031d01e701ce01f7019e031f01e7031d0325031f031d031d00000000000314000d031204040a0500000a0600011715 else 0x12701a3012b032b01270327032902710329012701270127032b0a000100000201030000010d0b))) else (if i < 220 then (if i < 218 then (if i < 217 then 0x2a3011701170117011701e90117000102000001000707 else 0xd3000101) else (if i < 219 then 0xb001700e2020200a9005d00a900a9032f031f002100a901bb01ea032d009701bb00a900a90e00010004000e0000060004020000030500001313 else 0xa100970017021e01bb009701e701bb0077009700170097000b001700a9001700010400000c00050201000100100d)) else (if i < 222 then (if i < 221 then 0x1b70057007f01b702320089000b01f2000b0089009b023a0077002101ea0331021e0021008900890089000e000b01110b0000090f010201060001010002011515 else 0xb005d02a50017020202ff000d000b023200970077000d000d00a9000d0333000d080007100e0000030000110a) else (if i < 223 then 0xb000101 else 0xb000101))))) else (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 0x133017d0017017d0335017d007f030201020100010707 else 0xa10337000d0049002100a9008900210021020500170305000102010400060b09) else (if i < 227 then 0x2a5000101bb0001000b00010009000100010005000805 else 0x33d033901ed000003390339033b01000002010705)) else (if i < 230 then (if i < 229 then 0x227000101 else 0xd3000101) else (if i < 231 then 0x2300450045000401 else 0x350017003501250035008900350000000100000806))) else (if i < 236 then (if i < 234 then (if i < 233 then 0xd1000101 else 0x22d000101) else (if i < 235 then 0xd3000101 else 0xd3000101)) else (if i < 238 then (if i < 237 then 0x17000d300d3021d021300d300d3020000040300000707 else 0xd1000101) else (if i < 239 then 0x45000101 else 0x45000101)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 0xd1000101 else 0x45000101) else (if i < 243 then 0x2130045000401 else 0x25700000045000401)) else (if i < 246 then (if i < 245 then 0x1170001000401 else 0x249024c00000202) else (if i < 247 then 0x241000101 else 0x241026a00000202))) else (if i < 252 then (if i < 250 then (if i < 249 then 0x213003d00ef00ef003d01f300ef00020100000705 else 0x97033f00010001030502010003020505) else (if i < 251 then 0x1b1015f0213015f017d015f00010001000605 else 0x1f3027000000202)) else (if i < 254 then (if i < 253 then 0x26f02aa0267026f02960267034101a301a301a302eb01a301a30500010000000c01000d09 else 0x267029f029e027902c602670267012b0000029602670267026704010005000000010005000d0b) else (if i < 255 then 0x227022702e202eb026702710227022702c6026702da0267022702270d0000040100040000000405000e0d else 0x2670267026f02670277026702da01a3026702aa0267070005060000000100000b0a)))))))) else (if i < 384 then (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 0x127000101 else 0x12702f400000202) else (if i < 259 then 0x1f3034301f301f3034501f301f304030100000705 else 0x18103470181018101810000020503)) else (if i < 262 then (if i < 261 then 0x45000101 else 0x45000101) else (if i < 263 then 0x27f000101 else 0x45000101))) else (if i < 268 then (if i < 266 then (if i < 265 then 0x1000101 else 0x45000101) else (if i < 267 then 0x45000101 else 0x290045000d00450125004505000602)) else (if i < 270 then (if i < 269 then 0x3f028e004501e9004500dd0045020100010501000707 else 0x7f0045007700450125004505000602) else (if i < 271 then 0x97000100010349000b03020000030505 else 0x34902aa026f000100890001007700010700020101000806)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 0x45000101 else 0xd1000101) else (if i < 275 then 0x45000101 else 0xd3001b018102b8004500000045000000450100000104000906)) else (if i < 278 then (if i < 277 then 0x4501e9003f00dd004500040201000505 else 0xd1000101) else (if i < 279 then 0xd1000101 else 0x1f0021034b02d8012500d100d100d100d100070000000108000908))) else (if i < 284 then (if i < 282 then (if i < 281 then 0x45000101 else 0x45000101) else (if i < 283 then 0x1000101 else 0x1e500010077000101000402)) else (if i < 286 then (if i < 285 then 0x45000101 else 0x101) else (if i < 287 then 0x101 else 0x297000101))))) else (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 0x101 else 0x35000101) else (if i < 291 then 0x297000101 else 0x81000101)) else (if i < 294 then (if i < 293 then 0x20100ef034d00ef012500ef05000602 else 0x12b030000000202) else (if i < 295 then 0x12b031800000202 else 0x1c000100d1003f0030001800010001000100010045006f00d100260045001a00d3001e004500320045004500d10024004500050000004500d3004500d3006f0000000b00450045004300010005003500d1003f00450045007f004500090000000700d500450218080102252701020a0401020710282e2a030b2d050309320703162308121a1f1418011b00031c210f031a252903332f))) else (if i < 300 then (if i < 298 then (if i < 297 then 0x5000000450001000b0007000b00090005006f0001000100010045000101000c0a0000000a0800010102000f0e else 0x350090006800a8007a004a00600000005200180018001800090000000600000a0300000c0c) else (if i < 299 then 0x4500450035000100350045003500450045003500d30035003500350100020c000d0006010e09 else 0x10049000000d300450101004500010103000100130005009b00c500010045000500050005004f000500c400ff00d10005060000000d00070500000d06001101130603000a07070113001a19)) else (if i < 302 then (if i < 301 then 0x4500c00107006f00450000004500010105006f0019006f007b006f006f003f0101006f00020102060304060803020100120d else 0x100d30109000900450009003500090045000100d800970009007700000009010b0009000900d501000600010e0006020001020201060601000005011515) else (if i < 303 then 0x10f01110049006f00f2010b00f600d8000b00a1008900f00109010800d1000b004500f40113000b00450000010a000b000b0045000b010d00210097010900450001000b000b0000010c00011a001e0a04191d011a18101a07020408000a000f190e1100231e else 0xd30035013a000b000d00170117010d0045000b0077007b002100010119007b00450000000b01150045000b000b004501200077009b000b010f0b020717020613010c060612011501160b00130c0c0001000006011e1b)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 0xd1001d00d3002f0120015600190045004500000117000b00010115000701520045000700010007001d0007000700070c0e000f080004010000000f1203060c0703021813 else 0x11d0109003f004500d3004500450045016a00d1011b00450045000100d30000004500d1001300450045004500001505011104000001050001000c0000010705091615) else (if i < 307 then 0x16800450045004500450035011f00010045004500010045000000000045012100450100000100000a060100080b0200110e else 0x1003f01230035003500d50045003f002100d30125003f0182003f00000089003f000000350000003f0045051404100201000200010409000e06040005010001011616)) else (if i < 310 then (if i < 309 then 0x19a01e40129001d019e01bc018000000045000100ef01270019004501ca0045000101e0000100010001007f0077000b00010000000100450003010a040d0916150603130606080600000109150601010000121c1b else 0x45000b003f004500d300d10007000000d3004500d300d100d300430001004500d300d30200020b090001000000020301000003051211) else (if i < 311 then 0x45007800b400a801f8007c00ac0000008400300030003000090000000600000a0300000c0c else 0x45000500450045003f004500450045004500010045000000010000020200000b0a))) else (if i < 316 then (if i < 314 then (if i < 313 then 0x7000b02100045000100d1012f01310043002b0000012b0043012d0000000d00d300130000004500350043004300d100430043004300ad0501130f010008070600081602000b0206000a05031c15 else 0x102100001000b0045012b00d3012d000000010045004500d30035000000010001000100010200070b090f030001000d0000020000031311) else (if i < 315 then 0x1a001a00010000000303 else 0x100000024000401)) else (if i < 318 then (if i < 317 then 0x32003200010000000303 else 0x18001800010000000303) else (if i < 319 then 0x30003000010000000303 else 0x228001c0258001a0048024002460048025e022e00480a020608040203060102000b0b)))))) else (if i < 352 then (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 0xd1000101 else 0x180005000000180274000501) else (if i < 323 then 0x1c006f0270000100000404 else 0x288000000180009000000000404)) else (if i < 326 then (if i < 325 then 0x18028802d002e803000318000b02a402b8020400000000000907 else 0x35034e001800180330000501) else (if i < 327 then 0x180001033003600100000403 else 0x3780018000b000003920301000503))) else (if i < 332 then (if i < 330 then (if i < 329 then 0x3c000000007000003ac03780018000701 else 0x1c00050000001c03dc000501) else (if i < 331 then 0x18006f03d8000100000404 else 0x180000001803f80045000100000504)) else (if i < 334 then (if i < 333 then 0x45001803f000000000010403 else 0x18001800010000040800000000000505) else (if i < 335 then 0x450001800000440000104680408048004240498020303000104000a07 else 0x4b0001804e0001c006002400244006004c8023400600a020608040203060102000b0b)))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 0x3f000101 else 0x4f800000018003505160203000503) else (if i < 339 then 0x510001e001e052e00010004000503 else 0x54200180018003f0002010403)) else (if i < 342 then (if i < 341 then 0x58a001a0000057e000105a2054005be055a05d2020303000104000a07 else 0x1c0000001c05f00045000100000504) else (if i < 343 then 0x24004505e8000100000404 else 0x1a00050000001a0604000501))) else (if i < 348 then (if i < 346 then (if i < 345 then 0x6f001e060000000000000403 else 0x7f0000063200180618000501) else (if i < 347 then 0x1a0662000700000630064a00000001000705 else 0x3500180018000301)) else (if i < 350 then (if i < 349 then 0x3500180678000000180000000503 else 0xd3000000180678000501) else (if i < 351 then 0x3500000000001806a00000000503 else 0x69000240024000100000000000503))))) else (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 0x3500000018001806ac0000000503 else 0x1c000106a8000100000404) else (if i < 355 then 0x1800d300180000000303 else 0x260003006d8001a0078025804ca007806c204d200780a020608040203060102000b0b)) else (if i < 358 then (if i < 357 then 0x45000101 else 0x180718001806f400d30100000503) else (if i < 359 then 0x70800240728000707300000010503 else 0x7380000004300180100000403))) else (if i < 364 then (if i < 362 then (if i < 361 then 0x18073800010000000403 else 0x248001806d8001a009002400242009006da024a00900a020608040203060102000b0b) else (if i < 363 then 0xd3000101 else 0x7600018001800350002010403)) else (if i < 366 then (if i < 365 then 0x778000107b8002407a40770078c075007ac00240005030000000001010a09 else 0x18000100000001000303) else (if i < 367 then 0x4e8003004e0001800a806d8025c00a806c0026400a80a020608040203060102000b0b else 0x45000101)))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 0x3500450045000000d307ce00010035003500350045003500350035004500350506050100000005000200050f00100e else 0x1d000b00cb013700450005000107e20135006700450035000100000039006f00090019006f013300010001000100011100000310100b090a00010008000209000a03000d01001817) else (if i < 371 then 0x1001800000202 else 0x45001c00000202)) else (if i < 374 then (if i < 373 then 0x7f8000100d300450000002300350045000000350035004500350045003505000701000801030002010702000f0e else 0x450001013d000100d500010045013b01390005006f0045000108140007000100ad000000010001004500010000000107000c01040000010b00030108121612) else (if i < 375 then 0x45001800000202 else 0x6f001a00000202))) else (if i < 380 then (if i < 378 then (if i < 377 then 0xd3003500450035003500350045004500390001003500350000080008010107000507000002010d0d else 0x1000000d300d30045003f00d100d30043000000d3004500d100cb000b00d300d300d30000030f0001000f0000060700060202001211) else (if i < 379 then 0x45001d000000000045003f0045003f013f00d300010035003f013f00d300190035003f003f06000c020100010406000900000000000b1311 else 0x10005000100010001000b004500770001000000090045000100d1000100070045000b0d04000d0c0000010402000c02120f)) else (if i < 382 then (if i < 381 then 0x4500000018000401 else 0xd3000000000045004500000045000100000000000100450045000000450102000102020800050200010102000f0f) else (if i < 383 then 0x4500000018000401 else 0x10045000000000000004500010045000000450000004500000045000000d300450045010000050c0001000001010000010e0000011312))))))) else (if i < 448 then (if i < 416 then (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then 0x45000100d5000100d30045010f000000000045010f000000d10045014101410141000309000008040000050900000200001110 else 0x3f00000045000100d100450001003500dd00010143007f004500010001004300010001000112010101060000050a030004000100000000011313) else (if i < 387 then 0xd3000101 else 0x45001800000202)) else (if i < 390 then (if i < 389 then 0x83e000108820866087a0026084e083600000000000200000808 else 0x45001800000202) else (if i < 391 then 0x24000b08cc08ac08c408dc0898089000000000000200000808 else 0x18000108f80000020303))) else (if i < 396 then (if i < 394 then (if i < 393 then 0x260916090e000700000000020503 else 0x35000101) else (if i < 395 then 0x3ec09900960097803d800c00270092200c00145010101010145014701450145014501450149014901450145014500c00145014501450101010101450101014b09520145093a014501450145060001070e0000000a000d2614100b230e10092103100d24131f11250a100c270a10000118100b2019102826 else 0x107014f0145014d014f00c0010701070145014f010101070145010700c0010701070101014b00020104040202010603000100020e0101021312)) else (if i < 398 then (if i < 397 then 0x1090049015100a1010b09ce0045009b01090a0a0057015b015309e40113015d00a100a10155015901090157004509f400a100a100b909b800a100a10704000b05001015110c001004010604020c16030000190002001e1a else 0x77016f0009016d00d300910163015f015001610a48000d01670001000b01690a220a560165016b000b0009000b002300430077000b000b000b0e00011006080000010a12010600090b0207070a000e100000000000001d1d) else (if i < 399 then 0x15f017d0029010f00f0001f01730a6c017f01610a82000101770029017701790077000d0175017109f0017b001f001f001f00010e0000060c0000120100000800001910 else 0xd100450ab6017d004501610a9a00890091004500d30181019800dd004500d300d1015f004500450a00040b010008020004000001000108001411)))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then 0x45001d00d30045003f00010045003500350045098200d3003f003f003f000503000004010000070900000006001010 else 0xd100010183000100d30035000000450001010900010001000000450a080089001300010001010b018500010001000a000500160a0000040e0b000003000000000b1714) else (if i < 403 then 0x450111004500f40009000900450109006f0001000b0a680113010f01870001010d0045006f000000d1010b000100350001000100010000010c020f0505000a060e01000d0a0b0a0301001b15 else 0x4500d300000045018900450ad2000000450000003500d30aca00450001004500450045000500d100450100110b0705000400140a040400040203001512)) else (if i < 406 then (if i < 405 then 0x890ae20043011700010115004500d1015e0a5800c5018d004500c5018f0000001d002100c500c50a5000c50007018b00c50045015600d300c504130f00070a001a09001900000013150f000000000f03000406150c091d1d else 0x4501970000000501990195004500010afa00d30000000500c5000100450045000100050005004f0000019301910023000500050b12070806001600050201080b000000020001000106071a17) else (if i < 407 then 0x6f004500450000008300cb0101007b0045006f0045000100450000006f006f006b006f050002010c000801070000010400030101001212 else 0x3f00d100450045000000350000004500230109000100dd00010067003f00450045004500450035070101030400030804100405000001140f))) else (if i < 412 then (if i < 410 then (if i < 409 then 0x4501210045019b0045004500450000000100450045004500450035000102030d0601020001010e0b else 0x4500d50000003500000035000100450035003500d30000003500450c00080b00040504020001020304010f0f) else (if i < 411 then 0x9b00570b140ab00b42001901a1019e0001011d000101a5019d0b1c0b2a01a6004500e3000101a30129000100010b5801270ab800450001019f0001001d000100d7000100010045010d200002001b00011316010107000004031a16191a06000105001311001f00012521 else 0x320005000000320964000501)) else (if i < 414 then (if i < 413 then 0x300005000000300994000501 else 0x3509180045003500450001004500d3004500350045003500350000010001020a0000000107000e0d) else (if i < 415 then 0x1000000450001004500010045000101a901010005004500c501a70001000500010001000100d500d30e0201050202020108020802000f050201021512 else 0x45007b007b0b72004500000045006f0105007b001d007b007b007b007b0001003f007b00050100060704100803010200120d))))) else (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then 0x100010045019b000b01ab004500010005006f010f00070009010f0113006f00010000010f000100010001010000120200000e0000000008131510 else 0x11b01050b8e006f0be80ba2006f0145000000cb0bd00045006f00450045006f0bbc00450000007b006f0001006f0045006f0045030005040d020e02010015000308000003020f0013120001011a19) else (if i < 419 then 0x1000b007b003f00450071006f00d3000b0101093a0019000001050073007b0045007b006f007b01050107000b01ad0105010501050105010d0e13000c0b03000012060005000b0e0109000101000c031c19 else 0x1d0c06004500000000004500450045003f0045004500010045004500d3004500000701000800010b080101110a)) else (if i < 422 then (if i < 421 then 0x45004500d3003f0045000100d100dd004500450045000001af006f0045004500d100450102060101110001000707010100120e else 0x4500000045004500450000004500d3000100450045004500450000080100030002000101010e0a) else (if i < 423 then 0x16100dd095000dd0045001b010f000b003f00d3000000dd00dd00dd00d100dd00dd004500dd000106120202000100000d070e070006050308011412 else 0x100450c300c440c64004500000045000100450c5200450c1e0045000000d300450045010000050a0001000001010900010e0000011312))) else (if i < 428 then (if i < 426 then (if i < 425 then 0x32006f0960000100000404 else 0x30006f0990000100000404) else (if i < 427 then 0x1b5000001b70c9401090a0801090c9201b10c84010902880109028a01090cda01b1028e0a0c00d801b30ccc0a0a010901b101b5010901b10cd801090c90010901b101b101090ca801090c960109010901b100d801b301090a0e010901090caa028c00d80000020428000f2b002b052907031507000926170009011200092404000d220b1e061c09000d20170806280300322d else 0x1b10cfc0109010901bb01090109010b010901b501b1010900d80109010900d80109010901b902010d06100001000301010f0b0101000001011313)) else (if i < 430 then (if i < 429 then 0xd1801c301bf01bd019700fb000100d1016f00230009000101b000010d300001000101c10002000100060d000001000a00010e0006011212 else 0x4501c50101004500350045007b00450001006f006f006f00450000006f006f006f0000060a060003010004050002000c01001111) else (if i < 431 then 0xcc000d3004500d30000000000d50045003501c700ef013f003f00010001003900d300450301000002010600000100000601010002011212 else 0x100000001004500d500350035003500d30035004500350000003500350004030401000606080f09)))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then 0x11701c9000001b50d3e00d300970d22001d01cd007f009700a900070097000100d10d3a01cb0045004301be0045004500c901ad000b0097000b001d00770097000012090600000100190500161900000019081a1b140008001100100900201e else 0xcd8000000300009000000000404) else (if i < 435 then 0xc78004500010d5e0d56004500d30d5c0d6800450d540000004500450d6a0001004500450001050300010000020801000005010402001212 else 0x1d108c401d300810d9a01330892010f0135010f0db800050304000101330001010f008102ea02a2010f007900010d8c0133010f000b0dc80001000500f0010f010f017d013301cf00010081007f010f000900f0010f00f009b201cf01d5002f0001008900f00007010f0001010f11341b080900171d09122f0811000b08090001221b2904082c000d132a280d252414040232110b1535001814230f182d3001183733)) else (if i < 438 then (if i < 437 then 0xe100dfa011101130e280089017d0c9001090049000100890017010f01d3008900a1000b00f00089010f000b010f0e400089000100f000210109010f010b0de2008900890089000c0e1e011a0012170f0000170318170017000202120b0400030118021d0c10012321 else 0x18501a70045000000050001009f00fe0005000101d7006f000100bf004500010005006f000700bf0009006f0001000100450e01000000130d000a0f000000010d0005011300000c1a16) else (if i < 439 then 0x1db000b009f08ae01d701d900ad00bb0e8409cc01080091000b000b004902d60021005700a3000d000b008900a700170ea2000b01080e8a0108000b09ec0091009b0cfc00a1000b000b031c0091008909d40057000b0e7c000b000d000d08dc0077009d0ec40e5800570057000d007f010809e402d2000b0318000c260e3538270a390c0b0a17320b38040c3628352c0a10321f002f0412171a041f022c20262423041f0d1d041f2d1332053906223d35 else 0x4900210dfc0df80e440109010b000b0109000b0ca8005701130e4000a1010800970089000b000b000b000b000b0111000d0ed00091000b0108000b000b14000000050109001813001c03000006181615111a0400101905010c09020c1f1f))) else (if i < 444 then (if i < 442 then (if i < 441 then 0x7b00b900d30089000b0017004500a7003f0eea000b010a008901370077000b00d300450021010d010f000b00b9000b0001002101370057004501df0021009b013a001701dd0000000b090004181e0f02200e15111e1920001d00150b09090f102106150114011a251e else 0xf0200450f060f300f1800d1000100cb0045004500d1004500d300450f1c004500d10000004500d100d100d100d100d100020208020004020601010f04000710000102120500001817) else (if i < 443 then 0x9f601090d94010901b70e7c0a08010901b501b10109010901b5010901b901090109011b01090109010901090b06001200030101000003000000090001000201001615 else 0x4901e501e7012901e10021000b01e3000b00890057007701b7008901380ee8000b000b00170f4e0f7a000b0f7e0e880f4a00890f62000b000b000b000b0f03000b130000040f00000300000b0e00000b00030e1b0816001f1a)) else (if i < 446 then (if i < 445 then 0x300cd80ea00d980dcc0dc8000b0d9c0f90020400000000000907 else 0xfb203780634037c070806300fc010080fc4012001eb0120011710200117012001e90117011701170117011701e9011701e901170fda01e9011701170ff2011701200117100002140e1802200518041e0501081c0501001a0501001d05010f1f0501042106012222) else (if i < 447 then 0x1ed0117012001200115011701e901ef01ed01150115011501c901170115011501f1011500000101000005070608000c0000030506001212 else 0x117104e01170117104601f301170117012001e9011701170117011701f50117011700030201000202000004020c00000000011111)))))) else (if i < 480 then (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then 0x101f901fb0007007500010197105401fd000d002901770009000101f7000b01e00005000101ff1082107800010001000715130009060405000d0c0000060500000000001815 else 0x203000b020110dc002110a600770205007710d40077011710ae0057007710e0002110bc007700770207007700020c0908000d0906070001010010010002000101001716) else (if i < 451 then 0x117014d00010001004500070145015201050000006700450a200019006f002f001d001900830019006f00190019001912000a060d0f0a040a0002120c010009000901000c00001817 else 0x127007f1112007f009102130211007f007f007f00570108020f020d000b007f007f020b020900ad10f80008000b0000010400000a0400000104000300041514)) else (if i < 454 then (if i < 453 then 0x21061800a7009d000b007f117011b800bd008900a91136009b000b0e5800bf01380089061c00a1005d0138005700bb021b039400bf0390000d000b0219000d114411a002150219000b00a10217000b08e810e2020102010138106c1068000b00771188000b1140000b013800570a3c118c0057000b01380a38000b00a100a71158000b1f280003210640001733030001022f003c06070d010010381c00033a010f00173a0d0634400f31002f2e2c1226250602201d15001902151a28350c00362206423f else 0xcb00a9000d0d0811d20127010811d60013000d006f000d00890001000d00450023120401bb007f00a1000d0097000d01bc10f8007f000b0021000b1200000b0138000b000d00890045000b006f11ea0057000b000001bb000d000d002b08051602041c18291a262221010d242519000004072000020000000c28171f0200001f1813000b1a0913002e2d) else (if i < 455 then 0x29007f000b01380ff0000d001f021d0089000b00a70213007f00bf0138005700ad007f001f00ad00290201000b007f00d70029007f007f00000a060d00040c0a1201050300040503050104020000021300011d1b else 0x3011b8007f0000000403))) else (if i < 460 then (if i < 458 then (if i < 457 then 0x211021f121a00ad00ad012d001f000000a700ad004300ad00a1007f00910025007f00bb1232012b01c800ad00ad00000109000a00060d000c0201000001001711 else 0xd500010045101800450045124800010045004500d3004500450141004500d10045060a00020601001107) else (if i < 459 then 0xd3000100350035003f004500350045126e003f0000003f0013003f003f003500130045003f00d1003f003f0207000400000100000700040d0003000202001613 else 0x7f012901e400d101fb00011050006b000100450221004500010045000000a90007000b0001004500010001000100000005020806120001010500000a01000d0307011715)) else (if i < 462 then (if i < 461 then 0x10045127a010f000b010d00890045000000000223007b020700d30097000000830045000b007700ad000b000b000b000b000b07031212030d1807000002150400090a00000514021a15 else 0x35022900450001004502270000000b01ca000100d30045022500010001123000ef00010001004500010f02070a0003010a0e0000050200150e) else (if i < 463 then 0x10200030000b000011a20301000503 else 0xd300450fa80001004500451292000112a6003500d30035003500000035004500350704040100000b0409020c030400110e)))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then 0x64c12c800ef003f0001000d003f12d80001000100d300ef0073072a03c200d300d300d303aa12aa090c00d31044009100d3015f00d3000700d100d30073015000f70077000100d300ef000100d300d300350035000500d300ef00d300d300090150000501500105080001240b000106030001072c0c2b2a022c3104002c32070007240c13071f0500191e150016200f0007252900332f else 0x22d01f300850fc0022d12f200c50152022b002f0085002f00850047002f002f01ed022d000b006b002f002f002f100e0704020000060b0a00030d06020800000b0e0e00001717) else (if i < 467 then 0x22f00c5023302310089007b015e0000000b004500770001004500210235001702350045000100d9018f00890005002102310021002100210089002100160a180305031110030817041b03001000000000140c0010011406041e1d else 0x1fb02310045023900090fd8000b00070001023b0077004500010000000d00050001000100010237000502310001000100010d00100a0306000409100600000102000d00010b0000011917)) else (if i < 470 then (if i < 469 then 0x45003f00d30213004500dd00d10045006f00450000000500000045004500d100450002050100030401010007010100110e else 0x1352000100451370132c00000045000000450001004513420045130e0045000000d300450045010000050a0401000001010900010e0000011312) else (if i < 471 then 0xd300dd003f004500dd00dd0043000000d10019012d021d00d300d1000100dd00d3000b004500dd00450045120f110004011106001002160b else 0x100d3004513b4138600000045000000010117007f000113820001000100450001001113a40045000113b000010001101603100a170a03000e01090c0007020800001813))) else (if i < 476 then (if i < 474 then (if i < 473 then 0x3212de12da00000007000100000504 else 0x12a800000007000012ac10200030000701) else (if i < 475 then 0xf2010d005f023d0a8000450107000b01c500d1004500010023023f00230045010f002300230067006f005f0000006f00450023003f01000d030805141108000000010600000c0d02130e0d000f091b19 else 0x24513f8016813e002410187024113da03f00243024d02410241024103fa05f202430249024502450187024113ea016805e8024702410243024b024102450241024502410245011f02410245016802410187024702410241016804090001020d0e010e0d0001020b270129030001240215092b0a00221e0b0018160c0007140d151b1d050023250b002f2f)) else (if i < 478 then (if i < 477 then 0x253011f022102450168024100000251011f024f0249024301870241011f0245011f0168011f011f012100010000000110000504010007010f0002011512 else 0xd314060045003f013f00ef003f010f01c700d50001004500000081004500d300d300d3000f03000007000000010900000402001210) else (if i < 479 then 0x7f004302590045108001410045025701e200d300d100d100db142600d100d1004500d10045025500000109142e002100d1003f09010c02010b100e0001000000010606000a0b00120a040003011a1a else 0x4501c501010045003f007b006f00450001006f0045006f00450000006f006f006f00000605010004070004050002000c01001111))))) else (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then 0x300000003013e80045000100000504 else 0xd300450001004513c80045004500450045004500450500000400000001010b09) else (if i < 483 then 0x4500090005000100450009000101450005000900d500c5025d025f025b00450009000000d300090045000910000e010100090b010000010000160e else 0x10261004500010045003500d30000004500d100d3003f00430043000b01ef004500450045070d10040f00020001010001000100130f)) else (if i < 486 then (if i < 485 then 0x100090005000000450001000b0045010f000700050045010f00050001006f0001006f0001000100010307020000010d0003010802000d0000001413 else 0x45003013e000000000010403) else (if i < 487 then 0x71110004f144601170089006f144201c9000d0089009d0089010a007f0023002100890001000b01dd00450045000101dd0263000b000b00890089004500010b1e00011300110d0a12161903001a19010a000d0000000103000b01201e else 0x102650005011700d10005004500090001004500000001000100070001004500010c0000010a0007010200110a))) else (if i < 492 then (if i < 490 then (if i < 489 then 0x26b026b040c040801270227026714641488012701800127012701270544012701a3027305400127012701800750026f0271012714d00127147401a3026b02671470012702710127012701a314a001270180012714bc02690180026b027114b80267026d026f14e801a3080b1007252d2f07080d120708010a110107082b3110080b3211082322110c1c1a000c171e131f03260d0c0d2d2e08352f else 0x267012701270127026f0180026f02770127012702750277150c0127026b02270127027501290127026b012713030e0000090604050102070001030200010301001615) else (if i < 491 then 0x152e01fb0207026b026f0127012b01290267018001fb0279026f012901290180026b0129012701290207000001fb152601fb0129012901290c0200180a0a0000171b01081913000a030008030701001c17 else 0x1003000000202)) else (if i < 494 then (if i < 493 then 0xd5004500010045008100d1004500d514f800d5004500d500d5003500d50003050100000a040600100a else 0x27d01450021010700e3019a00970045001900010129027b0045006f00010a9800000067001900450019006f007b00190019001912000002100f1103090005090700000d000402000601001a17) else (if i < 495 then 0x450045004500d300010000004501c900d100070001012d00d30035004500450045004504020100001000011001000e0500120e else 0x14d200300030003f0002010403)))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then 0xd101890045153c00451458158a15520281004500d3027f0045004515341560000100450045154a0045004500450d00001604140003000a0204030d09030005040004021716 else 0x235004500d3083415c0077200450045001715b0055c159200450198028300d100f1048204220141006f019815240045007d00170045004901980017003f10a400ef004500d100450017007700d3020100450017019800450045003f0f4800350285000d0198007700d100210045070818060708080611080f1007080a0612201e0a320d04072d000c182c2a29262513040e2b16211e33001a36240e1a0a31011a3733) else (if i < 499 then 0x14700000000016380275160a00010019019a0001001f15da01fb000115f8000100010089162000010001007700010001001d0001000100000d09010d0c0200000000000500050102100104100000001b19 else 0xb00070049023101a60000023100450287000100010001019f00450001009b004500090021001300050231000100010001000100010015061501040516030306150104081403000600000e0a0600001300021d1d)) else (if i < 502 then (if i < 501 then 0x4440043017d00ef008300d1057a00db166800d1000100db043c1652000101b0000100ad0081084200d1003d006f01b0000501b000d1150000d1057200db00d100ef000100d1000901b000d1116800d100d1002101b000d100d100d110b0000716820001010207181202000c0102002c01020400012b041c0117070c29000d262504221f1e0a070c24111a2f31041804140f22052b00073333 else 0x1fb148815f8001d160016c0027701bc00a916a60001000116b800010001001900a700770089000101bc0001000100040001040a09111000030c00000302000003010e0001010000091b1b) else (if i < 503 then 0x2101b5028b000001be000b00770077000502890017009700010089000b00ad023100d9000900170045009b000b01cd006f00a700a900450f60000100770097013a000d00770d000c200d001b000e00141f16041a1e061b001d0f0005000000190010000d071800030708002626 else 0x28f00d100db16ee05a405a000430043000b00d1023100d1078e00d100d100f1046a046e00ef00d1004516ca00d100d1023500d1028d01c800d1023101c8004500ef004300d3002101c800d1004300d10864003d00db007f00d1004500ad00d1002101c800c5007d00d1021b270102280c010207040102080300312d030b2f05030a30080325240d161d1f1219010c00101c230f031d282c03352f))) else (if i < 508 then (if i < 506 then (if i < 505 then 0x16fe02070000160a160e14a016a600d1000100d30227001100d101ca00d1000116fa000100010001002900210089000101ca000100d10003010a040d090d140603110606010600000109110601010000121b1b else 0xef0045000100d100d100ef00d100ef01ca0007004300d100d300450045003f004300d100d1004500d100d5000000d3000d001900d3000b00ef00ef000b050f000c02070000100f00011c01180200110110000500000409001e1d) else (if i < 507 then 0x2b002f00230003001902910027087a01e0000d004d00290001029110d40031001d0001000505ba001d05d2171200770001000d01e001e0000707a40001000f000100010009049c008900010011001b00290f7a01e0000d000d17320001000500010001001317400013000d0001002900021a3518020100282f31332e02010f270c2931180804162f2d0a060d2814011c1f22111c12211e1c121a000d1224110d3430011d3835 else 0x1e0175816fa008901fb01e0000d14b80277162416380001000100190001001d0001000100010077002916b8000100010001000100011305080e120901000001010e070000040100011b13)) else (if i < 510 then (if i < 509 then 0x450005003f004500450045004500d1004500d100000109003b00d30045006f01e60045007b0045004507100602070000000b0206040b0200001305001513 else 0x177200320000165e000115c214d0171615c61712020303000104000a07) else (if i < 511 then 0x159016c815941740000100301674174400000000000905 else 0x3000d300300000000303))))))))) else (if i < 544 then (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then 0x5178800300200000403 else 0x10030178800000000010403) else (if i < 515 then 0x17a2003000450000010403 else 0x1003217a000000000010403)) else (if i < 518 then (if i < 517 then 0x4500300030000301 else 0x17d0003f003017ba17c217ca0004010603) else (if i < 519 then 0x4517ec17f417e817d0003000300600000703 else 0x6cc003006c0003201f806c406c601f806c206ce01f80a020608040203060102000b0b))) else (if i < 524 then (if i < 522 then (if i < 521 then 0x45000101 else 0x1004500450005003f000100ad00050005018b00050045000000a700010001000500050509001100070200050904060000040004001212) else (if i < 523 then 0x5010f0045010d0000006f0001005b0045000b00d1004500450001000100450001000102000800000003000d0000000800010a02001212 else 0x10000004500010000000000450045000100450035004500010207000102020003020c0b)) else (if i < 526 then (if i < 525 then 0x4501c50045010f0293029502970001000d000700010045010d0297007b0045000b00010000023f00010035000100000c010e0209010400060112000a01000000011616 else 0x500d3029b00451812180a00450299003f0000003f1802003f0035000100450045003f0001003f003f003f0e0b110c050400010700040a01020b0001021612) else (if i < 527 then 0xd102590035000b003f181e00d100010043004500450045181a00d300170000025900451826028b004500010045004502000c000d0e0004020f0e020d050300100001010000011817 else 0x4500000030000401)))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then 0x4500000030000401 else 0x43003000000202) else (if i < 531 then 0x1003000000202 else 0x1ca0085012900010007000d000100010007183200191218000000450007000b00010007004501c900ef00d118360001000700450611001406110809000b0400060806000e08000002011a16)) else (if i < 534 then (if i < 533 then 0x73c026d0227012b1860022707460210029d029d012b073a0279073e0279026d026d012b18480210012b02a107380227026d012b021002790227012b012b027902270227012b0210012b0744029f0210012b021005050c0105130c0102010001020b00152519000113052201290800091e0b0001170a0211041216191c0500202319222f2f else 0x12b027900000000026d012b02100227026d012b0210012b026d0000026d012b029f012b012b012d04030700010100130103060201140d) else (if i < 535 then 0x100450045003f0001004518600045004300450045000101020601030003010b0a else 0x901170005022900000021000100010001010f00010045010d0035006f0045000b007b000100450005000100010000030303000d0b000e0000000c1300000400000f001716))) else (if i < 540 then (if i < 538 then (if i < 537 then 0x4500010001004500451848004500450045000000060004000907 else 0x16800ea00da0082011401420152007800d8001801b0004e007a01160108008000e000a80030018200e2014000b8010c007e00e8002a003e007c01800132012201300034009800f4012000f00022004a00d200c2006e00fe01280032006400c000280020005601480138014a003600b0010e013a010a016a004c00ca012a00a000f6006200d00150003c006000480198001a006600fc00f2006c00c800900000005433504a010a3e3601142f2a01292320013d150d01000c0801451a1f011e3547015120) else (if i < 539 then 0x2d00190023000900a800330007001f002900780001001b000f00000018002101080001002f00180210000d0011000100010056000d00310138012200150001000d021401c801f80025000d000700180001001d00d800640001001d001f00010007000b001100050018002b0001007c01e0002700130000010c0001001700f200010001001800900228000d0018006001cc0001002700f600c00013000300114c4c01401c0030062809141241414244031a012200001d024a004b1c0b3e3c4a3b380d342e0f090e2d0009062c2a280617211b45071d09234a084901363709503f else 0x6a804d204ca047c02c005500690031802e8021005740258049e05f80348032002f002b803c00048068803b0044203780478051001d2024a028c06c00600039003f80630033c042003f0036001f005ba04b804b0045c02a8052805a2030002d0058802180260061803a8041602420350043a040e0380000006480660039804280368045404f804e003c8027003d8055801ca048205d00334030802d802a0003003e033504a010a3e3601142f2a01292320013d150d01000c0801451a1f011e3547015120)) else (if i < 542 then (if i < 541 then 0x72c026608a00756025e0828073803e407f8064a06f8078206d806e00768088a06f00710004307700035093008f808d000480724078a0048004804e008ca0048092a003300330048079800350035003f003f0035000b0035003508100035085a0035070800370033003503dc00350033000b003508400035075e0035004800330874003507400035003b0900003307b0003d003b003500350035003300390035003d003f003507f0003300450041003507cc000b002a003d44001c55175716521d54274f2a50054c2c4d00491b4a00572f4e1e46121d1e3e351d0a26351d3352101d094c223c1e010c4305540c4000570c3f1e5a28385c3e else 0x5b000000490330006d006b00590a38005d00150015000500630af8003b09ae0005006009b60060004f005f00050060027000670047006300050a200005000500470060004b07760aaa09ea004d0053003b0ae00a120055002d0065004900200033005100690005006b09f8004d006000050057099e0060000509c60982000500570a50000500050060048000490000005b0005094c004d0ab200050049096c076e0018000500610a900a780031000500600338097a0013000000050ac809f00047000309960060003109ce0051000500090a0a09640005010856005b61240010230207026332624f1c3f4c5e38343b530e5a07684f13192623272f423d27281232584046294a001b20270a4860276c37) else (if i < 543 then 0x7f007b0b1a0071007b00730b74001d000f07940948000f006f0073006f007d0075000f006f02880ba00000007100180078000f007309740b5a006f0c180039000f004b0348000b006f0019006f003700370b6e0073000b006f00780078006f007900280078006f0498008300780b800bea006f006f09600078004b006f0b3000780c00000f006f00390b88006f00810b400078006f07800bba006f00770078000f006f035c0bd20000006f0c30006f0002013f500201513a0201500302014e030201320e2f35312141442b0e100c0d1719394a0e4805001b27230029024e073f415545255835 else 0x2a00018000b0c84008d008d00110009000b02a6000000970090007700110067009000090090008702a400090cf000010c9800890009008b09f00009000b002b0009001700900009000b0cf2008b007f0c6200900009002f008f0c4800950085000900090cc00001003909f40009009308dc0090000b000900910cd8009900090c8609f60009007500900cc2001700850ca200900019001a0009000b09f200850091008508de00090cda0c9a0009000900090009001302a200130c60000b002f00090ca0009000090cb40b0d13181a590c1f4e295d4b5c100c472e34336201590c5701254e0b02306441021a50441b01094942113f063b3600332b292c2854225b56523d120b3b653d))))) else (if i < 552 then (if i < 548 then (if i < 546 then (if i < 545 then 0xab0000009100000b7400a8097c0db200210077005d001802bc02b80077009700a808ea000d0000000b00a30b7200a8002100a80de20c48000b0d220c62009f0d6a007f0d14000b0d240089000b000b0d600c600b76000b00210d5a0057007700a80d8000890d9a0d3800a7000b00a102ba0d980d20000b009b004900a80d3a000b00a90025097a0dfa000b000b097e0dc8000d000d0978000b009d000b000b0b7008e8009f005700a80d3e000b0077000b0d5802be0077009f000000ab000b0db00091007f000d00ad0dca00a50091008900a8000b00970dcc0d82002100a80dce0d3c000b0de0000b000b00a1001a0df8000b00890d260057000b0d680d6200a300a100a800210a0101061a7826023e1a353a04165d7d047942596467086a44001b6b0b6f6a67760f535c7755534d4b00454e3f37730632222f2d29077e21720f144861091a843f else 0xbf00a70eba000b04b20e100f58008900b300770f1a0f7800bb005700bd000b009109a6000b0e280f9000b900a1007f000b000b0f0200890049002100a10e700f3c000b007f0f500304000b000b0f6a00170ea200a1000d0cc0009d00c0005700000e40030000b7000b00c00057000b00210150000b00c0000b0000007704b60021090e00b10f72000b00b50057099e001700570c8605dc0057000d00c1009100c1001800c000c0000b00ad0eea0fa8000b000d00c00e9c0e94000b00c00e6e00c0000b00c000210ed200af00c0000d00bd0e6600c0000b00c00a240a20000b00c06d304a54572927016066004605036801611f625d2100545c3e6a5630193435393e3404014c460a186c0d426f5036126f562c005e25211d1c312a0e4e2f4516713f) else (if i < 547 then 0x106a0000001f000000cd04c8000d0918008500cb001d10180018000700270db0000100d80007001b00a9007700470027001910800007000700050318031c00331062001d00c5103a0007000100d80007002700d800070027105a00c500cf00d80ba405e800190007102210b00007008900d800a700c50001000110980ff0008500c500cb0007004700d8001d00d8015000c500c30007000700c900000e28001d00d800070fda0e400ff4000700170e10101004cc000700a700070ba000270fde00070000103e0fca00c700d800071b221230555a191a1721014f50285f07033226591200050256005150314f3747491c404a484240066100220029394000352d16110d06012c5f24201d03583d673f else 0x116211200020070e036010cc036a09f0112c004f10e20450001a1158045a110000f000130dc800f00045003f00d100450dd20013000009ae00f000d3001300450013009d0f4800d100451156004500d70a8a004500d50013004500d100d30035004500450013003f0045003500450a8000c70f52004510d600450e5e009d00450045115000d3001300d30045071400d110fa003f0e64004509fa00450045006f00451136004500f000450045001300d3004509b4006f00f0004f00130f014200265a0942260101003c572e005355460039001050440228592c4d1452080219571e4a235d06023a5c1e0233170d02305a0d02094f00415e3a)) else (if i < 550 then (if i < 549 then 0x7f0000000000d100d10b72000100000035004500d5004500d30009118a00450720105a0001003f11820108000b00070001072a11020045004500430045006f11d0004500450035010811ce00450382004501080108004510f80bd20001003504680000004511da001801080005037811900108105000010045000111a0006f00d30b780108004511aa11c800450045047200d100450bd810e0004500d100220108000b010800010002083e4d02084d440201110302013a0309333b03241c352a40432b11132c101a0920131e49233503050b2b29093a001e4b3f442f5435 else 0x3500dd003f000d121a09d400c5000b00350ea200d9015000430077003f003f1232003f000d039608ac0041001a012001200045000b003f09cc012000db003f1208124a01200000003f042400db003f0071066e003f00df003f00db0f48003f012000dd0120000b126200890420003511e80ab40120003f0cc0000b012012aa0000003f12c00ab012a6003d003f003f0f4c0120000b1286003f0f7a1210003f003f03920043003f129e003f003f0049003f240101473653042e000139490001574f000151000001504e4b39160626212200403f330326000700362d0d2c280524211e4344001a1345110f052f461a593d) else (if i < 551 then 0x31123000e7001d00010c001330001b13c8001d013800070138001312180001002b0077135001380138000f03ac003900e10138013800000001000500290018003b000100e5013800e1001313fa0001000d1428000100050438000d00010152001900e112e4000d01380c040138000100010e70136a000113080de000e1001d141012f20009002300cb13280138124800010001001d0db200e300e1000d1050000d0029001d1398001b013800191382002f08b8001d067800e3130c0029000100e913fe13b00089005b000113e413e013440005002703a8108012f600010138105413cc000d043c00e16f06515559126618036d251c366c31000302386e28612261390b4b004054090f68745e4d60064844612c34243e3919162e0601221f101b466a6542005a753d else 0x696004100ed00d100f100c800d800c000eb0588000b00ef000d00d3003500dd000b00d3058c00c50198004300d3009100e0000b013000d300730120144000d30692014a007f00d3013a004300d3012800d300ef00350000004900d300d3015000d000d301500594015000000073069e01b0003500ef00430150014200d300ef00e8000d000b01820617191e2a3c182502011c2a0201113d02012f3c0201323b3812251e07353a28070a3115073f232807010003021200040f4110050f4243360f120c020f443d))) else (if i < 556 then (if i < 554 then (if i < 553 then 0x6a80c220c1a11e40e001480020a10b01470022814b2088c0c1e10c00c3010b814780df806ac01800e0811dc141a11d011e014e8020205ac0c34093012d01168149005a00b0412c014881158023815180aee0ae611640cf8146815000fa81458144002300894142211d414aa05a40c38141214a211d8000008880d00116c12c81160115c14d014b806b40af80934149801fa0ae20fb80afc0fb014600cf00168093c33504a010a3e3601142f2a01292320013d150d01000c0801451a1f011e3547015120 else 0x8101570004500050021158a00d3006f0005015208400045004506c405bc14b800d1003f0045151a05b805c401800f000045109a0045154800d5153815c0004515d80045155000451560156815f0004510aa00f3157a15821608004501800005126000050f1000d106c000d3004500210180000500d314280045004715900045003f1268004500d115a800d1003514380045002115400045000501801430004510a20045153000450005000901800f08004501801558127000450180000506cc006f018002030830020333360203393c5258043e5c5c0443020058450200140e52034b1b2d1f0821540e082c4d1f33054e2c290358250b450222041e531614054c1500623f) else (if i < 555 then 0xf2a00430f2200f7162a00fb00430f78060c0091015200430f8200430043004316680150009d0600004300890198019800f300430043000d0198004300f515f00f80000b06020043007f0f8a01980043000d06061630000b0f7a00430f28004301980077019800430f1a0000000b00f3162800f700f7004300f70077019800430049060e00430f1800430f8800171638004300971650019800a7009100000043163200431620000b0604005715f20198019800430f201622165200f900bb004300c50198510426552b35015e0b0a005a36000d2c575f032e4f305122312a420216194e474a440d3445193f1200150b022f195958231038193b192046096239 else 0x10800031168800e1007f001d00051088003900e3002b0001015201b0000700771608008b01b0002701b0001b0043000100e31680061e00010011001d00fd061c01b000fb00cb000101b0000100010013061a000b160a001d00390001002f001300110043001d000100e3015000010033169000e3001706240001000b0001009101b000110005168a1650000116920023000f168201b0165200e30001108a0000000100030001001900f7109000110009169801b01092000100191082163800430000001106180001062606221e0653103a1a434d5b5c5e213361062e5a630605134a06225403502d02280b63453140013c0e573e3a3344490c30504d292552014a481a1300120b653d)) else 0x16800ea00da0082011401420152007800d8001801b0004e007a01160108008000e000a80030018200e2014000b8010c007e00e8002a003e007c01800132012201300034009800f4012000f00022004a00d200c2006e00fe01280032006400c000280020005601480138014a003600b0010e013a010a016a004c00ca012a00a000f6006200d00150003c006000480198001a006600fc00f2006c00c800900000005433504a010a3e3601142f2a01292320013d150d01000c0801451a1f011e3547015120))))

def nsE : Nat → Nat

  | 0 => 0

  | 1 => 0

  | 2 => 0

  | 3 => 0

  | 4 => 0

  | 5 => 0

  | 6 => 0

  | 7 => 34

  | 8 => 261

  | 9 => 242

  | 10 => 19

  | 11 => 1

  | _ => 0

def offE : Nat → Nat

  | 0 => 0

  | 1 => 0

  | 2 => 0

  | 3 => 0

  | 4 => 0

  | 5 => 0

  | 6 => 0

  | 7 => 0

  | 8 => 34

  | 9 => 295

  | 10 => 537

  | 11 => 556

  | _ => 0

def stateE (s i : Nat) := rowsE (offE s + i)

def actionE (s i h : Nat) : Nat :=
  let t := segE (offE s + i)
  let a := t &&& 255
  let b := (t >>> 8) &&& 255
  let d := (t >>> (16 + 8 * (h % a))) &&& 255
  (t >>> (16 + 8 * a + 16 * ((h / a + d) % b))) &&& 65535

def rotateE (g : Nat) (ws : List Nat) : List Nat := match g with

  | 1 => ws.map (blockWord 12 [1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22])

  | 2 => ws.map (blockWord 12 [2, 3, 0, 1, 8, 9, 10, 11, 4, 5, 6, 7, 14, 15, 12, 13, 20, 21, 22, 23, 16, 17, 18, 19])

  | 3 => ws.map (blockWord 12 [3, 2, 1, 0, 9, 8, 11, 10, 5, 4, 7, 6, 15, 14, 13, 12, 21, 20, 23, 22, 17, 16, 19, 18])

  | 4 => ws.map (blockWord 12 [4, 5, 6, 7, 0, 1, 2, 3, 10, 11, 8, 9, 16, 17, 18, 19, 12, 13, 14, 15, 22, 23, 20, 21])

  | 5 => ws.map (blockWord 12 [5, 4, 7, 6, 1, 0, 3, 2, 11, 10, 9, 8, 17, 16, 19, 18, 13, 12, 15, 14, 23, 22, 21, 20])

  | 6 => ws.map (blockWord 12 [6, 7, 4, 5, 10, 11, 8, 9, 0, 1, 2, 3, 18, 19, 16, 17, 22, 23, 20, 21, 12, 13, 14, 15])

  | 7 => ws.map (blockWord 12 [7, 6, 5, 4, 11, 10, 9, 8, 1, 0, 3, 2, 19, 18, 17, 16, 23, 22, 21, 20, 13, 12, 15, 14])

  | 8 => ws.map (blockWord 12 [8, 9, 10, 11, 2, 3, 0, 1, 6, 7, 4, 5, 20, 21, 22, 23, 14, 15, 12, 13, 18, 19, 16, 17])

  | 9 => ws.map (blockWord 12 [9, 8, 11, 10, 3, 2, 1, 0, 7, 6, 5, 4, 21, 20, 23, 22, 15, 14, 13, 12, 19, 18, 17, 16])

  | 10 => ws.map (blockWord 12 [10, 11, 8, 9, 6, 7, 4, 5, 2, 3, 0, 1, 22, 23, 20, 21, 18, 19, 16, 17, 14, 15, 12, 13])

  | 11 => ws.map (blockWord 12 [11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12])

  | _ => ws

theorem rotateE_ok (g : Nat) {s ws} (h : NatRun (mask 144) (goal 144) s ws) :
    NatRun (mask 144) (goal 144) s (rotateE g ws) := by
  unfold rotateE
  split <;> first | exact h | apply block_run h _ _ (by decide +kernel) (by decide +kernel)

def Z (s : Nat) := barrier 144 stateE nsE actionE sixE rotateE s

theorem h7y0 : span (Z 7) 10 0 = true := by decide +kernel

theorem h7y1 : span (Z 7) 10 10 = true := by decide +kernel

theorem h7y2 : span (Z 7) 10 20 = true := by decide +kernel

theorem h7y3 : span (Z 7) 4 30 = true := by decide +kernel

theorem z7 : span (Z 7) 34 0 = true := (@span_join (Z 7) 20 0 14 (@span_join (Z 7) 10 0 10 h7y0 h7y1) (@span_join (Z 7) 10 20 4 h7y2 h7y3))

theorem h8y0 : span (Z 8) 10 0 = true := by decide +kernel

theorem h8y1 : span (Z 8) 10 10 = true := by decide +kernel

theorem h8y2 : span (Z 8) 10 20 = true := by decide +kernel

theorem h8y3 : span (Z 8) 10 30 = true := by decide +kernel

theorem h8y4 : span (Z 8) 10 40 = true := by decide +kernel

theorem h8y5 : span (Z 8) 10 50 = true := by decide +kernel

theorem h8y6 : span (Z 8) 10 60 = true := by decide +kernel

theorem h8y7 : span (Z 8) 10 70 = true := by decide +kernel

theorem h8y8 : span (Z 8) 10 80 = true := by decide +kernel

theorem h8y9 : span (Z 8) 10 90 = true := by decide +kernel

theorem h8y10 : span (Z 8) 10 100 = true := by decide +kernel

theorem h8y11 : span (Z 8) 10 110 = true := by decide +kernel

theorem h8y12 : span (Z 8) 10 120 = true := by decide +kernel

theorem h8y13 : span (Z 8) 10 130 = true := by decide +kernel

theorem h8y14 : span (Z 8) 10 140 = true := by decide +kernel

theorem h8y15 : span (Z 8) 10 150 = true := by decide +kernel

theorem h8y16 : span (Z 8) 10 160 = true := by decide +kernel

theorem h8y17 : span (Z 8) 10 170 = true := by decide +kernel

theorem h8y18 : span (Z 8) 10 180 = true := by decide +kernel

theorem h8y19 : span (Z 8) 10 190 = true := by decide +kernel

theorem h8y20 : span (Z 8) 10 200 = true := by decide +kernel

theorem h8y21 : span (Z 8) 10 210 = true := by decide +kernel

theorem h8y22 : span (Z 8) 10 220 = true := by decide +kernel

theorem h8y23 : span (Z 8) 10 230 = true := by decide +kernel

theorem h8y24 : span (Z 8) 10 240 = true := by decide +kernel

theorem h8y25 : span (Z 8) 10 250 = true := by decide +kernel

theorem h8y26 : span (Z 8) 1 260 = true := by decide +kernel

theorem z8 : span (Z 8) 261 0 = true := (@span_join (Z 8) 160 0 101 (@span_join (Z 8) 80 0 80 (@span_join (Z 8) 40 0 40 (@span_join (Z 8) 20 0 20 (@span_join (Z 8) 10 0 10 h8y0 h8y1) (@span_join (Z 8) 10 20 10 h8y2 h8y3)) (@span_join (Z 8) 20 40 20 (@span_join (Z 8) 10 40 10 h8y4 h8y5) (@span_join (Z 8) 10 60 10 h8y6 h8y7))) (@span_join (Z 8) 40 80 40 (@span_join (Z 8) 20 80 20 (@span_join (Z 8) 10 80 10 h8y8 h8y9) (@span_join (Z 8) 10 100 10 h8y10 h8y11)) (@span_join (Z 8) 20 120 20 (@span_join (Z 8) 10 120 10 h8y12 h8y13) (@span_join (Z 8) 10 140 10 h8y14 h8y15)))) (@span_join (Z 8) 80 160 21 (@span_join (Z 8) 40 160 40 (@span_join (Z 8) 20 160 20 (@span_join (Z 8) 10 160 10 h8y16 h8y17) (@span_join (Z 8) 10 180 10 h8y18 h8y19)) (@span_join (Z 8) 20 200 20 (@span_join (Z 8) 10 200 10 h8y20 h8y21) (@span_join (Z 8) 10 220 10 h8y22 h8y23))) (@span_join (Z 8) 20 240 1 (@span_join (Z 8) 10 240 10 h8y24 h8y25) h8y26)))

theorem h9y0 : span (Z 9) 10 0 = true := by decide +kernel

theorem h9y1 : span (Z 9) 10 10 = true := by decide +kernel

theorem h9y2 : span (Z 9) 10 20 = true := by decide +kernel

theorem h9y3 : span (Z 9) 10 30 = true := by decide +kernel

theorem h9y4 : span (Z 9) 10 40 = true := by decide +kernel

theorem h9y5 : span (Z 9) 10 50 = true := by decide +kernel

theorem h9y6 : span (Z 9) 10 60 = true := by decide +kernel

theorem h9y7 : span (Z 9) 10 70 = true := by decide +kernel

theorem h9y8 : span (Z 9) 10 80 = true := by decide +kernel

theorem h9y9 : span (Z 9) 10 90 = true := by decide +kernel

theorem h9y10 : span (Z 9) 10 100 = true := by decide +kernel

theorem h9y11 : span (Z 9) 10 110 = true := by decide +kernel

theorem h9y12 : span (Z 9) 10 120 = true := by decide +kernel

theorem h9y13 : span (Z 9) 10 130 = true := by decide +kernel

theorem h9y14 : span (Z 9) 10 140 = true := by decide +kernel

theorem h9y15 : span (Z 9) 10 150 = true := by decide +kernel

theorem h9y16 : span (Z 9) 10 160 = true := by decide +kernel

theorem h9y17 : span (Z 9) 10 170 = true := by decide +kernel

theorem h9y18 : span (Z 9) 10 180 = true := by decide +kernel

theorem h9y19 : span (Z 9) 10 190 = true := by decide +kernel

theorem h9y20 : span (Z 9) 10 200 = true := by decide +kernel

theorem h9y21 : span (Z 9) 10 210 = true := by decide +kernel

theorem h9y22 : span (Z 9) 10 220 = true := by decide +kernel

theorem h9y23 : span (Z 9) 10 230 = true := by decide +kernel

theorem h9y24 : span (Z 9) 2 240 = true := by decide +kernel

theorem z9 : span (Z 9) 242 0 = true := (@span_join (Z 9) 160 0 82 (@span_join (Z 9) 80 0 80 (@span_join (Z 9) 40 0 40 (@span_join (Z 9) 20 0 20 (@span_join (Z 9) 10 0 10 h9y0 h9y1) (@span_join (Z 9) 10 20 10 h9y2 h9y3)) (@span_join (Z 9) 20 40 20 (@span_join (Z 9) 10 40 10 h9y4 h9y5) (@span_join (Z 9) 10 60 10 h9y6 h9y7))) (@span_join (Z 9) 40 80 40 (@span_join (Z 9) 20 80 20 (@span_join (Z 9) 10 80 10 h9y8 h9y9) (@span_join (Z 9) 10 100 10 h9y10 h9y11)) (@span_join (Z 9) 20 120 20 (@span_join (Z 9) 10 120 10 h9y12 h9y13) (@span_join (Z 9) 10 140 10 h9y14 h9y15)))) (@span_join (Z 9) 80 160 2 (@span_join (Z 9) 40 160 40 (@span_join (Z 9) 20 160 20 (@span_join (Z 9) 10 160 10 h9y16 h9y17) (@span_join (Z 9) 10 180 10 h9y18 h9y19)) (@span_join (Z 9) 20 200 20 (@span_join (Z 9) 10 200 10 h9y20 h9y21) (@span_join (Z 9) 10 220 10 h9y22 h9y23))) h9y24))

theorem h10y0 : span (Z 10) 10 0 = true := by decide +kernel

theorem h10y1 : span (Z 10) 9 10 = true := by decide +kernel

theorem z10 : span (Z 10) 19 0 = true := (@span_join (Z 10) 10 0 9 h10y0 h10y1)

theorem h11y0 : span (Z 11) 1 0 = true := by decide +kernel

theorem z11 : span (Z 11) 1 0 = true := h11y0

theorem checkedE (s : Nat) (hs : s ≤ 11) : ∀ i < nsE s, Z s i = true := by

  interval_cases s

  · intro i hi; simp [nsE] at hi

  · intro i hi; simp [nsE] at hi

  · intro i hi; simp [nsE] at hi

  · intro i hi; simp [nsE] at hi

  · intro i hi; simp [nsE] at hi

  · intro i hi; simp [nsE] at hi

  · intro i hi; simp [nsE] at hi

  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z9 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z10 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z11 i (Nat.zero_le i) hi

theorem noRunFull (s : Nat) (hs : s ≤ 11) (h : NatRun (mask 144) (goal 144) s xs516) : False := by
  have h11 : NatRun (mask 144) (goal 144) 11 xs516 := extend_run h hs
  have hr : NatRun (mask 144) (goal 144) 11 (rotateE 0 xs516) := rotateE_ok 0 h11
  have p : (rotateE 0 xs516).Perm (stateE 11 0) := by decide +kernel
  exact barrier_all rotateE_ok checkedE 11 (by decide) 0 (by decide) (run_perm p hr)
end Live516

theorem PEqualNP.Outside.L_meta_516 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 1) || (x 0 && x 4) || (x 4 && x 5) || (x 5 && x 1) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 1)) s → 12 ≤ s :=
  Live516.main516 Live516.noRunFull
