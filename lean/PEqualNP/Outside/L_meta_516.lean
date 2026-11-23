import Mathlib
import PEqualNP.Defs

namespace Live516
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    change (wiresFrom gs (w ++ [_])).length = _
    rw [ih]; simp; omega

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (wiresFrom gs (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

abbrev Stat := Sum Bool ℕ

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
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
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
    have h1 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h1]
    have h2 := ih (elimStep n acc g)
    have h3 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    simp only [List.length_cons]
    omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hs => Nat.lt_of_lt_of_le hs h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr j, hs => List.getD_append _ _ _ _ hs

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧
    ∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
      statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv
    have h1 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    have h2 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h1, h2]
    refine ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) ?_
    have hg := hok g List.mem_cons_self
    set W := wiresFrom acc.2 y with hW
    have hWlen : W.length = n + acc.2.length := by rw [hW, length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hss := simplify_sound g.op hg.1 W ins (by simp [hins]; exact hg.2) (by
      intro s hs
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hs
      rw [hWlen]
      exact (hinv.2 i).1)
    set res := simplify g.op (n + acc.2.length) ins with hres
    have hres_eq : simplify g.op W.length ins = res := by rw [hWlen]
    rw [hres_eq] at hss
    have heval : ins.map (statVal W) = g.inputs.map fun i => w.getD i false := by
      simp only [hins, List.map_map]
      apply List.map_congr_left
      intro i _
      exact (hinv.2 i).2
    have hW' : wiresFrom (acc.2 ++ res.1.toList) y = wiresFrom res.1.toList W :=
      wiresFrom_append acc.2 res.1.toList y
    have hstep_len : (elimStep n acc g).1.length = w.length + 1 := by
      simp [elimStep, hinv.1]
    refine ⟨by simp [hstep_len], ?_⟩
    intro i
    change statValid (n + (acc.2 ++ res.1.toList).length)
        ((acc.1 ++ [res.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ res.1.toList) y)
        ((acc.1 ++ [res.2]).getD i (Sum.inl false)) =
        (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).getD i false
    rcases Nat.lt_trichotomy i w.length with hlt | heq | hgt
    · have hlt' : i < acc.1.length := hinv.1.symm ▸ hlt
      rw [List.getD_append _ _ _ _ hlt', List.getD_append _ _ _ _ hlt, hW']
      have hv_old := (hinv.2 i).1
      refine ⟨statValid_mono (by simp) _ hv_old, ?_⟩
      cases hs : acc.1.getD i (Sum.inl false) with
      | inl c =>
        have := (hinv.2 i).2
        rw [hs] at this
        exact this
      | inr j =>
        have hj : j < W.length := by rw [hWlen]; rw [hs] at hv_old; exact hv_old
        have hget := getD_wiresFrom res.1.toList W j hj
        have := (hinv.2 i).2
        rw [hs] at this
        exact hget.trans this
    · subst heq
      rw [getD_snoc_len acc.1 res.2 _ _ hinv.1, getD_snoc_eq, hW', ← heval]
      refine ⟨?_, hss.2⟩
      have h1' : W.length + res.1.toList.length = n + (acc.2 ++ res.1.toList).length := by
        simp [hWlen]; omega
      rw [← h1']
      exact hss.1
    · rw [List.getD_eq_default _ _ (by simp [hinv.1]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.ok {m : ℕ} {g : Gate} (h : CleanGate m g) : Ok g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · exact ⟨by rw [h1]; exact Or.inr (Or.inr rfl), by rw [h2]; simp⟩
  · exact ⟨by rw [h1]; exact Or.inl rfl, by rw [h2]; simp⟩
  · exact ⟨by rw [h1]; exact Or.inr (Or.inl rfl), by rw [h2]; simp⟩

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha; simp at ha; subst ha; exact hj
  · rw [h2] at ha; simp at ha; rcases ha with rfl | rfl; exact hj; exact hk

theorem clean_ok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, Ok g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).ok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, statValid m s) :
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
    | zero =>
      simp at h; subst h; exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) : ℕ → List α → Prop
  | 0, ws => ws = [y]
  | s + 1, ws =>
    (∃ a rest, (a :: rest).Perm ws ∧ ∃ neg save : Bool,
      Run inv meet join y s ((if neg then inv a else a) :: kept save a rest)) ∨
    (∃ a b rest, (a :: b :: rest).Perm ws ∧ ∃ conj ka kb : Bool,
      Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)))

theorem run_done {α : Type} {inv : α → α} {meet join : α → α → α} {y : α} :
    Run inv meet join y 0 [y] := rfl

theorem run_perm {α : Type} {inv : α → α} {meet join : α → α → α} {y : α} {s : ℕ} {xs zs : List α}
    (p : xs.Perm zs) (h : Run inv meet join y s xs) : Run inv meet join y s zs := by
  cases s with
  | zero =>
    change xs = [y] at h
    subst h
    exact List.perm_singleton.1 p.symm
  | succ s =>
    rcases h with ⟨a, rest, hp, neg, save, hr⟩ | ⟨a, b, rest, hp, conj, ka, kb, hr⟩
    · exact Or.inl ⟨a, rest, hp.trans p, neg, save, hr⟩
    · exact Or.inr ⟨a, b, rest, hp.trans p, conj, ka, kb, hr⟩

theorem run_one {α : Type} {inv : α → α} {meet join : α → α → α} {y : α} {s : ℕ} {a : α} {rest : List α}
    (neg save : Bool) (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a rest)) :
    Run inv meet join y (s + 1) (a :: rest) :=
  Or.inl ⟨a, rest, List.Perm.refl _, neg, save, h⟩

theorem run_two {α : Type} {inv : α → α} {meet join : α → α → α} {y : α} {s : ℕ} {a b : α} {rest : List α}
    (conj ka kb : Bool)
    (h : Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest))) :
    Run inv meet join y (s + 1) (a :: b :: rest) :=
  Or.inr ⟨a, b, rest, List.Perm.refl _, conj, ka, kb, h⟩

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
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction s generalizing ws with
  | zero =>
    change ws = [y] at h
    subst h; rfl
  | succ s ih =>
    rcases h with ⟨a, rest, hp, neg, save, hr⟩ | ⟨a, b, rest, hp, conj, ka, kb, hr⟩
    · refine Or.inl ⟨e a, rest.map e, ?_, neg, save, ?_⟩
      · simpa using hp.map e
      · have ih' := ih hr
        have e1 : ((if neg then inv a else a) :: kept save a rest).map e
            = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
          cases neg <;> simp [kept_map, hi]
        rwa [e1] at ih'
    · refine Or.inr ⟨e a, e b, rest.map e, ?_, conj, ka, kb, ?_⟩
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
        have := (hcl q g' hg').lt _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
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
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
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
  have hok : ∀ g ∈ gs, Ok g := clean_ok _ gs hcl
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
    push_neg at hcon
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

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction s generalizing xs with
  | zero => change xs = [y] at h; subst h; simp
  | succ s ih =>
    rcases h with ⟨a, rest, hp, neg, save, hr⟩ | ⟨a, b, rest, hp, conj, ka, kb, hr⟩
    · have hl := hp.length_eq
      have h1 := ih hr
      cases save <;> simp [kept] at h1 hl <;> omega
    · have hl := hp.length_eq
      have h1 := ih hr
      cases ka <;> cases kb <;> simp [kept] at h1 hl <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction s generalizing xs with
  | zero => change xs = [y] at h; subst h; exact hw _ (by simp)
  | succ s ih =>
    rcases h with ⟨a, rest, hp, neg, save, hr⟩ | ⟨a, b, rest, hp, conj, ka, kb, hr⟩
    · apply ih hr
      have hw' : ∀ w ∈ a :: rest, w.testBit i = w.testBit j := fun w hm' => hw w (hp.mem_iff.1 hm')
      have ha := hw' _ List.mem_cons_self
      intro w hmem
      cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        kept, List.mem_cons] at hmem <;>
        first | (rcases hmem with rfl | hr'; exact ha; exact hw' _ (by simp [hr']))
              | (rcases hmem with rfl | hr'; simp [ha, hm]; exact hw' _ (by simp [hr']))
    · apply ih hr
      have hw' : ∀ w ∈ a :: b :: rest, w.testBit i = w.testBit j := fun w hm' => hw w (hp.mem_iff.1 hm')
      have ha := hw' _ List.mem_cons_self
      have hb := hw' _ (List.mem_cons_of_mem _ List.mem_cons_self)
      intro w hmem
      cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
        ite_false, ite_true, kept, List.mem_cons] at hmem <;>
        rcases hmem with rfl | hr' <;> first | simp [ha, hb] | exact hw' _ (by simp only [List.mem_cons]; tauto)

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
      simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k+k by omega, show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

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
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  apply List.any_eq_true.2 ⟨neg, by cases neg <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (run_perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht, hsl2]

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
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (run_perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
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
  · apply next_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply run_perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem next_complete {k s ws} (h : NatRun (mask k) (goal k) (s + 1) ws)
    (zs : List Nat) (q : ws.Perm zs) (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-zs.length) zs f = true := by
  rcases h with ⟨a, rest, hp, neg, save, hr⟩ | ⟨a, b, rest, hp, conj, ka, kb, hr⟩
  · exact next_one (hp.trans q) hr f hf
  · exact next_two (hp.trans q) hr f hf

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
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

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag)

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d+i)
       else if (tag <<< d).testBit i then w.testBit (i-d) else false) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> cases h1 : tag.testBit i <;> cases h2 : tag.testBit (i - d) <;> simp_all

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_run {k s ws} (h : NatRun (mask k) (goal k) s ws) (tag d : Nat)
    (hz : (tag &&& (tag <<< d)) = 0) (hm : moveBits tag d (mask k) = mask k)
    (hy : moveBits tag d (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (moveBits tag d)) := by
  rw [← hy]
  exact run_map _ (fun a => (move_hom tag d hz a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (move_hom tag d hz a b).1) (fun a b => (move_hom tag d hz a b).2.1) h

def move4 (tR1 tL2 tR2 tL1 d w : Nat) : Nat :=
  ((w >>> d) &&& tR1) ||| ((w <<< (2*d)) &&& tL2) |||
  ((w >>> (2*d)) &&& tR2) ||| ((w <<< d) &&& tL1)

theorem moved4 (tR1 tL2 tR2 tL1 d i w : Nat)
    (h12 : tR1 &&& tL2 = 0) (h13 : tR1 &&& tR2 = 0) (h14 : tR1 &&& tL1 = 0)
    (h23 : tL2 &&& tR2 = 0) (h24 : tL2 &&& tL1 = 0) (h34 : tR2 &&& tL1 = 0) :
    (move4 tR1 tL2 tR2 tL1 d w).testBit i =
      if tR1.testBit i then w.testBit (d + i)
      else if tL2.testBit i then (decide (2 * d ≤ i) && w.testBit (i - 2 * d))
      else if tR2.testBit i then w.testBit (2 * d + i)
      else if tL1.testBit i then (decide (d ≤ i) && w.testBit (i - d))
      else false := by
  have d12 := congrArg (fun v : Nat => v.testBit i) h12
  have d13 := congrArg (fun v : Nat => v.testBit i) h13
  have d14 := congrArg (fun v : Nat => v.testBit i) h14
  have d23 := congrArg (fun v : Nat => v.testBit i) h23
  have d24 := congrArg (fun v : Nat => v.testBit i) h24
  have d34 := congrArg (fun v : Nat => v.testBit i) h34
  simp only [Nat.testBit_and, Nat.zero_testBit] at d12 d13 d14 d23 d24 d34
  simp only [move4, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  by_cases hi1 : d ≤ i <;> by_cases hi2 : 2 * d ≤ i <;>
    cases h1 : tR1.testBit i <;> cases h2 : tL2.testBit i <;>
    cases h3 : tR2.testBit i <;> cases h4 : tL1.testBit i <;>
    simp_all

theorem move4_hom (tR1 tL2 tR2 tL1 d : Nat)
    (h12 : tR1 &&& tL2 = 0) (h13 : tR1 &&& tR2 = 0) (h14 : tR1 &&& tL1 = 0)
    (h23 : tL2 &&& tR2 = 0) (h24 : tL2 &&& tL1 = 0) (h34 : tR2 &&& tL1 = 0) (a b : Nat) :
    move4 tR1 tL2 tR2 tL1 d (a &&& b) = (move4 tR1 tL2 tR2 tL1 d a &&& move4 tR1 tL2 tR2 tL1 d b) ∧
    move4 tR1 tL2 tR2 tL1 d (a ||| b) = (move4 tR1 tL2 tR2 tL1 d a ||| move4 tR1 tL2 tR2 tL1 d b) ∧
    move4 tR1 tL2 tR2 tL1 d (a ^^^ b) = (move4 tR1 tL2 tR2 tL1 d a ^^^ move4 tR1 tL2 tR2 tL1 d b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
      moved4 tR1 tL2 tR2 tL1 d i _ h12 h13 h14 h23 h24 h34] <;>
    split_ifs <;> cases h1 : decide (2 * d ≤ i) <;> cases h2 : decide (d ≤ i) <;> simp

theorem move4_run {k s ws} (h : NatRun (mask k) (goal k) s ws) (tR1 tL2 tR2 tL1 d : Nat)
    (h12 : tR1 &&& tL2 = 0) (h13 : tR1 &&& tR2 = 0) (h14 : tR1 &&& tL1 = 0)
    (h23 : tL2 &&& tR2 = 0) (h24 : tL2 &&& tL1 = 0) (h34 : tR2 &&& tL1 = 0)
    (hm : move4 tR1 tL2 tR2 tL1 d (mask k) = mask k)
    (hy : move4 tR1 tL2 tR2 tL1 d (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (move4 tR1 tL2 tR2 tL1 d)) := by
  rw [← hy]
  exact run_map _
    (fun a => (move4_hom tR1 tL2 tR2 tL1 d h12 h13 h14 h23 h24 h34 a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (move4_hom tR1 tL2 tR2 tL1 d h12 h13 h14 h23 h24 h34 a b).1)
    (fun a b => (move4_hom tR1 tL2 tR2 tL1 d h12 h13 h14 h23 h24 h34 a b).2.1) h

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction s generalizing ws with
  | zero => change ws = [y] at h; subst h; exact hw _ (by simp)
  | succ s ih =>
    rcases h with ⟨a, rest, hp, neg, save, hr⟩ | ⟨a, b, rest, hp, conj, ka, kb, hr⟩
    · have hh := run_len hr
      have hpl := hp.length_eq
      cases save <;> simp [kept] at hh hl hpl <;> omega
    · have hh := run_len hr
      have hpl := hp.length_eq
      cases ka <;> cases kb <;> simp [kept] at hh hl hpl <;> try omega
      apply ih hr (by simp [kept]; omega)
      have hw' : ∀ w ∈ a :: b :: rest, w.testBit i ≤ w.testBit j := fun w hm => hw w (hp.mem_iff.1 hm)
      have ha := hw' _ List.mem_cons_self
      have hb := hw' _ (List.mem_cons_of_mem _ List.mem_cons_self)
      intro w had
      simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
      rcases had with rfl | ht
      · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;>
          cases hai : a.testBit i <;> cases haj : a.testBit j <;>
          cases hbi : b.testBit i <;> cases hbj : b.testBit j <;> simp_all
      · exact hw' _ (by simp [ht])

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
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers, he, required_up h he]
  · simp [covers, he, required h]

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

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction s generalizing ws with
  | zero => change ws = [y] at h; subst h; simp
  | succ s ih =>
    rcases h with ⟨a, rest, hp, neg, save, hr⟩ | ⟨a, b, rest, hp, conj, ka, kb, hr⟩
    · have hh := run_len hr
      have hpl := hp.length_eq
      cases save <;> simp [kept] at hh hl hpl <;> omega
    · have hh := run_len hr
      have hpl := hp.length_eq
      cases ka <;> cases kb <;> simp [kept] at hh hl hpl <;> try omega
      have ih' := ih hr (by simp [kept]; omega)
      rw [← (hp.map v).sum_eq]
      cases conj <;> simp [kept] at ih' ⊢
      · have hle := hor a b; omega
      · have hle := hand a b; omega

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6, Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, Nat.testBit_or] using value6_or
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
    · simp [hl, Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
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
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩

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
    obtain ⟨q, hq, j, hj, h⟩ := barrier_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

abbrev f516 : BFn 8 := fun x : Fin 8 → Bool =>
  (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 1) ||
  (x 0 && x 4) || (x 4 && x 5) || (x 5 && x 1) ||
  (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 1)

def rows516 : List ℕ := [1, 3, 4, 4, 6, 6, 6, 20, 20, 22, 22, 22, 24, 24, 84, 84, 86, 86, 88, 88, 88, 88, 1, 3, 16, 16, 18, 18, 18, 80, 80, 82, 82, 82, 96, 96, 84, 84, 86, 86, 100, 100, 100, 100, 1, 3, 64, 64, 66, 66, 66, 68, 68, 70, 70, 70, 132, 132, 84, 84, 86, 86, 148, 148, 148, 148, 1, 3, 16, 16, 18, 18, 18, 20, 20, 22, 22, 22, 36, 36, 84, 84, 86, 86, 100, 100, 100, 100, 1, 3, 4, 4, 6, 6, 6, 68, 68, 70, 70, 70, 72, 72, 84, 84, 86, 86, 88, 88, 88, 88, 1, 3, 64, 64, 66, 66, 66, 80, 80, 82, 82, 82, 144, 144, 84, 84, 86, 86, 148, 148, 148, 148, 2, 3, 8, 8, 9, 9, 9, 40, 40, 41, 41, 41, 36, 36, 168, 168, 169, 169, 164, 164, 164, 164, 2, 3, 32, 32, 33, 33, 33, 160, 160, 161, 161, 161, 144, 144, 168, 168, 169, 169, 152, 152, 152, 152, 2, 3, 128, 128, 129, 129, 129, 136, 136, 137, 137, 137, 72, 72, 168, 168, 169, 169, 104, 104, 104, 104, 2, 3, 32, 32, 33, 33, 33, 40, 40, 41, 41, 41, 24, 24, 168, 168, 169, 169, 152, 152, 152, 152, 2, 3, 8, 8, 9, 9, 9, 136, 136, 137, 137, 137, 132, 132, 168, 168, 169, 169, 164, 164, 164, 164, 2, 3, 128, 128, 129, 129, 129, 160, 160, 161, 161, 161, 96, 96, 168, 168, 169, 169, 104, 104, 104, 104, 5, 7, 5, 12, 7, 14, 38, 21, 28, 23, 30, 150, 25, 28, 85, 92, 87, 94, 89, 90, 92, 120, 17, 19, 17, 48, 19, 50, 146, 81, 112, 83, 114, 90, 97, 112, 85, 116, 87, 118, 101, 102, 116, 228, 65, 67, 65, 192, 67, 194, 74, 69, 196, 71, 198, 102, 133, 196, 85, 212, 87, 214, 149, 150, 212, 156, 17, 19, 17, 48, 19, 50, 26, 21, 52, 23, 54, 150, 37, 52, 85, 116, 87, 118, 101, 102, 116, 108, 5, 7, 5, 12, 7, 14, 134, 69, 76, 71, 78, 102, 73, 76, 85, 92, 87, 94, 89, 90, 92, 216, 65, 67, 65, 192, 67, 194, 98, 81, 208, 83, 210, 90, 145, 208, 85, 212, 87, 214, 149, 150, 212, 180, 10, 11, 10, 12, 11, 13, 25, 42, 44, 43, 45, 105, 38, 44, 170, 172, 171, 173, 166, 165, 172, 180, 34, 35, 34, 48, 35, 49, 97, 162, 176, 163, 177, 165, 146, 176, 170, 184, 171, 185, 154, 153, 184, 216, 130, 131, 130, 192, 131, 193, 133, 138, 200, 139, 201, 153, 74, 200, 170, 232, 171, 233, 106, 105, 232, 108, 34, 35, 34, 48, 35, 49, 37, 42, 56, 43, 57, 105, 26, 56, 170, 184, 171, 185, 154, 153, 184, 156, 10, 11, 10, 12, 11, 13, 73, 138, 140, 139, 141, 153, 134, 140, 170, 172, 171, 173, 166, 165, 172, 228, 130, 131, 130, 192, 131, 193, 145, 162, 224, 163, 225, 165, 98, 224, 170, 232, 171, 233, 106, 105, 232, 120]

def xs516 : List ℕ := [0x2c39c8b0e722c39c8b0e722c39c8b0e72154a5c55297154a5c55297154a5c552970c39c830e720c39c830e720c39c830e7200000c0000300000c0000300000c00003, 0x154a5c55297154a5c55297154a5c552972c39c8b0e722c39c8b0e722c39c8b0e7200000c0000300000c0000300000c000030c39c830e720c39c830e720c39c830e72, 0x2003eb52880010200040002003eb528ff00013effffffe03fff80ff00013efff000003c300000000000000000003c3000ff00003cffcfffe03fff80ff00003cffc, 0xff00013effffffe03fff80ff00013efff002003eb52880010200040002003eb528ff00003cffcfffe03fff80ff00003cffc000003c300000000000000000003c3000, 0x80010000800fad4a000800fad4a200040fffe03fc0004fbffffc0004fbffffff8000000000000f0c00000000f0c00000000fffe03fc0000f3ff3fc0000f3ff3fff80, 0xfffe03fc0004fbffffc0004fbffffff8080010000800fad4a000800fad4a200040fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000, 0xfad4a200040002003eb528800100008004fbffffff80ff00013effffffe03fc000f0c00000000000003c3000000000000000f3ff3fff80ff00003cffcfffe03fc000, 0x4fbffffff80ff00013effffffe03fc000fad4a200040002003eb528800100008000f3ff3fff80ff00003cffcfffe03fc000f0c00000000000003c300000000000000]

def deltaF : Nat := 0xfffffffffffffffffffffffffffffffff000000000000000000000000000000000fffffffffffffffffffffffffffffffff
def deltaT : Nat := 0x3ffffffffffffffff00000000000000003ffffffffffffffff00000000000000003ffffffffffffffff00000000000000003ffffffffffffffff
def maskR1 : Nat := 0xfffffffffff0000000000000000000000fffffffffff0000000000000000000000fffffffffff0000000000000000000000fffffffffff
def maskL2 : Nat := 0x3fffff0000000000000000000000000003fffff0000000000000000000000000003fffff0000000000000000000000000003fffff00000000000
def maskR2 : Nat := 0xfffffc000000000000000000000000000fffffc000000000000000000000000000fffffc000000000000000000000000000fffffc0000000000000000
def maskL1 : Nat := 0xfffffffffff0000000000000000000000fffffffffff0000000000000000000000fffffffffff0000000000000000000000fffffffffff0000000000000000000000

def t1 : Nat := 0x0
def t2 : Nat := 0x810800000008108000000000000000000000000000000000000000000000000000000000000000000000000
def t3 : Nat := 0x40000102120408001020004000010212000000000000000000000000000000000000000000000000000000000000000000
def t4 : Nat := 0x50000142801500001428015000014000000000000000000000000000000000000000000000000000000000000000000000
def t5 : Nat := 0xc000030e002c000030e002c0000300000000000000000000000000000000000000c000030e000c000030e000c000030000
def t6 : Nat := 0x4f00013c0004f00013c0004f00013c0000000000000000000000000000000000000f00003c0000f00003c0000f00003c000
def t7 : Nat := 0x200000800000000004a9400000004a000000000000000000000000000000000000000000000000000000000000000000000000000
def t8 : Nat := 0x100000000001040000000028100000000002000a000000010000800000000000000000000000000000000000000000000000000000000000000000000
def t9 : Nat := 0x10400000000104000000002c3800b00000c39c8b00000c39c8b0e000000000000000000000000000000000000c3800300000c39c0300000c39c030e00
def t10 : Nat := 0x8000000000000000200000fa000000000002003e800000000000800000000000000000000000000000000000f0000000000000003c000000000000000
def t11 : Nat := 0x8000000000000000200000ff00013c0004fbe03fc0004f00013ef80000000000000000000000000000000000ff00003c0000f3e03fc0000f00003cf80
def t12 : Nat := 0x9040000000010400200000ff3801bc0004fbfcbfc0004f39c9bef80000000000000000000000000000000000ff38003c0000f3fc3fc0000f39c03cf80
def t13 : Nat := 0x2800010200000000000035280500013efbfffde0014a807f00013e7ff0000000000000000000000000000030000f00003cffcfffe003cf80ff00003cffc
def t14 : Nat := 0x3f00dffc000000000fc037ff0000000003f00dffc000000000fc037ff00000c0007f00fffc000030001fc03fff00000c0007f00fffc000030001fc03fff
def t15 : Nat := 0x7f004000010000000000007f052a5dff7bf050b5c142d7052a5dff7bf00000c0007f00c00c0300300000c0007f0f3ffffffff0f3ffc3cfff0f3ffffffff
def t16 : Nat := 0x2fffb0400003f80b000000007f002003eb52800010200040002001eb52800000000ffcf0c00003f80f000000007c000003c300000000000000000003c3000
def t17 : Nat := 0x4100010400000000104000410002c3800b0e722c39c8b0e002c39c8b0e720000000000000000000000000000000000c380030e700c39c030e000c39c030e70
def t18 : Nat := 0x12a528800002000000000012a5280000012a528800002000000000012a528000000000000000000000000000000000000000000000000000000000000000000
def t19 : Nat := 0x12a528800002000000000032a528ff00013e528cfbe03fc0004f00013efa8000000000000000000000000000000000ff00003c0000f3e03fc0000f00003cf80
def t20 : Nat := 0x12afffb0400203f80b000012a57f002003eb52880010200040002001eb52800000000ffcf0c00003f80f000000007c000003c300000000000000000003c3000
def t21 : Nat := 0x16b528800002000000000016b5282c00013af7aac3802b0e002c00013af7a0000000000000000000000000000000000c000030e700c380030e000c000030e70
def t22 : Nat := 0x2000008000020000000000200000ff00013ef80ffbe03fef80ff00013ef80000000000000000000000000000000000ff00003cf80ff3e03fcf80ff00003cf80
def t23 : Nat := 0x34b108800002000000000034b108ea00012ad68eab403aad00ea00012ad68000003c300000000000000000003c3000ff00003cffcfffe03fff80ff00003cffc
def t24 : Nat := 0x340318d9040000318d9040000000d6ab4a3aa568002103aa568002101aad280000340318df0c0040318df0c0040000dfffff3ffffc0f3ff3ffffc0f3ff3ffffc
def t25 : Nat := 0x34031ff9040000318d9040000007f6fbeffff7ff052b5fbe7ff052b5dfffbf00003c031fff0c00c0318ff0c00c0007ffffffffffff0f3ffffffff0f3ffffffff
def t26 : Nat := 0x5c0129710400001297104000000172c38c8b0672042948b0672042948b0e3200000c0000300000c0000300000c000030c39c830e720c39c830e720c39c830e72
def t27 : Nat := 0xfc037ff904000037ff9040000003f6ab4ffab7ff002103ab7ff002101aad3f0001fc03ffff0c00c03ffff0c00c0007ffffffffffff0f3ffffffff0f3ffffffff
def t28 : Nat := 0x100008002810800080028108000040154a0054000050a5c54000050a5c55280000000000000000000000000000000000000000000000000000000000000000000
def t29 : Nat := 0x1000080038508000800385080000403d7a00f40000d3bdcf40000d3bdcf5e800000000000000000000000000000000000c3800300000c39c0300000c39c030e00
def t30 : Nat := 0x10000800a810800080028108200040ff4a017c0004fbe5ffc0004f0a5d7ff80000000000000000000000000000000000ff00003c0000f3e03fc0000f00003cf80
def t31 : Nat := 0x10000800b0400000800b04000000407ffe03fc000052b5ffc000052b5dfff8000000000000f0c00000000f0c00000000fffe03fc0000f3ff3fc0000f3ff3fff80
def t32 : Nat := 0x10000800fa000000800fad40200000fad40200000002003e80000001000080000000000000f0000000000f0c00000000f0c00000000000003c000000000000000
def t33 : Nat := 0x10000800fa000000800fad40200000ffd4033c0004fbe03fc0004f01013ef8000000000000f0000000000f0c00000000ffc0003c0000f3e03fc0000f00003cf80
def t34 : Nat := 0x10000800fa108000800fad48200040ffde0254000052a5ffc000050b5c55a8000000000000f0000000000f0c00000000f0c00000000000003c000000000000000
def t35 : Nat := 0x10000800fa400000800fad40200000fefc02b00000c39cbf80000c39c8b0e0000000000000f0000000000f0c00000000fcf800300000c39c3f00000c39c030e00
def t36 : Nat := 0x15c01a97b0400001a97b04000000577ffecbfc672052b5ffc672052b5dfffb200000c00003f0c00c00003f0c00c00003ffffcbfce720f3ffbfce720f3ffbffff2
def t37 : Nat := 0x15c03fbfb0400000ad73040000007f3040000007f002b5ec100000015c03fbf0001fc03ffff0c00c00ffff0c00c0007ff0c00c0007f003fffc30030001fc03fff
def t38 : Nat := 0x15c03fffb0400001ad73040000007f356a5dff7ff052b5ed52d7052b5dfffbf0001fc03ffff0c00c03ffff0c00c0007ffffffffffff0f3ffffffff0f3ffffffff
def t39 : Nat := 0x17c03fbfb0400003bdfb040000007f7af4a3aa57f002b5feb56800215dabfbf0001fc03ffff0c00c03ffff0c00c0007ffffffffffff0f3ffffffff0f3ffffffff
def t40 : Nat := 0x1a002d68a0000002d68a000000006853c6374f18d0102174f18d0102154f18d0001f003ffcf0c00003ffcf0c0000007cf3c637cf18d030637cf18d030637cf18d
def t41 : Nat := 0x1a002d7fa0400003d68a000000007f57ee7fff7bf050b5f5f3df052a5dff7bf0001fc03ffff0c00c03ffff0c00c0007ffffffffffff0f3ffffffff0f3ffffffff
def t42 : Nat := 0x1c800e7220000000e7220000000072154a5c55297050a5c55297050a5c552970001c800e7200000800e720000080007200000c0000300000c0000300000c00003
def t43 : Nat := 0x1fc03fffb0400003fffb040000007f7ffeffff7ff052b5fff7ff052b5dfffbf0001fc03ffff0c00c03ffff0c00c0007ffffffffffff0f3ffffffff0f3ffffffff
def t44 : Nat := 0x1fc03fffb8508003fffb850800007f7ffeffff7ff052b5fff7ff052b5dfffbf0001fc03ffff0c00c03ffff0c00c0007ffffffffffff0f3ffffffff0f3ffffffff
def t45 : Nat := 0x1fd2bfffb0400203fffb040012a57f7ffeffff7ff852b5fff7ff052b5dfffbf0001fc03ffff0c00c03ffff0c00c0007ffffffffffff0f3ffffffff0f3ffffffff
def t46 : Nat := 0x2000a042000010000040002000a042015000014297154a005528015000014297000000000000000000000000000000000000000000000000000000000000000000
def t47 : Nat := 0x2001aa52880010200040002001aa5281500013e7bf954a02552801500013e7bf000000000000000000000000000000000000000000000000000000000000000000
def t48 : Nat := 0x2001aa52880010200040002003aa528ff00013e7bfdffe03fd2805f00013efbf000000000000000000000000000000000ff00003c0000f3e03fc0000f00003cf80
def t49 : Nat := 0x2001eb52880010200040002001eb5283d00013efffbd7a02f5e803d00013efff0000000000000000000000000000000000c000030e700c380030e000c000030e70
def t50 : Nat := 0x2001eb52880010200040002003eb528b500013effffffe02d5a807f00013efff000003c300000000000000000003c3000ff00003cffcfffe03fff80ff00003cffc
def t51 : Nat := 0x2003aa52880010200040002003aa528d300010e18dd3c6034f180d300010e18d000003c300000000000000000003c3000f300000c18cf3c603cf180f300000c18c
def t52 : Nat := 0x2003aa52880010200040002003aa528d700011e39fd7ce035f380d700011e39f000003c300000000000000000003c3000f300000c18cf3c603cf180f300000c18c
def t53 : Nat := 0x2003aa52880010200040002003ab528d700013efbfffde035fb80ff00013e7ff000003c300000000000000000003c3000ff00003cffcfffe03fff80ff00003cffc
def t54 : Nat := 0x2003e800080010200000002003eb500ff00013c800fffe03fc800ff00013efc0000003c000000000000000000003c3000ff00003c000fffe03fc000ff00003cf80
def t55 : Nat := 0x2003ea52880010200000002003eb5288000012ad28fad40200800fa00012a568000003c000000000000000000003c300000000000000f0c00000000f0000000000
def t56 : Nat := 0x2003ea52880010200040002003eb5289500013efbfffde0255a80ff00013e7ff000003c000000000000000000003c300000000000000f0c00000000f0000000000
def t57 : Nat := 0x2003eb50080010200040002003eb500fa000000840faf403ebd00fa000000840000003c300000000000000000003c3000f0000000000f0c003c3000f0000000000
def t58 : Nat := 0x2003eb52880010200040002003eb528d300010effff3c6034ff80f300010e1ff000003c300000000000000000003c3000f300000cffcf3c603cff80f300000c1fc
def t59 : Nat := 0x2003eb52880010200040002003eb528ea00012affffaf403abf80fa00012ad7f000003c300000000000000000003c3000ff00003cffcfffe03fff80ff00003cffc
def t60 : Nat := 0x2003eb52880010200040002003eb528ff00011ebdffffe03fff80ff00011ebdf000003c300000000000000000003c3000ff00003cffcfffe03fff80ff00003cffc
def t61 : Nat := 0x2003eb52880010200040002003eb528ff00013effffffe03fff80ff00013efff000003c300000000000000000003c3000ff00003cffcfffe03fff80ff00003cffc
def t62 : Nat := 0x2003eb52890410200040106003eb528ff3801befffffffcbfff80ff39c9befff000003c300000000000000000003c3000ff38003cffcffffc3fff80ff39c03cffc
def t63 : Nat := 0x2100a0c2028118000840283080a0460154a0054297154a5c55280150a5c55297000000000000000000000000000000000000000000000000000000000000000000
def t64 : Nat := 0x2103ebd28a8118200840283083eb568ff4a017effffffe5ffff80ff0a5d7ffff000003c300000000000000000003c3000ff00003cffcfffe03fff80ff00003cffc
def t65 : Nat := 0x2103ebd28fa010200840faf403eb528ffd4033effffffe03fff80ff01013efff000003c3000f0000000000f0c003c3000ffc0003cffcfffe03fff80ff00003cffc
def t66 : Nat := 0x21fca3fffb0410003fffb06000a047f7ffeffff7ff156b5fff7ff152b5dfffbf0001fc03ffff0c00c03ffff0c00c0007ffffffffffff0f3ffffffff0f3ffffffff
def t67 : Nat := 0x21ffebfffb0410203fffb06003eb57ffffefffffffffff5ffffffff2b5dfffff0001ffc3ffff0c00c03ffff0c00fc307fffffffffffffffffffffffff3ffffffff
def t68 : Nat := 0xfe02c2fffb041fc03f80b0bffec107f802103ebd287ad5a200840faf4a1eb56800fe03c0ffcf0c1f003f80f03ff3c307c000003c3000f0c00000000f0c003c3000
def t69 : Nat := 0xfffec10000001fc0007f00fffec1000ffdffc14ad77ffefdfffbfffdffc14ad700ffffc30030001fc0007f00ffffc3003fffffc3cfffffffffffffffffffc3cfff
def t70 : Nat := 0xfffec3fffb041fc03fffb0fffec107ffffffffffff7fffffffffffffffdfffff00ffffc3ffff0c1fc03ffff0ffffc307ffffffffffffffffffffffffffffffffff
def t71 : Nat := 0xffffeb5288001fe0007f00ffffeb528ffdffd3effffffefffffbfffdffd3efff00ffffc30030001fc0007f00ffffc3003fffffc3cfffffffffffffffffffc3cfff
def t72 : Nat := 0x40848102120408481021204084810212040848102120408481021204084810212000008000020000080000200000800002000008000020000080000200000800002
def t73 : Nat := 0x408481021214484810212144848102122c3848b02120c39c8b02120c39c8b0e120000080000200000800002000008000020c3808300020c39c8300020c39c830e02
def t74 : Nat := 0x4094810a122c18c810a122c18c810252154a4854212050a5c54212050a5c55292000008000020000080000200000800002000008000020000080000200000800002
def t75 : Nat := 0x4284bfb73a84094a1025204284bfb73aff08493effffffe4bfff92ff08493efff00000bc30020000080000200000bc3002ff00083cffefffe0bfff82ff00083cffe
def t76 : Nat := 0x50a5c5528015000014297154a00550002c108030e722c3800b0e202c010030e720000000000000000000000000000000000c000030e700c380030e000c000030e70
def t77 : Nat := 0x50a5c5528015400014297154a00540002c3880b00400c39c8b04200c39c8b0e000000000000000000000000000000000000c3800300000c39c0300000c39c030e00
def t78 : Nat := 0x50bfc57fffb5400017fffb54a005407f7ffeffff7ff052b5fff7ff052b5dfffbf0001fc03ffff0c00c03ffff0c00c0007ffffffffffff0f3ffffffff0f3ffffffff
def t79 : Nat := 0x52a5fff7a8950102142d7156a03ff528ff10813effffffe03fffa0ff01013efff000003c300000000000000000003c3000ff00003cffcfffe03fff80ff00003cffc
def t80 : Nat := 0x52aa1fc0404f9ffc17528cfbeffff780cfbeffff78005d4a13e7ff052aa1fc0400f3e03fc0000f3ff03f0000f3ff3fff800f3ff3fff800fc0003cffc0f3e03fc000
def t81 : Nat := 0x52b5dfffbfffdffc14ad77ffeffff7ffb040000007f00fffec10000001fc03fff0f3fffffffffffffc3cfffffffffffffff0c00c0007f00ffffc30030001fc03fff
def t82 : Nat := 0x52b5dfffbfffdffc14ad77ffeffff7ffbc400030e7f2cfffef1e002c01fc33fff0f3fffffffffffffc3cfffffffffffffffcc00c30e7f0cfffff3e030c01fc33fff
def t83 : Nat := 0x52b5ffffbfffdffe14ad77ffeffff7ffff40013effffffffffff80ff01fd3ffff0f3fffffffffffffc3cffffffffffffffffc00c3cffffffffffff83ff01fc3ffff
def t84 : Nat := 0x52bfdfffffffdffc17ffffffeffff7fffffeffff7ff05ffffff7ff052bfdfffff0f3fffffffffffffc3ffffffffffffffffffffffffff0ffffffffff0f3ffffffff
def t85 : Nat := 0xc39cbfbf28ac010230e722c3803fb528ff40013effffffe03fff80ff00013efff0c39c3f3e000c000030e700c3803f3000ff00003cffcfffe03fff80ff00003cffc
def t86 : Nat := 0x106101aad28ea95a0418406ab4a3aa5689c79c8b0e0d2cc63671e722c3834b318d0f3ff3ffffcfffff03cffcfffff3ffffcfcf9c430e0d0cc637f3e710c38343318d
def t87 : Nat := 0x114214450851142144508511421445085283180a0c60283180a0c60283180a0c600000040000100000400001000004000010c39c030e700c39c030e700c39c030e70
def t88 : Nat := 0x15000055297154a0055280150000552972c2000b0e722c3900b0e402c2000b0e720000000000000000000000000000000000c000030e700c380030e000c000030e70
def t89 : Nat := 0x1500013e7bf954a02552801500013e7bf002001aa52880010200040002001aa528000000000000000000000000000000000000000000000000000000000000000000
def t90 : Nat := 0x152003ff7bf954b02552c0152003ff7bfff2001befffffff03fffc0ff2001befff000003c300000000000000000003c3000ff00003cffcfffe03fff80ff00003cffc
def t91 : Nat := 0x154a0054000154a5c54000154a5c552802c3900b08002c39c8b08002c39c8b0e400000000000000000000000000000000000c3800300000c39c0300000c39c030e00
def t92 : Nat := 0x154a5c55297154a5c55297154a5c55297242948b0e722c39c890a522c39c8b0e7200000c0000300000c0000300000c000030c39c830e720c39c830e720c39c830e72
def t93 : Nat := 0x154a5c55297154a5c55297154a5c55297283180a0c60283180a0c60283180a0c60000000000000000000000000000000000000000000000000000000000000000000
def t94 : Nat := 0x154a5c55297154a5c55297154a5c55297283180a0c722839c8a0c602831c8a0e7200000c0000300000c0000300000c000030c39c830e720c39c830e720c39c830e72
def t95 : Nat := 0x154a5c55297154a5c55297154a5c552972c39c8b0e722c39c8b0e722c39c8b0e7200000c0000300000c0000300000c000030c39c830e720c39c830e720c39c830e72
def t96 : Nat := 0x154a5c55297954a5c55297154a5e55297ff39c9bce726fbfcbfce726f39c9beff200000c0000300000c0000300000c00003ff39c83ce720f3fcbfce720f39c83cff2
def t97 : Nat := 0x154a5d7f7bf954a5e55297154a5d7f7bf2c39c9baf7aac39cab0e722c39c9baf7a00000c0000300000c0000300000c000030c39c830e720c39c830e720c39c830e72
def t98 : Nat := 0x154b5c55a973d5adc55a973d5adc552d73d7bc8f4e722d3bdcf4e722d3bdcf5ef200000c0000300000c0000300000c000030c39c830e720c39c830e720c39c830e72
def t99 : Nat := 0x154b5c55a97ff4a5c55a97ffde5e55297fefdcab0e722c39cbf8e722c39c8b0e7200000c00003f0000c00003f0c00c00003fcf9c830e720c39cbf0e720c39c830e72
def t100 : Nat := 0x154bfc57fffb54a5c57fffb54a5c552ff7ffffffffff2d3bdffffff2d3bddfffff0001fc03ffff0c00c03ffff0c00c0007ffffffffffff0f3ffffffff0f3ffffffff
def t101 : Nat := 0x156a5cf56b7154b5c552d7156a5cf56b73d39c8b4ef73d7bc8f5ef23d39c8b4ef700000c0000300000c0000300000c000030c39c830e720c39c830e720c39c830e72
def t102 : Nat := 0x156a5dff7bf954b5e552d7156a5dff7bf3d39c9befffbd7bcaf5ef23d39c9befff00000c0000300000c0000300000c000030c39c830e720c39c830e720c39c830e72
def t103 : Nat := 0x156a5fff7bf954b5e552d7156a5fff7bfff39c9befffffffcbffff2ff39c9befff00000fc300300000c0000300000fc3003ff39c83cffeffffcbffff2ff39c83cffe
def t104 : Nat := 0x156b5dfffbfffdffc55ad77ffeffff7ffbc79c8b0e7f2cfffef1e722c39fcb3fff0f3fffffffffffffc3cfffffffffffffffcf9cc30e7f0cfffff3e730c39fc33fff
def t105 : Nat := 0x1d7bdcf5e973d4a5c75ef73d7a5cf52973c79c8b0e722c39c8f1e722c39c8b0e720c39cc30e030c000c30e730c380c300030c39c830e720c39c830e720c39c830e72
def t106 : Nat := 0x2912954f1cdd3e634a44a553c7374f98da50a5c552e815b5a294297154ba056d68030637cf18df3c6340c18df3c637cf18df0c0000007c00fff3c30000001f003ffc
def t107 : Nat := 0x2c2003fbf7aac3902b0e402c2003fbf7aff00017fffffffe03fff80ff00017ffff0c0003f3e700c380030e000c0003f3e70ff00003cffcfffe03fff80ff00003cffc
def t108 : Nat := 0x2c39c8b0e722c39c8b0e722c39c8b0e72154a5c55297154a5c55297154a5c552970c39c830e720c39c830e720c39c830e7200000c0000300000c0000300000c00003
def t109 : Nat := 0x2c39c8b0e722c39c8b0e722c39c8b0e72154a5c552971d5adc552971d5adc552970c39c830e720c39c830e720c39c830e7200000c0000300000c0000300000c00003
def t110 : Nat := 0x2c39c8b0e722c39c8b0e722c39cab0e72954a5c552975fde5c552975f4a5c552970c39c830e720c39c830e720c39c830e7200000c0000300000c0000300000c00003
def t111 : Nat := 0x2c39c8b0e723c39c8b0e723c79c8b0e723d5a5c55297156a5cf5297154b5c55a970c39c830e720c39c830e720c39c830e7200000c0000300000c0000300000c00003
def t112 : Nat := 0x2c39c8b0e726e39c8b0e726ebdcab0e72954a5c55297154a5c55297154a5c552970c39c830e720c39c830e720c39c830e7200000c0000300000c0000300000c00003
def t113 : Nat := 0x2c39c8b0e72ac39c8b0e722c39cab0e72ff4a5d7d2975ffe5ffd2975f4a5d7ff970c39c830e720c39c830e720c39c830e72ff000c3c0030f3e0ffc0030f000c3cf83
def t114 : Nat := 0x2c39c9baf7aac39cab0e722c39c9baf7a154a5d7f7bf954a5e55297154a5d7f7bf0c39c830e720c39c830e720c39c830e7200000c0000300000c0000300000c00003
def t115 : Nat := 0x2c39cbfbf7aac39cab0e722c39cbfbf7aff4a5d7fffffffe5ffff97ff4a5d7ffff0c39cbf3e720c39c830e720c39cbf3e72ff000c3cffffffe0ffff83ff000c3cfff
def t116 : Nat := 0x2c39fcb3fffbc79c8b3fffbc79c8b0e7f7ffeffff7ff156b5fff7ff156b5dfffbf0c39fc33ffffcf9cc33ffffcf9cc30e7ffffffffffff0f3ffffffff0f3ffffffff
def t117 : Nat := 0x2d39c8b4ef23d39c8b4ef23d39c8b4e72154a5c55297154a5c55297154a5c552970c39c830e720c39c830e720c39c830e7200000c0000300000c0000300000c00003
def t118 : Nat := 0x2d3bdcf5ef23d39c8b4ef73d7bc8f4e723d5adc552d7156a5cf56b7154b5c55a970c39c830e720c39c830e720c39c830e7200000c0000300000c0000300000c00003
def t119 : Nat := 0x3040000007f002b5ec100000015c03fbf00015c03fbfb0400000ad73040000007ff0c00c0007f003fffc30030001fc03fff0001fc03ffff0c00c00ffff0c00c0007f
def t120 : Nat := 0x3041000087ffa2b5ec1800fad55e03fbffad55e03fbfb06003e8ad73041000087ff0c00c0007ff03fffc3003f0c1fc03ffff0c1fc03ffff0c00fc0ffff0c00c0007f
def t121 : Nat := 0x397394e5ce5397394e5ce5397394e5ce5397394e5ce5397394e5ce5397394e5ce50c39c430e710c39c430e710c39c430e710c39c430e710c39c430e710c39c430e71
def t122 : Nat := 0x3d39c9befffbd7bcaf5ef23d39c9befff156a5dff7bf954b5e552d7156a5dff7bf0c39c830e720c39c830e720c39c830e7200000c0000300000c0000300000c00003
def t123 : Nat := 0x3d3bdcf5ef73d7bc8f5ef73d7bc8f4ef73d7adcf56f7156b5cf56f7156b5cf5eb70c39c830e720c39c830e720c39c830e7200000c0000300000c0000300000c00003
def t124 : Nat := 0x3d7bc8f4e722d3bdcf4e722d3bdcf5ef2154b5c55a973d5adc55a973d5adc552d70c39c830e720c39c830e720c39c830e7200000c0000300000c0000300000c00003
def t125 : Nat := 0x3d7bdcf5ef73d7bdcf5ef73d7bdcf5ef73d7bdcf5ef73d7bdcf5ef73d7bdcf5ef70c39cc30e730c39cc30e730c39cc30e730c39cc30e730c39cc30e730c39cc30e73
def t126 : Nat := 0x3d7bdffffffbd7bdef5ef73d7bdffffffff7bddfffffffffdfffff7ff7bddfffff0c39cff3e730c39cc30e730c39cff3e73ff39cc3cfffffffcfffff3ff39cc3cfff
def t127 : Nat := 0x4a94a2000000000012a528800000000004a94a2000000000012a52880000000000000000000000000000000000000000000000000000000000000000000000000000
def t128 : Nat := 0x4a94a20003f00dffd2a5288000fc037ff4a94a20003f00dffd2a5288000fc037ff00000c0007f00fffc000030001fc03fff00000c0007f00fffc000030001fc03fff
def t129 : Nat := 0x4ab4a3eb5288001032a568802003eb528ff94a33effffffe03fffa8ff00013efff000003c300000000000000000003c3000ff00003cffcfffe03fff80ff00003cffc
def t130 : Nat := 0x4f2003fffa8ff01033efc0ff2003ff528ff00033effffffe03fff80ff00013efff0f0003fff80ff00003cf80ff0003ff000ff00003cffcfffe03fff80ff00003cffc
def t131 : Nat := 0x4f40013ef80ff01fd3ef80ff01fd3d000050b5e14a977fdefe14a977fdefc142d70fc00c3cf83ff01fc3cf83ff01fc3f0030f3ffc3cffffffffc3cffffffffc3cfff
def t132 : Nat := 0x4fbe03ff528cf01033c0404fbe03ff528ff00013effffffe03fff80ff00013efff0f3e03ff0000f00003c0000f3e03ff000ff00003cffcfffe03fff80ff00003cffc
def t133 : Nat := 0x4fbffffff80ff00013effffffe03fc000fad4a200040002003eb528800100008000f3ff3fff80ff00003cffcfffe03fc000f0c00000000000003c300000000000000
def t134 : Nat := 0x4fbffffffa8ff01033effffffe03ff528ffd4a33effffffe03fffa8ff01013efff0f3ff3fff80ff00003cffcfffe03ff000ffc0003cffcfffe03fff80ff00003cffc
def t135 : Nat := 0x4fbffffffffff40013fffffffe03fc07ffffeffff7ff052b5fff7ff852b5dfffbf0f3ffffffffffc00c3fffffffe0ffc07ffffffffffff0f3ffffffff0f3ffffffff
def t136 : Nat := 0x53c6374f18d0102174f18d0102154f18d0001a002d68a0000002d68a0000000068f3c637cf18d030637cf18d030637cf18d0001f003ffcf0c00003ffcf0c0000007c
def t137 : Nat := 0x53c6374f18d9142174f18d9142154f18d6ab5a3aad68a02103aad68a02101aad68f3c637cf18df3c637cf18df3c637cf18dfffff3ffffcfffff3ffffcfffff3ffffc
def t138 : Nat := 0x5ffffffff97ff4a5d7fffffffe5ffd297fefdeab0e722c39cbfbf7aac39c8b0e720f3ffffff83ff000c3cffffffe0ffc003fcf9c830e720c39cbf3e720c39c830e72
def t139 : Nat := 0x5ffffffffbfff4b5f7fffffffe5fff7bffffdebbefffffffcbffffaff39c9befff0f3ffffff83ff000c3cffffffe0fff003fff9c83cffeffffcbffff2ff39c83cffe
def t140 : Nat := 0x6ab4a3aa568002103aa568002101aad280000340318d9040000318d9040000000dfffff3ffffc0f3ff3ffffc0f3ff3ffffc0000340318df0c0040318df0c0040000d
def t141 : Nat := 0x6ab5ffabfffb06103abfffb06101aad7f7ffeffff7ff956b5fff7ff956b5dfffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def t142 : Nat := 0x6ebdeab0e722c39c9baf7aac39c8b0e725fdefe55297154a5d7f7bf954a5c552970c39c830e720c39c830e720c39c830e7200000c0000300000c0000300000c00003
def t143 : Nat := 0x6f39c9bce726f39c9bce726f39c9bce72154a5c55297154a5c55297154a5c552970f39c83ce720f39c83ce720f39c83ce7200000c0000300000c0000300000c00003
def t144 : Nat := 0x6fbffffff80ff39c9befffffffcbfce00fad4a200040106003eb528904100008000f3ff3fff80ff39c03cffcffffc3fce00f0c00000000000003c300000000000000
def t145 : Nat := 0x6fbfffffff2ff39c9befffffffcbfce72ffdefe552d7156a5fff7bf954b5c55a970f3ffbffff2ff39c83cffeffffcbfce72f0c00c0000300000fc300300000c00003
def t146 : Nat := 0x7fdefc142d7052a5dff7bf050b5c14a970001fc010000000000007f00400000000fffffc3cfff0f3ffffffff0f3ffc3cfff0001fc0300300000c0007f00c00c00003
def t147 : Nat := 0x7ffeffff7ff052b5fff7ff052b5dfffbf0001fc03fffb0400003fffb040000007ffffffffffff0f3ffffffff0f3ffffffff0001fc03ffff0c00c03ffff0c00c0007f
def t148 : Nat := 0x7fff03fc800b56b5ffc800b56b5dfffc07fff03fc800b56b5ffc800b56b5dfffc0fffe03fc000fffff3fc000fffff3fff80fffe03fc000fffff3fc000fffff3fff80
def t149 : Nat := 0x7ffffffffffb56b5ffffffb56b5dfffff7ffffffffffb56b5ffffffb56b5dfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def t150 : Nat := 0x800100008006a94a0008006a94a200040954a00540004f9efc540004f9efe55280000000000000000000000000000000000000000000000000000000000000000000
def t151 : Nat := 0x80010000800fad4a000800fad4a200040fffe03fc0004fbffffc0004fbffffff8000000000000f0c00000000f0c00000000fffe03fc0000f3ff3fc0000f3ff3fff80
def t152 : Nat := 0x80010003d28fad4a000840fad4a200068fffe03fe7ff4fbfffff7804fbffffffbf00000003000f0c00000000f0c00000000fffe03fcffc0f3ff3fff800f3ff3ffffc
def t153 : Nat := 0x80010041800fad4a000800fad4a241040fffe03fce726fbffffce006fbfffffff200000000000f0c00000000f0c00000000fffe03fce700f3ff3fce000f3ff3ffff0
def t154 : Nat := 0x8001012ad28fad4a200800fad4a32a568fffe03fe528cfbffffc0004fbffffffa800000000000f0c00000000f0c00000000fffe03fc0000f3ff3fc0000f3ff3fff80
def t155 : Nat := 0x80010200800fad4a200800fad4a200040fffe03fef80ffbffffef80ffbffffff8000000000000f0c00000000f0c00000000fffe03fcf80ff3ff3fcf80ff3ff3fff80
def t156 : Nat := 0x8001fc03ffffad4a003ffffad4a20007ffffeffff7ff4fbfffff7ff4fbffffffbf0001fc03ffff0c00c03ffff0c00c0007ffffffffffff0f3ffffffff0f3ffffffff
def t157 : Nat := 0x802003ebd28fad50200840fa2003eb568ff2003fefffffff03fff80ff2003fffff000003c3000f0c00000000f00003c3000ff0003fcffcfffe03fff80ff0003ffffc
def t158 : Nat := 0x802100a0c20fad5a000840faf4a2a0460fffe03fc2975ffffffd2805fbffffff9700000000000f0c00000000f0c00000000fffe03fc0000f3ff3fc0000f3ff3fff80
def t159 : Nat := 0x802103ebd28fad5a200840faf4a3eb568fffe03feffffffffffff80ffbffffffff000003c3000f0c00000000f0c003c3000fffe03fcffcfffff3fff80ff3ff3ffffc
def t160 : Nat := 0x850b5c55a80ffd4a014a97ffdea254040fffe83fc0404fbffffc4204fbffffff8000000000000f0c00000000f0c00000000fffe03fc0000f3ff3fc0000f3ff3fff80
def t161 : Nat := 0x9501013efbfffdea255a80ffd4a33e7fffffe03fe528cfbffffc0404fbffffffa800000000000f0c00000000f0c00000000fffe03fc0000f3ff3fc0000f3ff3fff80
def t162 : Nat := 0x954a00540004f9efc540004f9efe55280800100008006a94a0008006a94a200040000000000000000000000000000000000000000000000000000000000000000000
def t163 : Nat := 0x954a5c552975fdefc552975fdefe55297ac39c8b0e726ebde8b0e726ebdeab0e7200000c0000300000c0000300000c000030c39c830e720c39c830e720c39c830e72
def t164 : Nat := 0x954b00548006f9efc548006f9efe552c0954b00548006f9efc548006f9efe552c0000000000000000000000000000000000000000000000000000000000000000000
def t165 : Nat := 0x954b0054800ffdefc54800ffdefe552c0ffff03fc8006fbffffc8006fbffffffc000000000000f0c00000000f0c00000000fffe03fc0000f3ff3fc0000f3ff3fff80
def t166 : Nat := 0x954b5c55a97ffdefc55a97ffdefe552d7ffffcbfce726fbffffce726fbfffffff200000c00003f0c00c00003f0c00c00003ffffcbfce720f3ffbfce720f3ffbffff2
def t167 : Nat := 0x956b5ffffbfffdffe55ad7fffeffff7ffffffcbfefffffffffffff2ffbffffffff00000fc3003f0c00c00003f0c00fc3003ffffcbfcffefffffbffff2ff3ffbffffe
def t168 : Nat := 0xa8118000840faf4a0a0c20fad5a200840fffe5ffd2805fbffffc2975ffffffff8000000000000f0c00000000f0c00000000fffe03fc0000f3ff3fc0000f3ff3fff80
def t169 : Nat := 0xac39c8b0e726ebde8b0e726ebdeab0e72954a5c552975fdefc552975fdefe552970c39c830e720c39c830e720c39c830e7200000c0000300000c0000300000c00003
def t170 : Nat := 0xac39c8b0e72fefde8b0e72fefdeab0e72fffe5ffd2975ffffffd2975ffffffff970c39c830e72fcf9c830e72fcf9c830e72fffe0ffc0030f3ffffc0030f3ffffff83
def t171 : Nat := 0xac39cbfbf7afefdeab0e72fefdebfbf7afffe5fffffffffffffff97fffffffffff0c39cbf3e72fcf9c830e72fcf9cbf3e72fffe0ffcffffffffffff83ff3ffffffff
def t172 : Nat := 0xb040000007f00fffec10000001fc03fff052b5dfffbfffdffc14ad77ffeffff7fff0c00c0007f00ffffc30030001fc03fff0f3fffffffffffffc3cffffffffffffff
def t173 : Nat := 0xb06003eb57f80fffec10400021ffebfffff2b5dffffffffffffffd7fffeffffffff0c00fc307f00ffffc30030001ffc3fffff3ffffffffffffffffffffffffffffff
def t174 : Nat := 0xbd7bc8f4e726fbffcf4e726fbffef5ef2954b5c55a977fdefc55a977fdefe552d70c39c830e720c39c830e720c39c830e7200000c0000300000c0000300000c00003
def t175 : Nat := 0xc284230a108c284230a108c284230a108c284230a108c284230a108c284230a108f3c633cf18cf3c633cf18cf3c633cf18cf3c633cf18cf3c633cf18cf3c633cf18c
def t176 : Nat := 0xc284370b18dd2c4230b18dd2c4230a10deab4a3aa568c2a523aa568c2a523aad28f3c637cf18df3c637cf18df3c637cf18dfffff3ffffcfffff3ffffcfffff3ffffc
def t177 : Nat := 0xc68c6b1a31ac68c6b1a31ac68c6b1a31ac68c6b1a31ac68c6b1a31ac68c6b1a31af3c63bcf18ef3c63bcf18ef3c63bcf18ef3c63bcf18ef3c63bcf18ef3c63bcf18e
def t178 : Nat := 0xca95a200800fad4a12ad28fad4a200040fffea3fc0004fbffffe528cfbffffff8000000000000f0c00000000f0c00000000fffe03fc0000f3ff3fc0000f3ff3fff80
def t179 : Nat := 0xcfbffffff80ffd4a13effffffea3fc040fffea3fc0404fbfffff528cfbffffff800f3ff3fff80ffc0003cffcfffe03fc000fffe03fc0000f3ff3ff0000f3ff3fff80
def t180 : Nat := 0xcfbffffffa8ffd5a33effffffea3ff568fffea3feffffffffffffa8ffbffffffff0f3ff3fff80ffc0003cffcfffe03ff000fffe03fcffcfffff3fff80ff3ff3ffffc
def t181 : Nat := 0xd339c98e18dd3c7cb4f1f2d339c98e18d156a5fbe7bf954b5e552d7156a5fbe7bff339c80c18ef3c7cbcf1f2f339c80c18e00000fc300300000c0000300000fc3003
def t182 : Nat := 0xd3c6374f18dd3c6374f18dd3c6374f18deab5a3aad68eab5a3aad68eab5a3aad68f3c637cf18df3c637cf18df3c637cf18dfffff3ffffcfffff3ffffcfffff3ffffc
def t183 : Nat := 0xd3c6374f18ddbd6b74f18ddbd6b74f18deab5a3aad68eab5a3aad68eab5a3aad68f3c637cf18df3c637cf18df3c637cf18dfffff3ffffcfffff3ffffcfffff3ffffc
def t184 : Nat := 0xd3c7374f98dfbd6b74f98dfbd6b74f1cdffffa3fed68efbffffed68efbffffffe8f3c637cf18df3c637cf18df3c637cf18dfffff3ffffcfffff3ffffcfffff3ffffc
def t185 : Nat := 0xd3c7ff4fffff3c6374fffff3c6374f1fffffffffffffefbffffffffefbfffffffff3c7ffcfffff3c63fcfffff3c63fcf1fffffffffffffffffffffffffffffffffff
def t186 : Nat := 0xd3e637ef5add3c7374f1cdd3e637ef5adffb5a3befffffffa3fffe8ffb5a3beffff3c637cf18df3c637cf18df3c637cf18dfffff3ffffcfffff3ffffcfffff3ffffc
def t187 : Nat := 0xd6ed6ab0e322c19cb5bb5aac38c8b06725af5a3aad17ea4a5d6bd68eab45fa9297fcf9c830e720c39cbf3e720c39c830e720f3ffffff83ff000c3cffffffe0ffc003
def t188 : Nat := 0xd7c6375f39fd7ce375f38dd7c6375f39feab5a3aad68eab5a3aad68eab5a3aad68f3c637cf18df3c637cf18df3c637cf18dfffff3ffffcfffff3ffffcfffff3ffffc
def t189 : Nat := 0xd7ce7f5f39fd7ce7f5f39fd7ce7f5f39feebdebbaf7aeebdebbaf7aeebdebbaf7af3c63fcf18ff3c63fcf18ff3c63fcf18ffffffbffffefffffbffffefffffbffffe
def t190 : Nat := 0xd7ef7ffffbfffdfff5fbdffffeffff7fffaf5a3aad7feaffffebd68eab5ffabfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def t191 : Nat := 0xdffffffff8dffc6377fffffffe37ff18dfaf5a3aad68eab5a3ebd68eab5a3aad68fffff7fff8dffc637ffffdfffe37ff18dfffff3ffffcfffff3ffffcfffff3ffffc
def t192 : Nat := 0xea95a200840faf4a1aad28fad5a200840fffefffd2805fbffffe7bfdffffffff8000000000000f0c00000000f0c00000000fffe03fc0000f3ff3fc0000f3ff3fff80
def t193 : Nat := 0xeab5a3aad68eab5a3aad68eab5a3aad68d3c6374f18dd3c6374f18dd3c6374f18dfffff3ffffcfffff3ffffcfffff3ffffcf3c637cf18df3c637cf18df3c637cf18d
def t194 : Nat := 0xeab5a3ebd68eab5a3aad68eab5a3ebd68ffc6377fffffffe37fff8dffc6377fffffffff3ffffcfffff3ffffcfffff3ffffcffc637ffffdfffe37fff8dffc637ffffd
def t195 : Nat := 0xfad4a200040002003eb528800100008004fbffffff80ff00013effffffe03fc000f0c00000000000003c3000000000000000f3ff3fff80ff00003cffcfffe03fc000
def t196 : Nat := 0xfad4a200040106003eb528904100008006fbffffff80ff39c9befffffffcbfce00f0c00000000000003c3000000000000000f3ff3fff80ff39c03cffcffffc3fce00
def t197 : Nat := 0xfad4a2000404ab4a3eb528ca95a200800cfbffffff80ff94a13effffffea3fc000f0c00000000000003c3000000000000000f3ff3fff80ff00003cffcfffe03fc000
def t198 : Nat := 0xfad4a241040002003eb528800100418006fbfffffff2ff3801beffffffe03fce72f0c00000000000003c3000000000000000f3ff3ffff0ff38003cffcfffe03fce70
def t199 : Nat := 0xfad4a32a568802003eb5288001012ad284fbffffffa8ff00033effffffe03fe528f0c00000000000003c3000000000000000f3ff3fff80ff00003cffcfffe03fc000
def t200 : Nat := 0xfad5a200840283083ebd28a81180008405ffffffff80ff0a5d7effffffe5ffd280f0c00000000000003c3000000000000000f3ff3fff80ff00003cffcfffe03fc000
def t201 : Nat := 0xfad5a200840faf4a3ebd28fad5a200840fffffffff80ffbffffeffffffffffff80f0c00000000f0c003c3000f0c00000000fffff3fff80ff3ff3fcffcfffff3fff80
def t202 : Nat := 0xfaf4a2a0460002103eb568802100a0c205fbffffff97ff4a017fffffffe03fc297f0c00000000000003c3000000000000000f3ff3fff80ff00003cffcfffe03fc000
def t203 : Nat := 0xfaf4a3aa568802103eb568802101aad285fbffffffbfff4a037fffffffe03fe7bff0c00000000000003c3000000000000000f3ff3fff80ff00003cffcfffe03fc000
def t204 : Nat := 0xfaf4a3eb568802103eb568802103ebd28ffbfffffffffffe03ffffffffe03feffff0c003c3000000003c3000000003c3000ff3ff3ffffcfffe03ffffcfffe03fcffc
def t205 : Nat := 0xfaf5a3ebd68faf5a3ebd68faf5a3ebd68ffffffffffffffffffffffffffffffffff0c003c3000f0c003c3000f0c003c3000fffff3ffffcfffff3ffffcfffff3ffffc
def t206 : Nat := 0xfbd6b6450c5116217ef5ad914314458856fbffffffe0ff3181befffffff83fcc60f0c00400001000007c3001000004000010f3ff3ffff0ff39c03cffcffffc3fce70
def t207 : Nat := 0xfbf7b7efdedfbf7b7efdedfbf7b7efdedfbf7b7efdedfbf7b7efdedfbf7b7efdedfffff7ffffdfffff7ffffdfffff7ffffdfffff7ffffdfffff7ffffdfffff7ffffd
def t208 : Nat := 0xfefdeab0e722c39cbfbf7aac39c8b0e725ffffffff97ff4a5d7fffffffe5ffd297fcf9c830e720c39cbf3e720c39c830e720f3ffffff83ff000c3cffffffe0ffc003
def t209 : Nat := 0xff00013effffffe03fff80ff00013efff002003eb52880010200040002003eb528ff00003cffcfffe03fff80ff00003cffc000003c300000000000000000003c3000
def t210 : Nat := 0xff00013effffffea3fff80ff94a33efff802003eb528ca95a2000404ab4a3eb528ff00003cffcfffe03fff80ff00003cffc000003c300000000000000000003c3000
def t211 : Nat := 0xff01013effffffe83fff80ff10813efff156a03ff528850b5e54040052a5fff7a8ff00003cffcfffe03fff80ff00003cffc000003c300000000000000000003c3000
def t212 : Nat := 0xff01fd3fffffffe03fffffff40013efff7ffeffff7ff852b5fff7ff052b5ffffbfff01fc3fffffffe0ffffffffc00c3cffffffffffffff0f3ffffffff0f3ffffffff
def t213 : Nat := 0xff0a5d7fffffffe03fff97ff4a017efff283083eb568802102a0460002103ebd28ff00003cffcfffe03fff80ff00003cffc000003c300000000000000000003c3000
def t214 : Nat := 0xff10813effffffe03fffa0ff01013efff052a5fff7a8950102142d7156a03ff528ff00003cffcfffe03fff80ff00003cffc000003c300000000000000000003c3000
def t215 : Nat := 0xff2001befffffff03fffc0ff2001befff152003ff7bf954b02552c0152003ff7bfff00003cffcfffe03fff80ff00003cffc000003c300000000000000000003c3000
def t216 : Nat := 0xff2003fffffffff03fffc0ff2003fffffff2003fffffffff03fffc0ff2003fffffff0003ffffcfffe03fff80ff0003ffffcff0003ffffcfffe03fff80ff0003ffffc
def t217 : Nat := 0xff2103fffffffffa3fffc0fff4a3ffffffffe03ffffffffffffffc0ffbffffffffff0003ffffcfffe03fff80ffc003ffffcfffe03ffffcfffff3fff80ff3ff3ffffc
def t218 : Nat := 0xff3801befffffffcbfff80ff39c9befff002003eb52890410200040106003eb528ff38003cffcffffc3fff80ff39c03cffc000003c300000000000000000003c3000
def t219 : Nat := 0xff39c9bce726fbfcbfce726f39c9beff2154a5c55297954a5c55297154a5e55297ff39c83ce720f3fcbfce720f39c83cff200000c0000300000c0000300000c00003
def t220 : Nat := 0xff39c9beffffffe03ffff2ff3801befff106003eb52880010241040002003eb528ff39c03cffcfffe03ffff0ff38003cffc000003c300000000000000000003c3000
def t221 : Nat := 0xff39c9befffffffcbffff2ff39c9befff156a5fff7bf954b5e552d7156a5fff7bfff39c83cffeffffcbffff2ff39c83cffe00000fc300300000c0000300000fc3003
def t222 : Nat := 0xff39cbfffffffffcbffff2ff39cbfffffff6a5ffffffffff5ffffd7ff6a5ffffffff39cbffffeffffcbffff2ff39cbffffeff000fffffffffe0ffff83ff000ffffff
def t223 : Nat := 0xff4a017effffffe5ffff80ff0a5d7ffff002103ebd28a8118200840283083eb568ff00003cffcfffe03fff80ff00003cffc000003c300000000000000000003c3000
def t224 : Nat := 0xff4a5d7d2975ffe5ffd2975f4a5d7ff972c39c8b0e72ac39c8b0e722c39cab0e72ff000c3c0030f3e0ffc0030f000c3cf830c39c830e720c39c830e720c39c830e72
def t225 : Nat := 0xff94a33effffffe03fffa8ff00013efff4ab4a3eb5288001032a568802003eb528ff00003cffcfffe03fff80ff00003cffc000003c300000000000000000003c3000
def t226 : Nat := 0xffbfffffffffffe03ffffffffe03feffffaf4a3eb568802103eb568802103ebd28ff3ff3ffffcfffe03ffffcfffe03fcffcf0c003c3000000003c3000000003c3000
def t227 : Nat := 0xffd4a2142d7156a03ff7a895010014a974fbffffffa0ff01013effffffe03fc420f0c00000000000003c3000000000000000f3ff3fff80ff00003cffcfffe03fc000
def t228 : Nat := 0xffd4a33e7ff956a03ff7a89501013efbf4fbffffffa8ff01033effffffe03fe528f0c00000000000003c3000000000000000f3ff3fff80ff00003cffcfffe03fc000
def t229 : Nat := 0xffdea254040052a5fff528850b5c55a804fbffffff80ff10813effffffe83fc040f0c00000000000003c3000000000000000f3ff3fff80ff00003cffcfffe03fc000
def t230 : Nat := 0xffdefe552c0152003ff7bf954b00548006fbffffffc0ff2001befffffff03fc800f0c00000000000003c3000000000000000f3ff3fff80ff00003cffcfffe03fc000
def t231 : Nat := 0xfffe03fc0004fbffffc0004fbffffff8080010000800fad4a000800fad4a200040fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t232 : Nat := 0xfffe03fc0004fbffffc0004fbffffff8080010020c20fad4a000800fad4a220460fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t233 : Nat := 0xfffe03fc0004fbffffc0004fbffffff808001012ad00fad4a000800fad4a328040fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t234 : Nat := 0xfffe03fc0004fbffffc0004fbffffff8084010010a12fedca010a00fed4a210252fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t235 : Nat := 0xfffe03fc0004fbffffc0004fbffffff8084090010800fedce810800fedcea10240fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t236 : Nat := 0xfffe03fc0004fbffffc0004fbffffff8085010014a80ffd4a014a80ffd4a214040fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t237 : Nat := 0xfffe03fc0004fbffffc0004fbffffff80850b0054800ffd4a014800ffdea254040fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t238 : Nat := 0xfffe03fc0004fbffffc000cfbffffff80ca950200800fad4a128800fad4a200040fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t239 : Nat := 0xfffe03fc0004fbffffd0004fbffffff80802100a0c00fad4a000840faf4a2a0040fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t240 : Nat := 0xfffe03fc0004fbffffe500cfbffffff8080010200800fad4a000800fad4a200040fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t241 : Nat := 0xfffe03fc0005fbffffc0005ffffffff80a8110000800faf4a0a0800fad5a200840fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t242 : Nat := 0xfffe03fc0404fbffffc4004fbffffff8080010041800fad4a000800fad4a240040fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t243 : Nat := 0xfffe03fc2124fbffffc2004fbffffff9280010000800fad4a000800fad4a200040fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t244 : Nat := 0xfffe03fc2805fbffffc2805fbffffff8080010000800fad4a000800fad4a200040fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t245 : Nat := 0xfffe03fc2975ffffffd2805fbffffff97802100a0c20fad5a000840faf4a2a0460fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t246 : Nat := 0xfffe03fc4204fbffffc0004fbffffffa080010000800fad4a000800fad4a200040fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t247 : Nat := 0xfffe03fc4204fbffffc0404fbffffffa095010014a97ffdea055a80ffd4a2142d7fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t248 : Nat := 0xfffe03fc8006fbffffc8006fbffffffc080010040800fad4a000800fad4a241040fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t249 : Nat := 0xfffe03fce006fbffffce006fbffffff8080010000800fad4a000800fad4a200040fffe03fce000f3ff3fce000f3ff3fff8000000000000f0c00000000f0c00000000
def t250 : Nat := 0xfffe03fce726fbffffce006fbfffffff280010041800fad4a000800fad4a241040fffe03fce700f3ff3fce000f3ff3ffff000000000000f0c00000000f0c00000000
def t251 : Nat := 0xfffe03fce726fbffffce406fbfffffff295010055a97ffdea055a80ffd4a2552d7fffe03fce700f3ff3fce000f3ff3ffff000000000000f0c00000000f0c00000000
def t252 : Nat := 0xfffe03fcef77ffffffde807fbfffffff7802100e1c20fad5a000840faf4a2e1460fffe03fce700f3ff3fce000f3ff3ffff000000000000f0c00000000f0c00000000
def t253 : Nat := 0xfffe03fe528cfbffffc0004fbffffffa88001012ad28fad4a200800fad4a32a568fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t254 : Nat := 0xfffe03fe528cfbffffc0404fbffffffa89501013efbfffdea255a80ffd4a33e7fffffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t255 : Nat := 0xfffe03fe7bfdffffffd2805fbffffffbf802101aad28fad5a200840faf4a3aa568fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t256 : Nat := 0xfffe03fe7ff4fbfffff7804fbffffffbf80010003d28fad4a000840fad4a200068fffe03fcffc0f3ff3fff800f3ff3ffffc00000003000f0c00000000f0c00000000
def t257 : Nat := 0xfffe03fef7aefbffffce006fbfffffffa8001016bd28fad4a200800fad4a36b568fffe03fce700f3ff3fce000f3ff3ffff000000000000f0c00000000f0c00000000
def t258 : Nat := 0xfffe03feffffffffffff80ffbffffffff802103ebd28fad5a200840faf4a3eb568fffe03fcffcfffff3fff80ff3ff3ffffc000003c3000f0c00000000f0c003c3000
def t259 : Nat := 0xfffe03ff528cfbffffc0404fbffffffa8ff01013effffffea3fff80ffd4a33effffffe03ff0000f3ff3fc0000f3ff3fff80ff00003cffcfffe03fff80ffc0003cffc
def t260 : Nat := 0xfffe5ffd2805fbffffc2975ffffffff80a8118000840faf4a0a0c20fad5a200840fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t261 : Nat := 0xfffe5ffd2975ffffffd2975ffffffff97a83180a0c60faf5a0a0c60faf5a2a0c60fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t262 : Nat := 0xfffe5ffd2975ffffffd2975ffffffff97ac39c8b0e72fefde8b0e72fefdeab0e72fffe0ffc0030f3ffffc0030f3ffffff830c39c830e72fcf9c830e72fcf9c830e72
def t263 : Nat := 0xfffe83fc0404fbffffc4204fbffffff80850b5c55a80ffd4a014a97ffdea254040fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t264 : Nat := 0xfffe83fc4604fbffffc4604fbffffffa0950b5c55a97ffdea055a97ffdea2542d7fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t265 : Nat := 0xfffe83fce726fbffffce206fbfffffff2850b5c55a80ffd4a014a97ffdea255040fffe03fce700f3ff3fce000f3ff3ffff000000000000f0c00000000f0c00000000
def t266 : Nat := 0xfffea3fc0004fbffffe528cfbffffff80ca95a200800fad4a12ad28fad4a200040fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t267 : Nat := 0xfffea3fc0404fbfffff528cfbffffff80cfbffffff80ffd4a13effffffea3fc040fffe03fc0000f3ff3ff0000f3ff3fff800f3ff3fff80ffc0003cffcfffe03fc000
def t268 : Nat := 0xfffea3fe5684fbffffe5684fbffffffa88001340398dfad4a00398dfad4a20004dfffff3ffffc0f3ff3ffffc0f3ff3ffffc0000340318df0c0040318df0c0040000d
def t269 : Nat := 0xffff03fc8006fbffffc8006fbffffffc0954b0054800ffdefc54800ffdefe552c0fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t270 : Nat := 0xffff03fc800fffffffc800fffffffffc0ffff03fc800fffffffc800fffffffffc0fffe03fc000fffff3fc000fffff3fff80fffe03fc000fffff3fc000fffff3fff80
def t271 : Nat := 0xffff03fcc206fbffffc8406fbffffffe0954b0054a97ffdefc55a80ffdefe552d7fffe03fc0000f3ff3fc0000f3ff3fff8000000000000f0c00000000f0c00000000
def t272 : Nat := 0xffff03fce726fbffffce006fbfffffff2954b0055800ffdefc54800ffdefe552c0fffe03fce700f3ff3fce000f3ff3ffff000000000000f0c00000000f0c00000000
def t273 : Nat := 0xffff83fcc606fbffffcc606fbffffffe091431445885fbd6b445885fbd6b6450c5ffffc3fce700f3ff3fce700f3ff3ffff000000400001f0c00400001f0c00400001
def t274 : Nat := 0xffffcbfce006fbffffce726fbffffff8090410000800fad4a041800fad4a200040ffffc3fce000f3ff3fce700f3ff3fff8000000000000f0c00000000f0c00000000
def t275 : Nat := 0xffffcbfce726fbffffce726fbfffffff290410041800fad4a041800fad4a241040ffffc3fce700f3ff3fce700f3ff3ffff000000000000f0c00000000f0c00000000
def t276 : Nat := 0xffffcbfce726fbffffce726fbfffffff2954b5c55a97ffdefc55a97ffdefe552d7ffffcbfce720f3ffbfce720f3ffbffff200000c00003f0c00c00003f0c00c00003
def t277 : Nat := 0xfffffffff80ffbffffeffffffffffff80fad5a200840faf4a3ebd28fad5a200840fffff3fff80ff3ff3fcffcfffff3fff80f0c00000000f0c003c3000f0c00000000
def t278 : Nat := 0xfffffffffc0ff2003fffffffff03fc800fffffffffc0ff2003fffffffff03fc800fffff3fff80ff0003ffffcfffe03fc000fffff3fff80ff0003ffffcfffe03fc000
def t279 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def rowsE (i : Nat) : List Nat :=
  (if i < 274 then (if i < 137 then (if i < 68 then (if i < 34 then (if i < 17 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then [] else []) else (if i < 3 then [] else [])) else (if i < 6 then (if i < 5 then [] else []) else (if i < 7 then [] else [t47,t95,t108,t133,t151,t195,t245]))) else (if i < 12 then (if i < 10 then (if i < 9 then [t61,t68,t95,t108,t133,t151,t195] else [t61,t80,t95,t108,t133,t151,t209]) else (if i < 11 then [t61,t86,t108,t133,t151,t209,t231] else [t61,t95,t106,t133,t151,t209,t231])) else (if i < 14 then (if i < 13 then [t61,t95,t108,t120,t195,t209,t231] else [t61,t95,t108,t128,t151,t209,t231]) else (if i < 15 then [t61,t95,t108,t131,t151,t195,t231] else (if i < 16 then [t61,t95,t108,t133,t148,t195,t209] else [t61,t95,t108,t133,t161,t195,t255]))))) else (if i < 25 then (if i < 21 then (if i < 19 then (if i < 18 then [t61,t95,t108,t133,t164,t195,t209] else [t61,t95,t108,t178,t209,t266,t278]) else (if i < 20 then [t61,t95,t114,t133,t151,t195,t245] else [t61,t95,t122,t133,t151,t195,t255])) else (if i < 23 then (if i < 22 then [t61,t95,t122,t133,t151,t228,t231] else [t61,t95,t133,t142,t168,t209,t231]) else (if i < 24 then [t61,t95,t133,t142,t192,t209,t231] else [t61,t95,t133,t151,t181,t195,t231]))) else (if i < 29 then (if i < 27 then (if i < 26 then [t61,t95,t133,t151,t187,t209,t231] else [t61,t95,t133,t165,t169,t195,t209]) else (if i < 28 then [t61,t95,t133,t165,t174,t195,t209] else [t61,t95,t133,t168,t208,t209,t263])) else (if i < 31 then (if i < 30 then [t61,t95,t133,t169,t197,t209,t270] else [t61,t95,t133,t170,t200,t209,t269]) else (if i < 32 then [t61,t95,t144,t151,t195,t218,t276] else (if i < 33 then [t61,t98,t133,t170,t195,t209,t269] else [t61,t98,t133,t170,t195,t211,t231])))))) else (if i < 51 then (if i < 42 then (if i < 38 then (if i < 36 then (if i < 35 then [t61,t121,t133,t151,t195,t209,t231] else [t61,t133,t151,t177,t195,t209,t231]) else (if i < 37 then [t61,t133,t163,t169,t195,t209,t270] else [t9,t43,t61,t108,t133,t166,t195,t209])) else (if i < 40 then (if i < 39 then [t9,t61,t69,t108,t133,t166,t195,t231] else [t9,t61,t81,t108,t133,t166,t209,t231]) else (if i < 41 then [t9,t61,t108,t133,t140,t195,t209,t231] else [t9,t61,t108,t133,t162,t166,t195,t209]))) else (if i < 46 then (if i < 44 then (if i < 43 then [t9,t61,t108,t133,t166,t195,t209,t231] else [t9,t61,t108,t133,t166,t196,t209,t231]) else (if i < 45 then [t9,t61,t133,t166,t182,t195,t209,t231] else [t11,t43,t95,t108,t133,t159,t195,t209])) else (if i < 48 then (if i < 47 then [t11,t81,t95,t108,t133,t159,t209,t231] else [t11,t95,t108,t133,t146,t195,t209,t231]) else (if i < 49 then [t11,t95,t108,t133,t159,t195,t209,t231] else (if i < 50 then [t11,t95,t108,t159,t172,t195,t209,t231] else [t11,t95,t133,t159,t182,t195,t209,t231]))))) else (if i < 59 then (if i < 55 then (if i < 53 then (if i < 52 then [t11,t108,t133,t159,t193,t195,t209,t231] else [t12,t95,t108,t133,t159,t195,t209,t231]) else (if i < 54 then [t13,t95,t108,t151,t173,t195,t209,t231] else [t14,t61,t95,t108,t127,t151,t209,t231])) else (if i < 57 then (if i < 56 then [t16,t61,t95,t108,t133,t151,t195,t212] else [t17,t61,t108,t133,t166,t195,t209,t231]) else (if i < 58 then [t18,t43,t95,t108,t133,t151,t195,t216] else [t18,t61,t95,t108,t133,t151,t195,t245]))) else (if i < 63 then (if i < 61 then (if i < 60 then [t18,t90,t95,t108,t133,t151,t195,t231] else [t18,t95,t108,t133,t151,t195,t216,t231]) else (if i < 62 then [t18,t95,t108,t133,t151,t195,t216,t253] else [t18,t95,t114,t133,t151,t195,t216,t231])) else (if i < 65 then (if i < 64 then [t18,t95,t133,t151,t182,t195,t216,t231] else [t19,t95,t108,t133,t159,t195,t209,t231]) else (if i < 66 then [t20,t43,t61,t95,t108,t133,t151,t195] else (if i < 67 then [t20,t61,t95,t108,t133,t151,t195,t231] else [t21,t103,t108,t133,t151,t195,t209,t231]))))))) else (if i < 102 then (if i < 85 then (if i < 76 then (if i < 72 then (if i < 70 then (if i < 69 then [t23,t95,t133,t151,t186,t195,t209,t231] else [t25,t61,t95,t108,t133,t151,t195,t209]) else (if i < 71 then [t26,t61,t100,t108,t133,t151,t195,t209] else [t27,t61,t95,t108,t133,t151,t195,t209])) else (if i < 74 then (if i < 73 then [t28,t43,t61,t95,t133,t170,t195,t209] else [t28,t61,t69,t95,t133,t170,t195,t231]) else (if i < 75 then [t28,t61,t81,t95,t133,t170,t209,t231] else [t28,t61,t95,t108,t133,t162,t195,t209]))) else (if i < 80 then (if i < 78 then (if i < 77 then [t28,t61,t95,t133,t136,t195,t209,t231] else [t28,t61,t95,t133,t169,t195,t209,t231]) else (if i < 79 then [t28,t61,t95,t133,t170,t195,t209,t231] else [t28,t61,t95,t133,t170,t195,t209,t269])) else (if i < 82 then (if i < 81 then [t28,t61,t95,t133,t170,t195,t211,t231] else [t28,t61,t95,t133,t170,t200,t209,t231]) else (if i < 83 then [t28,t61,t98,t133,t170,t195,t209,t231] else (if i < 84 then [t28,t61,t108,t133,t163,t195,t209,t231] else [t28,t61,t133,t170,t193,t195,t209,t231]))))) else (if i < 93 then (if i < 89 then (if i < 87 then (if i < 86 then [t29,t61,t108,t133,t166,t195,t209,t231] else [t30,t95,t108,t133,t159,t195,t209,t231]) else (if i < 88 then [t31,t61,t95,t108,t133,t156,t195,t209] else [t32,t43,t61,t95,t108,t179,t195,t209])) else (if i < 91 then (if i < 90 then [t32,t61,t69,t95,t108,t179,t195,t231] else [t32,t61,t95,t108,t119,t195,t209,t231]) else (if i < 92 then [t32,t61,t95,t108,t179,t195,t209,t231] else [t32,t61,t95,t179,t182,t195,t209,t231]))) else (if i < 97 then (if i < 95 then (if i < 94 then [t34,t61,t95,t108,t179,t195,t209,t231] else [t36,t61,t95,t108,t133,t151,t195,t209]) else (if i < 96 then [t38,t61,t95,t108,t133,t151,t195,t209] else [t39,t61,t95,t108,t133,t151,t195,t209])) else (if i < 99 then (if i < 98 then [t41,t61,t95,t108,t133,t151,t195,t209] else [t42,t61,t95,t116,t133,t151,t195,t209]) else (if i < 100 then [t43,t47,t95,t108,t133,t151,t195,t209] else (if i < 101 then [t43,t61,t69,t81,t95,t108,t133,t151] else [t43,t61,t69,t95,t108,t133,t147,t195])))))) else (if i < 119 then (if i < 110 then (if i < 106 then (if i < 104 then (if i < 103 then [t43,t61,t69,t95,t108,t133,t151,t195] else [t43,t61,t69,t95,t108,t151,t172,t195]) else (if i < 105 then [t43,t61,t69,t95,t133,t151,t182,t195] else [t43,t61,t69,t108,t133,t151,t193,t195])) else (if i < 108 then (if i < 107 then [t43,t61,t72,t125,t133,t151,t195,t209] else [t43,t61,t81,t95,t108,t133,t151,t209]) else (if i < 109 then [t43,t61,t81,t95,t133,t151,t182,t209] else [t43,t61,t89,t95,t108,t133,t151,t195]))) else (if i < 114 then (if i < 112 then (if i < 111 then [t43,t61,t95,t108,t133,t147,t195,t209] else [t43,t61,t95,t108,t133,t150,t195,t209]) else (if i < 113 then [t43,t61,t95,t108,t133,t151,t195,t209] else [t43,t61,t95,t108,t133,t151,t195,t210])) else (if i < 116 then (if i < 115 then [t43,t61,t95,t108,t133,t151,t195,t211] else [t43,t61,t95,t108,t133,t151,t195,t213]) else (if i < 117 then [t43,t61,t95,t108,t133,t151,t195,t214] else (if i < 118 then [t43,t61,t95,t108,t133,t151,t195,t215] else [t43,t61,t95,t108,t133,t151,t195,t218]))))) else (if i < 128 then (if i < 123 then (if i < 121 then (if i < 120 then [t43,t61,t95,t108,t133,t151,t195,t220] else [t43,t61,t95,t108,t133,t151,t195,t223]) else (if i < 122 then [t43,t61,t95,t108,t133,t151,t195,t225] else [t43,t61,t95,t108,t133,t151,t196,t209])) else (if i < 125 then (if i < 124 then [t43,t61,t95,t108,t133,t151,t197,t209] else [t43,t61,t95,t108,t133,t151,t198,t209]) else (if i < 126 then [t43,t61,t95,t108,t133,t151,t199,t209] else (if i < 127 then [t43,t61,t95,t108,t133,t151,t200,t209] else [t43,t61,t95,t108,t133,t151,t202,t209])))) else (if i < 132 then (if i < 130 then (if i < 129 then [t43,t61,t95,t108,t133,t151,t209,t227] else [t43,t61,t95,t108,t133,t151,t209,t229]) else (if i < 131 then [t43,t61,t95,t108,t133,t151,t209,t230] else [t43,t61,t95,t108,t133,t152,t195,t209])) else (if i < 134 then (if i < 133 then [t43,t61,t95,t108,t133,t153,t195,t209] else [t43,t61,t95,t108,t133,t154,t195,t209]) else (if i < 135 then [t43,t61,t95,t108,t133,t158,t195,t209] else (if i < 136 then [t43,t61,t95,t108,t133,t160,t195,t209] else [t43,t61,t95,t108,t133,t165,t195,t209])))))))) else (if i < 205 then (if i < 171 then (if i < 154 then (if i < 145 then (if i < 141 then (if i < 139 then (if i < 138 then [t43,t61,t95,t114,t133,t151,t195,t209] else [t43,t61,t95,t118,t133,t151,t195,t209]) else (if i < 140 then [t43,t61,t95,t124,t133,t151,t195,t209] else [t43,t61,t95,t133,t147,t182,t195,t209])) else (if i < 143 then (if i < 142 then [t43,t61,t95,t133,t151,t169,t195,t209] else [t43,t61,t95,t133,t151,t182,t195,t209]) else (if i < 144 then [t43,t61,t97,t108,t133,t151,t195,t209] else [t43,t61,t98,t108,t133,t151,t195,t209]))) else (if i < 149 then (if i < 147 then (if i < 146 then [t43,t61,t101,t108,t133,t151,t195,t209] else [t43,t61,t108,t133,t151,t163,t195,t209]) else (if i < 148 then [t43,t61,t108,t133,t151,t193,t195,t209] else [t43,t61,t133,t151,t182,t193,t195,t209])) else (if i < 151 then (if i < 150 then [t44,t61,t95,t108,t133,t151,t195,t209] else [t45,t61,t95,t108,t133,t151,t195,t209]) else (if i < 152 then [t47,t95,t108,t133,t151,t195,t209,t231] else (if i < 153 then [t47,t95,t108,t133,t151,t195,t209,t254] else [t47,t95,t108,t133,t151,t195,t215,t231]))))) else (if i < 162 then (if i < 158 then (if i < 156 then (if i < 155 then [t47,t95,t108,t133,t151,t195,t216,t231] else [t47,t95,t108,t133,t151,t195,t226,t231]) else (if i < 157 then [t47,t95,t108,t133,t151,t203,t209,t231] else [t47,t95,t114,t133,t151,t195,t209,t231])) else (if i < 160 then (if i < 159 then [t47,t95,t115,t133,t151,t195,t209,t231] else [t47,t95,t133,t151,t182,t195,t209,t231]) else (if i < 161 then [t47,t102,t108,t133,t151,t195,t209,t231] else [t47,t108,t133,t151,t193,t195,t209,t231]))) else (if i < 166 then (if i < 164 then (if i < 163 then [t48,t95,t108,t133,t151,t195,t209,t231] else [t49,t95,t108,t133,t151,t195,t209,t231]) else (if i < 165 then [t50,t95,t108,t133,t151,t195,t209,t231] else [t51,t108,t133,t151,t194,t195,t209,t231])) else (if i < 168 then (if i < 167 then [t52,t95,t108,t133,t151,t195,t209,t231] else [t52,t108,t133,t151,t193,t195,t209,t231]) else (if i < 169 then [t53,t95,t108,t133,t151,t195,t209,t231] else (if i < 170 then [t55,t95,t108,t133,t151,t195,t209,t259] else [t56,t95,t108,t133,t151,t195,t209,t231])))))) else (if i < 188 then (if i < 179 then (if i < 175 then (if i < 173 then (if i < 172 then [t58,t95,t108,t133,t151,t195,t209,t231] else [t59,t95,t108,t133,t151,t195,t209,t231]) else (if i < 174 then [t60,t95,t108,t133,t151,t195,t209,t231] else [t61,t63,t95,t133,t170,t195,t209,t231])) else (if i < 177 then (if i < 176 then [t61,t66,t95,t108,t133,t151,t195,t209] else [t61,t70,t95,t108,t133,t151,t195,t258]) else (if i < 178 then [t61,t72,t125,t133,t151,t195,t209,t231] else [t61,t72,t133,t151,t175,t195,t209,t231]))) else (if i < 183 then (if i < 181 then (if i < 180 then [t61,t74,t125,t133,t151,t195,t209,t231] else [t61,t77,t108,t133,t166,t195,t209,t231]) else (if i < 182 then [t61,t78,t95,t108,t133,t151,t195,t209] else [t61,t82,t95,t108,t133,t151,t209,t231])) else (if i < 185 then (if i < 184 then [t61,t84,t95,t108,t133,t151,t209,t267] else [t61,t87,t133,t151,t189,t195,t209,t231]) else (if i < 186 then [t61,t91,t108,t133,t166,t195,t209,t231] else (if i < 187 then [t61,t92,t108,t133,t151,t195,t209,t231] else [t61,t93,t108,t133,t151,t195,t209,t231]))))) else (if i < 196 then (if i < 192 then (if i < 190 then (if i < 189 then [t61,t94,t108,t133,t151,t195,t209,t231] else [t61,t95,t107,t133,t151,t195,t221,t231]) else (if i < 191 then [t61,t95,t108,t133,t141,t151,t195,t209] else [t61,t95,t108,t133,t149,t195,t209,t270])) else (if i < 194 then (if i < 193 then [t61,t95,t108,t133,t151,t195,t209,t231] else [t61,t95,t108,t133,t151,t195,t209,t232]) else (if i < 195 then [t61,t95,t108,t133,t151,t195,t209,t233] else [t61,t95,t108,t133,t151,t195,t209,t234]))) else (if i < 200 then (if i < 198 then (if i < 197 then [t61,t95,t108,t133,t151,t195,t209,t235] else [t61,t95,t108,t133,t151,t195,t209,t236]) else (if i < 199 then [t61,t95,t108,t133,t151,t195,t209,t237] else [t61,t95,t108,t133,t151,t195,t209,t238])) else (if i < 202 then (if i < 201 then [t61,t95,t108,t133,t151,t195,t209,t239] else [t61,t95,t108,t133,t151,t195,t209,t240]) else (if i < 203 then [t61,t95,t108,t133,t151,t195,t209,t241] else (if i < 204 then [t61,t95,t108,t133,t151,t195,t209,t242] else [t61,t95,t108,t133,t151,t195,t209,t243]))))))) else (if i < 239 then (if i < 222 then (if i < 213 then (if i < 209 then (if i < 207 then (if i < 206 then [t61,t95,t108,t133,t151,t195,t209,t244] else [t61,t95,t108,t133,t151,t195,t209,t245]) else (if i < 208 then [t61,t95,t108,t133,t151,t195,t209,t246] else [t61,t95,t108,t133,t151,t195,t209,t247])) else (if i < 211 then (if i < 210 then [t61,t95,t108,t133,t151,t195,t209,t248] else [t61,t95,t108,t133,t151,t195,t209,t249]) else (if i < 212 then [t61,t95,t108,t133,t151,t195,t209,t250] else [t61,t95,t108,t133,t151,t195,t209,t251]))) else (if i < 217 then (if i < 215 then (if i < 214 then [t61,t95,t108,t133,t151,t195,t209,t252] else [t61,t95,t108,t133,t151,t195,t209,t253]) else (if i < 216 then [t61,t95,t108,t133,t151,t195,t209,t254] else [t61,t95,t108,t133,t151,t195,t209,t255])) else (if i < 219 then (if i < 218 then [t61,t95,t108,t133,t151,t195,t209,t256] else [t61,t95,t108,t133,t151,t195,t209,t257]) else (if i < 220 then [t61,t95,t108,t133,t151,t195,t209,t261] else (if i < 221 then [t61,t95,t108,t133,t151,t195,t209,t264] else [t61,t95,t108,t133,t151,t195,t209,t265]))))) else (if i < 230 then (if i < 226 then (if i < 224 then (if i < 223 then [t61,t95,t108,t133,t151,t195,t209,t268] else [t61,t95,t108,t133,t151,t195,t209,t269]) else (if i < 225 then [t61,t95,t108,t133,t151,t195,t209,t271] else [t61,t95,t108,t133,t151,t195,t209,t272])) else (if i < 228 then (if i < 227 then [t61,t95,t108,t133,t151,t195,t209,t273] else [t61,t95,t108,t133,t151,t195,t209,t275]) else (if i < 229 then [t61,t95,t108,t133,t151,t195,t211,t269] else [t61,t95,t108,t133,t151,t195,t213,t260]))) else (if i < 234 then (if i < 232 then (if i < 231 then [t61,t95,t108,t133,t151,t195,t214,t263] else [t61,t95,t108,t133,t151,t195,t218,t276]) else (if i < 233 then [t61,t95,t108,t133,t151,t195,t219,t258] else [t61,t95,t108,t133,t151,t195,t220,t274])) else (if i < 236 then (if i < 235 then [t61,t95,t108,t133,t151,t195,t221,t245] else [t61,t95,t108,t133,t151,t195,t223,t262]) else (if i < 237 then [t61,t95,t108,t133,t151,t195,t224,t258] else (if i < 238 then [t61,t95,t108,t133,t151,t195,t225,t266] else [t61,t95,t108,t133,t151,t197,t209,t277])))))) else (if i < 256 then (if i < 247 then (if i < 243 then (if i < 241 then (if i < 240 then [t61,t95,t108,t133,t151,t197,t210,t231] else [t61,t95,t108,t133,t151,t200,t209,t269]) else (if i < 242 then [t61,t95,t108,t133,t151,t200,t211,t231] else [t61,t95,t108,t133,t151,t209,t229,t276])) else (if i < 245 then (if i < 244 then [t61,t95,t108,t133,t154,t195,t209,t253] else [t61,t95,t108,t133,t158,t195,t209,t247]) else (if i < 246 then [t61,t95,t108,t133,t165,t195,t209,t276] else [t61,t95,t109,t133,t151,t195,t209,t231]))) else (if i < 251 then (if i < 249 then (if i < 248 then [t61,t95,t110,t133,t151,t195,t209,t231] else [t61,t95,t111,t133,t151,t195,t209,t231]) else (if i < 250 then [t61,t95,t112,t133,t151,t195,t209,t231] else [t61,t95,t114,t133,t151,t195,t209,t231])) else (if i < 253 then (if i < 252 then [t61,t95,t114,t133,t151,t195,t209,t253] else [t61,t95,t114,t133,t151,t195,t216,t231]) else (if i < 254 then [t61,t95,t114,t133,t151,t195,t226,t231] else (if i < 255 then [t61,t95,t114,t133,t151,t199,t209,t231] else [t61,t95,t115,t133,t151,t195,t215,t231]))))) else (if i < 265 then (if i < 260 then (if i < 258 then (if i < 257 then [t61,t95,t117,t133,t151,t195,t209,t231] else [t61,t95,t118,t133,t151,t195,t209,t231]) else (if i < 259 then [t61,t95,t118,t133,t151,t195,t209,t260] else [t61,t95,t118,t133,t151,t209,t230,t231])) else (if i < 262 then (if i < 261 then [t61,t95,t118,t133,t160,t195,t209,t231] else [t61,t95,t122,t133,t151,t195,t209,t231]) else (if i < 263 then [t61,t95,t123,t133,t151,t195,t209,t231] else (if i < 264 then [t61,t95,t133,t137,t151,t195,t209,t231] else [t61,t95,t133,t142,t151,t201,t209,t231])))) else (if i < 269 then (if i < 267 then (if i < 266 then [t61,t95,t133,t143,t151,t195,t209,t231] else [t61,t95,t133,t151,t176,t195,t209,t231]) else (if i < 268 then [t61,t95,t133,t151,t182,t195,t209,t231] else [t61,t95,t133,t151,t182,t195,t209,t245])) else (if i < 271 then (if i < 270 then [t61,t95,t133,t151,t182,t195,t209,t247] else [t61,t95,t133,t151,t182,t195,t209,t250]) else (if i < 272 then [t61,t95,t133,t151,t182,t195,t209,t253] else (if i < 273 then [t61,t95,t133,t151,t182,t195,t209,t269] else [t61,t95,t133,t151,t182,t196,t209,t231]))))))))) else (if i < 411 then (if i < 342 then (if i < 308 then (if i < 291 then (if i < 282 then (if i < 278 then (if i < 276 then (if i < 275 then [t61,t95,t133,t151,t182,t197,t209,t231] else [t61,t95,t133,t151,t182,t200,t209,t231]) else (if i < 277 then [t61,t95,t133,t151,t182,t206,t209,t231] else [t61,t95,t133,t151,t182,t209,t227,t231])) else (if i < 280 then (if i < 279 then [t61,t95,t133,t151,t182,t209,t230,t231] else [t61,t95,t133,t151,t183,t195,t209,t231]) else (if i < 281 then [t61,t95,t133,t151,t185,t195,t209,t276] else [t61,t95,t133,t151,t188,t195,t209,t231]))) else (if i < 286 then (if i < 284 then (if i < 283 then [t61,t95,t133,t151,t190,t208,t209,t231] else [t61,t97,t114,t133,t151,t195,t209,t231]) else (if i < 285 then [t61,t97,t133,t151,t182,t195,t209,t231] else [t61,t98,t133,t151,t182,t195,t209,t231])) else (if i < 288 then (if i < 287 then [t61,t125,t133,t151,t195,t207,t209,t231] else [t61,t133,t151,t182,t193,t195,t209,t231]) else (if i < 289 then [t1,t43,t61,t95,t108,t133,t151,t195,t209] else (if i < 290 then [t1,t61,t95,t108,t133,t151,t195,t209,t231] else [t1,t61,t95,t133,t151,t182,t195,t209,t231]))))) else (if i < 299 then (if i < 295 then (if i < 293 then (if i < 292 then [t2,t61,t95,t108,t133,t151,t195,t209,t231] else [t3,t61,t95,t108,t133,t151,t195,t209,t231]) else (if i < 294 then [t4,t61,t95,t108,t133,t151,t195,t209,t231] else [t5,t61,t95,t108,t133,t151,t195,t209,t231])) else (if i < 297 then (if i < 296 then [t6,t61,t95,t108,t133,t151,t195,t209,t231] else [t7,t61,t95,t108,t133,t151,t195,t209,t231]) else (if i < 298 then [t8,t61,t95,t108,t133,t151,t195,t209,t231] else [t9,t43,t61,t95,t108,t133,t151,t195,t209]))) else (if i < 303 then (if i < 301 then (if i < 300 then [t9,t61,t69,t95,t108,t133,t151,t195,t231] else [t9,t61,t81,t95,t108,t133,t151,t209,t231]) else (if i < 302 then [t9,t61,t95,t108,t133,t147,t195,t209,t231] else [t9,t61,t95,t108,t133,t151,t195,t209,t231])) else (if i < 305 then (if i < 304 then [t9,t61,t95,t108,t133,t151,t196,t209,t231] else [t9,t61,t95,t108,t133,t166,t195,t209,t231]) else (if i < 306 then [t9,t61,t95,t133,t151,t182,t195,t209,t231] else (if i < 307 then [t9,t61,t108,t133,t151,t166,t195,t209,t231] else [t9,t61,t108,t133,t151,t193,t195,t209,t231])))))) else (if i < 325 then (if i < 316 then (if i < 312 then (if i < 310 then (if i < 309 then [t9,t61,t108,t133,t166,t195,t209,t231] else [t10,t61,t95,t108,t133,t151,t195,t209,t231]) else (if i < 311 then [t11,t43,t61,t95,t108,t133,t151,t195,t209] else [t11,t61,t81,t95,t108,t133,t151,t209,t231])) else (if i < 314 then (if i < 313 then [t11,t61,t95,t108,t133,t147,t195,t209,t231] else [t11,t61,t95,t108,t133,t151,t195,t209,t231]) else (if i < 315 then [t11,t61,t95,t108,t133,t159,t195,t209,t231] else [t11,t61,t95,t108,t151,t172,t195,t209,t231]))) else (if i < 320 then (if i < 318 then (if i < 317 then [t11,t61,t95,t133,t151,t182,t195,t209,t231] else [t11,t61,t108,t133,t151,t193,t195,t209,t231]) else (if i < 319 then [t11,t95,t108,t133,t159,t195,t209,t231] else [t12,t61,t95,t108,t133,t151,t195,t209,t231])) else (if i < 322 then (if i < 321 then [t13,t61,t95,t108,t133,t151,t195,t209,t231] else [t13,t61,t95,t108,t151,t172,t195,t209,t231]) else (if i < 323 then [t14,t61,t95,t108,t133,t151,t195,t209,t231] else (if i < 324 then [t15,t61,t95,t108,t133,t151,t195,t209,t231] else [t16,t43,t61,t95,t108,t133,t151,t195,t209]))))) else (if i < 333 then (if i < 329 then (if i < 327 then (if i < 326 then [t16,t61,t95,t108,t133,t151,t195,t209,t231] else [t17,t61,t95,t108,t133,t151,t195,t209,t231]) else (if i < 328 then [t18,t43,t61,t95,t108,t133,t151,t195,t209] else [t18,t46,t95,t108,t133,t151,t195,t209,t231])) else (if i < 331 then (if i < 330 then [t18,t61,t69,t95,t108,t133,t151,t195,t231] else [t18,t61,t95,t108,t133,t151,t195,t209,t231]) else (if i < 332 then [t18,t61,t95,t108,t133,t151,t195,t209,t253] else [t18,t61,t95,t108,t133,t151,t195,t216,t231]))) else (if i < 337 then (if i < 335 then (if i < 334 then [t18,t61,t95,t108,t133,t151,t195,t226,t231] else [t18,t61,t95,t114,t133,t151,t195,t209,t231]) else (if i < 336 then [t18,t61,t95,t133,t151,t182,t195,t209,t231] else [t18,t95,t108,t133,t151,t195,t216,t231])) else (if i < 339 then (if i < 338 then [t19,t61,t95,t108,t133,t151,t195,t209,t231] else [t21,t61,t95,t108,t133,t151,t195,t209,t231]) else (if i < 340 then [t22,t61,t95,t108,t133,t151,t195,t209,t231] else (if i < 341 then [t23,t61,t95,t108,t133,t151,t195,t209,t231] else [t23,t61,t95,t133,t151,t182,t195,t209,t231]))))))) else (if i < 376 then (if i < 359 then (if i < 350 then (if i < 346 then (if i < 344 then (if i < 343 then [t24,t61,t95,t108,t133,t151,t195,t209,t231] else [t26,t43,t61,t95,t108,t133,t151,t195,t209]) else (if i < 345 then [t26,t61,t95,t108,t133,t151,t195,t209,t231] else [t28,t43,t61,t95,t108,t133,t151,t195,t209])) else (if i < 348 then (if i < 347 then [t28,t61,t69,t95,t108,t133,t151,t195,t231] else [t28,t61,t81,t95,t108,t133,t151,t209,t231]) else (if i < 349 then [t28,t61,t95,t108,t133,t147,t195,t209,t231] else [t28,t61,t95,t108,t133,t151,t195,t209,t231]))) else (if i < 354 then (if i < 352 then (if i < 351 then [t28,t61,t95,t108,t133,t151,t195,t209,t269] else [t28,t61,t95,t108,t133,t151,t195,t211,t231]) else (if i < 353 then [t28,t61,t95,t108,t133,t151,t200,t209,t231] else [t28,t61,t95,t108,t133,t166,t195,t209,t231])) else (if i < 356 then (if i < 355 then [t28,t61,t95,t108,t133,t170,t195,t209,t231] else [t28,t61,t95,t133,t151,t170,t195,t209,t231]) else (if i < 357 then [t28,t61,t95,t133,t151,t182,t195,t209,t231] else (if i < 358 then [t28,t61,t95,t133,t170,t195,t209,t231] else [t28,t61,t98,t108,t133,t151,t195,t209,t231]))))) else (if i < 367 then (if i < 363 then (if i < 361 then (if i < 360 then [t28,t61,t108,t133,t151,t193,t195,t209,t231] else [t29,t61,t95,t108,t133,t151,t195,t209,t231]) else (if i < 362 then [t30,t61,t95,t108,t133,t151,t195,t209,t231] else [t31,t43,t61,t95,t108,t133,t151,t195,t209])) else (if i < 365 then (if i < 364 then [t31,t61,t95,t108,t133,t151,t195,t209,t231] else [t32,t43,t61,t95,t108,t133,t151,t195,t209]) else (if i < 366 then [t32,t61,t69,t95,t108,t133,t151,t195,t231] else [t32,t61,t95,t108,t133,t147,t195,t209,t231]))) else (if i < 371 then (if i < 369 then (if i < 368 then [t32,t61,t95,t108,t133,t151,t195,t209,t231] else [t32,t61,t95,t108,t133,t179,t195,t209,t231]) else (if i < 370 then [t32,t61,t95,t108,t179,t195,t209,t231] else [t32,t61,t95,t133,t151,t182,t195,t209,t231])) else (if i < 373 then (if i < 372 then [t33,t61,t95,t108,t133,t151,t195,t209,t231] else [t34,t61,t95,t108,t133,t151,t195,t209,t231]) else (if i < 374 then [t35,t61,t95,t108,t133,t151,t195,t209,t231] else (if i < 375 then [t37,t61,t95,t108,t133,t151,t195,t209,t231] else [t40,t61,t95,t108,t133,t151,t195,t209,t231])))))) else (if i < 393 then (if i < 384 then (if i < 380 then (if i < 378 then (if i < 377 then [t42,t43,t61,t95,t108,t133,t151,t195,t209] else [t42,t61,t95,t108,t133,t151,t195,t209,t231]) else (if i < 379 then [t43,t43,t61,t95,t108,t133,t151,t195,t209] else [t43,t61,t61,t95,t108,t133,t151,t195,t209])) else (if i < 382 then (if i < 381 then [t43,t61,t67,t95,t108,t133,t151,t195,t209] else [t43,t61,t69,t95,t108,t133,t151,t195]) else (if i < 383 then [t43,t61,t69,t95,t108,t133,t151,t195,t209] else [t43,t61,t72,t95,t108,t133,t151,t195,t209]))) else (if i < 388 then (if i < 386 then (if i < 385 then [t43,t61,t81,t95,t108,t133,t151,t195,t209] else [t43,t61,t81,t95,t108,t133,t151,t209]) else (if i < 387 then [t43,t61,t95,t95,t108,t133,t151,t195,t209] else [t43,t61,t95,t100,t108,t133,t151,t195,t209])) else (if i < 390 then (if i < 389 then [t43,t61,t95,t103,t108,t133,t151,t195,t209] else [t43,t61,t95,t108,t108,t133,t151,t195,t209]) else (if i < 391 then [t43,t61,t95,t108,t115,t133,t151,t195,t209] else (if i < 392 then [t43,t61,t95,t108,t116,t133,t151,t195,t209] else [t43,t61,t95,t108,t125,t133,t151,t195,t209]))))) else (if i < 402 then (if i < 397 then (if i < 395 then (if i < 394 then [t43,t61,t95,t108,t133,t133,t151,t195,t209] else [t43,t61,t95,t108,t133,t134,t151,t195,t209]) else (if i < 396 then [t43,t61,t95,t108,t133,t135,t151,t195,t209] else [t43,t61,t95,t108,t133,t138,t151,t195,t209])) else (if i < 399 then (if i < 398 then [t43,t61,t95,t108,t133,t145,t151,t195,t209] else [t43,t61,t95,t108,t133,t147,t151,t195,t209]) else (if i < 400 then [t43,t61,t95,t108,t133,t147,t195,t209] else (if i < 401 then [t43,t61,t95,t108,t133,t151,t151,t195,t209] else [t43,t61,t95,t108,t133,t151,t156,t195,t209])))) else (if i < 406 then (if i < 404 then (if i < 403 then [t43,t61,t95,t108,t133,t151,t159,t195,t209] else [t43,t61,t95,t108,t133,t151,t166,t195,t209]) else (if i < 405 then [t43,t61,t95,t108,t133,t151,t170,t195,t209] else [t43,t61,t95,t108,t133,t151,t179,t195,t209])) else (if i < 408 then (if i < 407 then [t43,t61,t95,t108,t133,t151,t182,t195,t209] else [t43,t61,t95,t108,t133,t151,t193,t195,t209]) else (if i < 409 then [t43,t61,t95,t108,t133,t151,t195,t204,t209] else (if i < 410 then [t43,t61,t95,t108,t133,t151,t195,t209] else [t43,t61,t95,t108,t133,t151,t195,t209,t216])))))))) else (if i < 480 then (if i < 445 then (if i < 428 then (if i < 419 then (if i < 415 then (if i < 413 then (if i < 412 then [t43,t61,t95,t108,t133,t151,t195,t209,t226] else [t43,t61,t95,t108,t133,t151,t195,t209,t231]) else (if i < 414 then [t43,t61,t95,t108,t133,t151,t195,t209,t258] else [t43,t61,t95,t108,t133,t151,t195,t209,t259])) else (if i < 417 then (if i < 416 then [t43,t61,t95,t108,t133,t151,t195,t209,t262] else [t43,t61,t95,t108,t133,t151,t195,t209,t270]) else (if i < 418 then [t43,t61,t95,t108,t133,t151,t195,t209,t276] else [t43,t61,t95,t108,t133,t151,t195,t209,t279]))) else (if i < 423 then (if i < 421 then (if i < 420 then [t43,t61,t95,t133,t151,t182,t195,t209] else [t43,t61,t95,t133,t151,t182,t195,t209,t231]) else (if i < 422 then [t43,t61,t108,t133,t151,t193,t195,t209] else [t43,t61,t108,t133,t151,t193,t195,t209,t231])) else (if i < 425 then (if i < 424 then [t47,t61,t95,t108,t133,t151,t195,t209,t231] else [t47,t95,t108,t133,t151,t195,t209,t221,t231]) else (if i < 426 then [t47,t95,t108,t133,t151,t195,t209,t231] else (if i < 427 then [t51,t61,t95,t108,t133,t151,t195,t209,t231] else [t51,t61,t108,t133,t151,t193,t195,t209,t231]))))) else (if i < 436 then (if i < 432 then (if i < 430 then (if i < 429 then [t54,t61,t95,t108,t133,t151,t195,t209,t231] else [t55,t61,t95,t108,t133,t151,t195,t209,t231]) else (if i < 431 then [t57,t61,t95,t108,t133,t151,t195,t209,t231] else [t61,t61,t95,t108,t133,t151,t195,t209,t231])) else (if i < 434 then (if i < 433 then [t61,t61,t95,t133,t151,t182,t195,t209,t231] else [t61,t61,t108,t133,t151,t193,t195,t209,t231]) else (if i < 435 then [t61,t62,t95,t108,t133,t151,t195,t209,t231] else [t61,t63,t95,t108,t133,t151,t195,t209,t231]))) else (if i < 440 then (if i < 438 then (if i < 437 then [t61,t64,t95,t108,t133,t151,t195,t209,t231] else [t61,t65,t95,t108,t133,t151,t195,t209,t231]) else (if i < 439 then [t61,t67,t95,t108,t133,t151,t195,t209,t231] else [t61,t70,t95,t108,t133,t151,t195,t209,t231])) else (if i < 442 then (if i < 441 then [t61,t71,t95,t108,t133,t151,t195,t209,t231] else [t61,t72,t95,t108,t133,t151,t195,t209,t231]) else (if i < 443 then [t61,t72,t95,t125,t133,t151,t195,t209,t231] else (if i < 444 then [t61,t72,t95,t133,t151,t182,t195,t209,t231] else [t61,t72,t125,t133,t151,t195,t209,t231])))))) else (if i < 462 then (if i < 453 then (if i < 449 then (if i < 447 then (if i < 446 then [t61,t73,t95,t108,t133,t151,t195,t209,t231] else [t61,t74,t95,t108,t133,t151,t195,t209,t231]) else (if i < 448 then [t61,t75,t95,t108,t133,t151,t195,t209,t231] else [t61,t76,t95,t108,t133,t151,t195,t209,t231])) else (if i < 451 then (if i < 450 then [t61,t79,t95,t108,t133,t151,t195,t209,t231] else [t61,t83,t95,t108,t133,t151,t195,t209,t231]) else (if i < 452 then [t61,t84,t95,t108,t133,t151,t195,t209,t231] else [t61,t85,t95,t108,t133,t151,t195,t209,t231]))) else (if i < 457 then (if i < 455 then (if i < 454 then [t61,t87,t95,t108,t133,t151,t195,t209,t231] else [t61,t87,t95,t133,t151,t182,t195,t209,t231]) else (if i < 456 then [t61,t88,t95,t108,t133,t151,t195,t209,t231] else [t61,t90,t95,t108,t133,t151,t195,t209,t231])) else (if i < 459 then (if i < 458 then [t61,t95,t95,t108,t133,t151,t195,t209,t231] else [t61,t95,t95,t133,t151,t182,t195,t209,t231]) else (if i < 460 then [t61,t95,t96,t108,t133,t151,t195,t209,t231] else (if i < 461 then [t61,t95,t97,t108,t133,t151,t195,t209,t231] else [t61,t95,t98,t108,t133,t151,t195,t209,t231]))))) else (if i < 471 then (if i < 466 then (if i < 464 then (if i < 463 then [t61,t95,t99,t108,t133,t151,t195,t209,t231] else [t61,t95,t100,t108,t133,t151,t195,t209,t231]) else (if i < 465 then [t61,t95,t103,t108,t133,t151,t195,t209,t231] else [t61,t95,t103,t133,t151,t182,t195,t209,t231])) else (if i < 468 then (if i < 467 then [t61,t95,t104,t108,t133,t151,t195,t209,t231] else [t61,t95,t105,t108,t133,t151,t195,t209,t231]) else (if i < 469 then [t61,t95,t107,t108,t133,t151,t195,t209,t231] else (if i < 470 then [t61,t95,t108,t113,t133,t151,t195,t209,t231] else [t61,t95,t108,t115,t133,t151,t195,t209,t231])))) else (if i < 475 then (if i < 473 then (if i < 472 then [t61,t95,t108,t125,t133,t151,t195,t209,t231] else [t61,t95,t108,t126,t133,t151,t195,t209,t231]) else (if i < 474 then [t61,t95,t108,t129,t133,t151,t195,t209,t231] else [t61,t95,t108,t130,t133,t151,t195,t209,t231])) else (if i < 477 then (if i < 476 then [t61,t95,t108,t132,t133,t151,t195,t209,t231] else [t61,t95,t108,t133,t134,t151,t195,t209,t231]) else (if i < 478 then [t61,t95,t108,t133,t139,t151,t195,t209,t231] else (if i < 479 then [t61,t95,t108,t133,t149,t151,t195,t209,t231] else [t61,t95,t108,t133,t151,t155,t195,t209,t231]))))))) else (if i < 514 then (if i < 497 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then [t61,t95,t108,t133,t151,t157,t195,t209,t231] else [t61,t95,t108,t133,t151,t159,t195,t209,t231]) else (if i < 483 then [t61,t95,t108,t133,t151,t167,t195,t209,t231] else [t61,t95,t108,t133,t151,t171,t195,t209,t231])) else (if i < 486 then (if i < 485 then [t61,t95,t108,t133,t151,t175,t195,t209,t231] else [t61,t95,t108,t133,t151,t180,t195,t209,t231]) else (if i < 487 then [t61,t95,t108,t133,t151,t182,t195,t209,t231] else [t61,t95,t108,t133,t151,t184,t195,t209,t231]))) else (if i < 492 then (if i < 490 then (if i < 489 then [t61,t95,t108,t133,t151,t185,t195,t209,t231] else [t61,t95,t108,t133,t151,t189,t195,t209,t231]) else (if i < 491 then [t61,t95,t108,t133,t151,t190,t195,t209,t231] else [t61,t95,t108,t133,t151,t191,t195,t209,t231])) else (if i < 494 then (if i < 493 then [t61,t95,t108,t133,t151,t195,t205,t209,t231] else [t61,t95,t108,t133,t151,t195,t207,t209,t231]) else (if i < 495 then [t61,t95,t108,t133,t151,t195,t209,t216,t231] else (if i < 496 then [t61,t95,t108,t133,t151,t195,t209,t217,t231] else [t61,t95,t108,t133,t151,t195,t209,t222,t231]))))) else (if i < 505 then (if i < 501 then (if i < 499 then (if i < 498 then [t61,t95,t108,t133,t151,t195,t209,t231] else [t61,t95,t108,t133,t151,t195,t209,t231,t279]) else (if i < 500 then [t61,t95,t108,t133,t151,t195,t209,t245] else [t61,t95,t108,t133,t151,t195,t209,t247])) else (if i < 503 then (if i < 502 then [t61,t95,t108,t133,t151,t195,t209,t250] else [t61,t95,t108,t133,t151,t195,t209,t253]) else (if i < 504 then [t61,t95,t108,t133,t151,t195,t209,t258,t259] else [t61,t95,t108,t133,t151,t195,t209,t258,t262]))) else (if i < 509 then (if i < 507 then (if i < 506 then [t61,t95,t108,t133,t151,t195,t209,t258,t276] else [t61,t95,t108,t133,t151,t195,t209,t259,t276]) else (if i < 508 then [t61,t95,t108,t133,t151,t195,t209,t269] else [t61,t95,t108,t133,t151,t195,t209,t270,t276])) else (if i < 511 then (if i < 510 then [t61,t95,t114,t133,t151,t195,t209,t231] else [t61,t95,t115,t133,t151,t182,t195,t209,t231]) else (if i < 512 then [t61,t95,t115,t133,t151,t195,t209,t221,t231] else (if i < 513 then [t61,t95,t118,t133,t151,t195,t209,t231] else [t61,t95,t125,t133,t145,t151,t195,t209,t231])))))) else (if i < 531 then (if i < 522 then (if i < 518 then (if i < 516 then (if i < 515 then [t61,t95,t125,t133,t151,t182,t195,t209,t231] else [t61,t95,t133,t134,t151,t182,t195,t209,t231]) else (if i < 517 then [t61,t95,t133,t138,t151,t182,t195,t209,t231] else [t61,t95,t133,t145,t151,t182,t195,t209,t231])) else (if i < 520 then (if i < 519 then [t61,t95,t133,t151,t159,t182,t195,t209,t231] else [t61,t95,t133,t151,t182,t182,t195,t209,t231]) else (if i < 521 then [t61,t95,t133,t151,t182,t184,t195,t209,t231] else [t61,t95,t133,t151,t182,t189,t195,t209,t231]))) else (if i < 526 then (if i < 524 then (if i < 523 then [t61,t95,t133,t151,t182,t191,t195,t209,t231] else [t61,t95,t133,t151,t182,t193,t195,t209,t231]) else (if i < 525 then [t61,t95,t133,t151,t182,t195,t209,t216,t231] else [t61,t95,t133,t151,t182,t195,t209,t226,t231])) else (if i < 528 then (if i < 527 then [t61,t95,t133,t151,t182,t195,t209,t231] else [t61,t95,t133,t151,t182,t195,t209,t231,t279]) else (if i < 529 then [t61,t133,t151,t182,t193,t195,t209,t231] else (if i < 530 then [t9,t61,t95,t108,t133,t151,t195,t209,t231] else [t11,t61,t95,t108,t133,t151,t195,t209,t231]))))) else (if i < 540 then (if i < 535 then (if i < 533 then (if i < 532 then [t18,t61,t95,t108,t133,t151,t195,t209,t231] else [t28,t61,t95,t108,t133,t151,t195,t209,t231]) else (if i < 534 then [t32,t61,t95,t108,t133,t151,t195,t209,t231] else [t43,t61,t95,t108,t133,t151,t195,t209])) else (if i < 537 then (if i < 536 then [t43,t61,t95,t108,t133,t151,t195,t209,t231] else [t61,t61,t95,t108,t133,t151,t195,t209,t231]) else (if i < 538 then [t61,t72,t95,t108,t133,t151,t195,t209,t231] else (if i < 539 then [t61,t95,t95,t108,t133,t151,t195,t209,t231] else [t61,t95,t103,t108,t133,t151,t195,t209,t231])))) else (if i < 544 then (if i < 542 then (if i < 541 then [t61,t95,t108,t115,t133,t151,t195,t209,t231] else [t61,t95,t108,t125,t133,t151,t195,t209,t231]) else (if i < 543 then [t61,t95,t108,t133,t134,t151,t195,t209,t231] else [t61,t95,t108,t133,t151,t159,t195,t209,t231])) else (if i < 546 then (if i < 545 then [t61,t95,t108,t133,t151,t182,t195,t209,t231] else [t61,t95,t108,t133,t151,t195,t209,t216,t231]) else (if i < 547 then [t61,t95,t108,t133,t151,t195,t209,t231] else (if i < 548 then [t61,t95,t133,t151,t182,t195,t209,t231] else [t61,t95,t108,t133,t151,t195,t209,t231]))))))))))

def sixE (i : Nat) : Nat :=
  (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x88010f92144d0e else 0xa007005a24510b) else (if i < 3 then 0xa0040f91342d0e else 0x8000492a42d08)) else (if i < 6 then (if i < 5 then 0x8000311442d08 else 0xa0040f92144d0e) else (if i < 7 then 0xe0040493746d13 else 0x8020051e47908))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x51e42108 else 0x8000110b42108) else (if i < 11 then 0x220000010842108 else 0x8000892a48508)) else (if i < 14 then (if i < 13 then 0x4000010842108 else 0x8000493442d08) else (if i < 15 then 0xf8090493746d13 else 0x2200c0892a48514)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0xe0002b11442d08 else 0x30003092a47514) else (if i < 19 then 0xa0003092a42d08 else 0x312142d08)) else (if i < 22 then (if i < 21 then 0x30020058c4210b else 0x220040058c4210b) else (if i < 23 then 0xf8090493746d24 else 0x2200c3092a47514))) else (if i < 28 then (if i < 26 then (if i < 25 then 0x308120051e4391d else 0x234220e1374212a) else (if i < 27 then 0x30812005a24791d else 0xa0040491d46d0e)) else (if i < 30 then (if i < 29 then 0x234283092a42d08 else 0xf8090a13343913) else (if i < 31 then 0x25828005b84d133 else (if i < 32 then 0x30020058c4250b else 0x30020058d4210b))))))

def segE (i : Nat) : Nat :=
  (if i < 274 then (if i < 137 then (if i < 68 then (if i < 34 then (if i < 17 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x101 else 0x101) else (if i < 3 then 0x101 else 0x101)) else (if i < 6 then (if i < 5 then 0x101 else 0x101) else (if i < 7 then 0x101 else 0x10004001000400100040010004001000400100040010709070000040000030d09))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x101 else 0x101) else (if i < 11 then 0x101 else 0x101)) else (if i < 14 then (if i < 13 then 0x101 else 0x101) else (if i < 15 then 0x101 else (if i < 16 then 0x101 else 0xc003000c0030014003000c003000400300080604020a05))))) else (if i < 25 then (if i < 21 then (if i < 19 then (if i < 18 then 0x7001c007001c007001c007001c007001c007001c0070c0a09070503020000000d0a else 0x9002400900240090024009000701) else (if i < 20 then 0x2c00b002c00b002c00b002c00b000400b00080604020a05 else 0x2c00b002c00b002c00b002c00b000400b00080604020a05)) else (if i < 23 then (if i < 22 then 0x2c00b002c00b002c00b002c00b000400b00080604020a05 else 0x2400900240090024009002400900240090009050a03) else (if i < 24 then 0x2400900240090024009002400900240090009050a03 else 0x101))) else (if i < 29 then (if i < 27 then (if i < 26 then 0x101 else 0x7001c007001c007001c007000701) else (if i < 28 then 0x1c0070034007001c007001c007001c007000300000a04 else 0x9002400900240090024009000701)) else (if i < 31 then (if i < 30 then 0x7001c007001c007001c007000701 else 0xb002c00b002c00b002c00b000701) else (if i < 32 then 0x34009002400900240090024009000002000804 else (if i < 33 then 0xb002c00b002c00b002c00b000701 else 0xb002c00b002c00b002c00b000701)))))) else (if i < 51 then (if i < 42 then (if i < 38 then (if i < 36 then (if i < 35 then 0x101 else 0x101) else (if i < 37 then 0x7001c007001c007001c007000701 else 0x9000101)) else (if i < 40 then (if i < 39 then 0x9000101 else 0x9000101) else (if i < 41 then 0x2404c00000202 else 0x1c007001c007001c007001c007001c007001c007001c007001c007001c007001c007000000000a020605030808140b))) else (if i < 46 then (if i < 44 then (if i < 43 then 0x1c0090024009002400900240090024009002400900240090002020700000003000900000e0c else 0x24011002400900240070024009003c009002400900240090930009002400900240090002040c0f010f04060007140b) else (if i < 45 then 0x9000101 else 0x9000101)) else (if i < 48 then (if i < 47 then 0x9000101 else 0x240b600000202) else (if i < 49 then 0x2400b00240090024009002400900240090024009070505000000000c07 else (if i < 50 then 0x9000101 else 0x9000101))))) else (if i < 59 then (if i < 55 then (if i < 53 then (if i < 52 then 0x9000101 else 0x2400b00240090024009002400900240090024009070505000000000c07) else (if i < 54 then 0x101 else 0x2409000000202)) else (if i < 57 then (if i < 56 then 0x101 else 0x1c0090024009002400900240090024009002400900240090002020700000003000900000e0c) else (if i < 58 then 0xb000101 else 0xb002c00b002c013002c00b002c00b002c120002c00b002c00b05f800b002c00b002c00b002c0010e00040c010111090b0409170b))) else (if i < 63 then (if i < 61 then (if i < 60 then 0x2c00b002c00b002c1cc002c00b002c00b002c00b002c00b002c00b002c00b110e00010e0100050b00070000120d else 0x2c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b0f0d0c06090103000603010000100d) else (if i < 62 then 0xb002c00b001400b002c112002c00b002c00b005400b002c220002c00b002c00b002c00b100a120f01030009001509 else 0xb002c015002c00b0af0216002c00b002c214002c00b002c00b002c00b002c00b002c00b002c00b03000f0c000400090801170a)) else (if i < 65 then (if i < 64 then 0xb000101 else 0xb002c00b005c017002c00b002c00b002c00b002c00b030b02000900000d07) else (if i < 66 then 0x9000101 else (if i < 67 then 0x24009002400900240090024009000000000804 else 0x2400b002c019006400b002c00b002c019002c00b002c00b002c00b00090707000604001008))))))) else (if i < 102 then (if i < 85 then (if i < 76 then (if i < 72 then (if i < 70 then (if i < 69 then 0x101 else 0x9000101) else (if i < 71 then 0x101 else 0xb000101)) else (if i < 74 then (if i < 73 then 0xb000101 else 0xb000101) else (if i < 75 then 0xb000101 else 0x1c012001c007001c007001c007001c007001c0f0001c00e001c007001c007001c00d001c007001c007001c007001c007010003150004180c090a1c0a))) else (if i < 80 then (if i < 78 then (if i < 77 then 0x2c06400000202 else 0xd003400d003400d00341700034007003400d003400d003400d003401b003400d001c00d05b000d0b001113000800110011170a) else (if i < 79 then 0x2c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b0f0d0c04080002000401010000100d else 0xb002c00b002c00b002c00b002c00b006c228002c00b096000b002c00b002c232002c00b002c00b001501100003060d000108040700170e)) else (if i < 82 then (if i < 81 then 0xb002c00b002c00b002c00b002c00b006c00b002c1fc002c00b09c000b002c00b002c00b1412020b06000a090402070200150d else 0xb002c00b002c00b002c00b002c00b002c00b002c200002c00b002c01b08a000b002c00b0a010000110d1106080401150b) else (if i < 83 then 0x258006c270002c00b002c00b002c27a002c00b002c00b002c00b002c00b002c00b002c00b002c00b02120201040801070d02090300170d else (if i < 84 then 0xd003401b00341d4003400d003400d003400d003412e003400d003400700341320034007003400d003400d000a050e12000d0a0209070203190d else 0xb000101))))) else (if i < 93 then (if i < 89 then (if i < 87 then (if i < 86 then 0x1c01b006c01b006c01b006c01b006c01b006c01b006c01b0002020700000003000900000e0c else 0x2c00b002c017002c00b002c00b002c00b002c00b070505000000000c07) else (if i < 88 then 0x101 else 0x9000101)) else (if i < 91 then (if i < 90 then 0x9000101 else 0x2407800000202) else (if i < 92 then 0x240090024009002400900240090024009000705000a04 else 0x9000101))) else (if i < 97 then (if i < 95 then (if i < 94 then 0x2c00b002c00b002c00b002c00b002c00b000705000a04 else 0xb000101) else (if i < 96 then 0x9000101 else 0x9000101)) else (if i < 99 then (if i < 98 then 0x9000101 else 0x101) else (if i < 100 then 0x1000101 else (if i < 101 then 0x101 else 0x101)))))) else (if i < 119 then (if i < 110 then (if i < 106 then (if i < 104 then (if i < 103 then 0x101 else 0x101) else (if i < 105 then 0x101 else 0x101)) else (if i < 108 then (if i < 107 then 0x9000101 else 0x101) else (if i < 109 then 0x101 else 0xb000101))) else (if i < 114 then (if i < 112 then (if i < 111 then 0x101 else 0xd000101) else (if i < 113 then 0x9000101 else 0x9000101)) else (if i < 116 then (if i < 115 then 0x9000101 else 0x9000101) else (if i < 117 then 0x9000101 else (if i < 118 then 0xb000101 else 0x9000101))))) else (if i < 128 then (if i < 123 then (if i < 121 then (if i < 120 then 0x9000101 else 0x9000101) else (if i < 122 then 0x9000101 else 0x9000101)) else (if i < 125 then (if i < 124 then 0x9000101 else 0x9000101) else (if i < 126 then 0xb000101 else (if i < 127 then 0xb000101 else 0xb000101)))) else (if i < 132 then (if i < 130 then (if i < 129 then 0x9000101 else 0x9000101) else (if i < 131 then 0x9000101 else 0xb000101)) else (if i < 134 then (if i < 133 then 0x9000101 else 0x9000101) else (if i < 135 then 0xb000101 else (if i < 136 then 0x9000101 else 0x9000101)))))))) else (if i < 205 then (if i < 171 then (if i < 154 then (if i < 145 then (if i < 141 then (if i < 139 then (if i < 138 then 0xb000101 else 0x9000101) else (if i < 140 then 0x9000101 else 0x101)) else (if i < 143 then (if i < 142 then 0x9000101 else 0x101) else (if i < 144 then 0xb000101 else 0xb000101))) else (if i < 149 then (if i < 147 then (if i < 146 then 0xb000101 else 0x9000101) else (if i < 148 then 0x101 else 0x101)) else (if i < 151 then (if i < 150 then 0x9000101 else 0x9000101) else (if i < 152 then 0x400100040010004001000400100040010074001000400100040010004001060701030903000205000700000f0100021211 else (if i < 153 then 0x100040010004001000401f039000100040010004001000400100040010004164000400100740010a0604000b020e0c000c060102170d else 0x1000400100040010004001000400100040010074001000401f07c0001000400100040010b060f0010010d0301000b150b))))) else (if i < 162 then (if i < 158 then (if i < 156 then (if i < 155 then 0xb002c00b002c01f002c00b002c00b002c00b002c00b002c00b002c00b002c00b00050511000008031308 else 0x401f00040010004001007c001000400100040010004001000400100040010004001007c0010007020a020300110500160a) else (if i < 157 then 0x400100040010004001000401d000400103b0001000401f0004001000400100041820530001000400100040011816041404010c0801060100001a0d else 0x1007400100040010004001000418a00040010004001000400100040010004182000400100040010c05090b03040011101709)) else (if i < 160 then (if i < 159 then 0xb002c00b002c00b002c00b002c01d002c00b002c00b002c00b002c00b002c00b00050411000008031308 else 0x1000101) else (if i < 161 then 0x4001000400107c001d007400105900010570001000400100040010530001000400100040010510001000400100040010004001011c0c000913040c00110101021e0d else 0x1000101))) else (if i < 166 then (if i < 164 then (if i < 163 then 0x400100740010004001000400100040010000000a03 else 0x7c01f007c01f007c01f007c01f007c01f007c01f007c01f090800040002010e07) else (if i < 165 then 0x24009002400900240090024009000000000804 else 0x101)) else (if i < 168 then (if i < 167 then 0x4001000400100040010004001000000000804 else 0x1000101) else (if i < 169 then 0x24009002400900240090024009000000000804 else (if i < 170 then 0x2c00b002c00b002c00b002c00b002c00b000000000a04 else 0x1d007401d007401d007401d007401d000300000904)))))) else (if i < 188 then (if i < 179 then (if i < 175 then (if i < 173 then (if i < 172 then 0x24009002400900240090024009000000000804 else 0x24009002400900240090024009000000000804) else (if i < 174 then 0x24009002400900240090024009000000000804 else 0x2c00b002c00b002c00b002c00b002c00b002c00b002c001002c00b002c00b00000b02000908000005120a)) else (if i < 177 then (if i < 176 then 0x9000101 else 0x1401800000202) else (if i < 178 then 0x240090024009002400900240090024009000907000a04 else 0x242a000000202))) else (if i < 183 then (if i < 181 then (if i < 180 then 0x2c00b002c00b002c00b002c00b002c00b000907000a04 else 0x900240090024009002400900240090024009002401100240070c0804030100070f07) else (if i < 182 then 0x9000101 else 0x9000101)) else (if i < 185 then (if i < 184 then 0x2403000000202 else 0x101) else (if i < 186 then 0x7002401100240090024009002400900240090024009002400900060804000604000f08 else (if i < 187 then 0x24009002400900240090024009000000000804 else 0x1f00240090024009008c009002400900840090024009001c025002400900240090024009021111050103010f000b08150b))))) else (if i < 196 then (if i < 192 then (if i < 190 then (if i < 189 then 0x24009002400900240090024009000000000804 else 0xb002c00b002c00b002c00b002c00b002c00b002c00b002c00b0d020a0107000001000f09) else (if i < 191 then 0x7000101 else 0x1c0c000000202)) else (if i < 194 then (if i < 193 then 0x24009002400900240090024009000000000804 else 0x24009002400900240090024009000000000804) else (if i < 195 then 0x24009002400900240090024009000000000804 else 0x9002400900240090024009002400906000902))) else (if i < 200 then (if i < 198 then (if i < 197 then 0x90024009002400900240090024009000100000904 else 0x24009002400900240090024009000000000804) else (if i < 199 then 0x24009002400900240090024009000000000804 else 0x90024009002400900240090024009000300000904)) else (if i < 202 then (if i < 201 then 0x24009002400900240090024009000000000804 else 0x24009002400900240090024009000000000804) else (if i < 203 then 0x24009002400900240090024009000000000804 else (if i < 204 then 0x24009002400900240090024009000000000804 else 0x9002400b0024009002400900240090802000903))))))) else (if i < 239 then (if i < 222 then (if i < 213 then (if i < 209 then (if i < 207 then (if i < 206 then 0x24009002400900240090024009000000000804 else 0x90024009002c0090024009002400b002400900090705010b05) else (if i < 208 then 0x24009002400900240090024009000000000804 else 0xb002c00b002c00b002c00b002c00b06000902)) else (if i < 211 then (if i < 210 then 0x2c00b002c00b002c00b002c00b000000000804 else 0x24009002400900240090024009000000000804) else (if i < 212 then 0xb002c00b002c00b002c00b002c00b0802000903 else 0x2c00b002c00b002c00b002c00b002c00b000104000a04))) else (if i < 217 then (if i < 215 then (if i < 214 then 0xb002c00b002c013002c00b002c00b002c00b00090705010b05 else 0xb002c00b002c00b002c00b002c00b06000902) else (if i < 216 then 0xb002c00b007400b002c00b002c00b002c00b0001000505000b06 else 0x2c00b001400b002c01f002c00b002c00b002c00b002c00b00000004000808000e08)) else (if i < 219 then (if i < 218 then 0xb002c00b002c00b002c00b002c00b0802000903 else 0x2c00b002c00b002c00b002c00b002c00b000106000a04) else (if i < 220 then 0x2400900240090084009007c009008c009002400900240090024009000d0b00000000030003100a else (if i < 221 then 0x7c00b002c00b002c00b002c00b002c00b000504000a04 else 0x9400b002c00b002c00b002c00b002c00b0800050005030000000a09))))) else (if i < 230 then (if i < 226 then (if i < 224 then (if i < 223 then 0x2c00b002c00b002c00b002c00b000000000804 else 0xd002c00b002c00b002c00b002c00b006c00b0003030507000b06) else (if i < 225 then 0x3401d002c00b002c00b002c00b002c00b002c00b00000904000502000c08 else 0x6c00d002c00b002c00b002c00b002c00b002c00b0005070501000c06)) else (if i < 228 then (if i < 227 then 0x2c00b002c00b002c00b002c00b000000000804 else 0x2c00b002c00b002c00b002c00b002c00b00020705010a05) else (if i < 229 then 0xd002c00b002c00b002c00b002c00b006c00b0003030507000b06 else 0x2100240090024009002400900240090024009000404000b04))) else (if i < 234 then (if i < 232 then (if i < 231 then 0x90024009002400900240090024009000000000904 else 0xb002c00b009400b003400b002c009002c00b002c00b002c00b002c00b09000b0008051106) else (if i < 233 then 0x14005001400500140050014005009c005009c005001400500140050014005110d090104000400021209 else 0xb00240090024009090800900240090024009070701000501000b07)) else (if i < 236 then (if i < 235 then 0x23002c00b002c00b002c023002c00b000400b002c00b002c00b0b0306000808071007 else 0x700240090024009002401f0024009002400900240090024025090209040005010f07) else (if i < 237 then 0x7001c007001c0270014007001c007001c007001c007001c00707000b0503010f06 else (if i < 238 then 0x240090024009002c00900240090024009000807030100000a07 else 0x240090084009002400900240090024009002400900240090100010c01060e06)))))) else (if i < 256 then (if i < 247 then (if i < 243 then (if i < 241 then (if i < 240 then 0x24009002400d00240090024009002400903000005000a05 else 0xb08a001b002c00b002c00b002c00b002c00b003400b0005020501000d06) else (if i < 242 then 0xb003401b002c00b002c00b002c00b002c00b000709000b04 else 0xd007401d0074025007401d007401d007401d007401d0805000a0904060000000d0a)) else (if i < 245 then (if i < 244 then 0x5002c00300140010074112002c00b002c00b002c00b002c00b002c00b00030305000305001108 else 0x202000400b002c00b002c00b002c00b002c00b002c00b0106000208000d06) else (if i < 246 then 0xf0007401d009401d007401d001c00d007401d007401d007401d01000d060807000f07 else 0x24009002400900240090024009000000000804))) else (if i < 251 then (if i < 249 then (if i < 248 then 0x9002c0090024009002400900240090000040903 else 0x24009002400900240090024009000000000804) else (if i < 250 then 0x90024009002400900240090024009000600000904 else 0xb0074001002c00b002c00b002c00b002c00b002c00b002c00b0005050001000f06)) else (if i < 253 then (if i < 252 then 0xb0074001002c00b002c00b002c00b002c00b002c00b002c00b0005050001000f06 else 0xb002c00b002c00b002c00b002c00b002c00b007c00b002c00b002c00b000b0408000200001108) else (if i < 254 then 0x2c01f002c01f002c001002c00b007c00b002c00b002c00b002c00b002c00b002c00b000701061112000c091409 else (if i < 255 then 0xb002c00b002c0010074216002c00b002c00b002c00b002c00b002c00b00030305000305001108 else 0x2c00b002c00b002c00b002c00b002c00b002c00b002c00b0b0802030100000e07))))) else (if i < 265 then (if i < 260 then (if i < 258 then (if i < 257 then 0x24009002400900240090024009000000000804 else 0x24009002400900240090024009000000000804) else (if i < 259 then 0x2100240090024009002400900240090024009000404000b04 else 0x900840090998009002400900240090024009002400902000104000d05)) else (if i < 262 then (if i < 261 then 0x21002427e002400900240090024009002400900240090102000c08060402040d09 else 0x7c00b002c001002c00b002c00b002c00b002c00b002c00b002c00b002c00b08000006040a010c051209) else (if i < 263 then 0x9002400900240090024009002400902000902 else (if i < 264 then 0x9000101 else 0x90024009002400900240090024009002c009002c009002c0090024009002400910000f0a000a041307)))) else (if i < 269 then (if i < 267 then (if i < 266 then 0x24009002400900240090024009000000000804 else 0x9000101) else (if i < 268 then 0x9000101 else 0x9000101)) else (if i < 271 then (if i < 270 then 0xb000101 else 0xb000101) else (if i < 272 then 0xb000101 else (if i < 273 then 0xb000101 else 0x9000101))))))))) else (if i < 411 then (if i < 342 then (if i < 308 then (if i < 291 then (if i < 282 then (if i < 278 then (if i < 276 then (if i < 275 then 0x9000101 else 0xb000101) else (if i < 277 then 0x9000101 else 0x9000101)) else (if i < 280 then (if i < 279 then 0x9000101 else 0x9000101) else (if i < 281 then 0x2419a00000202 else 0x9000101))) else (if i < 286 then (if i < 284 then (if i < 283 then 0x241b000000202 else 0xb002c00b002c00100742bc002c00b002c00b002c00b002c00b002c00b00030305000305001108) else (if i < 285 then 0xb000101 else 0xb000101)) else (if i < 288 then (if i < 287 then 0x2428800000202 else 0x101) else (if i < 289 then 0x7081c207081c207081c200091c20708020300000000000907 else (if i < 290 then 0x24009002400b00240093a20e883a2000900240090024009002400900240090024009002400900240093a200090024009002400b3a200093a200090024e8800240090024e88002400916270024192400081d1402081a121917071f0002012a15 else 0x15900025590564159056415905641590020700000004000907))))) else (if i < 299 then (if i < 295 then (if i < 293 then (if i < 292 then 0x24009002400b00240093ff8ea64e6000900240090024009002400900240090024009002400900240093a200090024009002400b3a200093a200090024ea200240090025002002400916270024192400081d1402081a121917071f0002012a15 else 0x90024009002400b00240093ef0eec3a2000900240090024009002400900240090024009002400900240093b400090024009002400b3a200093ed00090024ed800240090024e88002400916282624192400081d1402081a121917071f0002012b15) else (if i < 294 then 0x24009002400b00240093a20f1e3a2000900240090024009002400900240090024009002400900240093c000090024009002400b52500093f300090024f1a00240090024e88002400916270024192400081d1402081a121917071f0002012a15 else 0x24009002400900240093a200090024009002504400240093a2000900240090024009002400900240090024009002c00b00240093a2000900240090802001b0c1f141f0018020d09140300040f2212)) else (if i < 297 then (if i < 296 then 0x24009002400900240093a2000900240090024e88002400955b000900240090024009002400900240090024009002c00b00240093a2000900240090802001b0c1f141f0018020d09140300040f2212 else 0x900240090024009002c0093dd0f344ec0009002c0090024009002400900240090024009002400900240093a200090024009002400b4fd80093a200090024eba00240090024e88002400916250022192300081d1417082012192007230002012b15) else (if i < 298 then 0x24009002400b002400940b8f4c4f2000900240090024009002400900240090024009002400900240093de0009002400900240293a200093a200090024e8800240090024fa2002400916270024192400081d1402081a121917071f0002012a15 else 0x70820080001fe07080000009000000000200000707))) else (if i < 303 then (if i < 301 then (if i < 300 then 0x923b870c006070c000082e0103000703 else 0x301c587c400000091c58d9e00000000000705) else (if i < 302 then 0x71400247ae00007a40201000503 else 0x90024e88002400941780090024009002400900240290024e880024009002400900240090024009002400901e00090024009002400b002400941880090024009000d01171320161c011903001e112401022511)) else (if i < 305 then (if i < 304 then 0x9002505e00240094178009002400900240090024029002505e0024009002400900240090024009002400902400090024009002401f002400949c00090024009000d01171320161c011903001e112401022511 else 0x900240094918009002400901e000900240090024009001c009002400901e00090024009002400900240090024009002400900240090024009003c0090044009002400f48f0009002400908270100241a000419090d171c1e162b0f) else (if i < 306 then 0x58a8009564159058800a802020000000605 else (if i < 307 then 0x900240090044009002400900240090024009001c009002400900240090024009002400900740780024009002401b0024009003c078002401d002400900240091c0023180a0a110013011306120400250f else 0x15e657a959c00000090003020503)))))) else (if i < 325 then (if i < 316 then (if i < 312 then (if i < 310 then (if i < 309 then 0x1e007801e0078002400f000003a01e00780024009026800902a0009003c00900440900044e4e003c01100240185b5000f0024009002400f004400901e00090024060002400900240090024009002400f012000900240300024009002401100240090024009002401101e00090044022002400900240090024009003c009003c009002400f003c00f01e000900240090024009003c00900240090024009007400901e0009352c453b422f2721001e50010e4f3d0f2a56585a1c43525c5e18 else 0x24009002400b0024e88002400900240090024009002c00900240090024009002400900240093a20009002400900240093a200090024009020001110e050f13051819001e0e1f01002011) else (if i < 311 then 0x1c200c0002470800000100000505 else 0xd81c5871600000090002000503)) else (if i < 314 then (if i < 313 then 0x2471400000202 else 0x108002400900240090024009002400b002400900240090024009002400900240090024e88002c0090024009002ce88002400900240090024009001d141b0313110702031a0401210d) else (if i < 315 then 0x2400b002c00b002c00b002c009002c00b002c00b002c00b002c00b002c009002c009002400b002c009002c00b042000b002c01f002c00b002c108002c00b0a050000110c00001414030f011a1c10191c1a1f002415 else 0x70a1c2800900001200100000503))) else (if i < 320 then (if i < 318 then (if i < 317 then 0x1590564000900001380100000503 else 0x159c567000900001500100000503) else (if i < 319 then 0x42000900240c005400c6345010804212b40360009002400b0024009002d254002c00b002c00b002410804200090024009002400b042000904200090024138002400900240090024009002400b03c000900241080024009002401d002400900240090024009002c009002c10800240090024009002400b002400b002400b002c00900a4009048000900240090024009002400900240090024009002400904200093551453b422f211e000f27010e38485b2a5759431c554f535c18 else 0x2c00900240090024009002400900240090024009002400900240090024009002400905a0e8800240090024009002c0090025062002c00900240091b1f0d190d01050a12100e050300220e)) else (if i < 322 then (if i < 321 then 0xb002c00b002c00b002400b002c01d002ce88007c00b002c00b002c00b002d0f4002400b002c009002400b002c00b002400b002c009002400b1a080c06001d0020161c10020012210e else 0xb236070a1c2818000040000000505) else (if i < 323 then 0x9002400900240090024009066000b00240090024009002401d00240090024009002400900240090024009002400901150b081407090002040700001b0d else (if i < 324 then 0x90024009002400b00240090024009002400900240090024009002400900240fe0024009002400b0024009002400901180f000713110e02040900001b0d else 0x1c2000006c000900007080100000703))))) else (if i < 333 then (if i < 329 then (if i < 327 then (if i < 326 then 0xb0024009002400b00240090024009002c0090024e88002400900240090024009002c0090024009002c009002400b0024009002400900240090a041d03001700000002100102090f210f else 0x24e880024009002400900240090024009002505c0024009002400b00250624778009002400900240090024029073800900241c800240090024009002400b002400900240090613000e09071e0102001513221e2710112811) else (if i < 328 then 0x9f024008401fa8a981c207082580000078000b0000000000010006070b09 else 0x10004001000420c00040010004001000400100040010f1000100040010870001000400100040010004ab0081000100040010004001000401d1150001007c00100040010004001231f031a000224140c13091504290d)) else (if i < 331 then (if i < 330 then 0x72420500002058726002c70c28f09c400020500010905 else 0x1002c00b002401d002c00b3a2000b002d0a4002c00b0025098002c01f08a000b002400b002c00b002c00b002540442b000b002c009428000b0074009002c00b002ce88002400b002c00b002400b002d3f8002c009002c00b2e01000e1e1504211b29161a29001f152231002f0a083316) else (if i < 332 then 0x1002c00b002c01d002c00b426000b002d350002c00b002d098002c01f090000b002c00b002c00b002c00b002d46c4bd800b002c00b4b0800b007400b002c00b002d098002c00b002c00b002c00b002d410002c00b002c00b2e01000e1e1504211b29161a29001f152231002f0a083316 else 0xb002c00b002c00b005400b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c015002c00b08a000b002c00b007c00b002c00b002c01508a000b002d428002c00b002c00b180105160e051b00150b001c150000250d23002601292b16))) else (if i < 337 then (if i < 335 then (if i < 334 then 0x2c01f002c00b002c00b002c00b510001f002c00b002c00b002c00b007c00b001400b002c00b002c001002c00b002c00b007c00b002c00b555800b4b7800b002c00b1f170722150f0a1a1b0804000000260e else 0x1002c00b002c01d002c00b4fe000b002d460002c00b002d410002c01f096000b002c00b002c00b002c00b002d710516000b002c00b506000b007400b002c00b002d3f8002c00b002c00b002c00b002d3f8002c00b002c00b2e01000e1e1504211b29161a29001f152231002f0a083316) else (if i < 336 then 0x5ca000b57c159058f963c57e02705ad15900000030006000001010a09 else 0x8a024808a0e7408a024c0780228090019a08a000b095000b08a000b07b001507a000b002c00b002c00b002c015002c228005400b002c00b002c258002c1f4005400b002c228005400b002c228002c0150054015099000b09f000b0054015002c015002c00b002c00b002c00b005400b002c015002c015002c015002c015005400b002c00b002c015002c228005400b002c015005400b002c270002c00b002c00b002c00b005400b1644123c205b4a4f40381e4d2c510208365f2e2d0c58425c0055601a)) else (if i < 339 then (if i < 338 then 0xb002c01d002c00b002d0a40024009002c009002c00b002c00b0024009002c00b002400b002c00b3a2000b002c009002400b0024001002c01f002c288002c01d0b18101e10080c221817001510100b0a00012512 else 0x2401f002400b007c01f007c01f004c01f002401f0054009007d1040b40019002402d007c01f002401f007c00b002c01b007d10c007c01f002401f002401f00ad404007c01f3a2001f007c00919260f0e0b0d1024161702131d270f0004022c12) else (if i < 340 then 0x2400b002400900240090024009002400900240090024009002400900240090024e8800240090024009002400b00240090024009161a08060d03000011000d0d00061e0e else (if i < 341 then 0xb002400b002c00b002c00b002400b002c009002400b002c00b002c00b00740090024e88002400b002c00b002400b002c00b002c00b181c0e060e0000001e190d0d00061f0e else 0xb564000056402e800000000000505))))))) else (if i < 376 then (if i < 359 then (if i < 350 then (if i < 346 then (if i < 344 then (if i < 343 then 0x5400240090024009002400b002400900240090024009002516400240090024009002400b0024009002401d002400900240090218051212080d0403000406001d0d else 0xc607081c2000000240000000000000000606) else (if i < 345 then 0x24009002400900240090024e88002400900240090024009002400b002400900240090024029002400900240090024009002400901010010031a021517030b0812101d00001e11 else 0x8621c20a801c2085828207380d20742002c000010300010000000b07)) else (if i < 348 then (if i < 347 then 0x33d83601e1891e1c3070c289800b1db08760000030100000001010a09 else 0x365037823307641c58716263000b25108960000030100000001010a09) else (if i < 349 then 0x7d41c5000b1f788b6255000026708ac020300000003000907 else 0xb002c00b002400b403800b002c00b002d00a002c009002c00b3f98009002c009002c00b006c00b002400b002c00d52c0e88002400b002c00b006c3d8002c00b45c0fea002c00b3a20009002c009002c01b06230a101e27061c00220f141b2d1b220200152f13))) else (if i < 354 then (if i < 352 then (if i < 351 then 0xb002c00b002c00b47a000b002c00b002d1f2002c00b002c00b4c2000b002c00b002c00b006c00b002c00b002c00d5381170002c00b002c00b006c3f0002c00b45c1312002c00b45c000b002c00b002c01b06230a101e27061c00220f141b2d1b220200152f13 else 0xb002c00b002400b403800b002c00b002d21c002c009002c00b4c80009002c009002c00b006c00b002400b002c00d53e100e002400b002c00b006c408002c00b47a136e002c00b4038009002c009002c01b06230a101e27061c00220f141b2d1b220200152f13) else (if i < 353 then 0xb002c00b002c00b4c8000b002c00b002d36a002c00b002c00b3f9800b002c00b002c00b006c00b002c00b002c00d5330fe6002c00b002c00b006c420002c00b4c21210002c00b3f9800b002c00b002c01b06230a101e27061c00220f141b2d1b220200152f13 else 0x6c01b007401b006d286006c01b006c01b006c01b002528a001c01b006c390003401b007538c4d3801d002401b006c01b006d344006c01b006c01b006c01b006c01b03001c11040c1600011c00000c1b161a0501020e002615)) else (if i < 356 then (if i < 355 then 0x2c00b002c00b002c00b002d2a6002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b007400d002c0294a7000b002c00b002c01d0f6000b0f6000b002c00b002c00b002c00b2b00022503250d20001d180b0c181a120200200f2a2c15 else 0x51c800b002c00b006c01b002c01b002c00b002c01b002c00b002c01b002c00b002c00b0f6000b002c00b002c00b002c00b002c00b002c00b002c00b002c3d8002c00b002c00b05002417190b000c1106051c120112280f) else (if i < 357 then 0x165a570800b59415c658200005d01590020300000003000907 else (if i < 358 then 0xd8000b006c00b0f603d80fc03d810203d80f6043810803a8002c37810a83485bf001b006c382002c3d8002c00b104800b0f6036a006c00b006c00b006c00b002c01b002c01b006c00b002c01b002c00b002c01b002c00b002c01b002c00b002c3d8002c00b002c468007401d002c00b002c00b0f6000b002c00b002c00b006c01b002c00b002c00b007401b0f6000b002c01b006c00b002c00b002c00b002c01b006c00b002c00b185f5e58235019482e522f2841420d0f352437430c4a5155004d5c5a601c else 0xb002c00b002c00b53e000b002c00b002d4fc002c00b002c00b533000b002c00b002c00b006c00b002c00b002c00d52c14b0002c00b002c00b006c438002c00b53814c8002c00b52c000b002c00b002c01b06230a101e27061c00220f141b2d1b220200152f13))))) else (if i < 367 then (if i < 363 then (if i < 361 then (if i < 360 then 0x5aa159c56e846856715b6002d6925a396ee0000020001020100000a09 else 0x1b006c01b006c01b423801b002c009006c01b3a2001b52c001b1200009006c01b006c009002c01b006c009006c01b002400b002401b00a400b002401b4248029006c0090c08001f120f1a24001d02120a0d030016152712) else (if i < 362 then 0x2c00b006c01b002c498002c01b002c00b0024009002400b002c00b002c00b002c009002c009002ce88006c009002c00b002400b0024fea002c00b002c00b1c160a190f120502131306050400240e else 0x12c00091c207080100000603)) else (if i < 365 then (if i < 364 then 0x7c0090024009002c009002400900240090024009002400900240090024e880024009002400b0024009002c009002400900240090003000f03190a12150116021c0e1d00011e11 else 0x70800004c800247080002000000000606) else (if i < 366 then 0x2470c1c304e00000000503 else 0x2471400000202))) else (if i < 371 then (if i < 369 then (if i < 368 then 0x93a2000900240090024009002400b00240090024510002400900240090024e8800240090024009002c009002400900240090024009002400902160f19190011050502040300210d else 0x2c009002400900240090024009002400900240090024009002400900240090024510002c00900240090024009002451000240090024009002400917002014110200060f011704190807220f) else (if i < 370 then 0x137051014404e036e05101440009002c4c813d0009002c00900240090024510002c02913e0009002400b0024009002400914400090024009002453c0024009002400b002400900240091440009002451000240090024009002c00b002400b002400914a000b00245100024009002401d0024009002c009002c00b002400b002c00b144000900240090024009002c009002400b002400b0024009002400935594a4842453b2f0021271e0e38010f2a4f51531c5543575a18 else 0x9564159000005280002010503)) else (if i < 373 then (if i < 372 then 0x240090024009002400900240090024009002c009002c009002c0090024e88002400900240090024009002400900240090024009001c13041706080f03010400011e0d else 0x2c00b002401b002400b002c00b006ce88002400b150000b006c00b402800b002c00b002401b002c009002c009002c009002c00b002c009002c00b002c00b0d0200130e051922000001111511000c0a012412) else (if i < 374 then 0x240090024009002400b002400900240090024009002400900240090024e8800240090024009002c009002400900240090024009001a04181502110302030607011e0d else (if i < 375 then 0x90024009002400900240090024009002400900245000024009002c009002c009002400900240090024009002400918100110061106060003031b0b else 0x90024009002400900243b40024009002400900240090024009002400900240090024009002c00b002400900240090019000c0116010b0e0c090612011901031b11)))))) else (if i < 393 then (if i < 384 then (if i < 380 then (if i < 378 then (if i < 377 then 0xb1c2070800005b80000020503 else 0x93a2000b002400b002c00b002c01d002c00b002400b002c029002c00b002c00b002c00b002c009002c00b0024029002c00b002c00900001905000909001706170800140d1f0f) else (if i < 379 then 0x91c20708000301 else 0x7081c2000b0002000303)) else (if i < 382 then (if i < 381 then 0x2a01c2070800241880102000503 else 0x17a0618180061818c0618192061819806181c2061818186181c3061800001002) else (if i < 383 then 0x9000101 else 0x1c206781c200090002010403))) else (if i < 388 then (if i < 386 then (if i < 385 then 0x9000101 else 0x17a0690185869018086901aa06901af06901c2069017e06901c5869000001002) else (if i < 387 then 0x708002470800000402 else 0x7081c2000000243180100000503)) else (if i < 390 then (if i < 389 then 0x6c0007800b1c207080203000503 else 0xb1c20708000301) else (if i < 391 then 0xd9800b1c20708000501 else (if i < 392 then 0x70816e070800000090000000503 else 0x1c206781c200290002010403))))) else (if i < 402 then (if i < 397 then (if i < 395 then (if i < 394 then 0x708002470800000402 else 0x1c204e6002c7080100000503) else (if i < 396 then 0x1ba1c2070800000090000000503 else 0xe307081c200090002010403)) else (if i < 399 then (if i < 398 then 0x7081768708011000b02000000000505 else 0xb000101) else (if i < 400 then 0x18006d818586d81c206d818286d826a06d826d06d818306d81c506d800001002 else (if i < 401 then 0x7081c200090002000303 else 0x1c204b01c200090000000503)))) else (if i < 406 then (if i < 404 then (if i < 403 then 0x1c2000b1c200c00200000503 else 0x5581c200001c200090001000503) else (if i < 405 then 0x708000000b0d20708000501 else 0x70813200001c200090000000503)) else (if i < 408 then (if i < 407 then 0x9000101 else 0x9000101) else (if i < 409 then 0x7081c20000049000b0000000503 else (if i < 410 then 0x918607081a407081b607081868708276070829407081a687083a207080f001102 else 0x1e01c2000b1c20000000501)))))))) else (if i < 480 then (if i < 445 then (if i < 428 then (if i < 419 then (if i < 415 then (if i < 413 then (if i < 412 then 0x70803a070800240000100000503 else 0x2400900240090024009002400900240090024009002c0090024009002400b002400900240090024009002400913170313000e000a0901011000001a0e) else (if i < 414 then 0x2470800000202 else 0x2c70800000202)) else (if i < 417 then (if i < 416 then 0x2470800000202 else 0x2470800000202) else (if i < 418 then 0x6f01c2001d0000000403 else 0x7081c207081c207081c200091c20708000200000904))) else (if i < 423 then (if i < 421 then (if i < 420 then 0x19209d81aa09d81c209d826a09d819289d829a09d81ac89d856409d800001002 else 0x9000101) else (if i < 422 then 0x1980a501af0a501c20a5026d0a501988a5029a0a501ae0a505670a5000001002 else 0x9000101)) else (if i < 425 then (if i < 424 then 0x2c00b002c001002c00b002401f002c00b002c001002c00b002c00b42c0001002c00b0004009002400b0004009002caf8543000b002c01d002c00b0024b584370ab0002c00b42e000b002c001002d174002d0d4007400b007400b002d3f8002c00b002c00b002400b002c01d007ce88002c00b32010014311a310b35001c0f230837222824003b223f4216 else 0x740010004001000400100040012ac0001000402f000400100040012ac000100040010004001000400100040010004001000400100040010004ab0000400100040700004001000400b000401d00bc001000400100111e182400001f251b230b00052c12001d001b1a183016) else (if i < 426 then 0x1bd00012ac0ac82ac0ae0007c01d0004b102ac0ab01b50b302ca0b4000046cc2e205d039a001d0004ab00004ab000040012b4000100045d8007400100740010004001007c001000401f0e80001002c001000400100040012e80001000401d00040010004ab0000401f0004b18007401d00040010004001000401d007c0310004001007401d0004001000400100040012dc00012ac0001007401f000401f0004001007c001000401f00040011861605f2355514a2e5043284142190d350f1d480c2f5b5d004d5956621c else (if i < 427 then 0x9002c009002c00b002c00b002c0093a20009002c009002400b002c00b002c00b002c00b0074001002c00b002c00b002400b002c00b002c00b002c00b080113011e060c1c121f0020140b011606002312 else 0xb56700005670c0000000000000505))))) else (if i < 436 then (if i < 432 then (if i < 430 then (if i < 429 then 0x240090024009002400900240090024009002400900240090024009007400900240090024009002c0093a20009002400900240091c050311131b190e0200081e0b else 0x1d002401d002401d006c009007401d002c00b002401d0075098005401d0074c60002401d007c009007c01d007400b002401d007401d00740090074e880074009001b0c070b05130d001f1413142108120000072513) else (if i < 431 then 0x240090024009002400900240090024009002c009002400900240090024009002400900a400900240093a2000900240090024009021c1016140e020f01021000001e0d else 0xb002c00b002400b002c00b002c009002c00b002400b002c00b002c0093a2000b002c00b002c00b002400b3a2000b002c009000c1c0300070100001410080017071d0f)) else (if i < 434 then (if i < 433 then 0x1590002d5900000020303 else 0x159c002d59c0000020303) else (if i < 435 then 0x24009002400b002c00b002400b002400b002c00b002c00b003c009002c00b3a2000b002c00b002d062002c009002c00b002c00b002400b002c009002c00b002400b002c009002c009002c00b002c00b14051516150721201e27171b140f07180600022e13 else 0x3f91188000400b002c00b007400b002cfea002c00b002d526002c01d002400900a400b4478009002c00b44a800b002c00b002400b002c00b002c00b002c00b002c00b002c00b002d18e002c009002ccd8002c00d3378e88002c00b002c00b0f0216050a002025272a001e1a012b0a1217262a282d3616))) else (if i < 440 then (if i < 438 then (if i < 437 then 0x2c00d002c00b006c00b002c00b002c00b002c00b002c00b007400b002c009002c00b002c00b0024fea002c00b002400b002c00b002400b002c00b002c009002c00b002c00b002c01b002ce88002c00b006c00b04251f150724120e1507021d010a00300f else 0xb002c00b002c009002c009002c00b002c00b002c00b002c00b002c009002400b002c00b002400b3a20009002c00b002c009002c00b002c00b002c0090621121f1a0e130001070312001d230e) else (if i < 439 then 0x900240090024009002c00900242b8002400b00240090024009002400900240090024009002400900240090024e8800240090024009030115130000050c0c0d1007081f0d else 0xb00240090024009002400900240093420009002400b0024009002400900240090024009002400900240090024009110c0409000003121405121b0b)) else (if i < 442 then (if i < 441 then 0x400b002c00b002c00b002400b002c00b002400b002c00b002400b002c00b002400b002400b002400b002c009002ce88002400b002c00b1e0f1804000003100c15100602200d else 0x900240090024009002c00900240093a20009002400900240090024009002400900240090024009002c00b34800093a20009002400900240090012081f00180311000a0803001501002110) else (if i < 443 then 0x900240090024009002c0090024d200024009002400900240090024009002400900240090024009002400900a40090024d2000240090024009002400902021b050a03140b161b190a011f1706002311 else (if i < 444 then 0x2559000000202 else 0x1a18d20348067c1a20d20348000900246785d60009002400900ac0090094d2000240211a10009002c00b0024009002400b00240093480009002467a00240090024009002c009002401b3480009007cd38002400900240253480009002c009002c01d348000b002c00900240090024009002c00900240090024009002c00900a400b348000900240090024009002400900240090024009002400900a400935594a4842453d3b00381e270e2c010f2a4f51531c5543575a18)))))) else (if i < 462 then (if i < 453 then (if i < 449 then (if i < 447 then (if i < 446 then 0x240090024e88002c0090024009002400900240090024009002400900240090024029002402900240090024009002400900240090015001400110103000800001e0c else 0x2c00b3a2000b002c00935414b0002c009006c00b002400b002c00b006c009002c00b0024009002c009002c00b002c009002c00b002c01b002c00b1911210a081d20140c150100020200220f) else (if i < 448 then 0x2400b002c00b002c00b002c00b002c00b002c00b002400b002400b002c00b002c00b002c00b002400b002c009002c00b002c0090024e88002c00b002c00b0b1b15110a0b000d0500181c0001240e else 0x2100240090024009002400900a40090024009002400946d0009002400b0024009002400935b8009002400900240090024e884530009002c0090024009002400900250182513080e1d131a001a141d170e0006131e040c2713)) else (if i < 451 then (if i < 450 then 0x2c009002c00b002c00b002c009002c00b0024e88002c00b0024009002c00b002400b002c00b406000b002c009002400b002c009002c00b002c00b002c009002c00b002400b002c00b002c00b002c0091a210915170b15002127001f22280a1400022e12 else 0x90024009002400900240090024009002400900240090024009002400b0024009002400b00240090024e880024009002400900180b0a15140606090201000801001d0f) else (if i < 452 then 0x90024009002400900240090024009002401d0024db0002400900240090024009002400900240090024009002400b111204190003000a01041b0a else 0x2c00b002c00b002400b002400b002c00b002c00b002c009002c009002400b002c00b002c00b002400b002c00b002c009002ce88002c00b002c00b10011a030000141808081d0f0f220d))) else (if i < 457 then (if i < 455 then (if i < 454 then 0x24009002c009002400900251c40024009002400900240090024009002400900240090024009002400900251c6002d1c80024009002400900a4e8800240090024009181400151306130c0d0008011220120708212612 else 0x166c002566a5641668372159000000100010705) else (if i < 456 then 0x240093a2000900a507c0024009007c00900240090025180002400900240090024009002400b0024009008c00900250740024009379000900240090024009002400b00240091711232200011814200f100604071d12012000231e2815 else 0xb002c00b00240092af000b002c00b002c00b002400b002c00b002c009002c00b002c00b002c00b002c00b002c00b084000b002c00b0024009002c00b0024009460000b002c009002c00b0024009002c00b0024e88002c00b172100271200161e180b1f00000823270b2b242f081f3316)) else (if i < 459 then (if i < 458 then 0x93a20009002400900a400900240093a2000900240090024009002400b0024009002400900240090024009002400900240090d0f151402171003020b000800001d0e else 0x159000255900100000303) else (if i < 460 then 0x24009002c009002400900240090024009002400900240090024009002400900a4009002400900240090025254002401f00240290024e880024009002400900240090203190e1a0d1b111c1f1f0a07021920002611 else (if i < 461 then 0x33007c00b004c01b002401f007cabc007c00900743d0007c015007c00b0024009007c0093a2001f002c009007c01f00ac009002401f002c01f007c01f007c01f007c00b002401f002c01d007c035007c01f007c01f501000b007c01f007c01f031f071c24240b27002a2906202c062b1e0b003017171d1e220012371b else 0x9006c01b006c00b006c01b006c009002c01b006c01b002c01b00254b0006c01b002401b002401b00a401b002401b3a20009002c00b006c01b006c01b006c01b006c00b00a4009006c00b006c00b1f0b0028230d131d081803000f20172400032d12))))) else (if i < 471 then (if i < 466 then (if i < 464 then (if i < 463 then 0x240090024009002400b0024009002400900240090024009002400900240090024e8800240090024009002402900a4009002400900240090024009181c02160d09001b03190b00021301220f else 0x900240090024009002400900240090024009002400900240090024009002c0090024e8800740090024009002400900240091a0d0c010303170c00000f1d0b) else (if i < 465 then 0xb002c00b002c00b002c00b0024e88002c009002400b002c00b002400b002c00b002c00b002c0092af000b002c00b002c00b002c00b01f000b002c0093a2000b002c00b002c00b002400b1a250d1b161e0a01112120080003072605002b12 else 0x15902eb000b56400ac000200000504)) else (if i < 468 then (if i < 467 then 0x9002400900240090024009007400900240090024009002400900240090024009002400b0024e88002400900240090024009081a011505010014000a09101203031d0f else 0x240090024009002400b002c00900240090024009002400900240090024009002400900240090024e88002400900a40090024009002400900240091719011c0d05001a14020214090305220f) else (if i < 469 then 0x2400b002c00b002400b002c00b002c00b390000b002400b002c00b002c00b002c00b002400b002c00b0024e88002c00b002c00b002c00b002c00b002c00b1a0800061f1501000010021d180520240f else (if i < 470 then 0xb002c01d00a4009002c00b002c00b007400b002400b002c00b002c00b002c00b002ce88002d2b4002400b002c00b002c00b002400b002c00b002400b18210703081806020106000e0400230e else 0x2c00b002c009002c00b002400b002c00b3a2000b002c009002c00b002c009002c00b002c00b002c00b002400b002400b002400b3a203dc002c00b002c00b0b220020011e09000213121609000001000f2412)))) else (if i < 475 then (if i < 473 then (if i < 472 then 0xe88006c009002c02f008402900a4e883480025002402900a4025007402900ac00b002400b00a402500a400b0074029002c00900a401f00a400900a4029002402900a4021060b021f1e18052000030f17180011270f else 0x2400b002c00b002ce88002ce88002c009002c00b002400b2f7000b002400b002c00b002400b002ce88002c009002c00b002c00b002c00b002c00b002c00b002400b1603081900211d1c0617030014260d) else (if i < 474 then 0x2c009002400b002c00b3a2000b002c00b002c00b002c00b0024009002c00b002400b002400b002c00b002c00b002400b002400b002c00b42a000b002c009002c009002c00b002c009002400b002c00b03160905212220000701281b1f00002e0f else 0xb002ce880024009002c00b002c00b002400b002c00b002c009002c009002c00b002400b002c00b002c00b002c00b002c00b002c009002c00b200004171b130f150012010108210d)) else (if i < 477 then (if i < 476 then 0xb002c00b002400b002400b002c00b3a2000b002c00b002c0090024009002c00b002400b002c00b002c00b002c00b002c00b002c009002c0091e0004101c1313150507010106210d else 0xb002400b002c00b002c00b002c00b3a2000b002c00b002c00b002c00b002c0090024e88002400b002c5160024009002c00b002c00b002c00b002c00b002400b0024091815180e1206000a050003250e) else (if i < 478 then 0x240092f3000b002c00b002c00b002c009002400b002400b002c00b002c00b002400b3a2000b002c00b3a2000b002ce88002c00b002c00b002c00b002c00b1401000c15000d11050220220a091e240f else (if i < 479 then 0x900240090024009002400900240092fb000937f0bf8002400900240090024e7000240092ff00090024009002c00b2fc0e0800240090024009002400900240090024009110019140e120023030618041d020d001c0f2712 else 0x9002400900240090024009002400900240090024009002c009002400900240093a2000b00240090024009002c00b00240090024009007c0090024009021100130b100f0b0d000d0413020d001b1c2312))))))) else (if i < 514 then (if i < 497 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then 0x2c009002c00b002400b002c009002c00b002c00b002c00b002c00b00240093a20009002c009002c00b002c00b002c00b0024009002c00b002c00b0818101f0608050e0002160602220d else 0xe88002400b002c009002c00b002400b002400b007400b002c009002c00d002c00b002400b002c00b002ce88042000b002c009002c00b002c009002c009002c00b002c00b002c00b1d000717161b13050e020e14000805290f) else (if i < 483 then 0xb0024009002ce88002c00b002400b3210c8a002c009002c00b002c00b002400b002ce88002c00b002c00b3a20009002c00b002c00b002c00b002c00b002400b002c0091a1d0b18140523020e030817000816270f else 0x240090024e880024009002400900240090024e88002400900240093a20009002c009002400900240090024009002400b002400900240091212090d180210090600080b000600200f)) else (if i < 486 then (if i < 485 then 0x900240090024009002c009002400900240090024009002c0090024d38002400900a40090024009002400900240090c0a19060907040801030e00001b0d else 0xb002c00b002c00b3a20009002c009002c00b3a2001d0024009002400b002ce88002400b002c009002c00b002c00b002400b002c00b002c00b002c00b2007001d14031e120317050d000a01230f) else (if i < 487 then 0x240090024009002c00900240090024009002400b0024009002400900240090024009002c009002400900240090004080a00070406000018001a0c else 0x900240090024009002400b00240090024009002c009002c00b3a20009002400900240090024009002400900240090024009002c0090c0a15000a07040604060103001f0d))) else (if i < 492 then (if i < 490 then (if i < 489 then 0x900256c832700090024009002400b0024009002400b00240090024ca60024009002400900240090024009002400900240090024009080a00071905000a080705030b001f0e else 0x900240070024c260024009002400900240093090e880024009002c009002400b30a00090024009002c009002400b002400900240090024009002400915211d0f0c0007070e05050e00020a230f) else (if i < 491 then 0xcaa002400b0024009002400931500093168007002400900240093340009002400900256f800240090024cb0002400900240090024009002ce2800240090024009002400925130315221925030704010e000a21270f else 0x90024009002400900240090024009002400b0024009002ce880024009002c009002c00900240090024009002400900240090d06000b06080006040303030d001d0e)) else (if i < 494 then (if i < 493 then 0xb002401d002c00b002ce88002c037002c00b002c009002c00b002c00b002c00b3a2000b3a20009002c00b002c00b002c009387000b0024009002c00b002c00b002c009002400d002c00b00190e2a19211a1b0d090e0524181d000c072b12 else 0x90024009002c00b002400900240090024009002400900240090024009002400900240095d60009002400900240090d08080c0005001603000a090202071b0f) else (if i < 495 then 0xb0024009002c00b002c009002c00b3a2000b002400b002c00b08a0e88002c009002c00b002400b002c00b002400b002c00b002c009002c00b002c00b19080a00100003080b060c00112100160e01052313 else (if i < 496 then 0x24009002c009002c00b002c00b3a20009002c00b002c00b002400b3a2000b002400b002400b3a20009002c00b002c00b007400b002c00b002c00b002c00b1d0608001203000b0d050a00100021120e02022413 else 0x2c00900240090024009002400900240093a2000900240090024e880024e88002400900240090024009002400900240090024009002c009060e1d080a06140a0202110e0004031b0b2011))))) else (if i < 505 then (if i < 501 then (if i < 499 then (if i < 498 then 0x2d5905670e88002470a00247081c60e883a200090024e88002c00900240093a2000b002400b00240090074009002c009002400b00240093a20009002400b002400b002400b3a2000b002400b002400b00240090024009002c71600240090024009002c0093a2000900240290024009002400900240090024009002c0091c300091c5000900240090024009002400b002400b002400b0024009180f191d2324282f2e0d484a41525354355657450c555137004f424d581c else 0x240090024e88002400900240093a200093a2000900240090024e8800240093a200090024e88002c009002c0090024009002400900240093a200090024009002400900240093a20009060a1d23120b201a030c1014080e2926002a11) else (if i < 500 then 0xfd83f601f822107ce21a0fd83f6000900245aa59800090024009002c009002cfd8002400b0024009002c00b0024009002400b3f600091d48009002529600240090024009002c009002400b56a0009002c0090024009002402549e0009002c009002c00b3f6000b002c92400240090024009002c00900240090024009002c00900d400b3f60009002400900240090024009002400900240090024009002c00935574a48421e453d003b2c210e2f010f2a4f51531c5543595b18 else 0x1008402073e22c1008402001d007c5925a5001d007c00b002c89c002c00b007400b402000b002c00b007401d002c00b4d2000b002c01f002c946002c00b007400b002c00b002c00b002c00b002d008002c00b007401d1da800b002c00b002c00b002c00b002d008002c01d007401f002c00b007c00b007c00b002c01f00d400b570000b002c00b007400b002c00b002c00b002c01f002c01f402001d354a484542382f2c0027211e0e0f3b012a4f51531c5543575918)) else (if i < 503 then (if i < 502 then 0x1050414079e2021050414001b006c30a58c001b006c00b002c83c002c00b006c00b414000b002c00b006c01b002c00b002c00b414001b002c7b2002c00b007400b002c00b002c00b002c00b002d050002c00b006c01d48d800b002c00b002c00b576000b002c8f4002c01b006c01b002c00b006c00b006c00b002c01b00a400b002c00b002c00b006c00b002c00b002c00b002c01b002c01b414001b354a4845421e3d3b00382f2c0e210f012a4f51531c5543575918 else 0x109842607262081098426001d007c57a592001d007c00b002c854002c00b007400b426000b002c00b007401d002c00b243000b002c01f002d098002c00b007400b002c00b002c00b1f8800b002d2e8002c00b007401d002c00b002c00b002c00b002c00b002d098002c01d007401f002c00b007c00b007c00b002c01f00d400b57c000b002c00b007400b002c00b002c00b002c01f002c01f426001d354a4845423d3b38002f211e0e0f27012a4f51531c5543575918) else (if i < 504 then 0x2c00b4260294007401d002c00b002c00b318000b002c00b002c01f002c00b002c005002c007002c00b002c00b002c00b002c00b002c00b1203061d1c00000903060e000b0105200f else 0x70024009002400b0024ce400240090024009002402f007c0090024025001c00900240090024fd800240090024009002400912a80090c0310001c06090414120d00001f0d))) else (if i < 509 then (if i < 507 then (if i < 506 then 0x414001d006c01d001c01d002c17a007401d009401d2c48025002c00700341d4007401d009401d006c01d0074025007401d007401d002c01d007401d009401d007401d0004080102080000010c150e24031d150b2611 else 0xb402000b002c00b002c544002c00b35f800b002c00b002c00b002c00b0034025002c00b002c00b002c00b00e400b007401d002c00b002c00b0a11091414070108010c000019210d) else (if i < 508 then 0x1170233001b006c3305aa0786232117045c117045c001b006c00b002d472002d38c006c00b002c00b255000b006c01b002c00b002c00b45c001b002cae2002c00b007400b002c00b002c00b582000b002c00b002c00b006c01d002c00b002c00b002c00b45c000b002d170002c01b006c01b002c00b006c00b006c00b002c01b00a400b1e0800b002c00b006c00b002c00b002c00b002c01b002c01b002c01b35592c3b42432721000f011e0e2f3d5a2a55574f1c5344515b18 else 0x95170007401d007401d37b001d007401d007401b0074afa0074007007401d007401d002c025006c01d007400b007401d007401d1c030012011401090700000a000d1e0e)) else (if i < 511 then (if i < 510 then 0xa044fe13f84fe13f85101428002c9605cd0b404fe001d007c9c4292001d007c00b002d54a002c9fc007400b512000b002c00b007401d002c00b554800b002c01f002c00b002c00b007400b002c00b002c00b4fe000b002c00b002c00b007401d118000b002c00b002c00b4fe000b002c968002c01d007401f002c00b007c00b007c00b002c01f00d400b54d000b002c00b007400b002c00b002c00b002c01f002c01f4fe001d355e575342483b2f001e2c210e0f38012a55515a1c4f435c5f18 else 0x2d59000000202) else (if i < 512 then 0xb007400b002c00b002c00b002c00b002d3f8002c00b002c2dc002c00b002c00b002c00b002c00b002c00b002c00b002cb58002c00b19000b0e000d02070004030a0f011f0e else (if i < 513 then 0xa557a5d394a00024992002497828c14a0528000900254a0006c0090024009528001f002401f0024009009400900bc009002401b0024009528000900240250024033002402b528001f002401f002401f00240090024009007ca1600240090024009007c00952800090024029002400900240090024009002400900a400925f800928d800900240090024009002401f0024021002401f0024009180f191d2324282f2e0d484a41525354355657450c555137004f424d581c else 0x21008402100a40211238035008402100840210084021008402152800210084021008400b00840210084021002402100240210084021357802100840210e02121f0c00000001170217040b00040d222312)))))) else (if i < 531 then (if i < 522 then (if i < 518 then (if i < 516 then (if i < 515 then 0xa559000000202 else 0x1590564000b000052e0100000503) else (if i < 517 then 0x47656400095640000000501 else 0x1590002cb740000000303)) else (if i < 520 then (if i < 519 then 0x1590000159004e000b0003000503 else 0x15905640009000301) else (if i < 521 then 0x56402ea00255900000000503 else 0x9564159030f8c4030f0dc80301000703))) else (if i < 526 then (if i < 524 then (if i < 523 then 0x564000930415900100000403 else 0x9000101) else (if i < 525 then 0x1590002c0005640270000501 else 0x58000956415900100000403)) else (if i < 528 then (if i < 527 then 0x92761590277159029795903a21590297159027695905dc1590298159007001102 else 0x15905641590564159056400095641590000700000904) else (if i < 529 then 0x29a177029b177029d97705641770567177029d177029a977029e177000001002 else (if i < 530 then 0x94b3018006c0150007c12000241e035a8f7005a0150002539805c811250181503dd004850281500250fd80024062024800943b81500360dba04a80294360db00024009054000900241980024009054000900240090024150002400904e01c80024025002401f009400905400f0007c1500024009002401f00240094e6015000241500024009002400900240090024009007c1080024009007c009038801f002400900ac150002400900240090024009006c009002400900240090024009002402900840290024009002400900bc0090024033007c029007c0090024009006c00900240090024009002401f1d00270014486d3e3132374627807f7a00516a3c0a7661704f5c645f575079743b658182458586598728 else 0x2a009602580a202b80024258030025845f8228096024002a13980960009024800b002d184096024601e91980024d680024009002400947a8009002c25840200c6002400935a81f843e02580024009002400b4e60009002c00909600090024009002c009002c009002c009002c2580024009002c0090024009002421600242d0002c00b00242580024009002400900240290024e3400240090024009002c00909d8009002c00900240090024009002400b0024270002c009002c21000240090024009002400b0024009002400b0024009002401d002400900240090024009002c009096000917182336223c69600c78574f387667735c7f72804c827081437e7d7a2d6c6f44002e5d018324))))) else (if i < 540 then (if i < 535 then (if i < 533 then (if i < 532 then 0x3f00ed11d44e603f010803f011a142410b14180ec03f012003f0002c45035d04740fc141040b03f0007d39803494c40fc14b80fc03f0013001d10e03f01070414104005835a000b10203cc45683c0110000b11703d845880c645b80c411300d0007400b002c00b002c00b5071166007401d002c00b002d020002c00b002c00b002c00b002c00b0ea000b002c00b002c00b002c00b002c01d002c01f002c00b002c0350ef001d002c01f002c444002c00b002c3f0002c00b007400b002c00b007400b002c3e4002c01d007400b002c00b0fc000b007c00b007401d002c00b002c00b002c01f002c00b002c01f007c01f002c00b002c01f002c00b002c00b007c00b002c01d116d5f88436d66544c47742e1a644f7936374e7e3d93661d00898581098d6c9023827d7655242d772c925b94952c else 0x5b8002c5a016e000b4f685b84f9858818286604e6064816e0f2c01e800b01f0fe403b001b16e000b5220dea16e0f28174059254405b801505581a4057003a000b018801b16e0de0002c5e84e606184f585b84f886a8002c00b002c00b180000b17c800b006c00b35a800b002c00b0f08fce006c01b002c00b002d038002c678002c00b002c5b8002c00b002c00b002c01b002c01b002c00b002c02916e001d002c01b002c630002c00b002c57a16e000b006c01b002c00b002d2f4002c01b002c01d002c00b002c01b002c00b16e000b006c01b002c00b002c00b002c01b002c00b002c01b006c01b002c00b002c01b002c00b002c00b006c00b002c01b1157745f5734526246706a7b236e497236888c8d3d8e8f90002e80440986678a1a607c834f746c2d2c267a1b912c) else (if i < 534 then 0x7681d9120e1da07c400240c21da00d61ec00d8002c00b1e607804e6076800247681d40e0c1da079403b0d780024df8002400900240094828009002c7684140208002400935a876841901f80024009002400b1da0009002c0091ce00090024009002c009002c009002c009002cf500024009002c009002400900247680024009002c00b0024720002400900240090024029002476800240090024009002c0091da0009002c0091cd00090024009002400b0025398002c009002c76800240090024009002400b0024009002400b00240090024025002400900240090024009002c0091d3000917363a3c224f69600c235718386f67705c8171824c79777f437e7d7b2d01765300445d2e8324 else 0x24c0c782488b5825e0c4822208b84e60b582d609fa1660b5804289d80840a382d609a827888702c4072a28a821a25a87202ac059c1ce8a422d6099a2ca0ac804d0a0821009482d608da04c0a1215c88aa03c0a800da899014a0a682940b880d80b7a0c70ae02d609f015d896022489002c083a82ae828c2be06f028808e8246032022e890a08e0b700ec8b401560a981cf89c004388a02340ba0180f191d2324282f2e0d484a41525354355657450c555137004f424d581c)) else (if i < 537 then (if i < 536 then 0x4ec025630c0ba02e80ba02e800092e8000b2e80c600f68bd00930c1830000002ee05ac2f68766297075c2fa0d762348ba021c0ba02450f441c208d62160f400024e10002400900240090c10009002cba01500378002c009390838243003080024009002400b3868009002c00941a000900240090024009002400b0024009002400b002c00900240090024009002400900a40090024009002c009002c009002c009002c1440024009002c00900240090024bc20024910002400b0024009002400b0024c90002c009002c00900240090024009002400b00240090024009002c009002401d002400900240090024009002c0090060009176f445e3f6a67700c6d5583227565865a7184874a8082852d1c188136245b6e00724b888c24 else 0x35a089035a09ee35a0d68002cd68007c00b007c00b002c5bc002c00b007c00b487000b007400b279801d007cd6800d4154007400b002d350007c01d002c00b35a1398366000b007c01f002c01d002c01d4e60d80002c00b096000b444000b002c00b2a1000b35a000b002c00b002c3f0002cbb0007476c002cd68002c01d007c00b002c00b002c25c468001d35a000b002c00b486000b222000b002c00b002c00b002c00b007400b1db9080002c01d002d1a8002c00b002c00b007cd6835a001d22000b1700331b355a5456575e66306a376b0a6c15011c3e3c6827475d6d47000100422c50496e26) else (if i < 538 then 0x8ea3a20e583a50e583ba0e584e600603960009396000b00248f6002400b0024e580024009002400900240090024e703f608ec0024e58002400b002400b0024009002400b00240090024009002c01d00a400b002400b0024009002c0090024009002c009002c0093be000939600090190009002400b00240090024e5823a00090024ef400248f8002ce7c4e60009002406c002ce580024009002c0093bb000901c000b00240090024e580024ea00024e58002c0090024ef6002c009002ceea002400900240090024e5800248f40024fe40024009002406e0024009002406200240094ce000b0121663213005d3b2a705366321e4e743a7e490e0a793e821c7c24810080447f12776d016f455836622e832a else (if i < 539 then 0x4e613982618fd8171108024d09884480e58054111e002511c3f6108400a50821718fd83f60fd8002401f002400900245c80024152002400900240090024009002400926100090084fd800ac0090024009002402f3f600253fc0fd8002401f007c00924c8009006c01f002401f3f60fd800240290024025007c009007c009002402944a0009002400900240090024009002400900240090024009002415424c129c00240090024009002401f00240090024009006c0330024fd83f6001f00240091e6b61592947204434351f3a403b5d6a4858566b0f12482e006656036e1c else 0xfd84201586007cce44e60cb44200ccc53d09684201080002cc28426000b1870184002c7f60ba07ee0bc1080002ced4420123046e15264e3000b420146a5200a46470000b52c12340791080450000b007c00b002d080002c00b148001f002c00b002d080002c00b06d0a4e007c00b002c00b002c00b4200960007d080002c03b002c01f002c00b5209080002d468007c01f007c00b002c01f002c00b00d539800bc00b007c00b35a000b002c00b002cacc002c00b007c00b002c00b002c00b002c00b007c00b002c00b002c00b002c00b002c00b00cc01f002c00b002c01f007c00b007c00b00cc00b002c00b002c033007c00b002c01f1d2c703114485f3e2728735c31686c6b0a50796200823774577d7f814f596646458a89853b7e7c548d28)))) else (if i < 544 then (if i < 542 then (if i < 541 then 0x3f9111020e14d045013982640ebc4440d682fe0ae44e611104440a2e19f06e04441110193111055b800b4e0124c4441452473911012f000b002d24820191c61b614e8002d450266000b007401d002c00b002c00b444000b002c00b007400b002c00b002c00b00ac01d002c00b00ac00b002c00b00ac01d002c00b002c00b002c00b002c00b203800b007402b002c00b002c00b18d000b00ac00b002c00b007400b00ac00b28d800b00ac00b444000b007400b002c00b002d110007402b002c01d002c01d007400b002c00b002c00b002c00b00ac01d002c00b002c00b002c00b00ac00b00ac00b444001d177f1801227a6e770c7666232d274d55515d5c6b4a835f844182657d386f2f73007b581c8624 else 0x112844a153c44a11282700fd845089cc44a112800a49c24e6114044a153045391284e609ce44a0fe445309c400a51281b3003500a551a1b095181b386d000a402945106c04541128547002900a403d54a002900a402900d49d000fc02900a402b00a46c4549926000d402900a402900d40293a8003d00a402900d402900a402900a402900ac03500a402900a402939f002900a402900a552400a402900a4e7000a402900a402900d402900a402900ad128010402900f402900a402944a002900ac02900f402900d402900d402900d402900a403500d402900a402900d403500a402900a402b00a402900a402900a4029112d3646430060004c836b841a706c73367464883d805e79007c7d1d094e658523786f8755862d7f2c565724892c) else (if i < 543 then 0x11a0468139846811a046811a055211a04e60d6828191a02c1879e1e191a0002cf001f7928627c14303c5947846807c855791a0002c00b002c4ac46e078e49e0afe1271438520000b00cc01f002c00b002c00b4df001f002c00b007c00b002c00b002c00b002c01f002c00b007c00b002c00b00d4812002c033007c00b002c00b002d36c002c01f002c00b002c01f002c00b002c00b002c00b002d1a0002c00b00ec00b007c00b473800b002c00b2f8000b007c00b002c00b002cd7800cc01f007cbd8002c01f007c00b002c00b002c00b002c00b007c02f002c01f002c00b002c00b007c00b007c00b468001f17713682226275760c79677a387b5e2e53444f854c186980437f68012d6b3a8100235a868724 else 0x12184861218486001d49e0ab00b412482f11218002d59009d8d60486000b4c803582e58390519143413316464860dc851312184860b4248c02701130d442f28d4a50e946a002d218002d398514800b002c033002c00b111800b4db803d007401d002c00b002d218002c00b002c00b002d39800dc033007521835a000b002c01d002cd6a002c00b002cab6002c01d002c00b002c00b002c01d007400b002c00b002c0334da000b007400b002c00b002c033002c00b002c033002c00b002c00b00cc00b486000b007401d002c00b002c00b002c00b002c00b002c00b002c00b002c00b007401d002c033002c00b002c03300b400b11426e5d556b74004d848687233c5e4633774f6d2c78518800817f8a096c63891a7e611b447226503a677a808b2c)) else (if i < 546 then (if i < 545 then 0x4ab04e04b6000b56a0b122cd0cfe3de13b013900183f90b364a40b140025668534930c13880094aa8e884aa161400255300024b3800c06600750cfc002466255f130a07594d4076129055e0009002400b0024009002c00b4a40009002400b0025308002c0095340b100024009002400900240094a412900025290002400900240090024009340157a010466400240090024009002c009002400b0025290002400900240094a40009002400b002529000240090024009002c0090024009002400b002401d002400b002c009002400b002c009002400b0024009002c009002400b002c00b0024009002400900240090024009002400b1d3b630014505f28317c6932277e7646007f7b2d0a856f494f865c59578737624572717d3b6e88488c28 else 0xb4d4000b4d4135052c000b4df0d30002cfb410b042035d13805880b78007d62c34c93984d40c1034993504dc0d68349138c4d4000b2e1135030113680cc94a44d40fa8007401d002cb7c002c00b2dc001d002c00b002c00b002c00b4d4000b007401d002c00b007c00b002c00b00d5374002c00b007c00b002c00b002c480002c01d002c01d002d350002c00b002c00b002c00b002d398002c00b007400b002c00b4d4000b007400b4d4001f002c00b002c01f002c00b007c01f007d350002c01d007400b002c00b002c00b002c00b007c00b007401f002c00b002c00b002c00b007c00b002c01d17573a8122617b640c631c2738657e4f535a82834c748480437501182d727336006e66678524) else (if i < 547 then 0x3f91650597139835e0b5a3f60b582da13984e6122405713980580d6a05491a64e611a035d8d682e88770423876a423025a42105b809912264e612284a411141da12181db91104e60bac09991a809a135016e8d6c096112016f0b662eb93521db11a20fc13544e61082171912835d0ba446905c446a85c8486825c444815e2d701542d9129c0fc911e1dc911c0fd121c054109039610802e80bb0180f191d2324282f2e0d484a41525354355657450c555137004f424d581c else (if i < 548 then 0x36a0c4a5a016503608c843fc0c483221650594163a0b196500b215a806695c059415903698d8032707b858f07b258e04fc4270d180b11622594154a318962413e95c40a81548594129011a95501ee962011b0d8413e109a1ed8c8632795f41ed15f211a159259415d806615603690c6455306b455486b857082a457c07b0313019c4e61608345956434515620a895943e4154e1ad90983180ca0180f191d2324282f2e0d484a41525354355657450c555137004f424d581c else 0x3901b006f019802e007a03600780220198066015c003019800400aa000813e066013802d80a8024806803f806203f001a03d0048009015e066016005a010c01801500198108066009c009814000a018001280ac006011801300860278182019013a00c018406600f2015812002d009404f00540508058054801c042800e01f0004021017400c811601a811400d0154000010003000f002400a0180f191d2324282f2e0d484a41525354355657450c555137004f424d581c))))))))))

def nsE : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 30
  | 8 => 251
  | 9 => 241
  | 10 => 19
  | 11 => 1
  | _ => 0

def offE : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 37
  | 9 => 288
  | 10 => 529
  | 11 => 548
  | _ => 0

def gInit : Nat := 0


theorem rows516_len : rows516.length = 528 := by decide +kernel

theorem enc_inputs516 :
    (List.ofFn fun (i : Fin 8) => (fun x : Fin 8 → Bool => x i)).map (fun a => encL a rows516)
      = xs516 := by decide +kernel

theorem enc_goal516 : encL f516 rows516 = goal 264 := by decide +kernel

theorem mask516 : mask 264 = 2 ^ rows516.length - 1 := by
  have h : (264 : ℕ) + 264 = 528 := rfl
  simp only [mask, lo, rows516_len, h]

theorem proper_fail516 : ∀ zs ∈ xs516.sublists, zs ≠ xs516 →
    (cov 264 zs &&& lo 264) ≠ lo 264 := by decide +kernel

theorem no_sub516 (noRunFull : ∀ s ≤ 11, ¬ NatRun (mask 264) (goal 264) s xs516) :
    ∀ s ≤ 11, ∀ zs : List ℕ, zs.Sublist xs516 → NatRun (mask 264) (goal 264) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xs516
  · subst e; exact noRunFull s hs h
  · exact proper_fail516 zs (List.mem_sublists.2 hz) e (required h)

theorem main516 (noRunFull : ∀ s ≤ 11, ¬ NatRun (mask 264) (goal 264) s xs516) :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 1) || (x 0 && x 4) || (x 4 && x 5) || (x 5 && x 1) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 1)) s → 12 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run f516 ⟨fun _ => false, fun _ => true, by decide⟩ s h
  have hr : NatRun (mask 264) (encL f516 rows516) s' (ws.map fun a => encL a rows516) :=
    run_map (fun a : BFn 8 => encL a rows516)
      (fun a => by rw [mask516]; exact encL_inv a rows516)
      (fun a b => encL_and a b rows516) (fun a b => encL_or a b rows516) hrun
  rw [enc_goal516] at hr
  refine no_sub516 noRunFull s' (by omega) _ ?_ hr
  rw [← enc_inputs516]
  exact hsub.map _

def setF (xs : List Nat) := xs.map (moveBits deltaF 132)
def setT (xs : List Nat) := xs.map (moveBits deltaT 66)
def setC (xs : List Nat) := xs.map (move4 maskR1 maskL2 maskR2 maskL1 22)

theorem runF {s ws} (h : NatRun (mask 264) (goal 264) s ws) :
    NatRun (mask 264) (goal 264) s (setF ws) :=
  move_run h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem runT {s ws} (h : NatRun (mask 264) (goal 264) s ws) :
    NatRun (mask 264) (goal 264) s (setT ws) :=
  move_run h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem runC {s ws} (h : NatRun (mask 264) (goal 264) s ws) :
    NatRun (mask 264) (goal 264) s (setC ws) :=
  move4_run h _ _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def rotF (b : Nat) (ws : List Nat) := if b = 0 then ws else setF ws
def rotT (b : Nat) (ws : List Nat) := if b = 0 then ws else setT ws
def rotC (c : Nat) (ws : List Nat) := if c = 0 then ws else if c = 1 then setC ws else setC (setC ws)
def rotateE (g : Nat) (ws : List Nat) := rotC (g % 3) (rotT (g / 3 % 2) (rotF (g / 6) ws))

theorem runRotF (b : Nat) {s ws} (h : NatRun (mask 264) (goal 264) s ws) :
    NatRun (mask 264) (goal 264) s (rotF b ws) := by
  unfold rotF; split; exact h; exact runF h

theorem runRotT (b : Nat) {s ws} (h : NatRun (mask 264) (goal 264) s ws) :
    NatRun (mask 264) (goal 264) s (rotT b ws) := by
  unfold rotT; split; exact h; exact runT h

theorem runRotC (c : Nat) {s ws} (h : NatRun (mask 264) (goal 264) s ws) :
    NatRun (mask 264) (goal 264) s (rotC c ws) := by
  unfold rotC; split; exact h; split; exact runC h; exact runC (runC h)

theorem rotateE_ok (g : Nat) {s ws} (h : NatRun (mask 264) (goal 264) s ws) :
    NatRun (mask 264) (goal 264) s (rotateE g ws) :=
  runRotC _ (runRotT _ (runRotF _ h))

def stateE (s i : Nat) := rowsE (offE s + i)

def actionE (s i h : Nat) : Nat :=
  let t := segE (offE s + i)
  let a := t &&& 255
  let b := (t >>> 8) &&& 255
  let d := (t >>> (16 + 8 * (h % a))) &&& 255
  (t >>> (16 + 8 * a + 14 * ((h / a + d) % b))) &&& 16383

def Z (s : Nat) := barrier 264 stateE nsE actionE sixE rotateE s

theorem h0y0 : span (Z 0) 1 0 = true := by decide +kernel
theorem z0 : span (Z 0) 1 0 = true := h0y0

theorem h1y0 : span (Z 1) 1 0 = true := by decide +kernel
theorem z1 : span (Z 1) 1 0 = true := h1y0

theorem h2y0 : span (Z 2) 1 0 = true := by decide +kernel
theorem z2 : span (Z 2) 1 0 = true := h2y0

theorem h3y0 : span (Z 3) 1 0 = true := by decide +kernel
theorem z3 : span (Z 3) 1 0 = true := h3y0

theorem h4y0 : span (Z 4) 1 0 = true := by decide +kernel
theorem z4 : span (Z 4) 1 0 = true := h4y0

theorem h5y0 : span (Z 5) 1 0 = true := by decide +kernel
theorem z5 : span (Z 5) 1 0 = true := h5y0

theorem h6y0 : span (Z 6) 1 0 = true := by decide +kernel
theorem z6 : span (Z 6) 1 0 = true := h6y0

theorem h7y0 : span (Z 7) 8 0 = true := by decide +kernel
theorem h7y1 : span (Z 7) 8 8 = true := by decide +kernel
theorem h7y2 : span (Z 7) 8 16 = true := by decide +kernel
theorem h7y3 : span (Z 7) 6 24 = true := by decide +kernel
theorem z7 : span (Z 7) 30 0 = true := (@span_join (Z 7) 16 0 14 (@span_join (Z 7) 8 0 8 h7y0 h7y1) (@span_join (Z 7) 8 16 6 h7y2 h7y3))

theorem h8y0 : span (Z 8) 8 0 = true := by decide +kernel
theorem h8y1 : span (Z 8) 8 8 = true := by decide +kernel
theorem h8y2 : span (Z 8) 8 16 = true := by decide +kernel
theorem h8y3 : span (Z 8) 8 24 = true := by decide +kernel
theorem h8y4 : span (Z 8) 8 32 = true := by decide +kernel
theorem h8y5 : span (Z 8) 8 40 = true := by decide +kernel
theorem h8y6 : span (Z 8) 8 48 = true := by decide +kernel
theorem h8y7 : span (Z 8) 8 56 = true := by decide +kernel
theorem h8y8 : span (Z 8) 8 64 = true := by decide +kernel
theorem h8y9 : span (Z 8) 8 72 = true := by decide +kernel
theorem h8y10 : span (Z 8) 8 80 = true := by decide +kernel
theorem h8y11 : span (Z 8) 8 88 = true := by decide +kernel
theorem h8y12 : span (Z 8) 8 96 = true := by decide +kernel
theorem h8y13 : span (Z 8) 8 104 = true := by decide +kernel
theorem h8y14 : span (Z 8) 8 112 = true := by decide +kernel
theorem h8y15 : span (Z 8) 8 120 = true := by decide +kernel
theorem h8y16 : span (Z 8) 8 128 = true := by decide +kernel
theorem h8y17 : span (Z 8) 8 136 = true := by decide +kernel
theorem h8y18 : span (Z 8) 8 144 = true := by decide +kernel
theorem h8y19 : span (Z 8) 8 152 = true := by decide +kernel
theorem h8y20 : span (Z 8) 8 160 = true := by decide +kernel
theorem h8y21 : span (Z 8) 8 168 = true := by decide +kernel
theorem h8y22 : span (Z 8) 8 176 = true := by decide +kernel
theorem h8y23 : span (Z 8) 8 184 = true := by decide +kernel
theorem h8y24 : span (Z 8) 8 192 = true := by decide +kernel
theorem h8y25 : span (Z 8) 8 200 = true := by decide +kernel
theorem h8y26 : span (Z 8) 8 208 = true := by decide +kernel
theorem h8y27 : span (Z 8) 8 216 = true := by decide +kernel
theorem h8y28 : span (Z 8) 8 224 = true := by decide +kernel
theorem h8y29 : span (Z 8) 8 232 = true := by decide +kernel
theorem h8y30 : span (Z 8) 8 240 = true := by decide +kernel
theorem h8y31 : span (Z 8) 3 248 = true := by decide +kernel
theorem z8 : span (Z 8) 251 0 = true := (@span_join (Z 8) 128 0 123 (@span_join (Z 8) 64 0 64 (@span_join (Z 8) 32 0 32 (@span_join (Z 8) 16 0 16 (@span_join (Z 8) 8 0 8 h8y0 h8y1) (@span_join (Z 8) 8 16 8 h8y2 h8y3)) (@span_join (Z 8) 16 32 16 (@span_join (Z 8) 8 32 8 h8y4 h8y5) (@span_join (Z 8) 8 48 8 h8y6 h8y7))) (@span_join (Z 8) 32 64 32 (@span_join (Z 8) 16 64 16 (@span_join (Z 8) 8 64 8 h8y8 h8y9) (@span_join (Z 8) 8 80 8 h8y10 h8y11)) (@span_join (Z 8) 16 96 16 (@span_join (Z 8) 8 96 8 h8y12 h8y13) (@span_join (Z 8) 8 112 8 h8y14 h8y15)))) (@span_join (Z 8) 64 128 59 (@span_join (Z 8) 32 128 32 (@span_join (Z 8) 16 128 16 (@span_join (Z 8) 8 128 8 h8y16 h8y17) (@span_join (Z 8) 8 144 8 h8y18 h8y19)) (@span_join (Z 8) 16 160 16 (@span_join (Z 8) 8 160 8 h8y20 h8y21) (@span_join (Z 8) 8 176 8 h8y22 h8y23))) (@span_join (Z 8) 32 192 27 (@span_join (Z 8) 16 192 16 (@span_join (Z 8) 8 192 8 h8y24 h8y25) (@span_join (Z 8) 8 208 8 h8y26 h8y27)) (@span_join (Z 8) 16 224 11 (@span_join (Z 8) 8 224 8 h8y28 h8y29) (@span_join (Z 8) 8 240 3 h8y30 h8y31)))))

theorem h9y0 : span (Z 9) 8 0 = true := by decide +kernel
theorem h9y1 : span (Z 9) 8 8 = true := by decide +kernel
theorem h9y2 : span (Z 9) 8 16 = true := by decide +kernel
theorem h9y3 : span (Z 9) 8 24 = true := by decide +kernel
theorem h9y4 : span (Z 9) 8 32 = true := by decide +kernel
theorem h9y5 : span (Z 9) 8 40 = true := by decide +kernel
theorem h9y6 : span (Z 9) 8 48 = true := by decide +kernel
theorem h9y7 : span (Z 9) 8 56 = true := by decide +kernel
theorem h9y8 : span (Z 9) 8 64 = true := by decide +kernel
theorem h9y9 : span (Z 9) 8 72 = true := by decide +kernel
theorem h9y10 : span (Z 9) 8 80 = true := by decide +kernel
theorem h9y11 : span (Z 9) 8 88 = true := by decide +kernel
theorem h9y12 : span (Z 9) 8 96 = true := by decide +kernel
theorem h9y13 : span (Z 9) 8 104 = true := by decide +kernel
theorem h9y14 : span (Z 9) 8 112 = true := by decide +kernel
theorem h9y15 : span (Z 9) 8 120 = true := by decide +kernel
theorem h9y16 : span (Z 9) 8 128 = true := by decide +kernel
theorem h9y17 : span (Z 9) 8 136 = true := by decide +kernel
theorem h9y18 : span (Z 9) 8 144 = true := by decide +kernel
theorem h9y19 : span (Z 9) 8 152 = true := by decide +kernel
theorem h9y20 : span (Z 9) 8 160 = true := by decide +kernel
theorem h9y21 : span (Z 9) 8 168 = true := by decide +kernel
theorem h9y22 : span (Z 9) 8 176 = true := by decide +kernel
theorem h9y23 : span (Z 9) 8 184 = true := by decide +kernel
theorem h9y24 : span (Z 9) 8 192 = true := by decide +kernel
theorem h9y25 : span (Z 9) 8 200 = true := by decide +kernel
theorem h9y26 : span (Z 9) 8 208 = true := by decide +kernel
theorem h9y27 : span (Z 9) 8 216 = true := by decide +kernel
theorem h9y28 : span (Z 9) 8 224 = true := by decide +kernel
theorem h9y29 : span (Z 9) 8 232 = true := by decide +kernel
theorem h9y30 : span (Z 9) 1 240 = true := by decide +kernel
theorem z9 : span (Z 9) 241 0 = true := (@span_join (Z 9) 120 0 121 (@span_join (Z 9) 56 0 64 (@span_join (Z 9) 24 0 32 (@span_join (Z 9) 8 0 16 h9y0 (@span_join (Z 9) 8 8 8 h9y1 h9y2)) (@span_join (Z 9) 16 24 16 (@span_join (Z 9) 8 24 8 h9y3 h9y4) (@span_join (Z 9) 8 40 8 h9y5 h9y6))) (@span_join (Z 9) 32 56 32 (@span_join (Z 9) 16 56 16 (@span_join (Z 9) 8 56 8 h9y7 h9y8) (@span_join (Z 9) 8 72 8 h9y9 h9y10)) (@span_join (Z 9) 16 88 16 (@span_join (Z 9) 8 88 8 h9y11 h9y12) (@span_join (Z 9) 8 104 8 h9y13 h9y14)))) (@span_join (Z 9) 64 120 57 (@span_join (Z 9) 32 120 32 (@span_join (Z 9) 16 120 16 (@span_join (Z 9) 8 120 8 h9y15 h9y16) (@span_join (Z 9) 8 136 8 h9y17 h9y18)) (@span_join (Z 9) 16 152 16 (@span_join (Z 9) 8 152 8 h9y19 h9y20) (@span_join (Z 9) 8 168 8 h9y21 h9y22))) (@span_join (Z 9) 32 184 25 (@span_join (Z 9) 16 184 16 (@span_join (Z 9) 8 184 8 h9y23 h9y24) (@span_join (Z 9) 8 200 8 h9y25 h9y26)) (@span_join (Z 9) 16 216 9 (@span_join (Z 9) 8 216 8 h9y27 h9y28) (@span_join (Z 9) 8 232 1 h9y29 h9y30)))))

theorem h10y0 : span (Z 10) 8 0 = true := by decide +kernel
theorem h10y1 : span (Z 10) 8 8 = true := by decide +kernel
theorem h10y2 : span (Z 10) 3 16 = true := by decide +kernel
theorem z10 : span (Z 10) 19 0 = true := (@span_join (Z 10) 8 0 11 h10y0 (@span_join (Z 10) 8 8 3 h10y1 h10y2))

theorem h11y0 : span (Z 11) 1 0 = true := by decide +kernel
theorem z11 : span (Z 11) 1 0 = true := h11y0


theorem checkedE (s : Nat) (hs : s ≤ 11) : ∀ i < nsE s, Z s i = true := by
  interval_cases s
  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z9 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z10 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z11 i (Nat.zero_le i) hi

theorem noRunFull (s : Nat) (hs : s ≤ 11) (h : NatRun (mask 264) (goal 264) s xs516) : False := by
  have h11 : NatRun (mask 264) (goal 264) 11 xs516 := extend_run h hs
  have p : (rotateE gInit xs516).Perm (stateE 11 0) := by decide +kernel
  exact barrier_all rotateE_ok checkedE 11 (by decide) 0 (by decide) (run_perm p (rotateE_ok gInit h11))

end Live516

theorem PEqualNP.Outside.L_meta_516 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 1) || (x 0 && x 4) || (x 4 && x 5) || (x 5 && x 1) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 1)) s → 12 ≤ s :=
  Live516.main516 Live516.noRunFull
