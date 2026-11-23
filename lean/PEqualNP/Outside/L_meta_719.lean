import Mathlib
import PEqualNP.Defs

-- Generic Run normalization adapted from Digger-Rockwell PR801, Apache-2.0.
-- Source commit ea90309308dd46a22d4a469766e46dd63f4484d0.
-- Monotone preservation, directed coverage, and this finite certificate are new.


namespace PEqualNP.Outside.L_meta_719_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool), P s (inv a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}

theorem Run.done : Run inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : Run inv meet join y s xs) :
    Run inv meet join y s zs := fun P d q u b => q p (h P d q u b)

theorem Run.one {s a r} (save : Bool)
    (h : Run inv meet join y s (inv a :: kept save a r)) :
    Run inv meet join y (s + 1) (a :: r) := fun P d q u b => u save (h P d q u b)

theorem Run.two {s a b r} (c ka kb : Bool)
    (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s + 1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {P : ∀ t ws, Run inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (save : Bool)
      (h : Run inv meet join y s (inv a :: kept save a r)),
      P _ _ h → P _ _ (Run.one save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun k ⟨h', ih⟩ => ⟨Run.one k h', one k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

end

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

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest save _ ih =>
    have e1 : (inv a :: kept save a rest).map e
        = inv' (e a) :: kept save (e a) (rest.map e) := by
      simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) :=
  List.foldl_append

theorem length_wiresFrom (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresFrom]
  | cons g gs ih =>
    intro w
    rw [wiresFrom_cons, ih]
    simp
    omega

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by
      rw [wiresFrom_cons, ht, List.append_assoc]⟩

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht⟩ := wiresFrom_prefix gs w
  rw [ht]
  exact List.getD_append _ _ _ _ h

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem split_at (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hgp : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp [hlt.le]⟩
  calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
    _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hlt]
    _ = gs.take p ++ g :: gs.drop (p + 1) := by rw [hgp]

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

def SCleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ j ≠ k ∧ g.inputs = [j, k])

theorem SCleanGate.lt {m : ℕ} {g : Gate} (h : SCleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, _, hin⟩ <;> rw [hin] <;> simp_all

def SCleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → SCleanGate (n + p) g

def statVal (w : List Bool) : Sum Bool ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Sum Bool ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Sum Bool ℕ, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Sum Bool ℕ, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def simpNot (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, if c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, if c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] =>
      if j = k then (none, Sum.inr j) else (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, if c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, if c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] =>
      if j = k then (none, Sum.inr j) else (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ)) : Option Gate × Sum Bool ℕ :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ))
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, SCleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpAnd] at hg
    · cases a <;> simp [simpAnd] at hg
    · cases a <;> cases b <;> simp only [simpAnd, Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk, ite_false, Option.some.injEq] at hg
        subst hg
        exact Or.inr ⟨Or.inl rfl, j, k, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), hjk, rfl⟩
    · simp [simpAnd] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpOr] at hg
    · cases a <;> simp [simpOr] at hg
    · cases a <;> cases b <;> simp only [simpOr, Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk, ite_false, Option.some.injEq] at hg
        subst hg
        exact Or.inr ⟨Or.inr rfl, j, k, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), hjk, rfl⟩
    · simp [simpOr] at hg
  · rcases ins with _ | ⟨a, l⟩
    · simp [simpNot] at hg
    · cases a <;> simp only [simpNot, Option.mem_def] at hg
      · contradiction
      · rename_i j
        cases hg
        exact Or.inl ⟨rfl, j, hv (Sum.inr j) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Sum Bool ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b
      · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
      · rename_i c j; cases c <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j c; cases c <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j k
        by_cases hjk : j = k
        · subst hjk
          simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
      · rename_i c j; cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j c; cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j k
        by_cases hjk : j = k
        · subst hjk
          simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def simpStep (n : ℕ) (acc : List (Sum Bool ℕ) × List Gate) (g : Gate) :
    List (Sum Bool ℕ) × List Gate :=
  let r := simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def simpPass (n : ℕ) (gs : List Gate) (acc : List (Sum Bool ℕ) × List Gate) :
    List (Sum Bool ℕ) × List Gate :=
  gs.foldl (simpStep n) acc

theorem simpPass_len (n : ℕ) (gs : List Gate) : ∀ acc : List (Sum Bool ℕ) × List Gate,
    (simpPass n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [simpPass]
  | cons g gs ih =>
    intro acc
    have h1 := ih (simpStep n acc g)
    have h2 : (simpStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [simpStep, List.length_append]
      cases (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;> simp
    have h3 : simpPass n (g :: gs) acc = simpPass n gs (simpStep n acc g) := rfl
    rw [h3, List.length_cons]
    omega

def SimpInv (n : ℕ) (x : List Bool) (w : List Bool) (acc : List (Sum Bool ℕ) × List Gate) : Prop :=
  acc.1.length = w.length ∧
  SCleanL n acc.2 ∧
  ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 x) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem simpPass_inv (n : ℕ) (x : List Bool) (hx : x.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List (Sum Bool ℕ) × List Gate),
      (∀ g ∈ gs,
        (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      SimpInv n x w acc →
      SimpInv n x (wiresFrom gs w) (simpPass n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (simpStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hcl, hi⟩ := h
    set w' := wiresFrom acc.2 x with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hx]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hvins : ∀ s ∈ ins, statValid (n + acc.2.length) s := by
      intro s hs
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
      exact (hi a).1
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by rw [lw']; exact hvins)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) x = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht⟩ := wiresFrom_prefix r.1.toList w'
    have hcl' : SCleanL n (acc.2 ++ r.1.toList) := by
      intro p g' hpg'
      cases hr1 : r.1 with
      | none =>
        rw [hr1] at hpg'
        simp only [Option.toList_none, List.append_nil] at hpg'
        exact hcl p g' hpg'
      | some g0 =>
        rw [hr1] at hpg'
        simp only [Option.toList_some] at hpg'
        by_cases hp : p < acc.2.length
        · rw [List.getElem?_append_left hp] at hpg'
          exact hcl p g' hpg'
        · have hpe : p = acc.2.length := by
            have := (List.getElem?_eq_some_iff.1 hpg').1
            simp at this
            omega
          subst hpe
          rw [List.getElem?_append_right le_rfl] at hpg'
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hpg'
          subst hpg'
          exact simplify_clean g.op (n + acc.2.length) ins hvins g0 (by simp [← hr, hr1])
    refine ⟨by simp [simpStep, hl], hcl', ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) x) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_len _ _ _ _ rfl, hl, getD_snoc_len _ _ _ _ rfl]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem exists_sclean {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ gs o, gs.length ≤ s ∧ SCleanL n gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  have hok : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    refine ⟨?_, hlen⟩
    rcases hop with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  set init : List (Sum Bool ℕ) := List.ofFn fun i : Fin n => Sum.inr i.val
  set acc := simpPass n C.gates (init, [])
  have hinit : ∀ x : Fin n → Bool, SimpInv n (List.ofFn x) (List.ofFn x) (init, []) := by
    intro x
    refine ⟨by simp [init], by intro p g hg; simp at hg, ?_⟩
    intro i
    by_cases hi : i < n
    · simp [init, hi, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ x : Fin n → Bool,
      SimpInv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc := fun x =>
    simpPass_inv n (List.ofFn x) (by simp) C.gates (List.ofFn x) (init, []) hok (hinit x)
  have hlen : acc.2.length ≤ s := by
    have := simpPass_len n C.gates (init, [])
    simp only [List.length_nil, zero_add] at this
    exact le_trans this hsz
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have h1 := ((hinv y).2.2 C.output).2
    have h2 := ((hinv y').2.2 C.output).2
    rw [hst] at h1 h2
    have e1 : wiresFrom C.gates (List.ofFn y) = C.wires (List.ofFn y) := rfl
    have e2 : wiresFrom C.gates (List.ofFn y') = C.wires (List.ofFn y') := rfl
    rw [← hev y, ← hev y']
    show (C.wires (List.ofFn y)).getD C.output false = (C.wires (List.ofFn y')).getD C.output false
    rw [← e1, ← e2, ← h1, ← h2]
    rfl
  | inr o =>
    obtain ⟨y, _, _⟩ := hnc
    have ho : o < n + acc.2.length := by
      have hv := ((hinv y).2.2 C.output).1
      rw [hst] at hv
      exact hv
    refine ⟨acc.2, o, hlen, (hinv y).2.1, ho, ?_⟩
    intro x
    have hv := ((hinv x).2.2 C.output).2
    rw [hst] at hv
    have e1 : wiresFrom C.gates (List.ofFn x) = C.wires (List.ofFn x) := rfl
    rw [← hev x]
    show (wiresFrom acc.2 (List.ofFn x)).getD o false = (C.wires (List.ofFn x)).getD C.output false
    rw [← e1, ← hv]
    rfl

def redir (m a : ℕ) : ℕ := if m < a then a - 1 else a

theorem redir_lt {m b a : ℕ} (hm : m ≤ b) (ha : a < b + 1) (hne : a ≠ m) : redir m a < b := by
  unfold redir
  split <;> omega

theorem redir_inj {m a b : ℕ} (ha : a ≠ m) (hb : b ≠ m) (heq : redir m a = redir m b) :
    a = b := by
  unfold redir at heq
  split at heq <;> split at heq <;> omega

theorem getD_drop_wire (w₁ u : List Bool) (b : Bool) (a : ℕ) (hne : a ≠ w₁.length) :
    (w₁ ++ u).getD (redir w₁.length a) false = (w₁ ++ [b] ++ u).getD a false := by
  unfold redir
  by_cases hlt : w₁.length < a
  · simp only [hlt, ite_true]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    have hlen : (w₁ ++ [b]).length = w₁.length + 1 := by simp
    rw [List.getElem?_append_right (by omega), hlen]
    congr 2
    omega
  · simp only [hlt, ite_false]
    have ha : a < w₁.length := by omega
    rw [List.getD_append _ _ _ _ ha]
    rw [List.append_assoc, List.getD_append _ _ _ _ ha]

theorem wiresFrom_drop_dead (w₁ : List Bool) (b : Bool) (post : List Gate) :
    ∀ u : List Bool,
      (∀ g ∈ post, w₁.length ∉ g.inputs) →
      ∃ u',
        wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (redir w₁.length)⟩) (w₁ ++ u) = w₁ ++ u' ∧
        wiresFrom post (w₁ ++ [b] ++ u) = w₁ ++ [b] ++ u' := by
  induction post with
  | nil => intro u _; exact ⟨u, rfl, rfl⟩
  | cons g gs ih =>
    intro u hdead
    have hg : w₁.length ∉ g.inputs := hdead g List.mem_cons_self
    have hmap : (g.inputs.map (redir w₁.length)).map (fun i => (w₁ ++ u).getD i false)
        = g.inputs.map (fun i => (w₁ ++ [b] ++ u).getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact getD_drop_wire w₁ u b a (fun e => hg (e ▸ ha))
    set c := g.op.eval (g.inputs.map fun i => (w₁ ++ [b] ++ u).getD i false)
    obtain ⟨u', h1, h2⟩ := ih (u ++ [c]) (fun g' hg' => hdead g' (List.mem_cons_of_mem _ hg'))
    refine ⟨u', ?_, ?_⟩
    · simp only [List.map_cons, wiresFrom_cons, hmap]
      rw [List.append_assoc]
      exact h1
    · rw [wiresFrom_cons, List.append_assoc, List.append_assoc]
      rw [← List.append_assoc w₁ [b] (u ++ [c])]
      exact h2

theorem erase_dead (n : ℕ) (gs : List Gate) (o p : ℕ) (hcl : SCleanL n gs)
    (ho : o < n + gs.length) (hp : p < gs.length) (hne : n + p ≠ o)
    (hdead : ∀ (q : ℕ) (g : Gate), gs[q]? = some g → n + p ∉ g.inputs) :
    ∃ gs' o', gs'.length + 1 = gs.length ∧ SCleanL n gs' ∧ o' < n + gs'.length ∧
      ∀ x, val gs' n o' x = val gs n o x := by
  let gs' := gs.take p ++ (gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩
  let o' := redir (n + p) o
  have hlen' : gs'.length + 1 = gs.length := by
    simp [gs']
    omega
  have ho' : o' < n + gs'.length := redir_lt (by omega) (by omega) (Ne.symm hne)
  have hcl' : SCleanL n gs' := by
    intro q g hqg
    by_cases hqp : q < p
    · have h1 : gs'[q]? = gs[q]? := by
        simp only [gs']
        rw [List.getElem?_append_left (by simp; omega)]
        exact List.getElem?_take_of_lt hqp
      rw [h1] at hqg
      exact hcl q g hqg
    · have hlt' : q < gs'.length := (List.getElem?_eq_some_iff.1 hqg).1
      have hq1 : q + 1 < gs.length := by omega
      have h1 : gs'[q]? = ((gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩)[q - p]? := by
        simp only [gs']
        rw [List.getElem?_append_right (by simp; omega)]
        simp [Nat.min_eq_left (Nat.le_of_lt hp)]
      rw [h1, List.getElem?_map, List.getElem?_drop] at hqg
      have hidx : p + 1 + (q - p) = q + 1 := by omega
      rw [hidx] at hqg
      obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hqg
      have hcl0 := hcl (q + 1) g0 hg0
      have hd0 := hdead (q + 1) g0 hg0
      rcases hcl0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hjk, hin⟩
      · refine Or.inl ⟨hop, redir (n + p) j, ?_, by simp [hin]⟩
        exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
      · refine Or.inr ⟨hop, redir (n + p) j, redir (n + p) k, ?_, ?_, ?_, by simp [hin]⟩
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · intro heq
          exact hjk (redir_inj (fun e => hd0 (by rw [hin]; simp [e]))
            (fun e => hd0 (by rw [hin]; simp [e])) heq)
  refine ⟨gs', o', hlen', hcl', ho', ?_⟩
  intro x
  unfold val
  have hsplit : gs = gs.take p ++ gs[p] :: gs.drop (p + 1) := by
    calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
      _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hp]
  set w₁ := wiresFrom (gs.take p) (List.ofFn x)
  have lw₁ : w₁.length = n + p := by
    rw [length_wiresFrom]
    simp [Nat.min_eq_left (Nat.le_of_lt hp)]
  have hdead_post : ∀ g ∈ gs.drop (p + 1), w₁.length ∉ g.inputs := by
    intro g hg
    obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop] at hgk
    rw [lw₁]
    have hlt_k : p + 1 + k < gs.length := by simp at hk; omega
    exact hdead (p + 1 + k) g (by rw [List.getElem?_eq_getElem hlt_k, hgk])
  set b := gs[p].op.eval (gs[p].inputs.map fun i => w₁.getD i false)
  obtain ⟨u', hu1, hu2⟩ := wiresFrom_drop_dead w₁ b (gs.drop (p + 1)) [] hdead_post
  have heq1 : wiresFrom gs' (List.ofFn x) = w₁ ++ u' := by
    simp only [gs', wiresFrom_append]
    rw [← lw₁]
    simpa [w₁] using hu1
  have heq2 : wiresFrom gs (List.ofFn x) = w₁ ++ [b] ++ u' := by
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_cons]
    simpa [w₁, b] using hu2
  rw [heq1, heq2]
  show (w₁ ++ u').getD (redir (n + p) o) false = (w₁ ++ [b] ++ u').getD o false
  rw [← lw₁]
  exact getD_drop_wire w₁ u' b o (by rw [lw₁]; exact Ne.symm hne)

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

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs)
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
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs) (ho : o < n + gs.length)
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
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
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
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hjk, hinp⟩
    · have hjm := hin j (by simp [hinp])
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hjm
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hjm h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff]
          simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hjm, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have hval : val gs n (n + p) = invF (val gs n j) := by
        funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval, invF]
      have IH' := Run.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.one _ IH')
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
        intro a
        rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
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
      have IH' := Run.perm (hp2.map (val gs n)) IH
      have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
          then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
        funext x
        rw [hvg x, hinp]
        rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval, meetF, joinF]
      rw [List.map_cons, kept_map, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')

open Classical in
theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  have hex : ∃ m, ∃ gs o, gs.length = m ∧ SCleanL n gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
    obtain ⟨gs, o, hl, hcl, ho, hev⟩ := exists_sclean f hnc s h
    exact ⟨gs.length, gs, o, rfl, hcl, ho, hev⟩
  set m := Nat.find hex
  have hm_le : m ≤ s := by
    obtain ⟨gs, o, hl, hcl, ho, hev⟩ := exists_sclean f hnc s h
    exact le_trans (Nat.find_min' hex ⟨gs, o, rfl, hcl, ho, hev⟩) hl
  obtain ⟨gs, o, hlen, hcl, ho, hev⟩ := Nat.find_spec hex
  have hnd : ∀ p, p < gs.length → n + p = o ∨
      ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra! hbad
    obtain ⟨hne, hdead⟩ := hbad
    obtain ⟨gs', o', hlen', hcl', ho', hev'⟩ := erase_dead n gs o p hcl ho hp hne hdead
    have hlt : gs'.length < m := by omega
    exact Nat.find_min hex hlt ⟨gs', o', rfl, hcl', ho', fun x => (hev' x).trans (hev x)⟩
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
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true, kept, List.mem_cons] at hmem
    · rcases hmem with rfl | hr
      · simp [ha, hm]
      · exact hw _ (by simp [hr])
    · rcases hmem with rfl | rfl | hr
      · simp [ha, hm]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k + i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all

def lo (k : Nat) := 2 ^ k - 1
def mask (k : Nat) := lo (k + k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k + i) := by
      simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k + k by omega, show k + i < k + k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k + i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k + i) hm hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

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


abbrev wheel : BFn 6 := fun x : Fin 6 → Bool =>
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4) ||
  (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 4 && x 5)

theorem wheel_iff (x : Fin 6 → Bool) :
    wheel x = true ↔ ∃ u v : Fin 6,
      (u.val,v.val) ∈ ([(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,5),(2,5),(3,5),(4,5)] : List (ℕ × ℕ)) ∧
      x u = true ∧ x v = true := by
  constructor
  · intro h
    simp only [wheel,Bool.or_eq_true,Bool.and_eq_true] at h
    rcases h with (((((((((⟨h0,h1⟩ | ⟨h1,h2⟩) | ⟨h2,h3⟩) | ⟨h3,h4⟩) | ⟨h0,h4⟩) |
      ⟨h0,h5⟩) | ⟨h1,h5⟩) | ⟨h2,h5⟩) | ⟨h3,h5⟩) | ⟨h4,h5⟩)
    · exact ⟨0,1,by simp,h0,h1⟩
    · exact ⟨1,2,by simp,h1,h2⟩
    · exact ⟨2,3,by simp,h2,h3⟩
    · exact ⟨3,4,by simp,h3,h4⟩
    · exact ⟨0,4,by simp,h0,h4⟩
    · exact ⟨0,5,by simp,h0,h5⟩
    · exact ⟨1,5,by simp,h1,h5⟩
    · exact ⟨2,5,by simp,h2,h5⟩
    · exact ⟨3,5,by simp,h3,h5⟩
    · exact ⟨4,5,by simp,h4,h5⟩
  · rintro ⟨u,v,huv,hu,hv⟩
    fin_cases u <;> fin_cases v <;> simp_all [wheel]

theorem wheel_hasCircuit {C : Circuit} (hmono : Monotone2 C)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6,
      (u.val,v.val) ∈ ([(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,5),(2,5),(3,5),(4,5)] : List (ℕ × ℕ)) ∧
      x u = true ∧ x v = true) (hs : C.size ≤ 8) :
    HasCircuitSize 6 wheel 8 := by
  refine ⟨C,?_,hs,?_⟩
  · intro g hg
    obtain ⟨hop,hlen⟩ := hmono g hg
    refine ⟨?_,hlen⟩
    rcases hop with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · intro x
    rw [Bool.eq_iff_iff,hev x,wheel_iff x]

theorem wheel_run (h : HasCircuitSize 6 wheel 8) :
    ∃ s, s ≤ 8 ∧ ∃ ws : List (BFn 6),
      ws.Sublist (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)) ∧
      Run (invF (n := 6)) meetF joinF wheel s ws :=
  exists_run wheel ⟨fun _ => false,fun _ => true,by decide⟩ 8 h

theorem encoded_wheel_bridge (rows xs : List ℕ) (k : ℕ)
    (hinputs : (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map
      (fun a => encL a rows) = xs)
    (hgoal : encL wheel rows = goal k)
    (hmask : mask k = 2 ^ rows.length - 1)
    (hproper : ∀ zs ∈ xs.sublists, zs ≠ xs → (cov k zs &&& lo k) ≠ lo k)
    (hno : ∀ s ≤ 8, ¬ NatRun (mask k) (goal k) s xs) :
    ¬ HasCircuitSize 6 wheel 8 := by
  intro h
  obtain ⟨s,hs,ws,hsub,hrun⟩ := wheel_run h
  have hr : NatRun (mask k) (encL wheel rows) s (ws.map (fun a => encL a rows)) :=
    Run.map (fun a : BFn 6 => encL a rows)
      (fun a => by rw [hmask]; exact encL_inv a rows)
      (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) hrun
  rw [hgoal] at hr
  have hz : (ws.map (fun a => encL a rows)).Sublist xs := by
    rw [← hinputs]
    exact hsub.map _
  by_cases he : ws.map (fun a => encL a rows) = xs
  · rw [he] at hr
    exact hno s hs hr
  · exact hproper _ (List.mem_sublists.2 hz) he (required hr)

theorem wheel_lower_from_full_exclusion (hno : ¬ HasCircuitSize 6 wheel 8)
    (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6,
      (u.val,v.val) ∈ ([(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,5),(2,5),(3,5),(4,5)] : List (ℕ × ℕ)) ∧
      x u = true ∧ x v = true) : 9 ≤ C.size := by
  by_contra hs
  exact hno (wheel_hasCircuit hmono hev (by omega))


def MonoL (gs : List Gate) : Prop := ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or

def HasMonoSize (n : ℕ) (f : BFn n) (s : ℕ) : Prop :=
  ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = f x

theorem simplify_mono (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∀ g ∈ (simplify op m ins).1, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩
    · simp [simplify,simpAnd] at hg
    · cases a <;> simp [simplify,simpAnd] at hg
    · cases a <;> cases b <;> simp only [simplify,simpAnd,Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk,ite_false,Option.some.injEq] at hg
        subst hg
        exact Or.inl rfl
    · simp [simplify,simpAnd] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩
    · simp [simplify,simpOr] at hg
    · cases a <;> simp [simplify,simpOr] at hg
    · cases a <;> cases b <;> simp only [simplify,simpOr,Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk,ite_false,Option.some.injEq] at hg
        subst hg
        exact Or.inr rfl
    · simp [simplify,simpOr] at hg

theorem simpPass_mono (n : ℕ) (gs : List Gate) (hgs : MonoL gs) :
    ∀ acc : List (Sum Bool ℕ) × List Gate, MonoL acc.2 → MonoL (simpPass n gs acc).2 := by
  induction gs with
  | nil => intro acc hacc; exact hacc
  | cons g gs ih =>
    intro acc hacc
    apply ih (fun q hq => hgs q (List.mem_cons_of_mem _ hq)) (simpStep n acc g)
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hacc q hq
    · exact simplify_mono g.op _ _ (hgs g List.mem_cons_self) q (by simpa using hq)

theorem exists_sclean_mono {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasMonoSize n f s) :
    ∃ gs o, gs.length ≤ s ∧ SCleanL n gs ∧ MonoL gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  have hok : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    refine ⟨?_, hlen⟩
    rcases hop with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  set init : List (Sum Bool ℕ) := List.ofFn fun i : Fin n => Sum.inr i.val
  set acc := simpPass n C.gates (init, [])
  have hinit : ∀ x : Fin n → Bool, SimpInv n (List.ofFn x) (List.ofFn x) (init, []) := by
    intro x
    refine ⟨by simp [init], by intro p g hg; simp at hg, ?_⟩
    intro i
    by_cases hi : i < n
    · simp [init, hi, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ x : Fin n → Bool,
      SimpInv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc := fun x =>
    simpPass_inv n (List.ofFn x) (by simp) C.gates (List.ofFn x) (init, []) hok (hinit x)
  have hlen : acc.2.length ≤ s := by
    have := simpPass_len n C.gates (init, [])
    simp only [List.length_nil, zero_add] at this
    exact le_trans this hsz
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have h1 := ((hinv y).2.2 C.output).2
    have h2 := ((hinv y').2.2 C.output).2
    rw [hst] at h1 h2
    have e1 : wiresFrom C.gates (List.ofFn y) = C.wires (List.ofFn y) := rfl
    have e2 : wiresFrom C.gates (List.ofFn y') = C.wires (List.ofFn y') := rfl
    rw [← hev y, ← hev y']
    show (C.wires (List.ofFn y)).getD C.output false = (C.wires (List.ofFn y')).getD C.output false
    rw [← e1, ← e2, ← h1, ← h2]
    rfl
  | inr o =>
    obtain ⟨y, _, _⟩ := hnc
    have ho : o < n + acc.2.length := by
      have hv := ((hinv y).2.2 C.output).1
      rw [hst] at hv
      exact hv
    have hm : MonoL acc.2 := simpPass_mono n C.gates
      (fun g hg => (hfan g hg).1) (init,[]) (by intro g hg; simp at hg)
    refine ⟨acc.2, o, hlen, (hinv y).2.1, hm, ho, ?_⟩
    intro x
    have hv := ((hinv x).2.2 C.output).2
    rw [hst] at hv
    have e1 : wiresFrom C.gates (List.ofFn x) = C.wires (List.ofFn x) := rfl
    rw [← hev x]
    show (wiresFrom acc.2 (List.ofFn x)).getD o false = (C.wires (List.ofFn x)).getD C.output false
    rw [← e1, ← hv]
    rfl


theorem erase_dead_mono (n : ℕ) (gs : List Gate) (o p : ℕ) (hcl : SCleanL n gs) (hmono : MonoL gs)
    (ho : o < n + gs.length) (hp : p < gs.length) (hne : n + p ≠ o)
    (hdead : ∀ (q : ℕ) (g : Gate), gs[q]? = some g → n + p ∉ g.inputs) :
    ∃ gs' o', gs'.length + 1 = gs.length ∧ SCleanL n gs' ∧ MonoL gs' ∧ o' < n + gs'.length ∧
      ∀ x, val gs' n o' x = val gs n o x := by
  let gs' := gs.take p ++ (gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩
  let o' := redir (n + p) o
  have hlen' : gs'.length + 1 = gs.length := by
    simp [gs']
    omega
  have ho' : o' < n + gs'.length := redir_lt (by omega) (by omega) (Ne.symm hne)
  have hcl' : SCleanL n gs' := by
    intro q g hqg
    by_cases hqp : q < p
    · have h1 : gs'[q]? = gs[q]? := by
        simp only [gs']
        rw [List.getElem?_append_left (by simp; omega)]
        exact List.getElem?_take_of_lt hqp
      rw [h1] at hqg
      exact hcl q g hqg
    · have hlt' : q < gs'.length := (List.getElem?_eq_some_iff.1 hqg).1
      have hq1 : q + 1 < gs.length := by omega
      have h1 : gs'[q]? = ((gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩)[q - p]? := by
        simp only [gs']
        rw [List.getElem?_append_right (by simp; omega)]
        simp [Nat.min_eq_left (Nat.le_of_lt hp)]
      rw [h1, List.getElem?_map, List.getElem?_drop] at hqg
      have hidx : p + 1 + (q - p) = q + 1 := by omega
      rw [hidx] at hqg
      obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hqg
      have hcl0 := hcl (q + 1) g0 hg0
      have hd0 := hdead (q + 1) g0 hg0
      rcases hcl0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hjk, hin⟩
      · refine Or.inl ⟨hop, redir (n + p) j, ?_, by simp [hin]⟩
        exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
      · refine Or.inr ⟨hop, redir (n + p) j, redir (n + p) k, ?_, ?_, ?_, by simp [hin]⟩
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · intro heq
          exact hjk (redir_inj (fun e => hd0 (by rw [hin]; simp [e]))
            (fun e => hd0 (by rw [hin]; simp [e])) heq)
  have hmono' : MonoL gs' := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hmono g (List.mem_of_mem_take hg)
    · obtain ⟨g₀,hg₀,rfl⟩ := List.mem_map.1 hg
      exact hmono g₀ (List.mem_of_mem_drop hg₀)
  refine ⟨gs', o', hlen', hcl', hmono', ho', ?_⟩
  intro x
  unfold val
  have hsplit : gs = gs.take p ++ gs[p] :: gs.drop (p + 1) := by
    calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
      _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hp]
  set w₁ := wiresFrom (gs.take p) (List.ofFn x)
  have lw₁ : w₁.length = n + p := by
    rw [length_wiresFrom]
    simp [Nat.min_eq_left (Nat.le_of_lt hp)]
  have hdead_post : ∀ g ∈ gs.drop (p + 1), w₁.length ∉ g.inputs := by
    intro g hg
    obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop] at hgk
    rw [lw₁]
    have hlt_k : p + 1 + k < gs.length := by simp at hk; omega
    exact hdead (p + 1 + k) g (by rw [List.getElem?_eq_getElem hlt_k, hgk])
  set b := gs[p].op.eval (gs[p].inputs.map fun i => w₁.getD i false)
  obtain ⟨u', hu1, hu2⟩ := wiresFrom_drop_dead w₁ b (gs.drop (p + 1)) [] hdead_post
  have heq1 : wiresFrom gs' (List.ofFn x) = w₁ ++ u' := by
    simp only [gs', wiresFrom_append]
    rw [← lw₁]
    simpa [w₁] using hu1
  have heq2 : wiresFrom gs (List.ofFn x) = w₁ ++ [b] ++ u' := by
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_cons]
    simpa [w₁, b] using hu2
  rw [heq1, heq2]
  show (w₁ ++ u').getD (redir (n + p) o) false = (w₁ ++ [b] ++ u').getD o false
  rw [← lw₁]
  exact getD_drop_wire w₁ u' b o (by rw [lw₁]; exact Ne.symm hne)


open Classical in
theorem run_live_mono (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs) (hmono : MonoL gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (fun a : BFn n => a) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
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
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
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
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hjk, hinp⟩
    · have hm := hmono g (List.mem_of_getElem? hg)
      rcases hm with hm | hm <;> rw [hop] at hm <;> cases hm
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
        intro a
        rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
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
      have IH' := Run.perm (hp2.map (val gs n)) IH
      have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
          then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
        funext x
        rw [hvg x, hinp]
        rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval, meetF, joinF]
      rw [List.map_cons, kept_map, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')


open Classical in
theorem exists_run_mono {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasMonoSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (fun a : BFn n => a) meetF joinF f s' ws := by
  have hex : ∃ m, ∃ gs o, gs.length = m ∧ SCleanL n gs ∧ MonoL gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
    obtain ⟨gs, o, hl, hcl, hm, ho, hev⟩ := exists_sclean_mono f hnc s h
    exact ⟨gs.length, gs, o, rfl, hcl, hm, ho, hev⟩
  set m := Nat.find hex
  have hm_le : m ≤ s := by
    obtain ⟨gs, o, hl, hcl, hm, ho, hev⟩ := exists_sclean_mono f hnc s h
    exact le_trans (Nat.find_min' hex ⟨gs, o, rfl, hcl, hm, ho, hev⟩) hl
  obtain ⟨gs, o, hlen, hcl, hmono, ho, hev⟩ := Nat.find_spec hex
  have hnd : ∀ p, p < gs.length → n + p = o ∨
      ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra! hbad
    obtain ⟨hne, hdead⟩ := hbad
    obtain ⟨gs', o', hlen', hcl', hmono', ho', hev'⟩ := erase_dead_mono n gs o p hcl hmono ho hp hne hdead
    have hlt : gs'.length < m := by omega
    exact Nat.find_min hex hlt ⟨gs', o', rfl, hcl', hmono', ho', fun x => (hev' x).trans (hev x)⟩
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
    exact run_live_mono n gs o hcl hmono ho hnd gs.length 0 (by omega)


abbrev MonoNatRun := Run (fun a : Nat => a) (· &&& ·) (· ||| ·)

theorem wheel_mono_run (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = wheel x) (hs : C.size ≤ 8) :
    ∃ s, s ≤ 8 ∧ ∃ ws : List (BFn 6),
      ws.Sublist (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)) ∧
      Run (fun a : BFn 6 => a) meetF joinF wheel s ws :=
  exists_run_mono wheel ⟨fun _ => false,fun _ => true,by decide⟩ 8 ⟨C,hmono,hs,hev⟩

theorem wheel_mono_encoded (rows : List ℕ) (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = wheel x) (hs : C.size ≤ 8) :
    ∃ s, s ≤ 8 ∧ ∃ zs : List ℕ,
      zs.Sublist ((List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map
        (fun a => encL a rows)) ∧ MonoNatRun (encL wheel rows) s zs := by
  obtain ⟨s,hs,ws,hsub,hrun⟩ := wheel_mono_run C hmono hev hs
  refine ⟨s,hs,ws.map (fun a => encL a rows),hsub.map _,?_⟩
  exact Run.map (fun a : BFn 6 => encL a rows) (fun _ => rfl)
    (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) hrun


abbrev MonRun := Run (fun a : Nat => a) (· &&& ·) (· ||| ·)

theorem bits_le {y s ws} (h : MonRun y s ws) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun a ha => hw a (hp.mem_iff.1 ha))
  | one save h ih =>
    apply ih
    intro a ha
    cases save <;> simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at ha
    · rcases ha with rfl | ha
      · exact hw _ List.mem_cons_self
      · exact hw _ (by simp [ha])
    · rcases ha with rfl | rfl | ha
      · exact hw _ List.mem_cons_self
      · exact hw _ List.mem_cons_self
      · exact hw _ (by simp [ha])
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;> grind
    · rcases (mem_kept ka _ _ _).1 ht with ⟨_, rfl⟩ | ht
      · exact ha
      · rcases (mem_kept kb _ _ _).1 ht with ⟨_, rfl⟩ | ht
        · exact hb
        · exact hw _ (by simp [ht])


def next (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := a
       f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
            (slack ≥ 2 && f (w :: a :: b :: r)))

theorem next_one {k a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : MonRun (goal k) s (a :: kept save a rest))
    (f : List Nat → Bool)
    (hf : ∀ ys, MonRun (goal k) s ys → f ys = true) :
    next (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  have ht := hf _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s + 2 - ws.length := by omega
    simp [ht, hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : MonRun (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, MonRun (goal k) s ys → f ys = true) :
    next (s + 2 - ws.length) ws f = true := by
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
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : MonRun (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, MonRun (goal k) s ys → f ys = true) :
    next (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : MonRun (goal k) t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, MonRun (goal k) s ys → f ys = true) →
      next (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k + i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : MonRun (goal k) s ws) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k + i) ≤ (goal k).testBit i := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k : Nat) (ws : List Nat) : Bool := covUp k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : MonRun (goal k) s ws) : covers k ws = true := by
  simp [covers, required_up h]

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o + a) = true) :
    span f (a + b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (T w h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if fld T w ((lo + hi) / 2) ≤ h then bsr T w h f ((lo + hi) / 2) hi
       else bsr T w h f lo ((lo + hi) / 2))
    else lo

def hw (w : Nat) : Nat := (w % 11400714819323198549 + 317) ^ 3 % 11400714819323198549 + 1

def hz : List Nat → Nat
  | [] => 0
  | w :: t => hw w + hz t

def hk (zs : List Nat) : Nat := hz zs % 4294967291

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def bar (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (s + 2 - ws.length) ws fun zs => covers k zs && !(found S N idx s zs))

theorem bar_sound {k S N idx} {s i : Nat} (hb : bar k S N idx s i = true)
    (h : MonRun (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, MonRun (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) := covers k zs && !(found S N idx s zs)
    have hF (zs) (hz : MonRun (goal k) s zs) : F zs = true := by
      simp only [F, covers_ok hz, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p hz)
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k S N idx} {cap : Nat}
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k S N idx s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ MonRun (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hh
    exact ih q hq (by omega) j hj h



theorem encoded_wheel_mono_exclusion (rows xs : List ℕ) (k : ℕ)
    (hinputs : (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map
      (fun a => encL a rows) = xs)
    (hgoal : encL wheel rows = goal k)
    (hproper : ∀ zs ∈ xs.sublists, zs ≠ xs → (covUp k zs &&& lo k) ≠ lo k)
    (hno : ∀ s ≤ 8, ¬ MonRun (goal k) s xs) :
    ¬ HasMonoSize 6 wheel 8 := by
  rintro ⟨C,hmono,hs,hev⟩
  obtain ⟨s,hs,zs,hsub,hr⟩ := wheel_mono_encoded rows C hmono hev hs
  rw [hinputs] at hsub
  rw [hgoal] at hr
  by_cases he : zs = xs
  · subst zs
    exact hno s hs hr
  · exact hproper zs (List.mem_sublists.2 hsub) he (required_up hr)

theorem wheel_lower_from_mono_exclusion (hno : ¬ HasMonoSize 6 wheel 8)
    (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6,
      (u.val,v.val) ∈ ([(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,5),(2,5),(3,5),(4,5)] : List (ℕ × ℕ)) ∧
      x u = true ∧ x v = true) : 9 ≤ C.size := by
  by_contra hs
  apply hno
  refine ⟨C,hmono,by omega,?_⟩
  intro x
  rw [Bool.eq_iff_iff,hev x,wheel_iff x]

def rowsG : List ℕ := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 3, 6, 12, 17, 24, 33, 34, 36, 40, 48, 3, 6, 12, 17, 24, 33, 34, 36, 40, 48, 3, 6, 12, 17, 24, 33, 34, 36, 40, 48, 3, 6, 12, 17, 24, 33, 34, 36, 40, 48, 3, 6, 12, 17, 24, 33, 34, 36, 40, 48, 3, 6, 12, 17, 24, 33, 34, 36, 40, 48]

def xsG : List ℕ := [0xa4290a4290a4290000000000fffff, 0x10c4310c4310c4300000fffff00000, 0x218862188621886003ff00000003ff, 0x45114451144511400000003ffffc00, 0x862188621886218003ffffc0000000, 0xf83e0f83e0f83e0ffc000000000000]

def NN : Nat → Nat
  | 4 => 15
  | 5 => 241
  | 6 => 313
  | 7 => 37
  | 8 => 1
  | _ => 0

def HT : Nat → Nat
  | 4 => 0xdd23db41d0e065cdc63c557dc10212bc9672e674866551737197011358331e59553b66e15308f15a38daf22d3454b27231683a3e2f90f94d2b3e4366
  | 5 => 0xfbe62072fba361d2fb3724cbf2a6feb3f22d691eeffad6b9efc17cbeee17beb7ee137fdbeb81e7a2eb4649c1eb259bece95520c9e6b309c7e665f896e38d74f7e37e074ae1e6c659e0e207c7df7cedeadd1e8126dc40ed12dafbb7fdd9a8b48cd9254bacd8d9f6fad8bf54bcd66d6eb4d5d1ceecd0f676e7d07e4e15d02e2596cd9eed2dcbffb0f5cbef0fa2cb85af7ecb416901c9c4c7afc831cb0ac61e04a8c53de200c47159f3c45196e7c3988d1fc34194e2c2928802c03167b0c0039f3fbff23585bfbf5eabbf423a0abe8597bcbdbfb856bdada02dbd7f929fbd658fabbd34bb60bbc48968bb4d941abb0f8468bad2b7ffb9acb6bfb73e6f5ab6f30b02b6989a04b68944adb4ec294eb1fea249b1ccc9f8b05f0a9fb0276158b00bd4d6aee9ad1bae6aae69ab768172ab1ea95ea91087f1a8e4282aa88676b8a87ec9faa878bf09a7f9b9f1a79d1d2da7456c41a69869a3a61f0821a5b1700fa3edef17a0fd1bfb9e4a1b389dc446649d46cb9699618ebd978a4dcc957472f794647a9c93aea4c3937825d991c371c69037b4c39025cd148f0503c08ddf65c38d2ff2ee8caa53288adf60dc8a2e5ef788793c91864ae80e863ad1da8616750584ab9d578434a29082d45c66807e7ce57ea73bf47e81a67f7cec1e737cb65e107ca1a82a7ba442497b5983eb7a89064f791819a178299fc57766f6cc773008af7699f891766dc5877664875f7538d9327310043c70a939e67051f0a3704f2bcb6e89c4816e4ec5436cad2bdc6c5e6d786bbbacf36b1908cf6a0c276c698fdc5568aef6ed6772faa566c99ee766a09cfc665dc08e65a692d763d34c3863b68a6c62f47a5862addf1b620b4fcf6152605e5ff8d5505fa1a8815f230b945dba43515cc6cb2d5bc9332a5ad40f5159badc0659995cbe590abc5c57fc12b354a7e6a354a34413520a7ddd5176cddd50e23230500e30bf4e1d59ef4d381e924a301032498d2bfd4934c3b248fdd59548851666473526ba465a59c545016de5421fbd8941b1828d40198f0e40001f953f5f3c813e28dea43d6c4a1e3cf2ab1a3c6ee0ea3b6952ac37dc7eb03380edaf3364cbd833563ef53345c9f230c4f4342ebfea3c2e62241e2dad32922a72cc2929cfedb529a5a96925a734f4251f69ae2354eee822fc6e4521e61d101f7bcadd1c3fe8bf1c08faa21bd5e9a01b7a7482190fa190179c2c86166f2df214e3388713c9fc2e13782fd512c3f711122000c9120ca7b411bfa8161169f4ee115c388f0f0c7cf60aa7c7b50a2d37a3092cfa63092940e10914e96c082995eb0629f1a205b2b9e60476779904157d5002c1eb15016d1761009ffb8d0023ec08
  | 6 => 0xff8e951dfc6f9e5ffbd72f85fa88cf5af9662d70f914e7edf8d2315ef76d6b6df766d289f7056b9af5d0439af423eb1df422851af361cf82f31fd052f2a6feb3f2a26d7befa8346eee137fdbee06f8fdeccd8c11ec59197eeb4649c1ea264460ea14b39ce986ce2fe896d4b5e85fe698e77c9063e572ac05e53b1a41e5183cb0e3ec282ae31e73b6e1f35344e1c4e065e171884ee15bd8c1de9d5272dd471f46dd1e8126da5ac943da25238bd8c8d98bd89848f9d85e7521d817ff3dd70b5091d6693c62d4c363cbd2cad8bdd18930d4d07e4e15cfd4145bce46a55acd4d1417cb85af7eca237151c98617e9c8272433c7c02730c75f707dc61e04a8c41b3b8bc34194e2c1bdbd7ebf49d241bf423a0abf23cf8abe26e664bdada02dbd610f9bbce7c90abcd33f6eba618532ba4b389fba1db18ab9acb6bfb8a61efcb675dd89b6365829b62e6ddab4ec294eb4104742b388cdcfb364a999b35565adb3054a4cb2bf2aa9b229e43bb220aed9b1ddcce9b1880113b12d1c57af81aee5af6deb41af429346ab1ea95ea9c1bf5aa69869a3a4f5eda9a47407a7a44ae482a226fdf1a0fd1bfba0dd7b71a0a604fca01e22ba9ec5c7909e907fc19d75e2049b6e70139848f016984868fc9847119a9810237d978febfe95e9185595413cfb94d2f25994c25c4c94647a9c9408b5d993eccb37937ad43a937825d993541db092fbb168925252ca91320b71902e47988ef768458c946b00891f3eb687601ca98650b20084bfdc8f8139d1337f9e042e7da3dd057cb65e107bbe005d7aaa4d4979f9ac007946bd8178b3a9f07827c1ac77cb2eb47766f6cc7699f891766163e47660399e751dbbea74a1666d743a65b5736d2b24730802a17160b9c870a939e6707437c570608f306f464ade6ebfef216cad2bdc6b57c57b6af039f86ac00b236a0c276c697ba2ee693fe464693c953e692d98d068ced64f66d3d24066a09cfc6603906e65ba64c76492167463d34c386299379e6298cddd629245cd60da9bcb608cd6555ff8d5505fb5e01a5f532b6d5f4d78e75db43cb15d99328d5d56de4f5d2a9af75cc6cb2d5c7efc405c355b735af448605aa70db458ba0bab579f0f625714ca40564ed0595592509c555bf761553e20d85486a3825359440c52c2cd3f50b56283500e30bf4f505d234e4a58064d00d5864c9619054b78da724b5d2f5c4b546e024b10102d4934c3b2490e3c0c48aa715c484276e4467c9155465a59c545cf514b45b5aed945b373b44402fa684368fe134206ad4a41f843e240001f953fbd527e3f5f3c813e28dea43de7baa73cf2ab1a3b3a3fc4395d654d393229813926773037eedd8336f0ab9135eb1fb835e6dd6535c4c60a354e2e3e33c788633345c9f2329fc2e431ef11ae30d9d75a30ad53c92f9df8d02ddf84a72cd901e02be282ce2bb15a072a9135ed29cbbe7e291c8553276cc12626bdb4182654bdf92607e0cc25a734f4253b008e2439643c242014652369480b2354eee8232f42eb22c3d99821e7c6b521875aac201f23c01e23f4101d479bc41c7c15981c3fe8bf1bf28e791ada73701901e35518b79b4e16de3ac0166f2df2164e09e314f3d43414bce6171498309a1412033b13fd1dbf12c159db11ed072a115c388f10d92e6010ba152e0ede5cbc0eceef180e86e8540d2785f90cd2a1fa0c9bb3dd0aa7c7b509b95403097b61d7083acf9807f9f7fa042368b603a10291034cda36031f3936026857a00113d542
  | 7 => 0xf766d289f361cf82f2a26d7be896d4b5e85fe698e77c9063d70b5091d2cad8bdca237151c8272433ba618532b675dd89b6365829b2bf2aa9a44ae482a226fdf1a0dd7b719847119a93eccb377bbe005d7827c1ac77cb2eb4766163e45d56de4f5359440c4d00d5864206ad4a395d654d37eedd83354e2e3e2354eee822c3d99814f3d43412c159db0e86e8540cd2a1fa031f3936
  | 8 => 0x2354eee8
  | _ => 0

def LT : Nat → Nat
  | 4 => 0x555555555555555
  | 5 => 0x6666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666
  | 6 => 0x7777777777777776776777677777777777777777677777777777677767777767677677677777767777677777777777777676777767777777777777777677767777777777777767777777667777777767777677767777776777677777677777776777777777777777677777777677776777777767667677777777777677777777777777776777767777777767777767777777767777777767777777777
  | 7 => 0x7777777777777777777777777777776777777
  | 8 => 0x6
  | _ => 0

def DT : Nat → Nat
  | 4 => 0x3894a8c4215c00007429518842980000e256210c63e00001c4c73d98c7c00003894a8431908000074b1d76741780000e254a31085300001c4c75d9e45e0000389768c2d0bc00007629508631f00000e2639d0c64300001e0c73a18c7c00003d5768c298bc0000712ed18531b00000e263aece833
  | 5 => 0x1d0a93a14c7c2f003894a89299247c0071294f6581f0bc00e2581d0a63e17801c4a9421d0a63e003b15874298f85e007129518742b8bc00e2529d0a64517801c4a53a14c902f003897474298f85e0071294e8581f0bc00f1529d0a63e17801f6e26894c7c2f003894a743514c5e0076294e8531f0d000e2551e4a63e17801d0a5461d0a62f003899c74298f85e00713094a741f0bc00e2529d0a64617801c4a5491d07c2f003894a7c298f85e0071314e8531f0bc00e963a94e83e17801eeee52a587c2f003895874318f85e00712953a531f0bc00f771348a63e17801c4bb3a1687c2f003894a74331247c0071294e85f298f800e252a50a63e17801c4a53a14c7c37003894a8c4214c160071294f4531f0bc00e2529d0ae3e17801c4a54794c7c2f003899aa53a0f85e00712952e741f0bc00e2529e0a63e17801c4ac4214c7c2f00389a4923a0f85e0071294e85e1f0bc00e2621d0be531f001c4ac3a14c7c2f003b9c4c43a0f85e0076294e853210bc00e2639eca63e17801c4c15aa94e82f003894a81298f85e0074294e8531f0bc00e252a4cbe531f001c4de529d07c2f003895474298f85e00773894a931f0bc00e2581d0a64817801c4a53a168882f003898c74298f85e0071380e8531f0bc00e2529eca64317801d6e252a24a62f003894a74298f86800712e0e853248f800e25ba94e85317801c4aa3a14c7c33003c14a7b298f85e0071294e853248f800f55d9d0a63e17801c4a53d98ca63e003894a73298f85e00712ece8531f0d800e260abd4a741f001c4d35294c7c2f003894a74310f85e007131d4a791f0bc00e2529d0a64317801c4a53a18c842f003ddc4a5490f85e00713314a74298bc00e252a30b43e17801c4da529d0a62f003b54a74298f85e0071294e85b1f0bc00e263aece82f08001e0a53a14c7c2f003896aaf529d0a600712f14a74298bc00f6529d0a63e17801c4a54014c7c2f0038962a53a14c7c0071294e86b1f0bc00e9529e4a63e17801eaa53a14c882f003894a74299106c00712950853210bc00e2529d0ba3e17801c4a5431f8e853003894a74299085e00793896074298f800e268b054a3e17801d6e2529d0cc2f003894a743614c7c00712952a741f0bc00f271294e85324001c4a53a14c7c35003894a743094c7c007dbc96674298f800e252a20e85317801c4d15aa94a62f003894a742992c5e007129512661f0bc00f552a30a63e17801c4a9461d0a62f003894a8c298f86c007aa94e85a1f0bc00e2529d0b43e1b001c4c7529d07c3300389b874298f85e0071294e853220bc00ee71294e85f1f001c4d43a14c7c2f003896ca53a14c5e00712f54a74298f800e252a38e8531f001c4a54194c7c2f003a54a74298f85e0074aed4a74298bc00e260a94e83e17801d6e25c1d0a62f00389a2af5294c7c007131ce8631f07000e2529d0b04317801c4a5431d0a62f003a54a74298f86600712c100531f0bc00f0529d0b03e17801c4a53c15c7c2f003896aa53a14c5e00712e112531f0bc00e252a00a64817801d4a53a14c7c2f003894a89298f85e00712ed18531788800e26ba94a63e17801d0a53a15c7c2f003894a8a298f85e0071294e865298bc00e252a6ce85317801d8a53a18c7c2f003894a742d0f85e00712c0e85d1f0bc00e2529d0a43e17801c4a43a14c7c2f003a14a78298f85e00713594a74298f800e2549d0a63e17801c4df5294c7c2f003894a742e9205e007129508742b8f800e257a94e8531f001c4ab3a14c7c2f003d54a74298f86c0071310e865298bc00e2561d0a63e1a001c4a53a1a07c2f00389a4863a14c5e00712952665298bc00e2529fce8531f001d8a54214c7c2f003a14a843a14c7c00712950474298f800ec529d0a63e17801c4a53a180a63e003894a74298f85c00712e4e8531f0bc00e2529d0a63d17801c4a53c94c7c2f0038976a53c94c5e007130d4a741f0bc00e264a94e8531f001c4a53f1d0a63e003894a84318f82c0071294f2531f0cc00e25c1d0cc3e17801e4e252a00a63e003d54a74298f85e0071294e8661f0bc00e2529d0a63e1b001c4b23a14c7c2f00389a2a5298f85e007bb894a86298bc00e2529d0a64a1f001c4c73a14c862f003c9c4a53a1747c00712b0e853210bc00f0639d0a63e17801c4a53d94c7c2f003c9d6a53a14c9800712b4e8531f0bc00f0529d0a64317801c4d23f1d0a63e003894a92431d05e0071294e853210d000e2529d0c65321801c4b83a14c7c2f003c14a743194c7c0071294e8531f0bc00fb71304e83e17801c4db5294c7c2f003894a99298f85e0071294e8531f0cc00e25da94e85319801c4d83a14c7c2f003b9d6a53a1a45e007db896a74298bc00e252a1ce85317801c4c43a14c7c2f003894a8d3a14c5e0071294e8652f94c00e252a60e8531f001dce2529d0ca2f003ddc4a53f14c7c0071295005d1f0bc00e9551d0a63e17801c4a53a1647c2f003894a93298f85e0071294e867298bc00e2691d0a63e17801f4a53a14c7c2f003894a8b298f85e007db895e74298f800e25f1d0a63e17801c4a93a15c7c2f003894a9c3a0f85e0075b894a742992400e26224ca63e17801c4ca3a14c7c2f003895278298f85e007dbddaa531f0bc00e264294e83e17801c4a5491f8e83e
  | 6 => 0x3896aa54f9d0a62f71294e8531f0bc12e2529d0a6511f0bdc4c7529d07c2f083894a80298f85e2971294e864298f85ee26ea94e8531f0bdc4a53d94c7c2f0e389c4a53a14c7c2f712a4e8531f0bc16e2529f8e86e298f9c4a53a14c7c2f03b8982a53a14c7c2f71294e8531f0bc08e2529d0a63e1788400e2581d0a63e17b894a743494c7c2f712bd4a9f3a14c7c0071294e853240bdc4a53c9d0a63e17b894a742e8f85e2974a94e8531f0bc200071294e8581f0bdc4bb3a14c7c2f11389aac73a14c7c2f7bbb94a74298f85ee2529d0a63e1f0bdc4bb529d0a63e17b894a74298f85e1c71294e865299345ee26ca94e8531f0bdc4a53a17ca63e17b894a74298f85e2571294e8531f0bc2ee2561d0a63e17859c4d1529d0a63e17bb9c4a54b1d07c2f71294e85a298f85ee252a30e8531782dc4a53a1c0a63e17801c4a5491d07c2f7eb894a74298f85ee252a8ce8531f0bdf0e2529d0a63e17bddc4a54614c7c2f71294e8531f0d02ce2529ece8531f0bde4e2529d0a63e17b894a74298f85e0f71294e8531f0bc3ce2529d0dc531f0bdc4a53a14c882f11001c4a53a17ca63e713454a9f298f85ee2529d0a63e1a0bddee2529d0a63e17801c4a53a15c7c2f712950874298f85ee2529d0a6491f0bdc4a53a1d0a63e17b894a74298f85e2a7cb894a74298f85e0071294f0531f0bdc4a5481d0a63e17801c4ac3a14c7c2f71294e8531f0bc18fb7ba94e8531f0bc00e8529d0a63e17bedc4b33a14c7c2f71294f2531f0bc2000712a8e8531f0bdc4a53a14c7c3017b894a743314c7c2f7129518531f0bc44e2529d0a63e1782dc4a53a14c7c2f16b89a4743714c7c2f003894a74298f868e2529d0b43e17889c4a53a18ca63e17b894a9f3a14c7c2f712952674298f85e0071294e853248f9e4e2529d0a64c1f3894a74298f85e1b71294e853200f85ee2529d0a6481f0bdc4a9529d0a63e17b894a74298f85e0171294e853210bc2ce2529d0a64f1f0bde4e259a94e8531f3894a74298f85e2371294e8531f0bc4efb7131ce8531f0bdc4a53a1607c2f0e3b9c4c7529d07c2f003894a742990c5ee2529d0a63e1786000f0529d0a63e17b8966a5421d0a63e71294e8531f0bc34e2529d0a63e17821c4a53a14c9a3e17801c4a54014c7c2f71294e853298f85ee2529d0ac531f0bdc4a53a14c923e1c3b9c4a53a1a47c2f7bb894a6e298f85ee268294e8531f0bdc4a53b1d0a63e17b894a74298f85e037a3894a74298f85ee2529d0a63e17841c4bb529d0a62f083898ea54b1d07c2f7bb894a84298f85ee2621d0a64d1f0bdeaa53a14c7c2f113edc4bb3a14c7c2f003894a742e8f85ee267a94e8531f0bdeee2529d0a63e17b894a743194c983e003894a74299085ee871294e8531f0bdc4a53a14c7c36113894a74298f8642f71294e8531f0cc20e252a4ca64d1f0bddceb529d0a63e17b894a923a1b87c2f71294e8531f0bc0b0071294e8531f0bdc4a53a14c7c2f1338976b33a14c7c2f71294e8531f0e85ee252a84e8531f0bdc4a53a14c7c2f08801c4a53a14c882f71294e8531f0bc52f071294e8531f0bdc4a54b230a63e17b894a7d3a14c7c2f712e14a74298f85ee2529d0a63e17889c4a53a14c7c2f01001d2a53a14c7c2f0038982a53a0f85ee252a94e8531f0bdc4a53a14c7c2f0a3898ebb3a14c7c2f71294e8531f0bc2ae2639d0a63e17871c4a53a14c7c2f093894a743694c7c2f712bd4a74298f85e00712950c74298bdc4cb529d0a63e17b894a742990c7c2f71294e853218bc38ec529d0a63e1785800e25aa94e85317b8968a53a14c7c2f71294f074298f85ef0529d0a63e1787000e252a24a63e17b8988a53a14c7c2f793894a843a14c7ce2529d0b8531f0bdc4a53a14c7c2f123894a742c14c7c2f71294e8531f0e45e0071294e865298bdc4a53a18ca63e0e3adc4a53a14c982f71294e86f298f85e0071294e85a1f0bddce2529d0c63e17bedc49f3a14c7c2f71294e8571f0bc16fe71294e8531f0bde6e2529d0a63e17801c4a93a14c7c2f71294e8531f0ec5ee26aa9508531f0bdd6e2529d0a63817b89a4a53a14c7c2f75b894a8c3a14c5ee26aa94e8531f0bdc4a53c14c7c2f05801c4af529d0a63e71294e853270f85efc71294e8531f0bdc4a53f1d0a63e17b894a923a14c7c2f71294e853210f85ee2529d0c63e17859c4a53a14c8e3e17ba14a74298f85e0b793894a743194c7ce2529d0a63e1e0bdc4a54494c7c3817b894a74298f85e1971294e8531f0bc0ce2529d0a63e1b0bdc4a53a14c7c2f06801d8a53a14c7c2f71294e85f299347cee71294e84d1f0bddce2529d0a63e17b894a843a14c7c0b74b894a74298f85ee2529d0a63e178a1c8e2529d0a63e17b896074298f85e29003894a79298f85ee2529d0ae531f0bdc4a5421d0c6531f3894a853a14c7c2f71294e853240bc520071294fc74298f9c4a5401d0a63e17b894a913a14c7c2f712c14a74298f85ee252a10a63e17859d6e2529d0d25317b894a74298f85e1671294e853220f85e007aa94e8531f0bdc4a53a150a63e17801c4a53a1987c2f003894a74298f86ce2529d0a63e178b000e268a94a63e17b895ca53a14c7c2f75b894a74298f85eff71294e8531f0bdd6e25da94e85317b894a74298f85e2f71294e8531f0bc1ce252a18e8531f0bdc4bf529d0a63e17b894a743914c7c2f712952c74298f85ee2529d0a63e1787c00e2529eca63e17b895474298f85e10712d54a74298f85ee2529d0a63e198bdc4a54d1d0a63e17b894a743894c7c2f7129d4a74298f85ee771294e8531f0bdc4a53a194a63e17b894a74298f85e1d71294e8661f0e05ee2529d0a63e17829eee26aa94a63e17b894a742a94c7c2f712a14a74298f85ee2529d0a6501f0bdc4a5501d0a63e17801c4b83a14c7c2f71294e8531f0bc00e252a88e8531f0bdd8e2529d0a63e17b894a74298f85e13003894a74298f85ee2529d0a63f1f0bdf6e2529d0a63e17b8dc4a53a14c7c2f71294e8531f0c45ee252a18e86e298bdc4a6529d0a63e17b894a773a14c7c2f713014a74298f85e0071294e8531f0cdc4a53a14c7c2f103c9c4a53a14c7c29793ad4a74298f85ee263a94e8631f0bdc4a5461d0d25317801c4c43a14c7c2f712b14a74298f85ee2529d0a64c1f0bdc4bb529d0a64c17b99c4a53a14c7c2f7ab894a74298f85ee252a78e8531f0bdc4b3529d0a63e17b894a742e94c7c2f003894a93298f85ee25c1d0a63e1c0bdc4aa529d0a63e17b894a893a14c7c2f712951884298f85ee2529d0a63e1c0bdcae2529d0a63e17b894a8c3a14c7c2f712ed4a8c3a14c5e0071348e8531f0bdf6e26a9d0a63e17b8982a54f9d07c2f71294e869318f85ee2529d0a63e178adc4e1529d0a63e17b894a74299047c2f71294ea74298f85ee263a94e8531f0bdf6f2529d0a63e17bddc4a54b14c7c2f
  | 7 => 0x389c4a53a14c7c2f71294e8531f0bc08e2529d0d2531f0bdc4a53a14c7c3e17b8976a53a14c7c2f71294e8531f0bc38f271294e8531f0bdc4a53a1b8a63e17b894a843a14c7c2f71294e874298f85ee2529d0a63e1782dc4a53a18ca63e17b894a9f3a14c7c2f71294e8531f0bc02e2529d0a63e17821c4a53a14c9a3e17b894a742994c7c2f71294e8531f0bc20f771294e8531f0bdc4a53a14c7c2f14b894a74298f85e2271294e8531f0bc04e252a94e8531f0bdc4d5529d0a63e17b894a74298f85e06773894a74298f85ee2529d0a63e17859d6e2529d0a63e17b894a74298f85e2f712952c74298f85e0071294e8531f0bdf6e2529d0a63e17b894a74299307c2f712cd4a74298f85ee2529d0a63e1c0bdc4a5461d0a63e17b898ea53a14c7c2f
  | 8 => 0x1c4a53a14c7c2f
  | _ => 0

def VT : Nat := 0xffbfeffbfeffbfefffffffc00003ffff7fdff7fdff7fdffc00003fffffffff3fcff3fcff3fcffffffffffffc00feffbfeffbfeffbffffffffff00000fe7f9fe7f9fe7f9fffffffc00ffffffe3f8fe3f8fe3f8fffffffc0000000fe3f8fe3f8fe3f8ffc000000000000fdff7fdff7fdff7ffc00fffffffc00fdbf6fdbf6fdbf6fffff003ffffffffd3f4fd3f4fd3f4ffc00003ffffc00fd3f4fd3f4fd3f4ffc000000000000fc3f0fc3f0fc3f0ffc000000000000fbfeffbfeffbfeffffff00000ffffffafebfafebfafebffc00fffffffffffa7e9fa7e9fa7e9ffc0000000ffffffa7e9fa7e9fa7e9ffc000000000000fa3e8fa3e8fa3e8ffc000000000000f9fe7f9fe7f9fe7ffffffffff003fff9be6f9be6f9be6fffff00000003fff9be6f9be6f9be6ffc000000000000f93e4f93e4f93e4ffc000000000000f8fe3f8fe3f8fe3ffc00fffff00000f8fe3f8fe3f8fe3ffc000000000000f8be2f8be2f8be2ffc000000000000f87e1f87e1f87e1ffc000000000000f83e0f83e0f83e0fffff0000000000f83e0f83e0f83e0ffc00ffc0000000f83e0f83e0f83e0ffc00003ff00000f83e0f83e0f83e0ffc0000000ffc00f83e0f83e0f83e0ffc0000000003fff83e0f83e0f83e0ffc000000000000e7b9ee7b9ee7b9e003ffffffffffffe6398e6398e6398003ffffc0000000e5394e5394e539400000003ffffc00e1b86e1b86e1b86003ff00000003ffd7f5fd7f5fd7f5f003fffffffffc00d6358d6358d6358003ffffc0000000d5354d5354d535400000003ffffc00d0f43d0f43d0f4300000fffff00000cf73dcf73dcf73d003ffffffffffffce338ce338ce338003ffffc0000000cd334cd334cd33400000003ffffc00ca729ca729ca7290000000000fffffc731cc731cc731c003fffffffffc00c731cc731cc731c003ffffc0000000c731cc731cc731c00000003ffffc00c6318c6318c6318003ffffc0000000c5314c5314c531400000003ffffc00c0300c0300c0300000000000000000b7edfb7edfb7edf003fffffff003ffb62d8b62d8b62d8003ffffc0000000b1ac6b1ac6b1ac6003ff00000003ffb0ec3b0ec3b0ec300000fffff00000afebfafebfafebf003ffffc00fffffae2b8ae2b8ae2b8003ffffc0000000aa6a9aa6a9aa6a90000000000fffffa9aa6a9aa6a9aa6003ff00000003ffa7a9ea7a9ea7a9e003ffffc00003ffa729ca729ca729c003ffffc0000000a6a9aa6a9aa6a9a003ffffc0000000a6298a6298a6298003ffffc0000000a5a96a5a96a5a96003ff00000003ffa3a8ea3a8ea3a8e003ff00000003ffa1a86a1a86a1a86003ff00000003ffa0280a0280a02800000000000000009ee7b9ee7b9ee7b003ffffffffffff9e2789e2789e278003ffffc00000009a6699a6699a6690000000000fffff98e6398e6398e6300000fffff0000096e5b96e5b96e5b003fffffff0000096a5a96a5a96a5a003ffffc0000000966599665996659003ffffc0000000962589625896258003ffffc000000094e5394e5394e5300000fffff0000092e4b92e4b92e4b00000fffff0000090e4390e4390e4300000fffff000009024090240902400000000000000008e6398e6398e639003ffffc00fffff8e6398e6398e639003ffffc00000008e6398e6398e6390000000000fffff8e2388e2388e238003ffffc00000008a6298a6298a6290000000000fffff88220882208822000000000000000087a1e87a1e87a1e003ffffc00000008721c8721c8721c003ffffc000000086e1b86e1b86e1b003ffffc000000086a1a86a1a86a1a003ffffc0000000866198661986619003ffffc0000000862188621886218003fffffff00000862188621886218003ffffc00ffc00862188621886218003ffffc00003ff862188621886218003ffffc0000000862188621886218000000000000000842108421084210000000000000000822088220882208000000000000000802008020080200003ff000000000080200802008020000000ffc000000080200802008020000000000000000075dd775dd775dd7003ffffffffffff751d4751d4751d400000003ffffc00719c6719c6719c6003ff00000003ff70dc370dc370dc300000fffff000006fdbf6fdbf6fdbf003ff003fffffff6d1b46d1b46d1b400000003ffffc006a5a96a5a96a5a90000000000fffff699a6699a6699a6003ff00000003ff659966599665996003ff003fffffff659966599665996003ff00000003ff65996659966599600000003ffffc0065194651946519400000003ffffc00619866198661986003ff00000003ff6018060180601800000000000000005fd7f5fd7f5fd7f00000ffffffffff5d1745d1745d17400000003ffffc005a5695a5695a5690000000000fffff58d6358d6358d6300000fffff0000055d5755d5755d5700000fffffffc0055956559565595600000003ffffc0055555555555555500000003ffffc0055154551545515400000003ffffc0054d5354d5354d5300000fffff0000051d4751d4751d4700000fffff0000050d4350d4350d4300000fffff000005014050140501400000000000000004f53d4f53d4f53d00000003fffffff4f13c4f13c4f13c00000003ffffc004e5394e5394e5390000000000fffff4d5354d5354d53500000003ffffc004d1344d1344d13400000003ffffc004b52d4b52d4b52d0000000000fffff4a5294a5294a5290000000000fffff4812048120481200000000000000004751d4751d4751d00000003ffffc004711c4711c4711c00000003ffffc0045d1745d1745d1700000003ffffc0045916459164591600000003ffffc0045515455154551500000003ffffc00451144511445114003ff003ffffc0045114451144511400000fffffffc0045114451144511400000003fffffff45114451144511400000003ffffc0045114451144511400000000000000044110441104411000000000000000041104411044110400000000000000040100401004010000000003ff000004010040100401000000000000ffc004010040100401000000000000000003bcef3bcef3bcef003ffffffffffff3a4e93a4e93a4e90000000000fffff398e6398e6398e6003ff00000003ff38ce338ce338ce300000fffff0000031cc731cc731cc7003fffffff003ff31cc731cc731cc7003ff00000003ff31cc731cc731cc700000fffff00000318c6318c6318c6003ff00000003ff30cc330cc330cc300000fffff00000300c0300c0300c00000000000000002bcaf2bcaf2bcaf003ff00000fffff2b8ae2b8ae2b8ae003ff00000003ff2b4ad2b4ad2b4ad0000000000fffff2acab2acab2acab0000000000fffff2a4a92a4a92a4a90000000000fffff29ca729ca729ca7003ff00000003ff298a6298a6298a6003ff00000003ff280a0280a0280a00000000000000002789e2789e2789e003ff00000003ff258962589625896003ff00000003ff23c8f23c8f23c8f003ff00000003ff2388e2388e2388e003ff00000003ff21c8721c8721c87003ff00000003ff218862188621886003ffffc00003ff218862188621886003ff003ff003ff218862188621886003ff00000fffff218862188621886003ff00000003ff218862188621886000000000000000210842108421084000000000000000208822088220882000000000000000200802008020080003ff00000000002008020080200800000000000003ff2008020080200800000000000000001ac6b1ac6b1ac6b00000ffffffffff1ac6b1ac6b1ac6b00000fffff000001ac6b1ac6b1ac6b0000000000fffff1a4691a4691a4690000000000fffff18c6318c6318c6300000fffff0000018060180601806000000000000000016c5b16c5b16c5b00000fffff0000015c5715c5715c5700000fffff0000014c5314c5314c5300000fffff0000012c4b12c4b12c4b00000fffff0000011c4711c4711c4700000fffff0000010c4310c4310c43003fffffff0000010c4310c4310c4300000fffffffc0010c4310c4310c4300000fffff003ff10c4310c4310c4300000fffff0000010c4310c4310c4300000000000000010842108421084200000000000000010441104411044100000000000000010040100401004000000ffc000000010040100401004000000003ff000001004010040100400000000000000000f43d0f43d0f43d0000000000fffff0e4390e4390e4390000000000fffff0bc2f0bc2f0bc2f0000000000fffff0b42d0b42d0b42d0000000000fffff0ac2b0ac2b0ac2b0000000000fffff0a4290a4290a429003ff00000fffff0a4290a4290a42900000ffc00fffff0a4290a4290a42900000003fffffff0a4290a4290a4290000000000fffff0a4290a4290a4290000000000000000a0280a0280a0280000000000000000842108421084210000000000000000802008020080200000000000ffc000802008020080200000000000003ff080200802008020000000000000000060180601806018000000000000000050140501405014000000000000000040100401004010003ff000000000004010040100401000000ffc000000004010040100401000000003ff000000401004010040100000000000ffc00040100401004010000000000000000024090240902409000000000000000020080200802008003ff000000000002008020080200800000ffc00000000200802008020080000000000ffc000200802008020080000000000003ff020080200802008000000000000000018060180601806000000000000000010040100401004003ff000000000001004010040100400000003ff000000100401004010040000000000ffc000100401004010040000000000003ff01004010040100400000000000000000c0300c0300c03000000000000000008020080200802003ff000000000000802008020080200000ffc000000000802008020080200000003ff000000080200802008020000000000003ff00802008020080200000000000000000401004010040100000ffc000000000401004010040100000003ff000000040100401004010000000000ffc000040100401004010000000000003ff004010040100401000000000000000000000000000000003ffffc0000000000000000000000003ff00000003ff000000000000000003ff000000000000000000000000000000fffff0000000000000000000000000ffc000000000000000000000000000003ffffc0000000000000000000000003ff000000000000000000000000000000fffff0000000000000000000000000ffc000000000000000000000000000003ff000000000000000000000000000000

def S (s j : Nat) : List Nat :=
  (List.range (fld (LT s) 4 j)).map (fun t => fld VT 120 (fld (DT s) 9 (7*j+t)))

def idx (s : Nat) (zs : List Nat) : Nat := bsr (HT s) 32 (hk zs) 12 0 (NN s)

def Z (s : Nat) := bar 60 S NN idx s

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel

theorem enc_goalG : encL wheel rowsG = goal 60 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (covUp 60 zs &&& lo 60) ≠ lo 60 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x0 : span (Z 4) 8 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h4x8 : span (Z 4) 7 8 = true := by decide +kernel
theorem z4 : span (Z 4) 15 0 = true := (@span_join (Z 4) 8 0 7 h4x0 h4x8)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x0 : span (Z 5) 8 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x8 : span (Z 5) 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x16 : span (Z 5) 8 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x24 : span (Z 5) 8 24 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x32 : span (Z 5) 8 32 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x40 : span (Z 5) 8 40 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x48 : span (Z 5) 8 48 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x56 : span (Z 5) 8 56 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x64 : span (Z 5) 8 64 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x72 : span (Z 5) 8 72 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x80 : span (Z 5) 8 80 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x88 : span (Z 5) 8 88 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x96 : span (Z 5) 8 96 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x104 : span (Z 5) 8 104 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x112 : span (Z 5) 8 112 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x120 : span (Z 5) 8 120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x128 : span (Z 5) 8 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x136 : span (Z 5) 8 136 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x144 : span (Z 5) 8 144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x152 : span (Z 5) 8 152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x160 : span (Z 5) 8 160 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x168 : span (Z 5) 8 168 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x176 : span (Z 5) 8 176 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x184 : span (Z 5) 8 184 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x192 : span (Z 5) 8 192 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x200 : span (Z 5) 8 200 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x208 : span (Z 5) 8 208 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x216 : span (Z 5) 8 216 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x224 : span (Z 5) 8 224 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x232 : span (Z 5) 8 232 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h5x240 : span (Z 5) 1 240 = true := by decide +kernel
theorem z5 : span (Z 5) 241 0 = true := (@span_join (Z 5) 120 0 121 (@span_join (Z 5) 56 0 64 (@span_join (Z 5) 24 0 32 (@span_join (Z 5) 8 0 16 h5x0 (@span_join (Z 5) 8 8 8 h5x8 h5x16)) (@span_join (Z 5) 16 24 16 (@span_join (Z 5) 8 24 8 h5x24 h5x32) (@span_join (Z 5) 8 40 8 h5x40 h5x48))) (@span_join (Z 5) 32 56 32 (@span_join (Z 5) 16 56 16 (@span_join (Z 5) 8 56 8 h5x56 h5x64) (@span_join (Z 5) 8 72 8 h5x72 h5x80)) (@span_join (Z 5) 16 88 16 (@span_join (Z 5) 8 88 8 h5x88 h5x96) (@span_join (Z 5) 8 104 8 h5x104 h5x112)))) (@span_join (Z 5) 64 120 57 (@span_join (Z 5) 32 120 32 (@span_join (Z 5) 16 120 16 (@span_join (Z 5) 8 120 8 h5x120 h5x128) (@span_join (Z 5) 8 136 8 h5x136 h5x144)) (@span_join (Z 5) 16 152 16 (@span_join (Z 5) 8 152 8 h5x152 h5x160) (@span_join (Z 5) 8 168 8 h5x168 h5x176))) (@span_join (Z 5) 32 184 25 (@span_join (Z 5) 16 184 16 (@span_join (Z 5) 8 184 8 h5x184 h5x192) (@span_join (Z 5) 8 200 8 h5x200 h5x208)) (@span_join (Z 5) 16 216 9 (@span_join (Z 5) 8 216 8 h5x216 h5x224) (@span_join (Z 5) 8 232 1 h5x232 h5x240)))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x0 : span (Z 6) 8 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x8 : span (Z 6) 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x16 : span (Z 6) 8 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x24 : span (Z 6) 8 24 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x32 : span (Z 6) 8 32 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x40 : span (Z 6) 8 40 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x48 : span (Z 6) 8 48 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x56 : span (Z 6) 8 56 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x64 : span (Z 6) 8 64 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x72 : span (Z 6) 8 72 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x80 : span (Z 6) 8 80 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x88 : span (Z 6) 8 88 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x96 : span (Z 6) 8 96 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x104 : span (Z 6) 8 104 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x112 : span (Z 6) 8 112 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x120 : span (Z 6) 8 120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x128 : span (Z 6) 8 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x136 : span (Z 6) 8 136 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x144 : span (Z 6) 8 144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x152 : span (Z 6) 8 152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x160 : span (Z 6) 8 160 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x168 : span (Z 6) 8 168 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x176 : span (Z 6) 8 176 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x184 : span (Z 6) 8 184 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x192 : span (Z 6) 8 192 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x200 : span (Z 6) 8 200 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x208 : span (Z 6) 8 208 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x216 : span (Z 6) 8 216 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x224 : span (Z 6) 8 224 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x232 : span (Z 6) 8 232 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x240 : span (Z 6) 8 240 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x248 : span (Z 6) 8 248 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x256 : span (Z 6) 8 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x264 : span (Z 6) 8 264 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x272 : span (Z 6) 8 272 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x280 : span (Z 6) 8 280 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x288 : span (Z 6) 8 288 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x296 : span (Z 6) 8 296 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x304 : span (Z 6) 8 304 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h6x312 : span (Z 6) 1 312 = true := by decide +kernel
theorem z6 : span (Z 6) 313 0 = true := (@span_join (Z 6) 160 0 153 (@span_join (Z 6) 80 0 80 (@span_join (Z 6) 40 0 40 (@span_join (Z 6) 16 0 24 (@span_join (Z 6) 8 0 8 h6x0 h6x8) (@span_join (Z 6) 8 16 16 h6x16 (@span_join (Z 6) 8 24 8 h6x24 h6x32))) (@span_join (Z 6) 16 40 24 (@span_join (Z 6) 8 40 8 h6x40 h6x48) (@span_join (Z 6) 8 56 16 h6x56 (@span_join (Z 6) 8 64 8 h6x64 h6x72)))) (@span_join (Z 6) 40 80 40 (@span_join (Z 6) 16 80 24 (@span_join (Z 6) 8 80 8 h6x80 h6x88) (@span_join (Z 6) 8 96 16 h6x96 (@span_join (Z 6) 8 104 8 h6x104 h6x112))) (@span_join (Z 6) 16 120 24 (@span_join (Z 6) 8 120 8 h6x120 h6x128) (@span_join (Z 6) 8 136 16 h6x136 (@span_join (Z 6) 8 144 8 h6x144 h6x152))))) (@span_join (Z 6) 80 160 73 (@span_join (Z 6) 40 160 40 (@span_join (Z 6) 16 160 24 (@span_join (Z 6) 8 160 8 h6x160 h6x168) (@span_join (Z 6) 8 176 16 h6x176 (@span_join (Z 6) 8 184 8 h6x184 h6x192))) (@span_join (Z 6) 16 200 24 (@span_join (Z 6) 8 200 8 h6x200 h6x208) (@span_join (Z 6) 8 216 16 h6x216 (@span_join (Z 6) 8 224 8 h6x224 h6x232)))) (@span_join (Z 6) 40 240 33 (@span_join (Z 6) 16 240 24 (@span_join (Z 6) 8 240 8 h6x240 h6x248) (@span_join (Z 6) 8 256 16 h6x256 (@span_join (Z 6) 8 264 8 h6x264 h6x272))) (@span_join (Z 6) 16 280 17 (@span_join (Z 6) 8 280 8 h6x280 h6x288) (@span_join (Z 6) 8 296 9 h6x296 (@span_join (Z 6) 8 304 1 h6x304 h6x312))))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x0 : span (Z 7) 8 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x8 : span (Z 7) 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x16 : span (Z 7) 8 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x24 : span (Z 7) 8 24 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x32 : span (Z 7) 5 32 = true := by decide +kernel
theorem z7 : span (Z 7) 37 0 = true := (@span_join (Z 7) 16 0 21 (@span_join (Z 7) 8 0 8 h7x0 h7x8) (@span_join (Z 7) 8 16 13 h7x16 (@span_join (Z 7) 8 24 5 h7x24 h7x32)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x0 : span (Z 8) 1 0 = true := by decide +kernel
theorem z8 : span (Z 8) 1 0 = true := h8x0

theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · simp [NN]
  · simp [NN]
  · simp [NN]
  · simp [NN]
  · intro i hi
    exact span_ok z4 i (Nat.zero_le i) (by simpa [NN] using hi)
  · intro i hi
    exact span_ok z5 i (Nat.zero_le i) (by simpa [NN] using hi)
  · intro i hi
    exact span_ok z6 i (Nat.zero_le i) (by simpa [NN] using hi)
  · intro i hi
    exact span_ok z7 i (Nat.zero_le i) (by simpa [NN] using hi)
  · intro i hi
    exact span_ok z8 i (Nat.zero_le i) (by simpa [NN] using hi)

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : MonRun (goal 60) s xsG) : False := by
  have hl := run_len h
  have hlen : xsG.length = 6 := by decide +kernel
  rw [hlen] at hl
  have hlo : 5 ≤ s := by omega
  interval_cases s
  · exact bar_all checked 5 (by decide) 34 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 5 34)) h)
  · exact bar_all checked 6 (by decide) 43 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 6 43)) h)
  · exact bar_all checked 7 (by decide) 6 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 7 6)) h)
  · exact bar_all checked 8 (by decide) 0 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 8 0)) h)

theorem no_small : ¬ HasMonoSize 6 wheel 8 :=
  encoded_wheel_mono_exclusion rowsG xsG 60 enc_inputsG enc_goalG proper_failG noRunFull

end PEqualNP.Outside.L_meta_719_aux

theorem PEqualNP.Outside.L_meta_719 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 5), (2, 5), (3, 5), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 9 ≤ C.size := by
  intro C hm hev
  exact PEqualNP.Outside.L_meta_719_aux.wheel_lower_from_mono_exclusion PEqualNP.Outside.L_meta_719_aux.no_small C hm hev
