import Mathlib
import PEqualNP.Defs

-- Generic Run normalization adapted from Digger-Rockwell PR801, Apache-2.0.
-- Source commit ea90309308dd46a22d4a469766e46dd63f4484d0.
-- Monotone preservation, directed coverage, and this finite certificate are new.


namespace PEqualNP.Outside.L_meta_740_aux

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


abbrev cube : BFn 8 := fun x : Fin 8 → Bool =>
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 4) || (x 1 && x 3) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)

set_option synthInstance.maxSize 100000 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cube_iff (x : Fin 8 → Bool) :
    cube x = true ↔ ∃ u v : Fin 8,
      (u.val,v.val) ∈ ([(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)] : List (ℕ × ℕ)) ∧
      x u = true ∧ x v = true := by
  revert x
  decide +kernel

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

theorem cube_mono_run (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = cube x) (hs : C.size ≤ 10) :
    ∃ s, s ≤ 10 ∧ ∃ ws : List (BFn 8),
      ws.Sublist (List.ofFn fun (i : Fin 8) => (fun x : Fin 8 → Bool => x i)) ∧
      Run (fun a : BFn 8 => a) meetF joinF cube s ws :=
  exists_run_mono cube ⟨fun _ => false,fun _ => true,by decide⟩ 10 ⟨C,hmono,hs,hev⟩

theorem cube_mono_encoded (rows : List ℕ) (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = cube x) (hs : C.size ≤ 10) :
    ∃ s, s ≤ 10 ∧ ∃ zs : List ℕ,
      zs.Sublist ((List.ofFn fun (i : Fin 8) => (fun x : Fin 8 → Bool => x i)).map
        (fun a => encL a rows)) ∧ MonoNatRun (encL cube rows) s zs := by
  obtain ⟨s,hs,ws,hsub,hrun⟩ := cube_mono_run C hmono hev hs
  refine ⟨s,hs,ws.map (fun a => encL a rows),hsub.map _,?_⟩
  exact Run.map (fun a : BFn 8 => encL a rows) (fun _ => rfl)
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



theorem encoded_cube_mono_exclusion (rows xs : List ℕ) (k : ℕ)
    (hinputs : (List.ofFn fun (i : Fin 8) => (fun x : Fin 8 → Bool => x i)).map
      (fun a => encL a rows) = xs)
    (hgoal : encL cube rows = goal k)
    (hproper : ∀ zs ∈ xs.sublists, zs ≠ xs → (covUp k zs &&& lo k) ≠ lo k)
    (hno : ∀ s ≤ 10, ¬ MonRun (goal k) s xs) :
    ¬ HasMonoSize 8 cube 10 := by
  rintro ⟨C,hmono,hs,hev⟩
  obtain ⟨s,hs,zs,hsub,hr⟩ := cube_mono_encoded rows C hmono hev hs
  rw [hinputs] at hsub
  rw [hgoal] at hr
  by_cases he : zs = xs
  · subst zs
    exact hno s hs hr
  · exact hproper zs (List.mem_sublists.2 hsub) he (required_up hr)

theorem cube_lower_from_mono_exclusion (hno : ¬ HasMonoSize 8 cube 10)
    (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8,
      (u.val,v.val) ∈ ([(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)] : List (ℕ × ℕ)) ∧
      x u = true ∧ x v = true) : 11 ≤ C.size := by
  by_contra hs
  apply hno
  refine ⟨C,hmono,by omega,?_⟩
  intro x
  rw [Bool.eq_iff_iff,hev x,cube_iff x]

def rowsG : List ℕ := [24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 105, 105, 105, 105, 105, 105, 105, 105, 105, 105, 105, 105, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 150, 150, 150, 150, 150, 150, 150, 150, 150, 150, 150, 150, 3, 5, 10, 12, 17, 34, 48, 68, 80, 136, 160, 192, 3, 5, 10, 12, 17, 34, 48, 68, 80, 136, 160, 192, 3, 5, 10, 12, 17, 34, 48, 68, 80, 136, 160, 192, 3, 5, 10, 12, 17, 34, 48, 68, 80, 136, 160, 192, 3, 5, 10, 12, 17, 34, 48, 68, 80, 136, 160, 192, 3, 5, 10, 12, 17, 34, 48, 68, 80, 136, 160, 192]

def xsG : List ℕ := [0x13013013013013013000ffffff000000000, 0x25025025025025025fff000000fff000000, 0x8a08a08a08a08a08afff000000000fff000, 0x20c20c20c20c20c20c000000fff000000fff, 0x150150150150150150fff000000000000fff, 0x460460460460460460000000fff000fff000, 0x980980980980980980000000ffffff000000, 0xe00e00e00e00e00e00ffffff000000000000]

def NN : Nat → Nat
  | 7 => 509
  | 8 => 560
  | 9 => 55
  | 10 => 1
  | _ => 0

def HT : Nat → Nat
  | 7 => 0xfffac911ffd50852fefecf3efee7af0bfd2b7d8dfbec626ffba322fafaca4575fa46bc7dfa3a7fe1f9aa9206f977068df965c9fcf958f61ef918ce35f857865ef82da8aaf7d3612bf5a9e238f588fb0ff4cb1848f45bc616f33b8b2af3031378f26c9b7df1988910f15a4726f01e6f09ef8fa16bef87e574eeb673b4ee33f7c6ece83359ebe14c92eb558ecfeaed28a4ea706750e95f1976e93b91e8e92b0085e90a8279e906a693e83fcaf8e7fef693e7c9a990e748668ae702953fe6d1108be68bd7dde68401dce623b2d2e4283e60e3fc39ebe29b1387e1ef1f35e1ae2259e1922e5de1369cd2df37aa50dd34cfdcdc99d192dc29b23cdc1f987bdc10b442dbfc1f9bdb4898dadae68c0edaa2023dda8c5b73d9e7eba7d9ae87c4d9a3ca99d9718e1cd91dfaedd810c52fd72f2804d727eb72d6ead9d9d5dd2108d53659b3d365ad8ad31b484ed2cba807d1d9fde5d166dda6d11a1c07d10995f2d100cbe2d0aebdccd0347ceecf5cb75dce26691ece251f95cd7e258dcd583917ccd45125ccd25b39cc03d699cc0330d6cb576682cb006ca4ca958942ca153aa6c95cac45c94be635c928c965c7115d57c6d0d1cfc6659303c643532ac4607851c40370eec356b04cc31ada27c2f9be5ec2baf956c29a3450c1ff0fe9c1e3d130c18fe33cc124dc61c0e418e8c09b1ca1c091fb44c0672505c009670cbffd79b7be8e7255be8a6566bd8f0cbbbbc5cf8abbbc6bc3bb9680cabaf719b1b99c9ed6b8bddec0b8b7a316b84fa9c3b7cbc507b79da3d4b76cdaacb4a69272b4230615b41b24bbb3f0a92eb3eace18b3780183b302cb29b2c78afcb236b143b180d57db1600e8eb0a3070db06c4074aeb6b146ad958355ad3c17cdacb5b1fdac9e0114ac6f7c4aac5bb476abe1ef67abb2a6acab5b5282ab1b1141aaf09c3faa2870acaa141c58a998a9c5a963be70a8791f2ca851aec3a7d85dcca6f4a20ea6c079d7a668ea34a5993444a5055bb9a47f690da43b47ffa41d50caa30701b9a2338c82a1ef6b74a145e724a126dfc6a0ed45ffa0df91aea045fa719ff265059fbd4b1d9ed22a199defd64b9cfd82f89bb0ef769ac504339a82810f9980b040994e426a98d1b9e198c7e78598bf2b3998946b82986ddd0c986dbfba9847ea7d9833811394f5825494b33a7b948a46ad947042619445943692bff029928fd8c7927eabbb9232647c915371d99120bd339066c9789042d9f28fcc66d78f34b93f8db6bdf38bcc4a4d8965850b8940cc45886053fd8824e9ae8808184087928879876d5203873ccab6873afebe86b21d0785c0b93c858e14cc84be7cfe84b7eead84aa836782e2d2d082d4e0ce810901cd81042d2080ef887e80479db37f3d76057cc7c3a17be3adbe7bc447097b7e53837b4dc6c57aa9993779c6c8b07964569c792f6b4779142aef785dbcac76deb0257636549f759ef21375653e8f74f3b23074b542e77460bb0173b4f0ad737ad43972e92c29722a0f6a71dded5a709d4f9e708a0239705c1f576ff9d81e6fa7c7e66f69c74d6f64c9c66f6096cf6da6b8c06da028f76d72a4ef6c39c73f6c2c1e586c2961626c1adc2e6bbc10786afaa1426a76e76369de5d3769bcbbf76935f0af687f2196684e6c63683989e36835bfb16746197066ebfc8066da7736665f7bab65bb56eb65408d1c644669ed641d4e3b63bc5c9a632775fb62ff162e62a3b23e611c0f6d60f8025160f06c7f60e9c320603cfb50603125335f7bd4c05f2ec3645eb84ff05e9359e95e77eda25de78f955ca86e7c5c4eb95159ecbf13596fd7c159341fa758e1bdca57a3d753571cfb4d55f0bff75540b86353686665530eedab52149c785204cf6951fa3f5f51dfb4b65144e6885126264d511e9b6850f4f0c450c0056f501d84864fe7ab644fb8f2de4fa736c24dd09d1f4d5e5bb94d5a5bdb4d5479b24c98f8434c8b41d04c6b2b7a4bbf61264b8f6eb94a452cd84a00006f49c6f9d749bcc91f49613eaa48f4e6ff48e9c03648cfd764482a386f476f9d37472dc0734618e9ed458ab59e45243ad645052b044482355f4423c194441322b943cf01ab42ec468d42dd532d42b1a2e44268a2d4424e9a4941e11d0141c7f95041a99a31417811c84155edd43fca240b3f015e693ef62da63eecdd593e2677b63d11dbcf3d0b115f3cfbfda23cdee2713cd2972a3c0c7acf3c08c8bc3bd78f7a3b5b92a23aaf98ee3a4a3f6139d5e71b39bd9293397a89713934a43738c0a1ca37da9abd375c7ea7374efea136f34791365e5c053606334b3498505f346c26273439cbbc33b32a1c336c534e3365c1cc33321654323ca21631db055b3168853730971c57302b2fd52fb230012fa8f3b62f24266b2ec1569d2e03eb7f2deb2b3a2dd22e672db569fa2d4707f72b2255142ae928492a1d808728c7b12f28ad6aa1284f0f0b282a2bb627fcaef827898ea5265399732619ecd32594191024490dea24020c69232ec5f922eeb5fa22eaa4eb22e7d69f22d48c4021c19a2d1fbc64141f5b703d1eab94651ea887d41e7f8fef1e7e70421e3a4f341e3598201c7d98d21bdb801b1b8997941a3d52e319cd63f519684e06193a3459191a70ea189a6f671896be1c17cab97717940bca170f471715e110a513530428131ecb32119da3cb111f68e110ae63151012847c0f7bdff00ecfad7e0ebe14ea0d272e750c9575640c5c7e6b0abe11960a4eeedf09f21c8808bdf51c088ef34806c65671067218910616292e053211b504ced4950480d95b03f66c8e03d2ca90039c4ab002dfd0f80202d62801cd639901839751015c12430113e6590107983b00daf96200a89591009e176d003e04c900045f76
  | 8 => 0xfffac911ffd18eecffa648c4ff989948ff19f817ff0d044ffe8b5444fe7a516bfd2e595ffd1bcbc6fd18c46cfcce1b8cfcc234e9fcb504eafc1f4aaefbcd4525fadb3a1cfaae073bfaa15298f977068df8c06422f8666d48f85088b9f7f80891f7f53ef5f7d3612bf6a8280df6955d05f636b989f3446378f2fc8313f2c3474bf292cb03f27ae811f2269433f1f42ffcf1ab3221efa5bc2beefefb6beed7b221ee390e15edb5b497ecff43dcecbf2d91eb558ecfea706750e991db76e83fcaf8e8145f41e812a01fe777de8fe742f33ae68bd7dde68401dce64c632be638de46e2dec1f5e29b1387e248cb3fe246d632e21367d6e20ad9efe1819246e0c91b73e0b83a14e08418a5e0764046e03d8103e01f2ee3dfb8bfcedef5192bde50cb0cdd00278bdbf4c6b1db6ad1dedb4898dadb0c1b55da5dfc5ad9e7eba7d9a3ca99d93c0b81d8fee1fcd7c8677cd750ba02d72f2804d727eb72d6ead9d9d64d11d6d5fda2e1d56d2a7ad5279d14d4015d81d3d20a5ed3586b79d34d2750d26b275cd2215e93d1a58021d14cb896d063cb55d043eea7d03566f5d0347ceecfffcd99cea9a0d3cd583917cc13dfd0cc0330d6cb576682cb4f73e2c9fdb28ec9b7cd54c9a98a9ac92ba0cdc90fbb54c909e4a4c89b4b95c894a03ec892cda5c7b89eeac7b0ac16c69e2019c5dc78a6c57efd8cc3abe567c356b04cc31ada27c285df0dc130782ec113dc60c0a7b82abfded03fbf27ca69bef19c0bbebacbaabe8e7255be4794d9bd322926bc17dc99bbacc179bb944d50baf7baabba1c8017b9f4cfaeb874ff07b85c03e7b84fa9c3b81e9aa5b7cbc507b7428a67b66775b2b634b884b60b5ef7b54f9105b53305c7b4906a40b3b220fcb302c838b21c4537b1cad42db1c54ae1b15ca7e2b0d3a4a3b0a4e456afede6b9afe423a4afc66b89afbd2224afa3fb92af9e96c1aeec3702ae31fb7aadf480b8ad5297a7acfbc0fdacf3bca1ac84f303abb2a6acab938a5dab1b1141aaa3fa59aa75fb22aa331424aa1d1ca6a9ed5f86a9a1b0d9a85f4477a851aec3a7d72849a755ac51a729450aa66e1ed1a66db9c3a6465e02a61a2e7aa5993444a5715549a52a36daa51b4a61a4ff593ea49eaf5aa4283ff1a3f24feda36ef59ba3614bbda322ac12a27c156fa2071527a0a4b327a004ba5b9ff265059fe2a0619fbdfe989f88bc329f6d07189f066d3f9ee30ac39ed22a199ec777ef9eadb1c39e0eb29b9de3826c9ddca1989d9bfbf79cfd82f89c43b6889b95ca799b237b9c9ad227c59ab924249a7f7e1c98f70f259882ff1897a52d5d96c0f294963f6b04962a38a69602731494f8452a94d6d46994d4e78194a4c89094573450944594369412a5e692e5456d928fd8c7927eabbb91ed51c3918021199100345c904b866a9032ae608f21e6968ee12a4a8eba66118de8cbe48dc18b9d8dc0755f8bf24bbf8bd2270e8b4328ea8a5d8cda8a57325789f05a6389c8cba98967faec889c0b12886ef30088568a4d87f19874876d52038748d1a98746b9ed86343dca86034d7285fb184f855b413b85099d5184ecfed584e7fe7684be7cfe83cfc06382cfaa9382c57aff8114ddc2810901cd80e878f67e37cf707dc955037c97feed7c3ca4817be56c687be3adbe7b7e53837af8abc17af145867ad4b85d7a3322ed79b110437995b6f77918ff4c790b2cd8783b421877b2072c7630e4a575fa3af67573775074f3b23074af767c74abd4c3745deaf773d05df671c98fa47151e7d8711833cd70b5810f70a141d0709c81316faf92bd6f4534d96f311cdf6ef3dbac6e1fe7536dc79e896c8706b86c39c73f6c2961626c23851769de5d3769ba48aa689edbfd689982c2684de2ff677934746602ded465f7b172656515e7656182856472563c643b62106403827663e1b1de639040e6632144f46282b9476244e1eb620a54ea61c111276084c5cb5f6034685d57b7915cedf46b5ca86e7c5c774ebb5c18c1b95b53e0025abbc9da5a9dcd025a754b3859bdad7a591deeb458ff2e6758ec7a9858bb396058866e1d57ed840f57b58dff573b0f22571e0a71571cfb4d56fcb67256d97693563a994855de103155a4244f5516b476546d88c553ebb10c539eda59534342f4530eedab5144e688504fb1694ee901324ea86a494cedda4a4c5d064a4b24f58a4a7d1ca34a55672f492dea8348f4e6ff48e9c03647c65193479acfaf4726931847209353469d39e9465293a14592f14b458c68e94541a47d428ddd77426d2365421d37aa41c7f95041c159114196eb7d408926fe40419a58401181e8400c895c3fdc56f13ef62da63ef419f23ed6ec473e2677b63e179cce3e113c3a3decdd243d2af3db3c5889613c0c7acf3bd78f7a3af50c313a77c9393a4af9533a3f440e3a073628397a89713934a43739194edf38e6fbb337fe3b5537bd1f4037b0c9b437a8c43037934aea377b83223767899a3718f0f436aa608b36a4ac4a3601a11d35b1523d34f864e434917b6b348a6db534827ab63416a4f533b32a1c339f83b933190843329e31193265f6ac323ca2163229f74b3217ca7931da2e05316dc41431688537312e927c31136e89309ddd3c30758e272fd7abb92fb230012f310b912e1abf342d80ac1a2cd5eb0b29bbfe6c2945dca028929c27288ba27528702899281a258227ff389327e444ea27d2ac562789f6a8272ee27b270ac84426e9b748269f30cb2692778625941910255c26ac24ee6c5824c8bd5822905e6d21954d4f218e1f4a2137c6c52120b5fe20d216ae20c913b02076e99b2018f13e1f10dec71ea887d41e7e66ba1e03f69b1dee72961dd228cc1d36427b1bd554a71b629d1b191a70ea18bd28461896be1c17f07b2517cab9771741494d16fb0412167d77ab163e2b7a15464c351541a62014a5046613ef3b1413530428118c2aef10f3507e104f6d5b0fa814e70f7bdff00f62d1df0eebb0cd0ecfad7e0ebe14ea0d816e990d73815b0ca723050c4730b10b0f666d0a4eeedf09d5575b0992c8990924f6120905a16b08ea25f708bdf51c088fa3cb07a04b790760ba4906c6567106a040620673707c06721891050eb88a04c9a0f804238a9e02969a2e01ab646c0154626900fb510a00ee8a2a00a5fca4
  | 9 => 0xf2c3474bf1ab3221e991db76d26b275ccea9a0d3c7b89eeac7b0ac16bf27ca69bd322926bb944d50b9f4cfaeb874ff07b66775b2b4906a40b302c838b21c4537aa75fb22a51b4a619f88bc329d9bfbf79b95ca799a7f7e1c962a38a69602731494d4e7818a57325784ecfed580e878f67af1458679b1104371c98fa4709c8131656515e7643b62106244e1eb6084c5cb5a9dcd0258866e1d57b58dff573b0f22563a9948458c68e93e2677b63d2af3db3a77c9393a4af95334827ab629bbfe6c269f30cb2018f13e1d36427b1b629d1b0f62d1df0905a16b04238a9e
  | 10 => 0x3e2677b6
  | _ => 0

def LT : Nat → Nat
  | 7 => 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888
  | 8 => 0x89999999999999999998999998999999999999999999889899998899989999999999999999989988999988899999999999999989989889999999999999999889999999989999999999898999999999999999999999999999989899999998999999989999999999999989999998999999899999999999999999989988999999999999999999999998999999999899998999999889999999999999899999999999999999889899999999999999999999999899999999999999998999999999988999999999889999999999998999999989989999988999998899999999999999999998999989999899999899999999999999999998999999999999989999999898989999999989999899889999989999989998998999999999
  | 9 => 0x9999999999999999999999999999999999999999998999999999999
  | 10 => 0x8
  | _ => 0

def DT : Nat → Nat
  | 7 => 0xb549dc2ab411907e2f005aaa92774a08be3f17802d56470aad04672f8fc016a93b8562882f8fc5e00b549dc2ab4ca08be3f005aa4f1f8eb85568217802d52770aad265f1f8bc016a93c2dc2822f8fc5e00b549dfeab411f8be2f005e64ee15caad045f1f802e52770aad2a822f8bc016a93b8556823f17c5e00b549df2ab4117c7e2f005aac9275da08be3f17802d52d70aad045f220bc0181b54b1c2ab4117c5e00b549dc2ab411c0be2f005aa4ee162208be3f17802d55c93c7156822f8fc017498b8556822f8fc5e00b549dc2ca411f8be2f005aa4f087f384be3f17802d5277f385b8ab2f8bc016f9638556822f8fc5e00b54e64ee155a08c83f005aa4ee15da08be471f802d52770aad045f228d4016aae49e4aab2f8fc5e00b549deee155a087e2f005aa4ee155a6d045f17802d5278ec71c2ab4117c017093b9d56822f8fc5e00b549dc2ab411c8be47005aa58e655a08be3f17802d52786aad045f1f8bc017b93b8556822f8fc5e00b549df0ab4117c7e2f005aa4ee162274be3f17802d52786acd56822f8fc016a93c963ae15597c5e00b549dc2c35d2ad042f005aa4f0d66aacbe3f17802d52c70aad045f1f8bc016aa0b8556a02f8fc5e00b549dd0ab4117c7e2f005aa5ae755a08be3f17803036a93b8556872f8bc018cb238556822f8fc5e00b549dc2ab4117c8a2f005aa82e155a08be3f178031f2770b6956822f8fc016aae4e556822f8fc5e00b54d9c2ab4117c902f005aa4ee155a08be3f1a002d52770af556822f8bc016f93b8556872f8fc5e00b5505c2c04117c7e2f005aa4ee755a08be44178032f6a93bc1565f1f8bc016a9cc75c2ab4117c5e00b549dc2ab4117c923f005aa4ee155a45045f17802d52770aad2a82328bc016aa0b8556823a0fc5e00b549df0ab4e97c7e2f005aa4ee155a08ce5f1f802d5617ab8556821f8bc016a93bb556822f9145e00b549dccab4397c7e2f005aa76e155a08be3f17802ed6a93b85045f1f8bc017e93b8556822f8fc5e00b549ddeab4117c7e2f005aa4ef055a08d03f178032f2786aad045f1f8bc017993b8556822f8fc5e00b55724eab4117c7e2f005aa4ee155a1cbe3f17802d52f70aad045f1f8d0017493b8556a0410fc5e00b549dd2ab4aa08be2f005aa4ee155a61047e17802d52770aad34821f8bc018fc0c9dc2ab411c85e00b549dc2aa4117c7e2f0065ed52770ad8be3f17802d52770aad246e1f8bc017093bcdc2ab4117c7e00b549dc2b24117c7e2f005aa4f1d70aad045f17802d52770aad3c5f1f8bc016a93bc172ab4117c7e00b549dc2ab4717c7e35005aa4ee155a80be521f802d52770b6956822f8fc016a93b85569d3397c7e00b549dc2ab5017ca82f005aa4ee15da08e45f17802d52770aad045f290fc016a93b8556822f9505e00b549dc2b6411a07e2f00672d4e155a08be3f17802d52d79b8556822f8fc016a9cc9dc2ab4397c7e00b949dc2ab411947e2f005aa4ee162208d85f17802d52770b01045f290fc016a93b8556823f97c5e00b549dc2c04117ca82f005aa4f1055a08e83f17802d527792ad045f1f8bc016a93bcdc2ab4117c8800b549dc2ab4717c7e2f006324ee155a08be3f17802d52770ad156822f8fc016a93b8556953e97c7e00ba49dc2ab4117c7e35005aa4eea55a08be3f17802d55d93b8556821f8bc016a93b8556823a1487e00b549dc2c54117c7e2f005aa4ee155a08e85417802d55170b0d56821f8bc017293ba556822f8fc5e00cb49dc2ab4117c7e2f006124ee155a80be3f17802d54a93c7dc2821f8bc018493b8556822f8fc5e00b54e1c2ab4117c7e2f005aa4ee155a30be3f1a002d5277c2ad046c2f8bc016aa749dc2822f8fc5e00b551dc2ab4117c7e2f005aa4f2370aad045f1f803092770b01045f1f8bc018f93c21c2822f8fc5e00ca49dc2ab411f4be3f005aa4ee155a20be3f17802e92770aad045f1f8bc018f93b85b8ab4117c5e00b549ddaab4717c7e2f006324ee155a74be3f17802d527843cd045f1f8bc018493b8556823a0fc5e00b552e4ee155a08be3f005aa4ce155a08be3f17802d52788385045f228bc016a93bcdb8ab4117c5e00b552a4f1c70a08be3f005aa4ee1632ad043f17802d52786ae5045f1f8bc016a93b855682330fc5e00ca551c2ab4117c7e2f005aa4eff55a54be3f17802d54270aad045f1f8bc016a93c0156822f8fc5e00b552a4f257097c7e2f005aaa92770a30be3f17802d52770aad046c3397c0197c0c9dc2ab4a97c5e00bcc9dc2ab4117c902f005d24eed55a08be3f17802d52770b0d56821f8bc018f93bf9c2ab2f8fc5e00b549de0ab4117c7e2f005aa4ee165254be3f17803035c93aad045f1f8bc016a963855682320fc5e00b549dc2c359aad043f005aa4ee166b0d563f178032f8f93b8556a01f8bc016a93b8556822f91c7e00bccd9c2ab4117c7e2f005aa4f0f55a08be3f17802d5277f3cd565f1f8bc019493bfd56822f8fc5e00ca49dc2ab4117c7e2f005aa4ee155a7cbe3f17802d53b70aad245f1f8bc017e93b8556922f8fc5e00b549df0c44117c7e2f005aa4ee955a08ca3f17802d53b70aad046e1f8bc017e93b855682370fc5e00b552a72e14117c7e2f005aa992770aad045f17803292770b29045f1f8bc016a93b8578822f8fc5e00cbdaa4ee1559a07e2f005aa4f0870a08be3f17802e12770aad105f1f8bc016a93b85b8ab4117c5e00b5585c2da55a08be3f005aa4ee15b208be3f17802d5278ab85565f1f8bc018fb54b5c2ab410fc5e00b549dc2ab4e9c87e2f005aa4ef570b6956821f802d53170aad40821f8bc016a96b8556882f8fc5e00b549e0aab4117c7e2f005aa4ee155a1cc83f17802d52f70aad2a822f8bc019793b8586ab410fc5e00b8c9dc2ab4117c7e2f005aa4ee155a08da5f17802d55e93aad045f1f8bc016a93b8588823397c7e00c7daa4ee155a08882f005ea4ee155a08be3f17803192770aad046c2f8bc016aa549dc2822f8fc5e00b549dc2ab4417c882f005aa4efe70aacbe3f17802e52770aad045f1f8bc016a93c81c2ab4117c7e00c2c9dc2ab4117c7e2f00606d52770ac1045f17802d55170ae956822f8bc016a93c41c28e2f8fc5e00c049dc2ab4117c7e2f005aa4ee15caad04681f802d52770aad045f1f8d8016f93b8560822f8fc5e00b549dc2ab4117c942f005aa4ee155a612a3f17802d5278fc71c2ab410fc016a9bb8556822f8fc5e00b5592a9104117c7e2f005aa4ef855a08ce5f1f802d52770aed045f1f8bc016aafc9dc2ab2f8fc5e00b549dc2c14117c7e2f005aa62e155a08be3f1a802e52f70aad045f1f8bc016aa7c9dc2822f8fc5e00b549dc2b14117c7e2f005d24f1070a08be3f17802d527732c1045f1f8bc018fb549dceab410fc5e00b549e4b1f70aac7e2f005aa4ee158208be3f17802d52c70aad0e5f1f8bc016a93b9d56882f8fc5e00b549de0ab4117c902f006524ee155a61043f17803192770b11045f1f8bc016a98b8556822f8fc5e00b54d9e0ab4117c7e2f005aa4ee15d2ad045f17802d52770b3d565f1f8bc016ab249d56922f8fc5e00b549dc2ab411787e2f005aa4ee15d2cd56822f802d52770b3574ab2f8bc016aa0c4156822f8fc5e00b55924eab411b87e2f005aa731f70aad043f17802d55493b85045f1f8d0016a93c9638e15597c7e00bf4edc2ab4117c7e2f005aa4ee155a08ca3f178031b2770aad045f1f8bc016aa0b8556822f9487e00b5505c2ab4117ca82f005aa732770ac1045f1f802d52770aad245f238fc016a93b856c822f9205e00b549dc2c35ca087e2f005aa4ee155a08dc471f802d56184385045f1f8bc016a93b8596822f8fc5e00b54c5daab4117c7e2f005aa4ee155a08be3e17802d56170b7156822f8bc018c93be156822f8fc5e00b549dc2ab411a4be3f005aa6ce15b208be3f178032b2770aad045f1f8bc017293b85568c2f8fc5e00b549dd2ab4117c7e2f005c24ee158a08be3f17802d52770aad04681f8bc016a93c21eae1410fc5e00b549dc2ab4717c8a2f005aa4ef570b71568217802d52770aad045f2a8fc016a93c7dc2ab410fc5e00b549dc2ab4517c7e2f005aab9278eaad045f17802d5649cbcd56822f8fc016a93b85beab4117c7e00cbc9dc2ba55a08be2f005aa5ee155a08ca3f17803034a93b85045f1f8bc0184a0b8556822f8fc5e00b54d5c2ab4117c7e2f005aa4ee155a81043f1a802d52770ad556822f8fc016a96b8562822f8fc5e00b549dc0ab4117c7e2f005aa732570aacbe3f17802d52779b8556882f8fc016ab0bf9c2ab2f8fc5e00b549dc2cc4117c7e2f005aa4ee162208e43f17802d53d70aad045f1f8bc016a93b855682378fc5e00bbc9dc2ab4117c7e2f006524ee155a08fc5f17803192770aad04672f8fc017493b8556822f9145e00b54bdd2ab4117c7e2f005aa4ee158a08be4417802d5277f3d5c2ab1f8bc016a93c4156822f9487e00b549dc2ab44a08be3f005aa4f1055a08be5417802d5278e38556822f8fc016aaa38556823e97c7e00b549ddcab4117c7e2f005aa60e155a08be3f17802d52770aad045f2a148016a93c3586ab410fc5e00b54f1c2ab4117c7e2f005aa4f2570aacbe3f178031d2770aad045f1f8bc016a93be15682390fc5e00b5591c2ab4e97c7e2f005aaa2e155a08be3f17802d5277faad047d2f8fc016a93b8576922f8fc5e00b549df4ab4117c7e2f00606d527732ad045f17802d52770aad047d2f8fc016aad49dc2ab4117c7e00c249e20ab4117c7e2f005aaa2e159aad045f1f802d55170b35565f1f8bc016aa9b8556822f8fc5e00b549dc2ab461947e2f005aa4ee15da08dc3f17802d52776aad40821f8bc016a93b85568d2f8fc5e00b549dceb14117c7e2f005aa4ee155a08ea3f17802d52770aad24722f8bc016a93b8594823e97c7e00b7c9dccab4117c7e2f006124ee155a08be521f803092770aad045f2a0bc017eb249d56822f8fc5e00b549dc2ab411d87e2f005aaa8ff55a08be3f17802d52770aad2a822f8d0016a93c4dc2ab410fc5e00b549dc2ab411a87e2f005aa4ee155a08be3f1a802df2770aad045f1f8bc016a98c41c2822f8fc5e00b4c9dc2ab4117c7e2f0065ed52770aacbe4817802d52774aad185f1f8bc016a93b8556823919c7e00b549dc2ab4117c8c2f005aa4f0170aacbe3f17802d56370aad045f1f8bc018793b8556822f8fc5e00bcc9de0ab4117c7e2f005aa76e155a08be471f802fd2770aad045f238fc0197b54d9c2ab2f8fc5e00b549dc2b0411907e2f006764ee155a08be3f17802d5277b38556821f8bc016a93c41e6b94117c7e00bfc9dc2ab4117c7e2f005aa4ee655a08be3f17802d52770ae972822f8bc016a93b8584822f8fc5e00b549dc2ab411a0902f0065ea2e155a08be3f17802d5279238556822f8bc016a93bfd56822f8fc5e00b549dc2ab411c47e2f005aa4ee155a08be3f17802d54393b85565f1f8bc016a93bb556822f8fc6a00ba49dc2ab4717c7e2f006064f1f70aad043f17802d53670aad04681f8bc016a93b8566ab4117c7e00b54b9c2ab4117c7e2f005aa4ee166aacbe3f17802df3993b8556822f8fc016a93b8580a02f8fc5e00b549dfeca4117c7e2f005aa4f0e55a08be3f17802d52770b3566ab2f8fc016a93b8594822f8fc5e00b549dc2c04117c7e2f0061ad52755a08be3f17802d52786385045f1f8bc016aadc9dc2ab4117c5e00bac9dc2ab4117c7e2f005ca4ee155a08be3f1a002d52770ae556822f920017993b856c822f8fc5e00b5589c2ab4117c7e2f0063ed52770aad103f17802d53993b9956822f8fc016a93b8556823a0fc5e00b549dc2d34117c7e2f005aa4ee155a04be3f17802d56470aad046c2f8bc016a93bb556822f8fc5e00b54d9c2b955a08be3f005aa5ee155a08be3f17802d52770b39565f1f8bc016a93bcdc2b14117c7e00b549dc2ab4e97c7e2f006064f1c70aad045f1f802d52784385b4822f8fc016a93b8580823a0fc5e00b549dc2dc6d2ad045f006324ee155a08e43f17802d55270aad045f1f8bc016aa6c9dc2ab410fc5e00b557295274117c7e2f005aa58e158208be3f17802d52770aad30823e8fc018193c95c2ab2f8fc5e00cbc9dc2b355a08be3f005aa4f0d5d2ad045f17802d52778aad045f1f8bc016a93badc2ab4117c5e00b549dc2ab4a17c7e2f0063ec2e155a08be3f17802d54a93c75c2822f8bc0172aa49dc2822f8fc5e00b849dc2ab4117c7e2f005aa62e155a08be4517802d52770aad045f1f8b8016a9db8576822f8fc5e00b5585e6ab4117c7e2f005fa4ee15da08be3f17802d52790b8556822f8bc016aaa3855698410fc5e00b549dfce16d2acbe3f005aa4ee155a71043f17802d52770ae1045f1f8bc016a93c25c2ab4117c7e00b54b5c2ab4117c7e2f005aa4ef579aad043f17802d53b70aad04722f8bc017e93b8556823917c5e00b55424ee15597c7e2f005aa4ee155a40be3f17802d56093aad045f1f8bc016ab238588822f8fc5e00b55924eab4117c8e3f005aa4ee15821cbe3f17802d52770aad04651f8d0016aa8b8572822f8fc5e00b549dc2ab4617c7e2f005aa4eff55a61043f17802d52770aad045f220bc016a93b855698410fc5e00b549dc2dd55a08be3f006524ee155a54be3f17802d52788385045f1f8d4016a93b8556822f9205e00b549dc2ca4c2087e2f005aa4ee155a812a7217802d53270aad045f1f8bc016a93ba556822f8fc6800c0daa4ee155a08c82f005aa4ee155a08d85f17802d53670aad045f1f8bc016ab0b8556822f8fc5e00b54ce4ee155a087e2f005aa4ee155a08fc7d2f802d52f70aad185f1f8bc016f93b855682320fc5e00b549deae155a087e2f005aa4ef05b208be3f17802d52770aad245f1f8bc016aaa49dc282328fc5e00b549dceab4117c7e2f005aa4ee155a08dc3f17802e12d70aad045f1f8bc017993b855682340fc5e00b9c9dc2ab4117c7e2f005aaa8e155a08fc5f17802d52770aad4082228bc016a93b856e822f8fc5e00b549dccab411907e2f005aab9278faad043f17802d52770b35725f1f8bc016aaa4e5c2b94117c7e00b549e14e155a08be2f005aa4ee155a08be5617802d53170aad1c5f1f8bc016a93b85569d3617c5e00c7daa4ee158a087e2f005aa4ee155a3cbe3f17802d52784385b8822f8bc016aa8c3556822f8fc5e00b849dc2ab4117c882f
  | 8 => 0x5aa4ee155a08c83f17daa512770aad045f1f8bed52770aad045f290fc5f6aa0c9dc2ab4117c7e2fb549dc2ab4917c7e3717daa4ee158a08be3f17852d52770aad04722f92c5f6aa8b8556a34117c7e2fb549dd8e155a55045f17daa4eed70aad045f1f8bf496a93b8556822f8fc5f6a93b855682370fc6e2fb54ea4ee155a08be3f17daaa8e155a08ee5f1f8bed52770aad04642f8fc5f97b549dc2ab4a97c7e2fb549dc8e155a08be3f17e96d52770aad045f1f8bed5278338556822f8fc5e00b549dc2ab411f8be2fb55024ee155a08be3f17daa4ee155a08be3f17846d52788b8556822f8fc5f6aab49dc2ab4117c7e2fb549e20fb55a08be3f17802d52770b11045f1f8bed52788385045f1f8bc416a9cc9dc2ab411acbe3fb549dc2ab411e8be3f17e5ed52781385565f1f8bed53b93b8556822f8fc5f6a93b8556822f8fc5e0ab549e3ae155a08be3f17daa4eff55a08ee5f1f8bed52770aad04632f8fc5f72b549dc2ab4117c7e2fb549dc2ab411dcbe3f17daa58e155a08be3f1783ed52770aad0e822f8fc5f7293b8556822f8fc5e1ab55524ee168208be3f17daa4ee155a08be541f8bed52770b2904772f8fc5f98b549dc2ab4117c7e2f005aa4f0d55a08be3f17802d5277c2ad045f1f8bed52770aad46822f8fc5e00b54b1c2ab4117c7e2fb54fa4ee155a55045f17daa4ee155a15045f1f8bed52770acd56a34117c7f6a93b859aab5197c7e2f005aa4ee155a08be4517802d54170aad045f1f8bf276a93b8556822f8fc5f97b549dc2ab2f8fc5e27b549dc2ab4117c7e2f06002d52770aad045f1f8d2dd6a93b8556822f8fc5f6a93b8556822f8fc5e13b549dc2ab4117c7e2f02daa4ee155a08be3f1782f1f6a93bedc2ab410fc5f6aa349dc2ab4117c7e2fb549dc2ab411b0be5717e3ef12770aad045f1f8bed96a93b8556822f8fc5f7cb549dc2b955a08be3fb549dc2ab411a07e2f13daa4f0470aad045f1f8bed52b93b8556822f8fc5f6a93b8556872f8fc5e0fb549dc2b955a08be4b1fdaa4ee155a08be471f8bed52770aad1c822f8fc5e00b549dc2ab4119cbe3fb552a4f1770a08be3f17e7ed52770aad045f1f8bc016a9db8556822f8fc5e00bf49dc2ab4117c7e2fb549dc2ab4117c843f17daa692770aad40821f8bf036a93b8556954117c5f6ab249df6ab4117c7e2f005e64ee155a08be3f17802d55c93aad045f1f8bc016a93b8556872f8fc5f9793b8556a34117c7e2fc7df24ee155a08be3f17daa4ee1572ad045f1f8bed52770ae556822f8fc4f6ab3c9dc2ab4117c7e2fc7daa4ee155a81043f17daa4f0279aad045f1f8bed52781b8556822f8fc5f6a93b8556822f8fc5e02b549dc2ab4117c8a2f105aa4ee770aad045f1f8bed52770aad04651f8bc356a93b8556884117c7e2fb54edc2ab4117c7e3717daa4efb70aad04721f8bc016a93c75c2ab4117c5f7e93b8556822f8fc6e2fb549dc2ab55a08be3f17802d52770b6956822f8fed52770b4156952f8fc5e00b549dc2ab4117ca43f005aa4ee155a08be5417daa4ee155a6104771f8bed52770b2956822f8fc5f6a93b8580ab4117c7e2fb549dc2da6aaad045f1fdaa4ee155a812a5f1f8bed52770b11045f2b8fc5f6a93b8556822f8fc5e12c85aa4ee155a08be3f17daa733470aad045f1f8bed52774aad045f1f8bc3578b549dc2ab4117c7e2fb549dc2ab4aa08be3f17daaa93470aad045f1f8bed5278db8556822f8fc5f6a9f49dc2ab411c8be2fb5daa4ee155a08be3f17802d52770aad1c5f1f8bc018c93b8556822f8fc5f6a93b8556a0411c87e2fb549dc2dc55a08be3f17daa4ee16f2ad045f1f8bed52770aad52822f8fc5f6a93c69c2ab4117c7e2fb549e04e155a08be3f17daa4ee155a08be3f1787ed52770aad045f1f8bc4400c249dc2ab4117c7e2fb549dc2be55a08e45f17df2d52770aad045f1f8bed52770aad045f1f8bc476a93be156822f95c7e2fb54d24ee155a08be3f17e6ed52770aad045f1f8bed52770aad045f1f8bc0d6a93b8556822f92c7e2fb549dc2ab4117c7e2f0a69ad52770aad045f1f8bc016a93b8556882f8fc5f6a93b855eab4117c7e2f005d24ee155a08be3f17daa4ee155a08be3f1c8bf1f6a93b8556822f8fc5f6a93c35c2ab4117c7e2fb549dc2ab5017c983f17daa4ef870aad045f1f8bf036a93b8556823917c5f6a93b8556822f9307e2fb549dc2ab4117cb23f17e22d52770aad045f1f8bed52770aad045f1f8bc4f6a93b8556822f9687e2fb549dc2ab4117c863f17e0ad52770aad045f1f8bf236a93b8556822f8fc5f6a93c7e2ee155a087e2fb549dc2db55a08be3f17daa4ee155a08be3f17886d527883cd56822f8fc5f6a93b8572a34117c7e2fbe5aa732770aad045f1fdaa4ee160208be4c1f8bed52770aad1c5f1f8bc416a93b8556822f94c7e2fb549dfae155a08be3f17daa532770aad045f1f8bed52770aad047e3b97c5f83b549dc2ab4117c7e2fb549dc2ab4119cbe571f802d52770b0d56821f8bed52770aad2c822f8fc5e00b549de0ab4117c7e2fb549dfce155a08be3f17daa4ee163aad045f1f8bed52779bb156822f8fc5f6a93b8556823a1307e2fcbdf24ee155a08be3f17e2ad52770aad045f1f8bedf6a93b8556822f8fc5e00b549dc2ab4117c8e3fb549dc2c355a08be3f17daa4ee155a08be4e1f8bed52770aad045f1f8bc516ab249d56822f8fc6e2fb55624ee155a08be3f17e82d52770aad045f1f8bf036a93bb1c2ab4117c5e00ca49dc2ab4117c7e2fb54fe4ee155a08be3f17daacb2770aad045f1f8bed52770aad04722f8fc5f6a93b8556822f8fc5e1bb55927ce155a08be3f17db6d52770aad045f1f8bed5277138556822f8fc5f6a93c722ee155a08be3fba49dc2ab4117c7e2f1065f1f2770aad045f1f8bed52770aad42822f8fc5f6aae49dc2ab4117c7e2fb549dc2ab4117c7e2f135aa4f1670aad045f1f8bc016a93c21c2822f8fc5f7093b8556822f8fc5e14cbe224ee155a08be3f17daa4ee155a08be3f1780f476a93b8556822f8fc5f6a93b85b0ab4117c7e2fbedaa4ee155a08be3f17802d52770b7156822f8bed52770aad04612f8fc5f6a93b8556822f91c7e37b549dc2ab4117c7e2f12daa4f258bb85565f1f8bed52770ae956822f8fc5f6ab549dc2ab4117c7e2f005aa4ee15b208be3f17daa4f0870b55045f1f8bed5278838556822f8fc5f6a93b85b8d555a08be2fb549dc2c855a08be3f17e06f12770aad045f1f8bed52770aad045f1f8bc356a96b8556822f8fc5e14b54aa4ee155a08be3f17daa4ee155a81165f1f8bed52786aad46822f8fc5f6a93b8556a44117c7e2fb549dc2ab45a08be3f17daa4eec70aad045f1f8bed53193b8556822f8fc5f6a93b8556823997c7e2fb549dc2b955a08be3f17de2d52788385045f1f8bf192770aad045f2b8fc5e00b552a4ee14117c7e2fb549dc2ab4117c9a3f17daa4ee155a08be4417850016a93bf9c2ab2f8fc5e00b949dc2ab4117c7e2fb54e62ee155a08be3f17daa4ee155a08be3f178a7036a9f49dc2ab4117c5f6a93c71c2ab4117c7e2fc0df24ee155a08be3f17daac92779aad045f1f8bed5277f385aaab2f8fc5f97b549dc2d05597c7e2fb54fa72e155a08be3f17daa5ee155a08be3f1786ad52770aad50822f8fc5f6aaa4f9c2ab4117c7e2fcbdaa4ee155a80be3f17daa4ee155a08f85f1f8bed52770aad04622f8fc5f97b549dc2ab4117c7e2fb549dc2ab4117c7e3817e06d52770af956822f8bf1f8193b8556822f8fc5f6a9cc9dc2ab45a08be3fb549dc2b04117c7e2f07daa4ee1622ad045f1f8bed5649cb8556822f8fc5e00b549dc2bb4117c7e2fb549dc2ab4117c902f13daa732770ae556822f8fed52770aad045f1f8bc3b88c0c9dc2ab4117c7e2fb5592a8e155a08be3f17e66d52770aad045f1f8bee16a93b8556822f8fc5f6a93c5dc2ab4117c7e2fb549dc2ab411f4be3f17802d52770ac5045f1f8bed52770aad045f1f8bc576a93bedc2ab502087e2fb54d9c2ab4117c7e2f13daa4ee755a08be3f17850016a93b8560822f8fc5f6a9f49dc2ab4117c7e2fb549dc2ab4117cb63f17daa4ee15da08be3f1b8bed52770aad045f1f8d45f9eb5591c2ab4117c7e2fb549dc2d955a08be3f17802d53170aad045f1f8bc016a93b8574ab4117c5f6a93b85a4ab4117c7e2fb55924ee155a08be3f17daad12770aad045f1f8bed52770aad04722b8fc5f6a93b857cab4117c7e2fb549df6f355a08be3f17daa4ee155a08e45f1b8bed52770aad045f1f8f45f6a93c61c2ab4117c7e2fb549dc2ab4117c7e2f075aa4ee155a08f05f1f8bed5277838556822f8fc5f6a93b85568c2f8fc5e1a005aa4ee155a08ca3f17daa4ee155a08be3f1781ed52770b5d56822f8fc5f6a93b8556822f8fc602fb549dc2ab4117c823f17daa4ee155a08be3f178bf3d8f93b8556822f8fc5f6a93b8556823297c7e2fb549dc2ab4ba08be3f17daa4ee163ae5045f1f8bf036a93b8556822f8fc5f6a93b8566ab4117c7e2fb555272e155a08be3f17daa4f2570aad045f1f8bed52770aad0472358fc5f6aa4c9dc2ab4117c7e2fb549dc2ab4117c7e3317e26d52770aad045f1f8bc016a93ba556822f8fc5e00b549dc2ab411a07e2fb55464ee155a08be3f17802d5278fb8556821f8bed55793b8556822f8fc5f7cb549de6e155a08be3fb549dc2ab41180be3f17daa4ee155a08d05f1f8bed53170aad045f1f8bc416a93c7dc2ab4117c7e2fb549dc2ab411e4be3f17daa4efb70aad045f1f8bed52779b8556822f92c7fa1b549dc2ab4117c7e2fb54e64ee155a08be3f17daa4ee155a08be3f17856d52779b8556822f8fc299eb5551c2ab4117c7e2fb549dc2ab4a9dcbe3f17daa4ee155a08be5c1f8bed55493b8556822f8fc5f6a93b85a8ab4117c7e2fb549e20e15ca08be3f17daa4ee155a08be3f1f8bed52783b8556822f8fc5f97c0c9dc2ab4117c7e2fb5505c2ab4117c983f17802d5278e38556822f8fed52770aad045f1f8bc216a93b85a0ab5017c7e2fbc5aaa92770a08be3f17e5ed54493b85565f1f8bed52770b4156822f8fc5f6a93b8556822f93c7e2fb549dc2ad55a08be3f17e524ee155a08ee5f1f8bed52770aad045f1f8c45fa2b549dc2ab4117c7e2fc95aa4ee155a08be3f17e7ad52770aad045f1f8bf03278bb8556822f8fc5f6a93b8556a04117c7e2fb549e4ee155a08be3f17daa4ee161aad46821f8bc016a93c95c2ab2f8fc5f6a93b8dc2ab4117c7e2fb549dc2ab52a08be3f17daa4ee155a09045f1f8bf356a93b8556822f8fc5f81b549dc2ab4117c5e0fb549dc2d655a08be3f17daa4ee155a08be5d1f8bed52770b3556822f8fc5f6a93b8556822f8fc5e0dc7c9dc2d555a08be3f17802d55170aad045f1f8bc016a93b8556823e97c7f6f93b8556822f8fc5e0fb549dc2ab4117c7e2f125aa4ef36aaad045f1f8bed52770aad045f1f8bc336a93b8556824017c7e2fbcc9dc2ab4117c7e2f13daa5f2770aad045f1f8bed564a238556822f8fc5f6a93b9956822f8fc5e0f005aa4ee155a08be3f1a802df2770aad045f1f8bed52770aad3a822f8fc5f6aacc9dc2ab4117c7e2fb549dc2ab502087e2f105aa4f1055a08be4c1f8bed527883857c822f8fc5f6a93b8556a74117c7e2fc45aa4f1055a08be3f17daa4ee155a08be3f1783f3d9793b8556822f8fc5f6a93b95c2ab4117c7e2fb549dc2ab4117ca44c1fdaa4f1270aad045f1f8bc016a93b9956822f8fc5f6a93b8556822f950982fb549de6e155a2d045f1fdaa4f1470aad045f1f8bed52779b8572ab4117c7f6a93c89c2ab4117c7e2fb549dc2ab4117c7e2f005aa4ee15f2e5045f1f8bc016a93bfd56822f8fc5f6a93b8556822f8fc681ab559a4ee155a08be3f17802d52770aad045f1f8bed52770aad045f1f8bc2f6aaa49dc2c74117c7e2fb549dc2c955a08be3f17daa4ee155a08be3f17806d52770aad0c822f8fc5e00b549dc2b355a08be3f005aa4ee166aacbe3f17daa4ee155a08be441f8bed52770b5556822f8fc5f6a93b8556822f97c7e2fb549dc2ab41a08be3f17daa4ee155a99045f1f8bc016a93b8594822f8fc5e00b549dc2c04117c7e2fbf5aa4ee155a08be3f17daa4ee155a08be511f8bed53993b8556822f8fc1f6a96c9dc2ab4117c7e2fc7daa692770aad043f17daa4ee155a08be3f178b2d52770aad045f1f8bc3d6a93b8556822f8fc5e09b549de8e155a08be3f17daa4ee970aad045f1f8bed5278cb8556822f8fc5f79b549dc2ab4117c7e2fb549dc2ac55a08be3f17daa4ee155a08be481f8bf092770aad045f260fc5f8fb549dc2ab410fc5e14b549dc2ab4117c7e35105aa4ee155a08be3f1b8bed52770aad047b2f8fc5e00b549dc2ab411d07e2fb551272e155a08be3f17daac8e155a08be571f8bed52770aad105f1f8bc296a93b8556822f8fc782f005aa4eed55a08be3f17daa4ee155a08be3f178aad52770aad045f200fc5f6a93b8556823617c7e2fb549dc2bf55a08be3f17802d52f70aad045f1f8bed52770aad18822f8fc5f6ab249e04ab4117c7e2fb549e04e155a54be3f17daa4f0870aad045f1f8bed52770aad04742f8fc5e00b549dc2ab4e97c7e2fb55524f1070a08be3f17daaa92770a08be3f1786ad52770ad956822f8fc5f6aa449dc2ab4117c7e2fb549dc2ab4117c7e2f105aaab2770aad045f1f8bed527883b156822f8fc5f8bb549dc2ab4117c7e2fb55524ee15ca08be3f17daa892770aad405f1f8bed52770aad045f280fc5f6a9b49dc2ab4117c7e2fb55864ee155a08be3f17daa4f1070b41045f1f8bed52770ae556823597c7f6a93b8556822f8fc5e18b549dc2ba55a8d045f17daa892770aad045f1f8bf1f6a93b858eab410fc5e00b849dc2ab4117c7e2fb549dc2ab4117c7e2f0e622d56493aad045f1f8bed54a93b8556822f8fc5f8cb549dc2ab4117c7e2fb549dc2ab4117c7e2f0b5aa4ee155a81046b1f8bf1f6a93b855682390fc5f6a93b8556954117c962fb549dc2ab49208be3f17daa4ee1682e5045f1f8bed54593b8556822f8fc5f6a93b8556822f8fc5e08b549de0ab4117c7e2f13802d52d70aad045f1f8bed52770aad045f1f8bc5b84b549dc2ab4117c7e2fb55724f1755a08be3f17daa4eed55a08be3f17882d52779b8556822f8fc5f6a93b8556823f17c7e2fb549dc2ab4117c7e2f02002d52770aad185f1f8bed52770b4556822f8fc5e00b549dc2ab4117c882fb549dc2bb55a08be3f17802d52770aad30821f8bee96a93b8556822f8fc5f6a93c762ee155a08be2fb549dc2ab4117c7e3a17daa4ee155a08be3f1a0bed52770b1d5682390fc5f6a93b8562ab4117c7e2fb549dc2ab51208be3f17daa4ee155a61045f1f8bc016a93b8556822f9205f6a93b8560ab4117c7e2fb549dc2b64117c7e2f13daa4efc70aad045f1f8bed53993bcdc2ab4117c7e00b549dc2ab411b0be2fb549dc2ab4117cae3f17daa4ee155a08ce5f1f8bc016a9b38556822f8fc5e00b5585c2ab4117c7e2fb55924f1055a08be3f17daa4ee155a08be3f1d8bed5277338556822f8fc5f6a93b855695411c8be2fb5585c2d555a08be3f17802d5277ab8556821f8bed5277fb8556822f8fc5f6a93b8556844117c7e2fb549dc2ab4117c7e3217daa4ee170aad045f1f8bed52770aad045f228fc5e00b549dc2ab4917c7e2fb549dc2ab4117cb03f17daa4ee155a55165f1f8bed52770aad04641f8bc1e00b549dceab4117c7e2fb549deae16aaad043f17daa4ef570aad045f1f8bc016a93b855682370fc5f94b549dc2ab4117c7e2fb549dc2ab411f4ee5f1fdaa4ee155a08d65f1f8bed52770aad046e2f8fc5f6a93b8556954117c5e1ab54b24ee155a08be3f17daa4ee16d2ad045f1f8bed52770aad3a5f2b8fc5f6a93c79c2ab4117c7e2f
  | 9 => 0x5aa4ee155a08be3f1782ad52770aad04772f8fc5f6a93b8556a34117c7e2fb549dc2ab4117c7e2f015aa4ee155aad045f1f8bef16a93b8556822f8fc5f6a93b8556954117c7e2fb549e04e155a08be3f17df2d52770aad045f1f8bed53493b8556822f8fc5f6a93b8556822f92c7e2fb549dc2ab4117c7e2f0a63ed52770aad045f1f8bed52770aad045f260fc5f88b549dc2ab4117c7e2fb549dc2ab4117c7e2f13daa4ee163aad045f1f8bed52770aad04722f8fc5f6a93b8556822f8fc5e03b55aa4ee155a08be3f17daa4f1070aad045f1f8bed52770aad045f1f8bc356a93b85568b4117c7e2fb549dd8e155a08be3f17daa4ee15caad045f1f8bf2f6a93b8556822f8fc5f6a93c5dc2ab4117c7e2fb54fa4ee155a08be3f17daac92770aad045f1f8bed52770af956822f8fc5f6a93b8556822f8fc5e2fc0daa4ee155a08be3f17daa4efb70aad045f1f8bed53993b8556822f8fc5f6aaa49dc2ab4117c7e2fb549dc2ab4117c7e3f17daa4ee1682ad045f1f8bf3d6a93b8556822f8fc5f6a93b8556a04117c7e2fb549e4ee155a08be3f17daa4ee155a09045f1f8bed52770aad045f1f8bc1e00b549dc2ab4117c7e2fb549dc2ab4117c7e2f00daa4ee16aaad045f1f8bed52770aad045f2f8fc5f6a93b8556822f8fc6e2fb549dc2ab4117c7e2f105aa892770aad045f1f8bed52770aad045f1f8bc116a93bcdc2ab4117c7e2fb549dc2ab4117c7e2f025aa4ee155a08be571f8bed52770b8556822f8fc5f6a93b8556823597c7e2f
  | 10 => 0xb549dc2ab4117c7e2f
  | _ => 0

def VT : Nat := 0xfecfecfecfecfecfec000000fffffffffffffe0fe0fe0fe0fe0fe0fffffffffffffff000fdafdafdafdafdafdaffffff000000fffffffd0fd0fd0fd0fd0fd0ffffffffffff000ffffa5fa5fa5fa5fa5fa5ffffffffffff000000f93f93f93f93f93f93ffffffffffff000000f8cf8cf8cf8cf8cf8cffffffffffff000ffff8af8af8af8af8af8afffffffffffffff000f80f80f80f80f80f80ffffffffffff000000f80f80f80f80f80f80ffffff000000000000f80f80f80f80f80f80000000ffffff000000f75f75f75f75f75f75ffffff000fff000ffff70f70f70f70f70f70fffffffff000fffffff5cf5cf5cf5cf5cf5cfffffffff000000ffff53f53f53f53f53f53fffffffff000000ffff50f50f50f50f50f50ffffff000000000ffff40f40f40f40f40f40ffffff000000000000f10f10f10f10f10f10ffffff000000000000f00f00f00f00f00f00ffffff000000000000eeaeeaeeaeeaeeaeeafffffffff000fff000eafeafeafeafeafeafffffff000ffffff000e9be9be9be9be9be9bfffffffff000fff000e8ee8ee8ee8ee8ee8efffffffff000ffffffe8ae8ae8ae8ae8ae8affffff000000fff000e88e88e88e88e88e88ffffff000000000000e82e82e82e82e82e82ffffff000000000000e80e80e80e80e80e80ffffff000000000000e73e73e73e73e73e73fffffffff000fff000e6ce6ce6ce6ce6ce6cfffffffff000ffffffe65e65e65e65e65e65fffffffffffffff000e60e60e60e60e60e60fffffffff000fff000e60e60e60e60e60e60ffffff000000000000e60e60e60e60e60e60000000fff000fff000e50e50e50e50e50e50ffffff000000000000e40e40e40e40e40e40ffffff000000000000e37e37e37e37e37e37ffffffffffff000000e2de2de2de2de2de2dffffffffffff000fffe25e25e25e25e25e25ffffff000fff000000e24e24e24e24e24e24ffffff000000000000e21e21e21e21e21e21ffffff000000000000e20e20e20e20e20e20ffffff000000000000e1fe1fe1fe1fe1fe1ffffffffff000000fffe13e13e13e13e13e13fffffffff000000000e12e12e12e12e12e12ffffff000000000000e11e11e11e11e11e11ffffff000000000000e10e10e10e10e10e10ffffff000000000000e0ce0ce0ce0ce0ce0cfffffffff000000fffe0ce0ce0ce0ce0ce0cffffff000000000000e0ce0ce0ce0ce0ce0c000000fff000000fffe0ae0ae0ae0ae0ae0affffff000000000000e08e08e08e08e08e08ffffff000000000000e05e05e05e05e05e05ffffff000000000000e04e04e04e04e04e04ffffff000000000000e03e03e03e03e03e03ffffff000000000000e02e02e02e02e02e02ffffff000000000000e01e01e01e01e01e01ffffff000000000000e00e00e00e00e00e00fffffffff000000000e00e00e00e00e00e00ffffff000fff000000e00e00e00e00e00e00ffffff000000fff000e00e00e00e00e00e00ffffff000000000fffe00e00e00e00e00e00ffffff000000000000e00e00e00e00e00e00000000000000000000df3df3df3df3df3df3000ffffffffffff000df0df0df0df0df0df0fff000ffffffffffffdeadeadeadeadeadeafff000fffffffff000de5de5de5de5de5de5fff000fffffffff000de0de0de0de0de0de0000000fffffffff000dc0dc0dc0dc0dc0dc0000000ffffff000000da0da0da0da0da0da0000000ffffff000000d80d80d80d80d80d80000000ffffff000000d60d60d60d60d60d60000000fff000fff000d50d50d50d50d50d50fff000000000000fffce0ce0ce0ce0ce0ce0000000fff000fff000c8ac8ac8ac8ac8ac8afff000000000fff000c60c60c60c60c60c60000000fff000fff000c25c25c25c25c25c25fff000000fff000000c13c13c13c13c13c13000ffffff000000000c00c00c00c00c00c00000000000000000000bdcbdcbdcbdcbdcbdcfff000ffffff000fffbadbadbadbadbadbadfff000ffffff000fffb9fb9fb9fb9fb9fb9f000fffffffff000fffb8eb8eb8eb8eb8eb8efff000ffffffffffffb8cb8cb8cb8cb8cb8c000000ffffff000fffb88b88b88b88b88b88000000ffffff000000b84b84b84b84b84b84000000ffffff000000b80b80b80b80b80b80000000ffffff000000b50b50b50b50b50b50fff000000000000fffb0cb0cb0cb0cb0cb0c000000fff000000fffa8ca8ca8ca8ca8ca8c000000fff000000fffa8aa8aa8aa8aa8aa8afff000000000fff000a25a25a25a25a25a25fff000000fff000000a13a13a13a13a13a13000ffffff000000000a0ca0ca0ca0ca0ca0c000000fff000000fffa00a00a00a00a00a000000000000000000009f59f59f59f59f59f5fff000ffffff000fff9e09e09e09e09e09e0000000ffffff0000009da9da9da9da9da9dafff000ffffffffffff9d39d39d39d39d39d3ffffffffffff000fff9d09d09d09d09d09d0fff000ffffff000fff9d09d09d09d09d09d0fff000000000000fff9d09d09d09d09d09d0000000ffffff0000009c09c09c09c09c09c0000000ffffff0000009b79b79b79b79b79b7ffffffffffff0000009af9af9af9af9af9affff000fffffffff0009a59a59a59a59a59a5fff000ffffff0000009a49a49a49a49a49a4000000ffffff0000009a19a19a19a19a19a1000000ffffff0000009a09a09a09a09a09a0000000ffffff00000099b99b99b99b99b99bfffffffffffffff000993993993993993993000fffffffff000000992992992992992992000000ffffff000000991991991991991991000000ffffff000000990990990990990990000000ffffff00000098c98c98c98c98c98c000000ffffff00000098a98a98a98a98a98afff000fffffffff00098a98a98a98a98a98afff000000000fff00098a98a98a98a98a98a000000ffffff000000988988988988988988000000ffffff000000985985985985985985000000ffffff000000984984984984984984000000ffffff000000983983983983983983000000ffffff000000982982982982982982000000ffffff000000981981981981981981000000ffffff000000980980980980980980fff000ffffff000000980980980980980980000fffffffff000000980980980980980980000000fffffffff000980980980980980980000000ffffff000fff980980980980980980000000ffffff000000980980980980980980000000000000000000950950950950950950fff000000000000fff925925925925925925fff000000fff000000913913913913913913000ffffff0000000009009009009009009000000000000000000008a58a58a58a58a58a5fff000000fff000000893893893893893893000ffffff00000000088a88a88a88a88a88afff000000000fff000880880880880880880000000000000000000825825825825825825fff000000fff000000813813813813813813000ffffff000000000800800800800800800fff000000000000000800800800800800800000fff000000000000800800800800800800000000fff000000000800800800800800800000000000fff00000080080080080080080000000000000000000077c77c77c77c77c77cfff000fff000ffffff750750750750750750fff000000000000fff6ee6ee6ee6ee6ee6eefff000fff000ffffff68a68a68a68a68a68afff000000000fff00067f67f67f67f67f67f000ffffff000ffffff66d66d66d66d66d66dfff000ffffffffffff66c66c66c66c66c66c000000fff000ffffff668668668668668668000000fff000fff000664664664664664664000000fff000fff000660660660660660660000000fff000fff00064c64c64c64c64c64c000000fff000000fff62c62c62c62c62c62c000000fff000000fff625625625625625625fff000000fff000000613613613613613613000ffffff00000000060c60c60c60c60c60c000000fff000000fff6006006006006006000000000000000000005fa5fa5fa5fa5fa5fafff000fff000ffffff5e05e05e05e05e05e0000000fff000fff000575575575575575575fff000ffffffffffff573573573573573573fffffffff000ffffff570570570570570570fff000fff000ffffff570570570570570570fff000000000000fff570570570570570570000000fff000fff000560560560560560560000000fff000fff000550550550550550550fff000000000000fff4fb4fb4fb4fb4fb4fbfffffffff000fff0004ef4ef4ef4ef4ef4effff000fffffffff0004ea4ea4ea4ea4ea4eafff000fff000fff0004e84e84e84e84e84e8000000fff000fff0004e24e24e24e24e24e2000000fff000fff0004e04e04e04e04e04e0000000fff000fff0004ca4ca4ca4ca4ca4cafff000000000fff0004aa4aa4aa4aa4aa4aafff000000000fff00048a48a48a48a48a48afff000000000fff000477477477477477477fffffffffffffff000473473473473473473000ffffff000fff000472472472472472472000000fff000fff000471471471471471471000000fff000fff000470470470470470470000000fff000fff00046c46c46c46c46c46c000000fff000fff00046a46a46a46a46a46a000000fff000fff000468468468468468468000000fff000fff000465465465465465465fff000fffffffff000465465465465465465fff000000fff000000465465465465465465000000fff000fff000464464464464464464000000fff000fff000463463463463463463000000fff000fff000462462462462462462000000fff000fff000461461461461461461000000fff000fff000460460460460460460fff000fff000fff000460460460460460460000ffffff000fff000460460460460460460000000fffffffff000460460460460460460000000fff000ffffff460460460460460460000000fff000fff000460460460460460460000000000000000000453453453453453453000ffffff000000000440440440440440440000000000000000000433433433433433433000ffffff000000000425425425425425425fff000000fff000000420420420420420420000000000000000000413413413413413413000ffffff000000000400400400400400400fff000000000000000400400400400400400000fff000000000000400400400400400400000000fff000000000400400400400400400000000000000fff0004004004004004004000000000000000000003de3de3de3de3de3defff000fff000ffffff38c38c38c38c38c38c000000fff000000fff37d37d37d37d37d37dfff000ffffff000fff35f35f35f35f35f35ffffffffff000000fff35c35c35c35c35c35cfff000fff000000fff358358358358358358fff000000000000fff354354354354354354fff000000000000fff350350350350350350fff000000000000fff34c34c34c34c34c34c000000fff000000fff31c31c31c31c31c31c000000fff000000fff30c30c30c30c30c30c000000fff000000fff2af2af2af2af2af2affff000ffffffffffff29f29f29f29f29f29ffffffffff000ffffff28e28e28e28e28e28efff000fff000ffffff28e28e28e28e28e28efff000000000fff00028e28e28e28e28e28e000000fff000000fff28c28c28c28c28c28c000000fff000000fff28a28a28a28a28a28afff000000000fff00026c26c26c26c26c26c000000fff000000fff25c25c25c25c25c25c000000fff000000fff24c24c24c24c24c24c000000fff000000fff23f23f23f23f23f23fffffffffffff000fff22d22d22d22d22d22dfff000ffffff000fff22d22d22d22d22d22dfff000000fff00000022d22d22d22d22d22d000000fff000000fff22c22c22c22c22c22c000000fff000000fff225225225225225225fff000000fff00000021f21f21f21f21f21f000ffffff000000fff21e21e21e21e21e21e000000fff000000fff21d21d21d21d21d21d000000fff000000fff21c21c21c21c21c21c000000fff000000fff21b21b21b21b21b21b000ffffff000000000217217217217217217000ffffff000000000213213213213213213000ffffff00000000020f20f20f20f20f20f000000fff000000fff20e20e20e20e20e20e000000fff000000fff20d20d20d20d20d20d000000fff000000fff20c20c20c20c20c20cfff000fff000000fff20c20c20c20c20c20c000ffffff000000fff20c20c20c20c20c20c000000ffffff000fff20c20c20c20c20c20c000000fff000ffffff20c20c20c20c20c20c000000fff000000fff20c20c20c20c20c20c000000000000000000208208208208208208000000000000000000204204204204204204000000000000000000200200200200200200fff000000000000000200200200200200200000fff000000000000200200200200200200000000fff000000000200200200200200200000000000000000fff2002002002002002000000000000000000001ff1ff1ff1ff1ff1fffff000000fffffffff1db1db1db1db1db1dbfffffffff000ffffff1da1da1da1da1da1dafff000000000ffffff1d81d81d81d81d81d8fff000000000000fff1d21d21d21d21d21d2fff000000000000fff1d01d01d01d01d01d0fff000000000000fff1ca1ca1ca1ca1ca1cafff000000000fff0001a51a51a51a51a51a5fff000000fff00000019a19a19a19a19a19afff000000000fff000193193193193193193000ffffff00000000018a18a18a18a18a18afff000000000fff000180180180180180180000000000000000000177177177177177177ffffffffffff000fff175175175175175175fff000000fff000fff174174174174174174fff000000000000fff171171171171171171fff000000000000fff170170170170170170fff000000000000fff165165165165165165fff000000fff00000015c15c15c15c15c15cfff000000000000fff15a15a15a15a15a15afff000000000000fff158158158158158158fff000000000000fff155155155155155155fff000000000000fff154154154154154154fff000000000000fff153153153153153153fffffffff000000fff153153153153153153fff000000000000fff153153153153153153000ffffff000000000152152152152152152fff000000000000fff151151151151151151fff000000000000fff150150150150150150ffffff000000000fff150150150150150150fff000fff000000fff150150150150150150fff000000fff000fff150150150150150150fff000000000ffffff150150150150150150fff000000000000fff150150150150150150000000000000000000140140140140140140000000000000000000135135135135135135fff000000fff000000125125125125125125fff000000fff000000113113113113113113000ffffff000000000110110110110110110000000000000000000100100100100100100fff000000000000000100100100100100100000000fff000000000100100100100100100000000000fff000000100100100100100100000000000000000fff1001001001001001000000000000000000000ea0ea0ea0ea0ea0eafff000000000fff0000da0da0da0da0da0dafff000000000fff0000ca0ca0ca0ca0ca0cafff000000000fff0000bf0bf0bf0bf0bf0bffffffffffffffff0000af0af0af0af0af0affff000000ffffff0000ae0ae0ae0ae0ae0aefff000000000fff0000ad0ad0ad0ad0ad0adfff000000fff0000000ab0ab0ab0ab0ab0abfff000000000fff0000aa0aa0aa0aa0aa0aafff000000000fff0000a70a70a70a70a70a7fff000000fff0000000a50a50a50a50a50a5fff000000fff00000009b09b09b09b09b09bfffffffff000fff00009b09b09b09b09b09bfff000000000fff00009b09b09b09b09b09b000ffffff00000000009a09a09a09a09a09afff000000000fff000093093093093093093000ffffff00000000008f08f08f08f08f08ffff000000000fff00008e08e08e08e08e08efff000000000fff00008b08b08b08b08b08bfff000000000fff00008a08a08a08a08a08affffff000000fff00008a08a08a08a08a08afff000fff000fff00008a08a08a08a08a08afff000000ffffff00008a08a08a08a08a08afff000000000ffffff08a08a08a08a08a08afff000000000fff00008a08a08a08a08a08a000000000000000000088088088088088088000000000000000000082082082082082082000000000000000000080080080080080080fff000000000000000080080080080080080000000fff000000000080080080080080080000000000fff000000080080080080080080000000000000fff000080080080080080080000000000000000000075075075075075075fff000000fff000000073073073073073073000ffffff000000000065065065065065065fff000000fff000000060060060060060060000000000000000000053053053053053053000ffffff000000000050050050050050050000000000000000000040040040040040040fff000000000000000040040040040040040000000fff000000000040040040040040040000000000000fff000040040040040040040000000000000000fff040040040040040040000000000000000000037037037037037037ffffffffffff000000037037037037037037fff000000fff000000037037037037037037000ffffff000000000035035035035035035fff000000fff000000033033033033033033000ffffff00000000002f02f02f02f02f02ffff000000fff00000002d02d02d02d02d02dfff000000fff000000027027027027027027fff000000fff000000025025025025025025ffffff000fff000000025025025025025025fff000ffffff000000025025025025025025fff000000ffffff000025025025025025025fff000000fff000fff025025025025025025fff000000fff000000025025025025025025000000000000000000024024024024024024000000000000000000021021021021021021000000000000000000020020020020020020fff000000000000000020020020020020020000000fff000000000020020020020020020000000000fff000000020020020020020020000000000000fff00002002002002002002000000000000000000001f01f01f01f01f01f000ffffff00000000001b01b01b01b01b01b000ffffff000000000017017017017017017000ffffff000000000013013013013013013fffffffff000000000013013013013013013000fffffffff000000013013013013013013000ffffff000fff000013013013013013013000ffffff000000fff013013013013013013000ffffff000000000013013013013013013000000000000000000012012012012012012000000000000000000011011011011011011000000000000000000010010010010010010fff000000000000000010010010010010010000fff000000000000010010010010010010000000fff000000000010010010010010010000000000000000fff01001001001001001000000000000000000000c00c00c00c00c00c00000000000000000000a00a00a00a00a00a000000000000000000008008008008008008fff000000000000000008008008008008008000000fff000000000008008008008008008000000000000fff000008008008008008008000000000000000fff008008008008008008000000000000000000005005005005005005000000000000000000004004004004004004fff000000000000000004004004004004004000000fff000000000004004004004004004000000000fff000000004004004004004004000000000000000fff004004004004004004000000000000000000003003003003003003000000000000000000002002002002002002fff000000000000000002002002002002002000fff000000000000002002002002002002000000fff000000000002002002002002002000000000000fff000002002002002002002000000000000000000001001001001001001fff000000000000000001001001001001001000fff000000000000001001001001001001000000fff000000000001001001001001001000000000fff000000001001001001001001000000000000000000000000000000000000ffffff000000000000000000000000000000fff000000fff000000000000000000000000fff000000000fff000000000000000000000fff000000000000fff000000000000000000fff000000000000000000000000000000000000ffffff000000000000000000000000000000fff000000000000000000000000000000000000ffffff000000000000000000000000000000fff000fff000000000000000000000000000fff000000fff000000000000000000000000fff000000000000000000000000000000000000fff000000000000000000000000000000000000fff000000000000000000000000000000000000fff000000000000000000000000000000000000

def S (s j : Nat) : List Nat :=
  (List.range (fld (LT s) 4 j)).map (fun t => fld VT 144 (fld (DT s) 9 (9*j+t)))

def idx (s : Nat) (zs : List Nat) : Nat := bsr (HT s) 32 (hk zs) 12 0 (NN s)

def Z (s : Nat) := bar 72 S NN idx s

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 8) => (fun x : Fin 8 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel

theorem enc_goalG : encL cube rowsG = goal 72 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (covUp 72 zs &&& lo 72) ≠ lo 72 := by decide +kernel

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
theorem h7x32 : span (Z 7) 8 32 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x40 : span (Z 7) 8 40 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x48 : span (Z 7) 8 48 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x56 : span (Z 7) 8 56 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x64 : span (Z 7) 8 64 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x72 : span (Z 7) 8 72 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x80 : span (Z 7) 8 80 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x88 : span (Z 7) 8 88 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x96 : span (Z 7) 8 96 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x104 : span (Z 7) 8 104 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x112 : span (Z 7) 8 112 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x120 : span (Z 7) 8 120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x128 : span (Z 7) 8 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x136 : span (Z 7) 8 136 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x144 : span (Z 7) 8 144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x152 : span (Z 7) 8 152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x160 : span (Z 7) 8 160 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x168 : span (Z 7) 8 168 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x176 : span (Z 7) 8 176 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x184 : span (Z 7) 8 184 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x192 : span (Z 7) 8 192 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x200 : span (Z 7) 8 200 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x208 : span (Z 7) 8 208 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x216 : span (Z 7) 8 216 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x224 : span (Z 7) 8 224 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x232 : span (Z 7) 8 232 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x240 : span (Z 7) 8 240 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x248 : span (Z 7) 8 248 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x256 : span (Z 7) 8 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x264 : span (Z 7) 8 264 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x272 : span (Z 7) 8 272 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x280 : span (Z 7) 8 280 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x288 : span (Z 7) 8 288 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x296 : span (Z 7) 8 296 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x304 : span (Z 7) 8 304 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x312 : span (Z 7) 8 312 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x320 : span (Z 7) 8 320 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x328 : span (Z 7) 8 328 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x336 : span (Z 7) 8 336 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x344 : span (Z 7) 8 344 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x352 : span (Z 7) 8 352 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x360 : span (Z 7) 8 360 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x368 : span (Z 7) 8 368 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x376 : span (Z 7) 8 376 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x384 : span (Z 7) 8 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x392 : span (Z 7) 8 392 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x400 : span (Z 7) 8 400 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x408 : span (Z 7) 8 408 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x416 : span (Z 7) 8 416 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x424 : span (Z 7) 8 424 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x432 : span (Z 7) 8 432 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x440 : span (Z 7) 8 440 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x448 : span (Z 7) 8 448 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x456 : span (Z 7) 8 456 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x464 : span (Z 7) 8 464 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x472 : span (Z 7) 8 472 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x480 : span (Z 7) 8 480 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x488 : span (Z 7) 8 488 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x496 : span (Z 7) 8 496 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h7x504 : span (Z 7) 5 504 = true := by decide +kernel
theorem z7 : span (Z 7) 509 0 = true := (@span_join (Z 7) 256 0 253 (@span_join (Z 7) 128 0 128 (@span_join (Z 7) 64 0 64 (@span_join (Z 7) 32 0 32 (@span_join (Z 7) 16 0 16 (@span_join (Z 7) 8 0 8 h7x0 h7x8) (@span_join (Z 7) 8 16 8 h7x16 h7x24)) (@span_join (Z 7) 16 32 16 (@span_join (Z 7) 8 32 8 h7x32 h7x40) (@span_join (Z 7) 8 48 8 h7x48 h7x56))) (@span_join (Z 7) 32 64 32 (@span_join (Z 7) 16 64 16 (@span_join (Z 7) 8 64 8 h7x64 h7x72) (@span_join (Z 7) 8 80 8 h7x80 h7x88)) (@span_join (Z 7) 16 96 16 (@span_join (Z 7) 8 96 8 h7x96 h7x104) (@span_join (Z 7) 8 112 8 h7x112 h7x120)))) (@span_join (Z 7) 64 128 64 (@span_join (Z 7) 32 128 32 (@span_join (Z 7) 16 128 16 (@span_join (Z 7) 8 128 8 h7x128 h7x136) (@span_join (Z 7) 8 144 8 h7x144 h7x152)) (@span_join (Z 7) 16 160 16 (@span_join (Z 7) 8 160 8 h7x160 h7x168) (@span_join (Z 7) 8 176 8 h7x176 h7x184))) (@span_join (Z 7) 32 192 32 (@span_join (Z 7) 16 192 16 (@span_join (Z 7) 8 192 8 h7x192 h7x200) (@span_join (Z 7) 8 208 8 h7x208 h7x216)) (@span_join (Z 7) 16 224 16 (@span_join (Z 7) 8 224 8 h7x224 h7x232) (@span_join (Z 7) 8 240 8 h7x240 h7x248))))) (@span_join (Z 7) 128 256 125 (@span_join (Z 7) 64 256 64 (@span_join (Z 7) 32 256 32 (@span_join (Z 7) 16 256 16 (@span_join (Z 7) 8 256 8 h7x256 h7x264) (@span_join (Z 7) 8 272 8 h7x272 h7x280)) (@span_join (Z 7) 16 288 16 (@span_join (Z 7) 8 288 8 h7x288 h7x296) (@span_join (Z 7) 8 304 8 h7x304 h7x312))) (@span_join (Z 7) 32 320 32 (@span_join (Z 7) 16 320 16 (@span_join (Z 7) 8 320 8 h7x320 h7x328) (@span_join (Z 7) 8 336 8 h7x336 h7x344)) (@span_join (Z 7) 16 352 16 (@span_join (Z 7) 8 352 8 h7x352 h7x360) (@span_join (Z 7) 8 368 8 h7x368 h7x376)))) (@span_join (Z 7) 64 384 61 (@span_join (Z 7) 32 384 32 (@span_join (Z 7) 16 384 16 (@span_join (Z 7) 8 384 8 h7x384 h7x392) (@span_join (Z 7) 8 400 8 h7x400 h7x408)) (@span_join (Z 7) 16 416 16 (@span_join (Z 7) 8 416 8 h7x416 h7x424) (@span_join (Z 7) 8 432 8 h7x432 h7x440))) (@span_join (Z 7) 32 448 29 (@span_join (Z 7) 16 448 16 (@span_join (Z 7) 8 448 8 h7x448 h7x456) (@span_join (Z 7) 8 464 8 h7x464 h7x472)) (@span_join (Z 7) 16 480 13 (@span_join (Z 7) 8 480 8 h7x480 h7x488) (@span_join (Z 7) 8 496 5 h7x496 h7x504))))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x0 : span (Z 8) 8 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x8 : span (Z 8) 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x16 : span (Z 8) 8 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x24 : span (Z 8) 8 24 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x32 : span (Z 8) 8 32 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x40 : span (Z 8) 8 40 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x48 : span (Z 8) 8 48 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x56 : span (Z 8) 8 56 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x64 : span (Z 8) 8 64 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x72 : span (Z 8) 8 72 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x80 : span (Z 8) 8 80 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x88 : span (Z 8) 8 88 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x96 : span (Z 8) 8 96 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x104 : span (Z 8) 8 104 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x112 : span (Z 8) 8 112 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x120 : span (Z 8) 8 120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x128 : span (Z 8) 8 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x136 : span (Z 8) 8 136 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x144 : span (Z 8) 8 144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x152 : span (Z 8) 8 152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x160 : span (Z 8) 8 160 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x168 : span (Z 8) 8 168 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x176 : span (Z 8) 8 176 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x184 : span (Z 8) 8 184 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x192 : span (Z 8) 8 192 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x200 : span (Z 8) 8 200 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x208 : span (Z 8) 8 208 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x216 : span (Z 8) 8 216 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x224 : span (Z 8) 8 224 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x232 : span (Z 8) 8 232 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x240 : span (Z 8) 8 240 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x248 : span (Z 8) 8 248 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x256 : span (Z 8) 8 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x264 : span (Z 8) 8 264 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x272 : span (Z 8) 8 272 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x280 : span (Z 8) 8 280 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x288 : span (Z 8) 8 288 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x296 : span (Z 8) 8 296 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x304 : span (Z 8) 8 304 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x312 : span (Z 8) 8 312 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x320 : span (Z 8) 8 320 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x328 : span (Z 8) 8 328 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x336 : span (Z 8) 8 336 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x344 : span (Z 8) 8 344 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x352 : span (Z 8) 8 352 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x360 : span (Z 8) 8 360 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x368 : span (Z 8) 8 368 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x376 : span (Z 8) 8 376 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x384 : span (Z 8) 8 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x392 : span (Z 8) 8 392 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x400 : span (Z 8) 8 400 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x408 : span (Z 8) 8 408 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x416 : span (Z 8) 8 416 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x424 : span (Z 8) 8 424 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x432 : span (Z 8) 8 432 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x440 : span (Z 8) 8 440 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x448 : span (Z 8) 8 448 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x456 : span (Z 8) 8 456 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x464 : span (Z 8) 8 464 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x472 : span (Z 8) 8 472 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x480 : span (Z 8) 8 480 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x488 : span (Z 8) 8 488 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x496 : span (Z 8) 8 496 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x504 : span (Z 8) 8 504 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x512 : span (Z 8) 8 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x520 : span (Z 8) 8 520 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x528 : span (Z 8) 8 528 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x536 : span (Z 8) 8 536 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x544 : span (Z 8) 8 544 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h8x552 : span (Z 8) 8 552 = true := by decide +kernel
theorem z8 : span (Z 8) 560 0 = true := (@span_join (Z 8) 280 0 280 (@span_join (Z 8) 136 0 144 (@span_join (Z 8) 64 0 72 (@span_join (Z 8) 32 0 32 (@span_join (Z 8) 16 0 16 (@span_join (Z 8) 8 0 8 h8x0 h8x8) (@span_join (Z 8) 8 16 8 h8x16 h8x24)) (@span_join (Z 8) 16 32 16 (@span_join (Z 8) 8 32 8 h8x32 h8x40) (@span_join (Z 8) 8 48 8 h8x48 h8x56))) (@span_join (Z 8) 32 64 40 (@span_join (Z 8) 16 64 16 (@span_join (Z 8) 8 64 8 h8x64 h8x72) (@span_join (Z 8) 8 80 8 h8x80 h8x88)) (@span_join (Z 8) 16 96 24 (@span_join (Z 8) 8 96 8 h8x96 h8x104) (@span_join (Z 8) 8 112 16 h8x112 (@span_join (Z 8) 8 120 8 h8x120 h8x128))))) (@span_join (Z 8) 72 136 72 (@span_join (Z 8) 32 136 40 (@span_join (Z 8) 16 136 16 (@span_join (Z 8) 8 136 8 h8x136 h8x144) (@span_join (Z 8) 8 152 8 h8x152 h8x160)) (@span_join (Z 8) 16 168 24 (@span_join (Z 8) 8 168 8 h8x168 h8x176) (@span_join (Z 8) 8 184 16 h8x184 (@span_join (Z 8) 8 192 8 h8x192 h8x200)))) (@span_join (Z 8) 32 208 40 (@span_join (Z 8) 16 208 16 (@span_join (Z 8) 8 208 8 h8x208 h8x216) (@span_join (Z 8) 8 224 8 h8x224 h8x232)) (@span_join (Z 8) 16 240 24 (@span_join (Z 8) 8 240 8 h8x240 h8x248) (@span_join (Z 8) 8 256 16 h8x256 (@span_join (Z 8) 8 264 8 h8x264 h8x272)))))) (@span_join (Z 8) 136 280 144 (@span_join (Z 8) 64 280 72 (@span_join (Z 8) 32 280 32 (@span_join (Z 8) 16 280 16 (@span_join (Z 8) 8 280 8 h8x280 h8x288) (@span_join (Z 8) 8 296 8 h8x296 h8x304)) (@span_join (Z 8) 16 312 16 (@span_join (Z 8) 8 312 8 h8x312 h8x320) (@span_join (Z 8) 8 328 8 h8x328 h8x336))) (@span_join (Z 8) 32 344 40 (@span_join (Z 8) 16 344 16 (@span_join (Z 8) 8 344 8 h8x344 h8x352) (@span_join (Z 8) 8 360 8 h8x360 h8x368)) (@span_join (Z 8) 16 376 24 (@span_join (Z 8) 8 376 8 h8x376 h8x384) (@span_join (Z 8) 8 392 16 h8x392 (@span_join (Z 8) 8 400 8 h8x400 h8x408))))) (@span_join (Z 8) 72 416 72 (@span_join (Z 8) 32 416 40 (@span_join (Z 8) 16 416 16 (@span_join (Z 8) 8 416 8 h8x416 h8x424) (@span_join (Z 8) 8 432 8 h8x432 h8x440)) (@span_join (Z 8) 16 448 24 (@span_join (Z 8) 8 448 8 h8x448 h8x456) (@span_join (Z 8) 8 464 16 h8x464 (@span_join (Z 8) 8 472 8 h8x472 h8x480)))) (@span_join (Z 8) 32 488 40 (@span_join (Z 8) 16 488 16 (@span_join (Z 8) 8 488 8 h8x488 h8x496) (@span_join (Z 8) 8 504 8 h8x504 h8x512)) (@span_join (Z 8) 16 520 24 (@span_join (Z 8) 8 520 8 h8x520 h8x528) (@span_join (Z 8) 8 536 16 h8x536 (@span_join (Z 8) 8 544 8 h8x544 h8x552)))))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h9x0 : span (Z 9) 8 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h9x8 : span (Z 9) 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h9x16 : span (Z 9) 8 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h9x24 : span (Z 9) 8 24 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h9x32 : span (Z 9) 8 32 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h9x40 : span (Z 9) 8 40 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h9x48 : span (Z 9) 7 48 = true := by decide +kernel
theorem z9 : span (Z 9) 55 0 = true := (@span_join (Z 9) 24 0 31 (@span_join (Z 9) 8 0 16 h9x0 (@span_join (Z 9) 8 8 8 h9x8 h9x16)) (@span_join (Z 9) 16 24 15 (@span_join (Z 9) 8 24 8 h9x24 h9x32) (@span_join (Z 9) 8 40 7 h9x40 h9x48)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h10x0 : span (Z 10) 1 0 = true := by decide +kernel
theorem z10 : span (Z 10) 1 0 = true := h10x0

theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · simp [NN]
  · simp [NN]
  · simp [NN]
  · simp [NN]
  · simp [NN]
  · simp [NN]
  · simp [NN]
  · intro i hi
    exact span_ok z7 i (Nat.zero_le i) (by simpa [NN] using hi)
  · intro i hi
    exact span_ok z8 i (Nat.zero_le i) (by simpa [NN] using hi)
  · intro i hi
    exact span_ok z9 i (Nat.zero_le i) (by simpa [NN] using hi)
  · intro i hi
    exact span_ok z10 i (Nat.zero_le i) (by simpa [NN] using hi)

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : MonRun (goal 72) s xsG) : False := by
  have hl := run_len h
  have hlen : xsG.length = 8 := by decide +kernel
  rw [hlen] at hl
  have hlo : 7 ≤ s := by omega
  interval_cases s
  · exact bar_all checked 7 (by decide) 123 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 7 123)) h)
  · exact bar_all checked 8 (by decide) 142 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 8 142)) h)
  · exact bar_all checked 9 (by decide) 12 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 9 12)) h)
  · exact bar_all checked 10 (by decide) 0 (by decide)
      (Run.perm (by decide +kernel : xsG.Perm (S 10 0)) h)

theorem no_small : ¬ HasMonoSize 8 cube 10 :=
  encoded_cube_mono_exclusion rowsG xsG 72 enc_inputsG enc_goalG proper_failG noRunFull

end PEqualNP.Outside.L_meta_740_aux

theorem PEqualNP.Outside.L_meta_740 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7), (4, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 11 ≤ C.size := by
  intro C hm hev
  exact PEqualNP.Outside.L_meta_740_aux.cube_lower_from_mono_exclusion PEqualNP.Outside.L_meta_740_aux.no_small C hm hev
