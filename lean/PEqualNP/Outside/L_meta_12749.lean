import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12749_aux

-- From pequalnp-proofs/lean/PEqualNP/Outside/L_meta_7402.lean
section

namespace CoreTable7402_aux

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

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := a ^^^ m
       f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
            (slack ≥ 2 && f (w :: a :: b :: r)))

theorem next_one {k a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((a ^^^ mask k) :: kept save a rest))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s + 2 - ws.length) ws f = true := by
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
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s + 2 - ws.length) ws f = true := by
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
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s + 2 - ws.length) ws f = true := by
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

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) →
      next (mask k) (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

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

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s + 1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;>
        grind
    · exact hw _ (by simp [ht])

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

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s + 1) :
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
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s + 1
  · simp [covers, he, required_up h he]
  · simp [covers, he, required h]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat + c.toNat
  let y := (!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s + 1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s + 1)
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

def sumBelow (v : Nat → Nat) : List Nat → Nat → Bool
  | [], n => n != 0
  | w :: ws, n => decide (v w < n) && sumBelow v ws (n - v w)

theorem sumBelow_iff (v : Nat → Nat) (ws : List Nat) (n : Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n := by
  induction ws generalizing n with
  | nil =>
    simp [sumBelow]
  | cons w ws ih =>
    rw [sumBelow, Bool.and_eq_true, decide_eq_true_eq, ih, List.map_cons, List.sum_cons]
    omega

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s + 1 && sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f (goal k))

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s + 1
    · simp [hl]
      by_contra hb
      have hsum := (sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hb)
      exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)) hsum
    · simp [hl]

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

def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo

def hw (w : Nat) : Nat := (w % 11400714819323198549 + 317) ^ 3 % 11400714819323198549 + 1

def hz : List Nat → Nat
  | [] => 0
  | w :: t => hw w + hz t

def hk (zs : List Nat) : Nat := hz zs % 4294967291

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def scr (k s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck k s zs)

theorem scr_no {k s : Nat} (pool : List Nat) {zs : List Nat}
    (h : NatRun (mask k) (goal k) s zs) : scr k s pool zs = false := by
  unfold scr
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro x _
  rw [scoreCheck_no h x]
  simp

def bar (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (mask k) (s + 2 - ws.length) ws fun zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs)))

theorem bar_sound {k S N idx ori pool} {s i : Nat} (hb : bar k S N idx ori pool s i = true)
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) :=
      covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs))
    have hF (zs) (hz : NatRun (mask k) (goal k) s zs) : F zs = true := by
      simp only [F, covers_ok hz, scr_no pool hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k S N idx ori pool} {cap : Nat}
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k S N idx ori pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

end CoreTable7402_aux

end

-- From .pnp-tools/Monotone12750Lower.lean
section

namespace Monotone12750Lower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CoreTable7402_aux

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4277075694 * 2 ^ 32 + 4277067904)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

private def k : Nat := 63

private def rows : List Nat := [36, 16, 40, 52, 3, 11, 48, 1, 10, 40, 6, 9, 24, 10, 48, 2, 5, 9, 12, 24, 11, 36, 5, 20, 5, 5, 16, 32, 56, 52, 6, 56, 5, 56, 12, 52, 6, 56, 5, 5, 6, 56, 56, 12, 11, 5, 6, 52, 11, 56, 52, 52, 52, 12, 12, 52, 11, 11, 6, 6, 56, 52, 5, 37, 18, 44, 60, 19, 43, 50, 33, 42, 41, 38, 41, 26, 26, 49, 34, 13, 25, 28, 25, 15, 44, 37, 22, 7, 21, 17, 34, 57, 54, 34, 7, 44, 44, 17, 13, 14, 13, 17, 14, 18, 34, 33, 34, 14, 33, 28, 18, 7, 18, 14, 28, 34, 33, 7, 33, 18, 33, 7, 33, 17, 17, 34]

private def inputs : List Nat := [0x1f7092364bada558c30130c1035308b0, 0x22abcdc874c85ab90f0151104010a530, 0x226a85dd1fa8206ecfce9dd63e50409, 0x6285d881f9d9613631e26901e3b24, 0x188560a21b47382d309e862ab488504a, 0x25581701bc3067f6b09e862ab820424d]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
private theorem encodeTarget : encL target rows = goal k := by decide +kernel

set_option maxRecDepth 30000 in
private theorem encodeInputs :
    (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map (fun f => encL f rows)
      = inputs := by decide +kernel

private theorem masked : mask k = 2 ^ rows.length - 1 := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
private theorem properFails : ∀ ws ∈ inputs.sublists, ws ≠ inputs →
    cov k ws &&& lo k ≠ lo k := by decide +kernel

private def proofCount : Nat → Nat
  | 2 => 22
  | 3 => 108
  | 4 => 580
  | 5 => 1204
  | 6 => 707
  | 7 => 49
  | 8 => 1
  | _ => 0

private def stateWidth : Nat → Nat
  | 2 => 34
  | 3 => 44
  | 4 => 54
  | 5 => 64
  | 6 => 74
  | 7 => 74
  | 8 => 64
  | _ => 0

private def hashBlocks : Nat → Nat → Nat
  | 2, 0 => 0xf7d7c748f3f4ed2bed011beee8b641b8e5eb5a45dccafed0d36d995ed03415d8bf484d46bdd73718bafd73108e85c1938d62dea88218b4ad7cb3e29c79da1e9477162fce6cbf57d067643fcb24ec280523d3b4be1af9395a
  | 3, 0 => 0x9d4797c89cd8621d9b4ef08096ef082f9661712095efe800944b7de2921696ea902d922f8ef065dd8dbde7e389f7174385665396824d2e9980a73fa67bd810f07b7d72397a7861d5791434bb78e5620977e4359f75ed449973e9601f712d6a676e53a65f6b10dd606837195865db4264659ee56d650ecba257f390a45772658553a0797150f3426e4f52e5de4ec56d194c784e1748d20b144693c4ec468b550543d87baa42652f183e7d63a53e668c923dbc5ee13cfaa87537318a8833faf91d25aef495235a5ae21e0333961c5226181c1087ff1960c297174c25eb14ac6070117235320f65faa80dc6ce7d0c3a112d0c2ebc1109b6c78e0691a59604ef2dbf
  | 3, 1 => 0xfe1f20a5fc8d2d96fc054bdaf70deab7f5f03612f3d63293f2125d2ff067552aefc4a6ade9dfc7c9e9a4fdbce8a3f22ae695557ce6691089e44fcd51e2899922e27d32dddb86763bd4a8e879d1c66bf5cb228e04cac8cd9cc6b79bebc3e5303ec0ca275cbdfc985dbdd7cba8bafd7310b799a257b6120b1eb611e7a5b5cb6f8db51f02ecb506bccfb4b797d1b39703a7aeea933faa773359a7083208a61371a7a4b32a899e9c6a3a9e3cfbaf9d61bb2f
  | 4, 0 => 0x1fdb193a1e9a10ce1e6651401d524a0f1d3ab1ca1c5d38141b60ef2b1ac9a3e81a158489194e03c5185acacf1834cbc517f37b4117b56bb317abf35c1612798c1596b01b158dd4511571c6481535149c1486656814042c4e13a9a49513a84eaf128f4c10125ef2ec11c474bc11c2f4281195b80511764e71116bede01150df8c10ae6f641068f3d310102a450fd9b9f10fbd36660ec2ef580e9dda280e8636460e4aae620e30cf5f0e2bcad90e0501df0dd4ab5c0cab98f80c9755300c2ebc110c1d67500bbbc8950b6848930ace163309e9559509dced5b095aca7f06a3f71205ea56de05903930052e8e3304cef3e503d4e86402f0f90d028e299d00b0b1df
  | 4, 1 => 0x3d13727c3ce0b6123cda84543b9a34543b1110ca3a39ae743957d17838db990738d980d838844ef237ad8808372d58d436f220ba34e91af1345be36533c6373f33bae22333b95fef33ae388632f594fc324c1adf3244162a31d3afe731a8bc0331a2584f3150649331256ee930fdc9c4308a369c3051c5e53049651f2fe8d0ca2fa57dec2f46f12b2e58ef0c2e1aa4032d2f8c8d2c98f5232bb04c422b5870fa2acc2f642a33ddb8299db9df29700a7a292013e328ef145628dab57c28b71881270b8d8d26ba673d267d9f562658f167263bcc4225ea7342257555b725569dd6246a5e06239171f1231d5cd522f7b4f621fa4e8f214c4b1421074bdd20eda94d
  | 4, 2 => 0x5a7a897159a37a7c596652735942577e59177d4f5869605757c246335785959455f4c43755f1e7e155dea07455b9157b558248ba5563752f55041c7554efe20753cc59d65361007b52a9d4c252969613525dc32751ba7e8a519185af517dcd0d513956aa507a31d24eac3a3e4e343bb74e137fbb4e0690584e02a1164d3b1aa74b8c3e2b4b064df24ac321724aab306c4aa7e5424a77166c4a009f2149e4b77f49bebe3949881751496fb34f48ea11c248a35e7d487d4fad487d26ca47aa0f9d478f0c1f46b11ed8459c01b4456cca39455354b844020c354303d18442fdbd0442b2f0224298fc3941f1dcc44026ed3c3f503d323f2f4f533d9665f33d710e8a
  | 4, 3 => 0x773c8718763e65b9760d8fdb756d3368748ba3de747b013a747adf097474785a7460bba2743865497430e3777423e1ca742308f373f185f77194762b710abccd70cc79db70b480a270a14f3e709e248c6fc7d5016f70cafb6f0d90ad6e48db196e352c0b6e1feafe6d5453126d3aeb3a6ce2fb186c19d76e6c176f646be7853d6bc39cc96ba1fb296b828f5c6b64a1bc6b2e680169e28dc06935f00968dae9766837195867f27d1c660989b765d7bd1365bd9ec1651c5e8d6513b0e564ad2caf642ca224637840a762ff6dd361f13e1960ff72f260f9f789609743a45fffdfbf5ebdb09a5eba2c835e839eda5d7710945b91dab25b402eaa5ac07c385a9c9473
  | 4, 4 => 0x928289ac921696ea915e1d2f910c4e9d900d6e528fc33f6a8fb839eb8f41bcad8f3ede748f1d5b688ed100c38e3846408e2b56dd8e18e4408d6768768d59f86e8d2b0b7f8cfec3128cfa89e38c1fe0a98c0d4c088bdd880f8ba92de78accabc78ab0278189f71743887e8a0f886825a8886679ad884c6ae887c7ddf9873e49d18708525585ae019d85ac966384ea69ff84465edf83b13c04839af87080eb17c080b6474080672046804bb3c180007ec47f00123d7efe8b977ee034dc7ecdacd37eb72e6d7d76290f7d7352577d057c977c9852e27c7b76177c2c51567be3976e7b1a339d7a5e74f979e04e4b78dc4ba178b4a577789c284f77ff588e77521f59
  | 4, 5 => 0xa70f3a6ca633ac7da5fc8398a5f924ada5eb3699a58054fea45168a9a4161511a3e79f51a3d91530a3b620eca3ac7834a3643702a35147cda309984ba26e4b7aa23bb1dea235caada1ef1e9aa1e1f176a1243977a11ebe0ea10c0f03a0c01028a0bb2b8ea0a05acda071881ba0631160a0426e309f3af3cb9f1531d19e6a7d969dd0bfc59d2e2d6a9c5c6fe29bf74ef59b8854ca9b81b9d39b7586319b6b34599b43cb979a9f4ff69a099f8e992a9dea9922e16c990506ea988e26dc9811712397f1102797e34b3696cef0639675b0f4966f9743951ebad6951e50099502397b94d0ffdb946df40f941d12289418eff193df0ca592fd1bf792a392a592938beb
  | 4, 6 => 0xc55316cfc4ede141c4d3bddac464882fc326fffdc274339ec252800fc2483ba4c0f8eba3bfd3c6b1bf0960ccbf04fb61beabdb75bea40a26bd9e40a6bd888cd7bd71c135bd2795acbc9fa0ebbc56bb92bc36f202bbe5677cba997fc5ba603cacba5da2feb9a2bcfcb8d96bfcb8c0eed4b844a83db84091cab6dc5840b69e75fcb6325660b6168f19b54a0df5b5452029b4be091cb45d2bceb447cf78b2d7a458b2287d96b1c87370b1833d55b1794f0cb0e2abe1af325732aee5d742aee3bd75ae8119d3ae7e88f6ad8ee124acf279a8ace950b7ac9559dcac7548a8abf52ca7abdb746cab3e768ea9d954aba9048c96a8df8fcfa7c8848ca7447976a73156a0
  | 4, 7 => 0xe42886f1e3d13eb9e2f8964be2edc589e2899922e1ea526ce17f5a5ae0dff213e0cfeb63e0c8e2c3df90b0d0de8234e1de760e61dd5ca5dbdd13a97ddcef2d1adcab28fedc92e2e1dc43bde3db2329b9d98e4bf4d92b832ad888d76ad837beeed8248be1d7e7b90ed69a7779d55e630bd54cffbed543815bd4dd2c53d494851ed441d8add30d5b85d26063ded203596bd180b4e6d0940125d06d6941d03c6b1ccfad26e0cfa66ae0ceb83b27ce907272ce616fbcce2a92f5cd9f97b9cd9244cecd87237bccaebb35cc8b0553cc455372cc2e2ff7cc024e94cb97020bcb7bc9deca85e00ac982846ac94b4287c8c2ec7bc7c10915c6985110c648057dc570dd2c
  | 4, 8 => 0xfe3a1cc9fdbe59c2fd719f69fd65f588fd4c5c31fd41d4adfcc8186afc896efdfc845cacfb756dcafaec4a40fabe464afa737eb7fa3d3bd7f99a2855f95adb7df8d1d71af7fad906f6c69156f66a141bf60bb157f4f2ecc9f49b77a8f3b4ac48f30d09bdf2d42841f2aeb416f262b2c2f253ff10f17d91c5f168a2aef0cf692cf07b472bf03b9931efac5f6bef927697ef43f925eecc343bee43c1fdee0a7000edd5b208edce8959edbd6d1bedb3a7a9ec9a0f2debc58445eb8b85b8eb4abbcaeb33aa70ea344eb8e9590e74e8c764d5e87dcbbae85cebf5e8564d6ee826725be811de13e7561d25e60a8133e5cb78ebe599a2ffe563f1bae4dff252e46b30cb
  | 4, 9 => 0xff8a1c42ff2e2751fefd7105fe955eae
  | 5, 0 => 0xd96a74a0d95ca4f0d579f020d25c9160c2843550c1ec5a30c0960060bf83ffe0bf756e20bbbe5b30b5d64d00b28b6f50b0ec2c50a84bc620a816ab10a79eba009ea3db309d4ec44097678830954ffed09181360090b8071087fe1ba086c182a085508da07fd9b1407e3f40c074ef8fb071e5398071cd6e7071859030704921b0701f4a40675585506751e0106698190064cbbe90602347805141ce604e8cbf204d007c0048c6416047b533104282b4e0425d6190403108203f9c7c70378e15f0352e980030a559202fc37c8028e299d028505c002547ea202171b6c01fca35a019ead980192965e014cda4400bd204700b7a9410089a7ec008202f0003220db
  | 5, 1 => 0x1c7f12e01c79224c1c5615321c32fe151c279dbf1c11d9db1bdf75b71ba3a0441b9e1c091b03f4441aabc6271aab4f3e1a6dda761a6ada101a224e8019c256a719572282192a99a31909b7dc18f4c8c518c5e6d6189e86a2185b8f431851eb8b182d98ae17c7bf4817388582171e9cae167c445d1658e29c1606d32615edd47615ebc8f61561d81f15499332148752ac13eada93135c07c81317abcf12bfd08712069ebd11b5432a115cfda01152d24e113c8f69110243cb10e5348b10b7dcc310538aec103596901027e17c100ecb961009f1d10ffae0460fb298720f9e042a0f72c0670f5fa36b0f02075d0ecca4fd0e9dccf70dfe4eb10df73af00dec0e87
  | 5, 2 => 0x2d2f8c8d2d2a961d2d08e9422cdd3c002cbab4452c76c8232c451d102c3cfa662c24b3ce2c21fa522c1860442bd3252d2bc2a1982bb8437d2bae672a2b610e762b414e9b2b024bff2affde272a8cf03d2a84f4f32a1a4faf2a17384729f8754d29cc8f852920944f2761e33326f0bf802689971c2605553425f841c925f6118d25c642e0254a7fd924f1ea1024cd0718249869a324543e81243a26d424363edc24357bba2415951423e7552023a12499230193e122f667972291f73622787057226bc6ba223ca0d3222ff02221fc430321fa4e8f21c961ee212eee6e2115d81720d062c52022d098200df2c71fb2668a1f717e091f3a2bac1e1bc35a1d1af0ee
  | 5, 3 => 0x3b85377a3b6798743b501d6a3b3474c13a39ae743a1b722239eb18fe39e111fd39bcf122399d4cf83902748338dd059e38c3477438be2d553853884a3845a585380352b23765e00337611de337495c78373c3604372d58d436ed5a4436be64e236be578e364f156a362a003a36125c5835ef2ca035d6d47435bcf57135b7f0eb3511a07b346451c63437bf0a33ffc99533f3d33533ef139333bec3c933a98d62338a17fa32f46ea532e53b7e32bf9a693259528432567cd832443ad331707e563169136d3146a35930e6f09130c7564730b5060a3057fdca3051c5e53020c2d0301df0e72fd5b2cb2edd907d2eb8c4382ead07c52e301d242dcdc4fe2d767cf0
  | 5, 4 => 0x4a4f68e6498674a14979c6724903a18448d8712648d3954548c60e44489371ef4879cf5f485a25814823e0a74808ba9147d50b8347673f4c4723532a471abeca468c4c07462b18d045f277524538e36b45363bae44de702144dda1ba44c6d7dc43f8857243a1803b439da7e4432f1c1742f20f2442ed153d4255c9fa424fa548423be1f141a1aa9b418b793140da29d740cdc492404f13e34026ed3c4022cc07402002493fe6f0e13fd1b89f3f503d323f38196e3f0090203e9331f33e40ad0a3e2c8b1f3e21ed923da0692d3d6b5af83d32c71a3d22d62d3d057ae53cfdec5a3ce0b6123cdb8d713cc13aae3cbb96453c8668243c2ced193c2cd4bf3b905260
  | 5, 5 => 0x55d850ba55a6ca15559eb9ff558ed1c45531ef27550b791e550872c154e8b71c54e3f20754bbb29f549fa21b53ec9f1a53e86d8a53ce1a0853b176bc53a9aef753909242537f5768533c725452f68e3f525f40c0525dc3275258557651c003ca517798d35169adfe512823d45102a75950fc308c50dca34850ac39f550a2a5d1507b3a685066db8e50433e935033187a5013d0804fddde864fa313274f54d1d84ef085884ed2350e4e97b39f4e468d4f4e3bf2ae4e137fbb4e09c5684dff2f4e4df651b94de517794dc7f2544d7699544d3c9af14d017bc94c4d09da4bf684184b902f084b557e1d4b4ae8f94b28ebe54af9e7d24aa982e74a9ad0594a824927
  | 5, 6 => 0x6254b6a7621e693961c5d486611c00556103575160f9f78960e3f78a60c04fe36065a6ea601075045ff45d8a5fd279b25f96d14b5f8a080f5f39ae1a5f37b6115f2d57b95eba2c835eb97ee65e0685f45d8fa54a5d5a2be25d4fd49b5c7541035c54ff065c11e1465be809775b91dab25b505a7e5b4586015b3a5e985b2e925b5b1f4f1f5a7a89715a5f895d5a401d905a27c46259ebf63559d840f159c32dd55999af92597ca4795942577e5934e215592e7e6158dc8aa558b194fb5898810358963b7c588ee9665889efd6585b0a4958165cae5809473d57ddebf757d58b31571dc95756efe62156d3173d56c800475619361756129afb55fb1df155e5151e
  | 5, 7 => 0x6f9869576f4e5fa26f3635af6f21e5af6f0257026efffbe86ee4763f6df28a0a6ddfb2e46db9b6516da706ac6cdf7aca6cddb6816cb8c0936be7681d6bc30acb6ba1fb296b8e32476b2e68016aec98616aeb116a6ae9df8a6ac05b876a8ff7966a89e3166a3f16346a223a726a1d3bd269fc6e9369df855869996858697e02d66926bc0c690f284668eb627d68bc86c267b3134e677b34ba66e7f06766e12bcb66dc634466bb7565661b4194661823f0660fad8d64fbf3ed64dc78a064ba7d8164b816db646cdc24642ca224640c1ba563f3f53463d706b1638efa48637516406356c0eb6349321263388f6e63265a666324708a62618b8d62616758625c7464
  | 5, 8 => 0x7b6157437b45a9727af59b097aed268d7adf20237acffbfa7a22bc2579e9e93979e388ba79e1b7a779c9aac279a1f5627995fda3790e85247909f31f78c57cbc78bd99b278b4a577789c284f789a599d7899b1957896e61d7851906d780657e477c2f06e773c184376856c2d763e65b976386050763604ce760d8fdb759fa5cd7592b66a75832568753e084574d69a92748f85847489184b74704629743865497424901a742308f373e38a4e72927404726eca38725ad39772564d10724f47847237567e72340b5472307b1a718cc5337170dd91714ae44b7143825671143d6370fbd96170a555c0708c0eb67084bd2a707637d4702f848f700b506370094cdc
  | 5, 9 => 0x888b990488861d9b88704bca885165038841083e878c05d18765b81586fe431b86955f17866c6cb2864652958629ea0a85f0dc5585a485b38591bacd8541c299852c1be8851f57bb850336a6849b423383dbde3d83c646c0831e00c4831c444782dd7e5682d67e2582cc54bc82b06ec1828c16d8826af40e8228ba858206af8381f760e6815e5a588146980081222db580f2788580ce7d9080a3a361807f8b00800c05067ff586697f84fa8a7f389c127ee034dc7e8567e07e7ce37e7e6f02bd7e46b4177dff4ae17dfc6ca87ddf5c957dd5a81c7db489c77d80ea497d7e0df37d6ac6867d2745457cf5d4747cef9b417cca458d7ca87b7d7c7c08197bbc5146
  | 5, 10 => 0x951ebad695003d0f94c7114c948eb874944711fa93f2e08d93b2bf3093a39576937b8a0a9363f9be934fc2db9337b366933040c9932e213b931b54c4930ef6dd92ba8e1392a52d85929660089225522d91218055911ec1cf90e3164990ae709190670f8890266a098fdc4c428fc33f6a8fc147438f7d9e5c8f6521348f10719b8ef1f65b8ee0b4588ed8df978eb80d0e8ea236078e23f5d38e1243f78de913d18db799d68da22de98d63e3258d4f0af98d3fd1a48d075e9e8cd688c08ca8849f8c9fd6f78bdd880f8bb8c8368b9337678b6fe8ad8b0547d88b015e2e8af6faed8aec01d88ae0068f8a8b93e58a742f6b8a722ba08a57365c89fc981f897d642b
  | 5, 11 => 0xa2969641a261339ba1ea9b0ba18a1c18a0bb2b8ea042b693a040cb89a0284e619ffaeba49f8a40a19ede456b9ecb37739ec8ad2a9ebd89309dea6fac9dca8bcb9dacc8539d99b5ed9cd48d0a9c6edbce9c69fd5c9c07051b9c009e6c9bece1b49be9c0e69bc48b5b9bbd09899bb007dc9baf2f059b7dac099ab5fc7d9ab2badb9a9f4ff69a9902a09a844fe29a75504f9a10bcba99df8a3499a16afe99209c3d98aeadb2989ec0659896e2df98589fed982d7550982a4a9e9827533d9728f1889724de3697181a059704cc7c96fcf10d969c868c9699b6bf9675b0f49655ca9d95dbbf6f95d5012b95ca9b2695c3808495a92dc1958c745a9570644a952d3946
  | 5, 12 => 0xb369ae21b258d1d9b23c4d93b19d1209b16848dbb0bb985ab0a26a14b05fd421b05df605b041a3f4b02c5e94b00ab021aff44bbaaf732627af6a74b6af24c26daefc00f4aee31104aea4a7bdae947867ae1af0cbade5a97bad8ee124ad72159bad3ea9d9ad3a27afac79341aac6279acabe7b3bbabd284f1abb666d5ab271e82aaf84a02aaf6fa51aa044bdda883d509a8773dd2a8426d52a7ad24ffa78ca4d6a747d906a6faf03fa6cfe945a6c64abaa66c5aeea640e525a63122a1a6286ecca61a3e3da58983c6a53d9ddfa520ba72a5024f21a4ff7869a4efe494a491a2a9a48ab900a42478f4a4079c29a3ac7834a3055daca2ecb51aa2a680f4a2a659af
  | 5, 13 => 0xc0af077ec0912cfcc04baf71c01a4ceebf9d9735bf6f7148bf524967bf04fb61bef4b953bea1aa03be9f6831be5b1675be3e58ebbe283e5fbe01d706bdba0b03bcb03c12bcaae0e8bcaa761bbc8e5f8dbc5d25edbc36e3d4bc22265dbbb6c917bba9383abba51603bb8454a5bb7fafeebb71514bbb6b32b7bb0eef92baf4c27fbabfdcc8babaaaf4ba997fc5ba757119ba084f3fb9f2d2fab9ee7147b9c94900b9a2bcfcb8ea4341b8bf2022b834090cb809b513b7999464b795ec34b7842473b6cde2bfb6a9817ab6706788b65d26d5b622bb0db5b77cefb5a50a52b572ebf2b4be091cb48ae924b460d684b42f26e6b42e6b60b3f563c5b3f207a3b3ac06bb
  | 5, 14 => 0xcbb7fdeccba23b23cb892e14cb870201cb73c563cb653b42cb4b0a5ecb4246fecb389e46cb03f06bcacaa97ccab95c31ca3b8f62c9fa718cc9c7d7f0c9c57729c956df56c8b05f89c8aae420c89b71d1c8983515c8678ebfc84751a0c80e4673c7ef3772c7de96dcc7cef81fc7c10915c78eb53ac7171450c6c719ddc6a157e3c6873f0bc61da991c5fa6ebec5f82997c5f6a3a8c5b68152c570dd2cc566891ec55ce5d7c520f87dc4ba537cc485206ac460822ac45ad49ac457da09c4010f8fc3eec27fc3e895f4c3c37c13c329e6c3c2fbedbac2f75a6bc2d7713ec2d53546c2864779c2603f36c22b7608c19f3f4bc12a2482c11a31ddc0fa17b6c0b6c3fc
  | 5, 15 => 0xd905d319d8f814f8d8e13282d897f5ddd86ed1f3d7bab0c4d74db80dd73b59eed711a03ad6d68dd6d6cf6c47d6be7d44d66fe387d60aaf08d5e84709d5cdf446d5a03167d5751dffd543815bd52553c3d4dc86d3d4c80f67d46bd87fd44d88a0d4217feed3fee2f6d3a292d7d39d8086d38b4fced38152b9d3679a7ed33a073ad2ca9ca0d2c67412d2bc58dad2b682e2d2a0d756d23c7a31d238f1b6d16278aad1438854d107dcced0a7e0a0d045f1f8d03ce88ecfea050ccfa66ae0cf74c61dcf54aa9ecf10ea6cce907272ce616fbccdfcafeecde2762ecdd98827cd9244cecd8c8f58cd88a9aacd0c7b10cc8989f1cc86d26ecc793b3ecbdd8ebbcbc136b2
  | 5, 16 => 0xe5596b57e539fa7ae52a68a1e514b2e9e4edcf31e48bdad6e45b3db3e42bc6fde41b839ee3c31814e3718d8ee36f9ae6e3117b9fe2f8964be27a4db3e225a5d7e1fda8ece1ec62bee122ca85e12040f6e1118d44e0f9101ce0f1118de0df4f4fe0b01ed6e0677d18e04d14e6dfd0ce4fdfccb7dcdfa51782df4cb77fdf3bc6bddef89d44de9b4d86de8a01fade6a77a8de687e52de5004cbde2a9c0eddd671caddc5140edda2b52bdd7ed334dcc7fe34dc954d16dc7ff0c0dc7afb4fdc6a49e7dc4a2f2edc39d611dc34d0e7dc10d11cdc0e378bdbe951e0dbd3f58adb3165b3dafe1708daee0c39dad04fc6dabc106bda63ca6ada3c17c2d9b4a3a8d9549982
  | 5, 17 => 0xf44dc75ff43a6fdcf41a2a4af3f26112f3d17984f3ba5609f38e74a6f3407614f307eff0f2df3bfbf25e44cff21f7449f212061cf0d76899f0d1c509f0c73099f067279af03b9931efac5f6bef4d2f27ef07d789eefa13a7eedd8618eed1a2bbee88413bee3fb750ee274cc0ee247722ed9af1a2ed895f2eecfd033eecea7311ecb87576ec942318ec868431ec0c7a40ebf399baeb937cf3eb8b85b8eb33aa70eb1d1087eb1bc0d6eade3887eab3260fea6829b3e9874269e97816c1e905ff18e8ffc14ae8fbcdc5e8a7ee71e88511b5e811e457e78f654ee75fecc3e750de76e73d1ca9e71fb6c4e6912173e66f63c5e64d3551e5b6fdfde59fb400e58a30b2
  | 5, 18 => 0xffd03c56ffc57b0effb0b1f3ff770fecff197fd8fed298c1fea2c140fe7ac495fe269d8bfdda9fc5fdbe59c2fd7ba2a3fd43c475fcea891dfcd925d0fccfa76dfcb6c6e7fc695265fc3e4617fc20ab30fbcdfebffba6d400fb692727fb5f94eefb3870d8fb2b56e0fb1f6988faec4a40fad1e44bf9ee0f85f9ec89f0f9c18f30f9bc0527f9a13dd0f94dcb2ff8ee3904f879528df814ffc7f73290f2f6f8d7d2f6b398dbf6446139f61c9884f5ed95cef5e6ba43f54e553af51e6ae0f513498df4f2ecc9f4f21036f4c62580f45331e5
  | 6, 0 => 0x185356b017f34db117e3fd05173885821693fda01669ac2f165dc8d215cbdd67152717b91515854514eb474614449b8d1420492f1412aa48137fbfd1135531d41353e2231348474d1317abcf12a9369e12a7e6ed126a5e9e1152d24e1113688011043cd810b7dcc30f9e0a6e0edd048d0e97a5cf0e85569e0dd95b680d4324140d1656c90c94abec0c2843550c1800ed0ba7a9b50b499cec0afbc0fd0a9da1b60a84bc6208aef09c089f9e65083c44ed07e3f40c07313d9906c7ecd40684c35b05dc2ae205513a2505141ce6050af94b0461d06c0407216603f66ffe039cf73303816e600378e15f027a3250025c75dd023c720601c83dd901a8c8340091f930
  | 6, 1 => 0x2f701a1e2edd907d2edb1f0d2eaa79aa2ea47f152df5a7a22dd8e1fb2ca042f82bb451602bb1fc2b2b8f36942b696bc22b0507712adf0f922a1a4faf29f8754d29a3417e297dcaef292ad3aa28d9005628d6e77928494659281bcb332815cdfe27be46ed27af31392780d5a8275c626d2751a12527033603262ee7572606eaac254a7fd92507c8ba24cfea8c247aff2023e7552023ca6c2e2332fa1722f54d3e22f13c3a22c496ef22ab8f9f223ca0d3222ff022222630d2217a359c21482b3e207a5f1b200578a41fa125de1eacecf11e84fde91cda7b511c8b53321c7e364d1c524b971bdf57fc1bdd15cb1b3122851a41da4419ea6ae619ab9a60185deb20
  | 6, 2 => 0x4b2d4aab4a4f68e64a1e1d4849f7eccc49c8c6e549970344492bd66448bb148047ba099d479a18d946c651be45a68962450370f143a1803b439dffed432fc65642f93a3f41fa008841f7002241ae74924162baeb414e7cb940c16e3240b6bfb5402aacb43fde119d3fb9bec03ed4ea293e21ed923da0692d3d79fa883cdb8d713be9f93c3b7700a53ae82dda39bcf1223992c4cf390599b838f8e90738e923b238def86038c8b57b384402d537b4078e378e10e33787065836fee67936366ff9358a74c3358361023521f061346451c633bec3c933b4696733aaebb5338466103360d83d32b4dd07329ae8d732225efb320d90c3317663c53161125630e125ff
  | 6, 3 => 0x66dc63446696ee91661f580565d88a7565ccd31c65cb9fee65ae13a464fbf3ed64c82833646cdc246447bc5764128e3663b8fad163115d8c629d057261c5d486614917346129730a611861cb604a53675fd1cb975eed43f55ec85c165eb97ee65e4a8af45d1622cb5b7ff9475a7161905a6a79205a5f895d5a4bc07b59ebf63559e5789659e2a2ea59d060e5597ca47958fca46858d2c96b57e423dc57ddebf75761d8dd5669b68f55155d48550872c154f9d96b54eae67754b6bc2f546962125402ee3553d1432253ce1a0853c9207853ae206453a48656533a8d3c52f68e3f528e721152111b0551849b5f5158b5975085ea074dff2f4e4d917b464bc1a1cc
  | 6, 4 => 0x7b0b7d7a7acffbfa7a82b45179eb66d279e388ba79c9aac279afba1b7914c4907903bee5782ecbe3779ff692776a0498772f3939765e5b2075c818c0758b556074e7783e74c8c10374852b2273df1bb073d92fec731c551a72b511f772860de47226f66b71db8ef8712882427105ec8470b4ef1a70848cc6705fbb577052345670459d5e7040dbd96fe64b936fb006b96f94e0a36f6131956f4e5fa26efffbe86ee857a56eaf793c6e1872196db73ee26d7104b36cc5097d6c31bef96bd5c92c6bd16ba66b2da64d6b29cdf66a9712ed6a8c6f4c6a27884769dbcb5a69c8080369bf87246979691c69179f436859eaa467d5d6a067ac285b675ddeb166e12bcb
  | 6, 5 => 0x90ac819f909b4e589092a3a79077888f8f075acc8e7416798e6d51dd8da44a028d9bd39f8c8819ff8c46a3938c443ced8bb8c8368b9337678b632cc38b013c528ab0969c8a9988a08a8cd7ef89edb19f89aa8f4b88861d9b8780839c875e9fc48722f75d87162e2186b97dcb864652958617588785c8f4cd8592ac068591bacd8541c29983e1251883c9fbfa831e00c482bab86d82b06ec182ab75318206af8381ebaf6f81781c47814f53e78125d5a48108ca8b80ce7d90801b0f787ea9ef697e7ce37e7e5426597de652827daa24b07d9ec10d7d6476cc7d2ae0117cbe15397c979f307c9498d37c74dd2e7c2bc82d7bc4ecd27b78c52c7b5a401a7b3d9cce
  | 6, 6 => 0xa6286ecca6118df2a5fb28cfa5f06673a5d2da29a58b70f3a56b82a7a561ce2ea540afd9a4b36b57a4566b9fa3487758a2ed7d55a2ecb51aa2be784aa25c304ca25c220ca219d8efa16faecca155d0d4a12e1b74a09aab36a042b693a0284e61a0267faf9ec83e559dca8bcb9cca2e579c5ab3b29c1bab969c0abb7e9c04e89a9bfc6c3b9bc48b5b9baf2f0599e2732299df8a34997967a699245e1f98317bd2973a784a9728f18896da85b496ae0bc1968e7d14968c21fa96709c5195c38084957eb01c9545dc63951ebad6944711fa9444e6a5934f30dd932e213b92ba8e139278be7392555d1a924c819991a961e49198f4df91258e6a911ec1cf90e31649
  | 6, 7 => 0xb70baf78b69c97adb66cda6ab66505a9b65c171bb6443320b62e5c19b57539e3b543bfe8b52e53fbb4db310bb4cbf7b6b4621913b4466904b42e6b60b3f563c5b369ae21b31f5d79b2fc0ebfb2ee9c4ab2ac50b3b2916deab28320ffb200557db1fe51b2b188be31b0a88319afcd2e50ae8a692dae218529ae0cc45dadf892c4adf1ea6dad7d0267ad30abc5ad1de0dfaccde8abacb841faacab7dcdac8c7969ac276845abfe6808abe7b3bbab68044fab100adfaaf84a02aaf6fa51aaa86a59aa69a468aa62a437aa4c4eccaa3c94d3a8d2be12a8ae53c7a811805aa80bb112a7e7bab4a7ac0f2ea7982b18a773f6b3a711209ca6c4c224a67ed55fa66c5aee
  | 6, 8 => 0xccace084cb389e46cb03f06bcaf76445ca9183beca78db2cc9ed59adc9c57729c916422ac84751a0c7cedca5c6575d85c538ee65c460b31cc3fb01e0c3f6236ec375e6f8c2bc712ac2b0aca0c2603f36c248de02c23ee0edc22b7608c22528b2c21075f4c2017661c1d98c46c1c142e7c1bff336c19ce2ccc16bb046c12d9110c1212332c0d3056fc07c1884bf524967bef4b953beb5179abea44017be90f28ebe01d706bde1f0afbd655a8ebd56c138bd4fa696bcfc8a5cbcf167b1bcb95f58bcaae0e8bc2b01d5bc1ade86bbd3380cbb7f069fbb53760cbb3ee542ba9b1cefba315397b9c94900b9b5adffb8ada667b8aae7e1b86f3c5bb7b2901bb7687254
  | 6, 9 => 0xea126d8be8fbcdc5e8a657efe8863dc8e6de6f79e6912173e5ca7efde5b46471e4a2810ce3ae4c6fe32ce3c7e3107ab7e2fd775de29b15a4e280e891e24c02dae2407087e226928fe1cce950e1947551e17ef90ce1556f12e08e700ee04b4634dfc02f1edc4a2f2edc0e378bdbbb4cf8dbba9172db7e2db5da1cea52d96ecdbcd929381bd905d319d82e9026d7ebfa33d7ea1c17d7cdca06d7b884a6d7ab476fd78129cbd75ce3b5d6ff4c39d6b0e87fd66f3716d61b424cd5c101f9d5a716ddd543815bd524cca8d373d9cdd2847014d2832063d09241e5cf3e1398ced3ff18ce7937dcce5c0f57cdd98827cdbd48b3cdb494decda6644fcd58dbbacd15a9d8
  | 6, 10 => 0xfe9dc64cfe62b3e8fe5b9259fe206851fdc8962dfd7ba2a3fd746d1bfd5b8c95fccfa76dfcb6c6e7fcb179d5fca3f9c7fc543579fbf7fe91fb2eb8e9fa487eecfa42a8f4f97ba99cf93ffe16f8cfae66f89402e0f83406b2f7c90ea0f73290f2f61c9884f5ed95cef565ae39f412f880f3f01f34f34d5cc4f3155426f2d73070f290167df1519d3bf075e199f02797e3eff3b4d1efcecbfeef6abceeef5b1e31ef4d2f27ef1adb4cee88413bee13651dedeea29aed9eaa66ed8694d0ed844fa9ed42a764ecfd033eecf2af30ecb87576ecad1e8fec19f940ec11467cec0c7a40ebeca83cebe6faaceb937cf3eb8d35a1eb4fa225eb0d568eea8813ccea615b58
  | 6, 11 => 0xff85d955fed9de1ffec78000
  | 7, 0 => 0xfd7ba2a3fccfa76df565ae39f290167df1519d3be6de6f79e1556f12dbba9172d2847014d2832063cdb494deca78db2cc16bb046beb5179abd4fa696bcaae0e8bbd3380cb8aae7e1b86f3c5bad1de0dfaccde8ababe7b3bbaa3c94d3a25c220ca16faecc96da85b4968c21fa951ebad68e6d51dd8c8819ff81ebaf6f81781c478108ca8b7c9498d37b5a401a71db8ef86a27884765cb9fee65ae13a45669b68f51849b5f42f93a3f38def86033b469672f701a1e2ca042f82b05077114449b8d0091f930
  | 8, 0 => 0xbcaae0e8
  | _, _ => 0

private def packedBlocks : Nat → Nat → Nat
  | 2, 0 => 0x9e2630f4e6a914a8398e452d0e63914a139d6670f4e456c16e39b23b284e457315339b2452d0e67914a139b245284e6c914b239d5b04f0e6b914b5399e4529ce6c914a739e19854ce6c914a639b245290e6c914b339b21241ce729b03d3
  | 3, 0 => 0x915a554cb44915b054ca74915cf5403d494db05a4c149b1eb41cb349158f54ca14915be5c4c149aa455d0c14915b054ca6498e4575cc14915b054ca44915b04f0854915cd54cc14915b04cca149b245284824915b05c03d49b2452c0a149b24541ca149159154cb548cd5327c62498e452303d4915b054055499e452a06249b24575cc149b1dd41ca149b2456c0a149b1eb4883d4915c25c4c14915ad54c3d49ca6c304624915ad54c464915b04d4a84
  | 3, 1 => 0x9b2455d0b549b24537cc149159854c8c499e452143d4915b054cb4498e45304b049b1eb41ca64915b054ca14915ad54c5649b1eb41ca44915a154c3d4915b05403d4915a854c3d49b2452043d49b23b304b04915b05c4a149b2452846249b20841c3d4915cf590c14915c254ca84915b05bcc14915ce54c624915cf5c48c499e455c8c149b2455c8c1499e45304b049b245304b04915cf584c14915b054cb249d5b04cc3d49e18f54c3d4915cf54ca14
  | 3, 2 => 0x9e263304624925b05c4c14915b051c3d49b1eb41ca1498e452d46249ce333046249d6673046249b2457aca149b2453b0c149b21341ca149b245760a84935cf54cc149b24567cc148cd23304624915a654c3d40026c914a1398e45240624915ce54c3d49b1eb41cb24915ad5c4624915b05c4b549b245478c149b24554ca149b245304a34915ad54c454915b0590b54915b0520a74915b052c3d498e4527c624915a454c3d4915a254c3d49b245304ae4
  | 3, 3 => 0x9ae45760c14915b05143d4915b054cb34915b05283d4915ad5c43d4915b05c06249c9b054c3d4915cf54ca84915ad5403d49b245304a1494dc754cc1497a45304624
  | 4, 0 => 0x99e45520c118966391618304625915d46c1531156456c153304705915b0681530f56456c15339cc159b2453048b1896456c1534803d5915b054ca120964573d53304235915b054cc11995a54cd073046259b245520c11896456c1532243d5915b054cc1181400915ad54c3d4915b054d16305685915b05c43d5915b454cc1189663914c1230625915b054cc4189645741b054c625915b05f0c11fd6456c19654cc15915b062953305685915b05403d5915b05c52e18964563d5327c6259b2453a4c11896456c1532a46259fe456c1531896456b57a54c625
  | 4, 1 => 0x916156c1711895eb6c14a41c3d5915b054cc11ad6456f9533046259d2456c1530f5685915b054c465915b05c4c107d64573d53460c15915d654cc115966c915d85d0c15915b054d240f56446c1533046257adcf54d072a164563d53240625915b054d440f56456c1332143d5915b05d5531896456c153354625915b05c4a80f56457f5b05c4c159fa456c1531896456dd5330462594e456c1713056456c159304625915b054d250f566c915233046259d6456c1530f56456c154304625915b05a4c11896456c1533045d59b1eb41cc12856456c153304695
  | 4, 2 => 0x98e45894c11896456c1534a4625915b0524c11896456c15325c625915d46c1531896456c1532fc625915b054ca80f56456c1483043d5915b054cc1125645801b054ca85915b0544c11896456c1534843d5915b054d153056456c153480f65915b05dd5318966c914c12c0625915b054ca80816456c1533044b5915d86c1643056456c1532e0625915b054cb91896456c157304625915b054d2a1896456c1795d0625916146c1531895eb6c15341cb35915c254cc10f56457adad54c3d5a16456c1530f56456c153304435915b054d3b30564573d534b83d5
  | 4, 3 => 0x99e45304821896456c1533786258ee146c153189645855cf54c3d5915ad54cc10f566c914c1208625915b0538c11895f373d5341cc15915b054d1a2a164585d533b4625915b954cc11896456c1533b46259b1eb6c1072856456c173304625915b054cd21895eb7097141cc157adad54d070f564573d53304245915b0675530f55fd6c15341cb55915b054cca1896456c1532f4625915b0560c118964585d533a0c15915a354cc10f564582db054c3d5915d86c17130565c915cf54c3d5915cf54c850f56456c1533a0c15915b054cc11296739b245304625
  | 4, 4 => 0x915d8751531896456c14d304625915b054cad189660915b0304625915cf54c8c1896456c1501883d597e456c1530f56457e9b054cc15915b054cc116d677915b054c3d5915b054c8c1596456c15332c625915b054c95189654915cf54cc15915b05f0de189655915b06786257f1b054d0730567863d53304625915b05e5531556456c17254cc15915b05c52e0f56456c15335c3d5915b05c4c115964573d7454cc159fe456c1530f564563d532d4625915b0558c1189663915b0304625915b054cc12c16456c171460c158f1b054cc10f56458ccc1208625
  | 4, 5 => 0x915cf54cc11896456c179540625915b054c810f56456c153304565915b054c9a0f5645711533046259aa4554cc11896456c1744d4c15915b054d2e11964575953304625915b054c9918966795a45304625915b054ccd18965c915b05c43d57adb05c5113056456c1712143d59d5b04ccc11896456c1533045359b23b304821896456c153284625915a554cc11896456c1693043d5821b054d070f56456ad53304625915cf54cb51896456c153304645915b0598c118963341cc1208625915b054c9f1896456c15e304625915b054cc818966c7ad072c0a15
  | 4, 6 => 0x915b054caa18965c915b054c3d5915b054c800f55eb6c15341ca65915b054c850f5667915743046259b20841cc118966c915b02a06250026c914c12c1263914c12086257adb054d072916456c146304625915b154cc11896456c1532d42459b24546cc11896456c153304555915b0679531896456c153304615915b054cc115d66c91553304b05915b0584c11896456c153240625915b06b5530f5645855b05c43d59b1eb41ca12096456c15330459598e45760c11896456f9533043d5915b054d2e0f566c9159b304625915ad54cc11796456c1533043f5
  | 4, 7 => 0x915b054c98189645855b054c3d5915b05e5531896147f9b054d075915ad54d070f56456c1533603d5915b054cc12b964589153304625915b05d1532d56456c164304625915b054cc11616456a153304625915b054c941896456c15337cc15915b054cba18966c914c1204625915d36c1530f566c9155327c625916156c153119645845b054c625915b054ca21896456c173304465915b05c48c1896456c19e54c405915b054cc11b15eb6f97141cc15915d46c1530f56456c153304475952456c1713056456c153304545915b05f4c118963e6c153304625
  | 4, 8 => 0x915a754cc1189657915b030462599e45304851896456b553188325915b054cbe1896456c1535403d59b24554c901896456c153330625915c354cc11896456fd5330462598e456c0c10f56456c1532786259b2457acc12c15eb73d5341ca15915b05c4c11896406c1533046259da67914c118964573d7154cc15915b654cc11896456c1533783d59b245824c1189645685533046259158f54c8c0f56768cdb0304625915b054d3a30566c914c12083d5952456c1532d567998e45304625915b0540c1189655915b0304625915b054cc11156456c1533b43d5
  | 4, 9 => 0x915a554cc10f5400915b054ca14915cf54cb50f56558edb0304625915b054cc116966c7ad07304b05a0a456c1531896456c17854c3d59c6456c1530f56456c153304515915b0598c10f56456c15327c3d5915b0578c10f56456c15c3046257adcf58507305645691533046257adb054d072c96456c1532703d5915a254cc11896456c153478c15915af54cc11896456c1532d4625955b04fcc118964573d532303d5915b054cc128d400915b05403d4915b054cd10f56456c1533047e5915b054cc117d645751b0669535a16456b5530f56416c153304625
  | 4, 10 => 0x915d86c1532a16456c1532b0625915b054cc11956456c15d30462599e455e5531896456c172520c157adcf5c5072316456c15331862598e456c19a30564573d533043d5915d8645533056456c1533784259160073d5330566591553304625915c454cc10f56456c153340625971fd73d5341d6456c19f54cc15915b06798b54d64585d53304625915b04cca81896456c153304625915b054cdc0f564573d53304465915b052cc11896456c14f304625915bb54cc11896456c1532803d5915b054cc1121645751ad54c6257f5b054d072a163d6c153304625
  | 4, 11 => 0x94db054cc10bd6426c153304625915b0518c10f5685915b054c565915ad54c620696456c1533787f5915b0679530f56456c1532f0625915b054d1d0f5645745b054c625915b054cdd18964588d533046257adb05c5072856456c1532746259b1eb41ca11896456c153464c15915b054cec3056456c1534f0c159158f520c11896136c15341ca15915b0584c10f56456c1532403d5915b054ced13d6457adb05403d5915b05f0c11895eb73d6441cc157adc254d072a16456c17654c6259ae456c0c11896456c153304405915b054cc11cd6456c15b304625
  | 4, 12 => 0x915b05e5530f56456c1533046f57ada154d070f56456c153304745915b054cc11416456c1643043d5915b054c940f56456a953304625915b065d533056456c1532ac6257adb0541070f56456c15330c625915b054cc119d6456c1712303d58ee1754cc11896456c153304525915b05e5534f966c915532d46258edb054cc11895eb6a15341c3d58fdb054cc118964569953304625915c754cc118964581db054c3d5915b054c930f5655915b062cc159b1eb41c810f564575da554cc15915eb6c15328564573d53468c158ce2554cc1189685915cf54c625
  | 4, 13 => 0x915b0554c118966c7ad07304ae59b1eb5d1072d566c7ad0737cc15915b054d2b1896456c953304625915ba54cc11896456c1532d8625915b054cc12856456c153230465935b054cc11896456c1713043d59b1dd41cc12c16456c162304625915b054cc0189645801b05c4c15915b054cc11a16496c1533046259b2456c0c12c165c7f5b05c5075915b054cc11356456c15345cc1599e4554cc11896456c171304205915b054cc21895eb6c15341ca15915b0540c10f5655915b03043d5915b054cf530564583db054c625915fb6c15330566c914c121c625
  | 4, 14 => 0x915bb54cc10f56456c147304625915b054ced3a15eb6c16441cb55915ae54cc118966c91507304b0594a456c1533055f16c17141cc159b245694c11896456c153304465915b054d1f189650915b054cc15915b054d201895eb6c166460c157adb052d070f56456c1534f8c15915b054cc11056456b5531883d5915b054cc118d645749b054c625915b05c51a3056456c1532d43d5a16456c1711896457097454cc15916006c1532d56436c153304625915b054cbb1896536c153304315915b062d533056456c1533044e5915b054cc11116456c1532303d5
  | 4, 15 => 0x7adcf54d1330564588d533043d5915c254cc11896456cd533046250026c7ad072852456c15320c3d59c2456c1530f56456c17c3043d59c9b054cc118964573d534b8625915b054d2e1596456b550304625915b054cc11716456c153258625915d56b55318964588d534806257adb05c5072d566c7ad1e41cc159b1eb54d0728566c7ad07304a35952456c1532a16456c153468b55915b0540c1179663915d46c0625915cf6c1713055eb71153460c159161754cc10f56457f9b054cc15915b05c4a81896456c1533043d5915b054d2d1896456c153294625
  | 4, 16 => 0x9e63354cc11896456c19a54cc15915b054cf63056456c1533ac3d594e4573d533056456c1533043e59b1eb761072a16456c15326c3d5915b054cd418963b7f9b054cc15915b054cd30f563b6c1533043d5915c754cc10f564575db054cc15915b054ca81896456c145304625915b0520c11896456c133304b05915b054cb71896456c15331c6259b2456c0850f56456a5533046259b1eb67d073056456c1534805259b24554c8c0f5685915cf54c3d59160a6c1530f56456c14a304625915b054c8f1895eb6995341c3d57adb054d220f566c914c12c0825
  | 4, 17 => 0x9162354cf63056456c1533047f58f1b054cc1189663915a5304625925b054cc10f564569533304625915b054cb028566c914da3046259b1eb488c1189645855cf54c625915ad54cc1189667915533043d5915b054d07285645855b054c56599e455f8c11896456c14c3046259e2456c1530f564f915b054cc158cdb05f8c11896456b1533046259158f54cc12c16456c1533045e59161954cc11896456d55330462599e4554d3e3056456c1523046259b1eb41cec3056456c1532443d5915b0541070f564568d53304625915b054cc11096457f5cf54cc15
  | 4, 18 => 0x915b06615330564d6c1533043d5915b054cc113d6456c1533044c5
  | 5, 0 => 0x9ce456c153304626915eb6c1533d8c1679db054d07304626915b054d44304626915b054cc11882d67adb054d073045c60024554d393046257adb054d07258626915b04ccc1214626915b05ad5330462688deb54d2041c626915b054cf9304626915b054cc13043d6915b054cc11d46269a2456c153304626915b054cee304626915b054cc1188216779b054d07304626915cf54d073043d60027f915b054c625809b054d073043d6915eb6c1532a0626915b054cc1188186915eb6c148304626916396c153304626001fd73d5341cc15915b054d25304626915b054cc11881467adb054d1a41cb56915b0605533046269d6456c153304626915c16c153304626
  | 5, 1 => 0x829eb6c15341c3d6915b054cc12c46267adb0529073046267adb054d0723c6269b2456c153304626a06456c1533046269162354d073046269d2456c1533046269b1eb41cc12c0826915eb6c1533045e688deb54d073043d6915b054cc10f42a6966456c1533046267adc254d07304626915b054ce8380c167adb354d07304626915b05e9533043d60025c915534e4c157adb054d0720c3d6915b054cc1188236915b05f1073046269c1eb6c15341c3d67bdb054d073046267adb05f1073043d67adcf54d2e41c6267adb054d0c304626915d86c1533046260027f972456c153500245655393046257adb054d2e41c566915b054d24304626915eb6c19a54cc16
  | 5, 2 => 0x8edb054d073046267adb054d073506267adb054d0734c3d6915eb6c1533047f6915b054d2e304596915b0639533046267adb054d072a06267adb0521073046269162354cee304626915eb6b553304626915b054ced380626915b054cc1208626916356c1533046268adb054d073046267adb054d072dc626a16456c1533046267adb054d0731c6269da4569553304626002456c1533048357d5b054d073043d69b1eb6c1072143d6916156c1531881a67adb054d2041c5269b1eb54d072303d6915b054d31304626916336c15330462699e456c153304626791b054d073046269d9b04cd07304626915b05f9533043d6915b0590c11882467b9b054d07304626
  | 5, 3 => 0x7adb054d073045e6915b054cc11880767f5b054d073045067e1b054d073043d6865eb54d07304626915b054d2e1883d67adb054d063046269ea456c153304626879eb6c18b54cc16915b054cc1188106915b05e5534cc6267adb054d05304626915b054cc12a0626915b054d43304626915b054cce304626915b054cc11885669fe457adb054c626916256c1533043d67ada354d073046267adb054d073044267b1b054d07304626915b054cc12346267f5eb73d5341cc16915b054d1a3042a6915b054d213046267adb06695341cc167adb054d073d8c167adb054d073ac3d6a16456c17a54c6267b5b054d07304626915b054cc1188336915b054d18304626
  | 5, 4 => 0x88deb54d073d8c167adb054d073047f67a9b054d07304626811b054d073046269b23b6c1533046267adb054d072c0a16001b0654c12486258d9b054d07304626915b054d343046269b1eb41cda3046267adb054d0f3046269162a6c153304626855eb73d5341c62699e4554d07304626915b054cde1dc6267adad54d07304626915b0675533046269e6456c153304626001b054cc1248625002546c15330431500285915b054c3d5855eb6c15341c566915b054cc11883667adb054d0d3043d6915c96c1533046268cdb054d073046269160b6c1533046267f5b05c55341cc167adb054d133043d6915b054cc1188596a02456c153304626915b054d07304506
  | 5, 5 => 0x245751b054c625915b05fd533046267f5b054d072303d6916456c1533043d67adb05c52e41c626915d56c1534b8626915b054cc11880e60024573d531883d5952456c17454cc16972456c1531883d6915fd6c1533043d67f9dd6c15341cc167adb054d11304626775b054d073043d6915b054c851883d69b1eb41ce9304626915b054cc1210626915b054cc1188286809b054d073047f694e456c1533043d69b245761533046269fdeb6c15341c6267adb054d1030462695a456c1533046269161e6c153304626879eb6c1533043d6915b05c5073043d60025c6c1533049257adb054d073044f6915b054cc11880d6001fd6c17141cc157a1b054d07304626
  | 5, 6 => 0x2456c1531b86258a9b054d073046267adb054d072243d67cdb054d073046269b24554cc12086267adb054cff3046267adb054d0e3046267adb054d1641cc16915b0649533046267adb454d07304626915b054cc11881b6915b054cd7304626915b066d53304626915b061953304626915b054cc10f41f69fe456c1533046267add06c15341c6269160c6c1534b86267adb05f1073047f6915b054d38304626915b06515330462698a456c153304626002456c1533a0c157adb054d18304296915b062d5341cc169be456c153304626915b054cc1188246915b054cc1188016781b054d073043d67adb06595341cc16915b054d072303d67adb06295341cc16
  | 5, 7 => 0x915b0635533046267adb054d0030462694db054d073043d67adb0565073046260026c914c12086257adb054d2541c3d69b1eb48d0730462698e456c153304626915b054d33304626915b054cf73046267adb054d073045d67adb054d07304696a16457adb054c3d697e456c153304626915d46c18f54c6269de456c153304626915b054d073044667adb054d07304706915c26c1533046267adb06815341c3d6915b054cc1188356002456c1533b4625942456c15341cc16916156c1531883d6915b054d2041c6267adb054d0739cc169b1eb41cc122c6267adb054d2041c3d6915b054d3e41cc167adb054d072848267adcf54d073042367adb054d07304666
  | 5, 8 => 0x915b054cc10f41867add654d07304566992456c1533046269b1eb7617441cc16915b063153304626821b054d0730462600263915b0304625785b054d07304626002456c1530f42457adb054d2441c3d6962456c153304626002456c153304b057adb054d4441c3d6915b054cc1188166915b054cc11880a6915b058153304626915b054c8c188326915b05d153304626915b054d073043d6815b054d07304626932456c1533046267adb05d55341c626959b054d3f3046267adb05c5072a03d6002456c1533786257f5b054d073043d67f5eb6c17141cc16915b054d203b8626915b054cc11f0626915b064553304626915b054d1b3046267adb754d07304626
  | 5, 9 => 0x915b054d2e304626a15eb6c15341c3d6915b054cc10f42367adb054d1a3047c67adb054d07304436915f26c153304626915b054cc11882567adb054d3b41cc167adcf54d2e41c3d6915b054d2f304626915b054cc1204626915d86c1533043d6915b054cc1268626855eb6c17141c62691615755b054c626915eb6c1533a0c1691600761b054cc16915da6c1533046267adb054d073046b60024554d393043d5915cb6c1533046267adbe54d073046269e66c915533046269d1eb6c15341c3d6915eb751b054c626952456c153304626915b054cee3043d6779b054d073043d68aa2354d073046267adb05c5073041f67adcf54d1841cc169161a6c153304626
  | 5, 10 => 0x7adb054d2041cf667adb05dd5341c6269b1eb41cc12c0626789b054d07304626915b05e9534b8626915b054cc11f4626002456c1531a8625915b06b553304626895eb63d53304626002456c1531b46257adb054d072a02067adb054d073044b6915b054cef304626002456c15327c6257add86c16441cc16915b054cc1188326915eb6c1533b46267adb054d072e06267adb054d072e46267adb055d07304626915b0569533046267adb054d2a41c6269b2456c1533043d6851eb6c15341c626915b054ce5304626915c254d0730462698e456c18f3046269b2456c17e304626915b054cc11883467adc254d073043d6915b054cc11882c67adb054d183042a6
  | 5, 11 => 0x2458c5b06546257adb054d0725c626915b054cc1188626915b054cc11d8626915d86c153468c16915b054cc11883c6915b054d26304626915b05a15330462600254915b054c3d57add46c15341c626915b06798354c626915b054cc1238626915b054d072a0626002458c5b054c625916096c153304626915eb6c153378626915b0521073046269ba456c1533046267adb054d072a03d69da456c153304626915b06015330462600245695533046257adb054d07304496801eb6c15341ca86915b054cc12083d6881eb6c153304626915b054cc11880469b2457acc12086267adb054d2141c3d6a16456c1533043d67adb054d1541cc16002456c1711883d5
  | 5, 12 => 0x915cf54cc11883d60024573d53304625972456c153304626915b054cc12006267adb054d3f3a0c16915b054cc12146267adb054d0732862692e456c153304626915b054cd6304626915b054d39304626002456c15330456585deb54d073a0c167ada354d073043d682deb6c15341c3d67add86c17141cc16915b06695341cc16922456c1533046260025c916316c1535971eb73d5341c3d67adb054d0b3046267adcf54d072143d6915b054d073d8c167adb054d073a0c167adb054d073044a6915b054cc118813698e457adb03046267adb054d2941c626915b054cc1188086915eb6c153304b06915b054d183043d67f5cf6c15341cc167adb052507304626
  | 5, 13 => 0x1b054cc12483d5a0e456c1533046269b1eb41cc120862678db054d073046267adb054d3f3b4626002456c1532406257adb0539073046267fdb054d073045967adb054d1a41ca8685deb54d073b4626915c86c1533046269b6456c153304626915b054cf8304626915d36c1533046267adb954d0730462699e4554d33304626915b054c8c1881a6002456c1533045957adb054d073b4626915b054cf63b8c16915b054cc11883a67adb054d01304626915b054d073045e67adb05cd07304626915b061553304626915d46c1533046267adb054d07348626002456c1534b83d5915b054cc11882667adcf54d073042467adb06755341c3d6002456c168304625
  | 5, 14 => 0x915eb69553304626956456c183304626002456c1951883d5915b054d3530462698deb6c107304626915b054cc11881d6915b054cc1188036002456c1531883d57adb054d07304b067adb05c51841cc16915b054d073047f6915b059d53304626915b054ced304626916156c153304626915eb6c15327c626915b066553304626915b054d0f3046267adb054d07378626002456c19e54c6257adb054d0f3043d6915b054cc11b8626915b054cc11e8626955b041ce0304626915b054cc11881267adb054d03304626915ad54d07304626915b054cd8304626855eb73d5341c3d69162f6c153304626915bc6c1533046269e6456c1533043d60022c6c153304625
  | 5, 15 => 0x80db054d07304626915b054ce0304626955eb6c19e41c626915b054d32304626915b054cc10f4246915b054cc11881a69ee456c153304626915b0591533046267c1b054d07304626915f76c1533046268a9b054d2041c6267adb05c52e41c3d693a456c153304626915b0625533046267adb054d113043d6915b054cde3046260025c915b054c3d57adb054d0735c3d6002456c1532143d5915b054cc11880569fe456c15341c6269158f54cc1230626916156c17a54c6267adb05c5073045667adcf5d15341cc169fdeb6c15341c3d6809b054d0737862695a456c1533043d6915b058d53304626915b054cc11882f6915b054ce23046267adb055907304626
  | 5, 16 => 0x7adb057907304626915eb6c153304596915b054cc1188506781b054d2e41c626915b054d0e3046268a9b054d073043d69161d6c153304626002456c1643046257cdb054d073043d6002456c1532506257adb054d0e3043d67adb053507304626915b054d50304626915eb6c1534b83d6956456c1533046267adb054d072b4626981eb6c1073046267adcf54d07230626915b054d3e4ccc1697deb6c15341c3d67e9eb6c15341cc167adb054d073045b6915eb73d533046269ddeb6c15341c3d67adb054d072305669161754ce0304626a16456c1533045e69161863d533046267adb054d0732c6267adb054d07254626915eb6c1533045667adb05f107378626
  | 5, 17 => 0x915b054cc118809692a456c153304626915eb6c19e54c6267adb054d07304536851dd6c15341c626915b054cc11dc6267adb054d072846267ada554d07304626915b054cc11882b6915b054d333043d6915b054cc1248626915b05d153304206952456c153304316915b05e9743046267adab54d073046267adcf54d072d4626915b05f933304626002456c15030462500255915b0304625915b05c55330462677db054d07304626915ca6c1533046269e6456c1483046267adb054d07304646915eb6c153240626915b054cd1304626a16456b55330462600245855b054c3d57adb059907304626805b054d07304626002456c17954c6257adb054d0727c626
  | 5, 18 => 0x915eb6c1532143d60027963d53304625915b054cdb3046269f6456c1533046267adb054d072043d67adb054d073045667adb054d072683d6915b054cc11c4626915b054d123046267adc454d07304626915b05c4c11883d60025d915b054c625002456c171304625915b054cc11a86267ddb054d07304626916226c153304626915b05d1533043d6915b05e1533046269c6456c153304626915b054cc1188276915b054cc11e4626915b054cc11b46267adb054d2e41c4667add654d073046267adb054d07264626915b05a953304626915b054cc127c626971eb6c17141c3d6916006c17454cc16915b054d363046267adb05c5072143d6915b054cc1270626
  | 5, 19 => 0x7adb0585073046267adb054d0724062691a456c153304626915b05b153304626915b062d53304626855eb6c17141c3d69a6456c153304626915b054d30304626a2a456c153304626915b05f0c11dc6267adb054d07304596856006c15341c3d6915b054c8c1883d6916186c153240626915b060d53304626915b054cd9304626915b054cc11880c6915b054cc11883067adbe54d073043d6916156c153304506915b054cdc304626952456c1533043d67adb054d2e41c3d6915b054cc1188386915b054cea304626915b054cc12806269b1eb66d07304626916316c1533046267adb054d0a304626972457adb054c3d67adb054d073043f67adcf54d07304626
  | 5, 20 => 0x8a9b054d073d8c16915b054cc9304626915b054d53304626915b054cc12186269b2456c0c1208626915b054cc10f4326915b054d3e304626915b05e953304566915b054cc121c626915b054d1c3046267adb051907304626915b054ce630462600250916316c1535916157adb054c3d6915eb6c17954c6267adb054d072d42469b1eb46d07304626002456c1532d46257adb06795341c626915b054cc1188316915b05d153468c16946456c153304626915eb6c164304626915b061153304626915eb6c153250626915b064d533046267adb054d07304576915b054d2e3043d6915b064153304626a16456c15341c3d69160c6c1532506269b1eb54d07304b06
  | 5, 21 => 0x2456c153304625a1e456c1533046267adb054d07304476915b05d1532a0626916006c153304626002458c5b054c3d5915dc6c1533046267adb05f507304626795b054d07304626915b054cc12286267adb054d072a8626915c06c153304626001fd73d5341c625971eb6c15341c3d69da456c1533043d6915b0679533046267adb054d072143d6915b054d1d304626799b054d07304626001534e4c1248625915b054cc11881c6915b054cc1188206915b0655533046269b1dd41cc12086269b1eb6c1072a0626915b054cc1188466915b054cc12406260026c7ad07304b059162563d53304626915eb6c150304626956457adb0304626942456c153304626
  | 5, 22 => 0x24573d533043d5915b054cc124c626972456c1533043d6915b05f153304626915b054cc12143d60025c915b054cc15915b054d393043d67adb054d072e8626915b054d073a0c166c18354d3f3046269b1eb41cc12046267add36c15341c3d6855eb6c15341c466845eb6c15341c6269e5eb63d53304626002456c1953046257fdb054d07304626002456c153188115915b054cc11880067adb05cd07304466a26456c1533046267adb05c5072306260024585d53304625915d56c153230626915b054cc11883767adb06795341c4069160d6c153304626915b054cc11883d6915eb6c171304626915d46c15341c62691e456c153304626915b054d263043d6
  | 5, 23 => 0x9b24541cc1208626002456c1530f42059b1eb41cc12083d6915b057d53304626002456c17c304625915b063d533046267adb054107304626955eb6c10730462687deb6c153304626915b054d073b46267adb054d073b43d6916296c1533046267adb054d072606267adb054d41304626896026c153304626855eb6c15341c3d69161b6c1533046267adb05e55341c626915db6c15330462696a456c153304626915b054ccf3046267adb054d07304ae6891eb54d073046267adb05d15341cb560025c915b0654c157adb0591073046267adb054d073045867ada854d073046267adb054d072506267adb054d0737cc16a16456c153188326916076c153304626
  | 5, 24 => 0x9160c6c153304626915b054cc1188196915b054cc10f42f698e456c1073046267adb054d073306267adc354d07304626915b054d07304b067adb054d072786269b256915b03046267c5b054d07304626002456f553304625915b0695533046267adb05c507304626002766c133304625986456c153304626915d56c153304626915c56c15330462600245801b054c3d5915b054d07378626916156c1533043d67adcf5c55341cc167adb654d07304626915b05e5533046267adb054d073783d6a1a456c1533046269b2097ad073046267ada154d073046260024588d53304625915b054cc1250626915b054d1a304626915eb6c1532d46267adb054d3a41cc16
  | 5, 25 => 0x7adb054d072d46267adcf54d072303d67adb054d07304a36916026c153304626915eb73d533043d6915b066953304626915b054cc1188296915b05ed53304626915b054d27304626916106c153304626915b054cf63046267adb054d073443d67adb054d073047e6915b054ce03043d68b5b054d07304626915b054cc10f41a67f5d86c15341cc16915cf6c1533046267adb054d423046267ada754d07304626976456c153304626002456c15326c6250023b6c1533046257adb054d08304626916177ad5330462695deb6c107304626915b054cc5304626879b054ce0304626915eb6c1533046267adb054d072f86267adb054d023046269b1eb54d07240626
  | 5, 26 => 0x915b054cc12d4626915a554d073046260026791553304625916237ad53304626915b054cc10f42b6915b05e953230626915b054cc12483d6916186c153304626001eb6c15341ca157adcf54d072d43d6915b05c5533043d6915b062d8354cc16879eb6c19e54c6267adb054d073045a6001fd6c17141c625915eb6c17c3046267adb05e15341c3d67adb054d07304516915b054d0727c6267adb0599073043d6a12456c1533046267adb0579073043d67adb057107304626915b054cc11885e6002456c1533045057adb054d072703d6885eb6c153304626002456c1534683d5915b054cc12306267adb054cfb304626915b054d2c3046267adb054d1e41cc16
  | 5, 27 => 0x801eb73d5341cc16995eb54d0730462685deb54d3f3046267adc454d073043d67adb054d073406267adb067d5341cc16915b054cc1188176002456c1713043d57adb054d3f3046267ddb054d073043d6915d863d533046267adb06798b54d076915b054cc11fc6269161c6c15330462685deb54d07304626915b054cc1188226916306c1533046267adb054d073046267adb054d073703d67adcf54d073044667adb052d07304626915b04ccc1208626942458c5b054cc16a16456c1531881a67adbb54d073046267adb054d072803d6915b054cc12c08267adb054cfd3046269b2456c1743046267adb054d07304486915b054d3d304626915b054cc11dc3d6
  | 5, 28 => 0x915b054cf13046267adb054d40304626915b054cc1188116915b0609533046267adb056d07304626915b060d533043d6002456c1532303d5915b054cd93043d67add86c15341ca86916286c1533046267adb054d072b0626915d8755533046269162e6c153304626915b054d283046268edeb6c153304626915b054cc1304626915b054d2e41c3d67adb054d07304656002458c5534e46257f5b054d2e41c3d6915b054cf33046267adb054d07318626915cf54d07304626916316c1533043d6915b054cf4304626809b054d073046267adcf54d073043d6915b054d073045668e1eb6c153304626916276c153304626915b054cc11883b67adb054d07378426
  | 5, 29 => 0x915b054cc10f43167adb054d072f0626915b061d53304626915eb6c1533045067adb054d1d41c3d67add16c15341c626915f86c1533046267adb054d0737462688deb54d07304626915b054cc11882a6a22456c1533046268b1b054d07304626916006c1533043167adb054d1941cc167adb054d073b0c16915b05e953304626915b054d072406267adb0585073043d67adb054d072403d699a456c1533046267adb054d073b44f6915b054cc11881567adb05f1073046269158f54cc12086267adb05d95341c626915b054ce13046269fe5c915b054c626002456c18b54cc15915b054cc11e0626915b054d073045967adb054d073044067adb054d07304736
  | 5, 30 => 0x955eb6c18b41cc167f5b054d072143d6002458e5b054c625915b054cc1188026915b054cc12bc626916326c153304626915b054cc11880b699e457ad53304626915b054cc10f4206915b0655533043d6915b054cc120c6269da6c915b03046269c2456c1533046267d5b054d07304626002456c1533044657adb054cfe3046267adcf54d1a41cc16955dd6c10730462600250915b054cc15002456c153480625809b05f1073046268d1b054d07304626915b05f953304626002456c1534f8c15781b054d072506267adb0519073043d67adb054d073787f6915b06795341c626002456c1532246259561e7adb03046267adb06795341c3d6915b054cc11880f6
  | 5, 31 => 0x916256c1533046269e64563d53304626915b054d1a3043167e5b054d073046267adb054d073046767adb054d09304626002456c1953043d59b2456c0c12146269160e6c1533046260024554d391883d59b24554cc12306267adb05c5072303d67adb054d073045269b1eb54d072d4626915b054cc10f43d6915eb6c1713043d68e9eb6c1533046267d9b054d07304626002456c1533043d5916266c15330462695a456c1333046269160a6c153304626916006c1533043d6915b054d2e1883267ada654d07304626972456c15341c3d6915b054cda3046267adb054d22304626915b054d072143d681deb6c15341c3d67adb054d0724c3d6971fd6c15341c3d6
  | 5, 32 => 0x915c254cc1188206916156c15341c3d6915eb6c18b54cc16915b05e55341c6267edeb6c15341cc16915b054ceb3046269b1eb41cc121c626855fd6c15341c3d6915e06c1533046267adb054d073046f6915b062153304626915b054cc126c626915b059107304626915b054d07250626915b054cd33046269b245861533046267adb054d07304506915eb6c1532303d6915b054d3730462696e456c1533046267e1b054d073046267adb0591073043d67adb054d072503d69e6456c15327c626915b05b553304626915b054ce9304626915dd6c1533046267adb054d173ecc167adaa54d07304626915b054ce43046267adb065d5341cc167adb054d072ac626
  | 5, 33 => 0x942457adb054cc167f5b05d15341cc16915eb6c153480626801eb6c17141cc16915b054d48304626915d96c153304626915eb6c1534f8c169b1eb6c107304b06915c66c1533046267adb054d073044d67adb054d1741cc16915b054cc11fc776915b054d1a3043d60024570953304625a16456c1531883d699deb54d073046267adb054d2b3ec6267adb05c507304206915d86c153304246915b054cc1244626915b054107304626956456c1073046267adb054d0d304626002316c153248625915d56c153304466915b063d533043d6955eb6c1073043d67adb054d073d4c1683deb6c15341c626915b86c1533046267adb054d13304626915b054cf0304626
  | 5, 34 => 0x916456c153304626915b054d14304626915b054cfa304626915eb6c1533043d6915fd6c153304626775b054d07304626002456c1532a0625002456c1483046259160c6c1533043d6915b054cc10f4196916176c1533046267adb054d2b41c62694e456c153304626915b06c153304626915b054d23304626915b05d1333046267a5b054d07304626879eb6c1533046267adb054d043046267adb054d07304a16915b0595533046269e2456c1533046267adb054d072304669f2456c153304626915b05c5073046267c5b054d073043d67adb05c5073043d6915eb6c153304466915d56c1533043d6915b054cc122c626959b04cd07304626915b054cc11ec626
  | 5, 35 => 0xa16456c150304626915b054d072d46267adb054cfb3043d6001b054c921883d57add26c15341c6267adb05c51a41cc167adb054d072d43d68eddd6c1533046267adc25d15341cc16a1645755b054c626915b054cc11c8626915b054cc11881f6801eb6c15341cb567adb054d072ec626915b054ce8304626915b054cc10f4296915d86c17454cc16002456c19a54cc15002456c1533d8c157adb062d5341cc16915cf6c1533043d6916156c153188326915b054cf2304626915b054cc11882e6781b054d07304626976456c1533043d67adb054cfc3046267adb054d073044e60025d915b054cc15915b0671533046267adb054d072303d685ddd54d07304626
  | 5, 36 => 0x7adbb54d073043d69b24589553304626915b054cc1224626915b06698f54cc16915bd6c15330462694db054d07304626916166c153304626002456b5533046258ddb054d07304626916186c1533043d67adb054d073b4e86915eb70953304626915b054cc1188066001eb7616441cc15001eb7097441cc15915b054ce3304626915b054cc1220626916236c1533046267adb054d07304466915b054cc1188396915b054cc11881e67adb054d1f41c626941eb6c15341cc167adb054d2041c62695245761b054cc16915b054d2e1881a67adb054d3e41cc167adb054d07304416002456c1533045e5916066c153304626915b054cfb304626915b054cc12303d6
  | 5, 37 => 0x915b054cc12c0626915b054d3f3046267adcf6c17141cc16915b054cc10f41767adb054d3f3043d69161754d07304626915d86c1532d4626915b06815330462685deb54d073043d69da456c133304626002456c1533047f5915b054d07304626915b054d203046267f9eb6c15341cc167adb05c5072a06267adb054d073043d67f5b054d073046267adb054d2d41c626915f46c1533046267adb054d07294626
  | 6, 0 => 0x7adb054d073047b189c007adb054d2e41c5960026c915b054cc11899eb765b054d073046277adc66c15341cc1189e456c153469073046277adb054d073047f1dddeb6c153469073043d7001eb7095341cc11899eb761b054d07304247915b063d5341cc1189deb755b054d0730446700245761b054cc11899eb6e1b054d073046277adb054d073c0c1189deb7095341cc11882077adb054d073acc1189deb781b054d0730462700000915534e4c11895eb6c18854d07304627831e06c15341cc1189deb6c15341cd33046279b2187ad5341cc1189e5b7adb054d07304627916457adb054cc1189c00915b054cee3046267adb054d073a4c1189deb775b054d073046270025c915b054d073059eb6c15341ce4304627001eb6c17e3b8c1189a257adb054d07304627
  | 6, 1 => 0x7adb054d073043d0a5deb761b05d15341cc17001eb6c15341c621658007adb054d073d8c167adcf6c15341cc10f5deb6c15341cf23046277adb054d07304620b9e5d7adb054d073043d70025d7adb054d073059eb6c19c54d07304627959b054d07380c1189e457adb054d073046277adb054d1441cc1189deb6c15341cfa3046277f5eb6c15341cc1189e45831b054d07304627915b054d0730462065c00831b054d26304626001eb6c15341ca8189a0c7adb054d073043d77adb054d073043d065e177adb054d07304627002456c153304821899eb6c1b054d073046277adb054d2341cc1189c00a16456c1533046267adb05955341cc1189e7c7adb054d07304627001eb6c15346107189a45755b054d073046277add56c15341cc10f5deb6c15341cc122c627
  | 6, 2 => 0x1eb6c15341cc11fd9eb6c15341d073046277adb054d2041cc1189c008c5b054d2641c626001eb6c15343cc11899f47adb054d073046279b2257ad5341cc1189deb6c15341cc12246279b2457adb054cc1189deb6f5b054d07304627859eb6c15341cc1189c009e6456c153304626000006c15330492189645861b054d07304627861eb6c15341cc10f5deb6c15341cc11880677adb054d0738cc1189deb6c15341cc122062788deb6c15341cc1189e457add86c1533046277adb054d07304620e5deb6c1534b9071881a7915b054d073048c189e067adb054d073046277adb054d073ecc1189deb6c15341cc12303d7002457ad534e4c1189800959b041ce0304626915eb6c1533b8c1189deb6c15341cc11c86277adb054d073046207ddeb6c15341ce8304627
  | 6, 3 => 0x7add86c15341cc1189c00915b054cc11882460027f971eb6c15341d8007ad954e5073046267adb054d2441cc1189deb6c153511073046277adb054d07304620b5c007ad534e5073046267adb054d073e4c1189deb6c15341cc13043d77adb054d0730475189c007adb054d0735c6267adb054d073b8c1189deb6c15341cc11882170027f7adb054d0718980095a456c1533046267adb054d0730462061c00895eb54cc11dc6268e5eb6c15341cc1189deb6c1534950730462700231831eb6c1531899eb6c15341cc1188147915eb6c15330482189deb6c18154d073046277adc16c15341cc1189e456c15341cc1188177a16457adb054cc1189deb6c15341cc12c06277adb054d3f41cc1189deb6c15341cc10f41777add86c15341cb5189deb6c1a054d07304627
  | 6, 4 => 0x20c7adb054c620f59eb6c1534b9073045977adb06395341cc1189c00915b054d3330462688deb54d073b8c1189e79915eb6c153304627001eb6c153304921899eb6c15341ced3806277adb054d0730482189e357adb054d07304627a15eb6c15341cc1189c007adb054d07304836001b054d2641c620f5a157adb054d071881a77adb054d3141cc1189e456c17e54d073046277adb05f95341cc10f5deb6c16441cc11882477adb054d07304b1189c008a9b054d07304626001eb6c153438c1189a6c7adb054d07304627a05eb6c15341cc1189e747adb054d07304627915b054d07304620a9deb6c15341cc10f42a7965eb6c15341cc1189e456c17a54d073046277adb054d073a0e0305deb6c17a54d073043d70025c7ad534e5073059eb6c15341cc1188237
  | 6, 5 => 0x8a9eb6c15341cc1189c00915b054d2e3046267adb054d0737877189deb6c19d54d073046279e5eb6c15341cc1189deb6c153438c11881970020c7adb054c941899eb6c15341cc11883670025c7adb054d2e41da0b7adb054d073046277adb054d0730462165e457adb054cc1188247001eb6c1954b907189800952456c1533046267adb054d2e41c620f5e7a7adb054d07304627001eb6c1534b9071899eb6c15341cc12a06277adb054d4341cc1189deb6c15341cce304627916256c15341cc1189deb6c15341cc118856795a457adb054cc1189e257adb054d073043d77adb054d073048d189deb6c153469073042a77adb054d2141cc1189c007adda6c15341c626002456c17454cc1189800915b054d073043d67adb054d1841cc1189c007f5b054d073043d6
  | 6, 6 => 0x7adb066d5341cc1189deb6c18654d073046277adb054d073043d07dc00915b054d393046269fdeb6c15341cc1189e0c7adb054d2e41c627989eb6c15341cc1189c007adb054d073a0c169bdeb6c15341cc1189deb6c15341cc1188247916456c15341cc1189c00915b054d263046260020d7adb054cc1189a457adb05d1533046277adb05fd5341cc1189e457adb054d073043d77add56c1534b907189deb6c15341cc11880e700000916316c1531894007adcf54d071883d6971eb6c15341c620f5dfd7adb054d073043d77adb054d07214620f5c009da456c1533046267adb054d07304620a1e6c7add854d07304627959eb6c15341cc1189e1e7adb054d07304627915eb6c1534ccc1189c00915b054cc11883267adb054d0730462035deb6c1534d107304627
  | 6, 7 => 0x1eb6c15341cc12c18008618354d073046267adb054d0730462029e456c15341d073046277adb05815341cc1189c006c153499073046267adb05d15341cc1189c00916156c153304626915eb6c153304620c9c007adb054d073786267adb054d2041cee189deb6c15341cc11f06277adb054d1b41cc1189deb6c18d54d073046279b1dd6c15341cc1189c009b1eb41cc12086267adb054d3341cc1189deb6c15341cf7304627915eb6c1534b8c1189e5f7adb054d073046279ddeb6c15341cc1189deb709b054d073046277adb054d07304620d5c007adb054d073b4626855eb6c15341c620f5c006c153498fb3046269b1eb54d0730482189deb6c15341cc11881b7952457adb054cc1189c00972456c1533046267adb054d0735cc1189c00915b054cc1214626
  | 6, 8 => 0x915eb6c1534e4c1189e45761b054d073046277adb054d2f41cc1189deb6c15341cc12046277add86c15341cc10f5deb6c15341cc1268627002456c153380c1189800915b054cc11881a60025c831eb6c153305a157add56c15341c627801eb761b054d07305deb769b054d073046270024554d3941cc11898007ad534e5073043d60020c7adb0654c1189a456c15341cee304627915eb6c153498c1189e547adb054d073046277adb054d073b8c10f5c00916317adb054c6260025c6c15349907305800831eb6c153304626869eb6c15341cc1189deb6c15341cc10f41879da457adb054cc1189c007add554d07230626991eb6c15341cc1189deb6c18c54d07304627001b06552641cc11898007adb054d070f4246961eb6c15341cc1189c00002456c1531883d5
  | 6, 9 => 0x9b9eb6c15341cc1189c00915b054cc11dc6269d9eb6c15341cc1189deb6c18054d07304627002456c153304620ad800915b054cc1248626915b054d0730482189e85915b054d073046277adb054d07304820f5c007adb05c5071883d67adb05e9534b907189deb6c15341cc11f4627001eb6c15341c6a1898007adb054d071b46267adb054d073bcc1189deb6c15341cc1188327856006c15341cc1189deb6c15a54d073046279b2456c15341cc1189deb6c153498fb3046279b1eb6c15341cc10f5deb6c15341ce53046279b1eb6c17e41cc1189deb6c15341cc11883477adb054d07304620b1deb6c1534b907304627972457adb054cc1189deb6c15341cc10f4237915eb6c15330485189db060d5341ce03046277c9eb6c15341cc1189deb6c15341cc1188257
  | 6, 10 => 0x2456c153364c11899eb6c18554d07304627002456c1534b9071898007adb054d2e41c3d6001eb6c16841cc1189800916316c1533046267adcf54d07304620f5c007adcf54d07304626971eb6c15341cc1189deb6c15341cc121462792deb6c15341cc1189deb6c15341cd63046277adb054d3941cc1189c007adb054d073045660025c8c5eb6c15341d9eb6c15341cc1188137001f76c15341cc11899eb6c15341cc1188087895eb6c15330477189c00915eb6c1531883d67adb054d1841cc10f5c008c5eb6c19541c6267adb054d0730462189deb761b054d1a41cc177adb054d07304620f1deb6c153499073046277adb05a15341cc1189deb6c19e60d5341c627916157adb054cc1189deb6c15341cc1238627002317adb054d07189a097adb054d07304627
  | 6, 11 => 0x915eb6c153304620ade557adb060d07304627915eb6c15330492189c007adb0655071883d67adb054d0730462075deb6c15341cc1188037001eb6c15341c620f59eb6c16754d073046277adb054d073b4c1189e157adb054d073046277adb06655341cc1189deb6c15343d07304627001eb6c19e54d07189800915b054cc11883167adb054d073047a189deb6c15341cc11881278bdeb6c15341cc1189e79915b054d07304627001b054d07304921899eb6f1b054d07304627a0deb6c15341cc1189c007adb054d072406267adc86c15341cc1189e6d7adb054d073046277adb054d073e0c1189deb74db054d073046277adb054d0723062069c007adb054d07304596915eb6c153380c1189e457adb054cc11881a77adb054d073d8ee305c00915b060d53304626
  | 6, 12 => 0x875eb6c15341cc1189c007adb059107304626001eb6c15341c94189a557adb054d0730462700000972456c1533056458c5eb6c1533046277adb054d3f380c1189e177ad5341ce0304627915b054d0730462091c00002456c1953046257adb054d07380c1189deb6c1534c9073046277adb054d073043d091deb6c15341cc11881a79edeb6c15341cc1189c00915b054cc11883d67adb05915341cc1189df77adb054d0730462700000915b054cc1189400916006c1533046267adb06255341cc1189deb6c15341cde3046270025c7adb054d070f58007adb054d072143d67adb054d0730462015e56915b054d07304627855eb6c17a54d07189e567adb054d073043d7915eb6c15330477189deb6c15341ce2304627002456c15330462081800915b065553304626
  | 6, 13 => 0x245755b054cc11899eb6c15341cc11a8627889eb6c15341cc1189c006c153499073043d67adb05d15341cc10f5deb6c17854d073046277adb054d073046209ddeb6c15341cc11e46277adb054d073046d189deb6c16a54d07304627801eb6c17454d07305deb6c15341cc12706277adb054d0730462025c00915b054d1a3046268a9b054d073b8c1189e457adb054cc11883177adb054d0730477189e456c1534cd073046277adb054d07304620addeb6c15341cc12486277adb05d15341cc1081deb6c17a5d107304627002456c18f54cc1189800955eb6c1073046267adb05c55341cc1189deb6c15341cd1304627002157adb054d070f59eb6c15341cc1188507915eb6c18354cc1189deb6c15343907304627915eb6c153364c1189c00831e06c153304626
  | 6, 14 => 0x2457adb0654c11899eb6c15341c8c1883d7861eb6c15341c90189deb6c18354d073046277adb054d07364c1189deb6c15341cc11880c77adb054d07304620c1e457adb054cc11883d7855eb6c15341cc1141e54915b054d07304627002457adb054cc11899eb6c15341cdc304627916007adb054cc1189c009160c6c153304626002456c153304620659eb6c15341cc11883877adb054d073a8c1189deb6c15341cc12806270020c7adb054cc10f5a317adb054d073046277adb054d0736cc1189e7d7adb054d07304627809b054d0730477189deb6c15341cc11c4627915eb6c15330462081e457adb0655533046277adb054d1241cc1189c007adb05d1073042067adb05c507304620f5c00975eb6c15341c626915b05d15341cc1189c007adb05c507304626
  | 6, 15 => 0x915eb6c18f54cc1189e507adb054d073046277adb054d07324c1189deb6c15354d07304627915b054d07304620c9deb6c15341cc12186279b1eb6c10730482189deb6c17a54d073045677adb054d0730487189deb6c153471073046277adb054d07398c1189c00942317adb054d0767ddb054d07304620a9c007add854d07304246002456c1533048c1898007adb054cfb304626001eb6c15341cb51899eb6c15341cc11883177adb05d15346907305c007ad534e52e41c626915b054d2e41cc1189e517adb054d073046277adb06115341cc1189deb6c1534b9073043d77adb06415341cc1189e0c7adb054d072506270025c915eb6c1533059eb6c18b54d073046277adb054d3041cc1189e8a7adb054d07304627001eb6c1533c8c11899eb6c17c41cc11dc627
  | 6, 16 => 0x1b054d2741cc11899f86c15341cc11882b7001eb6c153494c1189800915b054cc1188176001eb6c1534fcc11898007adb065507304626001eb6c15341c620459eb6c15341cc1188007002177ad5341cc11899eb755b054d07230627915b054d2641cc1189e0d7adb054d073046277adb054d07304620f5e477adb054d07304627915eb755b054cc1189deb6c153499073043d7001eb6c15341cc1189800916316c15341c6267adb05d15341ca8189e007adb054d07304627002317adb054d070f5a76915b054d073046277addc6c15341cc1189deb6c19e54d073046277adb054d1d41cc1189c00916186c153304626915eb6c153468c1189deb6c15341cc11881c77adb054d0730462081deb6c19554d073046277adb054d0730462119deb6c15341cc1240627
  | 6, 17 => 0x855eb6c15341cc10f5c0088deb54d07304626002456c153304620a9a457adb054cc12306277adb054d0730494189deb6c15346907304627001eb6c15341c3d081800915b05e9533046267adb057d5341cc1189c007adb05f1073046267adb063d5341cc1189e297adb054d0730462786deb6c15341cc1189deb76db054d07304627969eb6c15341cc1189deb6c15341ccf3046270025c7adb065507305a5c915b054d07304627915eb7adb054cc1189c00809b054d07304626915b054d0730485189e077adb054d07304627001eb73d5341cc10f59eb6c15341cc124c627971eb6c15341cc10f5deb6c17c54d07304627915b054d3941cc1189e45831eb6c153304627915eb6c15330462065deb6c15341cc12143d70025c7adb054d073059eb6c1534e5073043d7
  | 6, 18 => 0x809eb6c15341cc1189c00916256c1533046267adb054d07304620a5deb6c17b54d073046277adb054d2741cc1189e107adb054d073046277adb054d073d8c1189e456c15341ce0304627001eb6c153468c10a9a456c15341cc11881a77adb054d07380c10f5deb6c15341cc10f41a77adcf6c15341cc1189e457adb054cc1188177001534e52641cc1189a5d7adb054d0730462700000915b054cc10f54007adb054d0734c6267adeb6c15341cc1189e0c7adb054d073046277adb054d0730462065e45861eb6c153304627002456c15341c620f5a6c959eb6c107304627001fd6c15341c620f58007adbd54d07304626002456c17e54cc1189a617adb054d073046277add56c15341cc1189deb715b054d07304627916156c15341cc1189c00801eb6c15341c3d6
  | 6, 19 => 0x7adb054d073d0c1189c00879eb6c15330462689deb6c15341cc1189deb6c15341cc11883b77adb054d073046205dc007adb05c5073043d67adb054d073047f189e1c7adb054d07304627915eb6c17e54cc1189e508c5eb6c15341cc17915b054d0730477189deb6c15341cc12c08279b1eb6c17441cc1189deb6c1534f5073046277adb054d07304770f5deb6c15341cc12d4627915b054d07304620ade456c15341cc1248627915eb6c153304620a9deb6c15341cc10f42b77adb05e95341c8c189e187adb054d07304627915eb6c17a54cc1189deb6c17154d073043d77adb062d8354d07305c007adb054d07304506001f86c15341cc11898007adb054d1a41c3d67adb054d073048c189deb6c1534b1073046270020c7ad534e4c1189a1e7adb060d53304627
  | 6, 20 => 0x7adb054d07304620a9deb6c17a54d073046270020c7adb054d2e189a667adb054d073046277adb054d0730462055e45895eb6c1533046277adb054d07384c1189e7f971eb6c15341c627001eb6c18b54d073059eb6c15341cc11e0627001e06c15341cc11899eb6c15341cf1304627915b060d5341cc1189e456c15341cd93046277adb054d0730462045deb6c18254d073046277adb060d5341cc10f5c007adb054d072303d67adb054d07364c10f5c00916456c1533046268a1eb6c15341cc1189c006c1534b92641c6267add87555341cc1189c00915eb6c1533043d68b9eb6c15341cc1189deb6c1534a107304627001dd6c15341cc11899eb6c15341cc1304627002317ad534e507189a458c5b054d073046277adb054d073ccc1189e317adb054d073043d7
  | 6, 21 => 0x839eb6c15341cc1189c007ad534e5071883d69b1eb54d073048c189e456c15341cc11883d77adb054d0f30462069c00915b054d073046267adb054d073043d0f5dfd6c15341cc11883d7001eb6c15341cc10f58007f5b054d07304626899eb6c15341cc1189e45801b054d07304627829eb6c15341cc1189e007adb054d073043d77adb054d07368c1189c008e5eb6c15341c6267adb054d0730462009e456c15341cc1188207915b06555341cc1189deb6c15341cc10f42077adb06555341cc10f5deb6c15341cc120c6279c1eb6c15341cc1189c007adb054d07304466002507adb054d073058007adb054d2041c6267adb05f95341cc1189c007adb054d07224626915b054d07304620c5deb6c15341cc11880f77adb061d5341cc1189df87adb054d07304627
  | 6, 22 => 0x915b065507304626001eb6c19541cc10f5a6c7adb041cc1214627
  | 7, 0 => 0x7adb054d0730462081deb6c19554d073046277adb060d5341cc1189deb6c15341cd9304627002457adb054cc1189a317adb054d073046277adb054d0730477189deb6c15341cc11882b77adb054d07380c1189deb6c15341cc11881a700000915b054cc11894007adb054d071883d6855eb6c15341cc1189e5c7adb054d073046277adb054d0730485189deb6c1534e5073046277adb054d2641cc1189c008c5eb6c15341c6267adb054d2e41cc1189c00831eb6c153304626001b054d2641cc11899eb6c17454d073046277adb054d0730462091e567adb054d07304627001eb6c1534b9071899eb6c15341cc12086279b1eb6c15341cc1189deb761b054d07304627001eb54d3941cc11899eb6c15341cee304627915eb6c15341cc1189e257adb054d07304627
  | 7, 1 => 0x915b054d07304626001eb6c15341cc10f59eb6c17e54d073046277adb054d07304620a9deb6c17a54d073046277adb054d073046205de187adb054d073046277adb054d073048c189e0c7adb054d073046277adb054d0730462065deb755b054d073046277adb054d1a41cc1189c00971eb6c15341cc16001eb6c19541cc11899eb6c15341cc11883d7001eb6c15341cc1189a007adb054d07304627
  | 8, 0 => 0x7adb054d07304626
  | _, _ => 0

private def wordBlocks : Nat → Nat
  | 0 => 0x62400000000000000000000000000001800000000000000000000000000000002400000000000000000000000000000018000000000000000000000000000000400000000000000000000000000000008000000000000000000000000000000000c044000004aa6c00000000000000000000000000000000
  | 1 => 0x2014000000000000000000000000000080020000000000000000000000000002000144000000000000000000000000080000041002062290000000000000000480000200000000000000000000000010000000000000000000000000000000080000200000000000000000000000000800100301100000100020
  | 2 => 0x60008090c27a18aac0010120000000010400200000000000000000000000000410000000000000000000000000000010000200000000000000000000000000400000800000000000000000000000010000004209c80082000000800000000201476404c0c588a4068ec900000000080505100000000000000000
  | 3 => 0x50002200000000000000000000000001400008000406028c5034708800000000660c0889ac27a18aac0810124000000198300796b09e862ab020020d00000006604096d8c27a18aac0010930000000190300206a09c80082020000900000006204016584008188a400008100000001801000060000000000000000
  | 4 => 0x82170203676400c0440000048a480002085c00088000036118040016292000082126206076584c0c588a40408c900020848000818900301100000102120000821200020000000000000000000000020848000000000c6049144004a50000000056207616584c0c588a404828900000014080d85100301100000120820
  | 5 => 0x108006004800180000000000000000004200019471804309e862ab08810080010800065088090c27a18aac2010120004200018073824309e862ab008504800108000450800108272002082000020004200008071804100206229008100000108000000800100000000000000000002085d801885920361180400162b24
  | 6 => 0x108056207e76584c0c588a4068689000420158817850610620e26900e1a040010805604ca001b83f2a3348f9400240042014080f9d1413031622901a18200010800665dc7e5ac27a18aac2a04834004200191720206a09c800820a0000900108006205c76584008188a4020481000420018012000630fe8e2ebcac524f
  | 7 => 0x18a176006a00580d84601000500080006285d801a800603611804001629200018a176006a00180180201000100000006285c000f980003611804001e39200018a12641480818b3f32471829010240062849881f1d9613031622901833240018a126004862184188389a4030cc100062848080f18941303162290183120
  | 8 => 0x18a176006a76584d8c789a4078ec90006285d801a989603611804001421200018a176006a62580180201000100000006285d801a988613631e26901e3b240018a176006a62184188389a4030cc10006285d801a980600600804000400000018a176006a16580d8460100058ac90006285d801a80960060080400040000
  | 9 => 0x18a176206a14580180201000100000006285d881a800610620e26900400000018a176205e76184188389a4038ec10006285d813a800680600804000400000018a176046a00180180201000100000006285d803a800680600804000400000018a176007e62184d8c789a4078ec90006285d801f980603611804001e3920
  | 10 => 0x18a176207e16584d8c789a40582890006285d881f851603611804001608200018a176207e14580180201000100000006285d881f850613631e26901e3b240018a176207e14184188389a40386810006285d881f800600600804000400000018a176206a76584d8c789a40508c90006285d881a859610620e2690040204
  | 11 => 0x18a176207e76584c0c588a4068ec90006285d881f9d9610620e26900c12040018a176207e76580d8460100058a480006285d881f9d1613631e26901e18200018a176207e74184d8c789a4078ec90006285d881f989613631e26901c31200018a176207e60184188389a40304000006285d881f859613631e26901e3b24
  | 12 => 0x18a176247e76584d8c789a4078ec90006285d883f9d9693631e26901e3b240018a176207ef6584d8c789a4078ec90006285d881f9d9e13631e26901e3b240018a176207e76584d8c789a407aeed0006285d881f9d9613631e26901e3b240018a176207e76584d8c789a40786890006285d881f9d9613631e26901c3324
  | 13 => 0x18a176607e76d84d8c789a4078ec90006285d917a8206a0fc880c20a400090018a176456a001883f2203082100020006285d905a820600600804000400000018a176416a00180180201000100000006285d903a8206a0fc880c202400090018a176406a08180180201000100000006285d893f9d9693631e26901e3b24
  | 14 => 0x2050200410060a40000000000000000006285d997f9f96b3ff9e2eb0be3b2d0018a176657e7658cffe78bac278ecb0006285d985f9f9613631e26901e3b240018a176617e76584d8c789a4078ec90006285d983f9f96b3ff9e2eb03e3b2d0018a176607ef6d8cffe78bac079edb0006285d981f9f9613631e26901e3b24
  | 15 => 0x21da376617e76fc4d8c789a4078ec9008768dd905a982f0060080400040000021da32001086004318124511232d40808560801847182d100206229008100002158200450860b48272002082000020085608010421825309e862ab488504a020d2320412062e40c0440000040848008140801840382d309e862ab0004048
  | 16 => 0x8820051223614600c044000004820c0220801441a88018c30130c1035100300882005106a20003000083040d040000220801440888000430130c1035308b00882000147800803b27387658f8410242208000408800180301100000100030088200010220000000000000000000002208000408000004c0061d143418490
  | 17 => 0x88a2127436008183001044100001000222884850c81a900f01511040102520088a2121432008603c054441004010c0222884850c802000c00411040000400088a2121022062600c044000004084c02228848408800000f0151104010a5300882005746e2081b827283248d840024220801449ad8510c30130c103530820
  | 18 => 0x88a217743e2080b3181a7550d941004222885dd0b88206ecfce9dd63650409088a217706e2080b3181a7550d941004222885dc0b88202cc6069d543650401088a217147a20803300187450d041000222885c408880004f6179d54357adb0088a2171022200013181a7550d1410002228849d0f80206ac9cc11860200409
  | 19 => 0x89aa12747e8081ab273046182801024226a849d0da02062cfcc91c60a40409089aa127436808183001044100001000226a84851ca02042c9cc118608004080892805747ea081b827283248f840024224a01451ea8004e09ca0c923c10008088a217747e2081bb27387658d841024222885dd1f88202ecfce9dd63e50409
  | 20 => 0x89aa17706ea001a0180201000100000226a85dc19a80060060080400040000089aa17702ea081b3181a7550d941004226a85dc0ba80068060080400040000089aa177026a00780d846010005000c0226a85dc09a80064c6069d543450400089aa177026a00180180201000100000226a85c41ca80004c6069d543c50400
  | 21 => 0x89aa177227e76597d8dffdf4d7efed0226a85dc89f9d9613631e26901e3b24089aa17707ea080b3181a7550f941004226a85dc1fa8006ecfce9dd63e50409089aa177076a00193181a7550f141000226a85dc1ba8206ecfce9dd63e50409089aa17706ea001bb3f3a7758f941024226a85dc1ba8006c06028c503450000
  | 22 => 0x89aa17743ea081ab3f3247180901024226a85dd0da82066cfce9dd63e50409089aa177436a08183181245100101000226a85dd0da82060060080400040000089aa177436a00180180201000100000226a85dd09a82060060080400040000089aa17726fe765b4d8cfb9e4d7cec90226a85dc89f9d9e13631e26901e3b34
  | 23 => 0x89aa17747ea081b83f2a3348f940024226a85dd1fa8206cc6069d543450400089aa17747ea081ab3f3247182901024226a85dd1fa8006e0fca8cd23c50008089aa177476a0819b3f3a7758f941024226a85dd1da82062cfcc91c60840408089aa17746ea081b83f2a3348d940024226a85dd0fa8206ecfce9dd63e50409
  | 24 => 0x89aa17747ea085bb3f3a7758f941024226a85dd1fa820eecfce9dd63e50409089aa17747ea081bbff7e7758fdeb6e4226a85dd1fa8206ecfce9dd63e70c89089aa17747ea081bb3f3a7758f969424226a85dd1fa8206ecfce9dd63e58499089aa17747ea081bb3f3a7758f941024226a85dd1fa8206ec9ce1d963e10409
  | 25 => 0x89aa177637e7e587d8d7cdb4078fc90226a85dd1fa9a96effdf9dd63f52529089aa17747ea6a5bb3f3a7758f941024226a85dd1fa9a06ecfce9dd63e50409089aa17747ea0a5bb3f3a7758f941024226a85dd1fa8226ecfce9dd63e50409089aa17747ea087bbff7e7758fd410e4226a85dd1fa821eecfce9dd63e50409
  | 26 => 0x89aa17767fe681bf3fbbfffcfb45024226a85dd9ff8716effdf9dd63f70c29089aa17767fe1c5bb3f3a7758f941024226a85dd9ff8206ecfce9dd63e50409089aa17767ea889bf3fbbfffcf951124226a85dd9faa206ecfce9dd63e50409089aa17767ea1e5bf3fbbfffcf941834226a85dd9fa8716ecfce9dd63e50409
  | 27 => 0xa9fa377637e76fc4d8c789a4078ecd02a7e8ddd1fa9a2fecfce9dd63e504090a9fa37747ea681fb3f3a7759fb6d42c2a3c8c850c81a290c004110400004000a8f2321032060243c054441004294c02a1c08050c818390301100000100030089aa17767fe7e5bffffffffcffcfcb4226a85dd9ff9f96fcfeeffff3ed160d
  | 28 => 0x1558e97620ea955a0180201000100000550121580308542c06028c50b670a851540485020b695420c04400000482080550120198302756a09c8008202000091540480620c0975a4008188a40000810550120188302546b09e862ab820424d15404800608095d2c27a18aac00101205501200082025508000000000000000
  | 29 => 0x600000886c1480b0c27a18aac001012180000220b05200800000000000000001ddae97767ea9d5bb3f3a7758f941024776ba5dc8bfbdde93631e26901e3b341dc2485126a29543000083040d040000770921440a88550c30130c1035308b01dc2480122a095620c044000004000c05563a5d883fbdd693631e26901e3b24
  | 30 => 0x62050288081460240c044000106ae6c9806287f8b1fbd9e13631e26901e3b246018a1fe2c7e80380180201000100001804203603078000406028c507cf1882601080886d1c8030827200208200002180420220b07380c1002062290081000601080882c1c8010c27a18aad221412980000360b0da5180301100000120820
  | 31 => 0x621582882d1ce034c27a18aad221412988560a20b4738090000000004881002621582882d1c60344008188a5220400988560a20b07382d309e862ab488504a621582880d1c6024000000001220400988140a21b4538290000000000000000620502884d0080a4827200209201012988140a20a0538291002062294085042
  | 32 => 0x621582886d1ce0b4c27a18aad221412988560a21b47382d209c800820800008621582886d1ce0b44008188a4020400188560a213473829209c80082488504a621582884d1c60b4c27a18aad221412988560a2134718290000000004881002621582884d1c6034827200209220402988560a20b4738291002062294885042
  | 33 => 0x6215828e6ddce8bec27a18aad2a1412d88560a39b573dbf309e862ab488524e6215828e6d5ce0bcc27a18aad221412988560a21b67382db09e862ab488504a621582886d1cf4f4c27a18aad221412988560a21b473a2d309e862ab488504a621582886d1ce2f4c27a18aad221412988560a21b47383d309e862ab488504a
  | 34 => 0x621da3fe2d7e767c4d8c789a5278ec9988768ff8a1fbdbf13631e26941e7b66621da3fe287e767c4d8c789a507aeed988768ea1b4f38bd339f962ab498716a621da3a86d3ce0b4c27a18aad221412988560b61b4fbd3d339f962ab49a586a621582d86d3ee0b4c27a18aad221412988560a39b773fbfb09e862ab4a8524f
  | 35 => 0x689aa1ff4ffe081bb3f3a7759fbc722da26a87fcb9fbd9e13631e26901e3b34688200d92eb68023000083040d040001a208036438d8008430130c1035308b0688200892e3480600c044000004000c188768ff9b5fbdbf33ff9e2eb49e7b6e621da3fe6d7ef6fc4d8c789a4078ec9188768ff9b5fb82f30fe8e2eb48c504a
  | 36 => 0x6a9fa3f96f3ee0b5ffffffffdf7ff7e9aa7e8fe43cf98094f6179d547dfbdb26a9fa3a96f3ce8b4f27b1cebd2215129aa5e0b65befb82df09ea6ebb7c9504a6a9782896f3ce0f4ce7e58aad26141e9aa5e0a25bcf382d309e862ab488504a6a8702890f000025300187451f061249a26a87fdbffa20eecfce9dd63e50409
  | 37 => 0x6a9fa3ff6ffefeffffffffffdffdfdbdaa7e8ffdbffba2ffcfeeffff7ed544b6a9fa3ff6ffee8bfb3f3a7758f941025aa7e8ffd3ff9a0feffdf9dd67ffbdbb6a9fa3ff4ffe683fb3f3a7759fb4502daa7e8ffd3faa22fecfce9dd67e5444b6a9fa3ff4fea083fb3f3a7759f96126daa7e8ffcbdf9d9f5f637ff7d7dfbfb6
  | 38 => 0x7550c88e2cdcf77a4008188a40204811d5432238b372546b09e862abca8524f754048d82cb695620c04400000482081d5012360b25a540c00020c103430880754048882c9495620000000000000001d5012220a05255803011000001208b075404888281495004008188a70296b19d50122203202040e09ca0c92fe140cb
  | 39 => 0x7755ca886d9cf5f6c27a18aad2214129d563a7f8b3fbdde93631e26901e3b247558e9fe2cfef75bcffefbbefffdefbdd563a7f8b3fa55e80600804000400007558e9fe287ef7784d8c789a4078eed1d563a7f8a1fbdd613631e269c1e7be67550c8de2cde951bc3fabbbeffbd6b3dd5432239b77275ea09c800820a00009
  | 40 => 0x7dc248892eb495620000000000000001f7092224ba52558c30130c1035308b07dc248892e949563000083040d040241f70922243a02048c00020c1034100907755cade6ddef5bfc3fabbbeffbd6b3ddd572a39b773f7fb09e862ab4a8504b7755ca8e6ddcf7fec27a18aad2214939dd572a39b773d6fb09e862abca8524f
  | 41 => 0x7dc248d92eb695620c044000004820c1f7092364bada550c30130c1035308b07dc248d92eb695230c04c3040d4c22c1f7092364bada540c30130c1035308b07dc248d92eb69503000083040d0c2201f7092364ba5a548c00020c1034308907dc248d92ab695630c04c3040d4c22c1f7092224bad25588301100000100030
  | 42 => 0x7dc248d92eb6f5630c04c3040d4c22c1f7092364bada5d8c30130c1035308b07dc248d92eb695630d84e3140d5c22c1f7092364bada558c30130c10353a9b07dc248d92eb695630c04c3040d4c22c1f7092364bada558c30130c1035308207dc248d92eb695630c04c3040d4400c1f7092364bada558c00020c103410000
  | 43 => 0x7dc248df2ef6977b4c0cdb8e4d4c2ad1f709237cbbda55ec30130c1035308b07dc248d96fb69d630c04c3040d4c22c1f7092365beda558c30130c1035308b07dc248d96eb69d630c04c3040d4c22c1f7092365bada57cf39fb6ebb35348f87dc248d96eb695e30c04c3040d4c22c1f7092364badbdd8c30130c1035308b0
  | 44 => 0x7dd2c8d92ebef5734c0cdb8e4d6c62c1f74b2364bafa55cc30130c1035308b07dca69f96fb69d633c05c7450d4c32c1f729a7e4badbdd8c30130c1035329b07dca69f92eb695633d85e7550d5eb6c1f729a7e4bada558c36138c5035729b07dca69f92eb695630c04c3040d4c22c1f709237dbbda75ee39db0c9237308b9
  | 45 => 0x7ddae9ff2efe957a0d846010005000c1f76ba7fcbbfa55e80600804000400007ddae9ff2efe951bfffffffffffffffdf74b237dbffa75ee39db0c923f308b97dd2c8df2efef77b4c0cdb8e4d6c6ad1f74b237cbbfa55ef3ffbeefbfff5aff7dd2c8df2efe957b0c04c3040d4c22c1f74b2365befa55ce39db0c923d308b8
  | 46 => 0x7ddae9ff6ffe9d1bb3f3a7758f9c3225f76ba7fd3faa24eecfce9dd63e504997ddae9ff4fea891bb3f3a775bf95132df76ba7fcbbfbdded3633ee7935f3bb47ddae9ff2efef77b0d84e3140d5ca6c1f76ba7fcbbfbdde93631e26901e3b347ddae9ff2efe957b0d84e3140d5c22c1f76ba7fcbbfa55ec06028c503450000
  | 47 => 0x7fdfebf92fbef5673d85e7551f7ef6c9ff5f2b65befbd7df39fb6ebb7db58fa7fcf6bf96fb6f7e70c04c3040d4ca6c1ff1d2b65bedbd79c30130c1035308b07ddae9ff6ffeff7bffffffffcffcfef5f76ba7fdbffa75eeffdf9dd63f70cb97ddae9ff6ffe9d7bb3f3a7758f941025f76ba7fdbffa746fcfeefffffef5ecf
  | 48 => 0x80201406f0411ed84008188a400008120080501b43042b6a09c80082020000980201406d0410a98c27a18aae081093600805003c0062b4309e862ab000404880201400d0010ac00000000000000001ff7faffdbffbf7ffffffffff7ff5cfb7fdfebff6ffef7ffcffefbbedf7deff9ff7faffcbffbd4fffffffffffffffff
  | 49 => 0x82251600d1016ae400000000000000020894580344042212c9cc1186ca0c44b82251600900162e40c044000004284c20894580240058a1100206229c08f3468038b576f07f7ed84d8c789a4078ec9200e2d5db41ac2b600600804000400008028352690410a083181245120929c1600a0d4834085ab00301100000102120
  | 50 => 0x823db776b07f76fc4d8c789a407aecd208f6dddac1fddb713631e269c1efb66823db726d1496a9cf3fb3cfbf2b3dd3e08d6581bc575fbf100206229008120482359606d5c96afe827200208280002608d6581b4525aa7309e862abca8524f822d3720d1216ae40c0440000040848208b4dc834405aa10c0041104000a500
  | 51 => 0x88bab577f27f7ef84d8c789a4078ecd222ead5df5fac2b6ecfce9dd63e5040988aa3521d3210ac0300104410000100222a8d48648842900f0151104010a53088a21401d2210ae00c044000004000c208f6dddbc5fdfbf13631e26901e3b24823db776f17f7edcffff7cfbf2fbfdbe08f6dddb45adabf0060080400040000
  | 52 => 0x8aaf3721d32168a43c054441004294c22abcdc874c05aa90c0041104000a5108aa71601d3216ae40c044000004000c22a9c58074c85ab900000000000000008aa71601d3016ae43c054441004294c22a9c58074c05ab90c004110400084108aa71601d30168a430010441000210422a9c58074c042290c00411040008410
  | 53 => 0x8aaf3721d3216ae43c054441004094822abcdc874c85ab90f015110401004308aaf3721d3216ae430010441000010022abcdc874c85ab903011000001021308aaf3721d3216ac43c054441004294c22abcdc874c85aa90f0151104010a5308aaf3721d3216a843c054441004294c22abcdc874c85aa10c0041104000a500
  | 54 => 0x8aaf3721f321eae43c054441004294c22abcdc87cc85fb90f0151104010a5308aaf3721d7a16ae63c054441004294c22abcdc875c85ab90f0151104010a5308aaf3721d3a16ae63c054441004294c22abcdc874c85ab90f6159144014a5308aaf3721d3216ae43c054441004ab6c22abcdc874c85ab90f0151104010a530
  | 55 => 0x8aaf3771d3236ae43d856451005ab4c22abcddc74c8dab90f0151104010a5308aaf3727f3617efc7c0d5ccb40429cd22abcdc9f4f85abfaf9dd1186030a5398aaf3727d3616afc3c054441004294c22abcdc87ccd5fb90f0151104010a5308aaf3721f3356ae43c054441004294c22abcdc87cc87abd3f9fd73af010e578
  | 56 => 0x8abfb727d3696afc3c054441004294c22afedc87ccf5abd1f035732d018b5308abfb721d7296af4be774461824294e22afedc874ca5abd0f0151104010a5308aaf3777d3637eec3d856451005abcd22abcddc7ccddfb90f0151104012ad308aaf3771d7a36ae73c05c7450d4694c22abcddc74c8dab94f6179d54357adb0
  | 57 => 0x8abfb777d36b6afc3d856451005294c22afedddf4dadabf0c604914400404008abfb777d36b6afc0d846010005000c22afedddf4dadabf00600804000400008abfb777d36b6a9dfffffffffffffffe2afedc9fcdf5fbf1f035732d018b7348abfb727d7e96afebe77446182c294e62afedc9f4da5abf3fffdf3efcbcf77f
  | 58 => 0x8abfb777f37f7efc4d8c789a4078ecd22afedddfcdfdfbf0f6159144016ad308abfb777d7eb6affbff7e7758fd694e62afedddf5fadabfecfce9dd63e504098abfb777d7eb6a9ff3fbbfffffb7dd3e2afedddf5fadaa7ecfce9dd63e5a5098abfb777d7eb08bfb3f3a7758f9610662afedddf5fac227ecfce9dd6fe5c44b
  | 59 => 0x95605c00f0819fd2c27a18aac001012255817003c2067f0b09e862ab820424d95605c00f0819fc20000000000000002558170034206260a09c80082820404995605c00b00197c04008188a600109125581700240045d0030110000812abb48abfb777f7ff7effffffffffcffefcf62afedddfcdfdfbf1f635f36d01ebf34
  | 60 => 0x95605c06d0c11fdac27a18aae08109365581701b43047f2800000000820020595605c06d0c11f5a82720020a08008365581701ac3067f2900206229820424595605c06b0c19f5ac27a18aae08109365581701ac3067d2800000000820020595605c06b0c11f5a4008188a608008165581701a43047d28000000008200205
  | 61 => 0x95605c06f1c19fdac27a18aae08109365581701bc3567f6b09e862ab820424d95605c06f0c1ffdac27a18aae08109365581701bc3067feb09e862ab820424d95605c06f0c19fdac27a18aae08109365581701bc3067f6a09c80082020000995605c06f0c19fda4008188a400008125581701b43067f2a09c80082820424d
  | 62 => 0x9570dc06f0ddffdac27a18aae0a1493655c3701bc3267f6b0fe8e2ebcac524f9570dc06f0c99fdac27a18aae081093655a1f49bc387ff6b39f962ab830636d95687d26f0e19fdac27a18aae08109365581715bc3de7f6b39f962ab8324a6d95605c56f0e39fdac27a18aae08109365581701bd3067f6b09e862ab820424d
  | 63 => 0x9578fd76f0ffffdac3fa38bae0b1493655e3f5dbc3ffff693631e26901e3b249578fd76f0eb9fdac3fa38bae091093655e3f5dbc3ae7f680600804000400009578fd76b07ff7d84d8c789a6079ed9255e3f5dac1fddd613631e26981ebbb49570dc06f5ddffdac27a18aae2a1493655c3701bd7267f6b09e862ab8a0424d
  | 64 => 0x9de25c0192810903300187452d8612465df7fc9bc727ff7bcfecf3efcacf74f9775de06f5c9fffec27a18aae28109365dd7781bc777fffb09e862ab828524d9775de06f1c9ffdec27a18aaf2a1493e5d95781bc707fffb09e862ab820424d9578fd76f5eb9fdac3fa38bae291093655e3f5dbc3ffff6b3ff9e2eb83e7b6d
  | 65 => 0x9dfafd77d7eb091bb3f3a775af96126677ebf5decbfdfd6df637ff7db7fbfb59dea7d77f2e39fdbffffffffeddfbff677a9f5de4b8c7d2cf6179d54b77afb59dea7d27f3e19fdaf27b1cebe08119367789715fdb8e7f6f09ea6ebbb61424d9de25c07f2e19fface7e58aae0c109f67789701fcb867f6b09e862ab820424d
  | 66 => 0x9fef7f21f3a1ffe63c054441004294c277ebf5dfdfffff6fffffffffbff7f6d9dfafd77f7eb9fdbf3fbbfffef95193677ebf5dfdfae7f6ecfce9dd63e504099dfafd77f2eb9fdac3fa38bae091093677ebf5dfcbae7f680600804000400009dfafd77d7eb899bb3f3a775af95112677ebf5df5fac7d6effdf9dd6bf7afbd
  | 67 => 0xe235968efd5deabcc27a18aaf2a1493f88d65a23f477abd309e862ab488504a9fffff77f7ebffffffffffffefd79df67ffffddfcffffffbfffdf3ef83eff7d9fffff77d3eb7fdffffffffffffffffe7fbdfddf4f8dffbcf6179d54b77afb59fef7f71f3b7ffe63c054441004ab4c27fbdfc9fcf87fffbf9fd73af830e77d
  | 68 => 0xeabfb7ffdf7f6abdffffffffffffffffaafedfe77cfdab94f6179d547dfbdb2eabfb7a9ff3deaf4fe7f5cebd263d5ebaabcdfe7fcdffb90f0151104012ad30eaaf37a9ff35eae43c054441004294c388f6debbf577aaf3cfecf3efcacf74fe235968efdddeafec27a18aad2a1412f88d65a3bf577fbf309e862ab488524e
  | 69 => 0xf7655e88980181a4000000003003034bd5c3737bf37e7f6f0feaeefbfef5acff570dc8efddd9ffac27a18aae2810937d5c3723bf377ffeb09e862ab828524df570dc8efcdd9fdac27a18aaf2a1493fd581723bf3567feb09e862ab820424deabfb7ffffffeaffffffffffdff7d5efaafedffffdfffbf3fffdf3ef49eff7e
  | 70 => 0xf7655e8efdd5fffec27a18aae0810937dd957a3bf7067ffb09e862abca0424ff7655e8ef8d5fffece7e58aaf0ebefffdd957a3be357fffb09e862abc28524ff7655e88fd95ffe60000000000000003dd957a237606269a09c80082ca0404bf7655e88b815f7e44c0c588a706befdbdd957a22e057df9100206229c085246
  | 71 => 0xf775de8efdddfffe4008188a40204813ddd77a3bf377fffb09e862abca8524ff775de8e9ddd7f6e0000000032a0481fddd77a23f677ffdb09e862abca8524ff775de88fd9dfff6c27a18aad221412bddd77a23f677a6db09e862abca8504bf775de88fd1df7f4ce7e58aaf26beffbddd77a23f477dfd309e862abc88524e
  | 72 => 0xf775dedebcdff7ffcffefbbeffffefffddd77a3bf777fffb39f962abcbafbfff775de8efdddfffec27a18aaf2a1493fddd77a3bf777fffb09e862ab8a0424df775de8efdddfffec27a18aae0a14937ddd77a3bf777fffb09e862ab4a8504bf775de8efdddfffec27a18aad221493bddd77a3bf777fffa09c800820a00009
  | 73 => 0xf77dfffeb87ff7fc4d8c789a7079ed9bddf7febbf7f7fffb39f962abcb8736ff77dffaefdfdfffec27a18aaf2a1493fddf7febbf777fffbcfecf3efcacf74ff77dffaef95dfffcffff7cfbf2fbffffddd77b7bf7fffffb39f962abcba5a6ff775dedefdfffffec27a18aaf2a1493fddd77b7bf77fffff0feaeefbfef5acf
  | 74 => 0xfdea7df9feb7ffe30c04c3040d4ca6c3f789737ffbde7fef39fb6ebbb734afdfde25cd9feb79fe30c04c3040d4c22c3ddf7fffbf7fffffb3ff9e2ebcbe7b6ff77dfffefdfffffec3fa38baf2b1493fddf7fffbf7fffff93631e26901e3b24f77dfffefddfff9ff3fbbfffffbfff3fddf7fffae1ffdff13631e269c1efbf6
  | 75 => 0xffe75e8fffc19ffff27b9fefff871b7fff9d7a27fed7ff98301100000100030ffe75e89ff95ffe7fe7fdfefffefffffff9d7a277e06269ec9ce1d96fe1c4dbfdfafdffffff9ffbffffffffefdd3bf7f7ebf7fffbffffef3ffbeefbb7f7bfdfdfafdffbeff9f5bfffffffffffffffff7a9f7fefbde7dacf6179d54b77afb5
  | 76 => 0xffef7fa9ffb5ffe63c054441004294c3ffbdfea7ecd7ff91f035732dc1afff6ffef7fa9fb35ffe43c054441004ab6c3ffbdfea77e87af9ef9df1d96ff1e5fbffe75ed9ffb7ffe70c04c3040d4c22c3ff9d7b67fede779ef9df1d96ff3ccfbffe75ed9beb7f7e74c0cdb8e7d6fefdbff9d7b66fadfdf9c30130c10353a9b0
  | 77 => 0xffef7ffffff7fffffe7fdfefedcfbff7ffbdffff7f8e7fbeffdf9dd6ff7efffffef7fffbaf7ffef7d8dffdf7dffffdfffbdffe7fedfff9cf0171d14353adb0ffef7ff9ffb7ffe70c04c3040d4ca6c3ffbdffe7fedfff98f0151104012ad30ffef7ff9dfa389a7bff7e775bfdfb7efffbdffe6e8dfdf95f637ff7df5ffff6
  | 78 => 0xffffffafdfc9ebbff3fbbfffffb7df7fffdf7b7fffffffff39fb6ebbffb5afffff7dedfffffffffc27a9baeffa5493fffdf7b7fff7e76ffcfeefffffefdedffff7de8ffffdfffece7e58aaf2e149ffffdf7a3ffff7fffb09e862abca8524ffff7de8fffddfffff27b9fefffa75b7fffdf7a27fe77a6dfc9ee7fbffe9d4db
  | 79 => 0xffffffffdfeb89bfb3f3a775bf97136fffffffff7fae26fecfce9dd6fe5444bffffffff9fff7f6f3d85e7553ffefedfffffffe7feffffdff9ff7fbf7dbfdfafffffff9dfbfe9a7bff7e775bffff7efffffffe6fcffdf95f637ff7dfdffff6ffffffaffffdfffefe7f5cebf2e3ddfffffffebffff7fffbc9ec73afca8564f
  | 80 => 0xfffffffffffffffffffffffffff7ddfffffffffffffffffff9ff7fbfffbfffffffffffffffffffff3fbbfffffb5593fffffffffffffffff3ffbeefbfff7bffffffffffffffffffbff7e7758fdeb6e7fffffffffffffffecfce9dd63e50409ffffffffffffffff7d8dffdf4d7efed3fffffffffffffffbfffdf3efcbeff7f
  | 81 => 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfdbffffffffffffffffffffffffffff5eff
  | _ => 0

private def wordAt (i : Nat) : Nat := fld (wordBlocks (i / 8)) 126 (i % 8)

private def unpack : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wordAt (fld ids 10 0) :: unpack n (ids >>> 10)

private def states (s i : Nat) : List Nat :=
  let packed := fld (packedBlocks s (i / 32)) (stateWidth s) (i % 32)
  unpack (packed &&& 15) (packed >>> 4)

private def index (s : Nat) (ws : List Nat) : Nat :=
  bsr (fun i => fld (hashBlocks s (i / 64)) 32 (i % 64)) (hk ws) 11 0 (proofCount s)

private def check (s : Nat) : Nat → Bool := bar k states proofCount index id [] s

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span2_0 : span (check 2) 22 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span2 : span (check 2) 22 0 = true :=
  span2_0

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span3_0 : span (check 3) 64 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span3_64 : span (check 3) 44 64 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span3 : span (check 3) 108 0 = true :=
  (span_join span3_0 span3_64)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4_0 : span (check 4) 64 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4_64 : span (check 4) 64 64 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4_128 : span (check 4) 64 128 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4_192 : span (check 4) 64 192 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4_256 : span (check 4) 64 256 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4_320 : span (check 4) 64 320 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4_384 : span (check 4) 64 384 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4_448 : span (check 4) 64 448 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4_512 : span (check 4) 64 512 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4_576 : span (check 4) 4 576 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4 : span (check 4) 580 0 = true :=
  (span_join (span_join (span_join span4_0 span4_64) (span_join span4_128 (span_join span4_192 span4_256))) (span_join (span_join span4_320 span4_384) (span_join span4_448 (span_join span4_512 span4_576))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_0 : span (check 5) 64 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_64 : span (check 5) 64 64 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_128 : span (check 5) 64 128 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_192 : span (check 5) 64 192 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_256 : span (check 5) 64 256 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_320 : span (check 5) 64 320 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_384 : span (check 5) 64 384 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_448 : span (check 5) 64 448 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_512 : span (check 5) 64 512 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_576 : span (check 5) 64 576 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_640 : span (check 5) 64 640 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_704 : span (check 5) 64 704 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_768 : span (check 5) 64 768 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_832 : span (check 5) 64 832 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_896 : span (check 5) 64 896 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_960 : span (check 5) 64 960 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_1024 : span (check 5) 64 1024 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_1088 : span (check 5) 64 1088 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_1152 : span (check 5) 52 1152 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5 : span (check 5) 1204 0 = true :=
  (span_join (span_join (span_join (span_join span5_0 span5_64) (span_join span5_128 span5_192)) (span_join (span_join span5_256 span5_320) (span_join span5_384 (span_join span5_448 span5_512)))) (span_join (span_join (span_join span5_576 span5_640) (span_join span5_704 (span_join span5_768 span5_832))) (span_join (span_join span5_896 span5_960) (span_join span5_1024 (span_join span5_1088 span5_1152)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_0 : span (check 6) 64 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_64 : span (check 6) 64 64 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_128 : span (check 6) 64 128 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_192 : span (check 6) 64 192 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_256 : span (check 6) 64 256 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_320 : span (check 6) 64 320 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_384 : span (check 6) 64 384 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_448 : span (check 6) 64 448 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_512 : span (check 6) 64 512 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_576 : span (check 6) 64 576 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_640 : span (check 6) 64 640 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_704 : span (check 6) 3 704 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6 : span (check 6) 707 0 = true :=
  (span_join (span_join (span_join span6_0 (span_join span6_64 span6_128)) (span_join span6_192 (span_join span6_256 span6_320))) (span_join (span_join span6_384 (span_join span6_448 span6_512)) (span_join span6_576 (span_join span6_640 span6_704))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span7_0 : span (check 7) 49 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span7 : span (check 7) 49 0 = true :=
  span7_0

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span8_0 : span (check 8) 1 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span8 : span (check 8) 1 0 = true :=
  span8_0

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < proofCount s, check s i = true := by
  intro i hi
  interval_cases s
  · simp [proofCount] at hi
  · simp [proofCount] at hi
  · exact span_ok span2 i (Nat.zero_le i) (by simpa [proofCount] using hi)
  · exact span_ok span3 i (Nat.zero_le i) (by simpa [proofCount] using hi)
  · exact span_ok span4 i (Nat.zero_le i) (by simpa [proofCount] using hi)
  · exact span_ok span5 i (Nat.zero_le i) (by simpa [proofCount] using hi)
  · exact span_ok span6 i (Nat.zero_le i) (by simpa [proofCount] using hi)
  · exact span_ok span7 i (Nat.zero_le i) (by simpa [proofCount] using hi)
  · exact span_ok span8 i (Nat.zero_le i) (by simpa [proofCount] using hi)

private theorem rootOK : span (fun s => found states proofCount index s inputs) 4 5 = true :=
  by decide +kernel

private theorem exhausted {s : Nat} (hs : s ≤ 8)
    (valid : NatRun (mask k) (goal k) s inputs) : False := by
  have hs5 : 5 ≤ s := by
    have hlen := run_len valid
    change 6 ≤ s + 1 at hlen
    omega
  have root := span_ok rootOK s hs5 (show s < 5 + 4 by omega)
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at root
  exact bar_all (ori := id) (pool := []) (fun h => h) checked s hs _ root.1
    (Run.perm root.2 valid)

theorem lower {bound : Nat} (fit : HasCircuitSize 6 target bound) : 9 ≤ bound := by
  by_contra! tooSmall
  have hnc : ∃ x y, target x ≠ target y := ⟨pt 6 0, pt 6 7, by decide +kernel⟩
  obtain ⟨s, hs, ws, sub, run⟩ := exists_run target hnc bound fit
  let words := ws.map fun g => encL g rows
  have projected : NatRun (mask k) (encL target rows) s words :=
    Run.map (fun g : BFn 6 => encL g rows) (inv' := fun n => n ^^^ mask k)
      (fun g => by rw [masked]; exact encL_inv g rows)
      (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) run
  rw [encodeTarget] at projected
  have wordSub : words.Sublist inputs := by
    rw [← encodeInputs]
    exact sub.map _
  by_cases eq : words = inputs
  · exact exhausted (by omega) (eq ▸ projected)
  · exact properFails words (List.mem_sublists.2 wordSub) eq (required projected)

end Monotone12750Lower

end

-- From .pnp-tools/Monotone12750Entry.lean
section

namespace Monotone12750Control

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[
  ⟨.or, [0, 1]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [4, 5]⟩,
  ⟨.or, [3, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [6, 8]⟩,
  ⟨.and, [2, 9]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [11, 13]⟩
], 14⟩

theorem monotone : Monotone2 circuit := by
  intro gate mem
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 15000000 in
theorem exactTable : ∀ x : Fin 6 → Bool,
    circuit.eval (List.ofFn x) = Monotone12750Lower.target x := by
  decide +kernel

end Monotone12750Control

end

end PEqualNP.Outside.L_meta_12749_aux

open PEqualNP.Outside.L_meta_12749_aux

open PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_12749 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075694 * 2 ^ 32 + 4277067904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075694 * 2 ^ 32 + 4277067904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have budget : 9 ≤ s := Monotone12750Lower.lower h
  exact ⟨Monotone12750Control.circuit, Monotone12750Control.monotone, budget,
    Monotone12750Control.exactTable⟩
