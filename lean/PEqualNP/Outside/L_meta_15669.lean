import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_15669_aux

private def packedWords : List Nat → Nat
  | [] => 0
  | w :: rest => w + (packedWords rest <<< 64)


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

section

namespace Monotone15670Lower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoreTable7402_aux

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4007717088 * 2 ^ 32 + 4007717024)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

private def k : Nat := 62
private def rows : List Nat := [42, 44, 17, 50, 42, 6, 52, 52, 51, 9, 41, 9, 20, 9, 3, 28, 6, 56, 1, 60, 41, 12, 24, 3, 51, 20, 49, 6, 18, 18, 60, 51, 41, 42, 60, 42, 60, 42, 41, 51, 41, 41, 6, 6, 60, 60, 42, 6, 60, 41, 51, 42, 41, 42, 42, 41, 51, 51, 51, 6, 60, 51, 43, 46, 21, 58, 58, 38, 54, 53, 55, 25, 43, 11, 21, 13, 11, 29, 14, 57, 5, 62, 45, 14, 26, 7, 59, 22, 57, 22, 22, 26, 22, 14, 22, 25, 25, 11, 38, 5, 25, 38, 11, 26, 26, 25, 5, 26, 14, 11, 14, 38, 25, 38, 5, 22, 26, 14, 5, 11, 26, 5, 11, 22]
private def inputs : List Nat := [(packedWords [0x679603c185946f04, 0x6c5265b8165bfe1]), (packedWords [0xef6cccaab9814139, 0xdbaf9e67efa535e]), (packedWords [0x9801bc144a2990e2, 0xa6ed42c76af6c79]), (packedWords [0xd0fb737f407aae13, 0x5b17bd3a95efb86]), (packedWords [0x37053094f74a91cc, 0x9190b91dfd2a4f7]), (packedWords [0xf7ff73ffc51a05db, 0x280240146817e])]

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
  | 2 => 1
  | 3 => 8
  | 4 => 155
  | 5 => 822
  | 6 => 739
  | 7 => 48
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
  | 2, 0 => 0x561c38e1
  | 3, 0 => (packedWords [0x1f435f40199eac71, 0x9c67ac487aa9d9c2, 0xbdbe6ee4a3256325, 0xf0a4b276c4668b98])
  | 4, 0 => (packedWords [0x2a2c04900eff892, 0x8672dac07263f6a, 0x11d9558b0c3de9f2, 0x134d5cb01334ee9b, 0x192d3cff149a152a, 0x247cef6a1b0eb667, 0x2814d71024c7fc97, 0x2ac76f2128e411f0, 0x2cbe09e72b0eb647, 0x316fb6622e322457, 0x3278513d31d01392, 0x33d5b6d5337bc0c4, 0x35603c7b348d9135, 0x390b060d36da7117, 0x39de4e45394fca82, 0x3b2963893a96d481, 0x3ba41e613b33cdeb, 0x3c948e283c13db07, 0x41a178aa3d84478f, 0x477c5bd246002db8, 0x4b0f3ca6485cecfe, 0x4c1d65264b8ba09f, 0x4f7cb1734eaba362, 0x5846e87e511d4309, 0x5b0de895591af6e5, 0x5e4e92b55b10059c, 0x6326f14c623f0ec0, 0x67622bc6639ab065, 0x69d6b9ed693d4fa9, 0x6c0289296aaadbf9, 0x6f00e16a6e7a82ae, 0x701058326f2c909f])
  | 4, 1 => (packedWords [0x7285b19d708d84a6, 0x769e6bdf74da057c, 0x78b6b2d978ab2a4d, 0x7a78a5d07a175661, 0x7f51a8e97d7fb0ea, 0x8067cba6802e0e7e, 0x8140e27480e67e89, 0x81cefcd7815e4b16, 0x82f6ff1182ad8a32, 0x85961e7585315436, 0x86becbe986293599, 0x8958c6d5892fc74f, 0x8ae6b10d8a532a24, 0x978479d096d1749c, 0x9d5283f79835442d, 0xa27336c49eac1526, 0xa520bc9fa3e21f37, 0xa77ce74ca6b17997, 0xa9abb3ada8023f82, 0xaa5b50d0a9fde207, 0xab7ff962aae521d2, 0xadf3484facd549cb, 0xaed3c61dae38a5b8, 0xb333042eb229cff8, 0xb5182e3fb4b2e3d1, 0xb7141ba5b70d5abd, 0xb9cbd8d5b7faa057, 0xba943231ba0eb498, 0xc12e07a8bb610f21, 0xc784d961c38532ad, 0xc7e2a422c7ba1172, 0xcdfe524acbee40eb])
  | 4, 2 => (packedWords [0xcfaee7b4cebe0b91, 0xd4e3ab08d237905a, 0xd6ebc21bd4eeca64, 0xe0f0b8b0e0b2ce67, 0xe27a5422e24c0fc5, 0xe49729c1e32f4107, 0xe7292f6ae506725b, 0xe998a5cee88b86d8, 0xed1606f4ebdb36d2, 0xf18db8cbefb78d41, 0xf732e82cf495d5b0, 0xf9423fd8f81dc879, 0xff513dacfb6ab409, 0xffb45364])
  | 5, 0 => (packedWords [0xc6049a00262523, 0xd75dbe00d66a74, 0x12656e10125cb45, 0x2153b3f020c196d, 0x2ae8485021d59d4, 0x37ef9a802e20834, 0x530e97b03e70584, 0x5c6f12805c221a5, 0x6eddeea06cb345a, 0x76264590720cb99, 0x7c742e107c004fa, 0x854d46907daeeb0, 0x88a0a79086b53ee, 0x8c3b90a0895b531, 0x95cdf28093f12fc, 0xade5e580a4ce9e5, 0xb1925f80afd51ba, 0xb3574dd0b343112, 0xb8318e50b771ec4, 0xcc945d60c213df2, 0xd6c911a0d651a55, 0xe24eadf0d6d79d7, 0xeaa4bda0e53af9f, 0xff7a62b0f897f54, 0x11809ae611144dbf, 0x11d9558b11bfb891, 0x12fd804012d02682, 0x13222f6a13200068, 0x134d5cb013232faa, 0x139ac369136b3527, 0x14d1ad9f13d0657a, 0x155601c51507122f])
  | 5, 1 => (packedWords [0x15840ec515835030, 0x1602d25a15af1580, 0x164b20811617f913, 0x1716d70e16d14ccd, 0x17786b221755f73d, 0x17f1187c17973df4, 0x1861b3fb18121dc9, 0x191a5b6618b1e30e, 0x19cc060019780038, 0x1ac5e0961a6906ba, 0x1b40fe8d1affd48a, 0x1bb625571b461de5, 0x1be0bd011be04aed, 0x1d4702371cc1150f, 0x1d54fc151d51252c, 0x1db13c771d6d39d8, 0x1e135e431dd00632, 0x1e8d29191e3b28ad, 0x1eaa20671ea2a3dc, 0x1ed411e01ed2dd56, 0x1fb960381fac682a, 0x1fc84bf91fc04794, 0x1ffec87f1fdb889e, 0x2057830020042c67, 0x20bec97d208cb142, 0x21f9e7e62183cec7, 0x22e69e7f22cf1064, 0x2427d08b23be9de6, 0x24cbb24b2443791c, 0x251fffb324dbe82f, 0x2541aae82528dab5, 0x258c9dba254b6a7e])
  | 5, 2 => (packedWords [0x2707a0c525d0c2b4, 0x2760c613273d2189, 0x27dcc9c9279c9a1a, 0x2829d40227f05e00, 0x292fc5d828592ce0, 0x29f0edf929cee99f, 0x2aa3ccfd2a529f2e, 0x2b2768b52ac76f21, 0x2d7a33212bc1cb81, 0x2dbb1f3c2d88d2ac, 0x2e5dfab42e322457, 0x306d0cfb2f42f17b, 0x30d3541f30ad7dc9, 0x310ef227310a9cd1, 0x319d34093164c734, 0x32743b993261c360, 0x332d36fb3327a7fe, 0x34b06e02339d11a8, 0x362654e23620166c, 0x36891bc236604199, 0x36cb1bd4368cc57e, 0x371adaa036f2ee18, 0x37c472af373837d4, 0x3818b7ab37dabd53, 0x38e007f838778fa0, 0x392f92533903c632, 0x3987f346397fb58d, 0x39f7da7239d87037, 0x3a6c72ab3a0d44d9, 0x3af0f6d03ac8b7c4, 0x3b2963893b06ab1f, 0x3b812e643b3cc920])
  | 5, 3 => (packedWords [0x3c44427a3c0bef6e, 0x3cccf24a3c6f7883, 0x3cf770313cecf840, 0x3dad99273d83fb5c, 0x3e3b63d93e2458cc, 0x3ef3f74d3e6d97f3, 0x3f46e13d3f3c8e70, 0x3f8a81833f6a12a1, 0x4056b2b43fc3c8cf, 0x40fb2cb4407df144, 0x421ddf6e41cb9c4c, 0x4285701742209014, 0x42b4014442ae4dfa, 0x430f2a3c4305c504, 0x435b7333435a903f, 0x436ebc83436c6985, 0x444cef7b440b0e3b, 0x44afa94d447c1c93, 0x45454bb844d9add1, 0x46194cd7458894a4, 0x47911ce9467f4afb, 0x48a0cca64828eaf6, 0x495cab5949310f0c, 0x499d5a7a49988e3c, 0x4ab2187249b2e5c7, 0x4ab671d84ab4e4d1, 0x4b0f3ca64aec6723, 0x4ca55fbb4b997854, 0x4d1874814d0c38a7, 0x4d5956d84d42d9b5, 0x4e2b8e2d4d6fa3e4, 0x4eb9374b4e7f49f6])
  | 5, 4 => (packedWords [0x4f8952c34ed0052b, 0x4fa9bd364f8c03cd, 0x50988b0d5089d01c, 0x514804e4512df217, 0x518520615177aaf8, 0x51d2ceba5197961e, 0x52bd4d96527fd3d6, 0x530bb84e52c04ae1, 0x535babca5327a68c, 0x54182e8653c2fda3, 0x548cf948547c0500, 0x54c0dcde54ba454d, 0x5539d9da54e57a84, 0x5574364f556a6abb, 0x56ad5e6d569f3c89, 0x578a1f4157710fc8, 0x587132fc581fc341, 0x5928459958d29cf5, 0x59f6b7aa5937e763, 0x5bac32fa5aaa1977, 0x5c56308c5bf549c8, 0x5ce9b80a5c662c32, 0x5d077aa45cee1dd6, 0x5d9cc9d95d30c762, 0x5e3730555defa98e, 0x5ebcac175e4cc896, 0x606f62c05ff11db8, 0x60a72f46609ebdbc, 0x60eda59860c0d946, 0x6265acf3622c360a, 0x62b17bbc62928059, 0x630cea1162daa0a9])
  | 5, 5 => (packedWords [0x63cc355d638c7c9f, 0x64518d9364205e31, 0x6594507864786fa6, 0x66f373b466983826, 0x675b96916749206a, 0x67b090b76769dc75, 0x68193af767c9c9c1, 0x6895ac3e6871a86c, 0x692497dc68c57568, 0x696098a9694d84f2, 0x69e125ad69d6b9ed, 0x6a37614e69f79c11, 0x6a44f64c6a429660, 0x6abe8d086aae6f83, 0x6ca6c9146c3d6bba, 0x6e48e2f46cc04b79, 0x6ea786946e5a674d, 0x6ec60f5b6ea98e71, 0x6f240a216ec8756d, 0x6fce6e726fab1aae, 0x700017af6fd89ff6, 0x7115b79770da1c14, 0x71e0b8637115ccf8, 0x727f03c772255ba8, 0x731e96a073063370, 0x73a1b038737d3d78, 0x74a71fc1741cd30a, 0x74c4743474b7157f, 0x757a2995756a4260, 0x76b72743759cdfc7, 0x773c7f797710ed4f, 0x7822b61177a37f0e])
  | 5, 6 => (packedWords [0x78e1d4b378b6b2d9, 0x794642c278ec56a2, 0x79addd48799590c7, 0x7a9b829d79cb9af8, 0x7b393fa57b345aee, 0x7bd725b37b8bb1ec, 0x7caa37017c812f2a, 0x7d2a9e1c7d286bc9, 0x7dcc8f167d2d8846, 0x7e5cd9ff7e0f94ec, 0x7e99ae8f7e7b32d3, 0x7f8dce297f5ccb64, 0x7fbca3c57fad74f9, 0x7ff8d8297fe7c7a9, 0x812d2a3a80c89374, 0x81b173bf814673fc, 0x8242433c821d95e9, 0x82cdba5a82929274, 0x832391f282e99515, 0x842f3d798325c59f, 0x8575961e844dd9aa, 0x86421fc2858d607f, 0x879211a786fe14a4, 0x87e5d7b7879cd694, 0x88e1756588bf39de, 0x89a4924888eb78d7, 0x8a9b4f188a212d26, 0x8aea0bc58ad02817, 0x8b73f8358b37cd98, 0x8c5892d98c40de3a, 0x8e3100ef8dfaf5b8, 0x900d23268fa7d8b8])
  | 5, 7 => (packedWords [0x913e18759137dc17, 0x92013b1491885623, 0x9313faa8927d232c, 0x93315b449323fc62, 0x93744def933b102c, 0x93bde45693bd7942, 0x93d9f3ce93d70ea0, 0x93f5c8e293ebfe6e, 0x952da790947f031f, 0x95623cd19534185b, 0x95c9b6e495b8ac40, 0x96583bd1964f0f1a, 0x96f4516996ba9c28, 0x974fcf029738b1f9, 0x97c0cdc897902aa7, 0x9823c08697dc5285, 0x98c865139847c7bf, 0x999370eb99657c56, 0x9a1b528499ae123e, 0x9a73cfe89a4ba29d, 0x9b2dd51d9b02586b, 0x9bd02b9c9bb7af4a, 0x9cae0c499c4017e7, 0x9cb385799caf0434, 0x9d81c51b9d5283f7, 0x9db661b39dae56c1, 0x9e0945b39df400cd, 0x9e95cda59e60086d, 0x9f02cf239f0070e9, 0x9fb1543e9f85c91f, 0xa06b24b09fb3503e, 0xa0e677d2a0d46462])
  | 5, 8 => (packedWords [0xa1ce64eaa1a78f87, 0xa1f94144a1dbf895, 0xa2a4f22ca22b4726, 0xa2e4cc43a2c1f9c9, 0xa4290a5ba3465464, 0xa576d1eca4559a6c, 0xa6796508a6260212, 0xa68e7a6aa689d341, 0xa6b825daa6a4a148, 0xa6ead193a6d7aad2, 0xa7e16388a7e06996, 0xa8e38623a8b51d91, 0xaa026231a9e9adbe, 0xab6c2b99aa064e59, 0xab7ff962ab71a5e3, 0xac1e3f6bab90e4f9, 0xad3b03eeac9512ae, 0xae11588bad401d9c, 0xae78ecd8ae1dadfa, 0xafef20d6afdb5b4d, 0xb13bdaf6b1345416, 0xb18c820eb1792f86, 0xb1b8c1a0b1b2ad37, 0xb2695ad6b2625b8e, 0xb3324daab2dd8aa9, 0xb38eb34eb374707e, 0xb3ba8996b3b6f004, 0xb3c52cb1b3bf9b29, 0xb3e18127b3d169b8, 0xb4404069b41a14a4, 0xb4a8f444b46f26c0, 0xb4cb3be1b4b2e3d1])
  | 5, 9 => (packedWords [0xb5453e85b4e300cf, 0xb606e10ab60165a3, 0xb6608537b64a2cf8, 0xb6d4a2b8b6cded2e, 0xb6fb4bbfb6f491e0, 0xb71ee776b71e4daf, 0xb7871ef2b759ebb7, 0xb85b33f0b8277d97, 0xb91d83c7b909a5ea, 0xb953d7efb93a6f8a, 0xb98c194db972a18e, 0xba3edbfab9fe7a8f, 0xbafc2decbacc556e, 0xbc1f7c30bb67543e, 0xbd82b495bd5b70ed, 0xbde4f941bd9639fc, 0xbe3d3e78be01f5e6, 0xbe8e39f0be45a7fe, 0xbf95aee0beab7d39, 0xc11e4a2cc03eda0a, 0xc235ce8bc1b9bf2d, 0xc27aaee7c24553d1, 0xc2d669afc28fdabe, 0xc323409dc31426f2, 0xc33b99fcc333e502, 0xc35f49e9c356d6ba, 0xc3b8cf40c390d92a, 0xc46db4b3c3ea44fb, 0xc4ac3f28c47292be, 0xc53891b3c4d88957, 0xc5876bb0c555dfd3, 0xc68ef9d3c636154a])
  | 5, 10 => (packedWords [0xc7a0f6a0c7462644, 0xc8176a01c81357a0, 0xc883555ec87caa14, 0xc909048dc8e772b4, 0xc952b389c93f8ff0, 0xca01d755c95a23cc, 0xcb795b9aca5772f6, 0xcbee40ebcb87f69b, 0xcc34a047cc09541e, 0xcc49e1c3cc4005c2, 0xcd0fdae9cc725401, 0xce28a397cdcd34f1, 0xceebc636ce6f4bb8, 0xcfa0b777cf1eed49, 0xd0213c05cff08343, 0xd06e9914d02d26da, 0xd0be6000d080b984, 0xd1258be9d0c611c2, 0xd25fd3c5d177dad9, 0xd2e3f959d260a70f, 0xd3ccb19fd36692e7, 0xd42f3335d3e307b0, 0xd4d27a2dd4d18a18, 0xd5105bb7d4ed9665, 0xd5e408c6d52e1937, 0xd7bd6639d6f2a9b8, 0xd8326cf8d80c5291, 0xd8754544d85f38e8, 0xd996a980d8a4e42a, 0xdaae83a5d9dee50f, 0xdbdad947db1c0cc8, 0xdc1d15e2dc1ab35e])
  | 5, 11 => (packedWords [0xdc47a35cdc3da35b, 0xdc7c3b7fdc74e7c8, 0xdd7007f1dd42582c, 0xde6156d4dd992120, 0xde7ec82fde73d81a, 0xdf145bcbdeefc245, 0xdf7ae191df36a50f, 0xe0b6bba1e066e23f, 0xe113957de0f0b8b0, 0xe17c0dd5e126c3d2, 0xe244bfc8e1ce4162, 0xe344b138e3159f14, 0xe3a2b0fce39dafa2, 0xe407fb6ae3bb87aa, 0xe4362a48e4111b17, 0xe49729c1e46e00de, 0xe4a45a0de49a1f12, 0xe5321d14e4a879fa, 0xe55875b1e557fba4, 0xe5f90a90e55a3dd7, 0xe65fda89e6255165, 0xe69a4dd9e660ba40, 0xe70bd2d6e6f0ff81, 0xe7d675f7e762c78f, 0xe8abd099e807c647, 0xe971547fe91accd7, 0xe9d10c56e9ceebf3, 0xea3698bfea176745, 0xeacfb92feaaf16a1, 0xeb92cd10eb45f598, 0xec35d46eeb95cb2b, 0xed058908ecfeadd8])
  | 5, 12 => (packedWords [0xee088f74ed4ffbbf, 0xeeca3fd4ee39d3a0, 0xeef802a5eed7405a, 0xef42f8fbef05ba72, 0xf099904bf003d449, 0xf166b5c6f11b1a2a, 0xf245f790f1fe0644, 0xf26e8eedf25e8af1, 0xf2dd14e0f28f6671, 0xf329bf23f2fda767, 0xf59f188ef558293c, 0xf674594bf6623b2d, 0xf6bcb071f6864efa, 0xf7118dc7f6de676d, 0xf7d4b5b1f77796a9, 0xf82ee014f7f36c6d, 0xf8436797f84115ec, 0xf88170a7f84728fd, 0xf933d12ef8cc1e94, 0xfae230a5fad28316, 0xfbacb7b7fb0f76ec, 0xfbf2449bfbed9a0e, 0xfcc6c045fc8cbdd5, 0xfd6efaf8fcdcec76, 0xfe3abc31fdfeee32, 0xfebf05bcfe4628ce, 0xff912bc9ff2cce43])
  | 6, 0 => (packedWords [0x26252300193ece, 0x61371e00389fc1, 0x985b100087e243, 0x128fbe200b81847, 0x19499c90135a6f3, 0x1beff9801a23fb4, 0x3e9389503441950, 0x4cc2bf9049be4f2, 0x56148fd05255c33, 0x5abf96a0599acea, 0x678c6a105c221a5, 0x8178244080d5ab8, 0x88a3779086c04d0, 0x90650ca08bd2618, 0x95cdf28095b86b8, 0x9d492720992ed7d, 0xa5d7f9709e8423e, 0xabb6e5b0a6308a3, 0xb7e82710b760649, 0xc03fa310ba157c7, 0xd71ada40c87f845, 0xe0d9df00da7d7ea, 0x10e27dda1036f369, 0x11a8770011144dbf, 0x124f11f211d9558b, 0x12c9a78212c01e26, 0x13b9995413222f6a, 0x1413edc813df0f3c, 0x147f8baf1426e045, 0x1507352b14891f5a, 0x15beb24a155eadd9, 0x170ea72e16a30947])
  | 6, 1 => (packedWords [0x177c95701756409c, 0x1896eb501804c388, 0x1978003818ff63a8, 0x1a9c16a71986327c, 0x1b5554171b2606cf, 0x1c46789e1b94f382, 0x1c7bdf701c4c298b, 0x1cd366901ca86e4e, 0x1d23fed11d1891f2, 0x1e2f6b7e1e135e43, 0x1e95df5e1e8f28a9, 0x1ed5941d1ec392ba, 0x1f1c51771ef999bc, 0x2044286f1fa8b3a2, 0x20b34f752073755e, 0x2114d79620c7bdb7, 0x21f9e7e6214fda2b, 0x232bde1e22e4ab04, 0x248ff60e23ffdec8, 0x24f2345b24c0f67d, 0x258ec661254b6a7e, 0x26557e1425d0c2b4, 0x272a391026aaa2ef, 0x2858d9af27af6539, 0x292fc5d8286abe0c, 0x29cee99f296f3aa1, 0x2a789fb72a08ec0f, 0x2aa9b55e2a911212, 0x2ae6f7762ab795b8, 0x2b7d50922b3b4b87, 0x2be5bd862bc1cb81, 0x2cba678b2cae534d])
  | 6, 2 => (packedWords [0x2d8c2fe02d0d1dd7, 0x2e9e36ad2de0cd18, 0x2f47b2b82f3d8b0e, 0x30c1b8902fb0c257, 0x312d72e030ce7085, 0x321a78b731e897d6, 0x33267d69321e85c4, 0x338951f03377ff23, 0x33b2af9d33921b50, 0x33c7cc1733b559b4, 0x3429d6dd34199556, 0x349c7060343074f3, 0x3569ce9034b6ac86, 0x35f1219035893234, 0x3641cb1c362654e2, 0x36ead0ae368cc57e, 0x37888db63759a081, 0x37a97af137a673a4, 0x37b8e34f37abe863, 0x38f6398938afd356, 0x39210e6d391a10e1, 0x3979ec2d39505833, 0x3a3b03e239f0c553, 0x3b4dc0c93ad5e545, 0x3beafb633b59083f, 0x3cc8d5553c5d376e, 0x3d17e1853cccf24a, 0x3f38e3263e9a2f6b, 0x412559ec40e034f6, 0x41c4e42f415f5c5c, 0x433e772b424f1f3b, 0x440b0e3b43dfd963])
  | 6, 3 => (packedWords [0x4464b469444cef7b, 0x46b5f5e6448fc244, 0x47871ba946c4ed4e, 0x48555d51480ff86f, 0x49988e3c48e3d382, 0x49d5c29449b0c048, 0x4a7564b94a737f9c, 0x4adfa06c4aaa1723, 0x4c64de134b0f3ca6, 0x4ced707b4cd4531c, 0x4dd7ff2f4d029b1b, 0x4e8e2a4e4de335cb, 0x4ef3f9924edf0217, 0x4f8772de4f6348b9, 0x4faa6b2d4fa07775, 0x5002d36b4fec26b9, 0x51475f8b500643a3, 0x51fdb667517f5470, 0x520dde105208117b, 0x5229c0e95223d50c, 0x52bd4d965291eeea, 0x5309ea3952c53f3e, 0x532e5d4a5322fcba, 0x53940e635388000a, 0x5423629753df78b8, 0x54b2f08b54afd615, 0x55dc09a854ba454d, 0x568f9d2c55fd604f, 0x56d89c2956be7804, 0x58270172573ef194, 0x58d29cf558b760ab, 0x5a720d8f5a00c0f9])
  | 6, 4 => (packedWords [0x5b617e885b50f5a7, 0x5bdc57d95bab8658, 0x5c2fda065bfbf943, 0x5d4f853a5d01290e, 0x5d94a25a5d751a70, 0x5e4cc8965defa98e, 0x5f341a545ef4403d, 0x5fc576e65f95a275, 0x60390ab25ff53209, 0x606f62c06046e3c6, 0x60eefe8960881063, 0x61df9e496139aa0b, 0x624e3a9f622c360a, 0x6265acf362622ff2, 0x629280596268a244, 0x630d80cb630a27f0, 0x631433c56310c0ed, 0x63552c976328c109, 0x64f2a9c664dd561e, 0x6672f1f065f4dc1f, 0x672f4c5366ca6a9e, 0x685d3b4167d9e780, 0x68a087af6883f79e, 0x69020d6f68e85235, 0x6959861d694c3f38, 0x69644e5d696098a9, 0x69957c3b69860f3d, 0x6af1ef416a5c8c70, 0x6d8859c36b776db4, 0x6dc87d976d9025a8, 0x6f15630c6ec60f5b, 0x7045eca470290d42])
  | 6, 5 => (packedWords [0x70e5baaf706962b5, 0x712e1e7f70eed90c, 0x71b4f330713664ad, 0x71df322371cee4d8, 0x72255ba8721f0c3a, 0x7280945b7263974b, 0x731d3b3f72bcc942, 0x746e4da273c265b6, 0x750fafda74ae27b9, 0x7541a1057523a86f, 0x75a338e3754619db, 0x7645bd8175fd6346, 0x77c5d30d76d6a4c5, 0x784c1d1177d3cdd9, 0x790f706378719032, 0x7982a657793b727e, 0x79894a9a79849d30, 0x79e8f0a679da51d4, 0x7a6d1eb27a3013e6, 0x7b1a48597a9b829d, 0x7cbac7527c812f2a, 0x7cf91fbb7cf2e30b, 0x7e60e59c7d0d4fbf, 0x7fa624cb7ea5e0eb, 0x7ff6f7fc7fad74f9, 0x80b36f7d800d2434, 0x823eee698160ca40, 0x82bb57358299c7ed, 0x8354549b83428afc, 0x843e6923842f3d79, 0x84bf18c284656ae9, 0x85076bc084ef4ec6])
  | 6, 6 => (packedWords [0x858581918536c0c5, 0x85e3701a85dcfa3f, 0x861404e086082d25, 0x8664385e861c7fa8, 0x87272dbc86c4e879, 0x889748a487fae1d6, 0x89a49248897bcbf5, 0x8abd2f198a978445, 0x8ae99fca8ae0938e, 0x8b5c82188b44b2b7, 0x8b9cf7918b6e3b5a, 0x8c3d9b1b8babf696, 0x8d40c12c8d25185f, 0x8e029c918deb9d97, 0x8e3e25c58e0bc8f1, 0x8ebc3b968eb6fe60, 0x8f13b4448ee8a669, 0x8fa7d8b88f5bc218, 0x909c6ba1907e8146, 0x90f1c1c490c06286, 0x918dea5e91319bdb, 0x91f1f2ea919323fc, 0x9351d35d92cb1921, 0x93e3717e93d79f77, 0x9463c00c9426a5f2, 0x95e0a0f6947e251f, 0x96ec09969645a252, 0x9762bd229703e546, 0x9871d6b59821b2ab, 0x98c8651398bdb7c9, 0x99657c569914a112, 0x9a3395699a287bc9])
  | 6, 7 => (packedWords [0x9ab0a4e59a6855e0, 0x9ac9de019ab0ce2a, 0x9bd050199b85adc6, 0x9c09abda9bec872f, 0x9d73d83d9c459b75, 0x9e4ea90b9dcaa487, 0x9e5ba4259e592d40, 0x9fa22a7b9ef7101f, 0x9fc5ff1e9fc49b56, 0xa0606928a04e03c5, 0xa0ce9345a066285f, 0xa0e96d23a0e848bf, 0xa1a98be8a0fb0295, 0xa266e43ca1f94144, 0xa369732ca2f367de, 0xa42165eba3dfe59c, 0xa4aec159a464cfff, 0xa538041da51abcc6, 0xa5f88eaba55c67b1, 0xa6d7aad2a6431085, 0xa7e5193ca6fe4905, 0xa8fcb923a802e0be, 0xa9a0d451a982a0fd, 0xa9bbb435a9a75234, 0xaa6f11b9aa1861e8, 0xaa8cb493aa8376f0, 0xab0104ddaafdce11, 0xab9d9e41ab098ebc, 0xad674934aba449eb, 0xae5176cbad9b96cb, 0xb02ab24ab01ed560, 0xb052801ab047d187])
  | 6, 8 => (packedWords [0xb0efd9bdb0bbeca3, 0xb115c84cb10ea6ec, 0xb1a56b46b19ed4a1, 0xb3371ce5b331908b, 0xb374707eb34b5b0e, 0xb3c172e4b3a5cbbe, 0xb3d169b8b3c52cb1, 0xb47e2e25b3d45f09, 0xb4cb5025b4947dce, 0xb5453e85b54150c4, 0xb5da768db5d40bb4, 0xb63fd13cb60165a3, 0xb6be694eb6637a88, 0xb7230f50b71e4daf, 0xb734424cb723994d, 0xb94fb191b8f97e3d, 0xba12c5a7b972a18e, 0xbad00b22bab9c8c5, 0xbb67543ebada6057, 0xbc3c1b20bbf217b2, 0xbd5f26a1bce138d8, 0xbf7137f5bd6bbce1, 0xbfab69ccbf95aee0, 0xc06afc51c042057d, 0xc11e4a2cc0849009, 0xc1541dc1c136de30, 0xc27c02cdc18c9c43, 0xc313cee5c2a830fe, 0xc37019a5c31e1d9a, 0xc49d4a87c423e586, 0xc5d9b5f2c4e5033d, 0xc6b1d6a0c6a276e6])
  | 6, 9 => (packedWords [0xc70ef5a8c6d34dcc, 0xc7462644c72b2e86, 0xc7fc96d4c769200b, 0xc8535475c8176a01, 0xc95a23ccc9567c68, 0xc99f6314c99b92ab, 0xca8800d8c9f83b8a, 0xcadabbd4cacae0cb, 0xcbb2bcd2cb27da05, 0xcc2d00d8cc29d2be, 0xcc9baed2cc8c93d0, 0xcd401990ccae266c, 0xcd7efff8cd57d5f0, 0xceebc636ce28a397, 0xd0e9f764d0119db0, 0xd181be42d106cf1e, 0xd2008a75d18bea21, 0xd2643c5dd25deaaf, 0xd2bdc48bd2a2b0ca, 0xd3122447d2e6eeaa, 0xd3a70d6fd34887ff, 0xd4390093d3bb4d2d, 0xd4d27a2dd4985f72, 0xd5b92012d5519f8a, 0xd65b0b8bd5e4e071, 0xd6ec1f2dd6914938, 0xd7959405d7956bf1, 0xd8394167d7cff523, 0xd8ea270ad874ba79, 0xd9aa36f1d996a980, 0xda21a13bd9e29ac3, 0xda5f10a2da2bcab8])
  | 6, 10 => (packedWords [0xdae4e7c6da8a76b9, 0xdb94a4b4db59561d, 0xdc1da8afdc1b4bc3, 0xdd49c451dcddc774, 0xdd76a439dd7007f1, 0xde0e720edd9c4f08, 0xdf5144e9df392e4c, 0xe113957ddf6dda4e, 0xe1667e3fe1157dad, 0xe1853896e17c0dd5, 0xe1b69f3ee1ac50ef, 0xe246f2d3e22ac39d, 0xe31954c8e2f815cf, 0xe3d51746e3a2b0fc, 0xe4bd9022e4362a48, 0xe5c46641e57f13e4, 0xe6402b99e5e11944, 0xe691dd56e67bafac, 0xe70bd2d6e69a4dd9, 0xe715dee0e710fa10, 0xe74c5dbbe71b78b8, 0xe951233fe85e9850, 0xea805dd7ea407a96, 0xeaea5478ea9ac11a, 0xeb967a6feb2aad66, 0xec3cb39aec28ea7a, 0xed0f7956ed043c9f, 0xed49c24eed449b14, 0xeda535d3ed75689f, 0xef4e0fdfee8d25df, 0xf004841eefb269b1, 0xf166b5c6f0ed19cd])
  | 6, 11 => (packedWords [0xf292feaef188d444, 0xf2e17077f2bd3acf, 0xf30c9851f2e413ae, 0xf47ebf02f34b1ddd, 0xf4c96b89f4c6783e, 0xf5707eb3f56d9b2c, 0xf623947af5ee6634, 0xf784b816f6e284c4, 0xf8939086f86a05ca, 0xf907c2d2f8d27e22, 0xfa34b3ecf9dba988, 0xfaf92149fabce5ff, 0xfb8c9a95fb7d62c5, 0xfd5bd937fc56caa6, 0xfdf0be26fd7d3c69, 0xfea45531fe9716a1, 0xfef20505fec97c12, 0xff2cce43])
  | 7, 0 => (packedWords [0xb8184700262523, 0x90650ca03441950, 0x10e27dda095cdf28, 0x1507352b14891f5a, 0x177c9570155eadd9, 0x20b34f752073755e, 0x2f47b2b82114d796, 0x349c706031e897d6, 0x46b5f5e639f0c553, 0x51fdb6674ced707b, 0x5c2fda06520dde10, 0x6268a24461df9e49, 0x69644e5d6328c109, 0x84ef4ec675fd6346, 0x8fa7d8b88664385e, 0x9c09abda9914a112, 0xbc3c1b20ba12c5a7, 0xc313cee5c2a830fe, 0xcadabbd4c72b2e86, 0xe113957dce28a397, 0xe3a2b0fce246f2d3, 0xe6402b99e57f13e4, 0xf907c2d2f86a05ca, 0xfe9716a1faf92149])
  | 8, 0 => 0x8fa7d8b8
  | _, _ => 0

private def packedBlocks : Nat → Nat → Nat
  | 2, 0 => 0x23a879393
  | 3, 0 => (packedWords [0xb5394879c14e4ed4, 0xf21e4e50148ea006, 0x1394a6e3c8813948, 0xa004e48d4a6a4388, 0x394a6e4387d3948e, 0x96a43879])
  | 4, 0 => (packedWords [0xc1643801b5525205, 0xe50159e643879011, 0xd53946d65c90e1e4, 0x1b54350158f6006, 0xe00755394056798, 0x563c882004e50159, 0x501596a43801b54e, 0x534499643801c94e, 0x1b557d0158f6006d, 0x279800f61c124380, 0x643801e44e520500, 0x39590e00755393e5, 0x3946169b97243881, 0xb54e4bd590e006d5, 0x3c801b54e569b90d, 0x43801b5525015a6e, 0x9590e006a9394816, 0x948163b8d6006d53, 0x6d539590e0068d3, 0xe8013940569a90e0, 0x3801c84e51b590e2, 0x598a007553940564, 0x23d63c801d54e501, 0x4e50158f2004e501, 0x6d53947d63d801d5, 0x90e0073101590dfb, 0x90e0071d39405679])
  | 4, 1 => (packedWords [0x564387e004e5015, 0xc539590e1e755394, 0xb139481643801b55, 0x1d34e501590e007, 0xe006d5394516438, 0x5643801b54e52a59, 0x470590e007393940, 0x5394816799820040, 0x60075539590e006d, 0xe1e705394056438d, 0x65690e006d539590, 0x15a0a4387939405, 0x39235643801d54d1, 0xf44e501596a43801, 0x43801b5405643881, 0x4389e005350159f6, 0x592200755394056, 0x940564389e004e52, 0x55101590e007813, 0x6d54740569d89e0, 0x37edd54e501590e0, 0x590e007b13940564, 0x3c965a8ea006d539, 0x4e501590e0075539, 0x800f61c1643801d8, 0x801a94e52059e643, 0x8f2006d539481643])
  | 4, 2 => (packedWords [0x81643801b5511015, 0xe52058f6006d5394, 0x8539405643879b54, 0x1e94e501590e007, 0xe006d5764e56438, 0xd643801d14e50159, 0x501590e007553946, 0x939481643801d44e, 0xe0040470590e006e, 0x6006b53949969c9e, 0x643801d24e50158f, 0x15801c14e4ed235, 0x49405660801d54e5, 0xae4e520590e00721, 0x5a90e204e5243801, 0x43801de4e4f75002, 0x1590dfb6d5494056, 0x945963e801b54e50, 0x80139590e006d53, 0x6d54540565a90e2, 0x3801b54d120590e0, 0x59ba43801b540564, 0x481643801b55251b, 0x4d1265922006d539, 0x6d539405643801ad, 0x801c84e52058f200, 0x90dfb6d539481643])
  | 4, 3 => (packedWords [0x5643879d14e5015, 0xe470590e13801394, 0x1d54056438d61e4, 0x1d54e4f659e6438, 0xe00735394056438, 0x9643801eb4e50159, 0x501590e007553941, 0x939405643856004e, 0xe0075539590e1e77, 0xa007553940565a90, 0x6006b939435015a4, 0x1590e0077d39405, 0x39405643879874e5, 0x4e501590dfc6d5, 0x16801764e564385a, 0x5890e006d539590e, 0x4590e006e5394816, 0xd4e5643801b55d93, 0x54e51d596a43801a, 0x6d539481643801b, 0x3801d54e50459820, 0x590e006d53947964, 0x1c1643879de4e4ed, 0x525015a767b800f6, 0x6d5394b1643801d5, 0x801c84e501590e00, 0x7edb54e50d405643])
  | 4, 4 => (packedWords [0x5643879cc4e5015, 0xe52858ea006d5394, 0x5139405643801b54, 0x1d55b939590dfb7, 0xe00755393ed6438, 0xd67990e006d52059, 0x48d590e006d53946, 0x53947d63c8013940, 0x6004e501590e006d, 0xe007553948164384, 0x6438b2004e501590, 0x15a4a006d539481, 0x39405643879db4e5, 0xb54e519590e0072d, 0x7a801011c1643801, 0x43801b5531015a76, 0x1590e006b5394816, 0x54e567d90e007550, 0x54e501590e006d57, 0x3801ec4e563b801b, 0x3879c44e5015a6e4, 0x590e1e6353940564, 0x243842004e520])
  | 5, 0 => (packedWords [0x90e006d539404406, 0x90e006d5393f8706, 0x90e006d5924e5016, 0x90e0075539404086, 0x90e006d54d404c46, 0x90e16801b54e5016, 0x90e006d53a404706, 0x90e006d5984e5016, 0xa4e43801b54e5206, 0x90e00765b54e5016, 0x90e17801b54e5016, 0x90e006d539404d76, 0x243801b5561015, 0x90e006a539404336, 0x90e006d539404896, 0x90e00779ae4e5016, 0x90e006c539404706, 0x90e006b539404676, 0x90e00799d54e5016, 0x90e108016e4e4706, 0x90e006a5544e5016, 0x90e006d54f4d1016, 0x90e35801de6d5396, 0x90e006d539480c46, 0x90dfd6d539404706, 0x8f6006d539404336, 0x90e007555b4e5016, 0x90e006d5394046c6, 0x90e006d54e4e5016, 0x90e006d539499016, 0x90e006d5394045f6, 0x90e1e6d539404336])
  | 5, 1 => (packedWords [0x90e007b139404856, 0x8f6006d5544e5016, 0x90e0076db54e5016, 0x90e006d5393f0706, 0x7edb54e5013b4706, 0x90e006d5414e5016, 0x90e0070db54e5016, 0x90e0066d393d8706, 0x90e20801b54e5206, 0x90e00779b54d1016, 0x90e1e6d5544e5016, 0x93243801b54e5016, 0x90e3580139234706, 0x243801f371d395, 0x90e00769b54e5016, 0xa6e438da204e4706, 0x90e006d539404eb6, 0x90e006d53b404706, 0x90e006d539404486, 0x243801d54e5015, 0xa76006d5393d8706, 0x91a006d539404706, 0x90e006d53948d016, 0x90e00779394048d6, 0x90e0067d39404706, 0x25a90e006d5395, 0x90e006d539404216, 0xa6e43801b54e51c6, 0x90e006d5494042b6, 0x90e006b139404706, 0x90e00771b54e5016, 0x90e006e939404336])
  | 5, 2 => (packedWords [0x90e0075539404046, 0x90e0073db54e5016, 0x90e006d539498e46, 0x90e006d539404286, 0x90e006d54d404c16, 0x90e006d532404706, 0x90e1080139404b56, 0x90e006d5394047d6, 0x90e2780139404406, 0x90e006d539404696, 0x2436d539480e55, 0xa4a006d539404496, 0x90e00801d54e5016, 0x90e00721b54e5016, 0x90e006b939404336, 0x90e006b939404686, 0x90e006d539404856, 0x90e0061d394048d6, 0x96e438d6006d5396, 0x90e35801b54e4336, 0x90e006d5394049d6, 0x90e006b9544e5016, 0x98643801d54e5016, 0x90e006d58e4e5016, 0x90e006d5394a5016, 0x90e006bd39404706, 0x90e006d58f4e5016, 0x90e006d539480c16, 0x90e00741a94e5016, 0x90e35801b5551396, 0x90e006d539404596, 0x90e006d539404d66])
  | 5, 3 => (packedWords [0x90e006d539480e56, 0x90e00711b54e5016, 0x90e08801d54e5016, 0x8f236801b54e5016, 0xa76006d554404c16, 0x90dfb6b939404706, 0x90e006d539404526, 0x90e006d539404e76, 0x90e006d54b4e5016, 0x8e6006d539404706, 0x92a006d539404706, 0xa36006d539404706, 0x90e006d5394046d6, 0x90e006d539404386, 0x90e16801544e5016, 0x90e006d534404336, 0x90e2780139499016, 0x90e006ad39404706, 0x90e006d55b4e5186, 0x90e006d58d4e5016, 0x90e0077939404906, 0x90e006d5544d1016, 0x90e006d5394047c6, 0xa6e43881de4e5016, 0x90e006a539404406, 0xa0e43801b54e5206, 0x90e006d539404456, 0x90e00709b54e5016, 0x90e006d5394045a6, 0x90e006d56e4e4b56, 0x9e643801b5404706, 0x90dfb779b54e5016])
  | 5, 4 => (packedWords [0x90e006d5393d8706, 0x8f6006d5394043f6, 0x95e43801b54e5016, 0x90e006d53945cf66, 0x8f6006d539404406, 0x90e006d5394042d6, 0x90e006d539498e66, 0x90e006d539418706, 0x90e006d539404516, 0x90e0075539404706, 0x97243801b54e5016, 0x90e1e6d539404406, 0x9ee43801cc4e5016, 0x96a43801b54e4706, 0x243801b54e5185, 0x90e00779393b48d6, 0xa4a006d539404706, 0x90e006a539499016, 0x922006d539404336, 0x90e006d539404796, 0x243801b5525015, 0x8f2006d539499016, 0x90e006d539404466, 0x90e006d58c4e5016, 0x90e006d5394802b6, 0x8f6006d539499016, 0x90e00755b54e5206, 0x90e006d537499016, 0xa6e43801b54e5206, 0x90e006d5404e5016, 0x9a243801b54e5206, 0x23180139234705])
  | 5, 5 => (packedWords [0x90e1e6d539499016, 0x90e006d539480676, 0x90e006d539404d06, 0x90e0072139404336, 0x90e006d539404ae6, 0x90e006b539404706, 0x90e00731394048d6, 0x90e006d539404656, 0x90e006d539404636, 0x982006b939404706, 0x9da43801b5551016, 0x90e006cd39404706, 0x90e006d539404b36, 0x90e006b939404406, 0x90e006d53946d016, 0x9ee6080139404706, 0x90dfb6d539404336, 0x90dfb6d539404686, 0x2438d6204e4705, 0x90e006d539410706, 0x90e006d539404e86, 0x90e006d5554e5016, 0x90e35801b54e4406, 0x90e0f80139404706, 0x90e006d539480086, 0x90e00755394041f6, 0xa767b98600404706, 0x90e28801b54e5016, 0x90dfb6d5544e5016, 0x243801c74e5015, 0x90e006d5393c8336, 0x90e0075539481016])
  | 5, 6 => (packedWords [0x90e006d5393d4706, 0x90e007cdd54e5016, 0x90e006f939404706, 0x90e006d5394042f6, 0x90e1e779394048d6, 0x90e2480139404706, 0xa027990e006d5016, 0x98200779b54e5016, 0x90e006d539404626, 0x90e006d539469016, 0x90e007557f4e5016, 0x90e006d539404576, 0x90e35882004e4706, 0xa6e43801ad4e5266, 0x90e006d534404406, 0x90e00721934e5016, 0x90e006d539404646, 0x90e00799b54e5206, 0x90e006d53944d016, 0x90e006b939499016, 0x90e006d55b4e5206, 0x90e006d539460706, 0x90e29801b54e5016, 0x90e0071d39404266, 0x90e006d5394044b6, 0x90e006e139404706, 0x90e00729b54e5016, 0x90e35801b54e5266, 0x90e006d539404416, 0x90e006d5894e5016, 0x90e00719b54e5016, 0x90e006d539489016])
  | 5, 7 => (packedWords [0x90e20801de4e5016, 0x90e1080139404706, 0x243881874e5015, 0x90e006d5393e0706, 0x90e0075539404126, 0x90e007559b4e5016, 0x90e006d549404706, 0x90dfe6d539404706, 0x90e006d539404b16, 0x8e2006d539404706, 0x90e006d539404ec6, 0x90e006d534499016, 0x90e006d5394043e6, 0xa7643801d54e5016, 0x90e006d5394047b6, 0x90e006d5393d8586, 0x90e006d53946c336, 0x90e0d80139404706, 0x90e20801874e5016, 0x90e006d539404366, 0x90e006d5834e5016, 0x243801b54e5205, 0x90e007b5e44e5016, 0x90e00771ae4e5016, 0x20075539404a95, 0x90e006e539404336, 0x90e0c80139404706, 0x90e0075539480336, 0x90e006d539404ab6, 0x90e006b5393b4706, 0x90e006d539404436, 0x90e006d539480046])
  | 5, 8 => (packedWords [0x9723c801b54e5016, 0x90e007554a4e5016, 0x90e006d5484e5016, 0x90e006d5434e5016, 0xa6e43801b54e50d6, 0x982006d539404336, 0x90e006d57a4e5016, 0x90e00801b54e5206, 0x8c2006d539404406, 0xa2a43801b54e4706, 0x90e006d539428706, 0x90e00779394048c6, 0x90e0071d39404706, 0x90e006d56e4e4706, 0x90e006d5794e5016, 0x90e006d539404b06, 0x982006d5544e5016, 0x90e006d539404ea6, 0x90e0072139404406, 0x90e006c139404706, 0x98643801b54e5206, 0x90e006d5934e51b6, 0x90e006d5393ec706, 0x90e006d5544e4fe6, 0xa6e43881b54e5266, 0x90e006d539404d26, 0x90e006d5514e5016, 0x90e2d801b54e5016, 0xa7a43801b54e5016, 0x90e006d539404326, 0x90e08801b54e5206, 0x90dfb6d539404406])
  | 5, 9 => (packedWords [0x90e006d539404726, 0x90e006d5424e5016, 0x90e006d539404af6, 0x90e006d539491016, 0x90e006d5764e4af6, 0x90dfa6d539404706, 0x90e006a539404636, 0x90e35801b5635396, 0x90e006d539400706, 0x90e006d539404976, 0x90dfd6d5544e5016, 0x9e643801ae404706, 0x90e006d5394043a6, 0x90e006d539404866, 0x90e006d5785b9396, 0x8f6006b539404706, 0x90e006d5394042b6, 0x90e006d539480c56, 0x90e00755b54e5016, 0x9ee43801393d8706, 0x90e1e6b539404706, 0x90e006d539404676, 0x90e006d5394045b6, 0x90e006d5394049e6, 0x90dfb6d539499016, 0x90e006d539404426, 0x90e006d539404b56, 0x90e006d539480706, 0x90e006d539445016, 0x90e006d539404376, 0x90e00755c04e5016, 0x90e00711394048d6])
  | 5, 10 => (packedWords [0x90e1880139404706, 0x9e643801de6d5016, 0x90e006d5393fc706, 0x90e00779b54e4f66, 0x90e0075539404a56, 0x90e007cdc74e5016, 0xa3a006d539404706, 0x90e00635394048d6, 0x90e20801cc4e5016, 0x243801bf6d5015, 0x90e2f801b54e5016, 0x90e00779d54e5016, 0x90e006d539404dd6, 0x902006d539404706, 0x99e43801d54e5016, 0x90e006d5534e5016, 0x90e006d53946c406, 0x96a43801de6d5396, 0xa7643801b5529016, 0x90e0079139404706, 0x243801ec4e5015, 0x90e00779394048f6, 0x90e006d5394046e6, 0x96a43801b54e5016, 0xa4a00779b54e5016, 0x9e64380101234706, 0x90e006d533404706, 0x90e006d5394042c6, 0x90e007b9de4e5016, 0x90e0069d39404706, 0x90e0069139404706, 0x90e006d539404cc6])
  | 5, 11 => (packedWords [0x90e00755874e5016, 0x90e006d539404276, 0x90e006d539404e16, 0x90e00705b54e5016, 0x97243801394048d6, 0x9ce436d539404706, 0x982006d539404406, 0x96a43801b561d396, 0x90e35801ad4e4706, 0x90e006d539449016, 0x90e006d56a4e4706, 0x90e006d5464e5016, 0x90e006d539404b76, 0x90e007b5b54e5016, 0xa0a43801b54e5016, 0x90e007d9b54e5016, 0x243801f06d5395, 0x90e00755394045e6, 0x90e006d5524e5016, 0xa6e43801b55f1396, 0x90e006d563404706, 0x90e00779ad4e5016, 0x90e006d539481206, 0x90e006d539404256, 0x90e006b534404706, 0x90e007cdb54e5206, 0x90e006d539404886, 0x9e643801b5404336, 0x90e0068d39404706, 0x90e006d5393d8336, 0x90e006d57f4e5206, 0x90e0075db54e5016])
  | 5, 12 => (packedWords [0x243801b55d9395, 0x982006d539499016, 0x90e006d5393cc706, 0x9e643801b5551016, 0x90e006d539418336, 0x90e006d5504e5016, 0x90e006d5544e4f66, 0x90e0075539404336, 0x90e006d539404506, 0x9de43801d54e5016, 0x90e006d5724e5016, 0x90e006d539404496, 0x90e006d539404666, 0x90e006d5394043d6, 0x90e006d535404706, 0x90e00755544e5016, 0xa4a006d539404336, 0x9e643801011c01d6, 0x90e006d539480126, 0x90e006d539404da6, 0x90e006d59b4e5206, 0x90e2f89e004e5016, 0x90df86d539404336, 0x96643801b54e5016, 0x90e006d539404266, 0xa4a006d5544e5016, 0x9fe43801d54e5016, 0x90e006d5394810c6, 0x90e0075539404ed6, 0x90e007b139404706, 0x2006a5393b4705, 0x90e006d539461016])
  | 5, 13 => (packedWords [0x90e006d56b4e4706, 0x90e006d53943d016, 0xa7643801b54e5206, 0x90e10801de4e5016, 0x243801e6755015, 0x90e006d5864e5016, 0xa49fb6d539404706, 0x90e006d539471016, 0x9ea4380139404706, 0x90e00755934e5016, 0x90e006d539404876, 0x2006d539480a95, 0x90e006d57b4e5206, 0x90e006b539404336, 0x90e0071db54e5016, 0x8f6006d539404676, 0x90e006d54a4e5206, 0x90e006d539404ad6, 0x90e006d539404be6, 0x90e006d539404d16, 0x90e006b5544e5016, 0x90e006d539410336, 0x28790e006d5015, 0x90e006d5394049a6, 0x90e00755704e5016, 0x90e006d53e404706, 0x90e0068139404706, 0x90e006b9393ec706, 0x90a006d539404706, 0x90e006d539404616, 0x90e006d539404706, 0x90e006d5764e4706])
  | 5, 14 => (packedWords [0x90e006d53945d016, 0x90e00779b55b9396, 0x90e006d539404736, 0x90e006d56e4d0706, 0x90e006d539404536, 0x90e36801d54e5016, 0x90e006d5393dc706, 0x801c16d539404ed6, 0x90e00779b54e4fb6, 0x90e006a139404706, 0x90e006d5393f4706, 0x90e006d565404706, 0xa762780139404706, 0x92643801d54e5016, 0x2437e5b54e5015, 0x90e20801c44e5016, 0x90e006d539404756, 0xa6e43801b54e4896, 0x90e1680139404af6, 0x90e006d5393e8706, 0x90e1080139404336, 0x9e643801b5404406, 0x90e006d5393d8406, 0x90e006d539404396, 0x90e0075539404146, 0x90e006d549404336, 0x9ee43801d54e5016, 0x2438da1e4e4705, 0x90e0075539404a96, 0x27998600404705, 0x90e208018d4e5016, 0x8de006d539404706])
  | 5, 15 => (packedWords [0x90e10801544e5016, 0xa6e43801b54e5266, 0x90e006d539404b86, 0x90e1e5fd39404706, 0x90e0075539404406, 0x90e006d5784e5016, 0xa2243801b5551016, 0x90e006ad39499016, 0x90e006d5394ad016, 0x9e64388200404706, 0x90e0075539404066, 0x9ee43801012a8706, 0xa4a006d539404406, 0x90e007c1b54e5206, 0x90e006d539404ba6, 0x9be43801b54e5016, 0x23c801b54e5015, 0x90e0069539404706, 0x90e006d539480a56, 0x90e006d5394049f6, 0x90e006d539404826, 0x90e006f539404706, 0x90e006d539404716, 0x90e006d539404956, 0x9e643801b5499016, 0x90e006c939404706, 0x90e006d539498f66, 0x97243882004e5016, 0x90e006d534404676, 0x90e1e66d39404706, 0x90e2780139404d16, 0x90e00779b54e5206])
  | 5, 16 => (packedWords [0x99e43801b54e5206, 0x90e006d593525016, 0x90e006d539404bd6, 0x90e006d539481016, 0x90e006d5694e5016, 0x90e0075539404156, 0xa2643801b54e5266, 0x90e0075539499016, 0x90e00755394048d6, 0x90e006d56e4e4336, 0x90e006d531404706, 0xa4a006d539499016, 0x90e006d5393ec336, 0x94e43801b54e5016, 0x90e2b801b54e5016, 0x90e006d5393ec686, 0x90e006b539404406, 0x90e006d56e551396, 0x90e2780139404706, 0x90e006d5394043c6, 0xa0243801b54e5016, 0x90e00791de4e5016, 0x90e006d5544e4fb6, 0xa6e43801b54e4856, 0x90e006d5394044d6, 0x90e00775b54e5016, 0x801b566d39435016, 0x90e006d539404776, 0x90e006d539495016, 0x243879de4e5015, 0x982006d5393d4706, 0x90dfb6d5393ec706])
  | 5, 17 => (packedWords [0xa76006d539404cd6, 0x90e006d539431016, 0x9de43801b5535016, 0x90dfb6d539404326, 0xa76006d539435016, 0x982006d539404576, 0x90e006b539499016, 0x90e00715b54e5016, 0x90e12801b54e5016, 0x90e006d5394046a6, 0x94643801d54e5016, 0x90e00721394042b6, 0x90e0076dad4e5016, 0x90e1e801de4e5016, 0x90e1b6d539404706, 0x90e006d5494e5016, 0x90e006d56c4e4706, 0x90e006e139404406, 0x90e006d539404586, 0x90e006d539404836, 0x9e643801c46d5016, 0x90e006d539404786, 0x90e00705394048d6, 0x90e006a539404706, 0x90e006d539480336, 0x27b98200404705, 0x90e00755394047f6, 0x90e006d57b4e5016, 0x9de43801b54e5206, 0x8f2006d539404706, 0x24385a004e5015, 0x90e1080139404406])
  | 5, 18 => (packedWords [0x8c6006d539404406, 0x90e006d5394042a6, 0x90e006d54a4e5016, 0x90e006d549404406, 0x90e007b1b54e5016, 0x90e006d5544e5206, 0x90e00755394041d6, 0x90e006d5394046f6, 0x90e006d539404946, 0x98e43801d54e5016, 0x8f6006d539404706, 0xa0a43801394048d6, 0x90e006d537404706, 0x90e17842004e5016, 0x90e006d539404846, 0x90e00755574e5016, 0x90e006d5774e5016, 0x982006d5394047b6, 0xa6e5c90e006d5396, 0x90e006d539404226, 0x90e1e6d539404706, 0x90e006d5394044e6, 0x90e006d539480ed6, 0x90e006d5394808e6, 0x90e0079139404336, 0x90e006d539404246, 0x90e006d539404996, 0x243801e66d5205, 0x90e00791544e5016, 0x90e2a801b54e5016, 0x90e016d539404706, 0x90e006d5844e5016])
  | 5, 19 => (packedWords [0x90e1080139499016, 0x90e046d539404706, 0x90e0075539404916, 0x90e006d5394047a6, 0x90e006d5934e5206, 0x90e006d539404cd6, 0xa6e3d801b54e5266, 0x90e006d539435016, 0xa0643801b54e5016, 0x90e006d539408706, 0x20066d393d8705, 0x90e006d5394043b6, 0x90e006d539404d36, 0x90e1e77939404706, 0x90e14801de4e5016, 0x90e006d539404b66, 0x90e006d5394045d6, 0x90e006d56e4e4406, 0x97243801d54e5016, 0x90e006d539404746, 0xa1643801d54e5016, 0x90e006d539420706, 0x90e006e939404706, 0x90e006d5704e5206, 0x90e006d538404706, 0x90e006d58a4e5016, 0x90e006d58b4e5016, 0x90e006d5393ec406, 0xa1a43801de4e5016, 0x97243801394048f6, 0x90db564d39404af6, 0x90e006d53946c2b6])
  | 5, 20 => (packedWords [0x90e006b939404706, 0x90e0069939404706, 0x90e006d539404556, 0x90e006d54d4e5016, 0x90e0068d39404336, 0x90e006d54f4e5016, 0xa4e43801d54e5016, 0x90e006d5394046b6, 0x9ee43801b5535016, 0x90e00701b54e5016, 0x90e35801b54e4706, 0xa76006d52f404706, 0x90e006dd39404706, 0xa72006d539404706, 0x90e006d5854e5016, 0x243801c84e5015, 0x90e1680139404706, 0x906006d539404706, 0x90e006d539404566, 0x90e36801b54e5206, 0x90e006d56e4e5266, 0x92643801b54e5206, 0x90e006c139499016, 0x90e00779b54e5016, 0x90e006d539498fb6, 0x90e006d534404706, 0x90e0075539404c46, 0x90e006d5764e5016, 0x90e006d539480146, 0x90e006d939404706, 0x90e006d539404b26, 0x9ee43801b54e5206])
  | 5, 21 => (packedWords [0x9ae43801b5404706, 0x90e006d5684e5016, 0x90e006d539480a96, 0x90e006d539404986, 0x90e1e6d5393b4706, 0x243801574e5015, 0x90e006d539404d96, 0x90e006d539480406, 0x90e006d539404236, 0x90e006d53949d016, 0x90e00779b54e4fa6, 0x90e20801d54e5016, 0x90e006d539404546, 0x90e006d5874e5016, 0x90e006d539480066, 0x2438015b4e5185, 0x90e006d5674e5016, 0x90e006d539404306, 0x97a006d539404706, 0x90e0068539404706, 0xa6e43801b54d1266, 0x90e006d53948cfb6, 0x90e007319b4e5016, 0x90e006d539404b46, 0x90e006d539441016, 0x90e006d5394045e6, 0x90e0079139404406, 0x90e006d139404706, 0x90e006d539404296, 0x90e006d539480156, 0x90e006d539499206, 0x922006d539404706])
  | 5, 22 => (packedWords [0x243879b54e5265, 0x90e006d5394045c6, 0x90e006d539404346, 0x90e006d5394808d6, 0x90e006d539404446, 0x90e006d5394044a6, 0x936006d539404706, 0x24375539404e55, 0x90e006d539404966, 0x90e006d536404706, 0x90e006d539404b96, 0x90e006d539404606, 0x90e006d539404cf6, 0x90e0079139404896, 0xa4a1080139404706, 0x96e43801b54e5016, 0x243801b54e51b5, 0x90e006d539404336, 0x90e006d539404766, 0x90e006d539404686, 0x902006d539499016, 0x9e66190e00404706, 0x90e0079139499016, 0x90e0072139404706, 0x90e006d5394044c6, 0x90e006d5544e5016, 0x90e006d5394042e6, 0x90e006d576551396, 0x90e0075539404c16, 0x90e006d57c4e5016, 0x90e006d539404356, 0x243801d54e5205])
  | 5, 23 => (packedWords [0x90e0075539404e56, 0x90e0078d39404706, 0x90e20801c14e5016, 0x90e1e6d539404996, 0x90e006d539404476, 0x90e27801de4e5016, 0x243801f3755395, 0x90e0a6d539404706, 0x9820066d39404706, 0x9fe43801b54e5016, 0x90e33801b54e4706, 0x90e006d539404d56, 0x90e006d5343b4706, 0x90dfb6d539404706, 0x90e006d5614e5016, 0x90e3c801b54e5016, 0xa0a43882004e5016, 0x90e006d539404df6, 0x90e006d5604e5016, 0x90e007d1b54e5016, 0x90e006d539404d46, 0x90e006d5393c8706, 0x90e006d539404ce6, 0x801b564d39435016, 0x94643801b54e5206, 0x9fa43801b54e5016, 0x90e006d539404936, 0x90e006fdb54e5016, 0xa0e43801d54e5016, 0x90e006d539480856, 0x90e1e6d5394045d6, 0x90e006d5393d0706])
  | 5, 24 => (packedWords [0x90e006d5394807f6, 0x90e006d5394044f6, 0x90e3687939404706, 0x90e006d5394b5016, 0xa4a006d56e4e4706, 0x99643801b54e5266, 0x90e006d539404e96, 0x90e006d5394602f6, 0x90e006d5394801d6, 0x90e006d539404d86, 0x90e006d539439016, 0x90e00731b54e5016, 0xa6e43801b54e5116, 0x90e00779a94e5016, 0x9ee4387939404706, 0x90e00779394049c6, 0x90e006d539404e06, 0x9c243801b54e5016, 0x90e006c9544e5016, 0x8f200779b54e5016, 0x2438015b4e5205, 0x8f600779b54e5016, 0x8f6006d534404706, 0x90e006d539455016, 0x90e006d5744e5266, 0x912006d539404706, 0x8fe006d539404706, 0x90e006d539404cb6, 0x90e00755394042b6, 0x90e00755d54e5016, 0x90e1e779b54e5016, 0xa6e43801d54e5016])
  | 5, 25 => (packedWords [0x90e006d539404316, 0x90e2780139404336, 0x90e006d53946c706, 0x90dff6d539404706, 0xa6e43801e44e4706, 0x90e00741b54e5016, 0x90e27801544e5016, 0x90e007b139499016, 0x90e006d539485016, 0x90e006e539404706, 0x90e0075539480706, 0x90e006d53e404406, 0x97243801b54e5206, 0xa1643801b54e5206, 0x90e0068939404706, 0x95243801b54e5016, 0x90e006d559404706, 0x90e00759b54e5016, 0xa4a006d539404b56, 0x90e006d539404a06, 0x982006d539404706, 0x90e006d5394043f6])
  | 6, 0 => (packedWords [0x801b556d39499017, 0x801b54e501101a43, 0x6a53940470700243, 0x4049c1c1e43801b5, 0x32470690e006d539, 0x1c1c0090e006d501, 0x690e006d539404a4, 0x90e00799b540470, 0x779b54e501049c0, 0xf4e50123470790e0, 0x566d39405e438017, 0x940470790e00779b, 0x29e438f6006d53, 0x790e006d5394047, 0x43801b564d394047, 0x6d5944e5011c1e, 0x6d53940470790e, 0x994e5011c1e9490e, 0x139870790e006d5, 0x11c1e43801b54e5, 0x1e79ca43801b54e5, 0xe43801b555139404, 0x643801de6d539405, 0xe006d539404896a7, 0xd39404e51c180090, 0x5012347070024356, 0x5011c1e438019b4e, 0x9017a9643801b54e, 0x1ea190e006d53949, 0xe0b801b54e5011c, 0x1cc6d5394047079, 0xd5704e5011c1e438, 0xd539404a9690e006, 0xe526405800801de6, 0x440700243801b54, 0x81a6190e006d5394, 0x243801b5404700])
  | 6, 1 => (packedWords [0x90e006d539404707, 0x801a94e5011c1e8f, 0x5593940470799e43, 0x481010cde43801b5, 0x40470790e006d539, 0xcde9990e006d539, 0x790e007cdb54e501, 0x3801e44e5011fc70, 0x6d53947101101e4, 0x6d53940440790e0, 0x356d391c1a438220, 0x940433700243801f, 0x9405e43801b55fd3, 0x1790e007cdb55513, 0x43801b55fd544e50, 0x36801b54e5011c1e, 0x6d539404eb690e, 0xb54e5011c1c0090e, 0xd54e501592643801, 0x811c1c0000243801, 0x70790e006d539404, 0xe43801b54e509404, 0x643801b54e526405, 0xe00779394048d698, 0x5ae4e5011c1c0090, 0x53940470790e006d, 0x433049e43801b54e, 0x501690e006d53940, 0xdc0090e30801b54e, 0xe006d59b4e5010c, 0x1b54e5011c01479, 0x1b54e5011c1e438, 0xe5012a47079ee438, 0xe526405e43801b54, 0x412790e08801b54, 0x5e43801b5551394, 0x90e006d59b551394])
  | 6, 2 => (packedWords [0x801b564139404707, 0x6d53940470101e43, 0x4e5012ec70790e00, 0x4e5010cde43801b5, 0x404687a7643801b5, 0x215a9d90e006d539, 0x700243801b54e501, 0x3801b54e5011c006, 0x779b56d539405e4, 0x6d5544e501790e0, 0x1310a51c1e9d90e0, 0x11c01d790e006d50, 0x90cda438019b4e50, 0x7002006d539404a, 0x43801b55cd394047, 0x43801ad4e5011c1e, 0xef6d539499017a6e, 0xf86d539405a43801, 0x122470700243801, 0x70045e43801b54e5, 0x1690e006d539404, 0xc0090e00711b54e5, 0xe006d55e4e5011c1, 0xdfb6d53940470790, 0xdb54e501395a9d90, 0x9394043370028390, 0x5012a5a43801b552, 0x4707002006d5544e, 0x5e43801b55b53940, 0xe006d539404b82a, 0xe006d5394047079, 0x1b54e5011c1e7c9, 0xe5011c015790e358, 0x99011c1e43801b54, 0x4a5790e006d5394, 0xc1e43801de6d5394, 0x90e006d5394048d1])
  | 6, 3 => (packedWords [0x801f26d539404707, 0x801b563539405a43, 0x6d53940470700243, 0x404c21c1e9690e00, 0x4e501790e006d539, 0x1c1e43801de779b5, 0x790e006d53940492, 0x790e00779b54e501, 0x2801b54e5011c1e6, 0x3801b540470690e2, 0x7cdb54e58009e64, 0x93d87060028390e0, 0x10a980090e006d53, 0x700243801e66d50, 0x9890e006d5394047, 0x6d59c4e5011c1e, 0x934e5013b470790e, 0x39404ca1c1e006d5, 0x13ac70790e006d5, 0x11c1a43801b54e5, 0x70700243801d54e5, 0xa43801b54e50131c, 0x25c90e006d539405, 0x643801b54e501600, 0x9394048d1c1c00a1, 0x53940440790e0077, 0xd39405e43801f36d, 0xc70790e00779b561, 0x5e43801b54e50130, 0xe006d5544e50133, 0x1b54e5011c01779, 0x1b54e5011c1e438, 0xd53940470690e308, 0xe5011c1800a4a006, 0x4707002438817f4, 0x1e6a90e006d5394, 0x90e006d57f4e5011])
  | 6, 4 => (packedWords [0x801b560939404707, 0x6d59a4e5011c1e43, 0x6d53940470690e00, 0x4e5011c1c0090df1, 0x3d870790e006edb5, 0x1c1e6190e006d539, 0x694643801b54e501, 0x90df36d53939470, 0x6d539404901c1c0, 0x54e50121470790e0, 0x94047003de43801b, 0x11fc70790e006d53, 0x11c1e43801b54e50, 0x7a6e43881b54e50, 0x43882005fd394047, 0x6d53940440049e, 0x6d53940470790e, 0x5b4e5010bde8c90e, 0x3940440790e006d5, 0xa50cde43801b566d, 0x70790e006d539404, 0xe9da4e006d539404, 0xe007cdb54e526405, 0x1f16d53940470790, 0x1b54e5011c1e4380, 0x53940470790e007e, 0x470075e4380e006d, 0x470790e006d53940, 0x1e4e90e006d53940, 0xe00711b54e5011c, 0x860066d394047069, 0xd57f4e526405c009, 0xb53940470690e006, 0xe501295c0090e006, 0x463690e006d5544, 0xcdc0090e006d5394, 0x90e00779b54e5010])
  | 6, 5 => (packedWords [0x90e006d539404707, 0x801de6d539405e69, 0x4e50122c7079de43, 0x4e501101e43801b5, 0x404337a7643801b5, 0x1c1e6790e006d539, 0x6a5e43801b54e501, 0xa1243801b54e501, 0x8019b4e5011c1c0, 0x54e4ed23470790e2, 0x54e5011c1e43801b, 0x940470790e26801b, 0x9405e43801b56353, 0x690e00779b55513, 0x90e0056d394047, 0x43801b555139405c, 0xe86d53940470799e, 0x954e5011c1e43801, 0x12a440690e006d5, 0xa91c1800801b54e5, 0x12700200799b5404, 0xe43801b54e526404, 0xe006d59b4e526405, 0xe006d5394042f690, 0x9b54e5013b5c0090, 0x50138870790e0077, 0x9b5405a43801b54e, 0x901700243801e677, 0x1e9d90e006d53949, 0x7243801b54e5011c, 0xe006d5394047079, 0x79b564d39405e859, 0xd53940470790e007, 0xe526055a43801ea6, 0x988d600243801b54, 0x580090e006d5394, 0x24388200779394])
  | 6, 6 => (packedWords [0x90e1080139404706, 0x801b54e5011c1800, 0x4e526404a9600231, 0x4e5011c1c00801b5, 0x404677a4e43801b5, 0x405e9b90e006d539, 0x790e00779b55c139, 0x590e006d53940470, 0x3801de6d501081a7, 0xe6d5564e50170024, 0x54e5011eda43801d, 0x940470700243801b, 0x30cde6090e006d53, 0x3790e006d5394043, 0x7790e006d5394043, 0x43801b54e5011c1e, 0x6d539404407a2e, 0x394048d1c1e4390e, 0xb54e520590e1e6d5, 0x10cdc0000243801, 0x8d790e006d5544e5, 0xe43801b54e501264, 0xe006d539404c41c1, 0xe006d5544e501790, 0x539404ef1c1e7790, 0x5011c063790e006d, 0xd39405e43801b54e, 0x470790e006d58d5f, 0x5e9d801b54e50130, 0xe006d5545513940, 0xda00779b54e50179, 0xd57c55139405e438, 0xbd3940470790e006, 0x4a51c1e43801b55, 0x440790db564d394, 0xcde43801b5535394, 0x90e006d539404ed0])
  | 6, 7 => (packedWords [0x90e006d539404707, 0x6d5394047001de84, 0x6d59b4e501790e00, 0x4e5011c1e43801c4, 0x2b070790e20801b5, 0x405a43801b54e501, 0x60028390e006d539, 0x90e00799b540433, 0x6d5394990d405c0, 0x555139404ed790e0, 0x55b9391c1a43801b, 0x129440700243801b, 0x1051e43801b54e50, 0x790e00779b54e50, 0x43801b54e5344047, 0x43801f36d539099a, 0x779b54e5017002, 0xb54e5011c1e7b90e, 0x39404a97a4243801, 0x700bde43801de6d5, 0x33790e006d539404, 0xa43801b564d39404, 0x243801e66d554405, 0xe006d5393ec70600, 0x1394048d1c1c0090, 0x53940440790e3680, 0x470061e43801de6d, 0x440790e006d53940, 0x1e6790e006d53940, 0x1643801b54e5011c, 0x1b564d544e50179, 0xd5644e5011c1e438, 0xd59b40470790e006, 0xe5012bda7990e006, 0x3470700243801b54, 0xcde7b90e004e5012, 0x90e006d5704e5010])
  | 6, 8 => (packedWords [0x90e006d539404707, 0x801de4e5011c1ea9, 0x4e5011c00c790e20, 0x404d1305e43801b5, 0x404a5790e006d539, 0x1c1a43801b54e526, 0x7002436d539404e5, 0x3801b55c1544e501, 0x1801b54e5011c1e4, 0x6d50129870690e2, 0xc5c139405c0090e0, 0x94042b690e006d57, 0x940580090e006d53, 0x5700243801d56d53, 0x43801de6d5394041, 0x779b54e526405e, 0xde6d5394048d790e, 0x394048c1c1e43801, 0x3949901790e006d5, 0xf01c1a6790e006d5, 0x1700243801b54e4, 0xa43801b54e526405, 0x243801b54e50119d, 0xe006d53940470700, 0x5394047b1c1ea390, 0x52f40470790e006d, 0x4c11c1e43801b54e, 0x4b5690e006d53940, 0xdc0090e006d53940, 0xe36801b54e5010c, 0x1b54e5012f07079, 0x1b54e5201c1a438, 0xe501394707002438, 0xe511405a43801b54, 0xfc70700243801b54, 0xc1e43801b54e5012, 0x90e23801b54e5011])
  | 6, 9 => (packedWords [0x801de6d539404927, 0x801b54e5010cde43, 0x7cdb54e470692643, 0x40470069c0090e00, 0x4e501790e006d539, 0x1c1e438da006d554, 0x790e006d5393b4c4, 0x3801b54e5010cc14, 0x3801b54e5010cde4, 0x54e5012a43379ee4, 0x54e5011c1e43801b, 0x94e50179da43801b, 0x11c1e43801b55513, 0x4790e006d59d4e50, 0x43801b5551394041, 0x8990e006d539405a, 0xb54e501100337002, 0xb555139405e43801, 0x394047079ee43801, 0x12a5e43876006d5, 0x70690e006d5544e5, 0xc0090e0079139404, 0xe43801b54e5011c1, 0xe006d539404407a0, 0x5934e5011c1a7790, 0x5011c0027002936d, 0x433019e43801b54e, 0x440790e006d53940, 0x5e43801b55513940, 0xee43801394047007, 0x1b54e5011c00b79, 0x1de6d539405e438, 0x5b54e5016946438, 0x4ed101c0090e007, 0xbc70790e006d5394, 0xc1e43801b54e5012, 0xaa243801b54e5011])
  | 6, 10 => (packedWords [0x801de6d5394047f7, 0x6d539404c61c1e43, 0x6d53940470790e00, 0x4e5011c1e4790e00, 0x40440690e32801b5, 0x1c1c0090e00799b5, 0x790e006d539404a2, 0x3801b565d3940470, 0x6d53940433055e4, 0x54e52640433790e0, 0x6d539405a43801b, 0x94047070028290e0, 0xd0cde4381e006d53, 0x1790e006d5394048, 0x7790e006d5394990, 0x779b54e501075e, 0xb564d3940440790e, 0x544e501055e43801, 0x3949901790e006d5, 0x1235e43801b5551, 0x70690e006d5544e5, 0xc008015b4e5012a4, 0xe006d57c4e526405, 0x1b54e5011c02b790, 0x5b54e5011c1e4380, 0x53940470790e0075, 0x5011c1e9b90e006d, 0x4707a4a43801b54e, 0xde43801bc6d53940, 0xe006d5394047019, 0x1b54e50123c7079, 0xd539499013b5e438, 0x795b4e501690e006, 0x4c11c1c0090e007, 0x440790e27801394, 0xc1e43801cc6d5394, 0x90e006d539404b51])
  | 6, 11 => (packedWords [0x801b55c139404407, 0x6d539404db1c1e43, 0x4f13940470790e00, 0x445011c1e43801b5, 0x40470790e006d539, 0x405a43801ee6d539, 0x600243801e66d526, 0x90e007553940433, 0x3801b54e5011c1c0, 0x6d53940466699a4, 0x9404f61c1c0090e0, 0x940470790e006d53, 0x6405e43801b55893, 0x1690e006d5934e52, 0x90e00789b54e50, 0x6d539404a51c1c, 0xb54e5011c0087a4a, 0xde6d539405e43801, 0x3940426697243801, 0x11c1c0090e006d5, 0x707a2643801b54e5, 0xe6190e0066d39404, 0x643801b54e5010cd, 0xa006d53940440794, 0x53940470035e438d, 0x53940470790e006d, 0x526405e43801b56b, 0x501790e006d5704e, 0xde5190e006d5544e, 0xe006d5394047f0c, 0xe006d5394710169, 0xd539404c81c1c009, 0xd53940470790e006, 0x4c91c1e43801f56, 0x470790e006d5394, 0x51e43801e66d5394, 0x90e006d539404400])
  | 6, 12 => (packedWords [0x90e00779b54e5017, 0x801b54e501101e93, 0x4e5012a44079ee43, 0x4e5011fde43801b5, 0xcc1d790e006d554, 0x1c1e43801b54e501, 0x7a7661801b54e501, 0x3801c16d53940470, 0x6d55b4e5011c1e4, 0x8013940470790e0, 0x54e5011c1e438da2, 0x11004079b243801b, 0x1075e43801b54e50, 0x790e006d5544e50, 0x8290e006d5394047, 0x43801b54e501345a, 0x6d539499017002, 0x39415011c1e438da, 0x3940470790e006d5, 0x11c1e43801b5645, 0x7079ee43882004e5, 0xa43801b560539404, 0x2438015b4e5010cd, 0x1de6d539404c4700, 0x1ef6d539405a4380, 0x5012a07070024380, 0x4fb1c1e43801b54e, 0x4637a7643801b54e, 0x5a6790e006d53940, 0x283801b54e5012a, 0xe0056d544e50160, 0x1b54e4ed1c1c009, 0xe5011c0207a6e438, 0x9901051e43801b54, 0x470790e006d5394, 0x5ea190e006d5394, 0x9ee43801b54e5264])
  | 6, 13 => (packedWords [0x8c6006d539404707, 0x6d539499012a5e43, 0x4e5011c003790e00, 0x4e5011c1a43801b5, 0x4e501700243801b5, 0x1c1e4388200779b5, 0x790e25801b54e501, 0x3842006d53940470, 0x6d53940440055e4, 0x54e52640440790e0, 0x940470001e43801b, 0x123440790e006d53, 0xcde43801b54e50, 0x3790e00755394047, 0x8590e006d5394043, 0x6d53940470011e, 0xb54e5011c066790e, 0xb54e5011c1e43801, 0x3940470799243801, 0x11c1e7190e006d5, 0x4a790e00789b54e5, 0xe9390e006d539404, 0xe00801b54e5011c1, 0xe006d53940470790, 0x139404a51c1ea490, 0x5011c026790e1080, 0x4a91c1a43801b54e, 0x4337001b54e50139, 0x1e9390e006d53940, 0x6e43801b55c1391c, 0x1b54e50126c707a, 0xe006d539499a438, 0xd5394047070029b9, 0xe5012e1a6190e006, 0x415700243801b54, 0xc1e43801b54e5264, 0x9b643801b54e5011])
  | 6, 14 => (packedWords [0x801b54e526499017, 0x779b54e501395a43, 0x6d5544e501700243, 0x49901235e9390e00, 0x40470790e006d539, 0x405e43801b54e51c, 0x790e21801de6d539, 0x3882006d5394045e, 0x8801b54e5011c1e4, 0x6d53940470790e0, 0x54e5011c1e438720, 0x11c01c7a6e3d801b, 0x1c1e43801b54e50, 0x3790e006d5394048, 0x43801b54e5013103, 0x7cdb54e4a91c1a, 0xb557139404707002, 0x7d4e5011c1e43801, 0x3940470790e006d5, 0x1101e4380a006d5, 0x70794643801b54e5, 0xe9b90e36801b54e4, 0xe00779b54e501305, 0x1b55f93940470790, 0x1b54e5011c1e4380, 0x139404c479e24380, 0x501395e43801b555, 0x470790e00779b54e, 0x5a43801b54e50134, 0x243801f3779b54e, 0xe006d5394810160, 0xd5394047f101c009, 0xd53940470790e006, 0xe5010cde43801ef6, 0x54c4790e20801b54, 0x75e43801b54e5013, 0x982006d539404700])
  | 6, 15 => (packedWords [0x90e006d539404707, 0x801b54e501101e52, 0x4e5011001d790e03, 0x404c71c1a43801b5, 0x29470700243801b5, 0x405e43801b55b939, 0x790e20801b555139, 0x3801b54e50130070, 0x389e004e5011c1a4, 0x54e5011c07070024, 0xe6d539405e43801b, 0x12247f7a0e43801d, 0x6405e43801b54e50, 0x794643801b54e52, 0x7990e006d5394047, 0x6d53942d011c1e, 0xb55b93940470790e, 0xb54e5011c1e43801, 0x3940426790e1a801, 0x1101a43801f36d5, 0x857002438015b4e5, 0xe43801b54e526404, 0xe00799b54e5010a9, 0x1b54e5011c016790, 0x1e656d011c1a4380, 0x1b54e50170024380, 0x9011fde5c90e3680, 0xc70790e006d53949, 0x1e43801b54e5013e, 0xe006d5664e5011c, 0xdb54e5013943369, 0xd53949901075c009, 0xd53949870790e006, 0xe501395a9b90e006, 0xc0197002436d5544, 0xc1e43801b54e5011, 0x90e09801b54e5011])
  | 6, 16 => (packedWords [0x801b54e5012e0707, 0x6d5394047e1c1e43, 0x6d53949901790e00, 0x4e5011c1e6990e00, 0x1c01e790e006d580, 0x39e43801b54e501, 0x690e006d53940470, 0xa2243801b54e501, 0x3801b54e5011c1c0, 0x54e501304337a9a4, 0x54e501161a43801b, 0x949901600243801b, 0xd1c180090e0056d3, 0x600267801b54e4e, 0x90e006a5394047, 0x43801b54e5200cd8, 0xb54e501394337002, 0xde6d539405e43801, 0xb54e4336a6e43801, 0xb5295c0090e007cd, 0x70790e006d539404, 0xa9b90e006d534404, 0x243801b54e5010a9, 0x1e46d53940470700, 0x5544e501305e4380, 0x54a4e501690e006d, 0x5011c1c0090e006d, 0x4e5797643801b54e, 0x1e43801b55513940, 0xe0079db54e5011c, 0xf6006d5394047069, 0xd539404f01c1c008, 0xcdb555139690e006, 0xe501101c0090e007, 0x4707a4e43801b54, 0xc1e4381a006d5394, 0x90e006d539481011])
  | 6, 17 => (packedWords [0x90e1e6d539404706, 0x7cdb54e5011c1c00, 0x6d53940470790e00, 0x4e5010cde4f90e00, 0x499017a0e43801b5, 0x265a5c90e006d539, 0x600243801b54e501, 0xa1a43801b54e501, 0x6d57f4e5011c1c0, 0x6d53940458790e0, 0x555139405e6190e0, 0x1310407a0e43801b, 0x11c1e43801b54e50, 0xd692e43801b54e50, 0x90e006d539404c, 0x1e801b54e5011c1c, 0x6d53940470790e, 0xb54e526405e9f90e, 0x39404407a4e43801, 0xd405a8490e006d5, 0x70600243801b54e5, 0xc009de436d501294, 0xe43801b54e47f1c1, 0x1b557539404707a6, 0x1b54e501101e4380, 0x5011c012790e2080, 0x5011c1e43801b54e, 0x501690e006d59b4e, 0x5c00a0e43801e66d, 0xe00799de6d53940, 0x1b555139404af79, 0x79c16d539405e438, 0xd55b4e501790e007, 0xe5011c1e43801de6, 0x4c4790e19801b54, 0xade43801b54e5264, 0x90e006d539404330])
  | 6, 18 => (packedWords [0x801b54fd39404707, 0x755b54e5010cde43, 0x6d53940470790e00, 0x4e5011c1a9d90e00, 0x40433700243801ae, 0x405e9b90e006d539, 0x6a0a43801de6d539, 0x90e006d54d4e501, 0xb90e006d5011c1c0, 0x54f539404707a767, 0x6d5391c1a43801b, 0x9404707002438d60, 0x15e9590e006d53, 0x1790e006d5394047, 0x9b90e006d5544e50, 0x43801b54e5011c1e, 0xb54e5011c0587a22, 0x39404a91c1a43801, 0x201c0337002006d5, 0x26405e43801b54e5, 0xc790e20801b54e5, 0xe43801b54e501100, 0x643801b54e5011c1, 0x1de6d53940420799, 0x539404700a9e4380, 0x50139440690e006d, 0x4e51c180090db54e, 0x470700243799b540, 0x1e43801b55293940, 0xe006d539404de1c, 0xe00779b54e50169, 0x1b54d1011c18009, 0xe5010cc087002438, 0xe5011c1e43801b54, 0x470790e34801b54, 0xb5e43852006d5394, 0x90e006d539445013])
  | 6, 19 => (packedWords [0x801b564d394042b7, 0x90e004e5011c1e43, 0x4e5013044079ee61, 0x6d539405e43801b5, 0x3c470799243801de, 0x1c1e43801b54e501, 0x790e006d53940499, 0x3801b54e50139440, 0x6d59e4e5011c1e4, 0x6d53940470790e0, 0x36d539101a8690e0, 0x940470700243801f, 0x51c1a43801b55d13, 0x9600243801f3799b, 0x801b54e5012e0a, 0x43801b561d394058, 0xb54e503404707002, 0x394b9011c1e43801, 0x26404e5690e006d5, 0x10cdc0090db54e5, 0x70790e00799b54e5, 0xe43801b54e501284, 0xe006d539404cd1c1, 0xe00779b54e501790, 0x539404ee1c1e6190, 0xd3940433790e006d, 0x501321e43801b556, 0x470790e006d5544e, 0x5e43801b54e50d40, 0xe00799b55513940, 0xe006d5394045e69, 0x1b54e5011c1c009, 0xd539404407956438, 0xe5011c1e8390e006, 0x4707a8a43801b54, 0x5e4390e006d5394, 0x90e006d55b551394])
  | 6, 20 => (packedWords [0x82200779b54e5017, 0x6d539404a71c1e43, 0x4e5011c010790e00, 0x49901305e43801b5, 0x40470790e006d539, 0x395e43801b56d539, 0x690e006d53949901, 0x90e007cdb54e526, 0x5801b54e5011c1c0, 0x6d5394044a690e0, 0x555139405c0090e0, 0x13ace56a0a43801b, 0x2dc0090db54e50, 0x790e006d5394044, 0xa090e006d5394047, 0x795b54e5011c1e, 0xb55353940470790e, 0xb54e5010cda43801, 0x122870700243801, 0x11c1e43801b54e5, 0x68690e006d5964e5, 0xc0090e006d539404, 0xe0e801b54e5011c1, 0x1b54e50129870790, 0x539404a31c1e4380, 0xd3940470690e006d, 0x4a51c1c0090e006e, 0x470690e006d53940, 0x5c009da43801b540, 0xe43801b54e52640, 0xe006d5544e5016a, 0xd539404eb395c009, 0xd57c4e501690e006, 0x433011c0090e006, 0x470790e006d5394, 0xade43801de6d5394, 0x90e006d539404400])
  | 6, 21 => (packedWords [0x90e006d539404667, 0x801b54e5011c1e77, 0x6d53940440799e43, 0x405011c1e9b90e00, 0x404d5690e006d539, 0x1c180090e006d539, 0x6002437edb54e501, 0xa46436d53940470, 0x38015b4e5010bd80, 0x54e5012a87070024, 0x54e5010cde43801b, 0x44e501790e00801b, 0x75a43801e26d55, 0x170027b90e004047, 0xa490e006d5544e50, 0x43801b54e5010cde, 0xb54e526404c67986, 0xb54e5011c1e43801, 0x7031070690e007dd, 0xed1c1c0090e006d5, 0x707a76006d539404, 0xe43801b561d39404, 0xe006d539404dc1c1, 0x1b56213940470790, 0x1b555139405e4380, 0x5394047079864380, 0x5011c1e43801fb6d, 0x4337a4643801b54e, 0x1e43822006d53940, 0xe006d55a4e5011c, 0x1b54e5011ec1d79, 0x1b54e5011c1e438, 0xd53949901797e438, 0x5139405e9b90e006, 0xc05e790e08801b55, 0x5a43801b54e5011, 0x243801cc6d5394])
  | 6, 22 => (packedWords [0x801b54e5264048f7, 0x6d53940470005e43, 0x4e5011000d790e00, 0x40470025e43801b5, 0x39070790e006d539, 0x405a43801b54e501, 0x700243801b555939, 0x389e006d53940470, 0x6d5394047004de4, 0x54e5011c04a790e0, 0x555139405e43801b, 0x94044079e243801b, 0x11c1e43801e66d53, 0x79d243801b54e50, 0x438d6006d57f4e47, 0x6d5394047006de, 0xb556d3940440790e, 0x6d539405e43801, 0x11c0337a0a7b90e, 0x39405e43801b54e5, 0x68790e007cdde6d5, 0xe43801b54e5011c0, 0xe43801b54e5011c1, 0xe006d5394047079d, 0x539404e31c1ea790, 0x57f4e501790e006d, 0x5011c1e43801de6d, 0x470790e006d5544e, 0x1e43801b54e53040, 0xe006d57c4e5011c, 0xe438015b4e50169, 0x1b54e5011c1c00a, 0xe507404707942438, 0x4d51c1e43801b54, 0xb470790e006d5394, 0x5e43801b54e5013, 0x90e00799b54e5264])
  | 6, 23 => (packedWords [0x90e006b939404707, 0x8da004e48d1c1a9d, 0x6d53940470600243, 0x98200])
  | 7, 0 => (packedWords [0x90e006d539404406, 0x801e66d5011c1800, 0x64d3940470700243, 0x4e5011c1e43801b5, 0x49901690e006d570, 0x1c1c0090e006d539, 0x790e36801b54e501, 0x3801b54e5011c014, 0x3801b54e5011c1e4, 0x54e5012a47079ee4, 0x940470101e43801b, 0x11c015790e006d53, 0x11c1e43801b54e50, 0x790e006d5394990, 0x43801b54e5012347, 0x43801b54e5011c1e, 0xb54e5011fc707946, 0x3940470075e43801, 0x3940470690e006d5, 0x11c1c0090e0056d, 0x707a4e43801b54e5, 0xe43801b54e501310, 0xe20801b54e5011c1, 0xe43801b54e501690, 0x539404e51c1800a0, 0x501304707002436d, 0x4e51c1e43801b54e, 0x470690e006d53940, 0x1c0090e007cdb54e, 0xe43801b54e5011c, 0xe006d539404707a, 0x99b54e5011c1e9b9, 0x6d3940470790e007, 0xe5011c1a43801b55, 0x470700243801b54, 0xc1e6190e006d5394, 0x90e08801b54e5011])
  | 7, 1 => (packedWords [0x801f36d539404707, 0x6d57f4e5011c1e43, 0x4e5011c012790e00, 0x4e5011c1e43801b5, 0x40470790e006d59b, 0x1c1a9d90e006d539, 0x6002006d539404a9, 0x90e00779b54e501, 0x3801b54e5010cd80, 0x54e5012947070024, 0x555139405a43801b, 0x940470700243801b, 0x11c1e43801de6d53, 0x3799e43801b54e50, 0x43801b54e5011c03, 0x43801b54e5011c1e, 0xb5551394047079de, 0x39404ed1c1e43801, 0x90e006d5])
  | 8, 0 => 0x90e006d539404706
  | _, _ => 0

private def wordBlocks : Nat → Nat
  | 0 => (packedWords [0x0, 0x2000000000000000, 0x10013014426a90c, 0xc00000000000000, 0x27040080b58441, 0x0, 0x4610000000000000, 0xc0000000000002, 0x70100130144008, 0x8800000000000002, 0x2200010013014400, 0x0, 0x400600000000000, 0x0, 0x42800000000000])
  | 1 => (packedWords [0x9001301440080002, 0x60000, 0x0, 0x20004, 0x4027040080810001, 0x1000000000004000, 0x1406704008081000, 0x108000000000400, 0x56270400808100, 0x1100000000042, 0x20106c068402a000, 0x1a04c20000000004, 0x480201093335544, 0x5000100000000001, 0x1408060270400808])
  | 2 => (packedWords [0x67fe43eb85120519, 0x1408106, 0x610013014400a000, 0xc800000000142800, 0x7637053094c50a01, 0x4000000000014280, 0x1004092034100100, 0x500000000001448, 0x8160679603c18510, 0xa041300000000144, 0x68106d0fb737f401, 0x1a05130000000014, 0x468166f7ff73ffc5, 0x51a05c8000000001, 0x1468176779733d5c])
  | 3 => (packedWords [0xf7ff73ffc51a05db, 0x4000000001468176, 0x92034104562e0, 0xc400102118100808, 0xa110013014464a90, 0xe0200102118100a4, 0x88010933355407aa, 0x102118104a, 0xa080000000000000, 0x10400102118140, 0xa4e127040080850, 0xa01cc0010211814, 0x42a4f737053094c5, 0x5000104001021181, 0x144a4e1270400808, 0x102118])
  | 4 => (packedWords [0x679603c185100504, 0x102118144a5e1, 0x8000000000000000, 0x1300280240000000, 0x88068402a000000, 0xc80028024000000, 0x180000000000000, 0x108002802400000, 0x58270400808100, 0xc000280240000, 0x7800000000000, 0x1c80028024000, 0x782704008085, 0x11002802400, 0x108c068402a0, 0x280240])
  | 5 => (packedWords [0x90013014400800c2, 0x9002802400020018, 0xe8068402a0000001, 0xdb00280240002001, 0x1e9069703e400a00, 0x28024000200, 0x588000000000000, 0xc0002802400020, 0x78900130144008, 0xa01db00280240002, 0x2007eb76d70bec50, 0x20028024000, 0x400088000000000, 0x100413002802400, 0x40108c0fa436b0, 0x280240])
  | 6 => (packedWords [0xe7fe43eb851005db, 0x2002802400040178, 0x8900130144008000, 0x280240006005, 0x7880000000000000, 0xc20028024000600, 0x789001301440080, 0x1ca002802400060, 0x78b7053094c508, 0xa00db00280240006, 0x6007e9069703e400, 0x1a04db0028024000, 0x6011ed0fb737f40, 0x1804d3002802400, 0x60178d0fb737f4, 0x280240])
  | 7 => (packedWords [0x90013014400880c2, 0x2002802400062078, 0x990013014400800c, 0xc200280240006247, 0x7890013014400800, 0x28024000628, 0x588000000000000, 0xc2002802400220, 0x78900130144008, 0x10800280240026, 0x2005ea7040080810, 0x1000028024004, 0x420158e704008081, 0x11002802400, 0x42015ec068402a0, 0x280240])
  | 8 => (packedWords [0xe76c40aa81000119, 0xb00280240042015e, 0xef76d70bec10a01d, 0xd900280240042015, 0x7ee76c40aa850001, 0x1d90028024004201, 0x17ef76d70bec1080, 0x1ca002802400420, 0x7eb7053094c108, 0x51b00280240046, 0x6015ee7fe43eb811, 0x8011b0028024004, 0x46015ef76d70bec1, 0x10801c2002802400, 0x460178f7053094c, 0x280240])
  | 9 => (packedWords [0xd069703e400800d3, 0x900280240046017e, 0xee76c40aa8100011, 0xdb00280240046017, 0x7ef76d70bec10801, 0x1190028024004601, 0x15ee76c40aa81000, 0x5ca002802400620, 0x8078379733d5c51a, 0xa04d300280240104, 0x48128d0fb737f441, 0x1a04db0028024010, 0x6803e90fb737f44, 0x41a04c2002802401, 0x1068078909333554, 0x280240])
  | 10 => (packedWords [0x67fe43eb851205d9, 0x800280240140817e, 0xe37053094c50a01c, 0xc800280240142807, 0x7eb7053094c50a01, 0x1db0028024014280, 0x7eb76d70bec50a0, 0x5db002802401428, 0x811ef7ff73ffc51a, 0x2051900280240142, 0x2815ee7fe43eb851, 0xa01190028024014, 0x42815ef76d70bec1, 0x5000119002802401, 0x142817ee76c40aa8, 0x280240])
  | 11 => (packedWords [0xf76d70bec50a01d9, 0xb00280240142817e, 0xee7fe43eb8512051, 0x1300280240144810, 0x68e7fe43eb851005, 0x5c80028024014481, 0x178679603c185100, 0x1c2002802401448, 0x8078b7053094c508, 0xa00c200280240146, 0x6807e90013014400, 0xa01ca0028024014, 0x46807eb7053094c5, 0x1a0413002802401, 0x146810ed0fb737f4, 0x280240])
  | 12 => (packedWords [0xd0fb737f401a04db, 0x300280240146811e, 0xed0fb737f401a041, 0x1900280240146815, 0x5ee7fe43eb811005, 0x51b0028024014681, 0x15ef7ff73ffc11a0, 0x4c2002802401468, 0x8178d09333554018, 0x50000280240146, 0x68178e79603c1851, 0x1805c20028024014, 0x468178f79733d5c5, 0x1a04d3002802401, 0x146817ed0fb737f4, 0x280240])
  | 13 => (packedWords [0xe7fe43eb85100519, 0xb00280240146817e, 0xef76d70bec50a01d, 0xca00280240146817, 0x7ef79733d5c51a05, 0x5db0028024014681, 0x17ef7ff73ffc11a0, 0x5db002802401468, 0x817ef7ff73ffc518, 0xa051b00280240146, 0x6817ef7ff73ffc51, 0x1a05d30028024014, 0x46817ef7ff73ffc5, 0x51a05d9002802401, 0x146817ef7ff73ffc, 0x280240])
  | 14 => (packedWords [0xf7ff73ffc51a05db, 0xb00280240146817e, 0xef7ff73ffc77a95d, 0xdf00280240146817, 0x7ef7ff73fff59e45, 0x5db0028024014681, 0x17ef7ff73ffc51a8, 0x5db00280240146a, 0xa57ff7ff73ffc51a, 0xa05db00280240146, 0x6a97ef7ff73ffc51, 0x1a05db0028024014, 0x66817ef7ff73ffc5, 0x500011d002802401, 0x142a5ffe76c40aa8, 0x382358])
  | 15 => (packedWords [0xf7ff73ffc55e2fdf, 0xb0038235814681fe, 0xef7ff73ffc51a05d, 0xc600382358146a1f, 0xf9b7053094c50801, 0x5df00382358146a4, 0x5fff7ff73ffc51a0, 0x95df00382358146a, 0xa5fff7ff73ffc75a, 0xaafdb00382358146, 0x6a9fef7ff73ffc57, 0x38235814, 0xa40008000000000, 0x288002020500020, 0xe6800900130144, 0x2050002])
  | 16 => (packedWords [0xd0fb737f403a8413, 0x30205000214ee906, 0x88868cc2a0821003, 0x22d0242008400, 0x5880000000000000, 0xc2022d024200a40, 0x789001301440080, 0x8002022d024200e4, 0x6858900130144028, 0x880c2022d024200e, 0xe687890013014402, 0x119022d024200, 0x4a415ee76c40aa81, 0x128811b022d02420, 0x4e695ef76d70bec, 0x22d0242])
  | 17 => (packedWords [0xf7ff73ffc51a05db, 0xb022d024214ec17e, 0xef7ff73ffc53a85d, 0x19022d024214ee97, 0x60068402a304200, 0x1100980081000, 0x60000000000000, 0x10c110098008520, 0x808627040080b542, 0xa80001110b918950, 0x2a08610013014404, 0x4a80c01110b91895, 0x52a0f61001301440, 0x54a81c81110b9189, 0x952a0f637053094c, 0x1110b918])
  | 18 => (packedWords [0x37053094c54a8104, 0x21110b918952a4e7, 0x690013014404a800, 0x131110b918956a08, 0x86d0fb737f405a84, 0x1191110b918956a1, 0x15ee76c40aa81000, 0x5db11289a408520, 0x817ef7ff73ffc51a, 0xa05db11289a40956, 0x6817ef7ff73fff55, 0x4a811911289a4095, 0x52a1def76d70bec1, 0x55a05df1138bb589, 0x95681fef7ff73fff, 0x1138bb58])
  | 19 => (packedWords [0x90013014404a80c2, 0xb1138bb58956a0fe, 0xef7ff73ffc55a85d, 0xdf1138bb58956a1f, 0xfff7ff73ffc55a85, 0x131138bb58956a5, 0x69069703e406a8, 0x80021305980281a4, 0xe88690013014406a, 0xa80db1315b91a95e, 0xa401e9069703e406, 0x7a85db132d9a4281, 0x5ec17ef7ff73ffc5, 0x56a81ca132d9a429, 0x95ee8feb7053094c, 0x133dbb5a])
  | 20 => (packedWords [0xf7ff73ffc57a85db, 0x4133dbb5a95ee9fe, 0x100000000060410c, 0x224404080001042, 0x92034100342e, 0xc22440408000508, 0xc211001301442289, 0x4104244040800052, 0x461270400808584, 0x24404080021, 0x52c6100000000000, 0x1005002440408002, 0x65ad61679603c185, 0x264ba04244040801, 0x12c81000000000, 0x24506198])
  | 21 => (packedWords [0x92034104142e04, 0x624506198105aca1, 0x110933355467ebec, 0x424506198105aca, 0xe127040080850001, 0xc224506198165ac, 0xc799001301442289, 0x4020246842c00072, 0x808008c000885, 0x441cc246842c0021, 0x1047927040080858, 0x246842c002, 0x272c798000000000, 0x800c2246842c00, 0x272c79900130144, 0x246842c0])
  | 22 => (packedWords [0xe76c40aa81000119, 0xf246842c00672d7f, 0xff7ff73ffc71e15d, 0xdb246842c0147857, 0x7ef7ff73ffc53e2f, 0x5db246842c014789, 0xd7ff7ff73ffc73a9, 0x45df246842c0147a, 0x857ff7ff73ffc59e, 0xa05db246842c0167, 0x7ad7ff7ff73ffc51, 0x7ebec6246842c016, 0x7acf99093335546, 0x51e2fdf247863d81, 0x147adfff7ff73ffc, 0x247863d8])
  | 23 => (packedWords [0xf7ff73ffc77ebfdf, 0xe247863d8147adff, 0xfb7053094c50a01c, 0xdf247863d8167acf, 0xfff7ff73ffc51a05, 0x2247863d8167ad, 0xc619001301440288, 0x222645408202f6, 0x480888008c000821, 0x880c2266d42c202d, 0xf6c7990013014402, 0x3a85db266d42c202, 0x6fed7ff7ff73ffc5, 0x946e11266d42c21, 0x130040fa436b0, 0x48020420])
  | 24 => (packedWords [0x4000000000000000, 0x480204200401300, 0x670400808180410, 0x48020420060134, 0x60679603c1859045, 0xf044802042016493, 0x380679603c185946, 0x2e00481225381409, 0xbb80409203410010, 0x2e0048122538144, 0x4bbe040920341001, 0x102f004812253814, 0x44bbe0679603c185, 0x5102f04481225381, 0x144bfe1679603c18, 0x48122538])
  | 25 => (packedWords [0xd0fb737f401a2e13, 0x448122538146bb86, 0x1670400808580410, 0x48122538160b7e, 0xc0679603c181906f, 0x11948122538164bb, 0x35ee76c40aa81000, 0x4100482a06600421, 0x1358e70400808180, 0x4119482a0660062, 0x2135ee76c40aa818, 0x8841c2482a066006, 0x661378f7053094c1, 0x51a05db482a06600, 0x146937ef7ff73ffc, 0x482a0660])
  | 26 => (packedWords [0xf7ff73ffc59e6fdb, 0xb482a0660146937e, 0xef7ff73ffc59a45d, 0xdf482a0660166937, 0xfef7ff73ffc59e6f, 0xf19483a277814693, 0xbdee7fe43eb81102, 0x2ec2483a2778146b, 0xbbf8d09333554018, 0xa2fdb483a2778146, 0x6bbfef7ff73ffc51, 0x1a2fdf483a277814, 0x46bffff7ff73ffc5, 0x58a41dd483a27781, 0x162b7fff76d70bec, 0x483a2778])
  | 27 => (packedWords [0xf7ff73ffc59a45df, 0xb483a2778166b7ff, 0xef7ff73ffc19a6f1, 0xdb483a2778166bbd, 0xfef7ff73ffc59a6f, 0xe13483a2778166bb, 0xb00c0fa436b00302, 0xae024a07042200c5, 0xfb80d09333554038, 0x2e134a17253a14e, 0xc5b08c0fa436b003, 0x8140314a2f066200, 0x285308c868cc2a08, 0x53a2fdb4a2f06620, 0x14edb7ef7ff73ffc, 0x4a2f0662])
  | 28 => (packedWords [0xf79733d5c538afc2, 0xb4a3f277a14efbf8, 0xef7ff73ffc53aafd, 0x194a3f277a14efbf, 0x6676c40aab18041, 0xa0459029c2085013, 0x2800000000030c46, 0x2e115912bd388101, 0x938640fa436b0052, 0x66f1d5912bd38950, 0x938667fe43ebb5d, 0x5aae005912bd3895, 0x56bb865093335540, 0x18041195912bd389, 0x852135ee76c40aab, 0x592a9e60])
  | 29 => (packedWords [0xf7ff73fff59a45db, 0xd592a9e60956937e, 0xee7fe43ebb5d66f1, 0xdb593abf7895293d, 0xfef7ff73ffc55a2f, 0xfdf593abf7895693, 0x3fef7ff73fff5de6, 0xafdb593abf789569, 0xbbfef7ff73ffc55a, 0x11593abf78956, 0xa5306c068402a000, 0x2880135b079c2285, 0x5e7b06d069703e40, 0x18041115b079c228, 0x87a5346e76c40aa8, 0x5b079c22])
  | 30 => (packedWords [0xd0fb737f401a0413, 0x5b079c2295ed306, 0x60aa0, 0x115b17bd3a8187a8, 0x8640fa436b0072ae, 0xe115b17bd3a958fb, 0x386c0fa436b00522, 0xae135b17bd3a95ad, 0xd386d0fb737f407a, 0x115b17bd3a95a, 0xaf386c068402a000, 0x4a80115b17bd3a95, 0x5af386d069703e40, 0x6aaa005b17bd3a9, 0x95afa86100130144, 0x5b17bd3a])
  | 31 => (packedWords [0xc0fa436b00722e13, 0x35b17bd3a95cdb86, 0x6d069703e404a801, 0x135b17bd3a95ef38, 0x86d0fb737f405a84, 0xe115b17bd3a95ef3, 0xb86c0fa436b00102, 0x80135b17bd3a95ef, 0xfb86d069703e406a, 0xaae025b17bd3a95e, 0xefb86d0933355407, 0x1a2e135b17bd3a95, 0x5efb86d0fb737f40, 0x38ae135b17bd3a9, 0x95efb86d0fb737f4, 0x5b17bd3a])
  | 32 => (packedWords [0xd0fb737f405aae11, 0x35b17bd3a95efb86, 0x6d0fb737f407aae1, 0xd35b17bd3a95efb8, 0x86d0fb737f427abe, 0xf1f5b17bd3a95efb, 0xb86f7ff73fff5fee, 0xae135b17bd3a95ef, 0xfbe6d0fb737f407a, 0xaaf135b17bd3a95e, 0xefbe6f7ff73ffc57, 0x7aaed35b17bd3a95, 0x5efbf6d0fb737f40, 0x57aafdb5b17bd3a9, 0x95efbf6f7ff73ffc, 0x5b17bd3a])
  | 33 => (packedWords [0xd0fb737f407aae13, 0x75b17bd3a95effe7, 0x7f7ff73ffc57aaf1, 0x135b17bd3a95effe, 0xc6d0fb737f407aae, 0xf135b17bd3a97efb, 0xbc6f7ff73ffc1fae, 0x115b17bd3a97ef, 0x535ec068402a0000, 0x1195b2f9e6285a, 0xa535ee76c40aa810, 0x800d35b2f9e6285, 0x5e537ed069703e40, 0x12881db5b2f9e628, 0x85e7b7ef76d70bec, 0x5b2f9e62])
  | 34 => (packedWords [0xe76c40aa81804119, 0xb5b2f9e6287a535e, 0xef7ff73ffc51a05d, 0xdb5b2f9e6295ed37, 0x7ef7ff73ffc53a85, 0x5db5b2f9e6295efb, 0x37ef7ff73ffc59a4, 0x80d15b2f9e6297ed, 0xf3fed069703e404a, 0xa81d95b3fbf7a95a, 0xaf3fef76d70bec54, 0x4a80d35b3fbf7a95, 0x5ef3fed069703e40, 0x55a85db5b3fbf7a9, 0x95ef3fef7ff73ffc, 0x5b3fbf7a])
  | 35 => (packedWords [0xd0fb737f407aae13, 0x35b3fbf7a95efb8e, 0xed0fb737f407aaed, 0xdb5b3fbf7a95efb9, 0x9ed0fb737f407aae, 0xe135b3fbf7a95efb, 0xbded0fb737f407aa, 0xaf1b5b3fbf7a95ef, 0xfbdef7ff73ffc17a, 0x2e115b3fbf7a95e, 0xefbfec0fa436b001, 0x182ed35b3fbf7a95, 0x5efbfed0fb737f40, 0x7aae135b3fbf7a9, 0x95efbfed0fb737f4, 0x5b3fbf7a])
  | 36 => (packedWords [0xd0fb737f407aaed3, 0x95b3fbf7a95efbfe, 0xee7fe43eb85102f1, 0xdb5b3fbf7a95efbf, 0xfef7ff73ffc17aaf, 0xfdb5b3fbf7a95efb, 0xbfef7ff73ffc51a2, 0xaf1b5b3fbf7a95ef, 0xfbfef7ff73ffc57a, 0xaafd35b3fbf7a95e, 0xefbfef7ff73ffc57, 0x7aafdb5b3fbf7a95, 0x5efbfef7ff73ffc5, 0x5feefdf5b3fbf7a9, 0x95efbfef7ff73fff, 0x5b3fbf7a])
  | 37 => (packedWords [0xd0fb737f407aaed3, 0xf5b3fbf7a95effff, 0xff7ff73ffc57aafd, 0x135b3fbf7a95efff, 0xded0fb737f407aae, 0xf1b5b3fbf7a97efb, 0xbdef7ff73ffc1fae, 0xaed35b3fbf7a97ef, 0xfbfed0fb737f407a, 0xaefdb5b3fbf7a97e, 0xefbfef7ff73ffc5f, 0x946e005b3fbf7a97, 0x251b004092034100, 0x18041006c4244a00, 0x653f61670400808, 0x6c4244a0])
  | 38 => (packedWords [0x846a04, 0x46c5265b80213e81, 0x14092034104946e0, 0x46c5265b8125bfa, 0xa14092034104142e, 0xf046c5265b8145bf, 0xfa1679603c185946, 0x2e006c5265b8145b, 0xbfe1409203410010, 0x41046c5265b8165, 0x5bfe167040080858, 0x906f006c5265b816, 0x65bfe1679603c181, 0x5102f006c5265b81, 0x165bfe1679603c18, 0x6c5265b8])
  | 39 => (packedWords [0x679603c185102f04, 0x46c5265b8165bfe1, 0x1679603c185946f0, 0x66c5265b8165bfe, 0xe1679603c185b46f, 0xf0c6c5265b8165bf, 0xfe1679603c1b5946, 0xffc66c5265b8165b, 0xbfe1779733d5c7fe, 0xe6f176c5265b8165, 0x7bfe7f7ff73ffc59, 0x946f0c6c5265b816, 0x67bff7679603c185, 0x59e6fcc6c5265b81, 0x167bff7779733d5c, 0x6c5265b8])
  | 40 => (packedWords [0xc0fa436b00946e13, 0xb6c6a46e00251b08, 0xff76d70bec18841d, 0xdb6c6a46e00673f7, 0x7ef7ff73ffc59e6f, 0x5db6c6a46e01679b, 0xf7ff7ff73ffc59a4, 0x6f046c6a46e0167b, 0xbfe9679603c18594, 0x46f066c7a67f8165, 0x5bfe9e79603c1859, 0x946f176c7a67f816, 0x65bfe9e7fe43eb85, 0x5946f0c6c7a67f81, 0x165bff9679603c18, 0x6c7a67f8])
  | 41 => (packedWords [0x679603c185946fcc, 0x46c7a67f8165bff9, 0x9e79603c185946f0, 0xc66c7a67f8167bff, 0xf9f79733d5c59c6f, 0xed36c7a67f8167bf, 0xfffd0fb737f401a2, 0x6f0c6c7a67f8167b, 0xbfffe79603c18594, 0x46f1d6c7a67f8167, 0x7bfffe7fe43eb859, 0x9e6fce6c7a67f816, 0x67bffff79733d5c5, 0x51a2fdb6c7a67f81, 0x167bffff7ff73ffc, 0x6c7a67f8])
  | 42 => (packedWords [0xf7ff73ffc59c6fdf, 0xf6c7a67f8167bfff, 0xff7ff73ffc59e6f1, 0xd76c7a67f8167bff, 0xfff7ff73ffc59e6f, 0xfdd6c7a67f8167bf, 0xffff7ff73ffc59e6, 0x6fdf6c7a67f8167b, 0xbffff7ff73ffc59e, 0xeffdf6c7a67f8167, 0x7bffff7ff73ffc7f, 0xa56a206c7a67f816, 0x295a0008008c0008, 0x8b56e316e4744a20, 0x295b0048facf6b0, 0x6e4744a2])
  | 43 => (packedWords [0x6f968fc18db56f24, 0x46e5765ba16dffe1, 0x1e79603c185946f0, 0x66e5765ba16fffe, 0xe1f79733d5c5bcef, 0xe336e5765ba16fff, 0xb08c8facf6b08b56, 0x6ffb6e6f46e202d5, 0xdb7effffffffcdbf, 0xffef76e6f46e216f, 0xdffa9d8fbff7f4ef, 0xb56f376e7f67fa12, 0x6dffe9effecfeb8d, 0x5946f046e7f67fa1, 0x16ffff9e79603c18, 0x6e7f67fa])
  | 44 => (packedWords [0xf79733d5c5bcefc6, 0xf6e7f67fa16ffff9, 0xff7ff73ffc5beefd, 0xdf6e7f67fa16ffff, 0xa777ff73fff7feff, 0xf047d52fdb8955bf, 0xfe1679603c1b5d46, 0x6f1d7d52fdb8975b, 0xbfe767fe43ebb5d6, 0x46f047d52fdb8975, 0x7bfe7679603c1859, 0xdeef047d52fdb897, 0x77bfe7779733d5c5, 0x7feffdf7d52fdb89, 0x957bffff7ff73fff, 0x7d7afff8])
  | 45 => (packedWords [0xf7ff73ffc5deefdf, 0xf7d7afff8977bfff, 0xff7ff73fff5de6fd, 0x137d7afff8977bff, 0x86d0fb737f407eae, 0xe177f57fdba95ffb, 0xf87d0fb737f427eb, 0xbed37f57fdba95ff, 0xffa7d0fb737f427a, 0xebed77f57fdba95f, 0xfffa7d0fb737f467, 0x7aae137f57fdba95, 0x7fffe7d0fb737f40, 0x5946f157f57fdba9, 0x97fffe7e7fe43eb8, 0x7f57fdba])
  | 46 => (packedWords [0xf7ff73ffc5feef17, 0x37f57fdba97fffe7, 0xfd0fb737f427abed, 0xdf7f7ffffa95ffff, 0xfff7ff73ffc77ebf, 0xf3f7f7ffffa95fff, 0xb8eeffecfebbdf76, 0xee337f7ffffa97dd, 0xfb8ed8fbff7f48ff, 0xaae137f7ffffa97f, 0xfffffd0fb737f407, 0x7aaed37f7ffffa97, 0x7fffffd0fb737f40, 0x5946f1d7f7ffffa9, 0x97fffffe7fe43eb8, 0x7f7ffffa])
  | 47 => (packedWords [0xf7ff73ffc57aafdb, 0xf7f7ffffa97fffff, 0xff7ff73ffc59e6fd, 0x1f7f7ffffa97ffff, 0xfff7ff73ffc5feef, 0xfd77f7ffffa97fff, 0xffff7ff73ffc5fee, 0xefdf7f7ffffa97ff, 0xfffff7ff73ffc5fe, 0x11cc7f7ffffa97f, 0x47127040080b70, 0x8080000568, 0x8200500000000000, 0x20890c0808000056, 0x6822471100130144, 0x80800005])
  | 48 => (packedWords [0x37053094c70a91c8, 0x4808000057c2a477, 0x137053094c70891c, 0xe88090211d7c2a4f, 0x1808008c003a0110, 0x1cc80a8024568000, 0x47927040080b7001, 0x80a802456800, 0x58800000000000, 0x890c080a80245682, 0x2247990013014420, 0x800c280a8024568, 0x8600789001301440, 0x20890c280a802456, 0x6862479900130144, 0x80a80245])
  | 49 => (packedWords [0x2f048c80b9814128, 0x980a802456a00058, 0xee76c40aa8100011, 0xd980a802456c2015, 0x7ff76d70bec30891, 0x5db80a802456c225, 0x17ef7ff73ffc51a0, 0x15df80a802457c68, 0x857ff7ff73fff71a, 0xa95db80a802457c6, 0x6a57ff7ff73ffc71, 0x1895c680a802457c, 0xc6a5f9f79733d5c7, 0x71a95df80b8235d7, 0x7c6a5fff7ff73ffc, 0x80b8235d])
  | 50 => (packedWords [0x90013014422890c2, 0x28285000768e6c71, 0x89801bc144a2990e, 0xc282ad024768a401, 0x7990013014422890, 0x2082ad024768e6c, 0x5888008c0008010, 0x90e082ad02476aa4, 0x64799801bc144a09, 0x900e282ad02476aa, 0xe40789801bc14480, 0x29802282ad02476a, 0xae68589801bc1448, 0x901013982ad02476, 0x6ea415eef6cccaa8, 0x82ad0247])
  | 51 => (packedWords [0xf7ff73ffc73a95db, 0xb82ad02477ceed7f, 0xeffffffffcd1b05f, 0xc882ad02477eec17, 0x1610013014724a90, 0x10891809805e9200, 0x5627040080b1000, 0x91c891809805ed20, 0x247737053094f308, 0xa01c891809805ed2, 0x2807637053094f50, 0x40900491809805fd, 0x9024810000000032, 0x24a90cc9190b91de, 0xe922497100130147, 0x9190b91d])
  | 52 => (packedWords [0x27040080b340910c, 0xc9190b91ded224d7, 0x710013014764a90c, 0xcc9190b91df92a4b, 0xf727040080b74211, 0x10c9190b91dfd084, 0x48727040080b7429, 0x91cc9190b91dfd0a, 0x809637053094f74a, 0x2010c9190b91dfd2, 0x280d627040080b54, 0x4a90c89190b91dfd, 0xd2a0961001301472, 0x4a80009190b91df, 0xfd2a0d6100130144, 0x9190b91d])
  | 53 => (packedWords [0x27040080b1000108, 0x89190b91dfd2a0d6, 0x637053094f14a810, 0xc89190b91dfd2a0d, 0xf637053094f14a81, 0x1c89190b91dfd2a0, 0xf637053094f54a8, 0x90049190b91dfd2a, 0xa48710013014724a, 0xa90c09190b91dfd2, 0x2a4f710013014424, 0x10c9190b91dfd, 0xd2a4f727040080b5, 0x74a91c49190b91df, 0xfd2a4f737053094c, 0x9190b91d])
  | 54 => (packedWords [0x37053094c74a91c8, 0x89190b91dfd2a4f7, 0x737053094f34a91c, 0xcc9190b91dfd2a4f, 0xf737053094f50a01, 0x10c9190b91dfd2a4, 0x4f737053094f54a8, 0x91cc9190b91dfd2a, 0xa4f737053094f708, 0xa91cc9190b91dfd2, 0x2a4f737053094f74, 0x6a91ce9190b91dfd, 0xd2a4f737053094f7, 0x7ced1cc9190b91df, 0xfd2a4f737053094f, 0x9190b91d])
  | 55 => (packedWords [0x77053094f74a91cc, 0xc9190b91dfd2a5f7, 0x737053094f74a91c, 0xce9190b91dfd6a4f, 0xf7b7053094f74a91, 0x5cc9190b91dfd6a4, 0x5f7779733d5f75a9, 0x95df9190b91dfd6a, 0xa5f7f7ff73fff75a, 0xa91cc9190b91dfd6, 0x6acf737053094f74, 0x4a91cc9190b91dfd, 0xf2a4f737053094f7, 0x24a90db9190b91df, 0xe92001e9069703e7, 0x91a89a45])
  | 56 => (packedWords [0xa7040080b1000108, 0x991a89a45ed2005e, 0xee76c40aab100011, 0xca91a89a45ed2015, 0x7eb7053094f10801, 0x1db91a89a45ed600, 0x57ff76d70bef3089, 0x5db91a89a45ed62, 0x817ef7ff73fff51a, 0xa95db91a89a45fd6, 0x6817ef7ff73fff75, 0x1a95db91a89a45fd, 0xd6a57ff7ff73fff7, 0x74a91cc91a89a45f, 0xfd2a4ff37053094f, 0x91b8bb5d])
  | 57 => (packedWords [0xb7053094f74a91cc, 0xe91b8bb5dfd2a4ff, 0xfb7053094f74a91c, 0xdf91b8bb5dfd2a4f, 0xffb76d70bef74a91, 0x1cc91b8bb5dfd2a4, 0x5fff7053094f74a9, 0x91dd91b8bb5dfd2a, 0xa5fff76d70bef74a, 0xa810a91b8bb5dfd2, 0x6a0deb7053094f14, 0x4a81ca91b8bb5dfd, 0xd6a0feb7053094f1, 0x15a851b91b8bb5df, 0xfd6a1def7ff73fff, 0x91b8bb5d])
  | 58 => (packedWords [0xf7ff73fff55a85db, 0x291b8bb5dfd6a1fe, 0xf90013014424a90c, 0xc91b8bb5dfd6a4f, 0xffa7040080b50001, 0x1ce91b8bb5dfd6a4, 0x4ffb7053094f5080, 0x91cc91b8bb5dfd6a, 0xa4ffb7053094f74a, 0xa91ce91b8bb5dfd6, 0x6a4ffb7053094f74, 0x5a94d391b8bb5dfd, 0xd6a5ffd0fb737f42, 0x510051d91b8bb5df, 0xfd6a5ffe7fe43ebb, 0x91b8bb5d])
  | 59 => (packedWords [0xf7053094f74a91ce, 0xf91b8bb5dfd6a5ff, 0xff76d70bef74a91d, 0xce91b8bb5dfd6a5f, 0xfff79733d5f75a95, 0x5db91b8bb5dfd6a5, 0x5fff7ff73ffc75a9, 0x5df91b8bb5dfd6a, 0xa5fff7ff73fff51a, 0xa95dd91b8bb5dfd6, 0x6a5fff7ff73fff75, 0x5a95df91b8bb5dfd, 0xd6a5fff7ff73fff7, 0x74a91ce91b8bb5df, 0xfd6acffb7053094f, 0x91b8bb5d])
  | 60 => (packedWords [0xb7053094f74a91cc, 0xe91b8bb5dff2a4ff, 0xfb7053094f74a91c, 0x2091b8bb5dff6a4f, 0x8008c003a6190, 0x1cc93859807e9840, 0x4f7b7053094f74a9, 0x91ce9395b91ffdae, 0xecf7b7053094f76a, 0x100399395b91ffde, 0xa401e8868cc2a380, 0x6b90fb93ad9a47e9, 0x9a401e9869fc3e7a, 0x901012893ad9a47e, 0xefa405eaf048c80b, 0x93ad9a47])
  | 61 => (packedWords [0xffffffffff7b95fb, 0xc93ad9a47fdec17e, 0xfb7053094f74a91c, 0xff93bdbb5ffdae4f, 0xffbf6dfcbeff6b91, 0x1ce93bdbb5ffdae4, 0x4ffb7053094f74a9, 0x91ce93bdbb5ffdee, 0xecffb7053094f76a, 0xa95df93bdbb5ffde, 0xeedfff7ff73fff77, 0x4b91ec93bdbb5ffd, 0xfae4ffbf05bc94ff, 0xa85502493bdbb5ff, 0x6a1040108008c003, 0xa4c04085])
  | 62 => (packedWords [0x2f048c80bf85512c, 0xa4c040856a10401, 0x110013014420890c, 0xe0a4c040856a72c7, 0x7908008c000a0110, 0x1eca4e842c56a104, 0x4792f048c80bf855, 0x90c2a4e842c56a10, 0x2c79900130144208, 0xf55ffa4e842c56a7, 0x7857fffffffffff9, 0x1a95dba4e842c57e, 0xe7ad7ff7ff73ffc7, 0xfffffeea4e842c57, 0x7a5acf93f97bfd5f, 0xa4f863dd])
  | 63 => (packedWords [0x8008c000a219020, 0xa6c540876a96c01, 0x108008c000a21902, 0xe2a6c540876ad6c6, 0x7988008c000a2110, 0x20a6ed42c76ad4c, 0xc7988008c0008010, 0x90c2a6ed42c76af6, 0x6c79900130144228, 0x900e2a6ed42c76af, 0xf6c799801bc14480, 0x298022a6ed42c76a, 0xaf6c799801bc1448, 0xa0990e0a6ed42c76, 0x6af6c799801bc144, 0xa6ed42c7])
  | 64 => (packedWords [0x9801bc144a2990e2, 0x2a6ed42c76af6c79, 0x99801bc144a6b90e, 0xeea6ed42c76af6c7, 0x79bf05bc94ffadd1, 0x1fba6ed42c76af6c, 0xd7fff6dfcbecb299, 0x90e2a6ed42c76ef6, 0xec7f9801bc144a2b, 0xb91eaa6ed42c77ef, 0xfec7fbf05bc94cf2, 0x3995e2a6ed42c77e, 0xefed79ff97bfd5cf, 0xa3b94f3a6ed42c77, 0x7efed7fd8fbff7f4, 0xa6ed42c7])
  | 65 => (packedWords [0xffffffffcf3b95fb, 0x6a6ed42c77efed7f, 0x99893bf554e7fbee, 0xe2a6fd63df7afecf, 0xf99801bc144a2990, 0x1e6a6fd63df7efec, 0xcf9bf05bc94cf299, 0x91cca6fd63df7efe, 0xa4f737053094f74e, 0xa91ceb5d0f99dfd3, 0x7acf737053094f76, 0x7ebfceb5d0f99dfd, 0xd7acf7379733d5f7, 0x7ced1ccb5d0f99df, 0xff3a4f737053094f, 0xb5d0f99d])
  | 66 => (packedWords [0x37053094f74a91cc, 0xeb5d0f99dff7acf7, 0xfb7053094f76a91c, 0xdfb5f8fbddfd7acf, 0xfff7ff73fff77ebf, 0x1ccb5f8fbddfd7ad, 0x4ff37053094f7ced, 0xd1ecb5f8fbddff3a, 0xa4ff3f05bc94ffcf, 0xa91ccb5f8fbddff3, 0x7acffb7053094f74, 0x4a91ceb5f8fbddff, 0xf7acffb7053094f7, 0x75a95dfb5f8fbddf, 0xff7adfff7ff73fff, 0xb5f8fbdd])
  | 67 => (packedWords [0xb7053094f76a91ce, 0xfb7d5f99ffffecf7, 0xfbf6dfcbeffefd1f, 0xfbb7eddac7ebb447, 0x7f9869fc3e7a6b90, 0xe2b7eddac7ebf6c, 0xc7f9801bc144a299, 0x91eab7eddac7eff6, 0x6c7fbf05bc94fb29, 0xfbeffb7eddac7eff, 0xfecbf98fbff7f7e7, 0x6b90e2b7fdfbdff9, 0xffecff9801bc144a, 0x76a91ceb7fdfbdff, 0xfffecffb7053094f, 0xb7fdfbdf])
  | 68 => (packedWords [0xbf05bc94ff6b91ee, 0xfb7fdfbdffffecff, 0xfffffffffff7b95f, 0x20b7fdfbdffffedf, 0x58ef048c80898141, 0x108caaf06676ea53, 0x35667040080b1804, 0x91ccd9829c25ef21, 0xb7f777053094f74a, 0xeffddd992bd3dfd2, 0x2b7f777ff73fff7d, 0x5abfccd992bd3dfd, 0xd6bff7779733d5f7, 0x7cad1ccd992bd3df, 0xff2b7f777053094f, 0xd992bd3d])
  | 69 => (packedWords [0xe76c40aab1804119, 0xbd9aa9e65ef2135e, 0xef7ff73fff59a45d, 0xdfd9aa9e65ff6937, 0xfff7ff73fff7deff, 0xfdfd9babf7dfd6b7, 0xffff7ff73fff75ab, 0xd1ccd9babf7dfd6b, 0xb7fff7053094f7ca, 0xad1ddd9babf7dff2, 0x2b7fff76d70bef7c, 0xcad1ced9babf7dff, 0xf6b7fff7053094f7, 0x7dad5dfd9babf7df, 0xff6b7fff7ff73fff, 0xd9babf7d])
  | 70 => (packedWords [0x8008c0038814020, 0x9db879c27eb85200, 0x6e76c40aab100011, 0xdddb879c27eda535, 0xf7f76d70bef74a91, 0xe13db97bd3ffdaf7, 0xbd6d0fb737f407aa, 0xaf1bdb97bd3ffdef, 0xfbd6f7ff73fff17a, 0xabed3db97bd3ffde, 0xefff7d0fb737f427, 0x7abfdfdb97bd3ffd, 0xdefff7f7ff73fff7, 0x8814039db97bd3ff, 0xeba531ec868cc2a3, 0xdbaf9e67])
  | 71 => (packedWords [0xc868cc2a38010039, 0x9dbaf9e67eda531e, 0xeef6cccaab981413, 0x11dbaf9e67eda531, 0x5ec068402a000000, 0x119dbaf9e67eda53, 0x35ee76c40aa81000, 0x119dbaf9e67eda5, 0x535ee76c40aab100, 0x10031dbaf9e67eda, 0xa535ec868cc2a080, 0x804119dbaf9e67ef, 0xfa535ee76c40aab1, 0x9814128dbaf9e67e, 0xefa535eef048c80b, 0xdbaf9e67])
  | 72 => (packedWords [0xef6cccaa89010139, 0x1dbaf9e67efa535e, 0xeef6cccaa8981413, 0x39dbaf9e67efa535, 0x5eef6cccaab90101, 0x139dbaf9e67efa53, 0x35eef6cccaab9814, 0x413ddbaf9e67efa5, 0x535eef6cccaabd85, 0xbd1fbdbaf9e67efa, 0xa535eff6dfcbefbe, 0x814139dbaf9e67ef, 0xfa777fef6cccaab9, 0xb89d1f9dbaf9e67e, 0xefa777fff6dfcbef, 0xdbaf9e67])
  | 73 => (packedWords [0xef6cccaab9814139, 0xbdbaf9e67efe537e, 0xeff6dfcbef98941f, 0x39dbaf9e67efe537, 0x5eef6cccaab98141, 0x13bdbaf9e67efe7b, 0xb5eff6dfcbef9a9c, 0x5dbdbaf9e67efe7, 0xd37ef7ff73fff51a, 0x14139dbaf9e67fde, 0xad37eef6cccaabd8, 0x8b41f9dbaf9e67ff, 0xfad37eff6dfcbefd, 0x99b453bdbaf9e67f, 0xffed35efffffffff, 0xdbaf9e67])
  | 74 => (packedWords [0xeffecfebbd914539, 0xbdbaf9e67ffed37e, 0xefffffffffd9b45f, 0xffdbaf9e67ffed37, 0x9effffffffffffff, 0x1dddbbfbf7ffdad3, 0x7fff76d70bef74a9, 0x95dfdbbfbf7ffdaf, 0xf7fff7ff73fff75a, 0xbbefbdbbfbf7ffde, 0xefb9ed8fbff7f7a7, 0x7aae13dbbfbf7ffd, 0xdefbded0fb737f40, 0x17aaf1bdbbfbf7ff, 0xfdefbdef7ff73fff, 0xdbbfbf7f])
  | 75 => (packedWords [0xd0fb737f407aaed3, 0xbdbbfbf7ffdefbfe, 0xef7ff73fff57aafd, 0xd3dbbfbf7ffdefbf, 0xffd0fb737f427abe, 0xfdbdbbfbf7ffdeff, 0xffff7ff73ffc77ab, 0xbfdfdbbfbf7ffdef, 0xfffff7ff73fff77a, 0x76f3ddbbfbf7ffde, 0xad3deeffecfebbdd, 0x814139dbbfbf7fff, 0xfaf3deef6cccaab9, 0x9cbc139dbbfbf7ff, 0xffaf3deff6dfcbef, 0xdbbfbf7f])
  | 76 => (packedWords [0xef6cccaabd81413d, 0xddbbfbf7fffaf7ff, 0xfff6dfcbeffcbd1f, 0x3ddbbfbf7fffaf7f, 0xffef6cccaabd8141, 0x1ffdbbfbf7fffef7, 0x7ffff6dfcbeffcbd, 0xd5ffdbbfbf7fffef, 0xf7ffffffffffffdb, 0xbae33dbbfbf7fffe, 0xefbded8fbff7f487, 0x916f39dbbfbf7fff, 0xfefbdeeffecfebb9, 0x9fbef3bdbbfbf7ff, 0xffefbdefffffffff, 0xdbbfbf7f])
  | 77 => (packedWords [0xfffffffff9fbeffb, 0xbdbbfbf7fffefbfe, 0xefffffffffdfbeff, 0xffdbbfbf7fffefbf, 0xfffffffffffffbff, 0xf04dbbfbf7fffeff, 0xff1679603c185946, 0xffc4ecd265bd7e7b, 0xbff1779733d5c79c, 0x57fececd265bd7e7, 0x5bff96f968fc1bf9, 0x946f04ecfa67fd7e, 0xe7bff9e79603c185, 0x79cffc6ecfa67fd7, 0x7e7bff9f79733d5c, 0xecfa67fd])
  | 78 => (packedWords [0xf7ff73ffc79effdf, 0xfecfa67fd7e7bfff, 0x9effecfebbfb57ff, 0xf3eeef46e76ad5f7, 0x79d8fbff7f4abdfe, 0xe2eeef46e76af7f, 0xf79d801bc144a299, 0xd1e2eeef46e76ef7, 0x7f79ff05bc94cba9, 0x9bee2eeef46e76ef, 0xffff9d893bf554a3, 0x956f24eeff67ff7e, 0xeffff9ef968fc18d, 0xfbdffe6eeff67ff7, 0x7effff9ff97bfd5c, 0xeeff67ff])
  | 79 => (packedWords [0xffffffffcfbfffff, 0xceeff67ff7efffff, 0x7679603c1b5946f0, 0xccfdd2fdbdff7bff, 0xf777053094f7cad1, 0xfccfdd2fdbdff7bf, 0xff7779733d5f7def, 0x7ffdfdd2fdbdff7b, 0x97ff6ffecfebbfd7, 0x46f0cfdfafffdff1, 0x7bfffe79603c1b59, 0x946f1dfdfafffdff, 0xf7bfffe7fe43ebb5, 0x7deffcefdfafffdf, 0xff7bffff79733d5f, 0xfdfafffd])
  | 80 => (packedWords [0xf7ff73fff59e6fdf, 0xdfdfafffdff7bfff, 0xff7ff73fff7deffd, 0xdffdfafffdff7bff, 0xfff7ff73fff7deff, 0xa24fdfafffdff7bf, 0xe8108008c003ae5f, 0xfee6ffd7fdbfeb97, 0xfea11893bf557eff, 0x7ff3dffd7fdbffbd, 0x9ff876ffecfebbff, 0xeffbecffd7fdbfff, 0xfbfef73f05bc94ff, 0xd956f24ffd7fdbff, 0xffdffe16f968fc1b, 0xffd7fdbf])
  | 81 => (packedWords [0x6f968fc1bff5ff24, 0x7ffd7fdbfffdffe1, 0x7d8fbff7f7afffe3, 0xd3ffd7fdbffffff8, 0xf7d0fb737f427abe, 0xfdfffd7fdbffffff, 0xff7f7ff73fff7fef, 0xfefbffd7fdbfffff, 0x5b1ed8fbff7f7aff, 0x54139ffefdee7ebf, 0xb535eef6cccaab98, 0x85413dffefdee7ef, 0xfb577fef6cccaabd, 0xf8551fdffefdee7e, 0xefb577fef6cccaab, 0xffefdee7])
  | 82 => (packedWords [0xeffecfebb9b56f3b, 0x3ffefdee7eff5b5e, 0xfd869fc3e4a2990f, 0x39ffefdee7eff7f7, 0x7fef6cccaab98141, 0x1fbffefdee7eff7f, 0xf7fff6dfcbefba9d, 0xd5fbffefdee7eff7, 0xff7fffffffffffbb, 0x5fbecffefdee7fff, 0x97ef92f048c80bfe, 0xeffaffffffffffeb, 0xbb7e9f9869fc3e7a, 0xaf5fe37ffffffffe, 0xebd7f89c8facf6b3, 0xffffffff])
  | 83 => (packedWords [0x9801bc147aedfae6, 0xdffffffffebf7ef9, 0xfef6cccaabbe5fb3, 0xd3ffffffffefb7fd, 0xffd0fb737f427abe, 0xef3fffffffffffff, 0xfffd8fbff7f4a7bb, 0x413dffffffffffff, 0xffffef6cccaabd81, 0x56f3dfffffffffff, 0xfffffeffecfebbd9, 0xfeffdfffffffffff, 0xfffffff7ff73fff7, 0xfebd1fffffffffff, 0xfffffffff6dfcbef, 0xffffffff])
  | 84 => (packedWords [0xff97bfd5ffffffee, 0xbfffffffffffffff, 0xfffffffffcf7bbff, 0xf7ffffffffffffff, 0xffffffffffcfffff, 0xffbfffffffffffff, 0xffffffffffffbfbf, 0x6fffffffffffffff, 0xfffffffffffffd9f, 0xfef3ffffffffffff, 0xffffffffffffffdf, 0x7bbfffffffffffff, 0xffffffffffffffff, 0xfbdfffffffffffff, 0xffffffffffffffff, 0xffffffff])
  | 85 => (packedWords [0xffffffffffdffffd, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffff])
  | _ => 0

private def wordAt (i : Nat) : Nat := fld (wordBlocks (i / 8)) 124 (i % 8)

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
private theorem span2_0 : span (check 2) 1 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span2 : span (check 2) 1 0 = true :=
  span2_0

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span3_0 : span (check 3) 8 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span3 : span (check 3) 8 0 = true :=
  span3_0

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4_0 : span (check 4) 48 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4_48 : span (check 4) 48 48 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4_96 : span (check 4) 48 96 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4_144 : span (check 4) 11 144 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4 : span (check 4) 155 0 = true :=
  (span_join (span_join span4_0 span4_48) (span_join span4_96 span4_144))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_0 : span (check 5) 48 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_48 : span (check 5) 48 48 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_96 : span (check 5) 48 96 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_144 : span (check 5) 48 144 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_192 : span (check 5) 48 192 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_240 : span (check 5) 48 240 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_288 : span (check 5) 48 288 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_336 : span (check 5) 48 336 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_384 : span (check 5) 48 384 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_432 : span (check 5) 48 432 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_480 : span (check 5) 48 480 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_528 : span (check 5) 48 528 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_576 : span (check 5) 48 576 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_624 : span (check 5) 48 624 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_672 : span (check 5) 48 672 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_720 : span (check 5) 48 720 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_768 : span (check 5) 48 768 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5_816 : span (check 5) 6 816 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5 : span (check 5) 822 0 = true :=
  (span_join (span_join (span_join (span_join span5_0 span5_48) (span_join span5_96 span5_144)) (span_join (span_join span5_192 span5_240) (span_join span5_288 (span_join span5_336 span5_384)))) (span_join (span_join (span_join span5_432 span5_480) (span_join span5_528 span5_576)) (span_join (span_join span5_624 span5_672) (span_join span5_720 (span_join span5_768 span5_816)))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_0 : span (check 6) 48 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_48 : span (check 6) 48 48 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_96 : span (check 6) 48 96 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_144 : span (check 6) 48 144 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_192 : span (check 6) 48 192 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_240 : span (check 6) 48 240 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_288 : span (check 6) 48 288 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_336 : span (check 6) 48 336 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_384 : span (check 6) 48 384 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_432 : span (check 6) 48 432 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_480 : span (check 6) 48 480 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_528 : span (check 6) 48 528 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_576 : span (check 6) 48 576 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_624 : span (check 6) 48 624 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_672 : span (check 6) 48 672 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6_720 : span (check 6) 19 720 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6 : span (check 6) 739 0 = true :=
  (span_join (span_join (span_join (span_join span6_0 span6_48) (span_join span6_96 span6_144)) (span_join (span_join span6_192 span6_240) (span_join span6_288 span6_336))) (span_join (span_join (span_join span6_384 span6_432) (span_join span6_480 span6_528)) (span_join (span_join span6_576 span6_624) (span_join span6_672 span6_720))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span7_0 : span (check 7) 48 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span7 : span (check 7) 48 0 = true :=
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
  have foundRoot := span_ok rootOK s hs5 (show s < 5 + 4 by omega)
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at foundRoot
  exact bar_all (ori := id) (pool := []) (fun h => h) checked s hs _ foundRoot.1
    (Run.perm foundRoot.2 valid)

theorem lower {bound : Nat} (fit : HasCircuitSize 6 target bound) : 9 ≤ bound := by
  by_contra! tooSmall
  have hnc : ∃ x y, target x ≠ target y := ⟨pt 6 0, pt 6 5, by decide +kernel⟩
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


end Monotone15670Lower

end

section

namespace Monotone15670Control

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[
  ⟨.and, [0, 1]⟩,
  ⟨.or, [3, 4]⟩,
  ⟨.or, [4, 6]⟩,
  ⟨.or, [5, 7]⟩,
  ⟨.and, [3, 8]⟩,
  ⟨.or, [2, 10]⟩,
  ⟨.and, [1, 9]⟩,
  ⟨.or, [0, 12]⟩,
  ⟨.and, [13, 11]⟩
], 14⟩

theorem monotone : Monotone2 circuit := by
  intro gate mem
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 15000000 in
theorem exactTable : ∀ x : Fin 6 → Bool,
    circuit.eval (List.ofFn x) = Monotone15670Lower.target x := by
  decide +kernel

end Monotone15670Control

end

end PEqualNP.Outside.L_meta_15669_aux

open PEqualNP.Outside.L_meta_15669_aux

open PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_15669 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4007717088 * 2 ^ 32 + 4007717024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4007717088 * 2 ^ 32 + 4007717024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have budget : 9 ≤ s := Monotone15670Lower.lower h
  exact ⟨Monotone15670Control.circuit, Monotone15670Control.monotone, budget,
    Monotone15670Control.exactTable⟩
