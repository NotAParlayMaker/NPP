import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_15867_aux

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

namespace Monotone15868Lower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoreTable7402_aux

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4008372970 * 2 ^ 32 + 4004162208)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

private def k : Nat := 63
private def rows : List Nat := [36, 36, 1, 22, 42, 14, 3, 14, 42, 56, 12, 44, 50, 3, 34, 48, 32, 24, 60, 14, 50, 18, 6, 28, 4, 52, 3, 1, 3, 22, 50, 42, 3, 22, 60, 22, 14, 50, 42, 3, 60, 50, 42, 14, 3, 3, 50, 60, 22, 42, 60, 60, 14, 42, 3, 22, 14, 50, 14, 60, 22, 14, 42, 37, 38, 5, 30, 58, 46, 7, 30, 43, 58, 13, 46, 58, 35, 38, 49, 33, 26, 62, 15, 54, 26, 38, 30, 5, 54, 11, 17, 19, 23, 9, 17, 33, 5, 5, 33, 9, 5, 33, 17, 17, 17, 38, 17, 26, 38, 26, 9, 38, 9, 38, 26, 38, 26, 9, 26, 33, 38, 5, 33, 17, 26, 5]
private def inputs : List Nat := [(packedWords [0x804030811c002044, 0x2ea145fffe84d2a2]), (packedWords [0x77f37efbf47871f8, 0x115eba001b7f3dfd]), (packedWords [0xbd9d891e23cc0cab, 0x230a921311ee2677]), (packedWords [0x6d3e8d54808e0fb0, 0x1075680822570fdc]), (packedWords [0x1a8dc32e62b69208, 0x18542dc05d5b494c]), (packedWords [0xca2ec764c215db13, 0x58a9224812afd99])]

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
  | 4 => 40
  | 5 => 473
  | 6 => 580
  | 7 => 48
  | 8 => 1
  | _ => 0

private def stateWidth : Nat → Nat
  | 4 => 49
  | 5 => 58
  | 6 => 67
  | 7 => 67
  | 8 => 58
  | _ => 0

private def hashBlocks : Nat → Nat → Nat
  | 4, 0 => (packedWords [0x4740bce01f921af, 0x1b53835209822f27, 0x2f1c73221fa21869, 0x35de639032b82e02, 0x490591c43bb91337, 0x5a472aec56e8ab77, 0x61c1da32604033dc, 0x71cbb1b16f51dc03, 0x7f89c4cb7ecc36bc, 0x92628cc0918a58e6, 0xa26794be964837a1, 0xb06fa320a795cc7c, 0xb1170f9bb0c1182e, 0xb4722320b3691485, 0xb9f1dc9db73528e6, 0xc1a98b27bcee5c52, 0xc9626d43c7f4ac54, 0xcf0b3a20cc68b70b, 0xdfff0d0fd6628ab3, 0xf9fa6fcae7334ab2])
  | 5, 0 => (packedWords [0x190f51b012c7f44, 0x21bdf3201c48c6c, 0x48b576d0395d0af, 0x62c31d704bd1857, 0x6a2976b06947bc7, 0x722f09e06bf3ed4, 0x72b136a0727b3a1, 0x88b307a08213ad4, 0x94b2f7e08ca4083, 0xb9639be0a2ebf0f, 0xc0f6ab90c0b0b9a, 0xe032a2d0c74fbcf, 0xef9e0870e0c9a8c, 0xf42a2430f20fc81, 0x10a099a60fc26fd0, 0x1356914e13102b68, 0x14226de113c1ac15, 0x155c58a4146a54a8, 0x160ed68015b54a09, 0x1678050f163856a9, 0x173a02ed16ad2b7b, 0x179f348a1786d393, 0x18d4131217fbf41f, 0x194b8f9f193cf2f4, 0x1a3c4fdb19db2b92, 0x1b2417fe1ab946a2, 0x1ccd8d321bc5ddab, 0x20e179611d8afa21, 0x218d303d213a4d98, 0x2330f05f21ffdfd0, 0x237baeaa235d9a7c, 0x24081a5c2389444d])
  | 5, 1 => (packedWords [0x24bc954c24122402, 0x252cc46c24e9c05c, 0x25f3ea0e25f18cd3, 0x2679632926242701, 0x2770d1f426e45212, 0x288af9812830f510, 0x294df5ed28e555c1, 0x2b9fb3e32a33a15b, 0x2fffb3de2db11267, 0x33fba90131221ff1, 0x35bee8bd355cbefc, 0x368aa7b935cc5b85, 0x3767535c36eaed91, 0x378395de376abb1e, 0x38c8783f38bb3e71, 0x3915e28839053f0e, 0x3af8dd4c39cafa95, 0x3bb8c85f3b0ac7ad, 0x3c652a243bd36a02, 0x3fc408d13d263428, 0x40480f4e3ff383d1, 0x40c458034051d793, 0x42ade95d41ea832c, 0x430e9b5042f13ae0, 0x4358b72b4335c348, 0x440e9b7443b3ade0, 0x450ee5af4488a1f2, 0x452c899845294b6d, 0x46212554461ee96f, 0x482657ec47da6ebe, 0x4b76e44749901653, 0x4c3ba18e4bf0606b])
  | 5, 2 => (packedWords [0x4e0478cc4cf5990a, 0x4efa2d684e768fc4, 0x503eb2bc4f41dda3, 0x51748c0750d6981e, 0x5196c32f51866f15, 0x5485f63f53cf5b4b, 0x54f2a6c054bf70ed, 0x5516931655051f7c, 0x55b1e1d5557833aa, 0x56443f6155fe99a0, 0x56ea242556bfc1fa, 0x585825fa582baee1, 0x58ae4eb55891f801, 0x58f7859358e1b1b6, 0x5987ccd759413d6c, 0x5a91e7fe5a57db3d, 0x5cd7291d5b18064e, 0x5ea09aaa5e6ea4db, 0x5f2b4d645f190753, 0x5f775bbe5f5da4c8, 0x5feabe4e5fa5f3b5, 0x624cc2d8604e28f0, 0x62f40af062afb20f, 0x6449abe363274287, 0x65be9a1a64c97970, 0x6753223d673b6ce8, 0x6855c6f167fa7d52, 0x688e7e26688d3808, 0x69d5c08a68d5ec02, 0x6a2f453f69e285fe, 0x6a4c7ba46a43aefd, 0x6b8679766b128ec5])
  | 5, 3 => (packedWords [0x6bf4dde06ba6a394, 0x6cf313226cee8adb, 0x6dcc56c46d584347, 0x6e49f5d06dd0b5e3, 0x6eda55096e529a30, 0x6f51dc036f0b961f, 0x6fbf34506f938bde, 0x7099c4e86fc883a9, 0x718ac5347109de0a, 0x727e729571c99432, 0x732b0a9e72ea458f, 0x746adf68743819c4, 0x748f2421748cb4a7, 0x74f297ff74aa7ce3, 0x77769533776509ca, 0x77d021aa779fe99d, 0x787e648677f0e1e6, 0x78d6534078c4264d, 0x78fb4e1778e40fe6, 0x79607fb47954f01e, 0x79b5e2a179980b8d, 0x7a9e70097a955e3c, 0x7cc6e9397ca3ce46, 0x7d3c60057d239bd3, 0x7ecc36bc7e52b34b, 0x7f23a6857efeca8e, 0x826c4d6a80905449, 0x8325ac3882fea9f7, 0x84152dd08354c15c, 0x846cc9a7841e8cfb, 0x860cf1d1854a8f77, 0x86a3be6c86679269])
  | 5, 4 => (packedWords [0x87bbb59c870d925f, 0x883b83298827e194, 0x886d2ff98866ca12, 0x89cca8ed890ffe30, 0x8a78562d8a18a73f, 0x8ca2208a8b0f4117, 0x8d4b2c338cf3d7d6, 0x8eb4d5e58d980d34, 0x8f532ffa8f3cb6f1, 0x9200ff9d8f725d91, 0x92853ae7925b1375, 0x941a9c0d92b15e02, 0x95efea9195545aa7, 0x9687ed1896355b4b, 0x9781684a968df3e8, 0x980cedb697d39c74, 0x99b45add98eb71c9, 0x9a89c36999f7ecaa, 0x9bbd05b89b3cad1a, 0x9c4e4bb49c3cd345, 0x9fd799f69c8322b2, 0xa0694609a01cf6cd, 0xa18553fba06a2aac, 0xa2a25031a2095a78, 0xa46f3487a2e365e1, 0xa4e14c3ca48b7335, 0xa561a56fa4e2c9ca, 0xa574f90aa5666872, 0xa5e88e4da5d8a22e, 0xa708f554a610dae3, 0xa832b0cba7bc595d, 0xa963cb88a93ec478])
  | 5, 5 => (packedWords [0xac0289edab2d9803, 0xad346b00ac23b2ea, 0xada2f6f4ad6c19c6, 0xaeedf524adeb224a, 0xb01e4b8cafd7d09f, 0xb12a9696b0fc9151, 0xb195461fb154a396, 0xb212fc58b19cfe6f, 0xb2884c1bb2578e42, 0xb2ff6290b2b6eb0b, 0xb456f968b4337d3e, 0xb5d63b41b4a205c8, 0xb7733559b7732cff, 0xb7fd9d50b7c755cd, 0xb8839970b8058a8b, 0xb8f7fb73b8a9f6a1, 0xb975d5eab94323e3, 0xbb491801ba197124, 0xbcaba853bc75418d, 0xbd8b11e0bcee5c52, 0xbff61b86beb38091, 0xc17ee06fc0e48bdb, 0xc206ca08c1f030bf, 0xc328752dc27fc9ee, 0xc462dbd2c3b4a190, 0xc5a19e0fc4f6a9d7, 0xc66215e7c6066a67, 0xc77fe544c769943c, 0xc93305c9c872562c, 0xc9e67423c9bcf961, 0xcc68b70bca2a09cf, 0xcd9ccbebccd3d9ef])
  | 5, 6 => (packedWords [0xce295d57cdb9ada6, 0xd1e14047d13bd169, 0xd28b8a93d1e3d4db, 0xd2980a0ad292623b, 0xd3728a50d320e945, 0xd3ebfcf0d39ed4e7, 0xd44e3bb3d40027f8, 0xd529a262d4626063, 0xd8c576c5d5a96fef, 0xd8e725ccd8de5d86, 0xd9e6ab0fd9d8e64b, 0xda74fc16da3fafb0, 0xdaafa61adaa13b32, 0xdb163b48dafa60ff, 0xdb589972db1f39ec, 0xdc0ccdb2db5ae0c7, 0xdefdab2fde908c64, 0xdfcce401df65fee9, 0xe181f421e10f2c9f, 0xe1d61495e1c86a64, 0xe4bff521e3ea63a2, 0xe533a707e5215309, 0xe619238fe5a96e05, 0xe7370ac2e6c7d92b, 0xe79f4960e796e388, 0xe9fbcc76e7cecb24, 0xea28153cea27b478, 0xea88a48dea552a86, 0xecb54495ebdf12d3, 0xecd392c7eccd0171, 0xecf2435cece459a3, 0xee437946ee05c658])
  | 5, 7 => (packedWords [0xef154cefeed383a3, 0xf0b8db84f06f0c26, 0xf1b875c6f1147b24, 0xf2fe25bef20e101c, 0xf3c62c87f37f561f, 0xf47c6d78f3cd6988, 0xf7206687f66a63b2, 0xf7fc0c1ff7b135bb, 0xf896900ef82954f0, 0xf9c58712f8f16a83, 0xfa460405fa3a1ea3, 0xfd08cebdfbb77c74, 0xfe446ddc])
  | 6, 0 => (packedWords [0xf31b500012d4ca, 0x1abaa00018aabce, 0x1f53e6201cfacc3, 0x32f625d0214aa8f, 0x4bedfc7049f16d2, 0x65571ec059592a7, 0x722f09e06b7f047, 0x7b9281007596946, 0x89ed2200864c3f9, 0x8f0cc3008ca4083, 0x9ba3e4109507089, 0xae6e43b0a80ab21, 0xb9639be0b7ce81f, 0xc0a6f730bba89df, 0xdcbff980d09438f, 0xdf21c420dd1211c, 0xe6185cd0e15969f, 0xe93cbb30e8a59e4, 0xf0652610e9c8f88, 0xfd5f4cf0faea879, 0x114c8459112604b9, 0x132d15441258ceac, 0x1464dbbd13363481, 0x14cc8dea14b8fc31, 0x14ede52a14d77fb0, 0x16dd0be41619689e, 0x1708909016eeb4ad, 0x174f55e71745493b, 0x19e056b717d03166, 0x1a3641371a24986e, 0x1b2543de1af081aa, 0x1be907251b65d226])
  | 6, 1 => (packedWords [0x1c7a02ae1c3dca3f, 0x1cb6205c1c94103f, 0x1dc31f721d0d42b1, 0x1edea6fa1df51ac0, 0x20b5cbec1fd5cad6, 0x2121fce220c08dd2, 0x213a4d9821250446, 0x22519775213e87ed, 0x22ce1d782279e177, 0x2412240222eca2fe, 0x243e1ed8241d700c, 0x24e9c05c24767d4e, 0x26242701258d0229, 0x2710a73c265523d3, 0x282e53d8273090be, 0x28772d002854b6f9, 0x29bf83aa298d1476, 0x2bd1d1f02ade5c00, 0x2db118a02c77e2db, 0x2e338a612df3135f, 0x2ed99aa92ecdb815, 0x2fab5b962f862c6d, 0x302ec7272fe58405, 0x318861b230610146, 0x31ccf40c31c6c0a1, 0x333a4fd232f2e9d0, 0x3510b866333fb522, 0x35dfc0cc354e4586, 0x36eaed91367df105, 0x3746695e371c8710, 0x37efebf0376abb1e, 0x3973544438b32933])
  | 6, 2 => (packedWords [0x3a72911a39a59a1b, 0x3ac5aca43a82909b, 0x3b7454f13b3d8acb, 0x3bd350843bcecaa4, 0x3d145c043ce642cb, 0x3d521b403d2b044e, 0x3e3c1c5a3d780bff, 0x3f5a84653f00316b, 0x4051d7933fcebf8a, 0x4125c4ba408eea9b, 0x42ab69da4135292b, 0x4398d68742ade95d, 0x43f4584143a0e6b0, 0x4552b67f445177f2, 0x48d7530047440ef6, 0x49901653491f976c, 0x4aa4ac264a23648b, 0x4d2b5faf4bbbf482, 0x4dee0c9c4d336a0b, 0x4e71b04d4e5e6583, 0x4fd69f264e7fa163, 0x50d6981e50c9100e, 0x516d836051588074, 0x529906f251e7eece, 0x53ce775453c6b4aa, 0x547ed64b542e1fd4, 0x54bf70ed549cc845, 0x55367947550f4149, 0x55709b1355454c84, 0x56837f6256443f61, 0x57c7f7be56b9ad9c, 0x58e1b1b6582baee1])
  | 6, 3 => (packedWords [0x5991939e598c5d04, 0x5a3d5cf359c36ae1, 0x5adef0275a57db3d, 0x5b5085a85afd8804, 0x5ba4eed15b85b62b, 0x5bebf6025be5ad31, 0x5c715eb25c6878c6, 0x5e57f01b5d97c50a, 0x5e88a51d5e829b7a, 0x5f90e5a05ee65eaa, 0x61adb47e60335281, 0x627b04eb622e8275, 0x62c16e0c62819641, 0x65121d7c63640a95, 0x65be9a1a65bcf94f, 0x66a143356674c4bd, 0x66f96df066af6df8, 0x6859518067928534, 0x691d348368f27c7f, 0x6989b49c697f69b6, 0x6a4c7ba46a2d48ee, 0x6b2184516a5c3cdd, 0x6b3e63b16b2d25a0, 0x6bdbbdd16bb05aa1, 0x6c97884e6c4bf67a, 0x6dd0b5e36d4a4137, 0x6e8e6a946e83a45c, 0x6f942f176f3f9e8d, 0x70efe74370819c86, 0x72215cfd713b1535, 0x72a6f068727570f4, 0x7322966972e7aec6])
  | 6, 4 => (packedWords [0x739e5db07336eff8, 0x74b1ce5e73e58dfb, 0x7638c23574c9c96d, 0x7756d5e276d4216f, 0x7906946577769533, 0x79c8be2e79360446, 0x7a0c58e879d52234, 0x7a7ec1037a6f854a, 0x7bf4ea8a7b4f575c, 0x7cb1ccd47c8c8838, 0x7cc6e9397cb65671, 0x7d271d507cf2e5f1, 0x7da5e3a67d4ebb66, 0x7e205d347db79157, 0x7f21f8ca7eff5114, 0x818a9325803b0ad5, 0x835ab9b582ad0d43, 0x843b2ca1841cc0a6, 0x8456cc20844e1818, 0x84fb57b284b39555, 0x8608a5d185c628b0, 0x875ba967874e4d53, 0x88204318879f8a0b, 0x89093aa388f4a5ea, 0x89a1ab888977e09d, 0x8a78562d89a2a991, 0x8aa6a0eb8aa69d53, 0x8af6835c8ae42c5c, 0x8c2a93488b0f4117, 0x8d1559c68c5408cd, 0x8e5de41d8e2463a9, 0x8ea315f18e9aa4f3])
  | 6, 5 => (packedWords [0x8f725d918ebc967c, 0x8fcb03aa8f7263ca, 0x916a238690f6b6bd, 0x918c1335916ca6c0, 0x91eab0a191a9b6fc, 0x91f0125191eaff54, 0x93905a3192886288, 0x94ea7dc894696f10, 0x957b8efe9533e8c6, 0x965df25c95e5d8c8, 0x99a9802b9907b488, 0x9a39fd1999e7fb05, 0x9b5554a49a89c369, 0x9c11128a9b66e545, 0x9e65905d9d0e352a, 0x9ecbe05c9eb5308d, 0x9f49e5689ee36963, 0xa02462d79f9bd957, 0xa0c3fc18a0914fa4, 0xa13cf7b7a1111d31, 0xa19668aba18553fb, 0xa2ce4e8ba19bcc20, 0xa3636675a2e70fe4, 0xa4e143e4a46f3487, 0xa561a56fa555f84c, 0xa593e6caa574f90a, 0xa6f5c4bca655462d, 0xa796e75ca76f9c3e, 0xa945104ea93f1f39, 0xac32e92aa972c60e, 0xacac5064ac544b70, 0xae688d15acc9a90d])
  | 6, 6 => (packedWords [0xaf5cf204aedf2b2e, 0xb0f0dde8b01e4b8c, 0xb2744301b25b70a5, 0xb2f8dcd1b28cae35, 0xb45a521cb4474b49, 0xb52d697eb51bc0b5, 0xb5533ad3b53f363c, 0xb6fda458b6cf4c78, 0xb8058a8bb752710b, 0xb8582fbcb82146f6, 0xb93b83a8b8892bcb, 0xba1a70d7b9513efd, 0xbb0dc5eeba27bbf6, 0xbc335c89bc02ed3d, 0xbd8053febd1d5bcb, 0xbdad412cbd8b11e0, 0xbe568c29be32a9dc, 0xbec18c96beb8fe5d, 0xbf60b1b3bf25aa44, 0xc0e48bdbbfefbb52, 0xc1d06bc8c183b1ff, 0xc269dd31c25636eb, 0xc3226348c27ec215, 0xc4a43ce3c3dc2240, 0xc6936bcac60c43d4, 0xc77e4479c74aed79, 0xc7bb2bcac77fe544, 0xc828d45dc7cbc947, 0xc91d10d1c8360fe7, 0xc953d05ec928a180, 0xc9ef5a02c96f57dc, 0xca1a9caaca09714b])
  | 6, 7 => (packedWords [0xca8c1ea0ca38cc37, 0xcb2fac7fcac1e5ac, 0xcca1b832cbaeafc5, 0xcd193360ccd3d9ef, 0xcd943da8cd7d1573, 0xce1b11dacddbb28d, 0xcea05e73ce1e1632, 0xceec3a65cec68542, 0xcf798e9ccf470149, 0xd045ce36d0203c9b, 0xd1319ea1d0c7558d, 0xd17904a3d15850ab, 0xd1e750c7d17e5b06, 0xd2801101d2079dbd, 0xd2ddf605d2b1326d, 0xd3d10f4ad3ad254f, 0xd4683b92d4660f36, 0xd4b62e4cd495cc3a, 0xd70875ffd5971ab3, 0xd7b20915d7970590, 0xd857b727d830be27, 0xd930b95bd8956c99, 0xd9b7e709d976e90b, 0xdaa13b32da3fafb0, 0xdb5272c0dafe5652, 0xdb90d011db87e343, 0xdd10a286dcf4a406, 0xdd58c06add345ea6, 0xde0442c1ddbef2c6, 0xde3a40e9de0d745b, 0xdfa4758edefdab2f, 0xe0175297dfb102f0])
  | 6, 8 => (packedWords [0xe0c09c3ee02e344d, 0xe2cd2175e1ef676e, 0xe4538339e3595377, 0xe46bd4ade457bcd6, 0xe5ed177ce4bff521, 0xe65d44fee5f68c87, 0xe67c0303e66d4b4c, 0xe783a134e69938b6, 0xea28153ce91cf491, 0xeab5f114ea373e63, 0xebf71629eb6c343d, 0xec67e87dec36231c, 0xed9a84e3ec953501, 0xee862026ee1553f7, 0xefac3831ef22e4ce, 0xf03d7e84efdee3f5, 0xf064611bf0435d09, 0xf26cd4a5f0f864df, 0xf2b801e7f27a7461, 0xf36b0226f2fe25be, 0xf398f882f3837ed4, 0xf3b7d7eff3ac4a7e, 0xf551a55bf4293980, 0xf677b26ff5b7663b, 0xf6b28eb0f6a037b0, 0xf74430f1f6c97ccd, 0xf7b135bbf7ac11e3, 0xf8021fb2f7cb11d5, 0xf87c11c4f81f3d86, 0xf985f9daf94f019b, 0xfb13b94ffa1fa059, 0xfc4fa56efbd679db])
  | 6, 9 => (packedWords [0xfcd6e403fc99602f, 0xfe446ddcfd7a0870])
  | 7, 0 => (packedWords [0x16dd0be40e15969f, 0x2854b6f916eeb4ad, 0x2ade5c00298d1476, 0x333a4fd232f2e9d0, 0x3d521b4039735444, 0x42ade95d3fcebf8a, 0x516d8360445177f2, 0x598c5d04542e1fd4, 0x5a3d5cf359c36ae1, 0x790694655d97c50a, 0x7d271d507cb1ccd4, 0x874e4d53843b2ca1, 0x91eab0a1916ca6c0, 0x9907b48891f01251, 0xa46f3487a2e70fe4, 0xc77e4479bdad412c, 0xca1a9caac953d05e, 0xd4683b92d2b1326d, 0xdd10a286d8956c99, 0xe46bd4ade0c09c3e, 0xee1553f7ec67e87d, 0xf2b801e7f064611b, 0xf3ac4a7ef36b0226, 0xf81f3d86f551a55b])
  | 8, 0 => 0xa46f3487
  | _, _ => 0

private def packedBlocks : Nat → Nat → Nat
  | 4, 0 => (packedWords [0x18ab7cb545da8c55, 0x28743157837c95b5, 0xadf18a9e26adf2a7, 0xa4b7ca73fd30525d, 0xf699616f94e7c278, 0x5f252c54f2df2a6f, 0xb7cb33fd8a9e5e0, 0x891616f97662a4cb, 0x46d4ff4f2fb3ab53, 0xba7be45dd2c55f66, 0xc1496f9537a314ca, 0xdfedc4f2df2a6ff4, 0x7ca9be13c525be54, 0x9617397c893798ab, 0xf098292efb4b7c62, 0xca9b1526725be54d, 0x156f95387b14b0b7, 0x4c52c2df28aff6d3, 0xbe3fd8a4d5ea54e2, 0x56f9458fb153cb98, 0xe962ae92f8ff7331, 0x53fd8a9e5ce5f256, 0x6f953629e0e8b90b, 0xe62adf29cff4c161, 0xe0e9ef8d])
  | 4, 1 => (packedWords [0x44ab7cbbb14f0585, 0xf84f1617597c7fb1, 0xe581e8c52c2df29c, 0xb0bcabe3153c255b, 0x64f1616f94e7c260, 0x5f1fe9e2c2df2a71, 0xcd])
  | 5, 0 => (packedWords [0x5b837c7fb518a586, 0x586be54dfec53c19, 0xf161b837ca9b1526, 0xb0526be54e06c54, 0xda62895af9537fa6, 0x9bfd3c586be54dfe, 0x5fec54f161b537ca, 0x7ca73fd30586be57, 0xe54dfac54f161bd9, 0xaf9538fb698a586b, 0x86be54dfec54f149, 0x161af9537fb153e5, 0x3c586d45f2a6ff4f, 0x37f961bd97caa3fd, 0xbfd8a9e6f6732f95, 0xfec54f161af967a9, 0xca9bfd8a286be52d, 0x54dfee24f161b997, 0xd97ca93fd3c586be, 0x6f65f2d4ff4f095b, 0x61af9537fb152458, 0xc256be535fec54f1, 0x4f161af9538fb153, 0xa93c586e0df1feb6, 0x5107f961af9537fb, 0x8d3fd3c726be54e3, 0x4dfeaf4f161af953, 0x9537c278b0526be5, 0xbe54dfec54e161af])
  | 5, 1 => (packedWords [0x1af9487fb153c586, 0x586cbdf2a6ff6296, 0xf161af9537fb0d3c, 0xd3c656be54decc54, 0xf84f161bd97ca9bf, 0x13153c586f65f29c, 0xe46ff62961af9538, 0x7cb03fd8a586be54, 0x65f2a6ff4e961baf, 0xbb37cbb3153c586f, 0x86f65f2a6ff4f165, 0x961b497c7fb15265, 0x3c586f65f2a6ff4d, 0x54f161af9537fb31, 0xb153c3a5cddf1fec, 0xa6ff629f9801457f, 0x37fb1530526c4df2, 0x5f2a6ff4f161af95, 0xf94e7fa7908586d9, 0x6be54dfeae4f161a, 0x51af953883d18a58, 0xc586be54dfec54f1, 0x4f095af9537fac53, 0x1526586be5aa2ec5, 0xec54f135af95388b, 0x7fb153c586d3df1f, 0x4e2eb84f161af943, 0x97ca9bf13c586be5, 0xe0df256c54f095bd])
  | 5, 2 => (packedWords [0x1b417ca9bfd3c586, 0x586be581fec53f16, 0xf161af9537fb1526, 0x53c4d6be54e5aff4, 0xc54f161af9357fb1, 0xfb153c586da5f2a6, 0xdfebf4f161af9697, 0x7cb4bfd8a9e6be54, 0xe54dfec550161b27, 0xaf9537fb153c476b, 0x86be4f9fec54f161, 0x161bd9d5a9bfd3c5, 0x3c526f65f2a6f44f, 0x53c161af9537c315, 0xbfd3c586be54e22c, 0x18ff62961bd97ca2, 0x37fb153c626be54e, 0x501fec54f161af95, 0xab7ca9c498a586be, 0x6be54dfec24f161b, 0x61b21537fb153c58, 0xa586be54dfeb44f1, 0x4f161af953883fd8, 0x153c726be54e0ec5, 0xec54f095af9537fb, 0xb53fd8a9e6eedf1f, 0xf2a6ff4f105b237c, 0x9537fb515e586f65, 0xd1df1fec54f161af])
  | 5, 3 => (packedWords [0x1af9537fb013c586, 0x586be5d98a9e4216, 0x2961b4f7c8bb153c, 0xd3c586d3df2a6f46, 0xc54f161b857ca9bf, 0xfb998a936be569fe, 0x2a7114f161af9537, 0x537fae93c586f65f, 0x65f2a7004f161af9, 0xaf9537fb153c4d6f, 0x86be54dfe982c0a1, 0x161af93d7fb153c5, 0xee586f65f2a6ff4f, 0x54f161af95389314, 0xb153c586ccdf1fec, 0xcf537fb15b9f537f, 0xc9fbfd3c586cc5f2, 0xdf2a6ff62961bd97, 0xf9537a3a58a586dc, 0x6be54e4ac54f161a, 0x61af9537fb153c51, 0x29e6be54e50c54f1, 0x4f161af95395bfd6, 0x153c586be555fec5, 0xec546961af9537f3, 0xa9b153c586be54df, 0x4dfec54d161b6b7c, 0x95393b153c586be5, 0xbe54dfead4f161af])
  | 5, 4 => (packedWords [0xdaf9537fb153c5f6, 0x586be54dfec54f12, 0xc161af9517fb153c, 0x526586be5d98a9e3, 0x9e2c0a1af9538931, 0xfb698a586be54df0, 0xdfec54f1d1af9537, 0x7c7fb798a9e6be54, 0x9df2a6ff6d315b39, 0xaf9537fb153c556c, 0x86be54dfeeb4f161, 0x161af94e7fb153c5, 0x3c586e05f1e8c54f, 0xc4f161af9587fb15, 0xb918a416be54e56b, 0x9cff4f149af9537f, 0xa7fb153c4d6f65f2, 0x5f2a6ff4c161af96, 0x1d7a9c458a585f6, 0x6be54dfec54f1318, 0x61af9538bb153c58, 0xc4a6f65f2a0ff4f1, 0x7fa796f9537fb153, 0x14f0586005f2a72a, 0xec54f161af953893, 0x7cb153c586be505f, 0xf2a6ff4f15daf953, 0x9538fb153c586f65, 0xbe54e4cff62a79af])
  | 5, 5 => (packedWords [0x5b277ca9c7d8a9e6, 0x586cc5f1fec52c09, 0xf961af9537fb151c, 0x53c586d0662f9537, 0xc44f161b7b7c7fb1, 0xfb918a586be54dfe, 0xdfec54f161af9537, 0x537fb758a9e6be5d, 0xe529fec54f161af9, 0xaf9537fa60b0316b, 0x86f2df2a6ff4f161, 0x161af9537faf53c5, 0x8a586df5f28ac54f, 0x62961b3195be3fd, 0xb153c726ecdf2a71, 0xa6f84f161bb37ca9, 0x17fb153c256f65f2, 0xdf2a6bb4f161af96, 0xf9427fb153c586e0, 0x6be539fec54c161a, 0xc5af94f7fb153c58, 0xc586cc5f1fec52c0, 0x4f161af9537fac13, 0x153c586c3df1fec5, 0x6c54f161af9547fb, 0x7fb6d8a9e6be54e2, 0xf2a6ff62961af953, 0x97ca9bfda8586e65, 0xbe54dfee562a79bd])
  | 5, 6 => (packedWords [0x1af9537fa7930526, 0x586be54dfec54816, 0x3961af9537fb393c, 0xd3c586be54d8a933, 0xc54f161af9537fac, 0xfb153c256be549fe, 0xdfee24f149af96a7, 0x7c7fb153c586be54, 0xe581fec53c161b81, 0x7117ca9bfd8a9e6b, 0x16005f2a6ff4c149, 0x161b4f7c7f9f8b03, 0xb0316be54dfeb84f, 0x54f109af9537c278, 0xb153c446be54dfec, 0xfeb54f161af9537f, 0xba9bfcfc286be54d, 0x54df4c54f161af97, 0xf9497fb153c586be, 0x6d2df28aff62961a, 0x61af95394bd18a9e, 0xc656f4df2a6ff4f1, 0x4f161af95388b153, 0x153c4d6be54e1cc5, 0x6ff4f161b837c7fb, 0xa9bfd8a9e6e3df2a, 0x4dfec54f195b0b7c, 0x9537fb153c456be5, 0xbe539f0c54f161af])
  | 5, 7 => (packedWords [0x9b7d7ca9b153c586, 0x586f6626f9537fa7, 0x961af9537fb053c, 0x58a586be54dfec55, 0xc54e961af9537fb6, 0x9be130586be54dfe, 0xdfec54f165bd97ca, 0x53833153c586be54, 0xe54e2ee962a79af9, 0xaf9537fb1536586b, 0x86be51dfec54f161, 0x161af976883fd8a5, 0x3c726be54e34ff4f, 0x37f961af9767fb15, 0xbfd3c586f6662f95, 0xa6f84f14974d7ca9, 0x37fb153c496005f2, 0x54dfec54f175af95, 0xf9538bb518a586be, 0x6ea54dfec54f161a, 0x95bd97cb03fd3c58, 0xa586be54dfed74f1, 0x4f16daf9537fb458, 0x4d8a586be54dfec5, 0xcc54f161b6b98be5, 0x7e3153c586be54e3, 0xf2a6ff62961af953, 0x9537fb153c5e6db5, 0xbe59dfec54f095af])
  | 5, 8 => (packedWords [0x1af953a73fd30586, 0x586be54e20c54216, 0x21c9b4b7ca9bfd8a, 0xd3c586be54d8a9e4, 0x537fa79bd97cbb3f, 0xfb1546586d05f2cf, 0x1feb44f161af9537, 0x537fb153c536ce5f, 0xe54dfebb4f161af9, 0xaf9537a3153c586b, 0xe6be54dfec54a961, 0x161b2b7cb3bfd8a9, 0x8a9e6be5a5fee24f, 0x93f0a1af95394bfd, 0xb153c586be54dfee, 0xa6ff4f159b397c95, 0x57fb153c586f65f2, 0x5c1fec54f161af94, 0xf9677fb153c316be, 0x6be54dfeca4f161a, 0x61af9537fb153c5a, 0x8586be54dfee95b1, 0x4f161af9537fb152, 0x518a256f6672f8ff, 0xcf84f161af96a7fb, 0x7fb153c3a6be54e9, 0xf1fec54f161af945, 0x57ca9bfd8a9e6d25, 0xbe54dfe9e3f149b0])
  | 5, 9 => (packedWords [0x1af9537fba18a4d6, 0x646be54dfec55416, 0xf105af9537fb153c, 0x53c586be54dfec54, 0xc53c161af94c7fb1, 0x2a78f0726be54e20, 0xe28c54f161af9536, 0x7ca9bfdbc9e6be54, 0xe54e34f84f161bd9, 0xb9989be54dfec56b, 0x86be54dfef84f149, 0x161b4f7c7faf13c5, 0x3c586be54e22c54f, 0xf4f161af95380315, 0xa7908286ef5f2a6f, 0xfec54f161af95395, 0x37fb153c4f6be54d, 0x5f2a6fd4f161af95, 0x797ca9b153c586f6, 0x6f65f2a6ff4f149b, 0x61bd97ca9bfd3e58, 0xa586be4fdfec54f1, 0x4f161af9537fb154, 0x795a9e6de5f27ec5, 0xf537fa79af9537fb, 0x7bb153c586f65f2c, 0xf2a6ff62961af953, 0x1357fb153c4d5d15, 0xebdf2a6ff6299580])
  | 5, 10 => (packedWords [0x9bd97da9bfd3c586, 0x586be54dfee95da7, 0xf161b397c89314f0, 0xd3c586be54e22d74, 0x9e2c0c5b877ca9bf, 0x3d4d8a9e6d05f1fe, 0x2a6ff6f315b6b7cb, 0x5c7fb153c586d3df, 0xe54dfed74f161af9, 0xaf9457fba58a9e6b, 0x86ce5f1fee962961, 0x161b937ca9b14f05, 0x8a586f65f2a6ff4e, 0x74f161b577ca9bfd, 0xbfd3c586be54dfee, 0xfec54f139bcf7ca9, 0x3893798a786be54d, 0x54dfebe4f161af95, 0x1a6be3fd3c585be, 0x6be51656ff62a798, 0x61af965a9bfd8a9e, 0xc526be54dfec5511, 0x3f195af94e7fb153, 0x153c656be54dfec5, 0xee26d161af9607fb, 0x7fb1530586be54df, 0x4ddec54f161af953, 0x1d5a9c498a585be5, 0xf65f2a6ff4c14980])
  | 5, 11 => (packedWords [0x1af94e7fa7930586, 0x586dfdf2a6ff4f16, 0xf15daf9507fb153c, 0x526586be54dfec54, 0xe662a79af95395b1, 0x73fd30585be54dfe, 0xdfebc4f1618017ca, 0x537a314b01d6be54, 0xe54dfec548961af9, 0xaf9537faad3c586b, 0x86be54e3ee24f161, 0x135af9537fb154c5, 0x3c586be5a5fec54f, 0xf49961af9768d3fd, 0xb5d30586f65f2a6f, 0xd2ff4f161af9537f, 0xca9bfd3c586f65f2, 0x559fec54f161b5b7, 0xf9697fb153c286be, 0x6be54dfeb94f161a, 0x61b6b7c62a78b025, 0xc526be54df0c54f1, 0x4f161bd97ca9be13, 0x153c586dae82f953, 0xff629c9af95382b, 0x963fd3c586be54e2, 0xf29cf84f1616f953, 0x9537fb518a586005, 0xbe54dfeb74f161af])
  | 5, 12 => (packedWords [0x9b6b95be3153c586, 0x586be54dfe9e4214, 0xc0c5af95379b153c, 0xd62586e0df13c842, 0xda62961b4f7ca9bf, 0x9b153c586be5a5fe, 0xdfec54f141b777ca, 0x7c62a78b0316be54, 0xbdf2a71162961b6b, 0xaf953629e0d8586e, 0x16be5baa6ff62a79, 0x961af9537fb153c7, 0x3c586be54dfed062, 0x7f961b417ca73fd, 0xbfd3c726f65f2a71, 0xe4c54f161bd97ca9, 0x1a9bfd3c586be54d, 0x54e62ff4f161bd99, 0xf9697fb153c256be, 0x6f5df2a6ff4f161a, 0x61b137ca9bfd8a9e, 0xc586be54ddcc54f1, 0x62961af9537fad93, 0xfd8a9e6be54e24f4, 0xc54c161af96aa2b, 0xa9b798a9e6be54df, 0x4dfec54f1cdb837c, 0x9537fac93c586be5, 0xbe5a63ec54f161af])
  | 5, 13 => (packedWords [0x1bd97ca9bfd3c4d6, 0x436cc5f2a6ff6296, 0x2961af9537fb153c, 0x53c4d6d65f2a6ff6, 0xc53f161af9539431, 0xfb153c586be54e22, 0x222c54f161af95f7, 0x6a7fb153c246be58, 0xe581fec54f161af9, 0xaf96ba9bfd8a9e6b, 0x86be54e66c53c161, 0x161af94e7fa78fc5, 0x3c586f65f2a6fe4f, 0x54f161af9447fb15, 0xc418a585be5d5fec, 0x56e9629e1801d9a9, 0x5be54d3c586be54e, 0xdf2a6ff62961bd9b, 0xf9538e3fd3c586e5, 0x6be5d9fec54f161a, 0x956f9687fb153c58, 0xc58600585fec54f0, 0x4f161af95384b153, 0x153c586f65f2a2ff, 0xec54b161b957ca9b, 0x7fb153c586be54df, 0x4e54ff4f161af946, 0x94e7fbe13c586be5, 0xe0e9ef8c53c161af])
  | 5, 14 => (packedWords [0x1af9537fb1532586, 0x586f65f2a6ff6d16, 0x28a1af9607fb5d3c, 0x53c566be54dfeda6, 0xff6a315af9537fb1, 0x9bfd3c556be54e56, 0x29cff4f161bd97ca, 0x537fb152e586f65f, 0xe54dfec54f121af9, 0xaf967a2bfd8a9e6b, 0x86d3df1fee962895, 0x161bd97ca9c5d3c5, 0x3c586f65f2a7123c, 0x54f161b397c7fb15, 0xb153c256be54df6c, 0xa71f4f161b637c7f, 0x378b153c586f65f2, 0x54e40ff62961af95, 0xf9538fb153c286be, 0x6be54deac54f161a, 0x61af95380b153c58, 0xa9e6be54dfee8629, 0x2f9537fb798])
  | 6, 0 => (packedWords [0xf2a6ff62a78f4587, 0x161a9bfd8a9e2c35, 0xa9bfd8a9e2c0f9c0, 0xf2a6ff62a60b0f7c, 0x77c90bfd8a586f65, 0x95bfd8aac4f30030, 0xfd8a9e2c095c0153, 0x7537fb14b0f7cb53, 0x62a78b02e7e65f2f, 0x153c581e3df2a6ff, 0xec54f161ef9537fb, 0x629603af7ca9cc9f, 0x78b0317ebdf2a6ff, 0xa9e293686f8ff62a, 0x4f161c017ca9bfd8, 0xe0b0fd5be54dfec5, 0xc587e0df2a6c54f1, 0x2c3e56f96a7fb153, 0x79b097ca9bfd8a9e, 0xe00be59ea6ff62a, 0x6be54e76ff62a78b, 0x802f95395bfd8a7e, 0xb17ca9bfd8a9e2c3, 0xca9bfda4c54f161f, 0xdf2a6ff74b14b0f7, 0x6f83be54dfec56d3, 0xca9bfdc49e2c3003, 0xbfd8a9e32961c017, 0xfec553a78b0f7ca9, 0x37fb153c417be54d, 0xb153c5818bdf2d95, 0xfec54f161ef96a7f, 0x962a784af7ca9c21, 0xbe54dfee])
  | 6, 1 => (packedWords [0xf2a6ff62a78ce587, 0x77ca9bfd8a9e2c3d, 0xbe54dfee162a79b1, 0xf2a6ff62a78b0e00, 0x6ff62a78ec587d8d, 0x7fb153c581c3df2a, 0xfd8a9e2c01def953, 0xecd62a78b0f7ca9b, 0x7c3153c587be54df, 0xfd8a9e12bfb2f953, 0xa9e2c101ef95395b, 0x62a78b0f7ca9bfd8, 0x153c587be54e14ff, 0xc580ebeaaf9537fb, 0x2c075ef9537fb14f, 0x604af7cb03fd8a9e, 0xc587be54dfed4629, 0x2c3dfef9537fb153, 0x79af9537fb153c77, 0xe00dbe9ef8ff62a, 0x7be54dfec54f210b, 0x5f2d9537fb153c58, 0x17cbdc85fe9e2c3, 0xcc1df2a6ff4f161c, 0x5f2a6ff62a78b0fe, 0xf9577fb153c586e9, 0x37fbb58a9e2c3802, 0x54e56c54f211af95, 0xd95395b153cc00be, 0x3be54dfe586005f2, 0xb7d8a9e2c3803d98, 0xa6ff4f161ef9537f, 0x54f16002fecd0df2, 0xbe54dfec])
  | 6, 2 => (packedWords [0xc2f9537fb153c587, 0x17c7fb153c6d2c36, 0xc1df2a6ff628a180, 0x4dfec54f16028e00, 0x6ff62ab0fc586be5, 0xa9c498a9e2c3802a, 0xfd8a9e34961fb37c, 0xcff62a78b0f7ca9b, 0x62aa53c587be54e9, 0xeea6ff4f35f2a6ff, 0xa9e2c095c01b7be5, 0x62a78b0fc1be3fd8, 0x153c587be5f2a6ff, 0x29e2c3676f9537fb, 0x49961c017ca9bfd6, 0x14b0f7ca9bfd8a9e, 0xc587ebdf2a7127fb, 0x2c3fb2f96aa9bfd3, 0x61ef9537fb153c75, 0xdb8be54dfec54f1, 0x700682f9537fa78b, 0xdf2d5537fb153c28, 0xf9539e3fd8a9e2c3, 0x3be515fec54f161e, 0x5f2a6ff62a4cb0d9, 0xd9a7be3fd3c58600, 0xcb4bfd8a9e2c3003, 0xbfd8a9e2c085c017, 0xf8ff62a78b0f7ca9, 0xc7fb153c286e0e56, 0x3fd8a9e2c38034f7, 0x8a9e2c025ef9538d, 0xf62a78b0f7ca9bfd, 0xd9df2a6f])
  | 6, 3 => (packedWords [0x2f9217fb153c586, 0x9537fb153c5814b8, 0xa9bfd8a9e3c161ef, 0x4dfec54f16004f7c, 0x8ff62a78b0317be5, 0xbe54dfe9e2c3f06f, 0x4d8aac4f161be1ec, 0x6ff62a78b0e00b65, 0x62a78b0417f05f2a, 0x153c852c3df2a6ff, 0xec54f161ef9537fb, 0x6c278b0fe3be54df, 0x78b00a7f65f2a6ff, 0xe9e2c3df2a6ff62a, 0x3f161fd97ca9c6df, 0x78b0f7ca9c49fec5, 0xc587efdf2a6ff62a, 0x1435f2a7047fb153, 0x6dc017cbdd4dfe9e, 0xcd7ca9bfd8a9e2c0, 0x7006def9537fb153, 0xdf2a7107fb153c58, 0xf9537fb153c702c3, 0xbe5b2a6c53f161a, 0x54dfec55da78b0e0, 0xf9537fb153c606be, 0xca9c41fec52c3002, 0xbfd8a9e2c049c017, 0xa6ff4f1602ef7ca9, 0x37fb153c726f65f2, 0xbfd8a9e12b802f95, 0x8a9e2c161ef96aa9, 0xf62a78b0f7ca9bfd, 0xc9df2a6f])
  | 6, 4 => (packedWords [0xb2f9537fa78b0527, 0x37ca9cad8a9e2c3f, 0xbe54dfec54f221b8, 0xf2a6ff62a78b0e00, 0x6ff633153c587c55, 0xa9b153c672c3df2a, 0xfd8a9e43161fb37c, 0x72b7fb153cf7ca9b, 0x7fb153c587be5b2a, 0x61fec54f37b6f953, 0xa9e2c03dc017ca9c, 0x62a78b0f7ca9bfd8, 0x153c587be5eea6ff, 0xa9e1635f2c9537fb, 0x4f161c017ca9bfd8, 0x78b0f8cbe54dfec5, 0x3a7be54e32ff62a, 0x26b5f2a6ff62a78b, 0xe9c017ca9bfd8a9e, 0xf93be54dfec54f0, 0x7f6706f9537fa78b, 0x5f2a71262a790858, 0x18cbe54dfec52c3, 0xf65f2a6ff4f1618, 0x54dfec54f204b0e0, 0xa72b7faed3c587be, 0x3913fd8a9e2c3df2, 0x54dfec54f0a1af95, 0xa6ff62a78b0e00be, 0x37fb1502586ca5f2, 0xbfd8a9e2c3802f95, 0x8a9e45161f937ca9, 0x362a78b0d7ca9bfd, 0x6d6f95])
  | 6, 5 => (packedWords [0xf2a7247fb153c587, 0x77ca9bfd8a9e2c3d, 0xa9bfd8a9e2c0fdfa, 0x4dfeda62a78b0f7c, 0x6ff62a78de587be5, 0xa9bfd8a9e2c3df2a, 0xe9fec54f161fbb7c, 0x7217fb153cd7ca9c, 0x7fb153c587005f25, 0x158a9e2c3ebef953, 0xec54f149ef9537fb, 0x6d314b0decbe54df, 0x7904587005f2a6ff, 0xa9e2c3df2a6ff62a, 0x37161f4f7ca9bfd8, 0x60b0f7ca9bfd8a9e, 0x277f65f2a6ff4f2, 0x2c3df2a6ff62a78b, 0x61ef9767fb153c67, 0x6d7ca9cd5fec54f1, 0x7007b2a6ff4f1603, 0x5f2a6ff62a791858, 0x17ca73fd8a9e2c3, 0xca9cc1fec54f161c, 0x54e24c54f1e0b0f7, 0xf9537fb153c587be, 0x37fb153c832c3f86, 0x5f2a6ff4c161af95, 0xa6ff62a78b0e00f6, 0xf62a78b03b7be5b6, 0x5eea6ff2c35f2a6f, 0x2ec54f161801ccbe, 0x2629e0b0c00be54e, 0x5f2a71])
  | 6, 6 => (packedWords [0xf2a6ff62a78b0117, 0x953a2bfd8a9e2c3d, 0xa9bfd8aac4f161ef, 0x4dfee962a78b0f7c, 0x9538fb153c586be5, 0xbe54dfec54f3002f, 0x4dfee962a79c01d1, 0x8ff4f16062d93be5, 0x6bb153c58700686f, 0xfd8a9e2c35f2a6ff, 0xec54f161c01959ab, 0x4f1601afa7c1df1f, 0x78b02d7f65f2a6ff, 0xe9e2c3df2a6ff62a, 0x4f161fe3ecbe54df, 0x153cf7ca9cadfec5, 0x1d7c9df2a72b7fb, 0x2c3df2a6ff629e0b, 0x61f3d7ca9bfd8a9e, 0xd7ca9b153c84339, 0x70069f077c7fb14b, 0xdf2a6ff703153c58, 0xf9537fb153c581bb, 0x90bfd8aac4f161a, 0x5d2a6ff62a78b0e0, 0xa6ff62a78b0247be, 0xca9bfd8a9e2c3df2, 0x54dfec54f161f8d7, 0xa6ff62a78b0f92be, 0xca9bfd3c587c75f2, 0x54df09e2c37b36f7, 0xa6ff4f161c01ecbe, 0xf62a78b0feef65f2, 0xe65f2a6f])
  | 6, 7 => (packedWords [0xf2a6ff62a78b0307, 0x9537fb153c5805bd, 0xf65f2a72b7fa79af, 0xf2a6ff71a78b0e00, 0x6ff62af13c587f65, 0xa9bfd8a9e2c3df2a, 0xfd3c7e2c0a1f897c, 0x2ff629f8b0d7ca9b, 0xbdd4dfe586005f24, 0x4dfec52c3003077c, 0xa9e2c099c01ccbe5, 0x4f1b0b0f7ca9bfd8, 0x153c587be54dfec5, 0xa9e2c3ed6f9537fb, 0x4f161ef973a9bfd8, 0xb13cd7cb8d4dfec5, 0xc587006dea6ff62a, 0x2c3df2a6ff62aad3, 0x61ef9537fb153c6b, 0xad7ca9bfd8a9e479, 0x7005f2d4ff62a784, 0xe26f9537fb153c58, 0xf953a9bfd8a9e2c3, 0xdbe54dfec54f161e, 0x54e7eff62a78b0fc, 0xf9537fa78b0016be, 0x7be54dfe9e2c3802, 0xc75fec54f161fd9d, 0xa6ff62a78b0f7ca9, 0xf62a78b0227be58a, 0xbfd3c580ebdf2a6f, 0x3c7833961fd97ca9, 0x37fb153cf7ca9b15, 0xc4df2f75])
  | 6, 8 => (packedWords [0x36f7ca9bfd8a7e6, 0xd7ca9bfd8a9e2c38, 0xbe54dfec549961f9, 0x4dfec54f1606afd9, 0xf7cbdbfd3c586be5, 0x7fab1569e2c38034, 0x4dfe9e2c0a1ef953, 0xec54f16030fecbe5, 0x7fb153c656be54df, 0xfd8a9e2c3802f953, 0xac54f161f077ca9b, 0x62a78b0f7ca9bfda, 0x153c586be54e2eff, 0xa9e2c3802f9227fb, 0x4f161b077c9fbfd8, 0xe0b0e00be5b242c5, 0xc586be54e24ff629, 0x2c3803d9537fab13, 0xadef9538fbfd8a9e, 0xd7ca9bfd8a9e2c0, 0x70060ef9537fb14b, 0x5f2a7337fb153c58, 0x17ca9c69fe9e2c3, 0xa9bfd8aac4f0a18, 0xdf2a6ff62a78b0e0, 0xf7537fb14fc587d0, 0x1a9bfd8a9e2c3df2, 0xdf27eff62961af96, 0xfec54f1e0b0e00c1, 0x37fa78fc587ce5f1, 0xbfdd2c54f3fb2f95, 0x8a9e2c0a9ef95395, 0xf62a78b0f7ca9bfd, 0xbe566a6f])
  | 6, 9 => (packedWords [0xf2a7377fb153c587, 0xfa7be54dfec52c3d, 0xdbdf2d95362a79ba, 0xaaa6ff62a78b0e00, 0x9537fb14fc286be5, 0xa9bfd8a9e2c3802f, 0xfdbcc54f1e1efd7c, 0x5537fb153cf7ca9b, 0x7fb153c587c9df2d, 0x156c9e2c3f074f7c, 0xec54f161af9537fb, 0x7c278b0e00d3df1f, 0xd93c587f65f2a6ff, 0xc7d2c3e9ef9537fa, 0x4f161ef9537fb153, 0x6062feff65f2a6ff, 0xc587be54dfe9e3f1, 0x2c3e36f9537fb153, 0x75afb7ca9bfd8a9e, 0xc00ebd4dfec52c0, 0x7005f2a6ff5da78b, 0x7b2f9537fa78b025, 0x1d5a9bfd8a9e2c3, 0xabe54dfec54f161c, 0xdf2a72b62a78b0fb, 0xf9537a3153c586ec, 0xca9bfdd2c52c3802, 0x5f2a6ff4f161faf7, 0xa6ff62a78b0fecf6, 0xf62a78b02f7e85f2, 0xb153c58103df2a6f, 0xfec54f135ef9537f, 0x27fa78b0f95be54d, 0xf65f2a71])
  | 6, 10 => (packedWords [0x62f9539abfd8a587, 0x17ca2bfd8a9e2c36, 0xbe54dfec54f161c0, 0xcaa6ff62a78b0ff0, 0xb7ca9bfd3c587be5, 0xa9bfd8a7e2c3fb32, 0xfdb0c54f161f4f7c, 0xec54f16034f7ca9b, 0xa9bfd3c587be54df, 0x4dfe9e2c37b3b37c, 0x2ff4f161c017cbdd, 0x62a78b0fecbe54e4, 0x153c587be54e36ff, 0x69e2c35f2a6ff6f3, 0x4f161801ecbe5b2a, 0x6020e00cf5f1fec5, 0xc286be54dfec54f1, 0x14b002f96ca9b153, 0x61c017ca9bfd8a9e, 0x2ff2be54dfec54f1, 0x7f65f2a6ff4f1606, 0xdf2a6ff62a78b017, 0xf9537fb153c58073, 0xca9bfd8a9e2c0e5e, 0x54dfee9629f8b0f7, 0xf9537fb153c416be, 0x37fb153c580b3802, 0xbfd8a9e2c149ef95, 0xa6ff62a78b0f7ca9, 0x37fb153c587f15f2, 0x3fd8a9e2c3df2cf5, 0xfec54f161fd97ca7, 0xf62a78b0f7ca9c35, 0xf35f2a6f])
  | 6, 11 => (packedWords [0xf2a6ff62a78f8587, 0x9538abfd8a9e2c3d, 0xa9bfd3c842c0a1ef, 0x4e2ec54f1604af7c, 0x7107fb14ce587be5, 0x7fb153c9e2c3df2a, 0xfd8a9e3919def953, 0xec54f16026f7ca9b, 0x88b153c586be54df, 0x4e56ff62b002f953, 0xec55da7980183be5, 0x62a78b0e00be54df, 0x153c587be54dfee1, 0xa9e2c3f06f9537fb, 0x4f161af97aa9bfd8, 0xa8b0e00be54dfec5, 0x57be54dfec54f1, 0x2935f2a6ff62a78b, 0x61801ecbe54dfe9e, 0xe00be4fdfec54f1, 0x7be54dfec54f200b, 0xdf2a6ff62a78b000, 0xf9537fb893c581d3, 0xca9bfd8a9e32875e, 0x5f2a6ff62a78b0f7, 0xf9537fb1500586c0, 0x37fb153c682c3802, 0x54dfec54f161ef95, 0xf92b7fb153cddcbe, 0x37fa78ce5870069e, 0xbd18a9e2c3fb2f95, 0xfec54f161ef9537f, 0x54f210b0fdabe54d, 0xbe54e56c])
  | 6, 12 => (packedWords [0xf2c1537fb153c587, 0x17ca9cadfebb4f35, 0xbe54dfed74f16180, 0x4dfec54f170b0e00, 0x6ff763153c587be5, 0x7fb153c8b2c3df2a, 0xfd8a9e3c961ef953, 0xec54f1600cf7ca9b, 0x7fb153c587be54df, 0x153c982c3df2ed53, 0xe9e42161ef9537fb, 0x7fa78b0fecbe54df, 0x153c587f65f2d953, 0xaac2c35f2a6ff63b, 0x7fa7980183a9bfd8, 0x78b0e00be5eea72b, 0xc587be54dfee262a, 0x2c3646f9537fb153, 0x61c017ca9bfd8a98, 0xcd7cbc54dfec54f1, 0x7006def9217fb153, 0x5f2cf539abfd8a9e, 0x1d7d3df1fec52c3, 0x7be54de8c54f161c, 0x5f2a73a7fb153cdd, 0xf9537fa78b001700, 0x37fb153c581b3fb2, 0x54dfebc4f161ef95, 0x5eff62a78b0fc1be, 0x3a73fd3c587be54e, 0x3fd6c9e2c37b2f95, 0xfebc4f161801a7be, 0x54f1601ae00be54d, 0xbe54dfec])
  | 6, 13 => (packedWords [0xc6f9537fb153c587, 0x9537fbc18a9e2c3f, 0xbe54dfec52c0d9af, 0x66a6c54f19cb0c00, 0x6ff4f210b0317007, 0xbe54dfe9e2c3df2a, 0xfd8aac4f161bd97c, 0x6ff55a78b0c00d3b, 0x62a78b03a7005f2a, 0xfd8a9e2c3df2d2ff, 0xec54f161f397ca9b, 0x4f1e0b0fc8be54df, 0x153c587be54e56c5, 0xa9e2c3e06f9537fb, 0x4f0e9af95388bfd8, 0x78b0e00c9d4dfec5, 0xc587be54e68ff62a, 0x4bdf2a6ff7fb153, 0x61bd97ca9bfd3c58, 0xe00d3df1fec53f1, 0x6dbdf2a6ff62a78b, 0x2f9537c3153c58, 0x189be5eea6ff4f3, 0xf65f242ff4f1618, 0x54e72ff62a78b0e0, 0xf9537fb153c587be, 0xca9bfd3c782c3fba, 0xbfda8c54f161fd97, 0xa72b7fb153cd7ca9, 0x17fb153c286005f2, 0x3fd8a9e2c3802f92, 0x8a9e44961ef9539c, 0x362a78b0f7ca9bfd, 0xbe54dfee])
  | 6, 14 => (packedWords [0xf2a6ff62a78b0467, 0x17ba9bfd589e2c35, 0xa9bfd8a9e30161c0, 0x4dfec54f16064f7c, 0x6ff62a78e4587be5, 0x7fb15629e2c3df2a, 0x4dfed462961af953, 0xec54f16006e00be5, 0x62aa93c587be54df, 0xb2a6c52c35f2a6ff, 0xec54f161c0183be5, 0x62a78b0f7ca9cb9f, 0x153c587be58ea6ff, 0xa9e2c3fa2f9537fb, 0x44161f5d7ca9bfd8, 0x6046f7ca9bfd8a9e, 0x257be54dfec54f1, 0x2c3e9ef8ff62a78b, 0x61f417ca9bfd8a9e, 0xfe4be54dfec54f1, 0x7ecf06f95362a78b, 0xdf2a6ff62a78b01e, 0xd97ca9bfd3c580db, 0xca9c61fec54f161f, 0x7b36f7ca9bfd3cd7, 0xa71162a78b01d700, 0xcbdd4dfe7e2c35f2, 0xbfd8a9e2c095c017, 0xfec54f16058f7c9a, 0x37fb153c587be54d, 0xb153c580cbf5ef95, 0x8a9e2c055ef9537f, 0x57fa78b0f7ca9bfd, 0xd05f2a73])
  | 6, 15 => (packedWords [0x33d7c7fb14fc586, 0x9537fb153c580eb8, 0xa9bfd8a9e2c135ef, 0x4dfec54f16066f7c, 0xb7c7fb153c587be5, 0x7fba5629e2c3e9f2, 0xfd8a9e2c071ef953, 0x9537fa78b0f7ca9b, 0xb63153c586f664ef, 0xfd8a9e2c38034f7c, 0xa9e2c0a1f2b7c9ab, 0x4f1607af7ca9bfd8, 0x153c587be54dfec5, 0xc7b2c3df2df537fb, 0x62a79af9537fb153, 0x78b0c00c4df2a6ff, 0x317005f2a6ff5b2, 0x2c3e9ef8ff62a78b, 0x61f317ca9bfd8a9e, 0xfa7be54dfec53c1, 0x7f65f2f7537fa78b, 0x5f2f3537fb153c58, 0x1537fb15589e2c3, 0xcbdd4dfec54f0a1c, 0x54dfec54f18cb0f7, 0x6aff62a78b0317be, 0xca9bfd8a9e2c3df2, 0x54dfe9e2c0e9fad7, 0xf9537fa78b0decbe, 0xca9bfd8a586005f6, 0xb153c612c3803317, 0x8a9e1d0a1ef9537f, 0x74f1603af7ca9bfd, 0xbe54dfed])
  | 6, 16 => (packedWords [0xf2a6ff62a78b0087, 0x9537fb153c7e2c3d, 0xabd4dfec54f161ef, 0xf2f76ca9a78b0d7c, 0x6ff62a78b0047005, 0x7fb218a9e2c3df2a, 0xfdd2c53c161ef953, 0x6ff629f8b0d7ca9b, 0x7fb153c586005f2a, 0x153c662c3802f960, 0xaa44f161ef9537fb, 0x4f21cb0f7ca9bfd8, 0x78ce587be54dfec5, 0xa9e2c3df2a71a7fa, 0x36961fb77ca9bfd8, 0x78b0f7ca9bfd8a9e, 0xc587be54e16ff62a, 0x2c35f2a6ff7c3153, 0x61c017cbb3fd8a9e, 0xf7ca9cd9fec54f1, 0x6f7df2a6ff62a78b, 0x2f96ca9b153c41, 0x17ca9bfd8a9e153, 0xca9bfdb4c52c0e9c, 0x54dfec54f1604af7, 0xf9537fb153c587be, 0xea9bfd8a9e2c3e1a, 0x54dfec54f161ef95, 0xfed662a78b0fecbe, 0x37fb153c587be54d, 0x54dfe9e2c3f46f95, 0x92c54f161fd9a7be, 0xf62a78b0f7ca9bfd, 0xf55f2a6f])
  | 6, 17 => (packedWords [0xf2d3537fb153c587, 0x953893fd8a9e2c3d, 0xa9bfd8a9e2c07def, 0xf2a7357fa78b0f7c, 0x6ff65b153c587f65, 0xa9bfd8a9e2c3df2a, 0xf29cff4f161b2b7c, 0x6ff62a78b0e00f65, 0x62a7874257ecdf2a, 0x153c7f2c3df2a6ff, 0xec54f161ef9537fb, 0x4f210b0f7ca9c85f, 0x78b0347e0df2a6c5, 0xa9e2c35f2a6ff62a, 0x2c0e9c017cb654d8, 0x78b0f7ca9c7d8a9e, 0xa9e6cb5f2a6ff62a, 0x4f3003757ca9bfd8, 0x61c01d9be54e56c5, 0xd9fbe54dfec54f1, 0x7005f2a6ff629fcb, 0x63ef9537fb153c58, 0x19cbe3fd8a9e2c3, 0xcbe54dfe9e2c045c, 0x5f2a6ff56278b0fe, 0xa6ff62a78b0317f6, 0xca9bfdd29e2c3df2, 0x54e6ac54f161fd97, 0xfeac55a78b0db5be, 0xf74b153c2870054d, 0xbfd8a9e2c3df2a6f, 0x56ff4f161ef95ba9, 0xf62a78b0fecbe54e, 0xbe54dfec])
  | 6, 18 => (packedWords [0x16f9537fb153c587, 0x9537fb153c58063f, 0xa9cadfec54f0a1ef, 0xf2a6ff6f3153cd7c, 0x5])
  | 7, 0 => (packedWords [0xf2a6ff62a78ce587, 0x9537fb153c842c3d, 0xb654dfec54f161ef, 0x4dfec54f16012f7c, 0x9217fb153c586be5, 0x7fb153c782c3802f, 0xfd8a9e2c06def953, 0x9537fb153cd7ca9b, 0x7fb153c587006def, 0xfd8a9e2c3e4ef953, 0xa9e2c0e9ef97ba9b, 0x7fa78b0d7ca9bfd8, 0x153c286007b2f953, 0xa9e2c3802f9537fb, 0x4f161f4f7ca9bfd8, 0x6022f7ca9cd5fec5, 0xc587be54dfec54f1, 0x2c3df2a6ff62ab13, 0x61ef9537fba58a9e, 0xf7ca9cadfec54f1, 0x6c1df2a6ff62a78b, 0x803077ca9bfd8a58, 0x437ca9bfd8a9e2c3, 0xcb554dfec54f161f, 0x69ef8ff62a78b0d7, 0xa6ff6c3153c58700, 0xcbdd4dfe9e2c35f2, 0xc6dfec54f161c017, 0xfec54f1602ef7ca9, 0x37fb153c587be54d, 0xbfd8a9e2c3706f95, 0x8a9e2c035c017ca9, 0xf62a78b0f7ca9bfd, 0xdbdf2a6f])
  | 7, 1 => (packedWords [0x2f95395bfd8a9e6, 0x9537fb8d8a9e2c38, 0xbe54dfec54f161ef, 0x4dfec54f1603afd7, 0x6ff62a78b0287be5, 0x7fb15589e2c35f2a, 0xfd8a9e3f161c0153, 0x6ff629f8b0d7ca9b, 0x62a78b0257005f2a, 0xfd8a9e2c3df2a6ff, 0xec54f161fd97ca9b, 0x62a78b0f7ca9c49f, 0x153c587cadf2a6ff, 0xa9e2c3f66f9537fb, 0x4f161af95390bfd8, 0x6062e00be5b2a6c5, 0xbe54dfec54f1])
  | 8, 0 => 0x2f9537fb153c586
  | _, _ => 0

private def wordBlocks : Nat → Nat
  | 0 => (packedWords [0x0, 0xc000000000000000, 0x203204100e1e380, 0x0, 0x800000000000000, 0x0, 0x0, 0x2, 0x8000000000000000, 0x10, 0x0, 0x8000000000000010, 0x410080c810400040, 0x800000000000020, 0x2420203204100010, 0x8])
  | 1 => (packedWords [0x4022044080000110, 0x20d98, 0x120ba151200102c4, 0x8366, 0x0, 0x4020, 0x1020320410021000, 0xa000000000010801, 0x5425100810000800, 0x2800000000004604, 0x950b472245002303, 0xfb00000000001181, 0xfdc6d3e8d54808c0, 0x460, 0x203204100810, 0x428])
  | 2 => (packedWords [0x200422040101000, 0x10a0908, 0x28330c910852480, 0x429242, 0x84a2ec764c2149b1, 0x10a4d9, 0x0, 0x81002, 0x0, 0x100000, 0x800000000000000, 0x80000000040100, 0x441081000a20000, 0x200000000114a0, 0x110623604388a10, 0x4528])
  | 3 => (packedWords [0x1a8dc32e62949208, 0x114a494c, 0xf67624788a3032a, 0x4538195, 0x0, 0x1800000, 0x800100c204500081, 0x681042, 0x80c810400860e, 0x214008200002, 0xa000000000000000, 0xdb00085002088100, 0x69065320c5080080, 0x2c40021400822040, 0x3e6120ba15120010, 0x8500208818])
  | 4 => (packedWords [0x2d1c8914008c0ca0, 0x214008224606d4, 0x100c2045000810, 0x300850020e8104a8, 0x165320c5081494db, 0x2c10a92000020241, 0x44a0508a98dc740, 0x42a480004a080, 0x1100000000000000, 0xc10a9200012a24, 0x462032041008102, 0xb13042a480004a89, 0xd194a2ec764c215d, 0x2c4c10a9200012a2, 0xb66720ba15120810, 0x42a480004a8])
  | 5 => (packedWords [0x42224660c0105110, 0x10a9200012a3d99, 0x528bb1d9300516c4, 0x3042a480004a8f66, 0x9ca2ec764c214591, 0xc10a9200012a3d9, 0x6628330c91085268, 0x10042a480004a9b4, 0x994a2ec764c214d3, 0x2ac10a9200012a7d, 0x154f67624788f303, 0xca3042a480005a89, 0x655ad1c8914028c0, 0x87c010a9200016e2, 0xd2c595c8f3465121, 0x42a48000890])
  | 6 => (packedWords [0x988d810e2284080b, 0x10a9200116a2455, 0x4d6442068812002a, 0x8042a480045b891d, 0x53d9d891e22cc00a, 0xac10a9200116e247, 0xd6f6762478893022, 0xa8042a480045b891, 0x753d9d891e20cc0c, 0x6e010a9200116e26, 0x7f5decd39eb81614, 0x48042a480045b8f, 0x2112c172ab74707, 0xc54010a920019283, 0xf6e50989db875041, 0x42a48006cb8])
  | 7 => (packedWords [0x35d1389b344820e8, 0xc10a92001b6e34f5, 0x2203204100816280, 0x120000920003000, 0x800000000000000, 0x4048000248000d08, 0x210889198300474c, 0x1012000092000366, 0x98c82e854480040b, 0x80048000248002dd, 0x62228330c9108524, 0x4012000092042b6, 0xa08040308114002, 0x855048000249a04d, 0x42010188d3067005, 0x128500b28802])
  | 8 => (packedWords [0x8000000000000000, 0xc4a1402ca204d280, 0x7008811020005244, 0x3162a48920082d24, 0x1c02204408001491, 0x4c58a92248020f49, 0x4720ba151208172c, 0x13162a48920083d2, 0x99c2224660c011db, 0xc4c58a92248020fd, 0x66720ba151200152, 0x3162a4892008af, 0x1820042204211d, 0x644c58a92248128f, 0xd247088919830847, 0x162a489204a3])
  | 9 => (packedWords [0xc82e854482054913, 0xc58a9224812ab491, 0x7088919830045644, 0x3162a489204aaf66, 0x9ca2ec764c215db1, 0xc58a9224812abd9, 0x4628330c91085760, 0x162a489204abd0, 0x9180000000000000, 0xc58a9224812af4, 0x2462032041008102, 0xb13162a489204abd, 0xd19ca2ec764c215d, 0x4c4058a9224812af, 0xf665088919830047, 0x162a489204ab])
  | 10 => (packedWords [0x4a2ec764c215db13, 0xc58a9224812afd99, 0x628330c910852680, 0x162a489204abf66, 0x9c2224660c010511, 0x4c58a9224812afd9, 0x6708891983084744, 0x13162a489204abf6, 0x99c82e854482040b, 0xc4058a9224812afd, 0x66728bb1d9300516, 0x913162a489204abf, 0xd99ca2ec764c2145, 0x4c4058a9224812af, 0xf66728bb1d930853, 0x162a489204ab])
  | 11 => (packedWords [0xca2ec764c215db13, 0xc58a9224812afd99, 0x728bb1d930e5f7c4, 0x3162a489204abf66, 0x9ca2ec764c215db1, 0x4c58a9224812eff9, 0x7728bb1d930a576c, 0xb3162a489205abf7, 0xddef3ecf74c29ddf, 0xc4c58a9224816eff, 0x66728bb1d9308576, 0xb13162a48920cbbf, 0xd99ca2ec764c215d, 0x6c4c58a9224912af, 0xf6e728bb1d930857, 0x162a489244bb])
  | 12 => (packedWords [0xdaafc76ee295db1b, 0xc58a9224916afddd, 0x7feff3dfb89776ee, 0x3162a489245bbf7f, 0x9ca2ec764c215db1, 0x4c58a9224992afd9, 0xe729bbdf975857ed, 0x13162a48926cbbf6, 0x99ca2ec764c297df, 0xc4c5abd22ca12aff, 0xe6728bb1d9308576, 0x20016af48b28cbbf, 0x80c810402868, 0x80005c044004, 0x0, 0x200017017001])
  | 13 => (packedWords [0x1281422a62309008, 0x80005c05d084000, 0x28330c910852480, 0x8200017017429242, 0x4188d810e2284000, 0x80005c05d4a404, 0x800100c204500081, 0x20001701781142, 0x8000000000000000, 0x11082145c87e0442, 0x901ca8570c7c, 0x3200179330034, 0x808000000000000, 0x810c8005e4dc00d, 0x200e, 0x328517b39003])
  | 14 => (packedWords [0x4030811c002044, 0xcca145ecee00d080, 0x728bb1d930a5f6c4, 0x3362a5f9314abf66, 0x9ca2ec764c215db1, 0x5cd8a97e4dd2afd9, 0x6728bb1d93285f6c, 0x1336af5fb394abf6, 0x99ca2ec764c215db, 0xc40dabd7ecff2eff, 0x4210889198300cf4, 0x4a84150a00000442, 0x443591081a21ea0, 0x1054280000510, 0x2530000000000000, 0x4150a000014c])
  | 15 => (packedWords [0x80c810400860200, 0x105428000053094c, 0x1b4fa355202383ec, 0x4150a000014c357, 0xc482e854480860b1, 0x81054280000530dd, 0x70b472245002383a, 0x84150a000015c3d, 0x4c1a8dc32e62b692, 0x8010542800015b09, 0x53028330c910a5a4, 0x1b04150a000056d2, 0xddc65320c5080080, 0x2ec1054280002570, 0x3771b4fa35520030, 0x4150a000095c])
  | 16 => (packedWords [0x6d3e8d54808e03b0, 0x1054280002570ddc, 0x1b4fa3552023036c, 0x4150a000095c3f7, 0x8426276e1d430715, 0x2105428000a11198, 0x30623604388a1808, 0x84150a000456c25, 0x4c1281422a603010, 0x8210542800195b09, 0x5306a370cb982d84, 0x84150a000656c2, 0x94c1a8dc32e62b41, 0x48210542800195b0, 0x25306a370cb988d2, 0x4150a000656d])
  | 17 => (packedWords [0x35d1389b346820e8, 0x105428001a550064, 0x195c8f346502087c, 0x84150a000695c77f, 0xc77b34e7ae03811b, 0x2105428001b5f0dd, 0xb04b05caadd0c0c1, 0x104150a0006d7c67, 0x8840220440800203, 0xc410756808221109, 0x73120ba151202180, 0xfb041d5a020894c2, 0xddc6d3e8d54808e0, 0x1281075680822530, 0x910944020400228, 0x41d5a0208954])
  | 18 => (packedWords [0x65320c50808a07b0, 0x1075680822550bcc, 0xb472245002381a8, 0x41d5a020895c2d3, 0xc000000000000000, 0x1075680822570bc, 0x3020320410021808, 0xb041d5a020895c2f, 0xdc65320c50800a03, 0xec1075680822570d, 0xd71b4fa355202383, 0xea041d5a020895c3, 0xfdc2d1c8914008e0, 0x2c41075680822570, 0x3f7120ba15120218, 0x41d5a020895c])
  | 19 => (packedWords [0x65320c50800801b0, 0x1075680822570fdc, 0x194c83142002036c, 0x41d5a020895c3f7, 0xc65320c50808a05b, 0xc1075680822570fd, 0x71b4fa355200302e, 0xb041d5a020895c3f, 0xdc6d3e8d54808c0d, 0xec1075680822570f, 0xf71b4fa355202380, 0xfb041d5a020895c3, 0xfdc6d3e8d54808e0, 0x3ecd075680822570, 0x3f71b4fa35520e3e, 0x41d5a020895c])
  | 20 => (packedWords [0xed3e8d54808e0fb0, 0x1075680822570fdc, 0x1b4fa355202383ec, 0x41d5a020895c7f7, 0xc6d3e8d54808e0fb, 0xc1075680822574fd, 0x71b4fa35520a383e, 0xb041d5a0208d7c3f, 0xdc6f3ecf74c29e9f, 0xec10756808235f4f, 0xf71b4fa355202383, 0xfb041d5a020c95c3, 0xffc6d3e8d54808e0, 0x3ee1075680832570, 0x3f71f6fe357a8a38, 0x41d5a020cd7c])
  | 21 => (packedWords [0x6d3e8d54808e0fb0, 0x107568083a570fdc, 0x1b5faf7565238bfc, 0x841d5a020e95c7ff, 0xc7fbfcf7ee0be1fb, 0xe107568083b5f0fd, 0x75decd39eb81e146, 0xbb457ae80005ecb5, 0x5d7fbfcf7ee3ffdf, 0x44115eba00017b2d, 0x7750889198300414, 0x1b8457ae80005ecf, 0xddd77b34e7ae0785, 0x6c115eba00017b3, 0xb77594c831420020, 0x457ae8000dfc])
  | 22 => (packedWords [0x77b34e7ae07851b8, 0x115eba00037f2ddd, 0x59cc939c3006146c, 0x8457ae8000dfcf77, 0xd77f37efbf47871f, 0xe115eba00037f3df, 0x75dfcdfbefd1e1c7, 0xa8457ae8002decf7, 0x7d3591081a204800, 0x6e115eba00117f2d, 0x5f5decd39eb81e14, 0x1b8457ae80045fcb, 0xdfd75b30c5aa0480, 0x46e115eba00137f2, 0xf7f5decd39eb8161, 0x457ae8004dfc])
  | 23 => (packedWords [0x1281422a60301008, 0x115eba00197b2d5d, 0x5decd39eb81e146e, 0x8457ae80065ecb57, 0xd77f37efbf47871f, 0x6115eba00197b3d7, 0x754a8d19ab80c144, 0xa8457ae80065ecf7, 0x7d37914a3a607810, 0x6e115eba00197f2d, 0x7f5decd39eb81e14, 0x1f8457ae80065fcf, 0xd7d77f37efbf4787, 0x46e115eba001b7f2, 0xb7f5decd39eb81e0, 0x457ae8006dfc])
  | 24 => (packedWords [0x77b34e7ae03851b8, 0x115eba001b7f3ddd, 0x4df45eaedd1e0c3a, 0x8457ae8006dfcf7f, 0xd52e376ebf430715, 0xc115eba001b7f3df, 0xf59dc9fbc75061c7, 0xf8457ae8006dfcf7, 0xfd75f33cdbb44821, 0x7e115eba001b7f3d, 0x7f5dfcdfbefd1e1c, 0xbf8457ae8006dfcf, 0xdfd7ffffffff47c7, 0xcfe115eba001b7f3, 0xf7f5ffffffffd3f9, 0x457ae8006dfc])
  | 25 => (packedWords [0x7ffffffff6fc71f8, 0xd15eba001b7f3dfd, 0x5ffffffffdfffffe, 0x8457ae8006dfcf7f, 0xdf7f37efbf47871f, 0xed15eba001b7f3df, 0xf7ffffffffd9f1e7, 0xf8457ae8006dfcf7, 0xfd77f37efbf47871, 0x7e115eba001b7f3f, 0xff5ffffffffd3f1f, 0x1f8457ae8006dfcf, 0xdfd77f37efbf4787, 0xcfe115eba001b7f7, 0xf7f5ffffffffd9f3, 0x457ae8006dfd])
  | 26 => (packedWords [0x6d3e8d5481cf4fb3, 0x117ffa0822772fdd, 0x5b4fa355202383ec, 0xb45ffe8208dfcbf7, 0xd7fbfcf7ee3ffdfb, 0xc117ffa08237f2fd, 0x7794c83142002006, 0xb345ffe8208dfcbf, 0xdded3e8d54828e0f, 0xec117ffa08237f2f, 0xf75bcfb3dd302797, 0xfb845ffe8208dfcf, 0xffd7dbf8d5ea0ce0, 0xc7e117ffa08337f2, 0xfff5dfcdfbefd1e1, 0x45ffe820edfc])
  | 27 => (packedWords [0x7ffffffff4fe7ff8, 0xd17ffa083b7f3ffd, 0x3b4fa35520a3e3ec, 0x53d5a0b2895f3f7, 0xced3e8d54808e0fb, 0x4d4f5682ca257dfd, 0x6728bb1d9308df6c, 0x10577ae89204eff6, 0xddc2224660c01051, 0xc4d5deba24817bfd, 0x77728bb1d9308576, 0xb13577ae89205eff, 0xdddca2ec764c297d, 0x7eed5deba24817bf, 0xf777feff3dfb8fff, 0x577ae89205ef])
  | 28 => (packedWords [0xef3ecf74c21ddbb3, 0xd5deba24837ffddd, 0x76abf1dbb88d76c6, 0x8577ae89265eff77, 0xdf7f37efbf47871f, 0xed5deba249b7ffdf, 0xf7ffffffffd9f7ef, 0xb3577ae8926dfff7, 0xdded3e8d54808f4f, 0xc4d5fffa2ca277bf, 0x66728bb1d93085f6, 0xb1357ffe8b28ceff, 0xfddca2ec764c297d, 0x46c15fffa2ca37ff, 0xff779cc939c30061, 0x57ffe8b28dff])
  | 29 => (packedWords [0xed3e8d54828e0fb3, 0xd5fffa2ca37fffdd, 0x7bcfb3dd30a7f7ec, 0xc57ffe8b28dffff7, 0xd77f37efbfc7971f, 0xe15fffa2cbb7fbdf, 0xf7dfcdfbefd1e1c7, 0xfb57ffe8b2edffff, 0xfdfffffffff6ffff, 0x8015fffa2cbb7fff, 0x4200801088100ca4, 0x2006150b70130452, 0x94c0a0cc32440b69, 0x48218542dc04c534, 0x25306a370cb98ada, 0x6150b701356d])
  | 30 => (packedWords [0x1081000a20a20008, 0x18542dc05c510044, 0x4a0508a982ca482, 0x86150b7017145253, 0xc188d810e20a6020, 0x18542dc05c53094, 0x3000000000000000, 0x6150b701714d25, 0x4c080c8104008602, 0x218542dc05c5349, 0x5304a0508a982c84, 0x2086150b701756c2, 0x94c1a8dc32e62b69, 0x48018542dc05d5b0, 0x253028330c910a5a, 0x6150b701756d])
  | 31 => (packedWords [0x1281422a60301008, 0x18542dc05d5b494c, 0x4a0508a980ca482, 0x86150b701756d253, 0xc1281422a6230900, 0x218542dc05d5b494, 0x30623604388a1808, 0x86150b701756d25, 0x4c1a8dc32e60b612, 0x8218542dc05d5b49, 0x5306a370cb988d24, 0x86150b701756d2, 0x94c1a8dc32e62b41, 0x48218542dc05d5b4, 0x25306a370cb98ada, 0x6150b701756d])
  | 32 => (packedWords [0x1a8dc32e63b79e0b, 0x18542dc05d5b494c, 0x26a370cb98ada482, 0x86150b701756d253, 0xc1a8dc32e62b6920, 0x218542dc05d5b49c, 0x706a370cb98ada68, 0x186150b701756d35, 0xdc5aafc76ee2b69b, 0x8218542dc05d5b4d, 0x7306a370cb98ada4, 0x2086150b701756d6, 0x96c1a8dc32e62b69, 0x48218542dc05d5f4, 0x2d306a370cb98ada, 0x6150b701757d])
  | 33 => (packedWords [0x3f9dcb3e62be9ea8, 0x18542dc05d5f4f5c, 0x6a370cb98ada482, 0x86150b7017d7d273, 0xc7fbfcf7ee2be93b, 0x218542dc05f5f4dd, 0xb06b37cebddadac9, 0xb06150b7017d7d67, 0xdc6d3e8d54828e8f, 0x1118756dc866574f, 0x100c20470888, 0xe0861d5b721b8440, 0xb4c1a8dc32e62b69, 0x8018756dc87d5b4, 0x2f30203204100218, 0x61d5b721f95d])
  | 34 => (packedWords [0x6d3e8d54808e0fb0, 0x18756dc87e574fdc, 0x6a370cb98ada482, 0x861d5b721fd7d2f3, 0xc7fbfcf7ee2be9fb, 0x2d8756dc87f5f4fd, 0x346a370cb98fdf48, 0x8657aff0175eda5, 0x5d1a8dc32e62b692, 0xeed95ebfc05d7b6d, 0x575feff3dfb8fff7, 0x8657aff0175edb, 0xd5d9281422a60301, 0x682d95ebfc05d7b6, 0xb5766a370cb98ada, 0x657aff0175ed])
  | 35 => (packedWords [0x5aafc76ee2b6d318, 0x195ebfc05d7b7ddd, 0x4fe772cf98bfa4aa, 0x8657aff0175fdb5f, 0xd77f37efbf47871f, 0xe195ebfc05f7f7df, 0xf5ffffffffdbfbcf, 0xf8657aff017dfdf7, 0xfd77f37efbf47871, 0xfe197fffc87f7f7f, 0xff5ffffffffdbfbf, 0xa0b65ffff21fdfdf, 0x94c9a8dc32e62b79, 0x4821cd42de4dd5bc, 0x67326a370cb98ada, 0x7350b793756f])
  | 36 => (packedWords [0x6d3e8d54888f8fb4, 0x1cf56dece657cfdc, 0x10989db8770cfcd5, 0x473d5b7b3b847662, 0xc6f7efff5dcbffff, 0xc1cf56decee57dfd, 0x73b4fa355202383e, 0x5c73d5b7b3f95f7f, 0xcc5aeff7effeb7f3, 0x821cf56decff5bd9, 0xf326a370cb98ada4, 0xb1373d5b7b3fd7f6, 0xd99ca2ec764c237d, 0x482dddebfe4cd3bf, 0xe5366a370cb98adf, 0x777aff9375ef])
  | 37 => (packedWords [0x9a8dc32e62b69a0b, 0xdddebfe4dd7bfddd, 0x728bb1d930a5f6c4, 0x8777aff9375eff77, 0xdd2a3466ae030511, 0x6dddebfe4dd7bfdd, 0x776abf1dbb8adf6c, 0xfc777aff9375eff7, 0xfd77f37efbfc79f1, 0x7e1ddebfe4df7ffd, 0x7f7dfcdfbefd1e1c, 0xbfb777aff937dfff, 0xdfdfffffffff6fff, 0xed5dddebfe4df7ff, 0xf66729bbdf9778df, 0x77ffffb3bcef])
  | 38 => (packedWords [0x7fffffffffffffff, 0x1dffffecef7bfddd, 0x5dfcdfbeff1e1c7f, 0xc77ffffb3fdfff7f, 0xd77f37efbfc7bf3f, 0xeddffffecff7ffdf, 0x77feff3dfb8aff7e, 0x377ffffb3fdffff, 0x2880c810403840c, 0x22000013008002, 0x88a0000000000000, 0x4a88800004c42100, 0x2663591081a21c80, 0x3282200001310c40, 0x19dab47224500230, 0x8800004c4318])
  | 39 => (packedWords [0x988d810e22840008, 0x2200001311ce0266, 0xa0100c2045000810, 0x48800004c6a104a8, 0x2255038911d4824e, 0x2221401b2284022, 0x8a00000000000000, 0xa38885006cca100a, 0x33a510081001480c, 0x28e30a921300a426, 0x8ceb47224500d303, 0xcab8c2a484c06b89, 0x677bd9d891e23cc0, 0x2e30a921301ee2, 0x808e420400288d00, 0x8c2a484c46a0])
  | 40 => (packedWords [0x988d810e23c40c0b, 0xe30a921311a82223, 0xe623604388d10202, 0xb8c2a484c46a890c, 0x39081000a2340000, 0xae30a921311ac222, 0xced64420688d2032, 0x8c2a484c46b098, 0x3380000000000000, 0xe30a921311ae26, 0x8ce2032041008102, 0xb8c2a484c46b89, 0x67988d810e23c40, 0x32ae30a921311ea2, 0x91def67624788f30, 0x8c2a484c47a8])
  | 41 => (packedWords [0xb591081a23c804ab, 0xe30a921311ec2267, 0xed64420688d2002a, 0x88c2a484c47b891d, 0x73591081a21c804a, 0xae30a921311ee267, 0xdcf67624788f3032, 0xb8c2a484c47b899, 0x77988d810e228408, 0x28e30a921311ee26, 0x9deb47224500a303, 0xa88c2a484c47b89, 0x677b591081a20480, 0x32ae30a921311ee2, 0x99ded64420688520, 0x8c2a484c47b8])
  | 42 => (packedWords [0xbd9d891e20cc0ca8, 0xe30a921311ee2677, 0xef6762478893022a, 0x88c2a484c47b899d, 0x7bd9d891e22cc00a, 0xae30a921311ee267, 0xdef67624788f3032, 0xab8c2a484c47b899, 0x77bd9d891e23cf8e, 0x2ae30a921311ee26, 0xbdef67624788f303, 0xeab8c2a484c47b89, 0xf7fbd9d891e23cc0, 0x3eee30a921311ee2, 0xbffff6fe357a8f30, 0x8c2a484c47b8])
  | 43 => (packedWords [0xbd9d891e23cc0cab, 0xe30a921311ee36f7, 0xffeff3dfb8f7176e, 0xb8c2a484c47b8fff, 0x7bd9d891e23cc0ca, 0xae30a921311ee667, 0xfefe772cf98f727a, 0xab8c2a484c47b9bd, 0xf7bd9d891e23cc0c, 0x2ae30a921313ee26, 0x9def67624788f303, 0xceb8c2a484c67b89, 0x6f7bdddb99f37cc2, 0x3aae30a92131bee3, 0x99def67624788f38, 0x8caf486cc7b8])
  | 44 => (packedWords [0xbd9d891e23cc0cab, 0x232bd21b33ee26f7, 0xa000000000000000, 0x79a0000de42134a8, 0x28000000009010c0, 0x126a1403fa080820, 0x8a0100c204700081, 0x479a8500fe8a124a, 0x23804030811d4160, 0xc4e78a923780a0b0, 0xe6f28bb1d930e577, 0x8039e2a48de06abf, 0x6b3880c810402040, 0x6c4e78a923791aef, 0xfeef28bb1d930857, 0x9e2a48de46bb])
  | 45 => (packedWords [0xbd9d891e23cd8eab, 0xe78a923791eee677, 0xef67624788f3032a, 0xb9e2a48de47bbdbd, 0xfffbfcf7ee3dddfb, 0x5e78a923791eefff, 0x6f28bb1d932c577c, 0xf79eaf48fe86abfe, 0xb3e5723cd19d496d, 0xfde7abd23fa2a4b6, 0xeefbdfbffd77d77f, 0xb139eaf48fe8ebbf, 0xfbbca2ec764c215d, 0xb7fe7abd23fb3aef, 0xdbdff7fef77eff35, 0x9eaf48fecfba])
  | 46 => (packedWords [0xbd9d891e23cc0cab, 0x27abd23fb3eef6f7, 0x84304c22cf580813, 0xa800174d7200008, 0x2800000000000000, 0x12a0005d35c84422, 0x800000000260810, 0x44a885176d920008, 0x22004030811c0020, 0xaaea2145db7e8402, 0x9def67624788f3a3, 0xcabac2a5f4d57b99, 0x677bd9d891e23cc0, 0x32aeb0a97d35dee6, 0x9bdef67624788f30, 0xacaf5f6dffb9])
  | 47 => (packedWords [0x800000000b018007, 0x2e8005f7c480c002, 0xa0100c2047000811, 0x4ba0017df7203408, 0x2800000000800000, 0x1eea145ffe480c20, 0xa203204102e1e38, 0x44ba8517ff920308, 0xa2804030811c0020, 0x91eea145fffe84d2, 0xa8a2132c6147e1eb, 0xb54ba8517fffa134, 0xfbac86eb5c59c042, 0xb392ea145fffe86d, 0x5bdab572e6547230, 0xba8517fffb1b])
  | 48 => (packedWords [0x8a4cf3a55e14b244, 0x2ea145ffff8edbaa, 0xa6336c63cfa10813, 0x7ba8517ffff3b4b9, 0xbca2ec764cb15db1, 0x3ef8a97f7c5aafd9, 0x8e4b05caadfdc7c1, 0x5fbe2a5fdf76a3c0, 0xbbdaeff7efff75fb, 0xc4ef8a97f7ddaafd, 0xeef28bb1d9308576, 0xcefbe2a5fdf76bbf, 0x677bfddfbbf7ffdf, 0x32aef8a97f7ddeef, 0xdbdef67624788f30, 0xbe2a5fdf77bb])
  | 49 => (packedWords [0xca2ec764ca15db17, 0xefabd7ffe5aaff9b, 0xf28bb1d932e5f7c5, 0x7beaf5fff96abfe6, 0x3ed7ebdd59fcfeff, 0xbefabd7ffe6a4f6b, 0xdef6762478af3e3a, 0x4fbeaf5fffd7bb99, 0x239acdf3af7ff7fe, 0x7defabd7fffda8f2, 0xacf95c8f3467525b, 0x4fbeaf5ffffa93d, 0x2a392c172ab7f71f, 0xf7fefabd7ffffacf, 0xdacfdfcdfbeffde7, 0xbeaf5ffffeb3])
  | 50 => (packedWords [0x804030811c002044, 0xefabd7ffffaef6b3, 0xe2132c6147810a11, 0x4beaf5ffffebbdac, 0xbc26276e1dc10715, 0x5efabd7ffffaeffb, 0xef29bbdf977857ed, 0xecbeaf5ffffebbfe, 0xf7b5d1389b3c4820, 0x3befabd7ffffeef6, 0xbdef776e67cff30b, 0xfffbeaf5fffffbbd, 0xfffffffffffffddf, 0x3ecefabd7ffffeef, 0x3f7bb4fa35520e38, 0xc9d5a06c8b5c])
  | 51 => (packedWords [0xed3e8d54808e0fb0, 0xf275681b32d70ffe, 0xef67624788fb832a, 0x8cd7ae84c47fc99d, 0xfb591081a204800a, 0xaf35eba1311ff2f7, 0xfef67624788f3032, 0xabcd7ae84c47fcbd, 0x7fbd9d891e23ce0e, 0xeef35eba1311ff2f, 0xdfffeff3dfb8fff7, 0xdbbcd7ae84c47fcb, 0xffffdbf8d5ea3cc0, 0x72af35eba1313ff2, 0xbdfefe772cf98ff0, 0xcd7ae84c67fc])
  | 52 => (packedWords [0xf7f37efbf47871f8, 0xf35eba131bff3fff, 0xfffffffffdff1f7e, 0x3cd7ae84c6ffcfff, 0xfed3e8d5481ce0fb, 0xaf37ffa1b22f72ff, 0xdef67624788f3832, 0xabcdffe86ccffc99, 0xffbd9d891e23ce0e, 0xecf37ffa1b33ff2f, 0xfffb4fa35520a383, 0x1b8cdffe86ccffcb, 0xffff5b30c5aa0480, 0x3eef37ffa1b33ff2, 0xbffff6fe357a8f38, 0xcdffe86ccffc])
  | 53 => (packedWords [0x77f37efbfd7875fc, 0x337ffa1b3bff3fff, 0xfdfcdfbefd1e1c7e, 0xbcdffe86ceffcfff, 0xffffffffff7fe7ff, 0xdf37ffa1b3bff3ff, 0x7bb4fa3552263c3e, 0xb0dbd5a0fe8b5e3f, 0xfeed3e8d54808e0f, 0x7e36f5683fb2d7df, 0xfffdfcdfbefd1e1c, 0xffbdf7ae8de6ffff, 0xffffffffffff7fdf, 0xbfdf7deba379bfff, 0xffffb5faf756773d, 0xdfffe8fe8bde])
  | 54 => (packedWords [0xffffffffffffffff, 0xf7fffa3fa3ffbfff, 0xffeff3dfb8f7f7ee, 0xcdfffe8fecffffff, 0xff7f37efbfc7871f, 0xff7fffa3fbbffbff, 0xffdfcdfbeff5e5f7, 0xbdfffe8feeffeff, 0x4e9a8dc32e63b69e, 0x823a542dd35ddb4b, 0xdba6a370cb98ada4, 0xfb4e950b74d777d2, 0xfde6d3e8d54898e0, 0x93b3a756ddb66d70, 0x998d744e26cf7a8, 0xe9d5b76dfb54])
  | 55 => (packedWords [0x7dffbddfbdee2ffc, 0x3a756ddb7ed70ffe, 0xbb4fa355202383ec, 0xce9d5b76dfb5d3ff, 0xe3fddfbbf7ffeb6e, 0x23a756ddb7fdf4b6, 0xba6a370cb98ada48, 0xbe9d5b76dff7d2f, 0x6f9a8dc32e63f692, 0x2afb5ebfd35dfb69, 0x9def67624788fb83, 0xa0bed7aff4d77fc9, 0xf7f9a8dc32e62b69, 0x42a3b5ebfd35dff6, 0xbdfede4528e981e0, 0xed7aff4d77fd])
  | 56 => (packedWords [0xbd9d891e23ce0eab, 0xfb5ebfd35dff6f7f, 0xefe772cf98ffa7aa, 0xced7aff4d77fdbdf, 0xf77f37efbfd7871f, 0xe3b5ebfd35fff3df, 0xffdfcdfbefd1e1c7, 0xfbed7aff4d7ffdff, 0xfffffffffff7feff, 0x3bfb5ebfd35fff7f, 0x9def776e67cffb8b, 0xfffedffff6dfffc9, 0xf7f7ffffffffffff, 0xc7f3b7fffdb7fff2, 0xfffddfcdfbeff1e1, 0xedffff6dfffc])
  | 57 => (packedWords [0x77f37efbfdfa75fc, 0xfb7fffdb7fff3fff, 0xffeff3dfb8ffa7ee, 0x8edffff6dfffdbff, 0xe9a8dc32e62b6920, 0xd3ed42df7dddfdbe, 0x7bb4fa355222383e, 0xb7fbd5b7ff9b5f3f, 0xdeed3e8d548b8f8f, 0xd5fef56dffe6d7cf, 0xe2b29bbdf977edff, 0xe0ffbd5b7ffba476, 0xb4e9a8dc32e6bb79, 0x8113ef56dfffddbc, 0x4a8a0100c2047088, 0xfbd5b7fffa57])
  | 58 => (packedWords [0xc26276e1dc33f354, 0xfef56dfffe95dbaa, 0xaf776e67cffbebbb, 0xcfbd5b7fffb57099, 0x6b5d1389b3dea24e, 0xf3ef56dfffed5d2e, 0xb9dfcdfbeff7efdf, 0x44fbd5b7fffb576f, 0xee804030811c0020, 0x913ef56dfffed7db, 0xfba2132c61472188, 0x1f4fbd5b7fffb5f6, 0xffee5723cd19c082, 0xbfd3ef56dfffed7d, 0x7ffbb5faf7567238, 0xfbd5b7fffb5f])
  | 59 => (packedWords [0x92c172ab7c30304c, 0x3ef56dffffdfdbee, 0xa6b37cebdfadac93, 0xcfbd5b7ffff7f6fb, 0xefffffffffebebff, 0x3fef56dffffdfdff, 0xbe6b37cebdffdfc9, 0xffff7affdf77efe5, 0x7fffffffffffffff, 0xeeffdebff7ddfbfd, 0xffffeff3dfb8fff7, 0x1fcff7affdf77fff, 0xdfff7f37efbfc787, 0xc7fffdebff7dffff, 0xf7ffdfcdfbeffde7, 0xff7affdf7fff])
  | 60 => (packedWords [0xffbfcf7eebffdfbf, 0xffffffffe5fbef5f, 0xf9dc9fbc775efffd, 0xfffffffffbad7fee, 0x7f5f33cdbbdeb6df, 0x7fffffffffef5b6f, 0xaf4b8ddbaffdcfcd, 0xeffffffffffee7e6, 0x67b7d17abb7ffbf4, 0x3b3ffffffffffdf2, 0xffedf45eaedf1e0c, 0xeeffffffffffffff, 0xfffbfddfbbf7ffeb, 0xc573ffffffffffff, 0xffff4b8ddbaff0c1, 0xffffffffffff])
  | 61 => (packedWords [0xdaeff7effeb7fb5f, 0x3fffffffffffffff, 0xf9dc9fbc77061c7d, 0x7fffffffffffffff, 0xfef7efff5de9ffff, 0xf3ffffffffffffff, 0xffd7ccf36ef12087, 0xfcffffffffffffff, 0xfff7f37efbfc7871, 0xffffffffffffffff, 0xffff7fef77eff38b, 0xffcfffffffffffff, 0xffffffffffffcfe7, 0xefffffffffffffff, 0xfffffffffffff9f7, 0xffffffffffff])
  | 62 => (packedWords [0xfffffffffefef3fc, 0xffffffffffffffff, 0xffffffffffff1f7f, 0xffffffffffffffff, 0xffffffffffffffff, 0x3ffffffffffffff])
  | _ => 0

private def wordAt (i : Nat) : Nat := fld (wordBlocks (i / 8)) 126 (i % 8)

private def unpack : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wordAt (fld ids 9 0) :: unpack n (ids >>> 9)

private def states (s i : Nat) : List Nat :=
  let packed := fld (packedBlocks s (i / 32)) (stateWidth s) (i % 32)
  unpack (packed &&& 15) (packed >>> 4)

private def index (s : Nat) (ws : List Nat) : Nat :=
  bsr (fun i => fld (hashBlocks s (i / 64)) 32 (i % 64)) (hk ws) 11 0 (proofCount s)

private def check (s : Nat) : Nat → Bool := bar k states proofCount index id [] s

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4_0 : span (check 4) 40 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4 : span (check 4) 40 0 = true :=
  span4_0

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
private theorem span5_432 : span (check 5) 41 432 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5 : span (check 5) 473 0 = true :=
  (span_join (span_join (span_join span5_0 span5_48) (span_join span5_96 (span_join span5_144 span5_192))) (span_join (span_join span5_240 span5_288) (span_join span5_336 (span_join span5_384 span5_432))))

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
private theorem span6_576 : span (check 6) 4 576 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6 : span (check 6) 580 0 = true :=
  (span_join (span_join (span_join span6_0 (span_join span6_48 span6_96)) (span_join span6_144 (span_join span6_192 span6_240))) (span_join (span_join span6_288 (span_join span6_336 span6_384)) (span_join (span_join span6_432 span6_480) (span_join span6_528 span6_576))))

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
  · simp [proofCount] at hi
  · simp [proofCount] at hi
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


end Monotone15868Lower

end

section

namespace Monotone15868Control

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[
  ⟨.or, [2, 3]⟩,
  ⟨.and, [3, 4]⟩,
  ⟨.and, [2, 5]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.or, [9, 6]⟩,
  ⟨.or, [7, 8]⟩,
  ⟨.and, [0, 10]⟩,
  ⟨.and, [1, 11]⟩,
  ⟨.or, [12, 13]⟩
], 14⟩

theorem monotone : Monotone2 circuit := by
  intro gate mem
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 15000000 in
theorem exactTable : ∀ x : Fin 6 → Bool,
    circuit.eval (List.ofFn x) = Monotone15868Lower.target x := by
  decide +kernel

end Monotone15868Control

end

end PEqualNP.Outside.L_meta_15867_aux

open PEqualNP.Outside.L_meta_15867_aux

open PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_15867 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4004162208) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4004162208) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have budget : 9 ≤ s := Monotone15868Lower.lower h
  exact ⟨Monotone15868Control.circuit, Monotone15868Control.monotone, budget,
    Monotone15868Control.exactTable⟩
