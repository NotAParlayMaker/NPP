import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_15309_aux

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

namespace Monotone15310Lower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoreTable7402_aux

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3937060992 * 2 ^ 32 + 3902851200)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

private def k : Nat := 63
private def rows : List Nat := [6, 12, 58, 3, 37, 19, 5, 37, 25, 33, 44, 60, 28, 41, 45, 17, 56, 58, 38, 19, 10, 5, 9, 45, 26, 17, 60, 22, 25, 26, 35, 35, 25, 58, 25, 54, 58, 60, 54, 54, 25, 45, 45, 35, 45, 35, 19, 54, 19, 58, 25, 19, 60, 19, 60, 60, 58, 19, 45, 45, 25, 58, 35, 7, 14, 62, 11, 53, 51, 7, 39, 57, 49, 46, 61, 30, 57, 47, 21, 57, 59, 46, 27, 14, 21, 11, 61, 30, 49, 62, 30, 29, 27, 49, 7, 11, 14, 7, 49, 49, 49, 14, 21, 14, 21, 14, 21, 7, 11, 21, 7, 7, 11, 21, 11, 11, 14, 7, 14, 21, 49, 49, 11, 49, 7, 14]
private def inputs : List Nat := [(packedWords [0xde2d7f05d2e8e3f8, 0x1faffd5ef975f5fc]), (packedWords [0xe32be8dae91e002d, 0x347ddaa3d6af2a77]), (packedWords [0x8cd096e80ca45cd3, 0x30f2efe34eda6e6b]), (packedWords [0x3dd6173735d37d06, 0x245d12a19eefbe87]), (packedWords [0x33ffc1ff3f0b9924, 0xb82255c3fd5dd9a]), (packedWords [0x6dd2befac4876e94, 0xb00001c2343b7da])]

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
  | 2 => 7
  | 3 => 60
  | 4 => 244
  | 5 => 841
  | 6 => 754
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
  | 2, 0 => (packedWords [0x23ce0b50018e2243, 0x6648f672326ea5e4, 0xde717c04d2fbbdbf, 0xf9419509])
  | 3, 0 => (packedWords [0x2dfd90c00d6d63c, 0x4f7036b034b3699, 0xf9d002c0bfe70a8, 0x1abb6a041044b027, 0x301ac5842bd27504, 0x3a11b187351991e0, 0x41d461bc3f500ae2, 0x47ba7df4435e5a80, 0x4a6775894a345a3a, 0x589de5c44ca5747e, 0x5e3578165ac380f9, 0x618ff3ef610d53f1, 0x62f151d961ac3922, 0x70308e836bfd4af8, 0x80a9da6273e9b52b, 0x886d35b9823b5a17, 0x8ab7537588ae50a5, 0x97313ae78c3845fd, 0xa954a84f9a8b0313, 0xadabc8a5ab579ab9, 0xaffc2fddaedba5d0, 0xb5c45df9b280a64f, 0xc508dc96bfe30386, 0xcb35d4e9cad03f70, 0xceb3311fcd221505, 0xe6c2aacbe60cf27f, 0xeb945836e7a3fdeb, 0xedbeec8cebcf9371, 0xf6768fbef56117f2, 0xf7cc659ff76a1ac2])
  | 4, 0 => (packedWords [0x1a96feb006122ce, 0x34b369902dfd90c, 0x835b164045411b5, 0xae3fda908f7bd8d, 0xc17a6660b053e53, 0xde30ee00d77b153, 0xe6d0bbc0e34eda9, 0xef370110e9ba10d, 0x109f7388103df079, 0x17c64bf217abc009, 0x1b41b2921b2c9e10, 0x226d88b11f0078b3, 0x231b39ba22f3949a, 0x23a2a2ec234165dd, 0x2565e68f2509f1a0, 0x29fde41c25edd50e, 0x2b80d5302a2dcac0, 0x3075c9972bdcc241, 0x3292f36132025a5f, 0x33ef37c133230096, 0x352c0366340b5d2f, 0x35ab6cd2358e4e43, 0x3649366035eb883d, 0x36e4b23e36c47830, 0x37528086373fe9ea, 0x3811391d37a8d8c0, 0x3a24670f3a18bfac, 0x3ce5168b3bd033e1, 0x3e98bedb3e119d6a, 0x3ef382503ec76e83, 0x3f89a3c73f2c07ae, 0x40a1c1ab4059673d])
  | 4, 1 => (packedWords [0x410d1f3840b1f162, 0x42a709914295d43f, 0x432f257842b8ec0a, 0x4423520343531531, 0x475920ab44b11920, 0x4b24160b485ed839, 0x4ceb62344b40f425, 0x4f4ffeba4f479062, 0x51949a7a4fcefa90, 0x5232609f521e574a, 0x52c1abeb52b2c50e, 0x581ebb9754aba473, 0x5adc947b5a215e49, 0x5bd4b0095b54d679, 0x5e1b159f5d47070e, 0x610a16725e991ca7, 0x62aba57a624eb741, 0x6503cdc86442aa6f, 0x6a17a46a67516544, 0x70eae1fd6ef6c487, 0x759edd777489dea3, 0x776c588475f07f35, 0x77d39a26776fe6f1, 0x78c42182782b7ee4, 0x7aa9ea9b7a1586b0, 0x80f15ba17f964a5b, 0x84b763ae8120431f, 0x85b3541c8547f68f, 0x87528b83861679a8, 0x893356a788c7f91a, 0x8a675d1d89f50f4d, 0x8b2dbc328ab75375])
  | 4, 2 => (packedWords [0x8cd989048bc9c67b, 0x8ff391408f60fc39, 0x954f2bbc900d2bcd, 0x965fce6395b2a7eb, 0x989df9d298856998, 0x9983513098c74a26, 0x9bf488aa9b04202c, 0x9f83b57d9d5475b8, 0xa0b33a78a0143af1, 0xa3f055e3a2d67b6e, 0xa718ef12a542ff53, 0xa8b9b9a1a7d4f61c, 0xaa8edc7fa9bf3397, 0xacac2dc7aab8bdf9, 0xaec366dfadd55a69, 0xb1d55e85af27b6e0, 0xb3b4fa9db394a43f, 0xb4b6486cb4367335, 0xb6e88e58b51c81dc, 0xb741b91db703ad54, 0xb9574197b7ab74c5, 0xb9d9e14bb998b9dc, 0xbd1053afbaee0d48, 0xbf29faefbe6bc301, 0xc245cb3ec1f43720, 0xc4d182e4c3077ba6, 0xc6703944c571dad8, 0xc7f2abd6c7038217, 0xc903677cc8793c14, 0xc9fa2e9cc9bf825c, 0xcb4de9c7ca46dcdc, 0xcd0d1c02ccf9586e])
  | 4, 3 => (packedWords [0xceee9405cea52540, 0xd0474129cf0022b6, 0xd1643389d0ebfec1, 0xd3974c7ed1a86639, 0xd56f8ca0d510eab2, 0xd5daea2dd5d74c2e, 0xdc47d5d4d6c82897, 0xde7797dcdcdf33e9, 0xe32c50e2dfcf60da, 0xe71690eee49382e7, 0xe8964318e78397c3, 0xe9ee95d8e9198358, 0xeb6db144ea00d77f, 0xee04d4abec9d8e6f, 0xee5dcadbee1904c7, 0xef986c83ef28dfad, 0xf0428eeef003ca10, 0xf10e87a9f0c416f3, 0xf1188b52f114d749, 0xf3218e22f1cf3f22, 0xf3b82da0f37b0bf4, 0xf5f97e33f3dfd091, 0xf7ddfa41f79efb26, 0xfbe20d0cf9dd4020, 0xfe15138bfc34ac61, 0xff5865e9fe3daf31])
  | 5, 0 => (packedWords [0x107bcda0007b3e2, 0x1e511d60172c551, 0x216b26d01f7537d, 0x2936b880234bb12, 0x29a966e029578ba, 0x3293a6b02d60ba1, 0x43dbde203e9ae3d, 0x5f49fc005855e7d, 0x69b10c8068224f0, 0x7816b0006b97916, 0x7de7f7607d9de02, 0x808c58007fa460e, 0x83afb0f082310b9, 0x8be04aa086df461, 0x8e261ee08e0c556, 0x92e8ceb09200650, 0x99dd583097e0ec0, 0xa9f83c109baa90b, 0xaa6c72a0aa5a94d, 0xb654f230acf04a6, 0xc17450a0bd7dc6b, 0xcb07ca90c9bd67d, 0xcbabb120cb41aa8, 0xce6b0120cc06064, 0xd95d9ba0d8d7e75, 0xdc89fff0daf91ab, 0xdda424f0dced82f, 0xe0929cd0df3e248, 0xedc1af10e4a9364, 0x1026472b0f20c416, 0x10dd91ae1052551a, 0x1110ea35110cefb0])
  | 5, 1 => (packedWords [0x124a3d8412163e93, 0x129c3aca128660b2, 0x12dd79dc12d2d356, 0x13317544130d4e0c, 0x142c4846139cd2d1, 0x14f2951a14e099c6, 0x151dd53115013024, 0x163adfca16052687, 0x168b800a1656613f, 0x16e7baa016ddf5fb, 0x1700220516ef80ee, 0x1816a2e01735340e, 0x1969558d19520540, 0x19efc5bb19e1fb14, 0x1b37ff3a1a20482b, 0x1b8c2ab91b41b292, 0x1c75f96f1beb1c53, 0x1cdb02be1c8dddd8, 0x1d952d891d0546e3, 0x1ecfc7dd1e831ccc, 0x1f4488ef1eefaadf, 0x1fc7dcd81f81ddd5, 0x2062574b1ffac0fd, 0x20ee398620c3f0ab, 0x2117efc421038a3b, 0x2144eab621431524, 0x2227b4eb21fc7dc2, 0x22f8a26a22cb120d, 0x23dc2c84236c0077, 0x243ab51c240b1402, 0x24a43eee2469ef9d, 0x255703df24de0526])
  | 5, 2 => (packedWords [0x26a8a52f2690c03b, 0x279435a126d15328, 0x283e691027da2aed, 0x28d8233028924651, 0x2987b470291ff283, 0x2a2ad80429d875f6, 0x2bdaed6b2bc6bd4f, 0x2c0e65802c0710bc, 0x2cd4b5932c30c4cc, 0x2dfe6d192dc82f20, 0x2eba55212e188d15, 0x2eda73f62ed6bfed, 0x2f4eb7a52f47601d, 0x2fbcc7eb2f58026f, 0x306621f3302e2f21, 0x30e376c630b6709b, 0x31b83d6530f2f77c, 0x31e8430931c30ecf, 0x323731f131ed0688, 0x3271621d324b5bdc, 0x32b056b03288ab60, 0x32bb948932b66ec3, 0x33231a0932e7a856, 0x33bb66d7335ce615, 0x340b5d2f33e2a098, 0x356582b7353cd67e, 0x35abe940358b4219, 0x35e8667e35af0cab, 0x36900dfc35f2143d, 0x36b04618369b2f97, 0x36db44e836c17f45, 0x379f28c437528086])
  | 5, 3 => (packedWords [0x389b5bc0380b8082, 0x38b3a59638adf67d, 0x393f179438bbb619, 0x3961358739508c98, 0x3a18bfac39f071e1, 0x3ab24df73a24670f, 0x3bac4d8d3aea1093, 0x3c18f8d33c0b94fc, 0x3ca858de3c2b0073, 0x3d1e39f53ce30488, 0x3d5f1df13d535c06, 0x3dd5bd253d743797, 0x3e03520e3de45107, 0x3f351a2b3ea33576, 0x409033cb3f843683, 0x410d1f3840a1c1ab, 0x41e8879241281b2e, 0x427f362c4215fa54, 0x43d90b45434424c0, 0x442cef444421dad9, 0x44bc3f5644b097f3, 0x4554793345121b02, 0x45c2c17d45b8add9, 0x4621c71745e137e1, 0x474d7ffa46b5d1f1, 0x4815879e47e8ebdf, 0x487fef6a486c4590, 0x49d98f0548d9f878, 0x4a2850dc49effe07, 0x4abf0b844a91b2c2, 0x4b0ab2744ae3b213, 0x4b3999f24b366c99])
  | 5, 4 => (packedWords [0x4b6973174b3d781f, 0x4bc6e75d4ba4f77f, 0x4cc393a44bf6d648, 0x4ccce9aa4cc53c5b, 0x4d1dcabf4cdd2f1d, 0x4de204364dbd8851, 0x4e15844f4dffd918, 0x4e8f59194e4d206c, 0x4fccaaef4f08b0dd, 0x500d789e4ff06254, 0x51ae37c250418122, 0x520e4fae51ec185b, 0x521ae308520e620d, 0x52312a67522e9ae6, 0x533e1035528036d8, 0x53e1dacf5386686a, 0x540e662054037a3c, 0x5482e7dc544c14be, 0x556da8a855471305, 0x55ef0b7755d9a929, 0x5641e56f5610801b, 0x56bdea7c5643c1d6, 0x572bea1b56e9fe49, 0x579bbe715735b858, 0x58e2396758154a66, 0x592c61b659039b31, 0x5963e08559502394, 0x59f46a3059e23f1c, 0x5a9d858a5a01aa13, 0x5be322165ac3d538, 0x5c1201245be7a73b, 0x5c8b2ce95c1d7ee5])
  | 5, 5 => (packedWords [0x5cd985ef5ca79519, 0x5dbd6fcb5d209a2d, 0x5e1771d35e13aefd, 0x5e708b965e3dab0f, 0x5ed1f5225e71196d, 0x5f693c9d5f5087e1, 0x5f927c175f8a595d, 0x5ff23bf75f935cec, 0x60b57d39602abba8, 0x61648b8b61034e7c, 0x616b5d4c616aefda, 0x61b1912161768d8a, 0x62cbda3f61c15a9a, 0x62e9ff5862d9ea3c, 0x6337701e631fb4f4, 0x64facab564ae94c5, 0x65f0f8fb655e0414, 0x67066171660a8547, 0x67467ab3670b88e4, 0x67c935df67bfccbb, 0x68993412687e04a9, 0x690e27b268ebc542, 0x69be8517699eaae0, 0x69f15c2c69eebad8, 0x6ab827e46a144f7c, 0x6b26db286af28200, 0x6bf690636bcdeff3, 0x6cd2d34c6c1b803a, 0x6d146d7c6d0bed31, 0x6dee66dd6d9da8a6, 0x7054dc006fc442fe, 0x70a69cc770578bd1])
  | 5, 6 => (packedWords [0x70e959e070c5e863, 0x712efc24712b394a, 0x716ff72a715650d7, 0x7217da4271cd45ce, 0x7383779573138c16, 0x73c51cbb73acd4c2, 0x7447b6a273e569b8, 0x748660cf7461220c, 0x7514692574e581a7, 0x758ad129756ac15f, 0x75e75a4975ad9411, 0x761d98d3760ceede, 0x77087bb976e9be2d, 0x77b2a4ea779a155e, 0x78dcbdb277daa84b, 0x7900926b78e38010, 0x7a10770e79a77a22, 0x7b02452e7a624530, 0x7b0a4d497b0797e2, 0x7d1065df7c0648a6, 0x7de935537d3d956c, 0x7e0ec44f7dfac046, 0x7e1b4fdc7e14690d, 0x7f21e2387e46de5b, 0x7f70ef437f2462d3, 0x80a36a908057bcde, 0x81bfc5be8181014a, 0x820c3b6581e53aa2, 0x82cc63f282681393, 0x830c6ce882f65bab, 0x839c4884836b9290, 0x84bda9cb84b763ae])
  | 5, 7 => (packedWords [0x854867a28546f493, 0x858e5c2485688c7b, 0x8620c0d885e732ab, 0x87528b8386fb6960, 0x8869b31b87f53fcd, 0x89cb1a8f8901ad28, 0x8b4ede2f8b2dbc32, 0x8bb2cd718b8804cc, 0x8c621d718bbf8469, 0x8cd989048c805a9c, 0x8d33d19e8d20d279, 0x8ebac8428eaa28f4, 0x8f4f3bf58ef7bbcf, 0x8f65d57d8f63b5e9, 0x90a8e95f8fe03fe9, 0x9198c18690ea7447, 0x91ea63ca91a4a1b7, 0x926d8d1291f12f99, 0x933f7fa1931feaf6, 0x94f296039483eab9, 0x9509ac719508d1fb, 0x95c59479951ceccd, 0x9625a8a595e0a436, 0x9712af419659f6fd, 0x97e346e89771614b, 0x9879bad39870105c, 0x989e7d1a987ce967, 0x9916bf1898e7d79a, 0x9b08efad999698a8, 0x9bdcfe3e9b297bb5, 0x9c792abd9c5b0546, 0x9cd55bc09cac643d])
  | 5, 8 => (packedWords [0x9ce5d6039cde6ee0, 0x9d3e289f9d327e85, 0x9da9d0159d7ddfff, 0x9e281d069de68440, 0x9ed7b8c49e77edcc, 0x9f76e5939f16bfda, 0xa0109fe0a0089e99, 0xa102eb98a05b1be6, 0xa14ab624a129d2a0, 0xa215206ca1eb8b46, 0xa324382ba2b78ce5, 0xa426f34ea3f055e3, 0xa4ac1329a494c4f8, 0xa51cdcc2a4d81d11, 0xa55ab52aa5322864, 0xa5c736fea5b2bcb6, 0xa62c65c0a5e71ae4, 0xa6791663a62ccb33, 0xa7bdf19ca6e2fe4c, 0xa81584b9a7cb461a, 0xa91a8f8da8335a86, 0xaa1e18f3a9a65ee0, 0xaaee2376aa3c5d56, 0xab0aff36aafdbf53, 0xabe28e6bab601198, 0xacec7739acd6576a, 0xae368b0aad7f9986, 0xaf7b1227af20c6f6, 0xaf9f0089af823a2e, 0xb09cb20fb029f4b1, 0xb24bc742b10479b5, 0xb2d6bbb7b274b26f])
  | 5, 9 => (packedWords [0xb3807a20b2e05915, 0xb41a2e52b3b267d4, 0xb47c0955b4290a17, 0xb4bb5b6fb49a530a, 0xb56efdeeb5588bd2, 0xb5b7e9e8b578cfc8, 0xb6fa4e1eb632c511, 0xb75e4bf3b6fba1ac, 0xb7da8970b764de1d, 0xb891282ab86bd33a, 0xb8d28b02b89575af, 0xb9ba9e09b996cea4, 0xb9f37d3db9e7fb00, 0xbafab14fbaf80ffb, 0xbb972cb9bb584c22, 0xbcfee437bca86d40, 0xbd5eb040bd3aa094, 0xbe176eeebdbf0f1b, 0xbea6fdc9be1dc29f, 0xbf29faefbef7bc00, 0xc000dfbabfdbacad, 0xc022d7a3c00c871d, 0xc06f25a2c03a17e7, 0xc0ed7e74c088f644, 0xc1278e5fc10ce96b, 0xc1d21f0cc140e85c, 0xc1f43720c1d5eb38, 0xc2d303b3c2794c4d, 0xc3699558c309df2e, 0xc3a3b7ddc3753cbb, 0xc49913b3c47fd347, 0xc4f043c4c4d2f054])
  | 5, 10 => (packedWords [0xc593fefec57dfd13, 0xc62bdee6c5aff0df, 0xc6833923c66f842a, 0xc70d4db8c6b9e2d8, 0xc730650cc718f7d2, 0xc8762f32c75b28bb, 0xc898184cc8793c14, 0xc8e67093c8d0aff8, 0xc922efc4c8f2463a, 0xc98011c4c96e1ce8, 0xc9b5db9bc98f8bed, 0xcafc65afca254f65, 0xcb6622c0cb19ca9f, 0xcb8fb816cb8488b0, 0xcba51753cb94634b, 0xcc4fa4cbcbb0552c, 0xcc8c0f67cc8bd861, 0xcd950f8ecc956f92, 0xcdc9b7e8cda75786, 0xcedd2721ce319721, 0xcf383516cefff152, 0xcfaf80a8cf8ff03a, 0xd07a4466d0279024, 0xd106bf04d07a6eee, 0xd29d7ef2d1b50fe3, 0xd30ee3b4d2c36e64, 0xd3430699d311145b, 0xd372df2bd3609a75, 0xd381d475d374908a, 0xd409c679d3db98a9, 0xd44daeb7d4172c89, 0xd522bc5dd506cfa8])
  | 5, 11 => (packedWords [0xd6388116d6308d42, 0xd6fb2b2fd6a9be8e, 0xd803a1e9d72ee0f9, 0xd887a8edd881b874, 0xd94e6b33d926382c, 0xd9b67149d9aa2e47, 0xdad46fb2da75c9e6, 0xdb77bdc9dafdf79f, 0xdbcbe50ddbaa8f45, 0xdc38e563dbe6fd16, 0xdcd4e0f5dc961081, 0xdd4e75b3dd0b77e1, 0xdde2bbdeddd62390, 0xde0a729cddf4fd85, 0xde984076de821cc1, 0xdfaa9294dfa33f88, 0xdfd5ea16dfcae77e, 0xe0db6e22e0112ce7, 0xe14206b4e109e0a5, 0xe1c19188e1680cf5, 0xe2adf6dae2aaaec9, 0xe31d117fe2fa11f3, 0xe448d4c4e3245189, 0xe4df1156e46b9e69, 0xe545f4dee5308ef2, 0xe5a52adce591da6f, 0xe5b82a1de5a6f0f0, 0xe67ba240e64805ff, 0xe7b260f1e70a44f2, 0xe8469234e835c26c, 0xe95cc67fe850c51e, 0xe9c107b7e97352eb])
  | 5, 12 => (packedWords [0xeb47f53eeb0fa3ab, 0xeb7907bbeb611d62, 0xec32d0d8ec189a2d, 0xecdd2639ec9f94d7, 0xed2a5708ed21fd80, 0xedc7243ded4ca905, 0xedfab879edd16626, 0xee5dcadbee3bd3a8, 0xeea0be62ee873522, 0xef065d7aeebea490, 0xf0072bdcef974724, 0xf07c8337f00ba849, 0xf0b1cc21f0a9c132, 0xf0f2470df0db7563, 0xf1f85bd4f0f4a742, 0xf2b30ea0f2540b47, 0xf2efc4b6f2de6a7b, 0xf3cbfe51f399adf0, 0xf3f584acf3dfd091, 0xf4c595f3f47cbb67, 0xf57556c0f506c1c7, 0xf6d08c21f5b5684c, 0xf70c3276f6f07007, 0xf889f2baf7c6b5c5, 0xf8aff5e7f8a8336f, 0xf8e6fc9af8e113ae, 0xf91efbb4f904afb2, 0xf9dcff62f98f47ae, 0xfa8f2065f9e48252, 0xfaf63a73fa9f437b, 0xfb7260fffb23ff6e, 0xfc89fee0fbdd9af0])
  | 5, 13 => (packedWords [0xfd7c5632fcebe38e, 0xfdfb4a94fd96b743, 0xff20202cfe77a8d8, 0xff7a13bcff454b52, 0xffbccc87])
  | 6, 0 => (packedWords [0xfe7fe000827e9a, 0x2f3f47b0189ffc0, 0x3e9ae3d03d15566, 0x4d3a237043dbde2, 0x4f0d7bb04dae076, 0x507a036050115b6, 0x52f60bc050a024b, 0x55a120d055754e8, 0x5bda03b05855e7d, 0x7e73809068224f0, 0x848d4f708022447, 0x8a8481f08781a17, 0x9938e1d08fd97ef, 0xa7fa6100a575836, 0xb2fc5090a8d77c1, 0xb89b2440b56f832, 0xd01745a0bc27a4f, 0xece93df0ea8ac6c, 0x101d36c40f20c416, 0x106a1f75104636e7, 0x1122831910806eb8, 0x1176c0161166d6cd, 0x11d37b6011924b6c, 0x13084d8a12163e93, 0x1534215213544778, 0x17169c2a16ecc870, 0x17b348851735340e, 0x1816a2e017f8fe0c, 0x19a8e5ba1972165c, 0x1a94c72b19e1fb14, 0x1ade113f1ad12091, 0x1c47f1b91b90417b])
  | 6, 1 => (packedWords [0x1c998dab1c8dddd8, 0x1cb804751ca5140c, 0x1dbffcbc1d952d89, 0x1e1cd10f1dd3158b, 0x1ecbc9491e9c3eaf, 0x1f9e45251f602073, 0x21196e8d2112a9f3, 0x2131af3e212508e4, 0x21bf508421bc5526, 0x2235923f21defc9b, 0x2317e64b22ae7b27, 0x2394e69e2353c313, 0x241576072409eea3, 0x2469ef9d242b0dbd, 0x24cc2d9624aa96a1, 0x251258ad24e1f5f5, 0x258c55b3251c68b1, 0x25d6250c25cdc3ce, 0x2667166e2646cd52, 0x2725b61f26ccac6b, 0x27510c1b27439e47, 0x282d05d027d6c69e, 0x29954aeb2909dde2, 0x29b8327629a332b1, 0x2a37a46d29e466c7, 0x2b244cc62a5dee46, 0x2be1415b2b934eca, 0x2c1367832c059739, 0x2cf0523e2c1aaac5, 0x2d4402942d3be7d5, 0x2d61ba7b2d619b5c, 0x2e188d152d9dfcab])
  | 6, 2 => (packedWords [0x2e9c715c2e81fc03, 0x2f775ae72ee26f69, 0x309c74db3086785b, 0x30f38e0530a7256c, 0x3196c3873161a8bb, 0x324893f9321b0f12, 0x32bb94893271621d, 0x33aac67633922c45, 0x34760f28346c7568, 0x35bfdf7934fc7265, 0x35f2143d35e8667e, 0x369b2f9736958a45, 0x36f3bca636c17f45, 0x37808073371e0027, 0x385ea38c3848f846, 0x3933d24038a01170, 0x3ace17cb393449a3, 0x3b41a6003aef1e63, 0x3c37fc4d3c18f8d3, 0x3dd93c6a3ce3c1bf, 0x3f0de76f3ec9a579, 0x3f9735203f34adf0, 0x400c5fea3fd9701f, 0x4089ec844080f72e, 0x4159578c412d628c, 0x434424c0427faf1a, 0x434ba6d64345ecc9, 0x440fa5d54374216e, 0x445cf967442038f8, 0x45117f01446f965e, 0x458d5c1e453baff9, 0x4622c0ec45beab19])
  | 6, 3 => (packedWords [0x46745cde4629657a, 0x46b0d11a467fed49, 0x46f5097e46b5d1f1, 0x47f7a042470b5a04, 0x4843dee9481cf947, 0x48770de24860352e, 0x48a0b1c848801367, 0x493aefa648af3860, 0x49d5881749728a17, 0x4a2ca1414a2850dc, 0x4a9ebfde4a5dbf1c, 0x4b2494f24ae6b6c8, 0x4bd91c914b53620e, 0x4cf56dcb4cc66ad8, 0x4d246c254d0bbe51, 0x4da588a44d5cbeae, 0x4e0a61fa4de70c35, 0x4e43ab1c4e15844f, 0x4ea1fba54e4ae27b, 0x4f5c19f74ed71685, 0x4fb8b3b04fa01978, 0x5092939d505e2369, 0x51b195d150dbb828, 0x521ae3085207d503, 0x533e1035526e9947, 0x544f795754440f69, 0x54c2cccb54a9a33f, 0x55369825551cb63f, 0x55860f4455471305, 0x574cc42f55b79230, 0x59039b315900391e, 0x59abf0c559522a1a])
  | 6, 4 => (packedWords [0x5abe45f959f76615, 0x5ba6f8e75ac72f82, 0x5be5b0825ba799e6, 0x5d06718e5c52bbd0, 0x5d6e33fb5d64e84b, 0x5e1771d35dbd6fcb, 0x5e2fc20d5e2f8c31, 0x5ed1f5225e81fd9c, 0x5fac55125f43fbf3, 0x5fdeeb4c5fdc9a72, 0x609aa4b45ff7ca62, 0x612de91660aee191, 0x62a8f3b561fc9dbb, 0x62ed557d62b4676e, 0x630da88662f75800, 0x63dd1d98633c04ba, 0x64b3a6f06436f814, 0x65561e4065532d77, 0x6655165265b1d4be, 0x66ac2f7c66600d9e, 0x66b369df66ac47de, 0x67c3f08366c5bb10, 0x687e04a968554812, 0x68c79a5468b4cbbb, 0x696f1006692f1cc4, 0x6a375c616a2516df, 0x6a45f99e6a3eaa12, 0x6a76b2d16a7472b9, 0x6b327cfb6ab03345, 0x6bda75b46b4988d1, 0x6c5c52636bf9f635, 0x6cb3ce2c6c7d8231])
  | 6, 5 => (packedWords [0x6dd3dd016dc454d0, 0x6f167e966e65b76b, 0x6f8e9d096f4b7f37, 0x7048cddf6ffacc03, 0x70988679707637d9, 0x71cd45ce70b93e51, 0x723b046171da43fe, 0x733ee762731888d9, 0x73588f35734d4c84, 0x74e581a773c5a89a, 0x755df71575146925, 0x75ae3f477579686b, 0x75e75a4975b3ebc4, 0x760a2af675f9b497, 0x76d6aedf76bc0f28, 0x779a4e8276f42aaa, 0x77db2b1b77daa84b, 0x78abf932789d8ac4, 0x791749ce78e38010, 0x79759123795cb281, 0x799382e3798fe8d2, 0x79c60ce779a77a22, 0x7a142df57a10d62b, 0x7c2a0d6c7ab480b2, 0x7ca3c5a07c651e15, 0x7d1065df7cf48ef7, 0x7d54800d7d461f22, 0x7de935537d9ab2cf, 0x7eb6b5f07e2f43f7, 0x7f7c2ad27f21e238, 0x7fec95dc7f7e711c, 0x80b4e4ff80394696])
  | 6, 6 => (packedWords [0x8107f3de80c581c3, 0x81bfc5be81b07a8f, 0x8272809281e95097, 0x82f65bab82b5b861, 0x8327de9783108ff0, 0x837b5857834ed303, 0x83c63f0583862f31, 0x848b14af83e94681, 0x852c1ff785046608, 0x85b0838c85413053, 0x8608a28d85e4773e, 0x86a54ee8864a36a6, 0x86c5e61086b8bdb0, 0x86fb696086e6a914, 0x87624e0b8731c080, 0x8880f423885ea0e5, 0x89cf5f0689b9ba7f, 0x8a25ddf08a02375b, 0x8b2dbc328a3c2e76, 0x8b7cc0098b3f5abe, 0x8c0906da8bd76cee, 0x8c77fea78c579e05, 0x8d0831bc8ca5b335, 0x8e192d568d8e938e, 0x8e2512328e228f7b, 0x8edbade68e521595, 0x8fc7f71c8f702061, 0x903f286990170f47, 0x9136b16290a08a43, 0x9188e19991747f8e, 0x919a9bee919341a7, 0x92e3c0e7923dc593])
  | 6, 7 => (packedWords [0x936e454c92f6792c, 0x944f41ec939c9d04, 0x95c5947994e14376, 0x9609000895d73305, 0x963d5a5496177394, 0x96cd9bb596b6cf34, 0x982212b9971adecc, 0x99264e6a987a9dd8, 0x9a208bc699b641b7, 0x9b5466df9a414b7b, 0x9ba815019b59d6a8, 0x9cc7d0459c327435, 0x9d27d2629cdcc537, 0x9d5f08749d283a87, 0x9de684409da507e3, 0x9f54379e9f459092, 0x9fca1b229fab50c8, 0xa068d4bc9fd11319, 0xa1c2f035a07ce739, 0xa20af10fa20662a8, 0xa2a79d6aa2448b94, 0xa324382ba2b78ce5, 0xa37e80c5a35e7bcb, 0xa5e53be0a41e78eb, 0xa767cc86a63fed48, 0xa8312bfca77a7630, 0xa9dd68d9a95ee018, 0xa9e43e51a9e124c6, 0xaab3e33faa3095e1, 0xab05c9ccaaf4c4f5, 0xac195dc9ab0aff36, 0xacec7739ac47cbc6])
  | 6, 8 => (packedWords [0xaeed21e9add02869, 0xaf8b52bfaf20c6f6, 0xafd322c6af8d26d5, 0xafe18913afd9c2e1, 0xb0d574b5b07fc513, 0xb0f2aea3b0d77878, 0xb1c6dc0cb1534bc0, 0xb274b26fb1ea9f53, 0xb3f686a4b3372861, 0xb416fda9b400ad23, 0xb4a2e036b4290a17, 0xb4ca6458b4b0b17c, 0xb59764f9b543c5ae, 0xb6d8885db5a2d77d, 0xb6fba1acb6f67d0c, 0xb76962c1b74fedf4, 0xb85197dfb7e6f780, 0xb8c22024b8a3b497, 0xb8d4e1b4b8d28b02, 0xb997f80db97fcecd, 0xba456871ba24ff1c, 0xbacb22f4bab115c9, 0xbb0d5ca9baeb6fe9, 0xbba33bcabb4f4ec1, 0xbbda6a67bbda344b, 0xbc978f07bc318391, 0xbd28a45dbd07e2f2, 0xbd4d24c7bd45d716, 0xbde5273abd91cb91, 0xbdf843a7bde55524, 0xbe18d9a6be112954, 0xbe580387be22e1b9])
  | 6, 9 => (packedWords [0xbec28471bea6fdc9, 0xbf07c3d9bef7bc00, 0xbf60ca4dbf4ceb6d, 0xbfaa6af4bf84908f, 0xc045ccbebfdda62e, 0xc10ce96bc0cb8741, 0xc297f354c2794c4d, 0xc317af3dc2b891b5, 0xc36a6349c3568d91, 0xc4fd09bfc3f65635, 0xc5e37348c5082826, 0xc6b7946ac646bee3, 0xc70d4db8c70309ba, 0xc790d82dc73df2b5, 0xc8451be5c7c2dd79, 0xc92c44cec90e17e9, 0xc98f9447c93976ff, 0xc9e52994c9d6235a, 0xca42433bca2816b5, 0xca583083ca57b66c, 0xcc9df1ffca93ba78, 0xcd112494ccbe2d3d, 0xcdf87129cde3dca1, 0xce6615cace360256, 0xcfc00b13cf5aaa25, 0xd0cd98c0d0b2fffe, 0xd1a0b996d1429bb9, 0xd347e3b9d1a525ff, 0xd3bf0d84d38da8b2, 0xd43666a3d3fda45d, 0xd5c5ce49d4cf9428, 0xd67961d1d647b6f3])
  | 6, 10 => (packedWords [0xd6cd7176d67ab3ab, 0xd76659fbd6f5daf0, 0xd7effe37d76afe24, 0xd819539cd8030316, 0xd8db119fd83b15a3, 0xd9171d42d911d884, 0xd968b934d967f608, 0xda85e1cbd9b3c99d, 0xdb00113edaebfc98, 0xdd046678db6bb8b4, 0xde40f4dfddf4fd85, 0xdf51a4b4df17818f, 0xdf9127eedf691d81, 0xe0d14c3fdfb42dea, 0xe1bb4a43e0ec60e5, 0xe386eff3e1e8dbed, 0xe3ffce4fe3ff91e1, 0xe4746bc8e448d4c4, 0xe4a5f227e4936ca5, 0xe68f503de4fc3159, 0xe7bff66de6f62da6, 0xe850da9ae7c02457, 0xe9c4e7a2e9177abd, 0xeab9ea5dea3850d8, 0xeb055fadeafc95a6, 0xeb68900eeb68630e, 0xec32d0d8eb949dca, 0xec7e18c0ec468670, 0xedd12568ed11f938, 0xee6624b7ee3bd3a8, 0xee9bf63cee6a2fd7, 0xf024e11defcaf39c])
  | 6, 11 => (packedWords [0xf19dacacf0a41160, 0xf246eabdf205a314, 0xf2540b47f249b371, 0xf3144632f27ee164, 0xf3b0f28df35e12e6, 0xf4c00631f3c26106, 0xf5196bc4f4ee04e9, 0xf544f1acf527ce0e, 0xf5b5684cf56b07b6, 0xf6caa91ff5e1b1d3, 0xf6ee4b1af6ea70bc, 0xf77c86a8f74d9f2a, 0xf7c16377f7975ca0, 0xf8d1d6acf7e185ee, 0xf8d3abeff8d1ea1b, 0xf9f16498f99a4b6e, 0xfac0ccd6fa45acc5, 0xfbf2f496fb5db93a, 0xfcebe38efbf9f396, 0xfd6a4bfbfd22b2ec, 0xfdc25df4fd763ce3, 0xfdf5eb2dfdf2b93e, 0xfe1dfc20fdfbf766, 0xff85dd30fe4adee3, 0xffc86379ff8f9a30])
  | 7, 0 => (packedWords [0x12163e93106a1f75, 0x1816a2e016ecc870, 0x22ae7b2721bc5526, 0x27d6c69e27510c1b, 0x2e188d1529a332b1, 0x4622c0ec3b41a600, 0x47f7a04246745cde, 0x554713055207d503, 0x723b046159522a1a, 0x7f21e23875b3ebc4, 0x90a08a438bd76cee, 0x99264e6a944f41ec, 0x9f54379e9ba81501, 0xa324382b9fab50c8, 0xaf8b52bfa63fed48, 0xb416fda9b400ad23, 0xbb4f4ec1b76962c1, 0xc70309bac6b7946a, 0xd1429bb9cfc00b13, 0xd4cf9428d3bf0d84, 0xe0d14c3fd967f608, 0xe4a5f227e3ffce4f, 0xedd12568e7c02457, 0xf3b0f28df3144632, 0xfd22b2ec])
  | 8, 0 => 0x7f21e238
  | _, _ => 0

private def packedBlocks : Nat → Nat → Nat
  | 2, 0 => (packedWords [0xbd2f41cded4bd0c3, 0x17541cdee4bd0c37, 0x75430d995d50c369, 0x18f6150c3669])
  | 3, 0 => (packedWords [0x304e46692f4303f4, 0x3d2f4309d46692f4, 0x4bc463d2f4308d46, 0x1a45d50c46d9513c, 0x9d46912f41c5b48b, 0x2f414bc463d45430, 0xc470da46150c463d, 0xf4308f489da46250, 0x47b5c35450c463d2, 0x4309d4805f44bd0c, 0x691764bd0746692f, 0x450c46dda4408704, 0x912f41c61489def5, 0x9d47fdfd4bd0c46, 0x92f4307e46912f41, 0x747d1b7430bc466, 0x514109d47bdc3545, 0x746692f43060463d, 0x35450c463d2f4309, 0x46f1513c0bc47b9c, 0x3c0bc46692f41c4e, 0x6692f4305b470d44])
  | 3, 1 => (packedWords [0x1c4e46912f41c3f4, 0xadef4bd0c46912f4, 0xd0c46d9514309d48, 0xd2f384a1463d864b, 0xc47c9a44bd0747b, 0x2f3848d47c58f4bd, 0xe46dda44309d4691, 0x13848d46912f41c5, 0x4669764bd0c463d5, 0x430b2463d694bd0c, 0x6912f41c9d463d2f, 0xd50c48b1ef4bd0c4, 0x912f41c7e48ada45, 0x87046dda44308f46, 0xd865450c46912f40, 0xc469175384a1463, 0x2f4303f47c59a4bd, 0xe46e1284309d4665, 0x44bd0c46652f4304, 0x7c5a])
  | 4, 0 => (packedWords [0xc95f4785c3430bc5, 0x304e470da44bd0c2, 0xbd0c2750006692f4, 0x912f4307050018f4, 0xd9a5210c1396216, 0x15c36915141c9d57, 0x9a58b1ef70d5143, 0x12f4315c36915143, 0xd0c2f04e5805e769, 0xd2f430bc27559a4b, 0x5a44bce12843f563, 0x7057f5b84a10c2f1, 0xc1c1623765c32f0, 0xe12844e5881b7691, 0x514bd071395a44bc, 0x16912f430445691, 0xd57b1c35450c2756, 0xc2f15c3675514309, 0xf430bc57f58f4bd0, 0x46195143162963d2, 0x46412f4309d570da, 0x57f58f6212f4315a, 0x1396026912f41c70, 0x3c4bc56912f4690c, 0x545021c158f4bd0c, 0x691424309d570da4, 0x8b19a4bd0c1395c3])
  | 4, 1 => (packedWords [0x315c36918441c705, 0xf07057c5c3669514, 0x450c2755994bd0c2, 0x912f4303f56f1a45, 0x912f41c8b1c162c6, 0x15c3665514303f56, 0x4e56dd9d430bc1c, 0x50c13962c6912f43, 0xda45450c570d9954, 0xdc35450c25d5f170, 0x5e070d514309d57b, 0xbc57bdc34bd0c285, 0xbc1115f463d2f430, 0x513c0bc56dda4430, 0x2f430bc1c162670d, 0xa44bd0c41c4e5669, 0x570d9d2f0440c95, 0xc2755a44bce12847, 0xf4308d570da44bd0, 0x4430a11c15c36912, 0x3674a11c03256dda, 0x570d9a5450c0fd5c, 0x2755c3691444309d, 0x43070570da454508, 0x544fb28559a6212f, 0x6912f430bc570da4, 0x70d9a5450c1395f5])
  | 4, 2 => (packedWords [0x755b86750c2f0705, 0x304e570d8f5450c2, 0x450c2755dc6912f4, 0x3d514308d56e1a45, 0xeda4544a11c15c36, 0x120c7bd51430bc56, 0x9d5001a44bcf61c, 0x4d21c15c36495143, 0x12f4309d56912f38, 0x1c35450c2f162869, 0x5c3691464309d57c, 0x9d570da45a551431, 0xc27562863d51430, 0x51400705785c3691, 0xa45150c2755c3691, 0xa44bd072f044570d, 0x2570da45a1514315, 0xc2755c369151430b, 0x44bd0c570da45210, 0xf41ca11c162c7c9a, 0x44bd0c3849d56912, 0x5805a44bd0c1395a, 0x1795fd6692f430bc, 0x1c04e58b1a44bd0c, 0x4bce12855a44bd07, 0x7f58f4bd0c57f5a4, 0x63d51430e1275601])
  | 4, 3 => (packedWords [0xf15f96692f430bc5, 0x30a1570da44bd052, 0x44e12855ef70d7c4, 0xe12f430bc57f58f5, 0x91784bce128559a5, 0xd5b76910c3ccbc56, 0x9d570da44bd0c23, 0x4a11c162c6912f43, 0xd072f06756655138, 0x1a45f10c2855a44b, 0x5c36912f41c4e583, 0x99570d8f5450c23d, 0xc2855c369151430, 0xc2f04e570da45d5, 0x9a4bd0c1c15b7691, 0x17d1c35450c5805, 0xd570d9c5450c2756, 0xc1c15c3669514309, 0xf4304e5805a44bd0, 0xf4bd0c2755a46692, 0x170da44308f56918, 0x57bdc35450c2855e, 0x27559a5452f4304e, 0x4309d563d514bd0c, 0x545071855c369149, 0x6912f41c4e470da4, 0x70da45450c275400])
  | 4, 4 => (packedWords [0x355ef70d51430b15, 0x307e570da45450c2, 0x90a11c122c6912f4, 0x914841c4e5001b76, 0x912f41cbc1395c36, 0x158f4bd0c1382856, 0x9d57fdfd70d5143, 0xd784315c36915141, 0x151430bc570da461, 0x151374bc1115f26f, 0x5c3675514309a56f, 0xbc5795a44bd0c2f1, 0xa11c15ef70d2f430, 0xc3e47056f151374, 0x9a5450c1815a44bd, 0xc36912f43097570d, 0xc56dda4430bc1c15, 0xc2f15bc691513c4b, 0xd2f04457c9c35110, 0xd6912f4315c3510d, 0x363d51430975805f, 0x563d2f430bc2815c, 0x2715e070d513c4bc, 0x28470570d9c5450c, 0x5450c2755c3510dd, 0x6d951430bc56f9a4, 0x8b1a44bd071395fd])
  | 4, 5 => (packedWords [0xf15c3691443c4bc5, 0x30a1570da4545052, 0xe12f4315fd63d2f4, 0xbd072f0705805a45, 0xda45450c27159a4, 0x55ff6912f4307057, 0x9d570d915450c27, 0x50c2355c36918943, 0x12f4305b570da462, 0xda45450c26162c69, 0x6016912f43060570, 0x4e56fda45450c275, 0xbc1c15c36695141c, 0x514308f56912f41c, 0x2f430f32f15c3691, 0xc3691844309d563d, 0xe56652f430a11c15, 0x70fd616691514304, 0xf41c70570da45450, 0x76910c2f15a46212, 0x36915141c4e57f5b, 0x570da45450c2795c, 0x4315a46312f41c70, 0x2f04458adef70d51, 0x5f10c2f159a4bd0c, 0x70d514309d57bdc3, 0x6912f384a11115ef])
  | 4, 6 => (packedWords [0xf15ef70d514308d5, 0x309056912f3c4e12, 0x30a11c15c3691514, 0x91675450c56692f4, 0xda46192f4315c36, 0x15be690a11c03257, 0x435839b76910c2f, 0x701395a44bd072f, 0x4f1384bc56692f43, 0xd2f4309d1c158f54, 0x5e270d284309d563, 0x705831ef5450c285, 0xc2f15b869151408, 0x75430bc5831a45f1, 0xa44bd072f15c3691, 0xc36914a4309d57f5, 0xd57bdc3544e12855, 0x11c15c3691514189, 0x454507569147384a, 0x45450c2755f270da, 0x3691394309d56f5a, 0x57c5c363d514315c, 0x2f15c3691513848d, 0x2f06757c98f4bd0c, 0x5450c2f159a4bd0c, 0x5e12f41cbc57bdc3, 0x70d9a4bd0c1395a4])
  | 4, 7 => (packedWords [0x795c363d2f4309d5, 0x309b570da4545071, 0xd92f4315c3691514, 0xbd0c3d87058b1a45, 0xada44bd0c0fd5a44, 0x9627691514309d58, 0x8d58ada44bd0c13, 0x50c2f16276915143, 0x1514309757d1b854, 0x1a44bd0c1855c369, 0x5c3691885dd0c58b, 0x9d57f5b55450c2f1, 0x2f4315fd63d2f430, 0x514303f570da45a5, 0xa45450c2195db691, 0xdb691514304e570d, 0x70da46090c1c15])
  | 5, 0 => (packedWords [0x70d8f5450c3ccbc6, 0x79da463d2f430bc6, 0x8b1a44bd0c284706, 0x7f5bd69151430bc6, 0x7f5c369139430bc6, 0x70da45450c2b8706, 0x70da44bd0c2f03f6, 0x70d995450c284706, 0x70da45450c2f0566, 0x7f5c369151430b86, 0x70da45450c2f0726, 0x70da44ed0c2f0706, 0x819c369151430bc6, 0x70da44bd0c2f04e6, 0x70da45450c224706, 0x7d1c369151430976, 0x79dc369151430bc6, 0x8b1a44bd0c1c04e6, 0x70da44f10c2f0446, 0x70da46315141c706, 0x70d9c5450c2f0446, 0x6f9a45450c2f06a6, 0x7f5c363d2f430bc6, 0x70d9a5450c2f0446, 0x70db3691514309d6, 0x1c36915141c435, 0x7f5c369151430b46, 0x63d2f430dd2f0706, 0x70da45110c2f04e6, 0x70d9d5450c2dc706, 0x729c36910c2f0706, 0x70da45450c2748b6])
  | 5, 1 => (packedWords [0x70da44dd0c2f0706, 0x70da45a951430bc6, 0x7bdc369151430a16, 0x805a45452f430706, 0x70da45450c3a0bc6, 0x70da45450c2f0556, 0x70da4544e1284446, 0x70da45450c254706, 0x70da45450c2dc446, 0x70da46212f4304e6, 0x6918f4bd0c2f0446, 0x70da4544f1384bc6, 0x70da44bd0c274706, 0x70da45450c31c4e6, 0x6e1a45450c2f04e6, 0x70da45c1514304e6, 0x6d9a45450c2f0706, 0x70da4691514309d6, 0x1f470d7f430bc5, 0x70da44bd0c2f0586, 0x70da44f90c2f0706, 0x70d9c5450c284706, 0x70da45e139430bc6, 0x70d9a5450c284706, 0x785c36910c3ccbc6, 0x7c9c369151430a16, 0x70d9d5450c2f0706, 0x70da45450c3a4bc6, 0x70da45450c2f06f6, 0x70da45250c2f0446, 0x70da45450c2809d6, 0x70da65450c2f0706])
  | 5, 2 => (packedWords [0x70da45450c2f0446, 0x70da45d951430bc6, 0x1c35450732c705, 0x6918f4bd0c284706, 0x70da4545072f0436, 0x1d270da4545075, 0x70da45450c2f0796, 0x70d9a5450c1c04e6, 0x70d8f5450c274706, 0x70da45010c2f0706, 0x1c3510dd2f0705, 0x70da45450c2fc706, 0x70da45c52f430706, 0x70da45450c2f0416, 0x70da45450c2845e6, 0x70da4544e4284706, 0x1fd70da4545075, 0x8b5c3691514309d6, 0x70da45250c284706, 0x691904bd0c2f0706, 0x70da45650c284706, 0x70da45450c2f0716, 0x70da45450c2f0616, 0x70da45450c284706, 0x70da45450c21c706, 0x785c36910c2f04e6, 0x70da45090c2f0706, 0x70da462151430446, 0x70da44c50c2f0706, 0x70da45450a2f0706, 0x1fd63d2f430bc5, 0x70da45450c0fc286])
  | 5, 3 => (packedWords [0x70da45450c284656, 0x1a45450c2748b5, 0x70da45450c2c4706, 0x70da45210c2f04e6, 0x82da44bd0c2f0706, 0x70da45450c138286, 0x70da45450c2845f6, 0x70da45450c308706, 0x1c36cda45450c5, 0x8b1a44bd0c2f0676, 0x83dc369151430bc6, 0x70da45451d4309d6, 0x70da45450c3d4bc6, 0x70da45450c2c4656, 0x8b1c36912f4304e6, 0x7f5c36915141cbc6, 0x789c36750c2f0706, 0x70da55450c2f0706, 0x1c366951430675, 0x70da45450c1382a6, 0x70da45450c288706, 0x70da453d0c2f0706, 0x70da44c10c2f0706, 0x789c3691514309d6, 0x715a44bd0c2f0706, 0x70d9c4bd0c2f0706, 0x70d9a4bd0c2f0706, 0x6912f430e12f04e6, 0x6f1a45450c2f0706, 0x70da45dd2f430bc6, 0x7c9c36912f430bc6, 0x70da45450c348706])
  | 5, 4 => (packedWords [0x70da44bd0c334bc6, 0x70da45450c220706, 0x70da44bce1284706, 0x8ada44bd0c2f0706, 0x70da44bd0c2dc706, 0x6f1a45450c2f0656, 0x7e1c369151430bc6, 0x70da45450c3d0bc6, 0x70d965450c2f0706, 0x7f5c369151430896, 0x6dda45450c2f0706, 0x70da4545012f0706, 0x7c9c363d51430bc6, 0x70d9a5450c2f0676, 0x70da44bd0c2f05e6, 0x70da45450c2741c6, 0x70da45690c2f0706, 0x70da45450c2a4706, 0x70da45450c32c9d6, 0x7bdc35450c2843f6, 0x70da44bd0c2f0706, 0x70da45450c2849d6, 0x70da45450c3d8706, 0x8adc3691514303f6, 0x1e170da4284705, 0x6c5a45450c284706, 0x7d1d270d51430bc6, 0x7f5ec70d51430bc6, 0x70da45f10c2f03f6, 0x70da45450c2848d6, 0x7f5c36912f4309d6, 0x8adc3691514304e6])
  | 5, 5 => (packedWords [0x70da45050c2f0706, 0x70da45b151430706, 0x70da44bd0c2d4706, 0x70da44fd0c2f0706, 0x70da44bd0c2f0656, 0x70da45f10c2f04e6, 0x75dc35450c2f0706, 0x70da45450c2f0a06, 0x70da45450c2f03c6, 0x76da45450c2f0706, 0x6f99d5450c2f0706, 0x70da45110c2f0706, 0x70da4545082f0706, 0x7f5c367551430bc6, 0x8c1c3691514309d6, 0x8b1c369151430616, 0x70da45450c2744e6, 0x22c6912f4304e5, 0x70da45450c2f0926, 0x70da45450c2f05d6, 0x70da45450c2d8696, 0x6f9a45450c2f0446, 0x1c36910c3b09d5, 0x70da45450c2f0676, 0x70da46212f430706, 0x70da45110c2f0656, 0x6e1a45450c2f0706, 0x70da45450c30c706, 0x70da45c151430706, 0x70da45450c2843a6, 0x19a4bd0c2f0705, 0x7f5c363d514309d6])
  | 5, 6 => (packedWords [0x70da45450c2845c6, 0x70da45550c2f0706, 0x705a45450c2f0706, 0x1be690bc1c0325, 0x70d9b5450c2f0706, 0x70da45450c358706, 0x70da45450c2f05a6, 0x8b1c3691484304e6, 0x70da46110c2b8706, 0x1a44bce1284705, 0x1c36912f4309d5, 0x70da44e10c2f0446, 0x7f5a46412f430bc6, 0x6f9a45450c284706, 0x70d955450c2f0706, 0x7f5c369151430a16, 0x701a45450c2f0706, 0x70d9a5210c2f0706, 0x70da45450c2f0756, 0x70da45450c2f0536, 0x70da45450c2f0766, 0x70da46110c224706, 0x70da45450c2cc706, 0x70da45450e2f0706, 0x7f5c369142430bc6, 0x70da45450c2f0426, 0x8b1a44bd0c2f04e6, 0x70da45190c2f0706, 0x1a44bce42f0705, 0x7f5c369151430b16, 0x1c3669514304e5, 0x1c363d514309d5])
  | 5, 7 => (packedWords [0x831a45450c2843f6, 0x70da4545112f0446, 0x885c369151430706, 0x70da457551430bc6, 0x785c36910c2f0706, 0x861c3691512f0706, 0x70da45450c2e4706, 0x70da458151430bc6, 0x6912f384bc284706, 0x70da44bd0c2f09d6, 0x691514bd072f0706, 0x70da45450c2f0786, 0x70da45450c2f0396, 0x70da45450c29c706, 0x70da45450c3c4a16, 0x70da45cd51430bc6, 0x70da45210c2f0706, 0x70da4545284309d6, 0x70da454511284706, 0x70da45e151430a16, 0x7f5bc69151430bc6, 0x70da45450c2f07a6, 0x70da45450c2f0456, 0x805e770da45450c6, 0x70da46110c2f0446, 0x70da45450c3ccbc6, 0x70da45450c2f06d6, 0x6912f430e22f0706, 0x70da45450c258706, 0x70d9c5450c2f04e6, 0x70da460d0c224706, 0x70d9a5450c2f04e6])
  | 5, 8 => (packedWords [0x70da45450c2b4706, 0x70da458951430a16, 0x70d8f5450c2f09d6, 0x70da45450c2a8446, 0x70da4544e12843f6, 0x6e9a45450c2f0706, 0x70da452d0c2f0706, 0x70da45450c2f03b6, 0x70da44bd0c2f03a6, 0x70da459551430a16, 0x7d1c35450c374bc6, 0x7f5e070d51430bc6, 0x70da4544e12844e6, 0x6912f430e12f0706, 0x7e9c369151430bc6, 0x70da462148430706, 0x70da45450c2dc4e6, 0x6918f4bd0c2f04e6, 0x70da46110c284706, 0x7658f4bd0c2f0706, 0x8c1c3690bc110326, 0x6f9a44bd0c2f0706, 0x70da45450c2d8446, 0x815c369151430bc6, 0x70d9d430bc1c0326, 0x7f5c36912f430bc6, 0x1c3691514949d5, 0x70d975450c2f0706, 0x8bdc3691514309d6, 0x70da45450c2f03f6, 0x70da45450c3ecbc6, 0x7bdc35450c2f0446])
  | 5, 9 => (packedWords [0x70da45450c274326, 0x70da45250c2f04e6, 0x70da4545132f0706, 0x7c9c3691514309d6, 0x70da45450c2f04e6, 0x805c369151430446, 0x8a5c36912f430bc6, 0x691884bd0c384706, 0x811c369151430bc6, 0x8c1c3690a11c0326, 0x6d5a45450c2f0706, 0x7f5c369144430bc6, 0x7f5c369151420bc6, 0x6eda45450c2f0706, 0x70da4544e0284706, 0x7d1c369151430a16, 0x6912f4690c2f0706, 0x8c1b86910c2f0706, 0x7f5c363d51430bc6, 0x7adc35450c2f0706, 0x70da4544e62f0446, 0x70da45450c25c446, 0x7bdc35450c284706, 0x7f5c3691884bd0c6, 0x70da44bd0c284446, 0x7f5b869151430bc6, 0x7f5c3691705450c6, 0x70da44bd0c3c4bc6, 0x70da45f942430bc6, 0x70da45f10c2f0706, 0x899f270d51430bc6, 0x70da45450c2f07b6])
  | 5, 10 => (packedWords [0x7f5c364951430bc6, 0x899c3544dd2f0446, 0x70da4621514304e6, 0x70da45450c274706, 0x70da45450c274286, 0x70da45e12f430bc6, 0x70d985450c2f0706, 0x8b19a4bd0c2f0706, 0x70da45450c2144e6, 0x70da45450c2f0586, 0x70da4544e6284706, 0x70da45450c234706, 0x70da45450c3cc8f6, 0x7f5d670d51430bc6, 0x70da44bd0c2f07e6, 0x801fd70d51430bc6, 0x70da45450c2f04b6, 0x70da4641514309d6, 0x809c36915141c706, 0x70da45451a4304e6, 0x81dc369151430a16, 0x70da45892f430bc6, 0x7f5c369151430b36, 0x70da45450c2f0506, 0x70da45450c2f08e6, 0x70d8f5450c3c4bc6, 0x899c3544dd284706, 0x70da44d10c2f0706, 0x70da45952f430bc6, 0x7f5c369146430bc6, 0x70da44bd0c2f03e6, 0x6c1a45450c2f0706])
  | 5, 11 => (packedWords [0x741c3691514309d6, 0x70da4621784bd0c6, 0x70da45c551430706, 0x70da45450c2f06e6, 0x831a45450c2f0446, 0x7f5e170da4430bc6, 0x8b1c3669514304e6, 0x70da44bd0c2a8706, 0x8b1a44bd0c2f0706, 0x899c3691513c4bc6, 0x6f1a44b90c2f0706, 0x70da35450c2f0706, 0x70d995450c2f0706, 0x70d9e5450c2f0706, 0x70da45792f430bc6, 0x70da44bd0c2f0686, 0x70da45c1625450c6, 0x7f5c369148430bc6, 0x70da45450c2f0546, 0x70da4545092f0706, 0x70da45450c2f0626, 0x70da45450c2bc706, 0x6912f431072f0706, 0x6e1a44a10c2f0706, 0x831a45450c284706, 0x88dc36912f2f0706, 0x7d1c36912f430bc6, 0x70da44bd0c2d8706, 0x8b1c3691514303f6, 0x70da45450722c706, 0x8b1a46212f430706, 0x70da44d50c2f0706])
  | 5, 12 => (packedWords [0x7bdc369151430bc6, 0x70da44e50c2f0446, 0x6912f430da2f0706, 0x70da45450c2f07c6, 0x8ada4544e1284706, 0x805c36912f430706, 0x8b1c3691514304e6, 0x7f5a44bd0c384bc6, 0x8b1a46312f430706, 0x1f570da45450c5, 0x70d9c5250c2f0706, 0x70da44f10c2f0706, 0x70da45450c2f4706, 0x70d9d5450c2f06a6, 0x70da45450c2749d6, 0x7d1c363d51430bc6, 0x70d9c5450c2f0706, 0x70d9a5450c2f0706, 0x70da45450c41c4e6, 0x70da451d0c284706, 0x70da45dd51430bc6, 0x7c9c369151430bc6, 0x70da45450c2748d6, 0x70da45450c324bc6, 0x70da44e50c284706, 0x771a44bd0c2f0706, 0x70da45450c334bc6, 0x70da45b551430706, 0x70da4544e1284706, 0x6f9a45450c2f04e6, 0x70da45450c2dc706, 0x7f58f5450c384bc6])
  | 5, 13 => (packedWords [0x6918f4bd0c2f0706, 0x7f9c369151430bc6, 0x765c349d0c2f0706, 0x70da45450c2b0706, 0x70da45450c3a8bc6, 0x70da458d51430bc6, 0x70da45450c350706, 0x70da45450c2f05e6, 0x70da45450c2846a6, 0x70da45250c2f0706, 0x70da45650c2f0706, 0x70da45e50c2f0706, 0x691784bd0c384bc6, 0x7d5c369151430bc6, 0x749c3691514309d6, 0x70da45450c2f0706, 0x8a9c3691514309d6, 0x70da44bd0c2f0806, 0x771c3691514304e6, 0x70da45390c2f0706, 0x6918f6212f430706, 0x7f5c3691514309d6, 0x1c3691513d8705, 0x70da4544fd284706, 0x70da45450c284666, 0x70da45450c2d4706, 0x70da45450c2f0656, 0x70da45450c2f8706, 0x7f5c3691514308d6, 0x1a45450722c705, 0x2016912f430705, 0x70da45450d2f0706])
  | 5, 14 => (packedWords [0x70da45c151430596, 0x1c36915141c445, 0x70da45452a4309d6, 0x70da45450c2f05f6, 0x70da45450c2f06b6, 0x8a1c3691514309d6, 0x70da462151430706, 0x1ef70d51430a15, 0x70da05450c2f0706, 0x70da95450c2f0446, 0x70da45450c2f0476, 0x70da44bd0c2f05b6, 0x1c3691514309d5, 0x799c369151430bc6, 0x70da45450c3c49d6, 0x70da45450c2dc4d6, 0x765c34a10c2f0706, 0x1c369176430bc5, 0x8b1fd6912f430bc6, 0x1c3691514308d5, 0x70da46110c2f04e6, 0x70da45450c3c48d6, 0x70da45450c284696, 0x1be69151284705, 0x70da45450c2a84e6, 0x805a44bd0c2f0706, 0x70da45450c2f0936, 0x70d9f5450c2f0706, 0x70da4545072f0446, 0x70db76910c2f0706, 0x711a45450c2f0706, 0x6912f430d92f0706])
  | 5, 15 => (packedWords [0x70da46212f4305b6, 0x7bdc35450c2f0a16, 0x70da45450c2f04d6, 0x8b1f270da45450c6, 0x70da45450c3b4bc6, 0x70da44bd0c2f06a6, 0x70da45450c23c706, 0x70da45450c2f0466, 0x70da45450c2f0436, 0x7bdc35450c2f03f6, 0x70da45450c2d84e6, 0x70da45450c2f09d6, 0x70da454507284706, 0x70da45450c2f04f6, 0x6c5a45450c2f0706, 0x7bdc35450c2f04e6, 0x70da45450c2f08d6, 0x70da45450c3849d6, 0x70da45450c2f0526, 0x70da45450c224446, 0x8b1a45e12f430bc6, 0x805c3691514304e6, 0x7f5c367151430bc6, 0x7f5c366951430bc6, 0x8b1c3691514305e6, 0x70da4545071c04e6, 0x70da44bd0c2843f6, 0x7f5c369151384a16, 0x805fd70d8f5450c6, 0x6f9a45450c2dc706, 0x70da45450c3749d6, 0x1c3691073b0705])
  | 5, 16 => (packedWords [0x819c369151430a16, 0x7f5c369151430b76, 0x70da44bd0c2844e6, 0x835a44bd0c2f04e6, 0x70da461d2f430706, 0x7f5a463d2f430bc6, 0x70da45450c2f03a6, 0x70da45450c2f06c6, 0x1c369162544a15, 0x895c3691512f0446, 0x70da45450c2f05c6, 0x79dc369151430a16, 0x7f5c369151430d46, 0x7e5c366951430bc6, 0x70da4631514309d6, 0x70da45450c2f04a6, 0x7f58f5452f430bc6, 0x1c36912f41c705, 0x7f5c369149430bc6, 0x70d9d5450c2f0446, 0x6f9a45450c2f0706, 0x7f5c369151430bc6, 0x1b76910c2f0705, 0x6912f430e32f0706, 0x70da45450c2f0486, 0x70da44bd0c2f0696, 0x895c369151284706, 0x1c3674bc1c0325, 0x70da45450c3209d6, 0x70da45450c2f04c6, 0x70da25450c2f0706, 0x70da44bd0c330bc6])
  | 5, 17 => (packedWords [0x70da44bd0c230706, 0x70da45450c2742e6, 0x7edc369151430bc6, 0x70da450d0c2f0706, 0x8a5c369151430bc6, 0x70da44e10c2f0706, 0x70da45450c2f0646, 0x70d9d5450c284706, 0x831a45450c2f03f6, 0x1c36915141c675, 0x6918f5e12f430bc6, 0x7e5c369151430bc6, 0x831a45450c2f04e6, 0x809f470d51430bc6, 0x7f5c3691885450c6, 0x70da45450c284446, 0x1c35450c32c9d5, 0x70da44bd072f0706, 0x70da45090c2f0446, 0x70da45450c3c4bc6, 0x879c369151430706, 0x70da45450c2a0706, 0x70da45e151430bc6, 0x70da45450c290706, 0x70da45450c2c4446, 0x7c9c354528430bc6, 0x70da45450c284616, 0x70da45450c2f07e6, 0x6fda45450c2f0706, 0x8b1c3691514309d6, 0x70da458951430bc6, 0x70da45090c284706])
  | 5, 18 => (packedWords [0x819c36912f430bc6, 0x6f151430dd2f0706, 0x70da4545072f0676, 0x70da44e50c2f04e6, 0x70da459551430bc6, 0x70da44bd0c224706, 0x789be6910c2f0706, 0x70d9c5450c2d8706, 0x70da45450c2f0606, 0x6dda4430dd2f0706, 0x79dc36912f430bc6, 0x70da45450c2f03e6, 0x7f1c367151430bc6, 0x70da4621785450c6, 0x70da46110c2f0706, 0x6f1a45450c2f0446, 0x70da4629514309d6, 0x7ddc369151430bc6, 0x805c366951430706, 0x7e1c367551430bc6, 0x70da45b951430706, 0x70da45450c2a8706, 0x70da460551430706, 0x6919a4bd0c2f0706, 0x1c36914841c705, 0x8b1a45452f4304e6, 0x70da457951430bc6, 0x70da45450c2f0686, 0x70da45450c3544e6, 0x70da45450c3b09d6, 0x70da45450c2ec706, 0x805a463d2f430706])
  | 5, 19 => (packedWords [0x669514bd0c2f0706, 0x6f1a45450c284706, 0x70da45250c2d8706, 0x70d9d4bd0c2f0706, 0x88dc3691512f0706, 0x7d1c369151430bc6, 0x70da45450c2d8706, 0x1a44bd072f0705, 0x70da457151430bc6, 0x691514bce1284706, 0x70da45452f4309d6, 0x779c3691514309d6, 0x70da45450c244706, 0x7f1c369151430bc6, 0x8ada44bd0c284706, 0x7bdc35450c2f0706, 0x70da44bd0c2f0446, 0x70da45f951430bc6, 0x70da45d92f430bc6, 0x70d44430dd2f0706, 0x6f1a45450c2c4706, 0x1c3691514308f5, 0x805c369151430706, 0x70da45450c2e8706, 0x70da4669514304e6, 0x6918f544e1284706, 0x70da463d514309d6, 0x70da44b90c2f0706, 0x70da4521072f0706, 0x70da45450c2f0406, 0x70da460d0c2f0706, 0x825a45450c2f0706])
  | 5, 20 => (packedWords [0x70da45450c3f0bc6, 0x70da4544e52f0446, 0x70da45110c2f0446, 0x70da44bd0c2f0616, 0x70da45450c25c706, 0x70da45450c2f0576, 0x7f5be69151430bc6, 0x70da44bd0c284706, 0x835a44bd0c2f0706, 0x70da45450c2f0746, 0x70da45450c274116, 0x81dc369151430bc6, 0x1c36915141c4e5, 0x7cdc369151430bc6, 0x70da4544f12f0326, 0x70da46212f430446, 0x70da45450c314706, 0x70da45f10c2843f6, 0x70da44f50c2f0706, 0x70da45450c1382c6, 0x6e1a45450c2f0446, 0x70da45c151430446, 0x63d2f430bc1c0286, 0x829a45450c2f0706, 0x70da45450b2f0706, 0x70da45450c284a06, 0x70da44bd0c2c4706, 0x70da45550c2f0446, 0x70da4544e5284706, 0x76da45450c284706, 0x70da45110c284706, 0x70da45450c2c0706])
  | 5, 21 => (packedWords [0x70da44bd0c138286, 0x70da45450c2f08f6, 0x8b2026912f430706, 0x6b9a44bd0c2f0706, 0x70da45450c2f0596, 0x22b69151384705, 0x70da45450c284926, 0x70da45450c284676, 0x70d955450c2f0446, 0x7f5c364551430bc6, 0x6e1a45450c284706, 0x761c36910c2f0706, 0x70da45110c2c4706, 0x70da45450c2f0806, 0x70da45450c274186, 0x70da45450f2f0706, 0x70da45450c2f0736, 0x70da45450c2f0516, 0x70da45450c274226, 0x845c3691514309d6, 0x70da4545072f04e6, 0x785c36750c2f0706, 0x6f1a44bd0c2f0706, 0x70da45450c3748f6, 0x70d8f5450c138286, 0x8b1c369184430706, 0x70da45490c2f0706, 0x7d1e270d51430bc6, 0x831a45450c2f0706, 0x70da44bd0c348706, 0x7f5bf69151430bc6, 0x70da45610c2f0706])
  | 5, 22 => (packedWords [0x70da45450c2f0776, 0x785c36910c2f0446, 0x70da45450c2f0636, 0x83db869151430bc6, 0x70da45450c28c706, 0x6f1a45110c2f0706, 0x70da4544e72f0446, 0x70da45290c2f0706, 0x70da44d90c2f0706, 0x70da44ed0c2f04e6, 0x70da45210c2f0446, 0x795c369151430bc6, 0x70da15450c2f0706, 0x70da45450c2f05b6, 0x7f5c369184430bc6, 0x70da4545062f0706, 0x70da45450c2244e6, 0x70da4601514309d6, 0x8b1a44bd0c22c706, 0x785c36910c284706, 0x70da451d0c2f0706, 0x7f5c369151430aa6, 0x70da45310c2f0706, 0x70da45451e4309d6, 0x70da45450c3e4706, 0x6f5a45450c2f0706, 0x70da44e50c2f0706, 0x70da45450c2dc6a6, 0x70da4544e7284706, 0x70da45450c2e0706, 0x70da44dd0c2f04e6, 0x70da45210c284706])
  | 5, 23 => (packedWords [0x70da45450c2741f6, 0x70da45450c294706, 0x735a44bd0c2f0706, 0x70da45450c2740d6, 0x6912f430e12f0446, 0x75dc34bd0c2f0706, 0x70da44bd0c2f0a06, 0x855c369151430bc6, 0x70da45450c2f0496, 0x70da4621514305b6, 0x7f5c369151430b66, 0x70da45450c3cca16, 0x70da45450c3c8bc6, 0x70da45450c2f06a6, 0x70da45450c2d0706, 0x70da44bd0c2f0676, 0x70da45450c2d84c6, 0x70d9d5450c2f04e6, 0x6e1a44bd0c2f0706, 0x6f9a4430bc1c0326, 0x70da44bd0c30c706, 0x70da45c12f430706, 0x8b1a44bd072f0706, 0x805fd70da45450c6, 0x6912f430e1284706, 0x70d9b4bd0c2f0706, 0x70da44bd0c358706, 0x1c36695141c705, 0x70d8f5450c2f0a06, 0x70da45450c2f0386, 0x70da45450c2f0666, 0x829a45450c2f03a6])
  | 5, 24 => (packedWords [0x7f5c36912f430a16, 0x691934bd0c2f0706, 0x709a45450c2f0706, 0x70d9c5450c2f0696, 0x70da45e90c2f0706, 0x70da45450c2843f6, 0x70da458551430bc6, 0x70da45450c274136, 0x70da45350c2f0706, 0x791c369151430bc6, 0x70da45450c1382b6, 0x8c5c3691514309d6, 0x7f58f4bd0c2f0706, 0x785b76910c2f0706, 0x70da45450c2844e6, 0x1ef70d51430bc5, 0x70da461d51430706, 0x70da45450c0fc266, 0x7f5e270d28430bc6, 0x70da45f10c2f0446, 0x8b1c36915141c4e6, 0x70da45090c2f04e6, 0x70daf691514309d6, 0x1c369151498705, 0x70da45450c138266, 0x70da45450c274446, 0x70da4545032f0706, 0x7a1c369151430bc6, 0x1a4524e12f0705, 0x7f5c363d51430a16, 0x1c36915141c705, 0x70da45450c2c44e6])
  | 5, 25 => (packedWords [0x70d9a545072f0706, 0x70da459151430bc6, 0x70da45410c2f0706, 0x899c3691514309d6, 0x1c369151430975, 0x70da45ad51430bc6, 0x70da45250c2f0696, 0x7fdc369151430706, 0x70da45f10c284706, 0x70da95450c2f0706, 0x70da45450c2f0696, 0x70da45450c330bc6, 0x70da45450c230706, 0x70da45e12f430a16, 0x70da45450c284586, 0x80dc3691514309d6, 0x70da457d51430bc6, 0x805c369151430606, 0x70da45bd51430706, 0x801fd70d51430a16, 0x1c369151394a15, 0x70da44bd0c3ccbc6, 0x885b869151430706, 0x809c3691514309d6, 0x859a45450c2f0706, 0x6f1a45450c2f04e6, 0x6e5a45450c2f0706, 0x7d1d470d51430bc6, 0x1c367551284705, 0x8b1a44bd0c2f0446, 0x70da45450c2f09f6, 0x7f5c36914a430bc6])
  | 5, 26 => (packedWords [0x70da4545072f0706, 0x70da45210c2f0676, 0x70da45450c2c44b6, 0x70da45450c3c0bc6, 0x70da45450c2f0976, 0x70da4545254309d6, 0x7d9c369151430bc6, 0x7f5c369151418bc6, 0x70da4545184309d6])
  | 6, 0 => (packedWords [0x691535450c2f0707, 0x4bd0c2f0700a1dc3, 0x5450c2f070770da4, 0x2f070079dc3691a4, 0x2f070770da45450c, 0x2f19c3691515250c, 0x60020670da45450c, 0x70da44bd0c2f04e, 0x369151430bc04dc0, 0x45450c2f07077f5c, 0x1430bc1c1e0d70da, 0xc280707821c36915, 0xc139dc369151430b, 0x774dc369151430b, 0xc3691515450c2f07, 0xc369151430bc111d, 0x51430bc280287749, 0xc2f0700b5dc3691, 0xc22470670da4545, 0xc2f1c0070da4545, 0xbc68c5fd70da4545, 0xc0079dc369151430, 0xd8f5450c2f0700a1, 0xdaf69151430bc770, 0x12f430bc1c1dfd70, 0xbc1c0677741c369, 0xbc111dc36915143, 0x1977f5c36915143, 0x1dc369151430bc1c, 0xda45451c430bc1c, 0x9c3691514307077, 0x9151430bc1c1e2c8, 0x910c2f07078b5c36, 0x30a11c1dc3691514, 0xf0707749c3691514, 0xc1dc36b9a45450c2, 0x70da463551430bc1])
  | 6, 1 => (packedWords [0x7f5c369151430bc7, 0x69151430e52f1a26, 0x5450c284707001c3, 0x430bc1c19fd70da4, 0x2f0706001f470d51, 0x1c1c0070d9d5450c, 0x770da45450c2f089, 0x369151430d72f070, 0x45450c2f08b1c19c, 0x369151430bc7001a, 0x1430bc1c1e037f5c, 0xc2f04e770dbc6915, 0xc1c1dc3691514a10, 0x670da456d51430b, 0x8ada45450c2847, 0xfd70da45450c2f1c, 0xa45450c2f0446809, 0xc3b8bc1c1c0070d, 0x5128470670da4545, 0xbc1c1c008c1c3691, 0x70770da454523430, 0xde270da45450c2f0, 0x5c3691514950c2f1, 0xda45450c2f06167f, 0x1514610c2f1c0070, 0x50c2f07077f5c369, 0xa11c1a1970da454, 0xc706001c36915143, 0x1c008b1c36915141, 0xb1c3691514308b1c, 0xda45090c2f07068, 0x917d430bc1398007, 0xbd0c2f0707001c36, 0x8470075dc370da44, 0xf070670da45450c2, 0x39800741a44bd0c2, 0x1c369151494bc1])
  | 6, 2 => (packedWords [0x70da45450c2c4706, 0x69151430bc139c00, 0x4650c2f07078bdc3, 0x3ccbc1c1dc369151, 0x13828670da45450c, 0x8dc0070da45450c, 0x770da45450c2f070, 0xd70da45450c2f070, 0x45450c2f04e0c9dc, 0x45450c2f04e770da, 0xc384bc111df270da, 0xc13809770da45450, 0xc1c19c369151430b, 0x7001da70d51430b, 0x3070da45450c2dc7, 0xa45450c2f044021e, 0xa45450c2f08b770d, 0x2f430bc1c1dfd70d, 0xcb2f0707749c3691, 0x700addc369151430, 0x4770da45450c2f0, 0xdc369151430bc1c0, 0xda44bd0c2f070031, 0x151430bc28470770, 0x50c2f0700d9dc369, 0x50c2f070770da454, 0x4bc111dc36e1a454, 0x70770da45450c37, 0x1e2c70da4545072f, 0x75c369151430bc1c, 0xda45450c2f04477, 0x9151430bc1c19f47, 0xbd0c2f0707001bc6, 0x84a11c1dfd70da44, 0xf070770da45450c3, 0xc19c36b1a45450c2, 0x1c35452c430bc1])
  | 6, 3 => (packedWords [0x69151430bc1c0267, 0x691a45450c2f1dc3, 0x430bc1c03f77f5c3, 0x430bc1c1dc369151, 0x2f0707845c369139, 0x2f1dc36ada45450c, 0x770da4589514950c, 0x369151430bc1c029, 0x45450c2f0b11c1dc, 0xc5450c2f044770da, 0x1430bc1c1dc36918, 0xc1c04e78c1c36915, 0xe0a1dc369151430b, 0x770da45450c2f04, 0xc3691935450c2f07, 0xa45450c374a11c1d, 0xa4430ec2f070670d, 0x51430bc1c1c0070d, 0xc2f070770da45d1, 0xbc1c1dc36915149d, 0x70770da45450c390, 0xe3270da45450c2f0, 0xda465151430bc1c1, 0xd8f5450c2f070770, 0x50c300bc1c1dfd70, 0x50c2f070770da454, 0xbc1c1dc870da454, 0x44770da45450c43, 0x19c369151430c82f, 0x22c691514308b1c, 0x9151430bc2507070, 0x3151430a11c1dc36, 0x610c2a870770da46, 0xf07f1c1dc3691514, 0xf070770da45450c2, 0xc19c3691915450c2, 0x1c36912f430bc1])
  | 6, 4 => (packedWords [0x7f5c369151430bc7, 0x70da45450c111a2d, 0x5450c2f07070022c, 0x430bc139dd370da4, 0x1c00b7741c369151, 0x1c19c369151430bc, 0x700151430cb2f08b, 0x3691784bd0c2f070, 0x269151430bc22d9c, 0x1430bc1c0587001d, 0xc2f070059dc36915, 0x828470770da45450, 0xc1119c369151430c, 0x6001c35450c32cb, 0x70da45450c2f0a, 0xc369144430bc1c18, 0x51430bc1f4707001, 0x51430bc1c1dc3691, 0xc2f08b671dc3691, 0xc1c18007f5a4545, 0x707001c670da4545, 0xdc369184430bc22c, 0xda45450c2f070069, 0xda45450c2f067670, 0x1884bd0c1c180070, 0x50c31c706001c369, 0xbc1c180070da454, 0x706001b86915143, 0x1c0070da45c15143, 0xda45450c3dcbc1c, 0xa1a45450c2f07077, 0x450c2f0700dddc36, 0x30cb28470670da45, 0x30bc1c1c0070d514, 0x30a167a5c3691514, 0xc1c00749c3691514, 0x8c1e270da4430bc1])
  | 6, 5 => (packedWords [0x70da45450c2f0447, 0x4bd0c384bc1c1e2c, 0x69151430bc770da4, 0x430bc1c1dfd789c3, 0x430a1670da454528, 0x1c1c007f5c369151, 0x78bdc367151430bc, 0x3691845450c2f070, 0x369151430bc1c1dc, 0x463d51430bc7751c, 0x1430bc1c1de770da, 0xc284707719c36915, 0xc1c1e2c70da45450, 0x770da44bd0c374b, 0xc369151430fe2f07, 0xa45450c2f07009dd, 0x51430cb2f03a770d, 0x2f430bc1c1dc3691, 0xc72f070770da4621, 0xbc1c1dc369151430, 0x44770da45c151430, 0x9c369151430ec2f0, 0x1e170da4430bc1c1, 0x18c4bd0c2f070700, 0x512430bc1c1dc369, 0x50c2f044770da454, 0xbc1c1e1070da454, 0x15770da462d5143, 0x9dc369151430bc1c, 0xb1c3691514307013, 0xda45f50c2f07068, 0x91805450c2f1c007, 0x250c2f0707845c36, 0x9cbc1c1a2f70da45, 0x2cbc7001c3691513, 0xc19fd70da45450c3, 0x1c369151494bc1])
  | 6, 6 => (packedWords [0x8b1c36910c3b0706, 0x69151430bc1c1c00, 0x430dd2f07078bdc3, 0x430bc285dc363d51, 0x2f07067f5c369151, 0x111c0070da45210c, 0x770da45452f430bc, 0xe70da45450c2f044, 0x45450c2f0700c9dd, 0xf430c82f070770da, 0xc2f08b1c19c36912, 0xc2f04e7001a46110, 0xc1c1dd270da45450, 0x77c9c369151430b, 0xc369151430ec2847, 0xa45450c3bcbc1c1d, 0x51430bc1c024770d, 0xc2f070025dc3691, 0xd92f070670da4545, 0xbc1c180070da4430, 0xbc6001c3430ec32c, 0x80070da45450c3cc, 0x1d270da4430ec2f1, 0x18f5450c2f044700, 0xda44bd0c1c19c369, 0x50c2f07070022c70, 0xbc1c1e306f9a454, 0xbc770da45452943, 0x9e307f5c36915143, 0xf5c369151430bc13, 0x9151430bc2047077, 0x452f430a11c1dc36, 0x450c28470770da45, 0x30bc1c1dde70da45, 0xf0707789c3691284, 0xf1a1470da45450c2, 0x1fd70da4430ec2])
  | 6, 7 => (packedWords [0x6915146d0c2f0707, 0x5452b430bc1c1dc3, 0x430e12f070670da4, 0x2f044045c006912f, 0x2f070670da45450c, 0x2f180070d2f430cb, 0x7001d270da44bd0c, 0xe70da45090c2f070, 0x45450c2f070085dd, 0x1430bc1c05e770da, 0x4430bc139dc36915, 0xc28470770da45451, 0xc1c19c36918f5450, 0x7001c36917f430b, 0xc369151430ab2847, 0xa45450c2f0701c1d, 0x51430bc1c028770d, 0xa44bd0c2f19c3691, 0x51430676001fd70d, 0xbc0fd8008b1c3691, 0x117001c369151430, 0xdc369151430a11c0, 0x5c3691514309d1c1, 0x1905450c2f07077f, 0x10c374bc1c1dc369, 0x50c2f0707785c369, 0xbc1c1dc36917b54, 0x4e68b1c36912f43, 0x5c0070da45450c2f, 0xda45450c2f07019, 0x9151430bc1c02a77, 0x9151430a11c1dc36, 0x450c2f0707801c36, 0x450c2f19c36d1a45, 0xf0707001fd70d8f5, 0x89dd070da45450c2, 0x70da45450c2f0440])
  | 6, 8 => (packedWords [0x70da45450c2f0447, 0x70da45450c1c1a11, 0x5450c2f07070022b, 0x3ccdd2f1e0b70da4, 0x2f070770da45450c, 0x1c1dc369151430c1, 0x670da454511430bc, 0x74dc369151430bc, 0x369151430bc19dc0, 0x45450c2f07078b1c, 0x1430bc1c1e2270da, 0xc274706849c36915, 0xc2f180070da45450, 0x7001c3691784bd0, 0x1f70da45450c2f07, 0x670daf69151431a, 0x2f430ec2f0707002, 0x51430bc1619c3691, 0x28430bc7001c3691, 0x70089dfd70da4545, 0x4e670da45450c284, 0xc0070da463151430, 0xda45450c2f0bc139, 0xda45450c28470770, 0x151430e01c1a1170, 0xbc1c0177001c369, 0xbc1c1dc36915143, 0x4e7715c36915143, 0x19c369151430e12f, 0x22c70da4545251c, 0x91805450c2f04470, 0x450c2f070015dc36, 0xbd0c2f070770da45, 0x30bc1c1dc36912f4, 0x30706779c36912f4, 0xc1c008b1c3691484, 0x70da454539430bc1])
  | 6, 9 => (packedWords [0x691514790c2f0447, 0x69151430c81399c3, 0x430c42f0707001c3, 0x430bc1c1dc369151, 0x1c03d78adc369151, 0x1c19c369151430bc, 0x7001c35452532cbc, 0x36918f4bd0c2f070, 0x270da4545252f19c, 0x45450c2f0707001d, 0xc2f04407de1370da, 0xd2f04e770da45450, 0x4035dc369151430d, 0x770da45450c2f04, 0xc369151430bc2747, 0x2c6912f430bc1c19, 0x805450c284707002, 0xa45450c2f1dc3691, 0xc2f0707819c36bd, 0xbc111dc36915147d, 0xbc670da45fd51430, 0xc007f5c369151494, 0xda45451e430a11c1, 0xda4430bc1c032770, 0xd0c2f070045e3070, 0x50c2f04e770da44b, 0x50c2f1dc36918c54, 0xc7068bdfd70da454, 0x1c006bda45450c22, 0xda45450c380bc1c, 0x51c369151430bc67, 0x9151430bc1c1c007, 0x450c2f032770dc36, 0x450c1119fd70da45, 0xf0707001c36bda45, 0x7ddc3691565450c2, 0x70da45450c284700])
  | 6, 10 => (packedWords [0x69151430a11c00d7, 0x69148430bc1c1dc3, 0x5450c2f07078b1c3, 0x430bc1c1e3a70da4, 0x2f04e770da454515, 0x1c1dc369151430c8, 0x78ddc369151430bc, 0x670da45450c2f070, 0x4595514a10c2f1e3, 0x1430bc1c03a770da, 0x1430bc1c1dc36915, 0xc2f07078edc36915, 0xc1399c3691514410, 0x460022c70da45450, 0x70da4544e12f04, 0xc369151430bc1c1c, 0xa45450c2f0707749, 0xc2f070031e2a70d, 0xe62f070770da4545, 0xbc1c1dc369151430, 0x13770da45450c338, 0x9c369151430bc110, 0x1c367151430bc1c1, 0xd9a5450c2f070600, 0x151430bc1c1c0070, 0xcb2f04e68cdc369, 0x70089c0070d5143, 0x70770da44bd0c2f, 0x19fd70da45450c2f, 0x1f270da45450c2f, 0xda44bd0c2f07070, 0x9151430bc0a1e117, 0x450c2f07077f5c36, 0x74bc1c1e3970da45, 0xf0447899c35450c3, 0x11dc36bda45450c2, 0x70da45450c2f0441])
  | 6, 11 => (packedWords [0x70da4544e1284706, 0x54532430bc1c1c00, 0x5450c2f070670da4, 0x5450c2f1c008ada4, 0x2dc7067f5c369190, 0x1c1c0070da45450c, 0x78d1c369151430bc, 0x3691514a90c2f070, 0x369162545252f19c, 0x45450c2f0707001c, 0x4430bc1c1e1d70da, 0xc2f070670da45451, 0x4dc006918f4bd0, 0x770da45450c2847, 0xc369151430df2f07, 0xad69151430bc1c1d, 0xa45450c2f044770d, 0x51430bc1c1e2670d, 0xc2f04e772dc3691, 0xa11c1a2c70da4545, 0x707001c369151374, 0x9c36bda45450c284, 0x1c369151430bc179, 0xda4544e42f070600, 0xda45450c2f1c0070, 0xa11c04477f5d070, 0xbc1c19c36915143, 0x327001c36914943, 0x1dc369128430bc1c, 0xda46012f430bc1c, 0xda45450c2f07067, 0x450c3c4bc1c1c007, 0x30d02f070770da45, 0xe0bc1c1dc3691514, 0xf070770da45450c3, 0xc1dc36912f4790c2, 0x899c369151430a11])
  | 6, 12 => (packedWords [0x70da45450c2f0447, 0x5450c2f070001e02, 0x5450c2f070770da4, 0x5450c2759c369178, 0x1c01d7001fd70da4, 0x1c1dc369151430bc, 0x770da4544e12f0a1, 0x36912f430bc1c01f, 0x369151430bc1959c, 0x1430d82f0707001c, 0x1430bc0a99c36915, 0xc2f0707001c36915, 0x71c1dc369151430d, 0x770da45450c2f0b, 0xc3691514308b2247, 0xa44bd0c2f070035d, 0xaf6910c3b070670d, 0xc2f070009c0070d, 0xc2f070770da4545, 0xb11c1dc369162545, 0x707899c369151430, 0xdc369151430ff2f0, 0xda45450c3b0bc139, 0xda45450c2f061770, 0x525430bc111e0270, 0x50c2d870770da454, 0xbc111e2f70da454, 0x70770da45451843, 0x1dc3691655450c2f, 0x9c369151430a11c, 0xda44bd0c2f07078, 0x91885450c1c19d97, 0xbd0c2f0707001c36, 0x30bc1c1e2e70da44, 0x3070670da4545334, 0xc1c0070daf6912f4, 0x70da45450c388bc1])
  | 6, 13 => (packedWords [0x69151430bc2f0707, 0x5450c2f070095dc3, 0x544f72f070670da4, 0x430bc139c0070da4, 0x2f04e770da45452f, 0x2755de70da45450c, 0x60000070da45450c, 0x70da45451a43070, 0x45450c33cbc1c1c0, 0x1430e12f070770da, 0x5430a11c1dc36915, 0xc2f09d770da45452, 0xc1a9dfd70da45450, 0x78c1c369151430b, 0xc3691514610c2847, 0xbc69151430bc1c1d, 0x8f5450c2f04e7899, 0xc2f070081dc3691, 0xc2f070770da4545, 0x70021dec70da4545, 0x7770da45450c2f0, 0xdc369151430bc110, 0xdc369151430bc1c1, 0x9a45450c2f070777, 0xd0c2f07004ddc36f, 0xbc22c44770da44b, 0xbc1c1dc36915143, 0x70770da46395143, 0x1dc369151430dd2f, 0xd1c369151430bc1c, 0x9151430bc1381177, 0x7551430bc1c1dc36, 0x450c2f070770da46, 0x450c1c19c3691885, 0xf05e70022c70d9a5, 0xc1dc36918c5450c2, 0x70da45450c2f0851])
  | 6, 14 => (packedWords [0x6bda44bd0c2f0707, 0x69151430bc1c1dc3, 0x430bc1c044770daa, 0x430bc1c1dc36912f, 0x2f070770da463151, 0x275a2470da45450c, 0x7001c369151430bc, 0x3691514690c2f070, 0x45450c3f4bc1c1dc, 0x1430a122c70770da, 0x45450c2f1dc36915, 0xc2f07077f5d270da, 0x91c1a2670da44bd0, 0xc7001a45450c22c8, 0x2a7f5c369151430b, 0xa45450c2f0700d5e, 0xa45450c28470770d, 0xc320bc1c1dc36c9, 0x51430bc770da4545, 0x700b9dfd7f5c3691, 0x70770da45450c2f0, 0xdc3691545450c2f0, 0xda45450c2f0831c1, 0xda45110c2f070770, 0xda45450c1c1a2670, 0x50c2f07070022c70, 0xbc1c1e2c70d9a54, 0x8227809c36912f43, 0x1dc369151430bc13, 0xda45450c2f0821c, 0xda45450c2f04e77, 0x91514a90c2f1e117, 0x890c2f07077f5c36, 0x30bc0e99c3691514, 0x1c706001c3691514, 0xc180070da45450c4, 0x1c35450c32cbc1])
  | 6, 15 => (packedWords [0x749c369151430bc6, 0x54542430bc1c1c00, 0x5450c2f070770da4, 0x545251c19d170da4, 0x2f04e7001c36bda4, 0x1119c36917d5450c, 0x7001f470d51430bc, 0xa70da45450c2f070, 0x44bd25430bc1c1dd, 0x1430bc1c031770da, 0x8430bc1c1dc36915, 0xc2f070670da44bd1, 0xc2f18006f9a45450, 0x46001fd70da45450, 0x69151430bc22c4, 0xc369151430f12f1c, 0x2f430bc1c03077f5, 0x51430bc139dc3691, 0xc2f070770da4601, 0xbc139e2c70da4545, 0x70770da45451e430, 0xdc3691514b10c2f0, 0xda459951430bc1c1, 0x151430a122c70670, 0x50c41cbc1c1c0069, 0x50c2f044770da454, 0x4e07dde270da454, 0x70770da45450c2f, 0x1dc369151430db2f, 0xda45c1514950c1c, 0x9151430bc1380d77, 0x450c2f0700cddc36, 0x450c28444670da45, 0xf08b1c1c0070da45, 0xf070770da44bd0c2, 0xf19e070da45450c2, 0x1c369151430f12])
  | 6, 16 => (packedWords [0x69151430fa2f0707, 0x5450c368bc1c1dc3, 0x5e151430bc670da4, 0x3b0bc1c1c0070da4, 0x4304e670da45450c, 0x1c1c0070daf69151, 0x770da45450c2f0a6, 0xd70da45450c384bc, 0x369151430a11c1df, 0x45450c2f0707789c, 0xc5450c1c1e1070da, 0xc1c00178b1c36918, 0xc161dc369151430b, 0x770da45451e430b, 0xc369151430bc2107, 0xa45453a430bc1c1d, 0x2f430bc1c01e770d, 0x625450c2f19c3691, 0xd32f0707001c3691, 0xbc1c1dc369151430, 0x707871c369151430, 0xdc3691514bd0c2f0, 0x9c369151430bc1c1, 0xda459551430bc677, 0x151430dd2f1c0070, 0xcb2f04477f5c369, 0xbc1c1dc36915143, 0x707771c36915143, 0x1dc36915145d0c2f, 0xda45450c378bc1c, 0x9151430bc2844477, 0x450c2f0701a9dc36, 0x30bc13813770da45, 0x30bc1c19c3691514, 0xf0707001c3691844, 0xc1e3070d9d5450c2, 0x70da463d51430bc1])
  | 6, 17 => (packedWords [0x69151430bc2ac707, 0x6918c5450c2f1dc3, 0x5110c2f07077f5c3, 0x2f0440fddc369151, 0x2a870670da45450c, 0x1c1c0070da45450c, 0x6895c369151430bc, 0x8bda4544e12f070, 0x45450c3acbc1c1c0, 0x45450c2f04e770da, 0x1430bc111dc36bda, 0xb2847078c1c36915, 0xe111dc369151430c, 0x670da45450c2f04, 0x6910c3b0bc22c7, 0xa464951430bc1c1c, 0x51430bc1c011770d, 0xc284a11c1dc3691, 0x2f43070770da4545, 0xcb1c19c369188545, 0xc60022c70d51430, 0x8008b1d270da4545, 0x1c36910c3b0bc111, 0xda45450c2f069700, 0x151430c82f1e2f70, 0x51e2847067f5c369, 0x700c980070da454, 0x1b70023070da42f, 0x9dc369151430bc1c, 0xda45450c2f04e03, 0xda45450c2f04e77, 0x9151430bc1c1e267, 0x30a11c0267759c36, 0x2cbc0e99c3691514, 0xf02e7001c35450c3, 0xc1dfd70da45450c2, 0x801c369151430bc1])
  | 6, 18 => (packedWords [0x7d1c369151430bc6, 0x5450c284700fdc00, 0x5450c2d870670da4, 0x430bc111c0070da4, 0x2f070770da45450c, 0x1c1a1b70da45450c, 0x7001a44bd0c2f08b, 0xa70da45450c2f070, 0xc7f5c3691514319e, 0x35450c32cbc60022, 0x1430a11c1c00749c, 0x11c04e78c1c36915, 0xc1119c369151430a, 0x6001c36912f430b, 0x805c3691514307, 0xc36910c3b0a11c18, 0xa4430ef2f0706001, 0x51430bc1c1c0070d, 0xc32cbc68e1c3691, 0xaa1c1c007f5c3545, 0x4e770da45450c2f0, 0xe0270da45450c2f0, 0xda45450c2f070051, 0x1514310c28470770, 0x12f430bc1c1dc369, 0x50c2f0707789c369, 0x70089de370da454, 0x70770da45450c2f, 0x1a1170da45450c2f, 0x1c36912f430a11c, 0x91514590c2f07070, 0x9151430bc0b99c36, 0x30bc1380f7001c36, 0xf0701a5dc3691514, 0xf070770da45450c2, 0xc1dc369151430c62, 0x785c369151430bc1])
  | 6, 19 => (packedWords [0x691514950c2f04e7, 0x5450c2f0b61c1dc3, 0x4610c2f04e770da4, 0x374bc1c19c369151, 0x2f07070022670d51, 0x2f1dc3691514850c, 0x78b1fd70da45450c, 0x36917d5450c2f070, 0x14a10c374bc1c1dc, 0x45450c2f070770d5, 0x8430bc1c1dcc70da, 0xc2f070770da45454, 0xc1c1e1a70da45450, 0x7805c369151430b, 0xc3691575450c2f07, 0xc369151430bc1c1d, 0x514a10c2f04478d5, 0x51430bc1c1dc3691, 0xd92f0707789b8691, 0xbc1c1dc369151430, 0x70770da460151430, 0xdc36912f430cb2f0, 0x1c369151430bc111, 0x1514790c2f070775, 0x50c2f08a1c1dc369, 0xbc28470770da454, 0x8b139dc36912f43, 0xbc770da45450c2f, 0xddfd70da45450c3b, 0xda45450c2f07007, 0x452f430e12f07077, 0x4528430a11c1da45, 0x30bc1c00d770da45, 0x30bc1c1dc3691514, 0xf070770da45c9514, 0xc1e3070da44bd0c2, 0x819c369151430bc1])
  | 6, 20 => (packedWords [0x6917f5450c2f0707, 0x4bd0c2f070139dc3, 0x430bc1c012770da4, 0x384bc1c1dc369151, 0x22c7066918f5450c, 0x1c1c0069151494bc, 0x7765c369151430bc, 0xd70da45452f430bc, 0xe70da45450c2f1df, 0x45450c2f07077f5d, 0x7430bc1c1e2e70da, 0xc2f070770da44bd2, 0xc1119e770da45450, 0x6001c369151494b, 0x70daf691514307, 0xc369151430bc111c, 0xa4545182f04468bd, 0x51430bc1c1c0070d, 0xbc11032773dc3691, 0xbc139dc369151430, 0xbc7835c369151430, 0xdfd70da463d51430, 0xda462d51430a11c1, 0xda44e50c2f070670, 0x520430bc1c1c0070, 0x52528470670da454, 0xbc045c0070da454, 0x47077f5c36915143, 0x1e2f70da45450c28, 0xda45450c394bc1c, 0xda4545182847067, 0x450c2f07004dc007, 0x30a11c032770da45, 0x30bc1c1dc3691514, 0xf07078c5c3691514, 0x119c369151430e32, 0x1c36917f430bc1])
  | 6, 21 => (packedWords [0x691785452f430bc7, 0x69151430bc1c1dc3, 0x5450c2f06a670daf, 0x328bc1c1c0070da4, 0x1c00a770da45450c, 0x111dc369151430bc, 0x770da45450c2f070, 0x369151430bc11028, 0x45450c2f08b1399c, 0x45450c2f0707001a, 0xc2f070039dc970da, 0xc2f070770da45450, 0x85e2670da45450, 0x670da45450c2847, 0x70da4544fd2f07, 0xa45450c2f070185c, 0x2f4a10c2f070770d, 0x51430bc089dc3691, 0xa11c02877f5c3691, 0xc2f1dc369151430, 0x707845fd70da4545, 0x9c369151430d12f0, 0x1d670da45450c2f1, 0xda45450c2f065700, 0x151430a10fda2670, 0x50c2f0447001c369, 0xbc1c1dd070da454, 0x4e780dc36915143, 0x1de270da45450c2f, 0x9c369151430bc1c, 0xda45450c2844e68, 0x452f430bc1c1c007, 0x450c2f07078b1a45, 0x4bc111dc369da45, 0xf070770da45450c3, 0xa1dc369151430d52, 0x70da45450c1c04e0])
  | 6, 22 => (packedWords [0x70da4494ec2f0706, 0x5450c2f07003dc00, 0x5450c2f070770da4, 0x430a11c1e1770da4, 0x1c02f7741c369151, 0x1c15c369151430bc, 0x70000070da454507, 0x369151430e72f070, 0x454525430bc1c1dc, 0x45450c1c003670da, 0x8430bc1c1c0070da, 0x1430bc770da45451, 0x41dfd70da46015, 0x670da45450c2f07, 0x70db2691514307, 0xc36912f494bc1c18, 0x51430bc1c0307001, 0x514790c2f1dc3691, 0xc2f07077f5c3691, 0xbc1a5a2f70da44bd, 0x57001c369151430, 0xdc369151430bc110, 0xda45450c2f0a10fd, 0x151430bc1c034770, 0xd0c2f0700c9dc369, 0x50c2f070770da44b, 0xbc1c1dc36919c54, 0x70770da46695143, 0xddc36912f430ef2f, 0xf5c369151430bc07, 0x9151430cb2f04e77, 0x9151430bc1c1dc36, 0x450c2f00d7739c36, 0xf0a1139dfd70da45, 0x2c70670da45450c2, 0x3180070daf5450c3, 0x1d270daf691514])
  | 6, 23 => (packedWords [0x70da45450c2f0707, 0x6918f5450c1c1dd5, 0x430bc1c0077805c3, 0x2f04e0fddc369151, 0x1c006770da45450c, 0x1c19c369151430bc, 0x7001c36915141cbc, 0x369151430bc22c70, 0xd70daf691514319c, 0x45450c2f04e7001f, 0x545251c1a3070da, 0xc1c02c7001c36917, 0xddc369151430b, 0xe770da45450c2f07, 0xc369151430bc1384, 0xa45452d430bc1c1d, 0xa45450c28470770d, 0x51430bc1c1e2b70d, 0xc2f070770db2691, 0xbc1399a463d514bd, 0x1c36910c3b0])
  | 7, 0 => (packedWords [0x69151430bc22c706, 0x69151430bc111800, 0x5450c2f0707001c3, 0x430a11c19e270da4, 0x2f0707001c369151, 0x1c1dc369151430cb, 0x770da45450c2f0a1, 0x70da45450c2f070, 0x45450c2f070139e3, 0x4430ec2f070670da, 0xf430bc1c180070da, 0xc2f0707001c36912, 0xc1c19c3691514a10, 0x7001c369151494b, 0x2f70da45450c2f07, 0xa45450c2f0700c9e, 0x51430bc1c028770d, 0x51430bc1399c3691, 0xc2f0707001c3691, 0xbc1c1dd070da4545, 0x707749c369151430, 0x9fd70da45450c2f0, 0x1c369151430bc1c1, 0x151430e12f070700, 0x50c374bc1c1dc369, 0x50c2f070770da454, 0xbc1c1dc36918c54, 0x70670da45450c32, 0x18008b1c36915143, 0x1c35450c32cbc1c, 0x49c369151430bc60, 0xda45450c2f18007, 0x450c2f0707001fd7, 0xb0bc1c1e2c70da45, 0xf070770da45450c3, 0xc1dc3691514bd0c2, 0x779c369151430bc1])
  | 7, 1 => (packedWords [0x6918f5450c2f0707, 0x5450c2f070045dc3, 0x430bc1c022770da4, 0x430bc1c1dc369151, 0x2f0707845c369151, 0x1c1dc3691805450c, 0x770da45451e430bc, 0x369151430bc1c01f, 0x45450c2f070035dc, 0xf6915143070670da, 0xc2f07004dc0070da, 0xc2f070770da45450, 0x111dc36bda45450, 0x770da45450c2f07, 0x2670da45450c2f07, 0xc369151430bc1c1e, 0x514950c2f0707809, 0x18430bc1c1dc3691, 0xbc22c70770da4545, 0x1c369151430])
  | 8, 0 => 0x70da45450c2f0706
  | _, _ => 0

private def wordBlocks : Nat → Nat
  | 0 => (packedWords [0x0, 0x4000000000000000, 0x203202010000, 0x2000000000000000, 0xd0002004011c0, 0x4800000000000000, 0x3000580003819b, 0x400000000000000, 0x21020012211300, 0x0, 0x1410000a00300000, 0x6900000000000048, 0x2404c003e00c0846, 0x240000000000022, 0x9120300058000201, 0x100])
  | 1 => (packedWords [0xc00160000806000, 0x41b480, 0x8840a03680008001, 0x4000000000804004, 0x221d280fa04070c0, 0x202020, 0x800020320001000, 0x400000000080889, 0x221020012000200, 0x100000000020322, 0x949840aa36b00180, 0x80000000000080c8, 0x40a00d080e804000, 0x2010000000002400, 0x5208874800c8100c, 0x906])
  | 2 => (packedWords [0xcd0162004804c00, 0x2422602, 0x833425ba01211324, 0x4000000000908992, 0xa6dd2befac4864c9, 0x1000000000243265, 0x8b74858c8120db0, 0x9400000000090eda, 0xca2dd296fa04876c, 0x1000000000243b6, 0xb49b74afbeb121db, 0x90ed, 0x802000080c808000, 0x6010000000006800, 0x2008874a03e8b40c, 0x1a00])
  | 3 => (packedWords [0x210280da08020004, 0x6810812, 0x300058000201000, 0x2000000002100900, 0x1cd4172514c17d0, 0x840948, 0x803400080100060, 0x4000000003b0030, 0x8221d20032040318, 0x8000000000ec19c, 0x4008a5000000200, 0x40000000040140, 0x8022102001221020, 0x90000000016850, 0x20488caf0368a428, 0x5a14])
  | 4 => (packedWords [0x632be8dae90e0024, 0x16872a52, 0x401004144000040, 0x4000000006116520, 0x231d601373503190, 0x9000000001ec59c8, 0x48cfff07fcf42c64, 0x4000000007b1672, 0x823dd6173735837d, 0x50800000001ec7be, 0x4010041449824, 0x208950020410, 0x4080000000000000, 0x7348082254008504, 0x1020334058801281, 0x20895002141])
  | 5 => (packedWords [0xd080e80c001800, 0x8225400ed04c0a, 0x833425ba03211724, 0x20895003b49b92, 0x122d41053b08912, 0x9008225401c94480, 0x688fef03e8b42860, 0x4020895007b5530, 0x8a31d681ff3d0319, 0x82008225401ed5dc, 0x110000a00301408, 0x1281034400200800, 0x4122d410533588, 0xb040d100090240, 0x518cada04b8468, 0x103440024094])
  | 6 => (packedWords [0x0, 0x40d100090252004, 0xc418045cc54c841, 0x103440024096421, 0x41c04170510c0610, 0x1040d10009865b48, 0x18f7585cdc530db4, 0x410344002699eda, 0x863dd6173735c379, 0x8a040d10009ee5bc, 0x44108a5a00308220, 0x2902c00007084000, 0x1584000a8c8c0040, 0x8c00b00001c21000, 0x4600401004144906, 0x2c0000708402])
  | 7 => (packedWords [0x2102001200030004, 0xb00001c21019190, 0x10000a0030000880, 0x42c0000708406464, 0x61022812c003220, 0x50b00001c2101919, 0x61840aa36b001c8a, 0x942c000070840647, 0xd06d023e12c08766, 0xa40b00001c2103b3, 0x620334058801205b, 0xe902c00007085025, 0x5d84cd0bee8c4856, 0xb00001c21409, 0x5660000000000000, 0x2c0000708506])
  | 8 => (packedWords [0x6dd23e32c4836e94, 0xb00001c21419598, 0x300058000201800, 0x2c0000708506d66, 0x80c0016000080409, 0xb00001c2141b5d, 0x610000a003000000, 0x902c0000708506d7, 0xd84c003e00c08062, 0xa40b00001c2141b5, 0x7613002fb2302118, 0xe902c0000708506d, 0x5d84cd03e20c4816, 0x8a50b00001c2141b, 0xd761b408f84b020d, 0x2c0000708506])
  | 9 => (packedWords [0x4c003e00c0846690, 0xb00001c2143b7d8, 0x9874aa3eb101cb81, 0x42c0000708c0e4e4, 0x26102a8dac007220, 0xb00001c2303b3d, 0x68034203a0100020, 0x42c0000708d0656, 0x9a210280da000200, 0x10b00001c234195, 0x668874800c8100c2, 0x8042c0000708d065, 0x59a21d280fa04030, 0xba50b00001c23419, 0x5668b74a5be8120d, 0x2c0000708d06])
  | 10 => (packedWords [0x61d2a8fac4032a04, 0xb00001c2341959a, 0x9874aa3eb101c2a5, 0x42c0000708d06576, 0xa2dd296fa0483680, 0x50b00001c2341b59, 0x68b74a5be8120d22, 0x902c0000708d06d7, 0xda4cd0bee8c4806a, 0x10b00001c2341b5, 0x769874aa3eb100c2, 0x2942c0000708d06d, 0x5da6d02bedac0826, 0xaa50b00001c2341b, 0xd769b748f8cb120d, 0x2c0000708d06])
  | 11 => (packedWords [0x6dd2befac4836a94, 0xb00001c2341b5da, 0x8874a03e8101c301, 0x42c0000708d0e5e6, 0x26dd23e32c4836e0, 0x10b00001c2343b79, 0x68874a03e8100c20, 0x42c0000708d0ede, 0x9a2dd2163204836c, 0x10b00001c2343b7, 0xe68b74a5be8120d3, 0xc042c0000708d0ed, 0x79a2dd296fa04836, 0x3240b00001c2343b, 0xdf6833425ba01211, 0x2c0000708d0e])
  | 12 => (packedWords [0x21d280fa04070804, 0xb00001c2343b7da, 0x8b74a5be8121d325, 0x42c0000708d0edf6, 0xa2dd296fa04876c9, 0x40b00001c2343b7d, 0x693002fb2302118a, 0x902c0000708d0edf, 0xda4cd03e20c4806e, 0xa40b00001c2343b7, 0xf693342fba31211b, 0x42c0000708d0ed, 0x7da6102a8dac0060, 0x2010b00001c2343b, 0xdf69874aa3eb101c, 0x2c0000708d0e])
  | 13 => (packedWords [0x6d023e12c0826294, 0xb00001c2343b7da, 0x9b40afb6b02198a5, 0x42c0000708d0edf6, 0xa6dd23e32c4836e9, 0x50b00001c2343b7d, 0x69b74afbeb120dba, 0x942c0000708d0edf, 0xda6dd2befac4866e, 0x250b00001c2343b7, 0xf69b74afbeb121d3, 0xa942c0000708d0ed, 0x7da6dd2befac4876, 0xb010b00001c2343b, 0xdf69b74afbeb121d, 0x2c0000708d0e])
  | 14 => (packedWords [0x6dd2befac4876e94, 0x8b00001c2343b7da, 0x9b74afbeb121dfa5, 0x62c0000708d0edf6, 0xa6dd2befac4e76ed, 0x54b00001c2343b7d, 0x69b74afbeb321dba, 0x942c0000708d0edf, 0xda6dd2befae5976e, 0x10b00001c2343b7, 0x668874a03e8300c2, 0x8042c0000709f067, 0xd9a21d280fa2d031, 0xba50b00001c27c19, 0xff69b74afbeb321d, 0x2c0000709f0e])
  | 15 => (packedWords [0x6dd2befaed877e94, 0xb00001c27c3bfda, 0x13000f80302018a4, 0x42c000070a506d76, 0xa6dd2befac4876e9, 0x10b00001c2b43b7d, 0x68874a03e8100c60, 0x942c000070bf0676, 0xda6dd2befac4877e, 0x490b00001c2fc3bf, 0x640ccbd045ccc2e0, 0x8042c000070c4164, 0xd9a21d280fa25030, 0x2090b00001c37c59, 0x76688fef03e8b42c, 0x2c000070df16])
  | 16 => (packedWords [0x6dd2befae5876e94, 0xb00001c37c7bfda, 0x9bfeffbebb63dbad, 0x42c000070df1eff6, 0xa31d681ff3503190, 0x50b00001c3fc59d9, 0x69f75affffd61dfe, 0xd02c000070ff1eff, 0x800000000022082, 0x80b82255c211041, 0x46008a7032028220, 0x8042e08957084410, 0x59a21d280fa0c030, 0x2090b82255c2351d, 0x56688fef03e8382e, 0x2e0895708d47])
  | 17 => (packedWords [0x1004010512008100, 0xb82255c2950d588, 0x435004945806640, 0x2e089570a543562, 0x81c04170512e0e3d, 0x48b82255c2950d58, 0x2073505c945b87ff, 0x202e089570a54356, 0x9812fdc1ed1e0999, 0xb82255c2950d5, 0x6600000000000000, 0x2902e089570a5475, 0x5d84c003e00c0806, 0x2010b82255c2951f, 0x5668874a03e8100c, 0x2e089570ad47])
  | 18 => (packedWords [0x21d280fa04031804, 0xb82255c2b51d59a, 0x8c75a07fc580e641, 0x42e089570ad47566, 0xa6dd2befac4876e9, 0x58b82255c2b53f7d, 0x69b74afbeb129dfb, 0xd62e089570ad4fdf, 0xda7dd6bfffd6e7ff, 0x400b82255c2b53f7, 0x628435207b478066, 0x9042e089570bf437, 0xd8a31d681ff3f039, 0x6000b82255c2fd0d, 0x7668034203a03000, 0x2e089570bf47])
  | 19 => (packedWords [0x210280da08020004, 0xb82255c2fd1dd9a, 0x8874800c8100c601, 0x42e089570bf47766, 0xa21d280fa0403180, 0x10b82255c2fd1dd9, 0x68874a03e8300860, 0x42e089570bf4776, 0x9a21d280fa0c0308, 0x10b82255c2fd1dd, 0x668874a03e8300c6, 0x8042e089570bf477, 0xd9a21d280fa2d031, 0xea40b82255c2fd1d, 0xf7693342fba33201, 0x2e089570bf47])
  | 20 => (packedWords [0x6dd2befacc877e94, 0xb82255c2fd3ffda, 0x48b504144822048, 0x2e089570e557566, 0x8122dc1cd1a08812, 0x80b82255c3955d59, 0x604bf50494582664, 0x242e089570e55756, 0x98332f4117330b81, 0x490b82255c3955d5, 0x660cffd04dcdc2e6, 0x3b02e089570e5575, 0x5d85e2d7f05d288e, 0x2480b82255c3955f, 0x56684bf707b45822, 0x2e089570ed57])
  | 21 => (packedWords [0x332fc1df120a8124, 0xb82255c3b55d59a, 0x8cffd04dc582e249, 0x42e089570ed57566, 0xa33ffc1ff160b892, 0xd0b82255c3b55d59, 0x69ffffffff5a3fbe, 0x202e089570ed5fdf, 0x8812fd41253f0999, 0x480b82255c3dd4dd, 0x66048b50414ec224, 0x9042e089570f7577, 0xd8a31d6013737039, 0x480b82255c3fd5d, 0x766848b707346822, 0x2e089570ff57])
  | 22 => (packedWords [0x12fd412516089920, 0xb82255c3fd5dd9a, 0x84bf707b47822648, 0x42e089570ff57766, 0xa21d280fa2d03180, 0x90b82255c3fd5dd9, 0x688fef03e8b42c60, 0x42e089570ff5776, 0x9a31d681ff3d0319, 0x490b82255c3fd5dd, 0x668ccbd045ccc2a0, 0x1242e089570ff577, 0xd9a332fc1df3b0a8, 0x6490b82255c3fd5d, 0x7668cffd04dcdc2e, 0x2e089570ff57])
  | 23 => (packedWords [0x33ffc1ff1e0b9924, 0xb82255c3fd5dd9a, 0x8cfff07fcdc2e649, 0x42e089570ff57766, 0xa33ffc1ff3f0a992, 0x90b82255c3fd5dd9, 0x68cfff07fcfc2e24, 0x242e089570ff5776, 0x9a33ffc1ff3f0b99, 0x498b82255c3fd5dd, 0x668cfff07fcfc2e7, 0x9252e089570ff577, 0xd9a33ffc1ff3f0f9, 0x6490b82255c3fd5d, 0x7668cfff07fcfc6e, 0x2e089570ff57])
  | 24 => (packedWords [0x3fffd7ff3febfff6, 0xb82255c3fd5dd9a, 0x9fffffffffe2feed, 0x42e089570ff57f76, 0xa33ffc1ff3f0f9d2, 0x90b82255c3fd7df9, 0x68cfff07fcfc2e64, 0x242e089570ff5ffe, 0x9a3fffd7ff3f8bfd, 0x490b82255c3fd7ff, 0xf68cfff07fcfc3e6, 0xdb42e089570ff5ff, 0xfda3fffd7ff3f8fd, 0x6490b82255c3fd7f, 0xff69cfffa7fffc3e, 0x2e089570ff5f])
  | 25 => (packedWords [0x7fffffffff8fffb4, 0xb82255c3fd7ffda, 0x9b74afbeb135dba7, 0x83c3440728d8edf7, 0x4522d6905d248a32, 0xb0f0d101cb125919, 0x51ccbda45fcd6e8c, 0x903c344072c49646, 0xdc4c003e00c08062, 0xa50f0d101cb165b5, 0xf79b74afbeb121db, 0xfbc3c344072cd9ed, 0x7de7ffffffff7dfe, 0x8e40f0d101cb367b, 0xd7717010fc174301, 0x3c344072e596])
  | 26 => (packedWords [0x7dd6bfffd4c76f94, 0x8f0d101cbb67b7de, 0x1fffdfcdfdfeffff, 0x3e3cd572e5d7567, 0xc122d41051208812, 0x80f8f355cb975f59, 0x7078b55c144b2384, 0x2c3e3cd572e5d7d6, 0x9e33ffc1ff3f5b99, 0xcb0f8f355cbff5dd, 0x679cfffa7fffd6ee, 0x9243e3cd572ffd77, 0xd9e33ffc1ff3f0b9, 0xe490f8f355cbff5f, 0xf678ffff5ffcff2f, 0x3e3cd572ffd7])
  | 27 => (packedWords [0xc0002800c02402d9, 0x5020c80240000060, 0x308a7a323203000a, 0x40832009000001c, 0x800000000000000, 0xa5020c8024000206, 0x8208a5000028a201, 0xd1428bb509004100, 0x68800080c8082400, 0x3410a2ed42401040, 0x1a23000580002810, 0xcd0428bb50921419, 0x66a8cd096e804a44, 0x63410a2ed424a526, 0xb1aa33425ba03281, 0x428bb5093b41])
  | 28 => (packedWords [0xcc003e00c0e062d8, 0x142dd802c0202064, 0x308a5a003002000a, 0xc50b7600b409481d, 0x6e32be8dac00e002, 0xb142dd802d227227, 0xdb8cafa36ba42800, 0x2850b7600b5a94a1, 0xf4de2d7f05d0c861, 0x5a142dd802d865b4, 0x9248b5041449a20, 0xf852bff50b60d10, 0x47cce297e00c0a84, 0x87414affd42d8756, 0xd3b270105c144381, 0x52bff50b61d7])
  | 29 => (packedWords [0xcc003e00c0806290, 0x1b20c81e6141b5f8, 0xbb74afbeb121dba5, 0xd6c8320798d0edfe, 0xaedd2befac4a76ed, 0xe1b20c81e6343b7f, 0xe308a5a00308a20b, 0xf96e8bb579844105, 0x78c229e8c8ca2c82, 0xb55ba2ed5e611041, 0xfebb74afbeb329db, 0xefd6e8bb5798d4fd, 0x7faeffbfefaceafe, 0xffedba2ed5e6353f, 0x57e37bf7ffb77bb7, 0x6e8bb579a543])
  | 30 => (packedWords [0x8c00160000a040d0, 0x1ba2ed5e6951f5f8, 0x33000f80302818b4, 0x46e8bb579a547d7e, 0xaadd296fa04a348d, 0x51ba2ed5e6b51f5f, 0xebb74afbeb129dbb, 0xd46e8bb579ad4fdf, 0xfaedd2befacca37a, 0xb51ba2ed5e6fd1fd, 0xfebb74afbeb329df, 0x1206e8bb579bf4ff, 0x5f8922d410512088, 0x7c1ba2ed5e7955f, 0xd7e278b55c144aa3, 0x6e8bb579e557])
  | 31 => (packedWords [0xf3ffe9ffff2f9bfd, 0x1ba2ed5e7fd5ddfa, 0xacfff07fcfc2e649, 0x46e8bb579ff57f7e, 0xabfffd7ff3fabd9f, 0x61ba2ed5e7fd5fdf, 0xf33000f80303818b, 0xdc7cb7607b8586d7, 0xfeedd2befac4e76e, 0xae1f2dd81ee363b7, 0x7f338a5f80302218, 0xebc7cb7607bc596d, 0x7feeffbfefac48f6, 0x8ff5f2dd81ef367b, 0x47f3ccbfa77fedfe, 0x7ebff57bc4d7])
  | 32 => (packedWords [0x922d410512088128, 0x1faffd5ef975d5bc, 0x248b5041449a205a, 0x7ebff57be5d756f, 0xc922d41051208812, 0xc1faffd5ef975f5f, 0xf278b55c144ba387, 0x287ebff57be5d7d7, 0xfcc2296800c00800, 0xb41faffd5ef975f5, 0x7f33000f80302818, 0x2f87ebff57be5d7d, 0x5fcce297e00c0a86, 0x4a1faffd5ef975f, 0xd7f348b5a4174822, 0x7ebff57be5d7])
  | 33 => (packedWords [0xdc043f05d0e063d0, 0x1faffd5ef975f5fc, 0x378b5fc174a238ee, 0x87ebff57be5d7d7f, 0xcde2d7f05d2a8c1f, 0xa1faffd5ef975f5f, 0xf378b5fc174b2384, 0xf87ebff57be5d7d7, 0xfcde2d7f05d2e8e3, 0xfe9faffd5ef975f5, 0x7f378b5fc174ba39, 0x3fa7ebff57be5d7d, 0x5fcde2d7f05d2e8f, 0x8fe1faffd5ef975f, 0xd7f378b5fc174be3, 0x7ebff57be5d7])
  | 34 => (packedWords [0xde2dffcddaece3f9, 0x9faffd5ef975f5fc, 0x37bf5fc975ba7ffe, 0xc7ebff57be5d7d7f, 0xcff2f7f17f3fbe3f, 0xe1faffd5ef975f5f, 0xf378b5fc174bb39f, 0xfc7ebff57be5dfdf, 0xfeffffffffd6ebeb, 0xfe1faffd5efb75f5, 0xffb7bf7ffb75bb3b, 0x3fc7ebff57beddfd, 0x7feff2fffdfd2eee, 0xbff1faffd5efb77f, 0xdffbfffdfcdf5baf, 0x7ebff57beddf])
  | 35 => (packedWords [0xffffffffd6efeffc, 0x1faffd5efb77f7fe, 0xb7bf7ffb77ba3efe, 0xc7ebff57bffd7f7f, 0xef3ffe9ffff0b992, 0xf1faffd5efff5fdf, 0xfbfcbfff7fefab8f, 0xfc7ebff57bffd7f7, 0xfeffff7f37f7ebfb, 0xff1faffd5efff5fd, 0x7fbffffffff7bafe, 0xbfc7ebff57bffd7f, 0xdfeffffffffffebf, 0xfff1faffd5efff5f, 0xfffbffffffffffbf, 0x7ebff57bffdf])
  | 36 => (packedWords [0x140403, 0xe05002a1000a0201, 0x400000000a440400, 0x381400a841220200, 0x300d080e80c041c0, 0x1605002a1068a0a0, 0xc840a0368a45800, 0x681400a841a2828, 0x321d2003225131c, 0x1e05002a1068a0a, 0x80c874a03e8b45c7, 0xed781400a841a282, 0xa032dd296fa2df77, 0x205002a1068a0, 0xa80c000000000000, 0x81400a841a28])
  | 37 => (packedWords [0xcd0162004805c02, 0xa05002a10eca2e03, 0xc33425ba01211724, 0x681400a843b28b92, 0x32dd2163204837c0, 0x1a05002a10ecbbe8, 0xcf7585cdcd60d74, 0x281400a847b3efa, 0xb0cd096e80c805c, 0xa0d227e10eda6e, 0x8143000580003419, 0x91744a8600a88, 0xa070000000000000, 0x1245d12a196af2, 0xa81c840800488448, 0x91744a865abc])
  | 38 => (packedWords [0x21d2003225131c06, 0xa45d12a196af2a07, 0xcb40858488749901, 0x491744a865abca81, 0x7232bc0da291a002, 0x1245d12a196af2a1, 0x5d840aa36b845800, 0x691744a865abca9, 0x8731d6013735533d, 0x41245d12a196af9a, 0xa1cc418045cc54c8, 0xc0491744a865abee, 0xe072dd2163225924, 0x201245d12a196ef2, 0xfa1c874800c8944c, 0x91744a865bbe])
  | 39 => (packedWords [0x2d02161221926004, 0x245d12a196efbe87, 0xcb74858c8964db01, 0x291744a865bbefa1, 0x5100401053150110, 0xa45d12a19cac080, 0x1470105c14c741d4, 0x691744a8672b8a8, 0x731d6013735531d, 0x41a45d12a19eae0a, 0x81cc418045cc5484, 0xd0291744a867abca, 0xe071cd4172535d05, 0x700a45d12a19eee2, 0xb81c334058801201, 0x91744a867bbc])
  | 40 => (packedWords [0x21d2003225121804, 0x245d12a19eef2e07, 0xcb40858488649001, 0x691744a867bbcb81, 0x72dd2163225925c0, 0x245d12a19eef2e0, 0x1c70105c14430184, 0x291744a867bbefa, 0x871cd4172514c07d, 0x1245d12a19eefbe, 0xa1c874800c8944c6, 0xc0691744a867bbef, 0xe872dd2163225937, 0x41245d12a19eefb, 0xfa1cc418045cc448, 0x91744a867bbe])
  | 41 => (packedWords [0x31d6013735131904, 0x245d12a19eefbe87, 0xcf4185c5cc749841, 0x691744a867bbefa1, 0x73dd6173714c37d0, 0x1a45d12a19eefbe8, 0x1cf7585cdcd64d74, 0x491744a867bbefa, 0x873dd6173735937d, 0x41a45d12a19eefbe, 0xa1cf7585cdcd70df, 0xd0691744a867bbef, 0xe873dd6173735d27, 0xb41245d12a19eefb, 0xfa1cf7585cdcd74d, 0x91744a867bbe])
  | 42 => (packedWords [0x3dd6173735d37904, 0xa45d12a19eefbe87, 0xcf7585cdcd74df41, 0x691744a867bbefa1, 0x73dd6173735f37fd, 0x1e45d12a19eefbe8, 0x1cf75a5ffcf75df4, 0x2691744a867bbefa, 0x973fffd7ff3ddb7d, 0x65a45d12a19eefbe, 0xb3cf7585cdcd74df, 0xd9691744a867bbef, 0xecf3dd697ff35d77, 0xf41a45d12a19eefb, 0xfb5df75affffd75d, 0x91744a867bbe])
  | 43 => (packedWords [0x3dd6173737f3fd46, 0xa4df37e19efffe87, 0xcf7585cdcd74df41, 0x6937cdf867bfffa3, 0xf3dd6173735f37dd, 0x1a4df37e19efffe8, 0x3cf75a5ffcf74df4, 0x97937cdf867bfffa, 0xdb6dd2befac4976e, 0x1eb5002bd234bb7, 0xe6c874a03e8b45c7, 0xe94ad400af49f2e7, 0xfdb6dd2befac4876, 0xfa5eb5002bd27cbb, 0xff6db74afbeb321d, 0xad400af49f2e])
  | 44 => (packedWords [0x6dd2befae5977e96, 0x6b5002bd27cbbfdb, 0xdb74afbebb65dba5, 0x7ad400af49f2eff6, 0xb6dd2befaed977e9, 0x1ab5002bd27cbbfd, 0x6cb74a5be8120d70, 0x92ad400af4bf2efe, 0xdb4cd03e20c4807e, 0xa5ab5002bd2fcbbf, 0xf6db74afbeb121df, 0xfd7ad400af4bf2ef, 0xf8b3dd697ff3ff7f, 0x701ebd227fd2fdad, 0x7e6c874a03e8301c, 0xaf489ff4bf6f])
  | 45 => (packedWords [0x21d280fa2d171c07, 0x2bd227fd2fdbdf9b, 0xc874a03e8300c601, 0x6af489ff4bf6ffe6, 0xb2dd296fa0c837c0, 0x5abd227fd2fdbff9, 0x6db74afbeb321dfa, 0x27af489ff4bf6fff, 0x9b33ffc1ff3f1b99, 0x49ebd227fd3fdddd, 0xe6ccfff07fcfc3e7, 0xd26af489ff4ff7f7, 0xf9b33ffc1ff3f1b9, 0x6496bd227fd3fdfd, 0x7e6ccfff07fcfc7e, 0xaf489ff4ff7f])
  | 46 => (packedWords [0x33ffc1ff3f1f9d27, 0x2bd227fd3fdfdf9b, 0xccfff07fcfc2e649, 0x6af489ff4ff7ffe6, 0xb3fffd7ff3f8bdd2, 0x5abd227fd3fdfff9, 0x7db74afbeb135dba, 0x2fbd744af68daedf, 0x9773ffe9ffff5fbf, 0x12f5d12bdb7af9b, 0xe7c8408004884480, 0x804bd744af6dfbef, 0xf9f21d280fa25130, 0x8a52f5d12bdb7efb, 0xff7db408f84b8649, 0xbd744af6dfbe])
  | 47 => (packedWords [0x6dd2befae5976e94, 0xaf5d12bdb7efbfdf, 0xcf7585cdcdf4ffc1, 0x6bd744af6ffbefe1, 0xf3dd6173735d37f9, 0xbaf5d12bdbfefbf8, 0x5dfffdfcdfdf6ffc, 0x6bd744af6ffbefe, 0x9f3dd6173735d37d, 0x41af5d12bdbfefbf, 0xe7cf75a5ffcd74df, 0xe96bd744af6ffbef, 0xfdf6dd2befae5977, 0xfe5af5d12bdbfefb, 0xff7df758fcdfd74d, 0xbd744af6ffbe])
  | 48 => (packedWords [0x7dd6bffff5d77f96, 0xaf5d12bdbfefbfdf, 0xccfff07fcfd6e649, 0x4bf7cdff6fff7767, 0xf31d601373713990, 0x1afdf37fdbfffff8, 0x3cf7585cdcdf4ff4, 0xd6bf7cdff6fffffe, 0x8f3dd6173737f3ff, 0x12fdf37fdbfffff, 0xe7c8408004884480, 0x804bf7cdff6fffff, 0xf9f21d280fa2d131, 0x492fdf37fdbffff, 0xfe7cccbd045ccc6a, 0xbf7cdff6ffff])
  | 49 => (packedWords [0x33ffc1ff3f1b9924, 0xafdf37fdbfffff9f, 0xcf7585cdcd74df41, 0x6bf7cdff6fffffe7, 0xf3dd697ff3dd37d0, 0x9afdf37fdbfffff9, 0x7cfffd5cdcdf6ff4, 0x26bf7cdff6fffffe, 0x9f3fffd7ff3fdbfd, 0xedafdf37fdbfffff, 0xf7dffffffffff7ff, 0x4d3bf7cdff6fffff, 0x2618c00160000a44, 0x7070caa3400a2, 0xa98e000203202010, 0xc1c32a8d1a28])
  | 50 => (packedWords [0xe102a8dac8060005, 0x7070caa3468b2a73, 0xe33425ba03211324, 0x3c1c32a8d1b28b9a, 0x38cd096e80c845c0, 0x97070caa34eca2e6, 0xce8caf0368a43800, 0x43c1c32a8d5a3ca9, 0x2180000000082010, 0x10f0f2efe34c9848, 0x88e034203a030907, 0x43c3cbbf8d3a692, 0xa63800080c808241, 0x610f0f2efe34e9a6, 0x30ae034203a03080, 0xc3cbbf8d3b61])
  | 51 => (packedWords [0x8cd016200ca05c43, 0x70f2efe34eda6e23, 0xe000203202010000, 0x1c3cbbf8d3b69b9a, 0xb80d080e80c04180, 0x430f2efe34eda6e6, 0xae30005800028103, 0xd1c3cbbf8d3b69b9, 0x6b8c0096c808a440, 0x34b0f2efe34eda6e, 0x9ae3340588012817, 0xcd2c3cbbf8d3b69b, 0xe6b8cd096e804a45, 0x700f0f2efe34eda6, 0xb9ae33425ba03211, 0xc3cbbf8d3b69])
  | 52 => (packedWords [0x8cd096e80c845c91, 0xb0f2efe34eda6e6b, 0xe33425ba03281734, 0x1c3cbbf8d3b69b9a, 0xb8cd096e80ca44cd, 0x470f2efe34eda6e6, 0xae33425ba0329163, 0xd3c3cbbf8d3b69b9, 0x6b8cd096e80ca45c, 0x34f0f2efe34eda6e, 0x9ae33425ba032957, 0xed3c3cbbf8d3b69b, 0xe6b8cd096e80ce47, 0x735f0f2efe34eda6, 0xb9aeb74a5be8b6dd, 0xc3cbbf8d3b69])
  | 53 => (packedWords [0xedd2befacca65cd7, 0xf0f2efe34edb6e7b, 0xe33425ba03291f34, 0x7c3cbbf8d3b6ffba, 0xbadd296fa0ca77cd, 0xdf0f2efe34edbfee, 0xeebfef5be8b6b973, 0xd7c3cbbf8d7b7db9, 0xebbdd697ff3da75d, 0x12f0f2efe35edffe, 0x960000000001c00, 0x9d1f76a8f00a00, 0x265c0002800c0140, 0x9b6f47ddaa3c02a2, 0x89973000f80303d1, 0xd1f76a8f00a8])
  | 54 => (packedWords [0xc000a8c8c8140009, 0x747ddaa3c6aa2a67, 0xf840aa36ba458003, 0xfd1f76a8f1aa8a99, 0x7edd2befaedf77ed, 0xef47ddaa3c6aa2a6, 0x9778b5fc17cff39f, 0x29d1f76a8f40b889, 0x2582294000291800, 0xa747ddaa3d4ac08, 0x99e08a70320a4700, 0x1d1f76a8f5ab8a, 0xa67800080c808040, 0x1347ddaa3d6af2, 0xa99e840800488448, 0xd1f76a8f5abc])
  | 55 => (packedWords [0xa10280da29160005, 0x747ddaa3d6af2a67, 0xf8408a04b8458003, 0x5d1f76a8f5abca99, 0x7a32bc0da291e002, 0xa347ddaa3d6af2a7, 0xdf08a5a003002000, 0x29d1f76a8f5abca9, 0x77c229e8c8c80c00, 0x1747ddaa3d6af2a, 0x9df840aa36ba4580, 0x2cd1f76a8f5abca, 0xa77e32b6812e11a0, 0xb747ddaa3d6af2, 0xa9df8cafa36b2038, 0xd1f76a8f5abc])
  | 56 => (packedWords [0xe32be8dae11e002c, 0x747ddaa3d6af2a77, 0xf8cafa36ba43800b, 0xcd1f76a8f5abca9d, 0x7e32be8dae91a002, 0xb747ddaa3d6af2a7, 0xdf8cafa36ba47800, 0x2dd1f76a8f5abca9, 0x77e32be8dae91f00, 0xbf47ddaa3d6af2a, 0x9df8fefa3ebb47c7, 0x6ffd1f76a8f5abca, 0xa77ef2bfedae9fe6, 0x32f747ddaa3d6af2, 0xb9ffbfeffbebb679, 0xd1f76a8f5bbc])
  | 57 => (packedWords [0xeffbfefaed9f6c2d, 0xf47ddaa3d6efbef7, 0xfbfeffbebb67970b, 0x6d1f76a8f7bbcb9d, 0x7bdd6173735d37d0, 0x1f47ddaa3deefbee, 0x9ef75a5ffcf75df4, 0xdfd1f76a8f7bbefb, 0xe7fdd63f37f5f77f, 0x4b747ddaa3deefbe, 0xbdfcfffa7fff47c6, 0x12dd1f76a8f7bbef, 0xef7ff2fffdff9de6, 0xf4bb47ddaa3deefb, 0xfbdffffdfcdfd76d, 0xd1f76a8f7bbe])
  | 58 => (packedWords [0xfffffffffddf7d2f, 0xf47ddaa3deefbef7, 0xf3342fba333d1fb6, 0xbd3ffff8f3be9b9b, 0x5922d41053b78916, 0xef4ffffe3dcbc482, 0x9778b5fc17eff3df, 0x6fd3ffff8f72f9a9, 0x27b3ffc1ff3f7f9d, 0x5bf4ffffe3debe4a, 0x9dfccbfa77fedfa4, 0xdfbd3ffff8f7afda, 0xe6f9efdd7ed3ffcd, 0x734f4ffffe3defe6, 0xb9be33425ba03291, 0xd3ffff8f7bfd])
  | 59 => (packedWords [0xad02161221b240d4, 0xf4ffffe3deff6e6f, 0xeb74a5be8b6d9735, 0xbd3ffff8f7bfdb9b, 0xfcef9fee8ccac5cf, 0xb74ffffe3deff6e7, 0xff8cafa36ba47800, 0x2dd3ffff8f7bfdb9, 0x7fe3fbe8faed1e18, 0x3f74ffffe3deff6e, 0x9ffbcaffb6ba6f90, 0xcffd3ffff8f7bfdb, 0xe7feffbfefaedbe5, 0xf5bf4ffffe3deff6, 0xfa9efffd5cdcffef, 0xd3ffff8f7bff])
  | 60 => (packedWords [0x9cd497ed1ce47dd3, 0xb4ffffe3defffeef, 0xef7585cdcd7cdf75, 0x7d3ffff8f7bfffbb, 0xfbdd697ff3df77dd, 0xff4ffffe3defffee, 0xfffffffffff7fdf7, 0xd7d3ffff8f7bfffb, 0xfbedd2befac4a76e, 0x17b70cabf634bb7, 0xfee874a03e8301c2, 0x291edc32afd9f2ef, 0xffbcc00bec8c8846, 0xba57b70cabf67cbb, 0xffefb74afbeb321d, 0xedc32afd9f2e])
  | 61 => (packedWords [0xedd2befacc877e97, 0xfb70cabf6fcbbffb, 0xf8fefa3ebbcfe7bf, 0xbefcbbffd9e692de, 0xbcef9fee8ceacdef, 0x4fbf2efff6fda6f7, 0xae33425ba03295fb, 0xd3efcbbffdbf6bff, 0xeb9cd497ed1ee5ff, 0x7bf2efff6fdaff, 0xfee0002032020100, 0x801efcbbffdbf6ff, 0xffb80d080e80c041, 0x734fbf2efff6fdbf, 0xffee33425ba03291, 0xefcbbffdbf6f])
  | 62 => (packedWords [0x8cd096e80ca47cd3, 0x7bf2efff6fdbfffb, 0xe874a03e8301c601, 0x7efcbbffdbf6fffe, 0xbadd296fa0ca75cd, 0x5fbf2efff6fdbfff, 0xeeb74a5be8329df3, 0xd3efcbbffdbf6fff, 0xfbccd0bee8cca47e, 0x17bf2efff6fdbff, 0xfef874aa3eb301c6, 0x2d5efcbbffdbf6ff, 0xffbed02bedac8a66, 0xfb5bbf2efff6fdbf, 0xffefb748f8cb128d, 0xefcbbffdbf6f])
  | 63 => (packedWords [0xedd2befac4a77ed6, 0x7bf2efff6fdbfffb, 0xfb74afbeb321dfa5, 0x7efcbbffdbf6fffe, 0xbedd2befacca67ed, 0x5fbf2efff6fdbfff, 0xefb74afbeb329d73, 0xd5efcbbffdbf6fff, 0xfbedd2befacca76e, 0xb5fbf2efff6fdbff, 0xfefb74afbeb329df, 0xed7efcbbffdbf6ff, 0xffbedd2befaedb77, 0x487bf2efff6fdbf, 0xffee48b707346832, 0xefcbbffdff7f])
  | 64 => (packedWords [0x9efdd7ed1eacddf3, 0x7bf2efff7fdffffb, 0xecfff07fcfc3e649, 0x7efcbbffdff7fffe, 0xbbfffd7ff3fafddf, 0xdfbf2efff7fdffff, 0xeffffffffffebfff, 0xdbefcbbffdff7fff, 0xfdcc003e00c0f466, 0xa77f7ddabfe16bb7, 0xfffb74afbeb125db, 0xedffdf76aff8daed, 0x7ffedd2befac4f76, 0xfb7ff7ddabfe36bb, 0xffffb74afbebb7dd, 0xfdf76aff9fae])
  | 65 => (packedWords [0xff2f7f17f3ffe7ff, 0x7f7ddabff12fb3f5, 0xf8cafa36bac7a08b, 0xdfdf76affdebcadd, 0x7e32be8dae91f222, 0xb7f7ddabff7afbbf, 0xdfccbfa77fed7e8c, 0x2dfdf76affdebeef, 0xffe32be8dae91e00, 0xb7f7ddabff7efbf, 0xfff8fefa3ebb47c2, 0xe94fdf76affdfbef, 0xfffedd2befae5976, 0xba57f7ddabff7efb, 0xffffb74afbebb65d, 0xfdf76affdfbe])
  | 66 => (packedWords [0xef2bfedae99e62bd, 0x7f7ddabff7efbfff, 0xfbfeffbebb67dbaf, 0xffdf76affdfbefff, 0xffffffffffddf7fb, 0xeff7ddabfffefbff, 0xf738a7fb232bf39b, 0xdbffffffff84e98d, 0xeddcd43f25d6f5ff, 0xb7ffffffffe97af7, 0xfffb74afbeb33ddf, 0x2dffffffffbfeff, 0xb7fe32be8daeb1e8, 0xbf7ffffffff7bf6, 0xadff8cafa36bacfa, 0xffffffffdefd])
  | 67 => (packedWords [0xde2d7f05d2f8e7fa, 0xfffffffff97ff7fd, 0x778b5fc174bf39fe, 0xbffffffffe5ffdff, 0xdd22de9cdfb7c93f, 0xbfffffffffdbc497, 0xd7ccbda45fedeecd, 0xfbfffffffff6f766, 0xad9efd57253ff9ff, 0xfefffffffffdfcdd, 0x7f778b5fc17efe3c, 0x92dfffffffff7f7f, 0xdbfb3ffc1ff3f1b9, 0x65bfffffffffffdd, 0x76fecfff07fcfdee, 0xfffffffffff7])
  | 68 => (packedWords [0xb3ffc1ff3f1b9924, 0x7fffffffffffffff, 0xecfff07fcfc7e649, 0x7fffffffffffffff, 0xfbfffd7ff3ffffdf, 0xe3ffffffffffffff, 0xff78b5fc174ba38f, 0xf9ffffffffffffff, 0xffde2dffcddaece3, 0xfebfffffffffffff, 0xfff7bf5fc975ba3f, 0xffbfffffffffffff, 0xfffdefdffeddeecf, 0xb7ffffffffffff, 0xffff8cafa36ba478, 0xffffffffffff])
  | 69 => (packedWords [0xe3fbe8faed1f182d, 0xffffffffffffffff, 0xfb74afbebb6ddfb5, 0xffffffffffffffff, 0xfeffbfefaedbf7ef, 0xb7ffffffffffffff, 0xffccbfa77fec7a04, 0x2dffffffffffffff, 0xfff3ffe9ffff1f99, 0xf5ffffffffffffff, 0xffff75afffff7ddf, 0x3fcfffffffffffff, 0xfffff2f7f17f3fae, 0x8ff7ffffffffffff, 0xfffffcbfff7feffb, 0xffffffffffff])
  | 70 => (packedWords [0xffff7f37f7fbfffe, 0xffffffffffffffff, 0xfffffffff7bbffff, 0xefffffffffffffff, 0xffffffffff7fffff, 0xf7ffffffffffffff, 0xfffffffffffe7ffe, 0xffffffffffffffff, 0xffffffffffffbfdd, 0x4bffffffffffffff, 0xfffffffffffff7ff, 0xffffffffffffffff, 0xfffffffffffffeff, 0xfffbffffffffffff, 0xffffffffffffffef, 0xffffffffffff])
  | 71 => (packedWords [0xfffffffffffeffff, 0x7fffffffffffffff, 0xfffffffffffffbff, 0xdfffffffffffffff, 0xffffffffffffffbf, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffff])
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
private theorem span2_0 : span (check 2) 7 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span2 : span (check 2) 7 0 = true :=
  span2_0

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span3_0 : span (check 3) 48 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span3_48 : span (check 3) 12 48 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span3 : span (check 3) 60 0 = true :=
  (span_join span3_0 span3_48)

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
private theorem span4_144 : span (check 4) 48 144 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4_192 : span (check 4) 48 192 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4_240 : span (check 4) 4 240 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4 : span (check 4) 244 0 = true :=
  (span_join (span_join span4_0 (span_join span4_48 span4_96)) (span_join span4_144 (span_join span4_192 span4_240)))

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
private theorem span5_816 : span (check 5) 25 816 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5 : span (check 5) 841 0 = true :=
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
private theorem span6_720 : span (check 6) 34 720 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6 : span (check 6) 754 0 = true :=
  (span_join (span_join (span_join (span_join span6_0 span6_48) (span_join span6_96 span6_144)) (span_join (span_join span6_192 span6_240) (span_join span6_288 span6_336))) (span_join (span_join (span_join span6_384 span6_432) (span_join span6_480 span6_528)) (span_join (span_join span6_576 span6_624) (span_join span6_672 span6_720))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span7_0 : span (check 7) 48 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span7_48 : span (check 7) 1 48 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span7 : span (check 7) 49 0 = true :=
  (span_join span7_0 span7_48)

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


end Monotone15310Lower

end

section

namespace Monotone15310Control

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[
  ⟨.and, [0, 1]⟩,
  ⟨.and, [1, 2]⟩,
  ⟨.or, [2, 5]⟩,
  ⟨.or, [4, 7]⟩,
  ⟨.or, [6, 7]⟩,
  ⟨.and, [0, 8]⟩,
  ⟨.and, [3, 10]⟩,
  ⟨.and, [11, 9]⟩,
  ⟨.or, [12, 13]⟩
], 14⟩

theorem monotone : Monotone2 circuit := by
  intro gate mem
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 15000000 in
theorem exactTable : ∀ x : Fin 6 → Bool,
    circuit.eval (List.ofFn x) = Monotone15310Lower.target x := by
  decide +kernel

end Monotone15310Control

end

end PEqualNP.Outside.L_meta_15309_aux

open PEqualNP.Outside.L_meta_15309_aux

open PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_15309 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937060992 * 2 ^ 32 + 3902851200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937060992 * 2 ^ 32 + 3902851200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have budget : 9 ≤ s := Monotone15310Lower.lower h
  exact ⟨Monotone15310Control.circuit, Monotone15310Control.monotone, budget,
    Monotone15310Control.exactTable⟩
