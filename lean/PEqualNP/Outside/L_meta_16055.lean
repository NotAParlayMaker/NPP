import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16055_aux

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

namespace Monotone16056Lower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoreTable7402_aux

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4277071584 * 2 ^ 32 + 4209699552)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

private def k : Nat := 63
private def rows : List Nat := [18, 12, 1, 33, 1, 26, 16, 24, 20, 8, 52, 4, 10, 34, 26, 56, 3, 3, 10, 2, 40, 1, 34, 20, 40, 52, 12, 18, 3, 34, 52, 26, 35, 44, 26, 44, 35, 56, 35, 56, 26, 35, 26, 56, 44, 26, 35, 44, 56, 26, 52, 52, 35, 44, 44, 35, 52, 52, 52, 52, 44, 56, 56, 19, 14, 5, 41, 17, 58, 17, 25, 21, 9, 60, 6, 11, 42, 27, 60, 7, 19, 42, 6, 42, 9, 50, 22, 41, 53, 28, 50, 11, 38, 42, 6, 42, 17, 9, 5, 5, 6, 28, 5, 50, 6, 42, 50, 9, 5, 9, 6, 17, 28, 50, 9, 50, 42, 50, 17, 17, 5, 6, 28, 28, 9, 42]
private def inputs : List Nat := [(packedWords [0x809042511023001c, 0x11c4b84f0991a9ee]), (packedWords [0x80926755b84f7021, 0x223a4790fc6fbc11]), (packedWords [0x1f6c900a46800d02, 0xf01517c5344c683]), (packedWords [0x7063bdae8514d2a2, 0x3c152a22aa9a7b55]), (packedWords [0xef0f2da4ca80c5e1, 0xceb84a1076162f8]), (packedWords [0x7ffddafb6350a408, 0x203a0680b5aa5214])]

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
  | 3 => 37
  | 4 => 232
  | 5 => 708
  | 6 => 661
  | 7 => 47
  | 8 => 1
  | _ => 0

private def stateWidth : Nat → Nat
  | 3 => 44
  | 4 => 54
  | 5 => 64
  | 6 => 74
  | 7 => 74
  | 8 => 64
  | _ => 0

private def hashBlocks : Nat → Nat → Nat
  | 3, 0 => (packedWords [0xcd18dd70c5a62b3, 0x18328bf41276e4b3, 0x28ae11db260a72c0, 0x3f0d961134379be5, 0x47c5030343159306, 0x4ce3bdb84caadd55, 0x6986d30b550afc40, 0x8b8e2c0d74eaf4cd, 0x8d0db9218c00aeec, 0x962dcf1a9381c130, 0xa7d696789e168fcc, 0xb5995c50afb97cc2, 0xc255e16ab6b972c4, 0xd1c5b4d8cb08f96a, 0xdfbef7b5d1fbd4d4, 0xe35d7659e1cd95ee, 0xe6f361f4e37b7646, 0xfad2835af242e4ea, 0xfd9886d0])
  | 4, 0 => (packedWords [0x31c322102f061ff, 0x46868080383b922, 0x77df7f1061b9715, 0xa0f0d8b09d8ed8f, 0xae47c230a5dcd52, 0xedeefba0c76adc6, 0xf9f6ff50f150fb6, 0x11ff89cb0fbf0897, 0x16d0b4c8151c4485, 0x17d2306c1754c23d, 0x1b8eaefd19e0cea5, 0x1c6d131a1c56d142, 0x1d68ec4e1d582eb1, 0x1f477f7f1f069aab, 0x2076b13b201b522f, 0x209be0022094b128, 0x2255cfd520f8e608, 0x240c9cd6231dbcfa, 0x27910ff225c5a0ad, 0x297d9b2b285bf598, 0x2a561da12a009fd5, 0x2b1c20812b0ae078, 0x2d7d88102beadf78, 0x2f7ed4292f5c1fcc, 0x32f16b8932e5bc11, 0x34379be533e67242, 0x36e8cf1736e68360, 0x37ebbe3c370a278f, 0x39e446f339ae26f7, 0x3ab1c1b23a96e19f, 0x409bbb3f3d5de29a, 0x446d9b6543183700])
  | 4, 1 => (packedWords [0x44fca703448df9a2, 0x467742484645dc02, 0x470d857c46d9981c, 0x48eae5bf4719e33c, 0x4a816c8749739d90, 0x4b213edc4b034afd, 0x4edbd4134db230be, 0x55f88c8c5580a6ee, 0x597865db59152905, 0x5b0fed515a2b5709, 0x60c14a8d602c07a6, 0x65c74cb862baf579, 0x669487f565f7596e, 0x670bbb0f66b54679, 0x696c20026826b07c, 0x6aa2b3f969aa9c7b, 0x6c9a53376c4ad497, 0x7065cfa56ec75058, 0x7442d4cd7150d6c2, 0x74b9fff1748ff64d, 0x7827c26a7798c973, 0x79190dd278355e1a, 0x7a5f56cd7933f048, 0x7f30e7627a974cfd, 0x801afe0e7fd83bb5, 0x828973ea81c03297, 0x84bdd07784a297dc, 0x84f6f66a84de3de0, 0x86a0d8d6857a66c7, 0x87ac163a871f139d, 0x8a93413989eadd7d, 0x91a672c68b4e5e47])
  | 4, 2 => (packedWords [0x93d6b6b0936f00bf, 0x95a1efab93f0bafc, 0x984784e996c37a20, 0x9a290cc0995e62c2, 0x9ba0222f9a5a3108, 0x9e00b6569c200dff, 0xa05327319fc5472f, 0xa0f3c35ca0ccfa75, 0xa18b651da12bfcf8, 0xa1d0860ea19a0bbd, 0xa2670770a1dcc3c5, 0xa794f111a6a00de8, 0xa9fe360ba9809e88, 0xac67283aaad9011c, 0xad0fc622acc0e499, 0xadbcf068ad7460e1, 0xb0b99058afad751d, 0xb3717eb6b0fccc17, 0xb4934f6fb37cff05, 0xb5230e5fb4cc2fd2, 0xb91b7134b599f6d5, 0xbb26a757b9564a82, 0xbe8ca4febd5a5dfa, 0xc3217d6dbeff306d, 0xc413e79ec3279c1b, 0xc71f0127c6f24925, 0xc8e3e804c8717f87, 0xcdf1ba1ac919e9c9, 0xce4107ccce282f9f, 0xd09afc0dcfa14aa6, 0xd34709f7d16f4525, 0xd4f05026d457ce31])
  | 4, 3 => (packedWords [0xdd7cdb96d59544f8, 0xdf5f6564de80a222, 0xe0113f8cdfe9cf2a, 0xe30bec28e280290d, 0xe484e99ee42d3fac, 0xe5bed9b1e4efd155, 0xe8fff6afe6fa48fc, 0xeb88d115eaaea153, 0xececf185eca19b6d, 0xedac9502ed372d47, 0xee68dc84edad69fb, 0xef192d4beeccab76, 0xf3e716c7f0caffe8, 0xf4c00a20f3e92106, 0xf583bbeaf564b406, 0xf62a824df589fb5f, 0xfa26b12ef9eecb83, 0xfc8f3799fa3db81e, 0xfe164134fdbcbd8f, 0xff6f1c47fefc8c29])
  | 5, 0 => (packedWords [0x3ab84f0006b217, 0x5eac09003cd213, 0x11b1bb30099b033, 0x127caec011b41f8, 0x19b2dc8013e9a3e, 0x3212db202117edf, 0x415b79f036a6835, 0x60b046705ba26cb, 0x83ee41e0768f64c, 0x85eb99008467e21, 0x8ced43e08b56c94, 0x8f2bc5a08dc357b, 0xad1e2d509866d30, 0xae07fbb0ad726ee, 0xb39920b0aefbf08, 0xcf4e6b40c6b06e8, 0xdabd47b0d00e76f, 0xf6a2c690de6f949, 0xf8cd1090f7d6330, 0x1044f77a0fb3a21c, 0x10aa5015106906f8, 0x1171091310b47494, 0x11e68b5d119e7398, 0x12b0309e1290395f, 0x12f45a5412c1733b, 0x1399eaaf12fddd88, 0x13ed8b6113cb18c5, 0x14e206a81466f9d4, 0x15345f33150cb520, 0x15e8d6a5155cd300, 0x1668c275161ff4d8, 0x16d0b4c8168a481a])
  | 5, 1 => (packedWords [0x184ed50f176c36e1, 0x18a202771856c698, 0x18e53e3618e50c22, 0x19f98c7819cac419, 0x1a5c1b9e1a00e415, 0x1b6571241a924fe4, 0x1c25ec681b96e11b, 0x1c43e2de1c407863, 0x1c9255071c6e0753, 0x1d0b807e1c982255, 0x1dd212681d2b5a3d, 0x1e8767921e077bc2, 0x1ef735901ef2500f, 0x1ffaaa6b1f8adbfe, 0x202f782120201246, 0x2103e3532083e229, 0x219e248021467a8e, 0x2334d422230f1976, 0x234757b9233c26be, 0x23da3cc323aafd3a, 0x24b4d42423f89b5c, 0x25c5a0ad24c2ca2d, 0x267c153b2675171d, 0x26e7a28c26dcdd98, 0x27d3ec0027587a98, 0x28de389f289ffca0, 0x29bad64f29138099, 0x29f6299329d2a52f, 0x2b09ef8c2ab47fdb, 0x2b8217662b808587, 0x2cb916842bd9840f, 0x2d4ca77e2cd342d7])
  | 5, 2 => (packedWords [0x2dba332c2d96f4a1, 0x2e3a3a852df12883, 0x2f14e4482ef87135, 0x2f771fb52f171cf1, 0x30919f9a300c65f4, 0x3214ceb031d94502, 0x329cf6cc3239e9e5, 0x330609c432b3fd5d, 0x333960db330e1b5b, 0x350d410434379be5, 0x35d8d84935759f2c, 0x3733896535ef55d5, 0x37c81518373fec10, 0x3840cc3d3822698b, 0x38d8bd72387c7b39, 0x39c3c48f3943d8bf, 0x3a9b5fed3a47f42b, 0x3ab6f3c43a9deeac, 0x3b4a0c133b039ab1, 0x3c474bd53c404050, 0x3c7ba0ba3c60a30a, 0x3cdd098b3cc581ab, 0x3d7050913d062420, 0x3e2ecfc73df5abe7, 0x3ec841813e738e7c, 0x3f2cc35a3eeeea89, 0x40099cdc3f9130a3, 0x404be9be400bb740, 0x409bbb3f409ab037, 0x4181a2e54130d6e3, 0x4271060442657c2a, 0x42f5cd6c42d7929b])
  | 5, 3 => (packedWords [0x43e305c14334d1f2, 0x4489e678445dbfca, 0x44b115ec449732ce, 0x458c5f5544fff213, 0x46d3df1e4694f392, 0x4777082f472d36cb, 0x487994af48474b51, 0x4afc61b74a12c27d, 0x4b3747264b25117f, 0x4c15b1cb4bb7f99b, 0x4c37afae4c2c35f2, 0x4c6d5bbd4c3c842c, 0x4dc7bd584d512bad, 0x4ee3ed7a4ded5494, 0x4f18c4a84f13c6a3, 0x4f9d98404f67faef, 0x511535465067a198, 0x521afbef517f18b6, 0x53a1c8f752fdbcaf, 0x53d69eb853ab7c91, 0x5436290753e9efa5, 0x545f71ef545a3885, 0x54804bcc546a09f4, 0x556b6763548a0d8c, 0x56514ea35636f646, 0x57bc4a5257100e27, 0x58b8765f57c5900c, 0x590c1eba58d33835, 0x59841c2d59700c1f, 0x5a59f40259d4257a, 0x5bdf5b9d5bac5362, 0x5ca87c3f5c8e71c6])
  | 5, 4 => (packedWords [0x5d6c2e095cd66fc3, 0x5e1220e55db51adf, 0x5eec58da5e2289d0, 0x5fa7896e5fa448a4, 0x6190d3dd5fb7e4b3, 0x6213d887620f234d, 0x6278991f622a11a2, 0x62cd1ed56278e121, 0x63527f9d63049365, 0x63e3339e63d8fb83, 0x63fe182a63f802e9, 0x64f514e064aa4acf, 0x65c3d1a3657011d6, 0x665bd6876613f48c, 0x674684c2673bb0bf, 0x67920cdb676405d6, 0x67e9cce967d689d0, 0x69041a55681eb1cd, 0x6a6648aa6a4fb192, 0x6ad8d4196a97863e, 0x6b3793af6ad9f53d, 0x6c50da226c4ad497, 0x6c980f066c733bff, 0x6e04092f6d399208, 0x6e31d57c6e245602, 0x6f12fbb56eb4ce36, 0x6f666a0b6f6529df, 0x6fad687c6f989e0c, 0x707336c3703d19aa, 0x70b32117709135d5, 0x715e90a87150d6c2, 0x72463f6c72054e71])
  | 5, 5 => (packedWords [0x738999fd72c08333, 0x73b75535738ae37f, 0x7428d9f57400eec5, 0x744b2582743f8ba9, 0x74866c947482d127, 0x7524757f74e989d1, 0x7606003d75ee6a53, 0x76a52eea76507a99, 0x776dce6f76d7ec0f, 0x77cc0d9977808643, 0x785ef5aa78057205, 0x7891dbe0786aa0e7, 0x79ce1bf5790a7089, 0x79e942da79e7fbe5, 0x7bb946a57b63063a, 0x7bf7ef597bbcbf51, 0x7c55db6f7c3cab21, 0x7cc2cd877c9389aa, 0x7db4f61c7d0fdfb5, 0x7e0e84b87dd18cdd, 0x7e5c63427e5914b4, 0x7eecd0ce7eb926e2, 0x7f9502a77ef6912c, 0x803171dd8006c1f3, 0x807d9ac7804dd4b4, 0x8178ff358080e835, 0x81fa9b62819ab231, 0x821a41c18215e1e0, 0x82b067ff82453538, 0x8312e6cd82b9730e, 0x83d33277835f16df, 0x843f435c84090c01])
  | 5, 6 => (packedWords [0x84a8445f84a297dc, 0x85cd4bc785954aec, 0x87ac929f8661215e, 0x884cbe9387b3371f, 0x88e15822888cb9b8, 0x895fd3c38922b346, 0x8a07bd0889e82466, 0x8a86251f8a159f8d, 0x8ac510ab8ab6d196, 0x8d839d5a8c95f634, 0x8dc0e6e38d8a3b1b, 0x8e75b1af8e1722b8, 0x8f64f8f68f2878b3, 0x8f6e30918f6536f2, 0x8f947b878f79820c, 0x8fd0ba458fca123f, 0x9078ecae8ffd2b1d, 0x912861b79091afd9, 0x918cd7969156d5d1, 0x91d2896691a672c6, 0x922662259206c983, 0x938e1bd8928baccc, 0x956f508993ce38dd, 0x9689fe04962e63e2, 0x974ce61b96fe0699, 0x97839e1397674643, 0x9819934e97c7d045, 0x983f40589834f5dc, 0x99fe6c9f984784e9, 0x9a32ee299a2827d3, 0x9bb48a179b03d58a, 0x9c200dff9bb9f7c4])
  | 5, 7 => (packedWords [0x9e0a92209c86590a, 0x9f8618849ec87f2b, 0xa0425affa039e92e, 0xa125600ba0df010c, 0xa1bdd52da1984950, 0xa2df6f50a2b5ecab, 0xa3795c14a3737005, 0xa400aca7a3ce8156, 0xa501046aa4aba443, 0xa59430a1a50c970a, 0xa7d603b5a6577091, 0xa8842d59a7f6b7f8, 0xaaa975fca9d63ff3, 0xab7d00e7ab00a91a, 0xabc7bb5dab7ed9f5, 0xac65d975ac003db3, 0xaca32effac982387, 0xace5191daca5ad17, 0xad3a1ffaad2b3c27, 0xad62bf22ad432680, 0xaf61e899ae2e4e1c, 0xaf6d36c9af65395d, 0xb08d3535b031b5b5, 0xb12ac395b09a8138, 0xb18be247b172e47c, 0xb23f8f64b1a9312a, 0xb29c6ff1b272fd76, 0xb3f6db68b36a89f0, 0xb4826762b42cfb64, 0xb558c517b4b57765, 0xb67259ecb6420c01, 0xb74afc5fb7442014])
  | 5, 8 => (packedWords [0xb915554db82d297b, 0xb94ebfd9b91b7134, 0xbadb04c3ba41ac26, 0xbc4ba081bc158085, 0xbd29ea21bcd10929, 0xbeab7ad8be70a8d4, 0xbf631045beff306d, 0xbfd9d0c6bfa676cd, 0xc0fd9b1fc02ddcae, 0xc19aaa1fc15639ed, 0xc1d70b54c1c2be6a, 0xc266f675c24d4977, 0xc2e46114c2a679eb, 0xc36196f9c2e6b9bf, 0xc46ecc54c45d72f2, 0xc54bff6ec4d4556d, 0xc58bcd5fc57f908e, 0xc6685131c65a083d, 0xc75600a9c6da1d43, 0xc7ac7c16c76f79f6, 0xc7c46404c7aed749, 0xc8679924c7d2cc49, 0xc9248884c8e3e804, 0xc9ccbd05c9b9ab78, 0xcaaf149dca7dd815, 0xcb634fc7caf75454, 0xcbf6a6eacbe9ef62, 0xcc3df020cc03f3ae, 0xcd197d0fcc7c13cd, 0xcdbe3a41cdad4206, 0xce9db893cdcb41f3, 0xd04140fdcffebd16])
  | 5, 9 => (packedWords [0xd0eff18dd08727c1, 0xd1432da1d109f5d9, 0xd1ef5f7fd161d95d, 0xd26cb931d23c4572, 0xd3c1ebd2d3c11a4c, 0xd3de99cbd3cb5f05, 0xd4740b7ad405be28, 0xd548075ed4f05026, 0xd61793b2d5562e0b, 0xd66aea0cd6471f6f, 0xd751dd82d742479d, 0xd7a5af89d787fd7e, 0xd85fe61ad852b14c, 0xd906fc0ed8e03327, 0xd9f86ea7d9bdf491, 0xda6020c1da0b84c4, 0xdc12c4c7dbb95a3e, 0xdc92b097dc786867, 0xdd03a9eadcabd4bb, 0xdd980968dd7a4b6a, 0xde0cfe39dde63552, 0xde2959acde17f538, 0xdf257719de32de56, 0xe0113f8cdfafdef1, 0xe1546f80e047e9a3, 0xe3b4d473e2ec39ce, 0xe51f2c76e41b0c9d, 0xe5879993e5224f07, 0xe63fe524e63adab3, 0xe691a371e67c9aa8, 0xe7e8527de6d0a0dd, 0xe8ccc90ae81080a1])
  | 5, 10 => (packedWords [0xe91004c9e9079ef0, 0xea8d9bbeea33a443, 0xeb3316a7eb05577c, 0xeb4767e8eb45caf0, 0xeb90aac2eb9037b7, 0xec755ee6ec19ddbe, 0xeca64291ec7f8a9e, 0xed364711ecd4935c, 0xedd2cb35ed72a67b, 0xee70cdcfee1606f4, 0xee8b893eee864c52, 0xefdba5b4efbc0d12, 0xf096dea4f09639e2, 0xf12ea9e6f0cee360, 0xf1c77fa6f171b468, 0xf27bb353f23c493c, 0xf336d061f316e66b, 0xf4082809f339e009, 0xf47e66c2f41f721b, 0xf595a3adf4e0016e, 0xf62a428bf60786ca, 0xf6642f03f634ac11, 0xf71174e6f6aa2e5b, 0xf7722d0af712691f, 0xf7cf0d94f7b7fd52, 0xf83fe234f7f901fd, 0xf914f28ef87b0b11, 0xfad9b816f977aecf, 0xfba5dfdbfb34b61f, 0xfbbcc7bffbb8c8b6, 0xfbd92d16fbbf28ca, 0xfd9e6b8cfc186b4a])
  | 5, 11 => (packedWords [0xfe744a98fe62fc8d, 0xff3239d9feb38432])
  | 6, 0 => (packedWords [0x1b08f90006e202, 0x2a0955002636ea, 0xb3ba0a00344d7f, 0x120807500c059d5, 0x19b2dc80123f477, 0x298cb7001a48dea, 0x32bb698032a0c98, 0x4bea4f60359706d, 0x558553605386f78, 0x6a69cef05cd4d96, 0x76ca63e075c4d5e, 0x87c8aa907a7fa5e, 0x8bed78b08b707cb, 0x8f7216a08da2eca, 0x9be25b909679600, 0x9f490b209c23682, 0xb268cae0aebabaf, 0xb68bb390b48b1b5, 0xcde1a3e0ba7bfbf, 0xd3093e70d0a209b, 0xfe9f5fc0eeacd12, 0x103b24350ffe0bd3, 0x106906f81044f77a, 0x11affab91075d919, 0x12269abf11e0db9f, 0x1290395f126e3ceb, 0x1392675712c5e6dd, 0x13cd66d813b15752, 0x14506b82144bcaba, 0x1512546414b48f99, 0x1668c275163aab25, 0x18049ff5178bb275])
  | 6, 1 => (packedWords [0x19ce9fd618e53e36, 0x1a8b0f751a315843, 0x1b70aa7c1ae298ac, 0x1ca9d9c31c5cdd72, 0x1cb4c8e41caa4a66, 0x1df66bb41cce5e10, 0x1e8767921e077bc2, 0x1f82fbf41ed618d3, 0x201933d42001825c, 0x206d79382040833c, 0x216ca5f02103e353, 0x2301075f21e2f9ec, 0x23f89b5c23c4b929, 0x25495d90241f412f, 0x25b8ce1225782111, 0x25f8d5ad25da88d1, 0x26850eb22629d2ee, 0x272dcd932695779d, 0x27d931d827593412, 0x287702922867ae6d, 0x28d1a801288625a9, 0x292617202914a5f0, 0x2a177a0c29ca1a7a, 0x2aef67e62aeb86ec, 0x2b7781322b575a25, 0x2c89f8df2c324eed, 0x2d6802ad2d1d389c, 0x2dc3e8f22da4bd7b, 0x2ecec4542eba7a26, 0x2f4c72b02f1d6e44, 0x30919f9a303c5e47, 0x31315f393095a7af])
  | 6, 2 => (packedWords [0x31d9ac7731770822, 0x32a965423214ceb0, 0x32f3400532b3fd5d, 0x338c1a14336ad473, 0x34a6aaae345c944f, 0x35858227350afcd3, 0x35d8d84935bef52b, 0x366debc536104906, 0x36f3c51036a10fac, 0x3756d2ca3700fa24, 0x37f2d0b437c81518, 0x389eca8c382c5b88, 0x39c3c48f38e9e76c, 0x3b9103a63b464f95, 0x3d88cb2b3cc51961, 0x3e7d38163e24b053, 0x3fe6f85a3ec84181, 0x404087053fed5d86, 0x420c78454097e8db, 0x42c75292422bc06f, 0x4511b2024364f4b2, 0x467226684627e3e9, 0x46d3df1e469de367, 0x481dbc6e46f1413c, 0x48e66d094831fcc2, 0x4a88cfad496dedd2, 0x4ab28b104a97ce7c, 0x4b2ad00f4af5713b, 0x4bd204ac4b92bfda, 0x4c6d77444c02b69d, 0x4e6b38cf4e20a651, 0x4ee3ed7a4edcdd3c])
  | 6, 3 => (packedWords [0x4f39e3424f220ba9, 0x501f806c4f83072d, 0x5105122650cf4bcb, 0x52120acb51de7683, 0x52767c295262dc8e, 0x543c739753d69eb8, 0x547bbd02545b9e76, 0x54e17c9a54a8d537, 0x5516eb0354f27fa6, 0x555dcc19553a9ca9, 0x55d20d2c55cf7598, 0x56c11cdd5636f646, 0x587018ea58323918, 0x594631c958b1fcd6, 0x5a59f4025a049907, 0x5c8984dd5b6011be, 0x5d4863f85cc77a54, 0x5dbfd1635db4197f, 0x5ea151af5dca599d, 0x5edfc1fa5ed5c404, 0x5f1822b35f136ca3, 0x5f70f4665f59d179, 0x5fe435295f762034, 0x6278991f615c8238, 0x62cfab1862c04b34, 0x645be07e62e65362, 0x64c94dc7647c58b9, 0x65aa5123655d3ded, 0x66a753f666279940, 0x66eef70766cec5b2, 0x67d689d06774fa7d, 0x68fdf54467e9cce9])
  | 6, 4 => (packedWords [0x6a36e5246963e209, 0x6b891a446b878d6e, 0x6c416f236c14ddc1, 0x6c65e0d56c4ad497, 0x6c9afdd66c91d409, 0x6d2b83b36cc467c9, 0x6dbb4c076d7f84d7, 0x6f0d9c246edcb879, 0x6fe6f35c6f961f2e, 0x7048f1827022260f, 0x7089ab81706d3a45, 0x7150d6c2709135d5, 0x719403c27182aa67, 0x7205af1171e891c7, 0x73c06345733da43d, 0x73efeeb473d5636f, 0x747296ee743aa92a, 0x74e30ce67486d93c, 0x759e29f4751c85d4, 0x7621e18c7607dd40, 0x769a01ab76507a99, 0x772640a6769b0e1d, 0x77efefa27783e365, 0x79df43077891dbe0, 0x7a1c1ef779ffdf0c, 0x7ad7f2c47ab27d31, 0x7bdf08627ba632a0, 0x7c3cab217bf63e73, 0x7ce3562f7c5a3350, 0x7d3deb7f7cf8921d, 0x7db4f61c7d9e1011, 0x7e26825d7df8c7e2])
  | 6, 5 => (packedWords [0x7eb8a6c87e4086a9, 0x7ef6912c7ec813a6, 0x7f5db1337f583b93, 0x807d9ac780681958, 0x80fc409e80abc542, 0x83064e5582fe2105, 0x834ad58b8324e9ec, 0x8478d86d83d33277, 0x867311d08646bbb1, 0x86800840867f0317, 0x87c63b188756263f, 0x87f5a12f87eac54d, 0x886204a3884cbe93, 0x89b24ee488c19fcb, 0x8a7e67e98a49f921, 0x8b438f098b1cc622, 0x8b6afd9e8b574ee1, 0x8bcd7b928bb0cc13, 0x8d01b63f8bea0d46, 0x8d0a27ac8d04e085, 0x8e4aeb3e8d5013ed, 0x8ec3e2a88eafae45, 0x8fd0ba458fa58771, 0x902ebf6b901f69e3, 0x9156d5d190da86f1, 0x9206c98391805454, 0x92eab6e892266225, 0x93716b83932df2a7, 0x94f643b394bb6767, 0x954cdc479528ccc9, 0x95fae23295ae2595, 0x9650944995ffb246])
  | 6, 6 => (packedWords [0x96ce536296684787, 0x974440be971b655f, 0x97740eae975434ef, 0x97d0f39097c42c8e, 0x9962df5a99506e8e, 0x997ce3a6996a5bbf, 0x9b095c0599f503c5, 0x9b4c97c49b31c7ad, 0x9d57cde79c200dff, 0x9dc913859d900c2a, 0x9defeb3c9dcccab2, 0x9e62b6389df585b5, 0x9ee2ca3c9e675c4c, 0x9fb5356a9f72da0c, 0xa03b4f1e9fe927fd, 0xa13056fda11a3841, 0xa2d0f387a2cc347d, 0xa36b3ce1a30ee069, 0xa51192b5a4843c8f, 0xa5767304a552a3fd, 0xa5aeb147a5a1d00c, 0xa67fec06a659231f, 0xa8842d59a691c2db, 0xa8dc70aba8cf104a, 0xa8eec12aa8df3204, 0xaa13efa3a94efc1a, 0xaae0c85caab644ec, 0xad2b3c27acb7c119, 0xae82bf0ead71491a, 0xaeba55b5aeadc880, 0xaf78befbaf3a87f3, 0xafda2d82afd33d35])
  | 6, 7 => (packedWords [0xb126a8a3b02bbfb8, 0xb14c486ab130c286, 0xb2a7c335b272fd76, 0xb300898bb2fecdb1, 0xb57574e9b42c86aa, 0xb645b902b585354f, 0xb797d2acb688f4c1, 0xb8f15318b8d43e73, 0xb98f5b81b90927af, 0xbb21668fbaaf3709, 0xbbaae5f5bb4a35f4, 0xbc158085bbbcb701, 0xbc92c540bc4ba081, 0xbcabea67bc950589, 0xbe505926bd6b8d63, 0xbea799debe93aa10, 0xbf48a684bee2e5d6, 0xbfafd6efbf9ba30a, 0xc0a06cd1c02ddcae, 0xc187ec3bc0b2d001, 0xc2251098c217b3ea, 0xc23440d2c231b836, 0xc3947b8ec2a9d855, 0xc466f9acc3ac16d0, 0xc653cf53c5c36b6f, 0xc6b6102ec65e663c, 0xc7301d43c70790c9, 0xc7fbdeaac7674ba1, 0xc8ada617c86a09fa, 0xc974df0ac8df2e3e, 0xcbb8cca4cbb7b46d, 0xcc1d619bcbdd55fd])
  | 6, 8 => (packedWords [0xcc88a567cc382a84, 0xcd13a1a7ccc2dfb3, 0xce7d0b59cd71a01f, 0xced4b54bced2c1fd, 0xcf34c096cf0df7af, 0xd055abaad00ea55e, 0xd09a0314d0568a36, 0xd0fdf9f0d0b1d1e6, 0xd2985075d1432da1, 0xd3536d83d3012ad0, 0xd3ffe075d3c7c2c9, 0xd6c09d7ed45e9b5a, 0xd6f1671ad6f130b0, 0xd7a5af89d775078f, 0xd804fc37d7b4e27a, 0xd9944bf1d8b8a831, 0xd9c236ccd9ab8202, 0xdae6b22fd9e3f6db, 0xdb1d4838db1acb95, 0xdbb55e1bdb1fcfed, 0xdbf5ca38dbdbc5ec, 0xdc28d856dc104798, 0xdc6dea57dc57d7be, 0xdce34040dc92b097, 0xdd279bb6dd2601b8, 0xdd6b5ec4dd41a01b, 0xddfb7a0ddd6fedb6, 0xdefa8d92de9a68d8, 0xdf27d062df0fd5cd, 0xdfd38797df3dc951, 0xe0fc3a56e00c8614, 0xe1bdfc3fe14ad8d1])
  | 6, 9 => (packedWords [0xe26c7a40e22e1bfc, 0xe3640b99e2f8d509, 0xe49bc6cce4767cdb, 0xe521888ae4c740b4, 0xe54e0357e5224f07, 0xe5e1f55de5abd561, 0xe6998e93e5f36d9b, 0xe6e8da34e6bd660a, 0xe7b72882e702263b, 0xe82b2b31e80981e1, 0xe86d9833e84cbda0, 0xe8f8d298e8d209b1, 0xe997096be967a491, 0xe9b96856e9af1e7c, 0xea111248e9fc1276, 0xeb8befbceaabc9b1, 0xeccda238ec8ef3dd, 0xed402da7ed285b15, 0xedc20e6aedba8741, 0xeeb833b0edfd3bce, 0xf036472beec59542, 0xf0c8ca4ff06b62bd, 0xf1627aa7f12ea9e6, 0xf1b738c9f1945095, 0xf22dc417f1cdc399, 0xf2b16171f23cf162, 0xf2d90bb9f2d67b84, 0xf3f5052ef357d40e, 0xf44f9aabf430b056, 0xf53d79f7f4ad98fa, 0xf579701df5750b24, 0xf6aa2e5bf634ac11])
  | 6, 10 => (packedWords [0xf712691ff6c6796e, 0xf860fcd5f7f62419, 0xf901db53f8be9f94, 0xf9d2664ef914f28e, 0xfb0fe494fa4c32ca, 0xfb3a9b3bfb180e11, 0xfb820e41fb78f78c, 0xfc4f5573fc186b4a, 0xfd96067cfd281d9b, 0xfe87f7cdfdc27e0a, 0xffb2d9d8])
  | 7, 0 => (packedWords [0x6a69cef01208075, 0x11e0db9f0b48b1b5, 0x19ce9fd61668c275, 0x2f4c72b01e876792, 0x39c3c48f3095a7af, 0x510512264364f4b2, 0x6278991f5edfc1fa, 0x6f0d9c246b878d6e, 0x759e29f474e30ce6, 0x7c3cab217bdf0862, 0x7e4086a97e26825d, 0x8478d86d7eb8a6c8, 0x8b438f098b1cc622, 0x9b095c0597c42c8e, 0x9dcccab29b4c97c4, 0xa57673049f72da0c, 0xbea799dead71491a, 0xced4b54bce7d0b59, 0xd8b8a831d6f1671a, 0xdfd38797df0fd5cd, 0xed402da7e4767cdb, 0xf06b62bdeeb833b0, 0xf4ad98faf1cdc399, 0xfc4f5573])
  | 8, 0 => 0x1e876792
  | _, _ => 0

private def packedBlocks : Nat → Nat → Nat
  | 3, 0 => (packedWords [0xc6547d5d120c654, 0x85d124c654771d12, 0xc794785d120c6047, 0x5d120c644849b820, 0x834785d120c65478, 0xd120c624801b85f8, 0x54785d12dc834785, 0x122c65487de17446, 0x4785d020c654785d, 0x20c644785d130c65, 0x7f9d120c654781d2, 0xc444785d15ac834, 0x85d1204654749a62, 0x4834849d120c6547, 0x1d120c4447f1e174, 0x434779d120c65480, 0xd15a4834885d1194, 0x54785d1208654785, 0x120c654785d16146, 0x47b9d120c654809d, 0x2544647b5d120c65, 0x881d120c654785d1])
  | 3, 1 => (packedWords [0xc794781d120c654, 0x85d1238654785d12, 0x834785d120c7247, 0x785d125])
  | 4, 0 => (packedWords [0x955e1749d120c655, 0xc655785854b4a61, 0x8831955e1749bb2, 0x44c420c655785d13, 0x85d120c650555e17, 0x56024b4a620c6557, 0xc6557b92d2988319, 0xca6195616785d120, 0x4831944e57853830, 0x9d26f4831955e174, 0x5ee749bd20c65580, 0x445785c06e083195, 0x831956006e13f20c, 0x3f20c6d5885e1744, 0xd1640831955e16e1, 0xe17448320c655785, 0x657b52d298831955, 0x31955e14b4a62544, 0x920c6557812d2988, 0x12e8831955e1744b, 0x17459420c655785d, 0x578532298831955e, 0x1955e14b4a620c79, 0x20c655785884fca6, 0x6f4831955e16fca6, 0x749bd20c655881d2, 0x785d120c650f55e0])
  | 4, 1 => (packedWords [0x955e17449620c655, 0xc65580db84fc831, 0xf4831e55e1749ba2, 0x44a620c655785d26, 0x85d120c650495e15, 0x55e1749a120c6557, 0x42b5785d165c8319, 0x88e1955e17448319, 0x831943257852d29, 0xdd26f4831955e16e, 0x636785d120c6557f, 0x6557853029883195, 0x650fd1e1749bd238, 0xa620c725001d120c, 0xb86153f1955e14b4, 0xe04f8a620c655785, 0x55001e1744831951, 0x31956123a0b120c6, 0x220c655785262988, 0x26f4831c95e14b4a, 0x26e13f20c655785d, 0x57b9b84fc8319560, 0x20d5e1538a620c65, 0x20c645785d26f494, 0x298831955e04fca6, 0x745b820c655785d1, 0x7d52d298831955e1])
  | 4, 2 => (packedWords [0x3d62f785d220c655, 0x94445785d120c650, 0x74831955e1744831, 0x44d020c655785d16, 0x85b8490831955e17, 0xd60f785d220c6557, 0xc655785b84fc831c, 0x4831695f5749bd20, 0x831e4345785d26f, 0x5d1544831955e16e, 0x5e14b4ad20c65578, 0x445785b84fc831e5, 0x3f20d5a64fca620c, 0x831943f5785b85a1, 0xb820c650e55e1744, 0xe16e13f238655785, 0x8577dd26f4831955, 0x31915e1744831940, 0xf20c7257852d2988, 0x26f4831915e16e13, 0x1745d120c655785d, 0x57f5e1749bd20d5e, 0x1955e17459220c65, 0x20c655785b82c483, 0x20c650cd5e17455b, 0x785d120c655785b8, 0x891e174483195614])
  | 4, 3 => (packedWords [0x955e14b4a620c655, 0xc655785d3748831, 0xd8831955e16e12d2, 0x49bd20c655785d26, 0xd5b84fc831955e17, 0x55e1744831941a57, 0xc655771b84fc8319, 0x8831955e1749aa20, 0x8a620c6558d9e074, 0x53e298831915e152, 0x6207490932865578, 0x365785b84fc93195, 0x650615e16e083194, 0xb7298835785d120c, 0xb84fc831815e14b4, 0x4fd092ec835785, 0x55785d2690831956, 0x31955e14f8a620c6, 0xd2dc835785d15bc8, 0xd2988b1955e1749b, 0x1749b420c6557852, 0x5831e1748831955e, 0x1e55e16e13e20c65, 0x20c655784e82c483, 0x744831955e1744b1, 0x744ca20c655819e1, 0x785d14b4831955e1])
  | 4, 4 => (packedWords [0x955e174909328945, 0xc655785d1694831, 0xfc831655e1745832, 0xcca620c655785b84, 0x85b820c650d15e14, 0x55dd749bd20c6557, 0xc655785d13448319, 0x831955e1749a620, 0x13f20c655785b853, 0x5d26f48318d5e16e, 0x5e14d0a620c65578, 0x655848e8298831e5, 0x650a95e17457420c, 0x83194285785d120c, 0xb94fc831955e1744, 0xe14b4c3298655785, 0x55785b24fc831955, 0x319560a785d220c6, 0xd30c655845d26f48, 0x1744831955e1749b, 0x9785b84fc8358bde, 0x5785d14f8831955f, 0x1955e17458920c65, 0x1944247e1b84fc83, 0x4fc8319540078483, 0x744831942057b1b8, 0x8017b424a620d5e1])
  | 4, 5 => (packedWords [0x951e16e13f2dc835, 0xc655001e1745a51, 0x1c831955e1744e82, 0x4483194195785b85, 0x7de16e13f1955e17, 0x55e16e13f22c6558, 0xc655801e17448319, 0x4831955e14b4b120, 0x8e8298835785d142, 0x5d120c650d16005f, 0x636785d220c64578, 0x655785d140483195, 0x831955e17453f20c, 0xb820c655785d1524, 0x6b4b4a620d5e1711, 0xda749bd20c655785, 0x55785d1604831955, 0x31955e16cd3f20c6, 0xd5ac8358d9e17488, 0xe2c4831955e1749b, 0x16bd2d20c6557853, 0x58492d298831955e, 0x1955e174dd120c65, 0x30c655785d26f481, 0x6f4831955e16e13f, 0x745bd20c655849d2, 0x784e82c4831955e1])
  | 4, 6 => (packedWords [0x955e14e0a620c655, 0x94425785b85f8831, 0xf4831855e1744831, 0xb4a620c445785d26, 0x85d26e0831956004, 0x55e1404b120c6557, 0xc655785d268c8319, 0xc6510d5e1745c620, 0x9bd20c445785d120, 0x5d12688319560074, 0x5e17490932465578, 0x655785d26f083195, 0x8e195633785d120c, 0xd320c65578530298, 0x2a298831955e1744, 0xe16f93f20c655785, 0x558852d2986510d5, 0x620d1e14a0a620c6, 0xd298835001e1745c, 0x32c4831955e15a52, 0x17453520c6557851, 0x57852b298831955e, 0x1195e16e16b4fc83, 0x20c655785d120c65, 0x744831955ea6e13f, 0x785d120c6557cde1, 0x785b855083195631])
  | 4, 7 => (packedWords [0x955d86e13f20c655, 0x94345785d1254831, 0x9c831956126e0831, 0xe0831943d5785b84, 0x49b84fc831955e16, 0x55e1749a820c6558, 0x785d26f48219])
  | 5, 0 => (packedWords [0x809d2424a620c656, 0x785d26f54920c656, 0x7b9d2424a620c656, 0x785bd4fca620c726, 0x785ae4fd0920c656, 0x785d254ca620c656, 0x7854c460a620c656, 0x7853f3b8a620c656, 0x7853c424a620c656, 0x7853f460a620c656, 0x785b84fcd120c656, 0x78544424a620c656, 0x785d2424a120c656, 0x785d4749bd20c656, 0x7857a4fca620c656, 0x785714fca620c656, 0x7853f424a720c656, 0x785d26f51320c656, 0x77d3f424a620c656, 0x78590544a620c656, 0x785b85d13f20c656, 0x785964fca620c656, 0x785b84fc831942a6, 0x7853f4d4a620c796, 0x7853e424a620c656, 0x7853f424a621c656, 0x78d3f424a620c656, 0x785d2640ca20c656, 0x885e16253f298656, 0x7853f484a620c656, 0x785bd4b4a620c656, 0x785a24fcc3298656])
  | 5, 1 => (packedWords [0x8bde14fca620c656, 0x7853f424a6244836, 0x785904c4a620c656, 0x7853f4f8a620c656, 0x8bde16e13f20c656, 0x83de14fca620c656, 0x7853f390a620c656, 0x785894fca620c656, 0x7853f3f4a620c656, 0x7653f424a620c656, 0x785cc424a620c656, 0x785d26f5bd20c656, 0x881d2424a620c656, 0x7d5bd4fca620c656, 0x784e829883194346, 0x7853f3e0a620c656, 0x785b86253f20c656, 0x785bd4fca620c5a6, 0x7853f424a620c646, 0x7893f424a620c656, 0x7f5e14fd09298836, 0x76d3f424a620c656, 0x785b84fc83194146, 0x7853f410a620c656, 0x785b83a083194346, 0x785d2424a620c796, 0x785b84fc83194206, 0x7854c3a0a620c656, 0x80954424a620c656, 0x7853f3a0a620c656, 0x785d14b50920c656, 0x1e17459020c655])
  | 5, 2 => (packedWords [0x7853f3a0a520c656, 0x78559424a620c656, 0x7853b424a620c656, 0x1e16e1a54fc655, 0x785b866d3f20c656, 0x785b84fce820c656, 0x809904fca620c656, 0x841e1749bd20c656, 0x7b9904fca620c656, 0x785d258ca620c656, 0x7853f424b120c796, 0x785b84fc83194196, 0x785d2688a620c656, 0x785904e4a620c656, 0x785c64b4a620c656, 0x7fdd2424a620c656, 0x785d14fd2d20c656, 0x7853f424a820c656, 0x7852d29883194436, 0x801e16e13f20c656, 0x785b842483194346, 0x7852d2989a20c656, 0x7854c424a620c656, 0x7853f424a620c656, 0x785a04fca620c656, 0x7853f424b020c656, 0x7853f424a520c656, 0x8d9e1748ca20c656, 0x7850129883194346, 0x7853f424bb20c656, 0x785d2424a6238656, 0x785b84fd0920c656])
  | 5, 3 => (packedWords [0x785d2719bd20c656, 0x785d26f483194436, 0x785b84fc83194346, 0x785d1640a620c656, 0x7853f46ca620c656, 0x785b84fc83194016, 0x2024fd09328655, 0x7853f424a61f8656, 0x7853f404a620c656, 0x7852d34ca620c656, 0x785bd4f8a620c656, 0x1e1544a620c655, 0x785b84fd0120c656, 0x1e17192d298835, 0x1e16f483194415, 0x785b84fd3f20c656, 0x7b13f3a0a620c656, 0x7853f3c0a620c656, 0x7853f3a4a620c656, 0x785354b4a620c656, 0x785d2424a620c726, 0x785d26f4d320c656, 0x785904fca6254466, 0x7853f3a0b7298836, 0x7853f424a6200656, 0x785b85253f20c656, 0x781904fca620c656, 0x1e1749c66f4835, 0x785d2424a6250836, 0x7851329883194346, 0x7852d29883194466, 0x78543424a620c656])
  | 5, 4 => (packedWords [0x7cde14b4a620c656, 0x785473a0a620c656, 0x7853f430a620c656, 0x785bd4fca620c646, 0x785904fca620c796, 0x7853f3a0a622c656, 0x785c2640a620c656, 0x7b13f424a620c656, 0x7953f424a620c656, 0x7853f44ca620c656, 0x785d26f483194466, 0x7853f424b7298836, 0x7852d2989520c656, 0x7cde1749bd20c656, 0x7853f3d8a620c656, 0x785d26c50920c656, 0x785b84fd1320c656, 0x8493f424a620c796, 0x785d120c654, 0x785d34fca620c656, 0x7853f468a620c656, 0x78547424a620c656, 0x8013f424a620c526, 0x7853f424a622c656, 0x785d26f49520c656, 0x7853f470a620c656, 0x785543e4a620c656, 0x785d24249c20c656, 0x785524fca620c656, 0x785b64fca620c656, 0x785bd530a620c656, 0x785bd4fca620c656])
  | 5, 5 => (packedWords [0x785904fca6238656, 0x7d5d2424a620c656, 0x8693f424a620c656, 0x7853f3dca620c656, 0x785d24b4a620c656, 0x78547404a620c656, 0x785bd6e13f20c656, 0x7853f374a620c656, 0x7853f3aca620c656, 0x7852d308a620c656, 0x1d26f59f20c655, 0x785c5424a620c656, 0x785d23b0a620c656, 0x785c43a0a620c656, 0x785bd6c13f20c656, 0x7852d310a620c656, 0x7853f424a6210656, 0x7853f370a620c656, 0x7853f424a620c5e6, 0x78554424a620c726, 0x7852d29883194156, 0x785d2749bd20c656, 0x785aa4fca620c656, 0x785d2424ac20c656, 0x8d9e04fca620c656, 0x1e1744a620c655, 0x7853f3b4a620c656, 0x785d26f4c220c656, 0x785d2414a620c656, 0x859e14b4a620c656, 0x785904fca620c726, 0x785d2424aa20c656])
  | 5, 6 => (packedWords [0x785d26f4c420c656, 0x785d14fd0920c656, 0x785d26f59e20c656, 0x7852d298831944e6, 0x785d26f483194156, 0x1e16f54720c655, 0x785b84fc83194176, 0x785d2460a620c656, 0x7753f424a620c656, 0x785664fca620c656, 0x7853f47ca620c656, 0x859e1749bd20c656, 0x7853f434a620c656, 0x8013f424b6298836, 0x885e14b4a620c656, 0x785a44fca620c656, 0x785c0688a620c656, 0x7853f424a620c636, 0x7853f3a0c3298656, 0x785c66e13f20c656, 0x7857b424a620c656, 0x77dd2424a620c656, 0x8017e4fd09298836, 0x785b84fc83194436, 0x785bd4fcb7298836, 0x8d9e17490920c656, 0x785b44fca620c656, 0x785904b4a620c656, 0x831e14fca620c656, 0x885e1749bd20c656, 0x7852d2988320c656, 0x8453f424a620c656])
  | 5, 7 => (packedWords [0x8d53f424a620c446, 0x785bd51ca620c656, 0x7853f424c1298836, 0x785934fca620c656, 0x785d26f483194266, 0x7a13f424a620c656, 0x8d9e17493f20c656, 0x7853f424c3298656, 0x785d26f59020c656, 0x785d2624a620c656, 0x785d23f4a620c656, 0x7d5904fca620c656, 0x7852d2e4a620c656, 0x7852d2e8a620c656, 0x785b84fcd320c656, 0x785944b4a620c656, 0x7853f4d4a620c656, 0x1e1719b84fc835, 0x785d2424bc20c656, 0x7f5e174909298836, 0x7857e3a0a620c656, 0x7c5e16e13f20c656, 0x785d2410a620c656, 0x7852d2989620c656, 0x785d26f4b920c656, 0x785273b0a620c656, 0x785093a0b120c656, 0x785d23a0a620c656, 0x785d24249b20c656, 0x784e82c483194346, 0x7c1e14fca620c656, 0x785b84fc83194466])
  | 5, 8 => (packedWords [0x785d26e0e820c656, 0x7cde16e13f20c656, 0x785d26f4831943d6, 0x785d26f49620c656, 0x785d2424bd20c656, 0x7852e424a620c656, 0x7852d29883194126, 0x8c1e1749bd20c656, 0x7853f3a0b120c656, 0x785974b4a620c656, 0x785b84fc9520c656, 0x7852d298831942b6, 0x7853f424a6254786, 0x785d2424a620c656, 0x7853f3a0a920c656, 0x785a64fca620c656, 0x785d26f4831d0656, 0x7858e4fca620c656, 0x785764fca620c656, 0x7853f478a620c656, 0x7853f3cca620c656, 0x8d9e14b4a620c656, 0x785d26f483194126, 0x785d26e10920c656, 0x7853f418a620c656, 0x785b84fccf20c656, 0x7853f424a620c5d6, 0x785d26f59f20c656, 0x785904f8a620c656, 0x7853f3a0ab20c656, 0x7853f424c32dca66, 0x12d298831943f5])
  | 5, 9 => (packedWords [0x7853f424b120c656, 0x785d2404a620c656, 0x1e17491320c655, 0x8d9e1749bd20c656, 0x829e14fca620c656, 0x785d26e10120c656, 0x7853f424a920c656, 0x785d26e13f20c656, 0x845bd4fca620c656, 0x7853f424a620c5c6, 0x1e14b4a620c655, 0x785b84fcc220c656, 0x785ca424a620c656, 0x1d26f4831943f5, 0x7858d4fca620c656, 0x785b84fcc420c656, 0x7856d4fca620c656, 0x7856b4fce8298836, 0x7854b424a620c656, 0x785bd4fcc3298656, 0x7853f424ab20c656, 0x785b84fc83194156, 0x7553f424a620c656, 0x7a93f3a0a620c656, 0x8153f424a620c656, 0x785543a0a620c656, 0x7853f3f0a620c656, 0x785904fca620c646, 0x1e1749bd20c655, 0x785ab4fca620c656, 0x7853f408a620c656, 0x859e16e13f20c656])
  | 5, 10 => (packedWords [0x7853f3c8a620c656, 0x7853f450a620c656, 0x7d93f424a620c656, 0x8013f424a620c406, 0x7853f384a620c656, 0x7693f424a620c656, 0x785d16412d20c656, 0x7853f424a61f0656, 0x785d244ca620c656, 0x848e829883194346, 0x7853f424a620c5f6, 0x7853f424a620c566, 0x785614fca620c656, 0x785d2424b7298836, 0x7856b4fd09298836, 0x785d23d8a620c656, 0x785273a0a620c656, 0x7853a424a620c656, 0x1e14fc831d4655, 0x7a93f424a620c656, 0x784e8298831943d6, 0x8493f3a0a620c656, 0x7853f424a6224656, 0x78554424a620c656, 0x7853f38ca620c656, 0x7853f3f8a620c656, 0x885e16e13f20c656, 0x7853f378a620c656, 0x7853f424a420c656, 0x785d2470a620c656, 0x78590530a620c656, 0x7853f480a620c656])
  | 5, 11 => (packedWords [0x785904fca620c656, 0x8d9e14f8a620c656, 0x785d26f483194296, 0x7853f424a6218656, 0x7852d298831940f6, 0x785d26f4a620c656, 0x7853f424a6204656, 0x7853f3e8a620c656, 0x7852d29883194446, 0x785d34fcb120c656, 0x785b86413f20c656, 0x7852d340a620c656, 0x78527424a620c656, 0x785c7424a620c656, 0x785624fca620c656, 0x785d26f5b820c656, 0x785b84fc831942d6, 0x8493f424a620c656, 0x7993f424a620c656, 0x7853f474a620c656, 0x78541424a620c656, 0x78555424a620c656, 0x785d26f4831940f6, 0x7853f424a620c586, 0x8853f424a61dc656, 0x8093f424a620c726, 0x785d2370a620c656, 0x785bd4fcb120c656, 0x785d26f483194446, 0x7853f388a620c656, 0x7853f45ca620c656, 0x785b84fcb920c656])
  | 5, 12 => (packedWords [0x1e14f8a620c655, 0x7853f41ca620c656, 0x78501298831943d6, 0x8d9e14fca620c646, 0x785b84fc831d4656, 0x785d2424bf20c656, 0x7853f3fca620c656, 0x7853f458a620c656, 0x78536424a620c656, 0x785b84fc9620c656, 0x785674fca620c656, 0x7853f3d0a620c656, 0x785c03a0a620c656, 0x8013f3a0a620c446, 0x7853f424a620c576, 0x775d2424a620c656, 0x8013f424a620c4c6, 0x785d2598a620c656, 0x7853f424a620c616, 0x7853f424a61fc656, 0x875e14fd09298656, 0x7853f424a620c546, 0x7853f39ca620c656, 0x78529424a620c656, 0x785d2424a620c636, 0x7853f3a0a620c6d6, 0x769bd4fca620c656, 0x7853f424a620c696, 0x785b84fc83194126, 0x785774fca620c656, 0x785904fcb7298836, 0x825e14fca620c656])
  | 5, 13 => (packedWords [0x785d2424ca254656, 0x785b84fc83194256, 0x785604fca620c656, 0x7852d298831943f6, 0x8d9e14fca620c656, 0x785bd5ad3f298836, 0x1e17452d20c655, 0x78554470a620c656, 0x785c0424a620c656, 0x8013f424a620c446, 0x7853f424a623c656, 0x7859051ca620c656, 0x785bd550a620c656, 0x78557424a620c656, 0x785d26f4831943f6, 0x785c3424a620c656, 0x785d24249720c656, 0x785904fcc8298656, 0x1b84fc831943f5, 0x7853f424a620c6d6, 0x785d2424c3298656, 0x785a74fca620c656, 0x839e16e13f20c656, 0x7852d29883194086, 0x1e16e083194345, 0x7853f37ca620c656, 0x785d24d4a620c656, 0x785bd49ca620c656, 0x75d3f424a620c656, 0x785d16410920c656, 0x849bd4fca620c656, 0x1e16e13f20c655])
  | 5, 14 => (packedWords [0x785824fd09298836, 0x785d14b4a620c656, 0x785924b4a620c656, 0x7853f4d4b120c656, 0x7855b4b4a620c656, 0x1e16e14920c655, 0x7853f438a620c656, 0x7853f464a620c656, 0x785d16413f20c656, 0x851e14b4a620c656, 0x891e14b4a620c656, 0x7853f40ca620c656, 0x78540424a620c656, 0x7853f400a620c656, 0x785d26f59220c656, 0x785754fca620c656, 0x785b829883194346, 0x86d3f424a620c656, 0x785d23a0ca20c656, 0x785c0424b7298836, 0x785704fca620c656, 0x885e174909328656, 0x785504fca620c656, 0x785b84fca620c656, 0x88de14fca620c656, 0x78551424a620c656, 0x785b86e13f20c656, 0x8d9e17499020c656, 0x785a34fca620c656, 0x785d2424b120c656, 0x7853f424a61ec656, 0x8553f424a620c656])
  | 5, 15 => (packedWords [0x785484fca620c656, 0x7852d298831941a6, 0x7853f424a6208656, 0x785b84fc831940f6, 0x785d2424ca20c656, 0x785854fce8298656, 0x785c06f4a620c656, 0x801bd4fca620c446, 0x785b84fc83194446, 0x7593f424a620c656, 0x7853f368a620c656, 0x7853f424c9298656, 0x78531424a620c656, 0x785514fca620c656, 0x785734fca620c656, 0x785d2634a620c656, 0x785bc4fca620c656, 0x785904fcc3298656, 0x785d26f4831941a6, 0x835e1749bd20c656, 0x785644fca620c656, 0x785d2404ca20c656, 0x7853f42ca620c656, 0x8093f3a0a620c656, 0x7b93f3a0a620c656, 0x785d23f0a620c656, 0x7d53f424a6238656, 0x785854fd09298656, 0x7e9e14fd09298836, 0x785d2424ca1943d6, 0x7852d29883194186, 0x7853d424a620c656])
  | 5, 16 => (packedWords [0x8493f4d4a620c656, 0x7859061d3f298656, 0x1e17450920c655, 0x7853f424a320c656, 0x785d25ad09298836, 0x7853f420a620c656, 0x8093f424a620c656, 0x7b93f424a620c656, 0x7856f4b4a620c656, 0x785534fca620c656, 0x78539424a620c656, 0x785bd4fcc520c656, 0x1e17453f20c655, 0x7858f4fca620c656, 0x7853f460a6238656, 0x1e17491620c655, 0x785d2640a620c656, 0x785b84fc831943f6, 0x785243a0a620c656, 0x785c1424a620c656, 0x785d2424a6204656, 0x785d26f56f20c656, 0x78537424a620c656, 0x7858a4fca620c656, 0x819e14b4a620c656, 0x1e1748831d0655, 0x7853f424a620c556, 0x7852d328a620c656, 0x8d1e1749bd20c656, 0x849d2424a620c656, 0x7853f3d4a620c656, 0x784e8298831e4346])
  | 5, 17 => (packedWords [0x785d1424a620c656, 0x785904fcb120c656, 0x8013f424be298836, 0x7852f424a620c656, 0x785964fca6238656, 0x785c0424c3298656, 0x785a84fca620c656, 0x819e1749bd20c656, 0x7c9e14fca620c656, 0x785d2388a620c656, 0x7856e4fca620c656, 0x785d26f4ca20c656, 0x236785d220c655, 0x7853f3a0a620c796, 0x7852d4b4a620c656, 0x8493f424b120c656, 0x7853f424a620c5b6, 0x7853f444a620c656, 0x7853f3a8a620c656, 0x785d14fca620c656, 0x785a54b4a620c656, 0x785bb4fca620c656, 0x785834b4a620c656, 0x785d2458a620c656, 0x1e15d12d20c655, 0x785794fca620c656, 0x8813f424a620c656, 0x7d13f424a620c656, 0x7813f424a620c656, 0x785b86493f20c656, 0x7854f4fca620c656, 0x785684fce8298836])
  | 5, 18 => (packedWords [0x785d2424a620c616, 0x785d26f5a520c656, 0x785d26f58320c656, 0x7853f424a620c796, 0x785c2424a620c656, 0x8b1e14fca620c656, 0x7852d344a620c656, 0x785bd4fca020c656, 0x784e829883194396, 0x825e1748a620c656, 0x785914fca620c656, 0x7853f364a620c656, 0x785905ad3f298836, 0x7853f3a0a6238656, 0x1e13a0b120c655, 0x8d9e1748a620c656, 0x8093f470a620c656, 0x801d2424a620c446, 0x78590550a620c656, 0x785634fca620c656, 0x785d26f4d120c656, 0x809bd4fca620c656, 0x7b9bd4fca620c656, 0x785a24fca620c656, 0x7fd3f424a620c656, 0x785684fd09298836, 0x785744b4a620c656, 0x7852d298831942a6, 0x7d53f460a620c656, 0x7853f424a61f4656, 0x7b93f374a620c656, 0x785b85b13f20c656])
  | 5, 19 => (packedWords [0x7853e328a620c656, 0x7854c424a6238656, 0x785b84fc831941a6, 0x7853f424a6238656, 0x7859049ca620c656, 0x7853f3a0a620c726, 0x7858c4fca620c656, 0x7854c3e4a620c656, 0x785d26f57420c656, 0x785d26f4831942a6, 0x7853f3e4a620c656, 0x7853f424a620c6b6, 0x849904fca620c656, 0x88de14fcc3298656, 0x78590554a620c656, 0x1e1749b820c655, 0x7853f43ca620c656, 0x784e82c4a620c656, 0x785894b4a620c656, 0x784e829883194336, 0x78525424a620c656, 0x7854d424a620c656, 0x7853f424a620c726, 0x7852d29883194206, 0x785d26f4831942e6, 0x785c03c8a620c656, 0x82de16e13f20c656, 0x7852c424a620c656, 0x785d240ca620c656, 0x7853f424a6250836, 0x785ac4fca620c656, 0x1e16952d298655])
  | 5, 20 => (packedWords [0x781bd4fca620c656, 0x7852d3a0a620c656, 0x785b84fcc620c656, 0x785d26f483194206, 0x785904fca6234656, 0x785a24fcb7298836, 0x2214fd092f4655, 0x7853f3bca620c656, 0x7852d29883194196, 0x785ba4fca620c656, 0x8c9e1749bd20c656, 0x785d26e0a620c656, 0x785bd4fca620c796, 0x785b85bd3f20c656, 0x785ad4fca620c656, 0x801e14b4a620c656, 0x785bd4fcae20c656, 0x1e1749bd694655, 0x785d26f4e820c656, 0x785724fca620c656, 0x7852739ca620c656, 0x7d53f3a0a620c656, 0x785c0640a620c656, 0x801904fca620c446, 0x785d26f483194196, 0x785d2424a6208656, 0x785a14fca620c656, 0x7852d424a620c656, 0x7853f428a620c656, 0x7856b4fcdf298836, 0x801e1749bd20c656, 0x819e16e13f20c656])
  | 5, 21 => (packedWords [0x785894fca6254656, 0x785b84fcca20c656, 0x7852d29883194346, 0x7853f380a620c656, 0x7855f4fca620c656, 0x785d2544a620c656, 0x784e829883194366, 0x785d26f483194416, 0x7853f3eca620c656, 0x7d54c424a620c656, 0x785d26f50920c656, 0x785d2590a620c656, 0x7d53f424a620c656, 0x1e12e8a620c655, 0x7853f4b4a620c656, 0x8013f388a620c446, 0x7853f424a620c5a6, 0x785bd4fca6238656, 0x8015e4fd09298836, 0x785d26f483194346, 0x785ae4fce820c656, 0x7853f3b0a620c656, 0x1e16e0b920c655, 0x7853f424a620c686, 0x785494b4a620c656, 0x785d26f50120c656, 0x7853f360a620c656, 0x7853f424a620c666, 0x785b86953f20c656, 0x785b860d3f20c656, 0x785d26f53f20c656, 0x885904fca6194436])
  | 5, 22 => (packedWords [0x7853f470a620c726, 0x7853f414a620c656, 0x785b74fca620c656, 0x785814b4a620c656])
  | 6, 0 => (packedWords [0x7853f424a620c657, 0x424a620c6504dde4, 0x31ca620c6577853f, 0x20c65059de14fd09, 0x1942677853f424a6, 0x195de14fd0929883, 0x77853f424a627083, 0x14fd092989520c44, 0x4fd0929883195de, 0x9298831940d77859, 0x8298831959e14fd0, 0x320c657001e14fd1, 0x3195de14fd092988, 0x57785d26f5092988, 0xe14fce82989620c6, 0x904fca620c650d1d, 0x3f424a620c657785, 0xe229883195de1551, 0xa620c656801e14fc, 0x83195c006f59f4fc, 0x6577853f424a6264, 0xde15093f424a620c, 0x53f424b929883195, 0x93f2988319446778, 0x4a620c650d1de159, 0x4a620c6578493f42, 0x883195de16513f42, 0xc657785d26f53f29, 0x5de14fd09388a620, 0x853f424ac2988319, 0x853f3d8a620c6577, 0x24a620c650d5e167, 0xfd092988377853f4, 0x9883195e00785834, 0x941277853f49d092, 0x95de14fce8298831, 0x785bd4fcc2298831])
  | 6, 1 => (packedWords [0x4fd09298831943d7, 0x5253f29883195de1, 0x2989620c65778590, 0x29883195de14fd09, 0x20c6577853f424aa, 0x195de16f53f310a6, 0x78c1e14fd0929883, 0x16f53f2988319415, 0xf4590929883195de, 0x9298831944d77853, 0xf29883195de14fd0, 0x620c657859e16f53, 0x4195e377853f424a, 0x567853f424a620c7, 0x785894fca620c6, 0xe14fcfd298831958, 0x92989820c657001, 0xa620c650fd9e14fd, 0x831941270013f3a0, 0x65101de14fd09298, 0x6577853f424a620c, 0x9e1749c6424a620c, 0x1e13a0a620c650d1, 0x9092988319443700, 0xd0929883195de174, 0x4a620c6577859f4f, 0x883195de173d3f42, 0x4657785974fd0929, 0xdde14fd092988319, 0x853f424a620c650a, 0x853f424a620c6577, 0x24d429883195e097, 0x24a620c6577853f4, 0x9883195a367853f4, 0xc657001e14fce82, 0x5a21785bd4fca62, 0x1e1424a620c651])
  | 6, 2 => (packedWords [0x785b84fce820c656, 0x424a620c650fd800, 0x424bd20c6560013f, 0x298831958007853f, 0x20c657001e1524e8, 0x99de17490934ca6, 0x7785bd4fca620c65, 0x16f5904fca620c65, 0x1749c6424a620d9e, 0x929883194457001e, 0x829883195de14fd0, 0x620c6577853f424c, 0x50b1de17013f424a, 0x567853f424a620c6, 0x7854c424a620c6, 0xe14fd09298831958, 0x92dca6258837001, 0xbc29883195de14fd, 0xa620c6577853f424, 0x831959e17213f424, 0x657001e151509298, 0xdf57853f424a620c, 0x53f424a620c65001, 0x5b84fd0920c65678, 0xd0929883195c0078, 0x4a620c6577a5e14f, 0xc65119de16f53f2e, 0xc657785d2424a620, 0x59f3785d2424a620, 0x1e14fd012988319, 0xfd092989b20c6570, 0xfce829883195de14, 0x9883194107785b84, 0x10a620d9e14fd092, 0x942f7001e17193f3, 0x95de14fd09298831, 0x865e14fd09298831])
  | 6, 3 => (packedWords [0x4fd0929883194437, 0x4fca625883195e00, 0x2f4a620c657785bd, 0x20c6503dde14fd09, 0x1b06577853f3a0a6, 0x195de14fd0929883, 0x77853f424b729883, 0x1749092989520c65, 0xf3a0a620c65111de, 0x9298831944877853, 0x620c650a9de14fd0, 0x620c6578093f424a, 0x5131e218193f424a, 0x977853f424a620c6, 0xe14fd09298831942, 0x5d4fd0929883195d, 0x9298a620c657785, 0xc5298831959e14fd, 0xa620c657001e14fc, 0x74195de14fd12424, 0x657785bd4fca620c, 0xde1719904fca620c, 0x5904fca620c6510d, 0x53f2988319412778, 0xd0929883195de16f, 0x4a620c657785b84f, 0x883195de16013f42, 0x8837785904fca626, 0x5de15ad3f424d329, 0x85bd67d3f2988319, 0xc13f424a620c6577, 0x24a620c6503dde16, 0x98831940977853f4, 0x98831959e14fd092, 0x94447001e14fd132, 0x95de14fd09298831, 0x785d274909298831])
  | 6, 4 => (packedWords [0x785bd4fca620c657, 0x424d229883195e36, 0x424b72988367853f, 0x29883195c007853f, 0x20c656785d2424c2, 0x195c007853f3d8a6, 0x77853f424a620c6f, 0x87853f424a620c65, 0xa4fd0929883195e1, 0x9310a620c6577855, 0x329883195de17490, 0x31943f6785904fcd, 0x3195c006f53f2988, 0x57785d2679092988, 0xe174909298831941, 0xe151d09298831959, 0xc6424b9298836001, 0x904fca620d800785, 0xa620c657001e1719, 0x83195e047853f424, 0x6577853f424c3298, 0xde14fd09394a620c, 0x5644fd0929883195, 0x53f470a620c65678, 0xd0932883195c0078, 0x8831944a7785d24f, 0x883195de14fd0929, 0x4836859e17490929, 0x5800785c65d13f42, 0x1e16f53f2988319, 0xfce8298831943f70, 0x24a620c65065de14, 0x98831944677b93f4, 0x9883195de16413f2, 0x940f67cde16413f2, 0x95c00785bd4fc831, 0x785874fd09298831])
  | 6, 5 => (packedWords [0x7853f370a620c656, 0x424a620c6500dc00, 0x298831941a77853f, 0x29883195de14fcd1, 0x258657885e174909, 0x195de14fd0930ca6, 0x7785994fd0929883, 0x16413f2989520c65, 0x14fd0929883195de, 0x9298831943f785de, 0x929883195de14fd0, 0x620c657785d26410, 0x3195de16f53f298a, 0xf77853f424a62288, 0xe151d09298831940, 0xe15993f298831959, 0x15424a620c657001, 0x929883195de14fd, 0x83194217785e14fd, 0x83195de14fd09298, 0x126785924fce8298, 0xc00785d242483194, 0x5bd4fca620c6503d, 0x9092e4a620c65778, 0xd0929883195de174, 0xca620c6577858b4f, 0x8831959e1749904f, 0x40a7001e14fca626, 0x1de14fd092988319, 0x85bd4fca620c6511, 0x13f424a620c6577, 0xfcc229883195e168, 0x10a620c657785904, 0x989520dde16413f3, 0x943d7785834fd092, 0x959e174909298831, 0x1e16412d298831])
  | 6, 6 => (packedWords [0x6713f424a620c657, 0x424a625883195de1, 0x29883194157785d2, 0x29883195de16413f, 0x20c6577853f424bf, 0x195e30785d2424a6, 0x7785924fd0929883, 0x14fd09298831c82a, 0x14fd0929883195de, 0x4fca620c6578a5e, 0x929883195e167859, 0x32986567855b4fd0, 0x3195c007853f424c, 0x577853f491092988, 0xe15953f424a620c6, 0x904fca620c65139d, 0x3f3a0a620c657785, 0xe629883195de15b1, 0xa620c6577853f424, 0x83195e247853f424, 0xa667853f424a6248, 0xc00785c66953f424, 0x53f424db29883195, 0xd092988e19420778, 0x4a620c65049de14f, 0x4a620c656785d242, 0xc65069c007853f4d, 0x43477853f3a0a620, 0x5de14fd09298831e, 0x853f424ca2989519, 0xfd09298831945177, 0xd13f3b0831959e14, 0xfca620c657001e15, 0x9883195a21785904, 0x98656001e1748e82, 0x95c00785874fd092, 0x785a24fd09298831])
  | 6, 7 => (packedWords [0x5b13f424a620c657, 0x424a620c65019de1, 0x424a620c6577853f, 0x20c650fda357853f, 0x1941d7001d2424a6, 0xfdde14fd0929883, 0x7785bd4fca620c65, 0x1641904fca620c65, 0xf424a620c65069de, 0x9298831944777853, 0x620c6514dde14fd0, 0x320c6577853f424a, 0x3195de16413f2988, 0x577853f424a625c8, 0xd7853f424a620c6, 0xe15f90929883195a, 0x929883194387001, 0x9298831959e14fd, 0x83194437001e1749, 0x83195de15913f298, 0x6577853f424b4298, 0xe077853f424a620c, 0x5904fcb929883195, 0xce8318a620c65778, 0x4be29883195de14f, 0xca620c6577853f42, 0x883195de1651904f, 0xc657785744fcec29, 0x5de15f13f424a620, 0x853f424a620c650e, 0xfcc4298831943f67, 0xfce829883195c004, 0x24a620c6577856f4, 0xc4831959e14fd224, 0xc656001e14fd092, 0x95c00785d2404a62, 0x785904fca6258831])
  | 6, 8 => (packedWords [0x4fd092988820c657, 0x4fd0929883119de1, 0x310a620c656801e1, 0x29883195c007853f, 0x20c6577853f424af, 0x195de15ad3f424a6, 0x5785bd6493f29883, 0x1e14b4a620c65, 0x16413f2986505580, 0xf424a620c657001e, 0x629883195e277853, 0x620c6577853f424c, 0x507de067853f3a0a, 0x577853f424a620c6, 0xe14fce8328a620c6, 0xd2424a620c650a5d, 0x9298a620c657785, 0x929883195de1749, 0x831941277856f4fd, 0x65081de16413f298, 0x6577d53f424a620c, 0xde160d3f3f4a620c, 0x5e14fd09328a6195, 0xd092988d20c65788, 0xd0929883195de14f, 0xa620c6567855c4f, 0x4831954007853f3f, 0xc65700000785d26f, 0x5de165d904fca620, 0xd1e14fd092988319, 0xfd09298831945078, 0xfca620c650adde14, 0x98831940f7785904, 0x98831959e1749092, 0xc657001e13a0b92, 0x95de14fd092c8a62, 0x8d9e16413f298831])
  | 6, 9 => (packedWords [0x4fd092c4a620c657, 0x424a620c6513dde1, 0x298831944477853f, 0x29883195de174909, 0x1e0657819e14fd09, 0x195de14fd0929883, 0x77853f424ca29883, 0x16953f3a0a620c65, 0x34fce829883195de, 0xb4fd092988367858, 0xf3a0831958007856, 0x3194337001e15d13, 0x50fd9e14fd092988, 0xf6001092e4a620c6, 0x6413f298831943, 0xe14fcb929883195c, 0x54424a620c656825, 0x9308a620dc00785, 0x831943f6801e14fd, 0x65069c005d13f424, 0x657785bd4fca620c, 0xe0d785bd4fca620c, 0x53f460a620c65081, 0xd162988319412778, 0x4b9298831959e14f, 0x4a620c657001e142, 0x8831959e14fd2d42, 0xc657001e16413f29, 0x5de14fce8344a620, 0x853f424a620c6501, 0x853f424a620c6577, 0xfd0929883195e2d7, 0x24a620c657899e14, 0x98831959e15193f4, 0xc657001e1749bd2, 0x95de14fd093b0a62, 0x785a54fd09298831])
  | 6, 10 => (packedWords [0x60d3f424a620c657, 0x5d13f424831959e1, 0x2989620c657001e1, 0x298831959e170109, 0x20c657001e149d09, 0x195e2e7853f424a6, 0x7785984fd0929883, 0xb7853f424a620c65, 0x24fd0929883195a2, 0xf424a620c6570021, 0xf42483195de77853, 0x620c657785d26f53, 0x510dde15d13f3a0a, 0xa78853f424a620c6, 0xe14fce8298831942, 0x3f48d0929883195d, 0x3f388a620c656785, 0xd129883195c00785, 0xa62206567853f424, 0x83195c007853f424, 0x6577853f424a627c, 0xde14fd18424a620c, 0x53f424a620c7a195, 0x909298831943f778, 0x4a620c650d9de174, 0x8831944477853f42, 0x883195e004fd0929, 0xc656785584fd0929, 0x5c007853f458a620, 0x853f424ce2988319, 0xfd09298831940777, 0xfd0929883195de14, 0xfca620c6577857f4, 0x9883195de16f56f4, 0xc6577ade14fd092, 0xa9de15d13f424a62, 0x7853f424a620c650])
  | 6, 11 => (packedWords [0x7853f298831d0656, 0x424cd29883195c00, 0x298831941e77853f, 0x29883195de14fd09, 0x20c657889e14fd09, 0x3dde14fd09354a6, 0x7785904fca620c65, 0x14fd092988319437, 0x94fce829883195de, 0xf424a62346567858, 0x620c65111c007853, 0x3194147785904fca, 0x3195de14fce82988, 0x77853f424a62148, 0xe14fce8298831942, 0x97853f298831959, 0xbd4fca620c657002, 0xa624083195e06785, 0xa620c6577853f424, 0x831959e16f53f328, 0x657002367853f298, 0xa2a7853f424a620c, 0x1e17010929883195, 0x13f424a620c44600, 0x53f3a0a619580080, 0xa620c657001e169, 0xc650b9de14fce83a, 0xc6567853f424a620, 0x5c00785092f0a620, 0x85d2649092988319, 0x253f424a620c6577, 0x24fd29883195de16, 0x98831941977853f4, 0xc65045de14fce82, 0xa86577853f424a62, 0xfd9e14fd09298831, 0x1a54fd09298650])
  | 6, 12 => (packedWords [0x5793f424a620c657, 0x424a620c65051de1, 0x2e4a620c6567853f, 0x20c65081c00785bd, 0x20c6577854c424a6, 0xd1e007853f3a0a6, 0x7785093a0a620c65, 0x14fd092988319420, 0x14fcc8298831959e, 0xf424a620c657001e, 0xf29883195e327853, 0x620c657785bd6953, 0x3195def7853f424a, 0x56785bd60d3f2988, 0x785bd5d13f20c6, 0xe16953f424a61958, 0x9298831941b7001, 0xe829883195de14fd, 0x3f20c6557853f424, 0x650d1c00001e16e1, 0x177853f3a0a620c, 0xde14fce829883194, 0x5b84fd093a083195, 0xd092988319419778, 0xd0929883195de14f, 0x89e20c6577ede14f, 0xc650edde14fd0929, 0xc6577853f424a620, 0x5de16953f370a620, 0x853f424a620c650c, 0x853f424a620c6577, 0xfcd129883195e007, 0x24a6194436785bd4, 0x98831a98008853f4, 0x943f7001e14fd092, 0x95de16413f298831, 0x7853f4fce8298831])
  | 6, 13 => (packedWords [0x4fd0929883194417, 0x424a620c65069de1, 0x3f0a620c657785d2, 0x29883195de16493f, 0x1942a77853f42509, 0x195de14fd1c29883, 0x7785864fd0929883, 0x15253f3a0a620c65, 0xf424a620c650d1de, 0x9298831942277853, 0x620c65005de14fd0, 0x620c6577853f424a, 0x50a9de16f5744fca, 0xa7785bd4fca620c6, 0xe14fd09298831943, 0xe16e13f298831959, 0x3f424a620c657001, 0x129883195de1531, 0xa620c6577853f425, 0x83195e218593f424, 0x657785b54fd09298, 0xde14fd3f424a620c, 0x9e14fd0929883195, 0x53f424a620c65784, 0xd0929883195e0178, 0x4a620c657785454f, 0x8831959e14fd092d, 0xc657001e17490932, 0x5de15253f424a620, 0xdde14fd092988319, 0xf53f298831942e77, 0x413f29883195de16, 0x989520c467785926, 0x98831959e14fd092, 0xc657001e1748c42, 0x95de14fd09314a62, 0x7853f424f1298831])
  | 6, 14 => (packedWords [0x6415b4fca620c657, 0x4fd0929883195de1, 0x298831dc657821e1, 0x29883195de14fd09, 0x20c656785d44fd09, 0x195c00785644fca6, 0x7891e16413f29883, 0x17496f424a620c65, 0xd4fca620c65081de, 0x929883194277785b, 0x929883195de14fd0, 0x620c6577853f44d0, 0x6195a34785d2424a, 0x57001e16f5a54fca, 0xe16f53f3a0a620c6, 0x3f424f629883195d, 0xd2424a620c657785, 0xd629883195e06785, 0x831941977853f424, 0x83195de16f53f298, 0x657785d2424ca298, 0xe00785bd4fca620c, 0x5a94fd0929883195, 0x5a54fcdc29865678, 0x4a620c65125c0078, 0x4a620c4477853f42, 0x883195a007853f42, 0xc656002024fd0929, 0x9c007b93f424a620, 0x853f424a620c6500, 0x413f298831941a77, 0x710929883195de16, 0x24a620c6577853f4, 0xc65071de14fd104, 0xd86577853f424a62, 0x95de14fd09298831, 0x785bd4fd09298831])
  | 6, 15 => (packedWords [0x4fd09308a6254837, 0x3a0a620c6505dde1, 0x424a620c6577853f, 0x23883195e257853f, 0x20c6567853f424a6, 0x195c00785d2640a6, 0x7785474fd0929883, 0x16f53f2988319434, 0xf424a620c650c1de, 0x5424a620c6577853, 0x620c70195de1749a, 0x620c6577853f424a, 0x3195de174983424a, 0x56871e14fd092988, 0x785d25d10920c6, 0x3f424a628083195c, 0x9370a620c657785, 0xa625883195de14fd, 0xa620c657785a24fc, 0x83195de14fd09330, 0x6577853f424d7298, 0xde17193f3a0a620c, 0x53f3a0a620c6510d, 0xd09298831e465778, 0xd0929883195de14f, 0x883194177841e14f, 0xc65031de14fd0929, 0xc6577853f424a620, 0x5de174909344a620, 0x85bd5253f2988319, 0x84c42e4a620c6567, 0x9109298831958007, 0x24a620c657001e14, 0x10831959e15993f4, 0xc657001e15d13f3, 0x199e14fd09298a12, 0x1e14fd09298951])
  | 6, 16 => (packedWords [0x8013f424a620c657, 0x6f53f29883195e06, 0x4fca620c657785d4, 0x20c65091de16416f, 0x20c6577853f424a6, 0x195de172d3f424a6, 0x7785c64fd0929883, 0x14fce834ca620c65, 0xf424a620c6510dde, 0x4424a620c6577853, 0x620c650a9de17497, 0xa20c657785d2424a, 0x5039de14fd092989, 0x577853f424a620c6, 0xe17113f424a620c6, 0xe17193f3a0a620d9, 0x3f44ca620c657001, 0x929883195de16f5, 0xa620c796785c94fd, 0x83195c007853f424, 0x657819e16413f298, 0xdf17853f3a0a620c, 0x5904fcca29883195, 0x12d424a620c65778, 0xd09298830fd9e164, 0x883194527001c64f, 0x883195de14fd0929, 0x44677856a4fd0929, 0x5de14fce82988319, 0x853f424d32988319, 0xf53f424a620c6577, 0x893f298831959e15, 0xa0a620c657001e16, 0x9883195df37853f3, 0x988367859a4fd092, 0x95800785c64fd092, 0x1e1640b9298831])
  | 6, 17 => (packedWords [0x6413f4b4a620c657, 0x424a620c650f9de1, 0x4fca620c6577853f, 0x20c72195de16f5bd, 0x20c6577853f424a6, 0x195de14fd35424a6, 0x77853f424a627483, 0x17853f424a620c65, 0x2424a620c65081df, 0x4fca620c657785d, 0xf29883195de16959, 0x920c6567859060d3, 0x3195c0078574424b, 0x57785844fd092988, 0xe14fce82989520c6, 0xe1641744fc831959, 0x3f424a6238656001, 0xa620c6508dc00785, 0x831943477853f424, 0x83195de14fd35298, 0x6577853f424b8298, 0xe32785d2424a620c, 0x9e14fd0929883195, 0xd092988319c65787, 0xd0929883195de14f, 0x8a620c657785564f, 0x4a61959e14fd092b, 0x4467001e1749a542, 0x59e14fd092988319, 0x1e15d1274248319, 0x49093a0a620c6570, 0xfd0929883195de17, 0x3ca620c6577cde14, 0x24a620d9e14fce83, 0x944b7001e15a93f4, 0x65de14fd09298831, 0x785d2424a620c650])
  | 6, 18 => (packedWords [0x6413f344a620c657, 0x6f53f29883195de1, 0x424a620c657841e1, 0x29883195de17393f, 0x20c657801e174909, 0x195de14fd0929895, 0x7785784fd0929883, 0x14fd092988319444, 0x24fce829883195e2, 0xf424a620c726785d, 0x620c650a9c007853, 0x620c65778554424a, 0x3195e027853f424a, 0xc77b9e14fd092988, 0xe14fd09298831943, 0x3f3a0c229883195d, 0x929883194417785, 0xb629883195de1749, 0xa620c6577853f424, 0x831959e14fd09300, 0x656001e14fcc6298, 0xc00785a54fcc4298, 0x53f424cf29883195, 0xce8310a620c65778, 0xcca29883195de14f, 0xca620c6578d9e14f, 0xc650a9de1641744f, 0x4347785904fca620, 0x5de1749092988319, 0x853f424a62308319, 0xfce8298831941577, 0xf53f29883195de14, 0x24a620c656785c66, 0xc6510dc0067d3f4, 0xc657785bd4fca62, 0x95de15f93f424a62, 0x7857449d09298831])
  | 6, 19 => (packedWords [0x7853f3a0a620c657, 0x4250129883195e16, 0x2e4a620c656785d2, 0x29883195c00825e1, 0x1b8657785d24fd09, 0x195de14fd0929883, 0x77853f424cb29883, 0x17353f424a620c65, 0xf424c229883195de, 0x92c4831943477853, 0xf328a61959e14fd0, 0x620c657001e16413, 0x3195de14fd09310a, 0x567853f424b32988, 0x7852d424a620c6, 0xd25250929883195c, 0x3f424a620c657785, 0xa620c650cd9e1679, 0x83194157001e14fc, 0x83195de14fd09298, 0xb7785bd4fcd3298, 0xde14fd0929883194, 0x5d24fd0129883195, 0x546424a620c65678, 0xd09328650a980078, 0x4a620c657001e14f, 0xca620d9e16553f42, 0xc657001e1719bd4f, 0x5a217853f3a0a620, 0x1e14fd092708319, 0x853f424a620c6570, 0x490929883195e167, 0xf0a620c657785d47, 0xc65081de14fd093, 0xc656785904fca62, 0x95800785d26f5092, 0x1f54fd09298831])
  | 6, 20 => (packedWords [0x4fd09298831944e7, 0x4fd2d298831959e1, 0x424a620c6e6001e1, 0x2e4a61958007853f, 0x298656001e169509, 0x195c00785a56413f, 0x6785904fce829883, 0x7853f3b0a620c65, 0x14fd0929883195c0, 0xf2988319446784de, 0xf29883195de16f53, 0x620c6577cde16f53, 0x9195a287853f424a, 0x57001e1695744fd0, 0xe16c53f424a620c6, 0x904fca620c65065d, 0xd26f53f20c656785, 0x929883195c00785, 0xa620c657885e14fd, 0x71195e00785904fc, 0x477853f424a620c, 0xde14fd0929883194, 0x53f3a0b929883195, 0x53f2989520c65778, 0x1e16f])
  | 7, 0 => (packedWords [0x6413f424a620c657, 0x424b929883195de1, 0x2989620c6577853f, 0x20c65049de14fd09, 0x20c6567853f424a6, 0xfd8007853f3a0a6, 0x60013f424a620c65, 0x7853f424a620c65, 0xf424a620c6503dc0, 0x9298831944477853, 0xf298831959e14fd0, 0x31943f7001e16f53, 0x3195de14fd092988, 0xa7785924fd092988, 0xe14fd09298831941, 0xe174909298831959, 0x3f310a620c656001, 0x929883195c00785, 0xa620c6577856f4fd, 0x83195e067853f424, 0x6567853f424ca298, 0x800785092e4a620c, 0x1e16413f29883195, 0x53f424a620c65700, 0xd0929883195de169, 0xd0920c656785834f, 0x883195c00785744f, 0xc6577853f424d129, 0x9de15d13f424a620, 0x853f424a620c650a, 0xfd09298831942077, 0x953f424a61959e14, 0xa0a620c657001e16, 0xc65065de14fd093, 0xc6577853f424a62, 0xd1e007853f424a62, 0x7853f424a620c650])
  | 7, 1 => (packedWords [0x5253f424a620c657, 0x4fd0929883195de1, 0x424a620c657785bd, 0x20c6510dde17193f, 0x20c6577853f424a6, 0x20d9e14fd0934ca6, 0x7001e17193f424a6, 0x14fd092988319446, 0x14fd0929883195de, 0x92989520c6577cde, 0x929883195de14fd0, 0x620c657785d24fd0, 0x3195de14fd09308a, 0x577853f424c42988, 0xe14fd09298831941, 0xe14fd0929883195d, 0x3f424a620c657859, 0x221785])
  | 8, 0 => 0x7853f424a620c656
  | _, _ => 0

private def wordBlocks : Nat → Nat
  | 0 => (packedWords [0x0, 0x0, 0x24109440000000, 0x0, 0x1000000000000000, 0x8000000000000000, 0x4000089412000100, 0x80, 0x4000000000000000, 0x20, 0x8004182402800000, 0x10, 0x210600108a000008, 0x4, 0x0, 0x2])
  | 1 => (packedWords [0x90425100000000, 0x8000, 0x2000000000000000, 0x4800, 0x0, 0x40000, 0x1000000000000000, 0x20000, 0x0, 0x10000, 0x2000000000000000, 0x4000000000004000, 0x2000f0c000042000, 0x20000000001004, 0x10024109440000, 0x600])
  | 2 => (packedWords [0x7f6d98aa43108408, 0x1804204, 0x0, 0x2000a00, 0x809042511003000, 0x2000000000801a80, 0x1202410944400c00, 0x2606a0, 0x0, 0x100000, 0x8007db2402908001, 0x4080000000044010, 0x2041ffcd25b42000, 0x11804, 0x40000000000000, 0xa812001080])
  | 3 => (packedWords [0x0, 0x402a048004600010, 0x2000894122001008, 0xa812001184804, 0x6f0d08a04200840, 0x8402a04800520421, 0x43bc3cb693280310, 0x800a81200158588, 0x146f9d4af1420084, 0x8402a048005a042, 0x4202499d56600d0, 0x40800a812003186a, 0xf9c425162402, 0x100002a048015200, 0x841fdb662a90802, 0xa812005481])
  | 4 => (packedWords [0x8000000000000000, 0xc08001010120e8, 0x2024109440000002, 0x3020004060483b, 0x8809042511003000, 0x740c080010901a8e, 0xa202410944e1ac81, 0xe103aa1204108400, 0x78e0032da48800c0, 0xea8481042120, 0x3e20000000000000, 0x40003aa120414848, 0x2f8ef0d08a042008, 0x15040ea848105216, 0x2a23c3000012a00, 0x3aa12041584])
  | 5 => (packedWords [0x8000000000000000, 0x40ea8481056120f8, 0x2000894122001008, 0x3aa1204158483e, 0x2000000000000000, 0x20100104c0100808, 0x1802410944000000, 0x4004130060202, 0x8280904251100300, 0x100104c0901a8, 0x2080000000000000, 0x4000400413044020, 0x2821f6c900a42000, 0x3570100104c1100c, 0x2a83c3000010a80, 0x70241340400])
  | 6 => (packedWords [0x809042511023001c, 0x1c0904d010180aa, 0xa000000000000000, 0x107024134040683a, 0x100022504880c502, 0x8420041104044040, 0x600089412603d40, 0x80104412116b0, 0x100000000000000, 0x2004110504484, 0x8047db2402908001, 0x801044145131, 0xc018090425110030, 0xb50420041105845a, 0x10003c300001ab20, 0x8a916415190])
  | 7 => (packedWords [0x80904251384b2001, 0x422a459054658400, 0x6000894122001008, 0xc08a916415196904, 0x200904251306b281, 0x8300515c5004840, 0xc41824028100020, 0xc014571401210, 0x820f0c000042800d, 0x300515c514484, 0x20c0000000000000, 0x9550c01457145121, 0x4aa8000000018ab0, 0xb5743c0d15d40458, 0x12aa3e710945ebac, 0xfab57755596])
  | 8 => (packedWords [0x0, 0x8c01002002004200, 0x1fdb662a91e423f0, 0x3300400800801080, 0x7f6fbdaecf9cdfe, 0x8c0100200200420, 0x441824028100000, 0xa030040080080108, 0x5060032da48000c0, 0x288c010020020062, 0x945c18ef6ba10030, 0x5003004008008018, 0x2800f0c000042800, 0x1408c01002003404, 0xa047db240291a00, 0x300400800d01])
  | 9 => (packedWords [0x6f0f2da4c280c5a0, 0x8c010020034062d0, 0x47db240291800100, 0x300400804c01080, 0x1f6c900a4280050, 0x84c0100201340428, 0x41bc3cb6932a0317, 0xa130ac1280198108, 0x50e0032da48800c0, 0x280c2b04a0066162, 0x941bc3cb69308031, 0x50030ac12801c818, 0x2906f0d08a042808, 0x1484c2b04a007604, 0x8a423c3894132a01, 0x30ac12801d85])
  | 10 => (packedWords [0x80022504888041e1, 0xcc18021024120e8, 0x1bc3422810a02170, 0x330600840c010ba, 0x8e0032da48000c0a, 0xcc18021030162f, 0xa23c3000010a0014, 0xe1330600840d058b, 0x78e0032da48800c0, 0x784ceb84a1062162, 0x3e20008941222010, 0x1e133ae128419848, 0xf8e0032da48880c, 0x1784ceb84a106612, 0x89e3bc3cb6932a03, 0x33ae12841985])
  | 11 => (packedWords [0xef0f2da4ca80c5e1, 0xceb84a1066162f8, 0x3800cb6920003028, 0x33ae12841c858be, 0x8ef0f2da4c200c4a, 0x84ceb84a1072162f, 0xe3bc3cb6932a0317, 0xe133ae12841c858b, 0xe88f0e2504ca8045, 0x504ceb84a1076120, 0xaa23c3000012a001, 0x5e133ae12841d850, 0x2b8ef0f2da4ca80c, 0x1704ceb84a107614, 0xba3bc3422812a02, 0x33ae12841d85])
  | 12 => (packedWords [0x8f0c000042800500, 0x4ceb84a1076162f8, 0x23c3894132a01148, 0x33ae12841d858be, 0x8e0032da48000c0a, 0x84ceb84a1076162f, 0xe3800cb692200302, 0x33ae12841d858b, 0xf8ef0d08a0428085, 0x784ceb84a1076162, 0xbe3bc3cb6932a031, 0x5e133ae12841d858, 0x2f9ef0f2da4ca80c, 0x178cceb84a107616, 0x8be7fdbef6bb3a03, 0x33ae12841d85])
  | 13 => (packedWords [0xef0f2da4ca80c5e1, 0x4ceb84a10761e2f8, 0x3bc3cb6932a03178, 0x933ae12841f858bf, 0xcef9f6ff5ca80c5e, 0x84ceb84a107e162f, 0xe3bc3cb6932a0317, 0xe133ae12843d85ab, 0xf8ef9f6ff5da83c5, 0x784ceb84a10f61ea, 0xbe3bc3cb6932a031, 0x5e133ae12845d858, 0x2f8ff6fbdaeca80c, 0x3408ceb84a117616, 0xa087db240291a00, 0x340441b00c01])
  | 14 => (packedWords [0x1060900a04000002, 0xd01106c0300c283, 0x83c3000010a00140, 0x1340441b00d030a0, 0xaef0f2da4ca80c5e, 0x84deb94ed0761e2f, 0xebbc3cb6932a0317, 0xe337ae53b45d878b, 0x1000225048c8c5b, 0xf8ce014130424404, 0x805fdbef6bb3e737, 0xd02380504c109111, 0x6011f6c900a46800, 0x8e01413052444, 0x1804418240281000, 0x380504c14913])
  | 15 => (packedWords [0xf0c000042800500, 0x4e0141305344c681, 0x7bc3cb6932a03178, 0x23baf16c55d979be, 0x3000000000480090, 0x8f01517c4244848, 0xc41824028100020, 0x23c0545f1481318, 0x31f6c900a46800d, 0x408f01517c5244c6, 0xa0c7db240291a003, 0xd023c0545f149131, 0x6831f6c900a46800, 0x3400f01517c5304c, 0x1a083c3000010a00, 0x3c0545f14d13])
  | 16 => (packedWords [0x1f6c900a46800d02, 0xf01517c5344c682, 0xc3c3000010a00140, 0x23c0545f14d131a0, 0x31060900a0400000, 0x8f01517c5344c68, 0xc7db240291a0034, 0x23c0545f14d131a, 0xc31f6c900a46800d, 0x688f01517c5344e6, 0xb4dfdbef6bb1a033, 0xd023c0545f14d139, 0x6839f6c900a46800, 0x3408f01517c5345e, 0x1a1c7db240291a00, 0x3c0545f14f13])
  | 17 => (packedWords [0x1ffcd25b46800d0a, 0x8f01517c53c4c687, 0xc7db240291a00340, 0x23c0545f16d13ba0, 0x39ffcd25b56830d0, 0x8f01517c5b45ee8, 0x4c7db240291a0034, 0x23cad57f15d931a, 0x937f6d98aa46808d, 0x48cf2b55fc5764c6, 0xa4e7dbad43b3a013, 0xd023cad57f15d979, 0x6eb9f6c900a46800, 0x350cfc1d17d5345e, 0x1aae7db240293a00, 0x3faf57f55d97])
  | 18 => (packedWords [0x9ffcd25b7eeb2d5f, 0x4febd5fd5765c6ab, 0xbbc3cb6932a03378, 0xd3faf57f55d979be, 0xaef9f6ff5faebedf, 0x8febd5fd5765e6f, 0xee7db240291a0034, 0xe13faf57f55d979b, 0xfbef0f2da4ca80c5, 0x78cfebd5fd5765e6, 0xbeffdbef6bb3a033, 0x3faf57f55d979, 0x9440000000000000, 0x1004280208902, 0xa51202410944400c, 0x4010a0082246])
  | 19 => (packedWords [0x90425100000008, 0x1004280209902944, 0x18004228004c20b7, 0x54312a00c024005b, 0x880022504982f52f, 0x710c4a8030811296, 0xb202410944408c00, 0x4312a00c2244a5, 0xec80000000000000, 0x8790c4a803099129, 0x4184182402814c02, 0x1c4410e13802400, 0x9060090425110230, 0x1104384e08908, 0xa718000000000000, 0x4410e1382642])
  | 20 => (packedWords [0x20001c, 0x11c4b84f019001ee, 0xa00000000408c005, 0xc4712e13c2046a7a, 0xe800000001023001, 0x711c4b84f099129e, 0xba02410944408c00, 0x4712e13c2644a7, 0xee80000000000000, 0x711c4b84f0991a9, 0x7ba00000000408c0, 0x1c4712e13c2646a, 0x9ee8090425110230, 0x711c4b84f0991a, 0xa7be02410944408c, 0x4712e13c2646])
  | 21 => (packedWords [0x809042511023001c, 0x11c4b84f09d1a9ee, 0xa02410944408c007, 0xc4712e13c6646a7b, 0xe9ffcd25b5223041, 0x711c4b84f1991ebe, 0xfa02410944408c00, 0x1c47baf33c36c6a7, 0xfeef9d4af1522384, 0x711eebccf0db1eb, 0x7fa02410944408c0, 0x3d47baf33c37c6a, 0x9fe8092675598234, 0x68591eebccf0df1a, 0x340c0000000050bc, 0x4c11e5792052])
  | 22 => (packedWords [0x80904251306b281c, 0x13c4f95f5995adee, 0xe02410944408c007, 0xd4f13e57d6756b7b, 0xe8f9c42517aeb2d5, 0x93eefddf5df5ade, 0x11c18662a814420a, 0xa27014a0880a410d, 0x4100022504840452, 0x9c0528220a1029, 0xd144182402810000, 0xa07014a0882a41a, 0xb5460032da48000c, 0x1785c0528220a906, 0xaff3bc3cb6932a03, 0x73beb28c3fc5])
  | 23 => (packedWords [0x4a00bd6, 0x9dc5b86f021001ea, 0x9fdb662a91ec23f7, 0xf7716e1bc0e410fb, 0xeff6fbdaedfbfdff, 0x71dc5b86f0b916be, 0xba02410944408c00, 0xde7716e1bc2e47af, 0xeefffddafb57b38f, 0x79dc5b86f0b91eb, 0xfbe43c3496c508c0, 0xbc7716e1bc2e47a, 0xbfee0936ff59023c, 0x1471dc5b86f0b91e, 0xafba3e7109454a8c, 0x7716e1bc2f47])
  | 24 => (packedWords [0xff6fbdaecfb0cfff, 0x5defbcef07f163fe, 0xbbc3cb6932a03178, 0xd77bef3bc3fc7aff, 0xeef9f6ff5daa3c5f, 0x9defbcef0ff1ebf, 0x1c7db240291a0034, 0xf77c15e5f96f53bf, 0xeb800225049caf5b, 0xffdfc5f97f4a55ad, 0x7be02499d5672bd6, 0xfff7f17e5fd2f56b, 0xfefff6fbdaedfbfd, 0x3f79fc5f97f4bd5e, 0x1fbdfdb662a91ec2, 0x7f17e5fd4f53])
  | 25 => (packedWords [0x9f6eb50edeaf5ff7, 0x9fc5f97f5b55efeb, 0xe7db240291a00340, 0xe7f17e5fd6f57bfb, 0xf9ffcd25b56a30d1, 0xddfc5f97f5bd5efe, 0xefbc3cb6937abf7f, 0xdf7fbff7fd3dd7bf, 0xeefffddafb7ffbaf, 0xffdfeffdff57f5c7, 0x7ae3e799d57fbbdf, 0xdff7fbff7fd7dd6b, 0xfffffffffffdea3c, 0x1feffdff5ff5e, 0x4040000000000000, 0x804008028028])
  | 26 => (packedWords [0x0, 0x20100200a00a1011, 0x1c18662a80442000, 0x8804008028229485, 0x470f1dafb0110800, 0x820100200a18a521, 0x4400089412001140, 0x2080400802a028e0, 0x1180926755900750, 0x820100200a80bb8, 0x855c18ef6ba04534, 0x880400802a229e, 0x410f0d25b21502, 0x10020100200b08a1, 0x4851fdb662a90c42, 0x80400802c629])
  | 27 => (packedWords [0x0, 0x203a0680a42a1010, 0x24109448100800, 0x80e81a0290a8404, 0x600108a02150a00, 0x8603a0680a42a101, 0x41800cb692a573cb, 0x880e81a0290a840, 0x1460914af12150a0, 0x203a0680a4aa10, 0x851c18662a804420, 0x880e81a0292a94, 0x21470f1dafb2150a, 0x100203a0680a4aa5, 0x4841bc3422810802, 0x80e81a0294a9])
  | 28 => (packedWords [0x60914af12150a008, 0x203a0680a5aa1014, 0x1be752bc58d42902, 0x80e81a0296a9485, 0x47f6d98aa4310840, 0x2203a0680a5aa521, 0x51fff76bed0c4210, 0x880e81a0296a948, 0x147ffddafb6350a4, 0x8603a0680a5aa52, 0x4202499d56e13dc, 0x2180e81a02b0ace, 0x8118002250488045, 0x800203a0680ac6b3, 0x4040000000008100, 0x80e81a02d0a8])
  | 29 => (packedWords [0x90425120402000, 0x203a0680b42a1010, 0x4024109448100800, 0x80e81a02d0a8404, 0x10f0d25b2040200, 0x203a0680b42a521, 0x4182452bc4810280, 0x80e81a02d0a948, 0x107f6d98aa6350a4, 0x203a0680b42a52, 0x841fff76bed8d429, 0x80e81a02d0a94, 0x100090425120402, 0x800203a0680b42a9, 0xc042024109448100, 0x80e81a02d0ac])
  | 30 => (packedWords [0x90425120402000, 0x603a0680b46a1010, 0x202499d56a101808, 0x80e81a02d1acc04, 0x4009042512040200, 0x2203a0680b4aa101, 0x5043c3496c854080, 0x880e81a02d2a840, 0x1460914af12150a0, 0x2203a0680b4aa10, 0x51c3c76bec85428, 0x80e81a02d2a84, 0x21470f1dafb2150a, 0x900203a0680b4aa5, 0x4851fdb662a98d42, 0x80e81a02d2a9])
  | 31 => (packedWords [0x7ffddafb6350a408, 0x203a0680b4aa5214, 0x24109448100800, 0x880e81a02d4a8404, 0xf9c42516240240, 0x203a0680b52a101, 0x403e710945890090, 0x80e81a02d4a948, 0x101ffcd25b624024, 0x203a0680b52a52, 0x841be752bc589029, 0x40080e81a02d4a94, 0x2107f6d98aa6350a, 0x900203a0680b52a5, 0x4841fff76bed8902, 0x80e81a02d4a9])
  | 32 => (packedWords [0x7ffddafb6350a408, 0x203a0680b52a5210, 0x24109448100802, 0x880e81a02d6a8405, 0x46f9d4af16350a40, 0x2203a0680b5aa101, 0x507ff3496d890090, 0x880e81a02d6a948, 0x146f9d4af16240a4, 0x2203a0680b5aa52, 0x851c3c76bec85428, 0x40080e81a02d6a94, 0x2147f6d98aa43108, 0x902203a0680b5aa5, 0x4851fdb662a98d42, 0x80e81a02d6a9])
  | 33 => (packedWords [0x7ffddafb6350a400, 0x203a0680b5aa5214, 0x1fff76bed8d42902, 0x880e81a02d6a9485, 0x57ffddafb6350a40, 0x2203a0680b5aa521, 0x51fff76bed8d4290, 0x880e81a02d6a94a, 0x547ffddafb6350a4, 0x2203a0680b5aa72, 0x851fff76bed8d429, 0x40880e81a02d6ab4, 0x214fffddafb6350a, 0x902203a0680b5ab7, 0x4851fff76bed8d42, 0x80e81a02d7a9])
  | 34 => (packedWords [0xffffffffeb50e429, 0x203a0680b5eb7214, 0x24109448100800, 0x80e81a02f0a8e04, 0x100926755a044702, 0x203a0680bc2a381, 0x4202410944c10c80, 0x880e81a02f0aee0, 0x147ffddafb6350a4, 0xa203a0680bdaa7a, 0x855ffffffff8d53d, 0x40880e81a02f6a9e, 0xa14fffddafb7353a, 0x800203a0680bdabf, 0xc3e2024109448100, 0x83ea1a06d4ac])
  | 35 => (packedWords [0xfffddafb6350a408, 0x20fa8681b5ab72fc, 0x3be752bc5c90e900, 0x883ea1a06f4afebe, 0xcfffddafb7353a40, 0x20fa8681bdabfaf, 0x4802410944810080, 0x884e85b32d4aa42, 0x967ffddafb6350a4, 0x213a16ccb5aad2, 0xa4a7ff3496dc90c9, 0x40884e85b32f4afe, 0xa96fffddafb7353a, 0xb57213a16ccbdabf, 0x4af9fff76bed8fc2, 0x87ea5b36d6a9])
  | 36 => (packedWords [0xfffddafb7373a41c, 0x21fa96cdb5abd2be, 0xbfff76bed8d42902, 0x287ea5b36d6afcbf, 0x11060900a255c3a0, 0x22104310f00e140, 0x402410944c13cc0, 0x2088410c43e03a70, 0x1100022504800450, 0x862104310f84ebc, 0x4602499d56e13dc, 0x88e91e43b1bef, 0x4110000000020402, 0xc08623a4790f46e1, 0x504400089412a131, 0x88e91e43d1b8])
  | 37 => (packedWords [0x90425120402000, 0x623a4790f46e1411, 0x402499d56a131c08, 0x88e91e43d1b8504, 0x1000000000000000, 0x223a4790f46e941, 0x4400000000810080, 0x2188e91e43d1ba50, 0x1100022504a84c70, 0x223a4790f46e94, 0x440241094481008, 0x2188e91e43d1ba5, 0x41180022504a84c7, 0xc08623a4790f46f3, 0x504602499d56e13d, 0x88e91e43d1be])
  | 38 => (packedWords [0x8090425120402000, 0x623a4790f46fb411, 0x602499d56a101808, 0x88e91e43d1bed04, 0x5009042512040200, 0x223a4790f4ee941, 0x4402410944810080, 0x888e91e43d5ba52, 0x1500904251204020, 0x2223a4790f5ee94, 0x855fff76bed8d429, 0x2188e91e43d7bb5, 0xc1100022504a84c7, 0xc08623a4790fc6e3, 0x704402499d56e13d, 0x88e91e43f1ba])
  | 39 => (packedWords [0x90425120402000, 0x223a4790fc6ebc11, 0x402499d568111c08, 0x188e91e43f1baf04, 0x180926755b84f702, 0x623a4790fc6f3c1, 0x602410944e13cc0, 0x2188e91e43f1be70, 0x1180022504880450, 0x8623a4790fc6fbc, 0x4600089412e13dc, 0x88e91e43f1bef, 0xc118090425130432, 0xc08623a4790fc6fb, 0xf04602499d56e13d, 0x88e91e43f1be])
  | 40 => (packedWords [0x80926755b84f7021, 0x623a4790fc6fbc51, 0x602499d56e13dc08, 0x188e91e43f3bef05, 0x5f0f3ffffb95ff02, 0x8623a4790fceffe1, 0x4602499d56e13dc0, 0x2188e91e43f5bef0, 0x9180926755b84f70, 0x8623a4790fd6fbc, 0x8467ffbdd7fe93dd, 0x42188e91e43f5bff, 0xe11ef9f6ff5fa4ff, 0xc0a623a4790fd6ff, 0xf05602499d56e13d, 0x88e91e43f7be])
  | 41 => (packedWords [0xfffddafb7353a408, 0x623a4790fdeffe15, 0x7ffffffffed7fd0a, 0x88e91e43f7bff85, 0x9809042512040200, 0xf62fac791f56fb4f, 0xe602499d56e1bdc1, 0x218beb1e47f1bef0, 0xf980926755b84f70, 0xa62fac791fd6fbc, 0x3f602499d56e13dc, 0x8beb1e47f7bef, 0x4930090425120402, 0xb07233a57dcf56e9, 0x5859fff76bedcdee, 0x8ce95f73d6bb])
  | 42 => (packedWords [0x7ffddafb6750ac0a, 0x233a57dcf5aed617, 0xc024109448100802, 0x88ce95f73d7ba525, 0x67ffddafb63d0ad0, 0x2233a57dcf5eed69, 0x5dfff76bed8d4290, 0x218ce95f73d7bb5a, 0x9380926755b84f70, 0xa633a57dcfd6fbc, 0x25e02499d56e13dc, 0xd5d8ce95f73f7bef, 0x6befffddafb7bfba, 0xc0f63fad7ddf5efd, 0xf2ee02499d56e1bd, 0x8feb5f77f5be])
  | 43 => (packedWords [0x8f9e6755faef7d7d, 0x63fad7ddfd6fbcbb, 0xe02499d56e13dc08, 0x28feb5f77f5bef3e, 0x17063bdae8514d2a, 0xac110220a20a521, 0x55c18662a8144200, 0xa0b04408828a2948, 0x547063bdae8110c0, 0x8ac110220a28a72, 0x844418ad43a10114, 0xa0b0440882a829e, 0xa5160032da48004d, 0x140ac110220aa0a7, 0x4a55fdb662a91e42, 0xb0ec1a829fa9])
  | 44 => (packedWords [0x10f0d25b24402002, 0x2c3b06a0b62a5211, 0x3e7109458b00940, 0x8b0ec1a82dda94a4, 0x47ffddafb6350a40, 0x2ac3b06a0b7aa521, 0x51fff76bed9f42bf, 0xab0ec1a82dea948, 0x157ffddafb6750a4, 0x2a2c3b06a0b7aa52, 0x951ffffffff8d439, 0x508b0ec1a82dea9c, 0x2947ffddafb63d0a, 0x942ac3b06a0b7ea5, 0x4a55fff76bed9f42, 0xb0ec1a82dfa9])
  | 45 => (packedWords [0xef0f2da4ca80c5e1, 0x6cfb86a1a76b72f8, 0x7bc3cb6932a03178, 0x1b3ee1a869dadcbe, 0xcff6fbdaecb90c5e, 0x86cfb86a1a7eb72f, 0xe7bc3cb6932a1357, 0xe1b3ee1a86bdadeb, 0xf8ef9f6ff5eac0e5, 0x722cfb86a1b76b72, 0xbf1fff76bed8f429, 0x508b3ee1a86dea94, 0x2fcfffddafb63d0a, 0x97a6cfb86a1b7eb7, 0xcbf3ffffffffaf43, 0xb3ee1a86dfad])
  | 46 => (packedWords [0x7ffddafb67d0ad0a, 0xad3b16ecb7aa5296, 0xdfff76bed9d42902, 0x8b4ec5bb2deab4a5, 0x67ffddafb63d0a50, 0xad3b16ecb7ead29, 0x45fdb662a99f42b4, 0xe3b8ed1ec3d9b958, 0x117f6fbdaeefdcff, 0xae3b47b0f66e56, 0x855c3c76bec95428, 0x500b8ed1ec3dbbb5, 0x6916f9d4af162c0a, 0xb42ae3b47b0f76ed, 0x5855fff76bed9f42, 0xb8ed1ec3dfb9])
  | 47 => (packedWords [0x7fffffffefdcffeb, 0xae3b47b0f7ee5615, 0x5fff76bed9d42902, 0x8b8ed1ec3dfbb585, 0x57ffddafb63d0a50, 0x86e3b47b0f7eed69, 0x4602499d56e13dc0, 0x23b8ed1ec3f9bff8, 0x1190f2f75fbc4f70, 0xf8ee3b47b0fe6ffe, 0x847ffffffffff7ff, 0xa1b8ed1ec3f9bff, 0xe51e0936ff5b84ff, 0xd486e3b47b0fe6ff, 0xfa463e799d57eb3d, 0xb8ed1ec3fdbf])
  | 48 => (packedWords [0xff6fbdaeefdcffe3, 0x6efbc7b1f76f76f9, 0x7be7dbfd7ab03978, 0x1bbef1ec7ddbfdbe, 0x9ef0f2da4ca84d5e, 0x86efbc7b1ff6ffef, 0xe7be7dbfd7eb3fd7, 0xe9bbef1ec7fdbffb, 0xfdfffffffffbdff5, 0x40aefbc7b1ffeffe, 0xa4c7db240291a003, 0xd02bc454df3cd3b5, 0x6977f6d98aa47908, 0x748af11537cf3ced, 0xfa4c7dbad43b1a11, 0xbc454df3ed3b])
  | 49 => (packedWords [0x1f6c900a46800d02, 0xaf3b57fcf76ed693, 0xc7ff3496d9b00b40, 0x2bced5ff3ddbb5a4, 0x37f6d98aa67d0ad0, 0x8ef3b57fcf76ed69, 0x4dfdbef6bbbf73ff, 0x2bced5ff3ddbb5a, 0x937ffddafb66c0ad, 0x42af3b57fcf76ed6, 0xa5c7ff3496d9b00b, 0xd02bced5ff3dfbb5, 0x6977f6d98aa47908, 0xb40af3b57fcf7eed, 0x5a5dfff76bed9f42, 0xbced5ff3dfbb])
  | 50 => (packedWords [0x7ffddafb67d0ad0a, 0xaf3b57fcf7eed697, 0xe7ff3496ddb0cb40, 0x3bced5ff3fdbffa4, 0x39ffef75ffecf7d2, 0x2af3b57fcff6ffe9, 0x5ffff76beddf4eb4, 0x2bbced5ff3ffbffa, 0x97ffffffffffdffd, 0xffef3b57fcffeffe, 0xaeffffffffffffff, 0xd0abfef5ff7ddbf5, 0x6fffffddafb67d0a, 0xb7aeffbd7fdf7eff, 0xdbffffffffffbf43, 0xbfef5ff7dfbf])
  | 51 => (packedWords [0xfffffffffecffde3, 0x2ffbd7fdff6ffefb, 0x2410944c5fcc87, 0x2c050a80aa268641, 0x51060900a0514120, 0x30142a02a89a190, 0x5000000000000000, 0xa0c050a80aa268e5, 0x5460032da48114d2, 0x30142a02a89a39, 0x5540000000000000, 0x20c050a80aa268e, 0x9550002250480045, 0x30142a02a89a3, 0xed51c18662a80442, 0xc050a80aa269])
  | 52 => (packedWords [0x90425120402000, 0x303e2e82bcba3954, 0x3c3c76becc54e800, 0x8c0f8ba0af2efed5, 0x47ffddafb6350a40, 0x2303e2e82bdba7b5, 0x53fff76bedcd4e90, 0x1cc0f8ba0af6efed, 0x7ce0914af13173a0, 0xbf70feae83acbb39, 0x5f3824dbfd6e5ffc, 0x400c3faba0eb2ece, 0xbfcff6d98aa43108, 0x9b730feae83adbb7, 0x4df1fff76bed8dc2, 0xc3faba0ed6e9])
  | 53 => (packedWords [0xfffddafb7373a41c, 0x70feae83bdbb7b7c, 0x3ffffffffedffdbf, 0x8c3faba0ef6ededf, 0xcfffddafb6350a40, 0x7b0feae83bdbb7bf, 0x59fff76bed9dc2b8, 0x1cc4f8fb3ad6e94c, 0x167ffddafb7373a4, 0x2313e3ecebdbadb, 0xf59fff76bed8d429, 0x1cc4f8fb3af6ebe, 0x9fe8090425110230, 0x731d4ba4fa99bb, 0xe7fe02410944408c, 0xc752e93ea66e])
  | 54 => (packedWords [0x809267559027503c, 0x31d4ba4fa99bb9ff, 0xbc3c76bec44ce007, 0xcc752e93ea66feff, 0xe809042511023001, 0x731febecfadbbb9f, 0xfa02410944c18c80, 0x1cc7fafb3eb6eee7, 0xfee0914af13173a0, 0xbf71febecfadbbb9, 0x7fb824dbfd6e5ffc, 0x41cc7fafb3eb6eee, 0xbfefffddafb53338, 0x90731febecfadbbf, 0x4ff9fff76bed8dc2, 0xc7fafb3ed6e9])
  | 55 => (packedWords [0x809042513063201c, 0x31febecfbdbbb9fe, 0xe02410944c18c807, 0xcc7fafb3ef6eee7f, 0xe9ffcd25b7263241, 0x731febecfbdbbfbf, 0xfbbe752bc5c98e90, 0x1cc7fafb3ef6efef, 0xfef0f1dafb3173a0, 0x731febecfbdbbfb, 0xffbfff76bedcdce9, 0x1cc7fafb3ef6efe, 0x9fe8090425130632, 0x80031febecfbdfbb, 0xf554024109448100, 0xc8f9be4bf3fa])
  | 56 => (packedWords [0x80926755b84f7021, 0x723e6f92fcffbd55, 0x602499d56e13dc0a, 0x5c8f9be4bf7fef55, 0x980926755b86f72f, 0xf72feef93fc7fbd7, 0xf602499d56e1bdc0, 0xfdcbfbbe4ff3fef5, 0x7de0936ff5b97ff2, 0x872feef93fcffbd, 0x7f602499d56e13dc, 0xa1ecbfbbe4ff7fef, 0xd0710f0d25b357f3, 0xc0f73147b5ef89e9, 0xf45e02499d56e1bd, 0xccf9ff7bf3fe])
  | 57 => (packedWords [0x90f2f75fbd7f7a3f, 0xb33e7fdefcffbd17, 0xdfff76bedddfef87, 0x1ccf9ff7bf6fb7c5, 0x780926755b84f702, 0x7b33e7fdefdffbdd, 0xbe43c3496cd5fce8, 0x35cf53ed7fe67ef7, 0xfb80926755b86f70, 0xbff3feffdffc7fbd, 0x5ffc3cffffef5ffe, 0xf5fcffbff7ff2fef, 0xdaf9ffcd25b7fff3, 0xfff73feffdffdff9, 0xf7fbbe7dbfd7efff, 0xcffbff7ff7fe])
  | 58 => (packedWords [0x809042511023001c, 0x33feffdffdffbdff, 0xe02410944c18c807, 0xdcffbff7ff7fef7f, 0xf80926755b86f703, 0x733feffdffdffbdf, 0xfffff76bedcdce90, 0x3dcffbff7ff7ffff, 0xfffffffffffb7ff4, 0x80b3feffdffdffff, 0xc144182402814504, 0x2a2f054a88aaa696, 0xb157063bdae8514d, 0x4a0bc152a22aa9a5, 0x6d15c18662a81452, 0xf054a88aaa69])
  | 59 => (packedWords [0x60032da48000c0a0, 0x3c152a22aa9a7b54, 0x1800cb69204534a8, 0xf054a88aaa69ed5, 0x47063bdae8110c0a, 0x8bc152a22aa9a7b5, 0x51c18ef6ba14534a, 0x2f054a88aaa69ed, 0x551060900a040000, 0x8bc152a22aa9a7b, 0xd54418ad43a10114, 0xa0f054a88aaa69e, 0xb5560032da48000c, 0x4283c152a22aa9a7, 0xed55800cb6920013, 0xf054a88aaa69])
  | 60 => (packedWords [0x706198aa05108002, 0xbc152a22aa9a7b55, 0x5c18ef6ba14534a8, 0x2f054a88aaa69ed5, 0x57063bdae8514d2a, 0x8bc152a22aa9afb5, 0x57c18ef6ba14534a, 0xa2f054a88aaa6ded, 0x55f0f3ffff9517d2, 0xa8bc152a22aa9bfb, 0xd55c18ef6ba14534, 0x2a2f054a88aab69e, 0xb557063bdae8514d, 0x4aabc152a22ab9a7, 0xed55c3cffffe1453, 0xf054a88aae69])
  | 61 => (packedWords [0x7063bdae8514d2a2, 0xbc152a22ab9a7bd5, 0x5fdbef6bb1e535e8, 0x2f054a88aaf69ef5, 0x57063bdae8514d2a, 0x8bc152a22ba9a7b5, 0x55fdbef6bb1c535a, 0xa2f054a88aee69ed, 0x557063bdae8514d2, 0xa8bc3f2ea2aeba7b, 0xd55c18ef6ba14534, 0x2a3f0fcba8abbe9e, 0xb55f063bdae8d14d, 0x5a8bc3f2ea2aefb7, 0xed55fdbef6bb1c53, 0xf0fcba8abee9])
  | 62 => (packedWords [0x7ffddafb6750a68a, 0xbc3f2ea2b7ba5354, 0x5c3cffffe9553ca8, 0xaf0fcba8afae9ed5, 0x57ffddafb6750a40, 0xabc3f2ea2bfba7b5, 0x55ffffffff9d53da, 0xe3f0fcba8afee9ed, 0xfdf063bdae8d94d3, 0xa8bcd5aa23aadb7b, 0xff7c18ef6ba14534, 0x2e3f356a88eae6de, 0xb7df063bdae8d14d, 0xcbffcffaea3aebb7, 0xedf7c3cffffef5ff, 0xf3feba8ebaed])
  | 63 => (packedWords [0xf063bdae8514d2a2, 0x7cffaea3afbb7bfd, 0x3bc3cb6932a03178, 0x1f3feba8ebfedeff, 0xcef0f2da4cb94d7e, 0xf7cffaea3affb7bf, 0xf3be7dbfd7efffdf, 0xe1f3feba8ebfedef, 0xfdef0f2da4ca80c5, 0x787cffaea3affb7b, 0xff7bc3cb6932a135, 0x2a2f3feba8ebfede, 0xbfdf063bdae8514d, 0x4a8fcffaea3affb7, 0xeff7c18ef6ba3453, 0xf3feba8ebfed])
  | 64 => (packedWords [0xff6fbdaecf94d7e3, 0xfcffaea3affb7bfd, 0x7ffffffffbf53dfa, 0x2f3feba8effedeff, 0x77063bdae8514d2a, 0x8bd153a6eab9afbd, 0x5dc18ef6ba14534a, 0xfef454e9baee6bef, 0xff7f6fbdaec7b4df, 0xa8bdd5ba6fab9a7b, 0xfffc18ef6ba14534, 0x2bef756e9beae6fe, 0xbfff0f3ffff9537d, 0xffffdd5ba6fab9bf, 0xeffbffffffffffff, 0xf7fefbbebeed])
  | 65 => (packedWords [0xffffffffdfb7d7ff, 0xbdffbeefaffbfbff, 0x9fff76bed9fc2bf7, 0xef7fefbbedee94ff, 0xefffddafb77f3afd, 0xfbdffbeefbfbbfbf, 0xffc3cffffed5dfca, 0x1ef7fefbbefeefef, 0xfffffddafb7773a4, 0xafbdffbeefbfbbfb, 0xfffffffffffdddfd, 0x5fdf7fefbbefeefe, 0xbfeef9f6ff5fae3e, 0x9473dffbeefbffbf, 0xeffbfff76bedcfce, 0xf7fefbbeffef])
  | 66 => (packedWords [0xfffffffffbf3e5fd, 0xfdffbeefbffbfbfe, 0x5c18ef6ba36736f8, 0x2f855accbab79fd5, 0x57063bdae8514d2a, 0x8fe156b32fadeff5, 0x55fdbef6bbbf73ff, 0xa2f8fdbecbfbf9fd, 0x5570f3ffffa554f2, 0xa8fe3f6fb2fefeff, 0xd57c18ef6ba34534, 0x2a3f8fdbecbfbfff, 0xf55f0f3ffffbd5ff, 0xdaafe3f6fb2fefff, 0xfd57fffffffffd7f, 0xf8fdbecbffff])
  | 67 => (packedWords [0xffffffffffffffff, 0xfeffefb3feff7f7d, 0x7ffffffffff7fdf8, 0x2fbffbecffffffff, 0x77063bdae8594dba, 0x8bf157b7eeadeffd, 0x5dc18ef6ba14536a, 0xbefc55edfbea7bfd, 0x5770f3ffffb57ffa, 0xc0bf157b7efa9eff, 0xe1c7db240291e507, 0xf1efc55edfbef7b7, 0xf871ffcd25b77ff3, 0x340bf157b7efbded, 0xff5c7db240291a00, 0xfc55edfbef7b])
  | 68 => (packedWords [0x7063bdae8514d2a2, 0xbf157b7efbdeffd7, 0xdfdbef6bb1e537e8, 0xffc55edfbef7bff5, 0x77ffffffffffffff, 0x2bf3f7ffefefedf1, 0x5dfff76bed9f42b4, 0xaafcfdfffbfffbff, 0xd77fffffffe7d4ff, 0xe8ff3f7ffefffeff, 0xf5fffffffffff7ff, 0xbf7fcfdfffbfffff, 0xffff063bdae9dbfd, 0xeffffd5fb7feadff, 0xf7be43cbdd7ef7fd, 0xff57edffeb7e])
  | 69 => (packedWords [0x7ffddafb77ffbfde, 0xbfd5fb7ffb9edfef, 0xfffffffff5edf7ef, 0xfff57edffef7ffff, 0xfe0936ff5bdfffbf, 0xfffffffffeeffbdf, 0xfdfdbef6bbbff3ff, 0xdeffffffffdff95f, 0xff7ffddafb67f0af, 0xfdfffffffff7fed7, 0x7ee02499d56f3bde, 0xff7fffffffff9fef, 0xffbff6fbdaefffff, 0xb47bffffffffe7ff, 0xfffe7ff3496ddb8c, 0xffffffffffff])
  | 70 => (packedWords [0x9ffef75ffeef7d3f, 0x7fffffffffffffff, 0xfbe7dbfd7eb8f97f, 0xdfffffffffffffff, 0xfef9f6ff5faeff5f, 0xfbffffffffffffff, 0xffc3cffffed5dfca, 0xbfffffffffffffff, 0xfff0f3ffffbd7ff2, 0xf8ffffffffffffff, 0xffffdbef6bb3e537, 0xd1efffffffffffff, 0xffffffddafb77f3a, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffff])
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
private theorem span3_0 : span (check 3) 37 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span3 : span (check 3) 37 0 = true :=
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
private theorem span4_144 : span (check 4) 48 144 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4_192 : span (check 4) 40 192 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span4 : span (check 4) 232 0 = true :=
  (span_join (span_join span4_0 span4_48) (span_join span4_96 (span_join span4_144 span4_192)))

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
private theorem span5_672 : span (check 5) 36 672 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span5 : span (check 5) 708 0 = true :=
  (span_join (span_join (span_join span5_0 (span_join span5_48 span5_96)) (span_join (span_join span5_144 span5_192) (span_join span5_240 span5_288))) (span_join (span_join (span_join span5_336 span5_384) (span_join span5_432 span5_480)) (span_join (span_join span5_528 span5_576) (span_join span5_624 span5_672))))

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
private theorem span6_624 : span (check 6) 37 624 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span6 : span (check 6) 661 0 = true :=
  (span_join (span_join (span_join span6_0 (span_join span6_48 span6_96)) (span_join (span_join span6_144 span6_192) (span_join span6_240 span6_288))) (span_join (span_join span6_336 (span_join span6_384 span6_432)) (span_join (span_join span6_480 span6_528) (span_join span6_576 span6_624))))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span7_0 : span (check 7) 47 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem span7 : span (check 7) 47 0 = true :=
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


end Monotone16056Lower

end

section

namespace Monotone16056Control

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.and, [2, 3]⟩,
  ⟨.or, [3, 4]⟩,
  ⟨.or, [0, 5]⟩,
  ⟨.and, [4, 7]⟩,
  ⟨.or, [6, 10]⟩,
  ⟨.and, [8, 9]⟩,
  ⟨.or, [2, 12]⟩,
  ⟨.and, [13, 11]⟩
], 14⟩

theorem monotone : Monotone2 circuit := by
  intro gate mem
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 15000000 in
theorem exactTable : ∀ x : Fin 6 → Bool,
    circuit.eval (List.ofFn x) = Monotone16056Lower.target x := by
  decide +kernel

end Monotone16056Control

end

end PEqualNP.Outside.L_meta_16055_aux

open PEqualNP.Outside.L_meta_16055_aux

open PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_16055 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4209699552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4209699552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have budget : 9 ≤ s := Monotone16056Lower.lower h
  exact ⟨Monotone16056Control.circuit, Monotone16056Control.monotone, budget,
    Monotone16056Control.exactTable⟩
