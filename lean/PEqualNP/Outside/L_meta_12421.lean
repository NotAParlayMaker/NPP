import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

-- NOT gates save nothing on this six-input function: an AND/OR circuit with 9 gates is given, and a
-- table of live-wire states, checked by the kernel, shows that no AND/OR/NOT circuit has 8 gates or
-- fewer. The checker (Run, exists_run, next, covers, bar, moves) is copied from the merged
-- PEqualNP/Outside/L_meta_8493.lean; the rows are all pairs of a zero row and a one row, and the
-- tables hold 64-bit truth tables that expand to those pairs.
namespace PEqualNP.Outside.L_meta_12421

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

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag) |||
    (w ^^^ ((w &&& tag) ||| (w &&& (tag <<< d))))

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

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
  exact Run.map _ (fun a => (move_hom tag d hz a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (move_hom tag d hz a b).1) (fun a b => (move_hom tag d hz a b).2.1) h

def applyMoves (ms : List (Nat × Nat)) (w : Nat) : Nat :=
  ms.foldl (fun acc p => moveBits p.1 p.2 acc) w

def moveOK (k : Nat) (p : Nat × Nat) : Bool :=
  (p.1 &&& (p.1 <<< p.2) == 0) &&
  (moveBits p.1 p.2 (mask k) == mask k) &&
  (moveBits p.1 p.2 (goal k) == goal k)

theorem applyMoves_run {k s} (ms : List (Nat × Nat)) (hok : ms.all (moveOK k) = true) :
    ∀ ws, NatRun (mask k) (goal k) s ws →
      NatRun (mask k) (goal k) s (ws.map (applyMoves ms)) := by
  induction ms with
  | nil =>
    intro ws h
    have e : ws.map (applyMoves []) = ws := by
      have hfn : applyMoves [] = id := funext fun _ => rfl
      rw [hfn, List.map_id]
    rw [e]
    exact h
  | cons p ps ih =>
    intro ws h
    simp only [List.all_cons, Bool.and_eq_true] at hok
    have hp := hok.1
    simp only [moveOK, Bool.and_eq_true, beq_iff_eq] at hp
    have h1 := move_run h p.1 p.2 hp.1.1 hp.1.2 hp.2
    have h2 := ih hok.2 _ h1
    have e : ws.map (applyMoves (p :: ps)) = (ws.map (moveBits p.1 p.2)).map (applyMoves ps) := by
      rw [List.map_map]
      rfl
    rw [e]
    exact h2

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

def pickMin (orig : List Nat) : List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [], best, _ => best
  | ms :: rest, best, bestH =>
    let img := orig.map (applyMoves ms)
    let h := hk img
    if h < bestH then pickMin orig rest img h else pickMin orig rest best bestH

theorem pickMin_run {k u} (orig : List Nat) (h0 : NatRun (mask k) (goal k) u orig) :
    ∀ (syms : List (List (Nat × Nat))) (best : List Nat) (bestH : Nat),
      syms.all (fun ms => ms.all (moveOK k)) = true →
      NatRun (mask k) (goal k) u best →
      NatRun (mask k) (goal k) u (pickMin orig syms best bestH)
  | [], _, _, _, hb => hb
  | ms :: rest, best, bestH, hok, hb => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    unfold pickMin
    dsimp only
    split
    · exact pickMin_run orig h0 rest _ _ hok.2 (applyMoves_run ms hok.1 orig h0)
    · exact pickMin_run orig h0 rest best bestH hok.2 hb

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (3941132456 * 2 ^ 32 + 3903383720) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 3, 3, 3, 3, 3, 5, 3, 7, 3, 3, 3, 11, 3, 13, 14, 15, 3, 3, 3, 19, 3, 21, 3, 23, 3, 3, 3, 27, 3, 29, 30, 31, 3, 3, 3, 35, 3, 37, 3, 39, 3, 3, 3, 43, 3, 45, 46, 47, 3, 3, 3, 51, 3, 53, 54, 55, 3, 57, 3, 59, 3, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 5, 5, 5, 3, 5, 5, 5, 7, 5, 5, 5, 11, 5, 13, 14, 15, 5, 5, 5, 19, 5, 21, 5, 23, 5, 5, 5, 27, 5, 29, 30, 31, 5, 5, 5, 35, 5, 37, 5, 39, 5, 5, 5, 43, 5, 45, 46, 47, 5, 5, 5, 51, 5, 53, 54, 55, 5, 57, 5, 59, 5, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 7, 7, 7, 3, 7, 5, 7, 7, 7, 7, 7, 11, 7, 13, 14, 15, 7, 7, 7, 19, 7, 21, 7, 23, 7, 7, 7, 27, 7, 29, 30, 31, 7, 7, 7, 35, 7, 37, 7, 39, 7, 7, 7, 43, 7, 45, 46, 47, 7, 7, 7, 51, 7, 53, 54, 55, 7, 57, 7, 59, 7, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 11, 11, 11, 3, 11, 5, 11, 7, 11, 11, 11, 11, 11, 13, 14, 15, 11, 11, 11, 19, 11, 21, 11, 23, 11, 11, 11, 27, 11, 29, 30, 31, 11, 11, 11, 35, 11, 37, 11, 39, 11, 11, 11, 43, 11, 45, 46, 47, 11, 11, 11, 51, 11, 53, 54, 55, 11, 57, 11, 59, 11, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 13, 13, 13, 3, 13, 5, 13, 7, 13, 13, 13, 11, 13, 13, 14, 15, 13, 13, 13, 19, 13, 21, 13, 23, 13, 13, 13, 27, 13, 29, 30, 31, 13, 13, 13, 35, 13, 37, 13, 39, 13, 13, 13, 43, 13, 45, 46, 47, 13, 13, 13, 51, 13, 53, 54, 55, 13, 57, 13, 59, 13, 61, 62, 63, 14, 14, 14, 3, 14, 5, 14, 7, 14, 14, 14, 11, 14, 13, 14, 15, 14, 14, 14, 19, 14, 21, 14, 23, 14, 14, 14, 27, 14, 29, 30, 31, 14, 14, 14, 35, 14, 37, 14, 39, 14, 14, 14, 43, 14, 45, 46, 47, 14, 14, 14, 51, 14, 53, 54, 55, 14, 57, 14, 59, 14, 61, 62, 63, 15, 15, 15, 3, 15, 5, 15, 7, 15, 15, 15, 11, 15, 13, 14, 15, 15, 15, 15, 19, 15, 21, 15, 23, 15, 15, 15, 27, 15, 29, 30, 31, 15, 15, 15, 35, 15, 37, 15, 39, 15, 15, 15, 43, 15, 45, 46, 47, 15, 15, 15, 51, 15, 53, 54, 55, 15, 57, 15, 59, 15, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 19, 19, 19, 3, 19, 5, 19, 7, 19, 19, 19, 11, 19, 13, 14, 15, 19, 19, 19, 19, 19, 21, 19, 23, 19, 19, 19, 27, 19, 29, 30, 31, 19, 19, 19, 35, 19, 37, 19, 39, 19, 19, 19, 43, 19, 45, 46, 47, 19, 19, 19, 51, 19, 53, 54, 55, 19, 57, 19, 59, 19, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 21, 21, 21, 3, 21, 5, 21, 7, 21, 21, 21, 11, 21, 13, 14, 15, 21, 21, 21, 19, 21, 21, 21, 23, 21, 21, 21, 27, 21, 29, 30, 31, 21, 21, 21, 35, 21, 37, 21, 39, 21, 21, 21, 43, 21, 45, 46, 47, 21, 21, 21, 51, 21, 53, 54, 55, 21, 57, 21, 59, 21, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 23, 23, 23, 3, 23, 5, 23, 7, 23, 23, 23, 11, 23, 13, 14, 15, 23, 23, 23, 19, 23, 21, 23, 23, 23, 23, 23, 27, 23, 29, 30, 31, 23, 23, 23, 35, 23, 37, 23, 39, 23, 23, 23, 43, 23, 45, 46, 47, 23, 23, 23, 51, 23, 53, 54, 55, 23, 57, 23, 59, 23, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 27, 27, 27, 3, 27, 5, 27, 7, 27, 27, 27, 11, 27, 13, 14, 15, 27, 27, 27, 19, 27, 21, 27, 23, 27, 27, 27, 27, 27, 29, 30, 31, 27, 27, 27, 35, 27, 37, 27, 39, 27, 27, 27, 43, 27, 45, 46, 47, 27, 27, 27, 51, 27, 53, 54, 55, 27, 57, 27, 59, 27, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 29, 29, 29, 3, 29, 5, 29, 7, 29, 29, 29, 11, 29, 13, 14, 15, 29, 29, 29, 19, 29, 21, 29, 23, 29, 29, 29, 27, 29, 29, 30, 31, 29, 29, 29, 35, 29, 37, 29, 39, 29, 29, 29, 43, 29, 45, 46, 47, 29, 29, 29, 51, 29, 53, 54, 55, 29, 57, 29, 59, 29, 61, 62, 63, 30, 30, 30, 3, 30, 5, 30, 7, 30, 30, 30, 11, 30, 13, 14, 15, 30, 30, 30, 19, 30, 21, 30, 23, 30, 30, 30, 27, 30, 29, 30, 31, 30, 30, 30, 35, 30, 37, 30, 39, 30, 30, 30, 43, 30, 45, 46, 47, 30, 30, 30, 51, 30, 53, 54, 55, 30, 57, 30, 59, 30, 61, 62, 63, 31, 31, 31, 3, 31, 5, 31, 7, 31, 31, 31, 11, 31, 13, 14, 15, 31, 31, 31, 19, 31, 21, 31, 23, 31, 31, 31, 27, 31, 29, 30, 31, 31, 31, 31, 35, 31, 37, 31, 39, 31, 31, 31, 43, 31, 45, 46, 47, 31, 31, 31, 51, 31, 53, 54, 55, 31, 57, 31, 59, 31, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 35, 35, 35, 3, 35, 5, 35, 7, 35, 35, 35, 11, 35, 13, 14, 15, 35, 35, 35, 19, 35, 21, 35, 23, 35, 35, 35, 27, 35, 29, 30, 31, 35, 35, 35, 35, 35, 37, 35, 39, 35, 35, 35, 43, 35, 45, 46, 47, 35, 35, 35, 51, 35, 53, 54, 55, 35, 57, 35, 59, 35, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 37, 37, 37, 3, 37, 5, 37, 7, 37, 37, 37, 11, 37, 13, 14, 15, 37, 37, 37, 19, 37, 21, 37, 23, 37, 37, 37, 27, 37, 29, 30, 31, 37, 37, 37, 35, 37, 37, 37, 39, 37, 37, 37, 43, 37, 45, 46, 47, 37, 37, 37, 51, 37, 53, 54, 55, 37, 57, 37, 59, 37, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 39, 39, 39, 3, 39, 5, 39, 7, 39, 39, 39, 11, 39, 13, 14, 15, 39, 39, 39, 19, 39, 21, 39, 23, 39, 39, 39, 27, 39, 29, 30, 31, 39, 39, 39, 35, 39, 37, 39, 39, 39, 39, 39, 43, 39, 45, 46, 47, 39, 39, 39, 51, 39, 53, 54, 55, 39, 57, 39, 59, 39, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 43, 43, 43, 3, 43, 5, 43, 7, 43, 43, 43, 11, 43, 13, 14, 15, 43, 43, 43, 19, 43, 21, 43, 23, 43, 43, 43, 27, 43, 29, 30, 31, 43, 43, 43, 35, 43, 37, 43, 39, 43, 43, 43, 43, 43, 45, 46, 47, 43, 43, 43, 51, 43, 53, 54, 55, 43, 57, 43, 59, 43, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 45, 45, 45, 3, 45, 5, 45, 7, 45, 45, 45, 11, 45, 13, 14, 15, 45, 45, 45, 19, 45, 21, 45, 23, 45, 45, 45, 27, 45, 29, 30, 31, 45, 45, 45, 35, 45, 37, 45, 39, 45, 45, 45, 43, 45, 45, 46, 47, 45, 45, 45, 51, 45, 53, 54, 55, 45, 57, 45, 59, 45, 61, 62, 63, 46, 46, 46, 3, 46, 5, 46, 7, 46, 46, 46, 11, 46, 13, 14, 15, 46, 46, 46, 19, 46, 21, 46, 23, 46, 46, 46, 27, 46, 29, 30, 31, 46, 46, 46, 35, 46, 37, 46, 39, 46, 46, 46, 43, 46, 45, 46, 47, 46, 46, 46, 51, 46, 53, 54, 55, 46, 57, 46, 59, 46, 61, 62, 63, 47, 47, 47, 3, 47, 5, 47, 7, 47, 47, 47, 11, 47, 13, 14, 15, 47, 47, 47, 19, 47, 21, 47, 23, 47, 47, 47, 27, 47, 29, 30, 31, 47, 47, 47, 35, 47, 37, 47, 39, 47, 47, 47, 43, 47, 45, 46, 47, 47, 47, 47, 51, 47, 53, 54, 55, 47, 57, 47, 59, 47, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 51, 51, 51, 3, 51, 5, 51, 7, 51, 51, 51, 11, 51, 13, 14, 15, 51, 51, 51, 19, 51, 21, 51, 23, 51, 51, 51, 27, 51, 29, 30, 31, 51, 51, 51, 35, 51, 37, 51, 39, 51, 51, 51, 43, 51, 45, 46, 47, 51, 51, 51, 51, 51, 53, 54, 55, 51, 57, 51, 59, 51, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 53, 53, 53, 3, 53, 5, 53, 7, 53, 53, 53, 11, 53, 13, 14, 15, 53, 53, 53, 19, 53, 21, 53, 23, 53, 53, 53, 27, 53, 29, 30, 31, 53, 53, 53, 35, 53, 37, 53, 39, 53, 53, 53, 43, 53, 45, 46, 47, 53, 53, 53, 51, 53, 53, 54, 55, 53, 57, 53, 59, 53, 61, 62, 63, 54, 54, 54, 3, 54, 5, 54, 7, 54, 54, 54, 11, 54, 13, 14, 15, 54, 54, 54, 19, 54, 21, 54, 23, 54, 54, 54, 27, 54, 29, 30, 31, 54, 54, 54, 35, 54, 37, 54, 39, 54, 54, 54, 43, 54, 45, 46, 47, 54, 54, 54, 51, 54, 53, 54, 55, 54, 57, 54, 59, 54, 61, 62, 63, 55, 55, 55, 3, 55, 5, 55, 7, 55, 55, 55, 11, 55, 13, 14, 15, 55, 55, 55, 19, 55, 21, 55, 23, 55, 55, 55, 27, 55, 29, 30, 31, 55, 55, 55, 35, 55, 37, 55, 39, 55, 55, 55, 43, 55, 45, 46, 47, 55, 55, 55, 51, 55, 53, 54, 55, 55, 57, 55, 59, 55, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 57, 57, 57, 3, 57, 5, 57, 7, 57, 57, 57, 11, 57, 13, 14, 15, 57, 57, 57, 19, 57, 21, 57, 23, 57, 57, 57, 27, 57, 29, 30, 31, 57, 57, 57, 35, 57, 37, 57, 39, 57, 57, 57, 43, 57, 45, 46, 47, 57, 57, 57, 51, 57, 53, 54, 55, 57, 57, 57, 59, 57, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 59, 59, 59, 3, 59, 5, 59, 7, 59, 59, 59, 11, 59, 13, 14, 15, 59, 59, 59, 19, 59, 21, 59, 23, 59, 59, 59, 27, 59, 29, 30, 31, 59, 59, 59, 35, 59, 37, 59, 39, 59, 59, 59, 43, 59, 45, 46, 47, 59, 59, 59, 51, 59, 53, 54, 55, 59, 57, 59, 59, 59, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 61, 61, 61, 3, 61, 5, 61, 7, 61, 61, 61, 11, 61, 13, 14, 15, 61, 61, 61, 19, 61, 21, 61, 23, 61, 61, 61, 27, 61, 29, 30, 31, 61, 61, 61, 35, 61, 37, 61, 39, 61, 61, 61, 43, 61, 45, 46, 47, 61, 61, 61, 51, 61, 53, 54, 55, 61, 57, 61, 59, 61, 61, 62, 63, 62, 62, 62, 3, 62, 5, 62, 7, 62, 62, 62, 11, 62, 13, 14, 15, 62, 62, 62, 19, 62, 21, 62, 23, 62, 62, 62, 27, 62, 29, 30, 31, 62, 62, 62, 35, 62, 37, 62, 39, 62, 62, 62, 43, 62, 45, 46, 47, 62, 62, 62, 51, 62, 53, 54, 55, 62, 57, 62, 59, 62, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1517175717571757151717571757175715171757175717570000000000000000151717571757175700000000000000001517175717571757000000000000000015171757175717571517175717571757151717571757175700000000000000001517175717571757000000000000000000000000000000000000000000000000151717571757175715171757175717571517175717571757000000000000000015171757175717570000000000000000000000000000000000000000000000001517175717571757000000000000000015171757175717570000000000000000151717571757175700000000000000000000000000000000000000000000000015171757175717571517175717571757151717571757175700000000000000001517175717571757000000000000000000000000000000000000000000000000151717571757175700000000000000001517175717571757000000000000000015171757175717570000000000000000000000000000000000000000000000001517175717571757151717571757175715171757175717570000000000000000151717571757175700000000000000000000000000000000000000000000000015171757175717570000000000000000151717571757175700000000000000001517175717571757000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a80000000000000000eae8e8a8e8a8e8a80000000000000000eae8e8a8e8a8e8a80000000000000000eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a80000000000000000eae8e8a8e8a8e8a8000000000000000000000000000000000000000000000000eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a80000000000000000eae8e8a8e8a8e8a8000000000000000000000000000000000000000000000000eae8e8a8e8a8e8a80000000000000000eae8e8a8e8a8e8a80000000000000000eae8e8a8e8a8e8a8000000000000000000000000000000000000000000000000eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a80000000000000000eae8e8a8e8a8e8a8000000000000000000000000000000000000000000000000eae8e8a8e8a8e8a80000000000000000eae8e8a8e8a8e8a80000000000000000eae8e8a8e8a8e8a8000000000000000000000000000000000000000000000000eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a80000000000000000eae8e8a8e8a8e8a8000000000000000000000000000000000000000000000000eae8e8a8e8a8e8a80000000000000000eae8e8a8e8a8e8a80000000000000000eae8e8a8e8a8e8a8000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8eae8e8a8e8a8e8a8

def cMZZ : Nat := 0x1517175717571757000000000000000015171757175717570000000000000000151717571757175700000000000000000000000000000000000000000000000015171757175717570000000000000000151717571757175715171757175717571517175717571757000000000000000000000000000000000000000000000000151717571757175700000000000000001517175717571757151717571757175715171757175717570000000000000000151717571757175700000000000000001517175717571757000000000000000015171757175717571517175717571757151717571757175700000000000000000000000000000000000000000000000015171757175717570000000000000000151717571757175715171757175717571517175717571757000000000000000015171757175717570000000000000000151717571757175700000000000000001517175717571757151717571757175715171757175717570000000000000000000000000000000000000000000000001517175717571757000000000000000015171757175717571517175717571757151717571757175700000000000000001517175717571757000000000000000015171757175717570000000000000000151717571757175715171757175717571517175717571757

def expandAB (w A B : Nat) : Nat :=
  ((A &&& cMZx) ||| (B &&& cMOZ) ||| ((w &&& 1) * cMOO)) |||
    (((B &&& cMxO) ||| (A &&& cMOZ) ||| (((w >>> 63) &&& 1) * cMZZ)) <<< 4096)
def expand (w : Nat) : Nat :=
  expandAB w (((((w &&& 4294967295) * cMC) &&& cSM) ||| ((((w >>> 32) * cMC) &&& cSM) <<< 2048)) *
    18446744073709551615) (w * cRR)
def xsG : List ℕ := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00,
  0xffff0000ffff0000, 0xffffffff00000000].map expand
theorem rowsG_len : rowsG.length = 8192 := by decide +kernel
theorem enc_inputsG :
    (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel
theorem enc_goalG : encL fG rowsG = goal 4096 := by decide +kernel
theorem maskG : mask 4096 = 2 ^ rowsG.length - 1 := by rw [rowsG_len]; simp [mask, lo]
theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 4096 zs &&& lo 4096) ≠ lo 4096 := by decide +kernel
theorem no_subG (noRunFull : ∀ s ≤ 8, ¬ NatRun (mask 4096) (goal 4096) s xsG) :
    ∀ s ≤ 8, ∀ zs : List ℕ, zs.Sublist xsG → NatRun (mask 4096) (goal 4096) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)
theorem mainG (noRunFull : ∀ s ≤ 8, ¬ NatRun (mask 4096) (goal 4096) s xsG) :
    ¬ HasCircuitSize 6 fG 8 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run fG ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 8 h
  have hr : NatRun (mask 4096) (encL fG rowsG) s' (ws.map fun a => encL a rowsG) :=
    Run.map (fun a : BFn 6 => encL a rowsG)
      (fun a => by rw [maskG]; exact encL_inv a rowsG)
      (fun a b => encL_and a b rowsG) (fun a b => encL_or a b rowsG) hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 3 => 6
  | 4 => 138
  | 5 => 399
  | 6 => 273
  | 7 => 27
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 3, 0 => 0xc758a13086037d6b83f60f784b881bad1f01c5e71c48926c
  | 4, 0 => 0x426344f34157281e4145fad83e169efc3d7d8a973c2904ba384fc30637f39f213766055a3673cff135aba837358755ba34f06d6a2f28418c2d8114e02cfe2a512c96741c2bf6e9cb2adb6cd12a20964428f9636228dc5f7728a9b82227845442272b0d7a271c8ada2583b8c0244f4452235928da22dfd00121b359fc216c31ce2102b9c01f1f43e71df391cb1c64368d1c507f081abc39a61851c200173d2bf016ea7c801583db95140328a213eb4e5813e4bf1412d4fd3411f31df50ffec7810fae80220e5a62db0b16e29b0a39291809a466ed0868802108518e65080ae6040801b0f607469cbe0454d11803e36131031924be02a28e6e021e3863019a7d21
  | 4, 1 => 0xd6700d62d5d0d11cd459e962d11c1378cf95193bce2b31a1bf5b1634b8f5cc90b7d3f262b272bb57b2552541b2452729b1c1e5eeaae133d0a9afadeba7db8b8aa51737d79f2201ae9eca89e69e47f3739a2fb1b699fad7c19620015891b077ca89cfdae988248b768536f62681146b0d810434a57f2637ed7c2cb8747b383d9f7788aa517708eb61769c15ec7611fde8734b447a7294a3a9729119b4723d37086fcae8126e4fcc256df513c86cd8f0ad6c96ece26971e8586707155d6658a79e61f12a325c57950a5c086c5e5aed86785a5b41365922f73a5859d8e2558922e25581025b50e0fa9f4ef175d64cab48c249d87fcb4518de5543abd2b843657b91
  | 4, 2 => 0xfd44b4a5f900a221f0178ffaedc7949fecedd4ffe6d8b88ae1f78519df881045db3848b4da9db7b2
  | 5, 0 => 0x13266a8e1323247212bef48612b330b811ce2ec71169677110ce0ac2109eef0810016ae30f92e2770f73ef2e0f67db230f0a76a10e6f8f6f0dd914420da5eb6b0d3c735d0cfea3d70cb77c860c1e46ad0aa55d4d0a9e230009fefdbb09b7106c093932a80926084208f3191908913ade088ff3f308518e65081c8df207d2023b077ccf57076d93890759d8ff073cd29506e7286706652ca1064977680643af68063c816a05df712b05160503047bc699047a63b9046548e90454d11803fc5afa03b40d6b035cc6e50324361d02f8e78a02aa410d029e8c69028bdd22024b20600242327e021e295201bd9532019a7d210176f21c0160a83100fd2ba700d7f1a7
  | 5, 1 => 0x2a50589929b74434299d68fa29758254296de61028fc68932862be5728280461272d737d261607de25c576ef25b62d422527350b24c9469024a7868324a0ff7a242d58be239fbef722f293e822e6e3fd22854b1121373262212686c8206834201eee00111ee42b531ed5030d1d8c7a941cbd2cd61c5dac521c51236a1c2ce67a1c29cb431bd683ae1bb614681bacbfbc1b61fb291b38856d1aa9a6d719e1679919bace7d1948a49e185b9ccf183ca19c1830a36818055c3717bf396c17a6f166173d2bf0171782501710e83f16ea7c80169c3d11165a4fe115f339e515331cff1513de2614e371bf14a61544148f18b813a730671364c717134a5a8c13347ffd
  | 5, 2 => 0x406e00d440614c68403b8ae13fc4bbec3fa2f6a13f8170b03e3051ff3d8e20783d6c6eaf3cda058a3cd01db03cafc1b03c68364a3c5155f73b4586423b38f11e3b2b2f733aca3de93a547a1b3a3ecb8d39f7545039ef5b7d39c7daee37d284af37abf90a3774c49736909a0d358cce9035698e3034d4c40e349061e5346f7ceb3411367933f2c40433a6f52133a69dc73326774e331524c1328e90fd323ef8933214c85231c9f02031c3ec1f3135ca4631096da9303fe1042fe58c552fc5cb612fbbd0962faf4e3a2faed2c82f9f352e2ef390312ebbb72f2e88eb1a2e80dd7e2d8241392d7fb4752d09b2db2cff56e62cc02b8a2c58a9d62c170a732c02fbec
  | 5, 3 => 0x5c086c5e5c05957c5bbf32b65b7291615b58115c5b24f1cd5a2ecd6559931885586b10af582274cd578b10395771762757671401574eadd2566d47425596f88e5581025b553dc35252bd22f25292613b526ff5345176941e505482ba4fae82af4f4fc3d34ed1fcad4e1904ff4e0152544df279cb4de94f594d7b42724d186f8e4cd7b1274c5bf4f04ba5bf844b9a1dd24b6fb4994b5f2a644b4aa1ea4b338fdb49d87fcb49a5c5204961f52548f8812f48e9e78648914ea7484225fb47e249e4474b85de4721675046d74439468976a44681d09d461009e145df3f2a4524959f44c5c8794466ce0f43f3eace43f3d8b243e2c84241f5559741babbf841642c38
  | 5, 4 => 0x7ef16ed57e669b667e37b8997e2ce17a7dea31677db4b2007d67b3d47cf67fbc7c9435097c8880527bd379027b8980e87b2c387b7b0bf9ee79d2255278fde0be78a126f3765f51e574a98ed2747c8a377469fafa72db2b2a7294a3a97226cf747211049c7170afc370b2307870a353cc7030185a6df0ca036d4e24aa6cd7005a6c5b9c936c3ca3856be92dc56b7af51e6b479a916afe48106aa075b66a88852c6a61cd2369bbfe8e69648590690396d06866721166e9bdb866b37ac16658a79e65dda5d3652bde0261d24a9c61400d1f60b7ff53602b60265f84fe175f4692ea5edfb8d15ece5d465ea557785dd3d86c5dbf65c85d1c51585d01b02b5c33ad1c
  | 5, 5 => 0xdd5c59a3da9db7b2da3e13f4d5d0d11cd3127227c804e97cc6d7714fc6b732c2bf218209bf17dddcbed04506bd5c405abd55cd15bc830b74bbced2d8ba539c93b9358872b8062a7bb5d02fcbb01f698aadfa97cbadd3d384ad721265ad54e8d2ad018bf0aae133d0a98b9685a7c92e0aa64966e9a45130b4a41ed9a6a38bef38a272c78b9f18fe8a9eb5d9649e7ee0c69bf44a289bb3b3739ae388339961e540993c1a47987558b39799392e95e427a49506a0cb9415f2c4928deb3791b077ca91ab1fc990cfce738ca59d748b5f173b8a81ad1089231e20890e19e0870bd77286696b5385c2df51854801ce8536f62684ff57a28394bf52828605e2809e5cca
  | 5, 6 => 0xf88ef632f7777fadf2dc13d6f1e885aaf1c135d6f12364b8ef52de56ecf34760eb1c6152e618b346e53a5bbee326559ce2d9c71ee20281c4e1f78519
  | 6, 0 => 0x21c6882d21a347cd20a9368820a2c1e2208579442078188c1fe0aebe1fe057641f4ede5e1df6349d1d6f83e31d4327461c29cb431bf58a331be907d71b2d49ce1939108318648844183cb5891710e83f15d7229715a79fad15362230150b0b0014a61544148f18b81461bdfe134a5a8c12ea6b48124fc17b1160eea81131d4951103002d0f4b60690f44a5c40f2c4d850e0174320dd914420d6040650cfea3d70cfba4c20ca1edbd0c0975e70b47c0830b2ef67f0b1de4f00afd132008f6e67308f31919088ff3f30866a017086384e007efce05075d64df06e360740415379703fc5afa034aa1dc0324361d02f4684a02aa410d022cf38200dfcee1002a417b
  | 6, 1 => 0x435dfdb543437db0431159ff42a700df41d0b22b41babbf83f3a1a263f3342883ef6dc8f3ea9aed13d6c6eaf3cda058a3be83c4c3b7208fc3a88db023a52be9c3a3b0bf13a2c33683a2308f639d79e5837ec235537df792137d3d76f3798e40137845b8737477b4b3604715335323acc3523a12333360e3e3310fdd632c3304132536eb13249c37e315e4f3c30ff821630d553da30a087ac302da46b2d09b2db2c9b06052c170a732bfe75892bdcb03e2bbb2a4d29d0032629b19ee929a6284c299c9aa9297582542913bf2728fc6893288b0f942772aabb2703f7862678852a26310ded2629151a261607de25a1b57f2557db0324c571de24960ef32353a4f7
  | 6, 2 => 0x70a353cc6fce78ef6cd816676b7af51e6ab090826aa075b669ee6b9d69a16d7168cdeea668c239ef677dacc166f54aa9660bdeef60b643d460a3b4975ffcc4c75fa65ea55f14e4c75edfb8d15ece5d465e20fa955cdd0d695b7291615b58115c59c4093b58d80d6958765d225822e76257b4aebb5781542e5778975b574eadd2573801ad56da2f5356c23ec956a1914f5581025b553d506d54d325bb5323775552ed345e5292613b525e788b5165979f4fa3671b4e6c0f934e1904ff4ced32414b804c874b4aa1ea4adf11154a0d9209493b69c848e9e78647ac4afe4791caf9474f8c9e45ccd22245b4b52b44dfb17d44a4ca4c43c4c9d643a0cd9e4388676f
  | 6, 3 => 0xc3a02790bf17dddcb9fd9899b9358872b8e249d0b7b97ce6b6ea257ab5349608b43ea319b153be56ab66a92eab5b3ba6a91e74b7a8bcc511a8691a8aa56f420fa45130b4a436a215a338c1d19e053ab79c5923279ae388339a34516899abcc02998ea26f993b458d924fb69f90cfce73908aea51905893438fc5a8d58f716b868eac81288e4f2d9d8c3568958b52b8278aef930189231e20890e19e0882e03c587ed6d10871d41d085ec41a5859b9edd8575d3e4854801ce8511263384af125083d2f2cb83b4d6658291028d81405a68804fac617f9d7bee7dea31677de4d9667d67b3d47798d0d877806f85755cd7bd7547d37d747c8a377345910f7166217b
  | 6, 4 => 0xff602426f4c9ad8bf1c135d6eee3faa5e5cb893de4c8afcfe3b1394ae326559ce20281c4ddfaef73dd5d1e55d92d00fdd7e0a169d7561aefcf600f39ce3c3b61c6d7714f
  | 7, 0 => 0xf4c9ad8bddfaef73d7e0a169ce3c3b61908aea51871d41d0755cd7bd7547d37d69a16d7160b643d45cdd0d6957b4aebb5581025b4388676f41babbf83d6c6eaf3a52be9c3523a1232913bf272078188c15362230124fc17b0f4b6069086384e0034aa1dc02f4684a00dfcee1
  | 8, 0 => 0x41babbf8
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f0f0f0f00000f0f00000f0f00000aaaaaaaaaaaa0000555555555555000055550000555500003333333333330000333300003333000000ff00ff00ff000000ff000000ff00000000ffffffff00000000ffff000000000000ff00ff0000000000aaaaaaaa000000000f0f0f0f000000000000ffff0000000000000000
  | 0, 1 => 0x505050505050505030303030303030300ffffffffffffff00ffffff00ffffff00ff00ff00ff00ff00ff00ff0000000000ff00000000000000f000f000f000f000aa00aa00aa00aa00550055005500550033003300330033000f000f000f000f0000ffffffffffff0000ffff0000ffff0000ffff000000000000ff00ff00ff00
  | 0, 2 => 0x44444444444444443f3f3f3f3f3f3f3f33ff33ff33ff33ff33ff000033ff00003333333333333333333300003333000033330000000000003300ff00ff00ff00330033003300330030303030303030300fff0000000000000f0fffffffffffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f000000000a0a0a0a0a0a0a0a
  | 0, 3 => 0x88888888888888888888000088880000808080808080808077777777000000005f5f5f5f5f5f5f5f5f5f0000000000005f005f005f005f0055ff55ff55ff55ff5555ffffffffffff55555555ffffffff555555555555555555555555000000005555000055550000555500000000000055005500550055004c4c4c4c4c4c4c4c
  | 0, 4 => 0xaaaa8888aaaa8888aaaa888888888888aaaa0000aaaa0000aaaa000000000000aaa8aaa8aaa8aaa8aaa0aaa0aaa0aaa0aa88aa88aa88aa88aa00ff00ff00ff00aa00aa00aa00aa00aa000000aa000000aa00000000000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a0a0a000000000a0a0000000000000a000a000a000a000
  | 0, 5 => 0xc000c000c000c000bbbbbbbbbbbbbbbbafafafafafafafafaaffaaffaaffaaffaaff0000aaff0000aaff000000000000aaaaffffffffffffaaaaffffaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaa00000000aaaaaa00aaaaaa00aaaaaa00aa00aa00aaaaa8a8aaaaa8a8aaaaa8a8a8a8a8a8aaaaa0a0aaaaa0a0
  | 0, 6 => 0xcccccccccc88cc88cccccccc00000000cccccc88cccccc88cccccc88cc88cc88cccccc00cc00cc00ccccc8c8ccccc8c8cccc8888cccc8888cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0cc00cc00cc00cc00c8c8c8c8c8c8c8c8c0c0c0c0c0c0c0c0c0c00000c0c00000c0c0000000000000
  | 0, 7 => 0xececececececececececcccccccccccceccceccceccceccceaeaeaeaeaeaeaeaeaeaeaea00000000eaeaaaaaaaaaaaaaeaea000000000000eaaaeaaaeaaaeaaaea00ea00ea00ea00e8e8e8e8e8e8e8e8e0e0e0e0e0e0e0e0ddddddddddddddddcfcfcfcf00000000ccffccffccffccffcccccccccccccccccccccccccccc0000
  | 0, 8 => 0xf000f000f000f000f000f00000000000f0000000f0000000f000000000000000eeeeeeeeeeeeeeeeeeeeeeee00000000eeeecccccccccccceeeecccc00000000eeeeaaaa00000000eeee0000eeee0000eeee000000000000eecceecceecceecceecccccccccccccceeaaeeaaeeaaeeaaee00ee00cc00cc00ee00cc00ee00cc00
  | 0, 9 => 0xf1f1f1f1f1f1f1f1f0f0fffffffffffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f000000000f0f0f0a0f0a0f0a0f0f0f000f000f000f0f0e0e0e0e0e0e0f0f0c0c0f0f0c0c0f0f0c0c0c0c0c0c0f0f0a0a0f0f0a0a0f0f0a0a0a0a0a0a0f0f00000f0f00000f0f0000000000000f0a0f0a0f0a0f0a0
  | 0, 10 => 0xfafaf0f0fafaf0f0fafaaaaafafaaaaafafaaaaaaaaaaaaafafa0000fafa0000fafa000000000000faf0f0f0f0f0f0f0faf00000faf00000faf0000000000000fa00fa00fa00fa00fa00f000f000f000f8f8f8f8f8f8f8f8f8f8f0f0f8f8f0f0f8f0f8f0f8f0f8f0f3f3f3f3f3f3f3f3f3f3000000000000f300f300f300f300
  | 0, 11 => 0xff00000000000000fefefefefefefefefefe0000fefe0000fefe000000000000fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0fcfcfcfc00000000fcfcf0f0f0f0f0f0fcfcccccfcfcccccfcfc000000000000fcf0fcf0fcf0fcf0fc00fc00fc00fc00fafafafafafafafafafafafaf0f0f0f0fafafafa00000000
  | 0, 12 => 0xff00ff00cc00cc00ff00ff00c000c000ff00ff00aa00aa00ff00ff0055005500ff00ff0000000000ff00fc00fc00fc00ff00fa00fa00fa00ff00f000ff00f000ff00f000f000f000ff00ee00ff00ee00ff00cc00ff00cc00ff00cc00cc00cc00ff00c000c000c000ff00aa00aa00aa00ff00550055005500ff000000ff000000
  | 0, 13 => 0xff550000ff550000ff55000000000000ff33ff33ff33ff33ff0cff0cff0cff0cff05ff05ff05ff05ff00ffffffffffffff00ffffff00ffffff00ffaaffaaffaaff00ff33ff33ff33ff00ff00ffaaffaaff00ff00ff33ff33ff00ff00ff00ff00ff00ff00ff00f000ff00ff00ff000000ff00ff00fc00fc00ff00ff00f000f000
  | 0, 14 => 0xffc0000000000000ffaaffaaffaaffaaffaaffaaff00ff00ffaaffaaaaaaaaaaffaaff00ff00ff00ffaaaaaaaaaaaaaaffaa0000ffaa0000ffaa000000000000ffa8ffa8ffa8ffa8ffa0ffa0ffa0ffa0ffa0ff00ff00ff00ff88ff88ff88ff88ff88ff00ff88ff00ff80ff80ff80ff80ff55ff55ff55ff55ff55ff00ff00ff00
  | 0, 15 => 0xfff00000f0f00000fff0000000000000ffee000000000000ffccffccffccffccffccffcc00000000ffccff88ff88ff88ffccff00ff00ff00ffccf000f000f000ffccccccffccccccffccccccccccccccffcc0000ffcc0000ffcc0000ff000000ffcc000000000000ffc0ffc0ffc0ffc0ffc0ff00ff00ff00ffc00000ffc00000
  | 1, 0 => 0xffff000000ff0000ffff0000000f0000ffff000000000000fffcfffcfffcfffcfffcff00ff00ff00fffc0000fffc0000fffc000000000000fffafffafffafffafffafffa00000000fff0fff0fff0fff0fff0fff000000000fff0ff00fff0ff00fff0ff00ff00ff00fff0f0f0f0f0f0f0fff0f000f000f000fff00000fff00000
  | 1, 1 => 0xffff0000ffff0000ffff0000fff00000ffff0000ffaa0000ffff0000ff000000ffff0000fc000000ffff0000f0f00000ffff0000f0a00000ffff0000f0000000ffff0000cc000000ffff0000c0c00000ffff0000c0000000ffff0000aaaa0000ffff0000a0a00000ffff000088880000ffff000088000000ffff000055000000
  | 1, 2 => 0xffff333333333333ffff333300000000ffff3030ffff3030ffff111111111111ffff111100000000ffff0f0fffff0f0fffff0c0c0c0c0c0cffff0c0c00000000ffff00ff00ff00ffffff00aaffff00aaffff00aa00aa00aaffff00aa00000000ffff000f000f000fffff0000ffffffffffff0000ffff0f0fffff0000ffff00ff
  | 1, 3 => 0xffffa8a8a8a8a8a8ffffa8a800000000ffffa0a0ffffa0a0ffffa0a0a0a0a0a0ffffa0a000000000ffffa000a000a000ffff8888ffff8888ffff888888888888ffff888800000000ffff8080ffff8080ffff808080808080ffff808000000000ffff555555555555ffff555500000000ffff5500ffff5500ffff550055005500
  | 1, 4 => 0xffffccccccccccccffffcccc00000000ffffcc88cc88cc88ffffcc00ffffcc00ffffcc00cc00cc00ffffcc0000000000ffffc0c0c0c0c0c0ffffc000ffffc000ffffc000c000c000ffffaaaaffffaaaaffffaaaaaaaaaaaaffffaaaa00000000ffffaa00ffffaa00ffffaa00aa00aa00ffffaa0000000000ffffa8a8ffffa8a8
  | 1, 5 => 0xffffff00ff00ff00ffffff0000000000fffffcfcfffffcfcfffffcfcfcfcfcfcfffffcfc00000000fffffc00fc00fc00fffffafafafafafafffffafa00000000fffff0f0fffff0f0fffff0f0ffff0000fffff0f0f0f0f0f0fffff0f000000000fffff000fffff000fffff000f000f000ffffeeeeffffeeeeffffccccffffcccc
  | 1, 6 => 0xffffffff88008800ffffffff55555555ffffffff33333333ffffffff05050505ffffffff00ff00ffffffffff00330033ffffffff0000ffffffffffff0000ff00ffffffff0000f0f0ffffffff0000aaaaffffffff00005555ffffffff00000000ffffffccffccffccffffffaaffaaffaaffffff00ffffff00ffffff00ffff0000
  | 1, 7 => 0xffffffffff00ff00fffffffffcfcfcfcfffffffffc00fc00fffffffff0f0f0f0fffffffff0f00000fffffffff000f000ffffffffccccccccffffffffcc88cc88ffffffffcc00cc00ffffffffcc000000ffffffffc0c0c0c0ffffffffaaaaaaaaffffffffaaaa0000ffffffffa0a0a0a0ffffffffa0a00000ffffffff88888888
  | 1, 8 => 0xffffffffffffffffffffffffffffff00fffffffffffff0f0ffffffffffffaaaaffffffffffff0000fffffffffff0fff0ffffffffffaaffaa
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xafa710657486b50ec57480a70e25747c270e25745fa64e25747b270d6574
  | 4, 0, 0 => 0x86b5154712bac45a89c3895d668d44e1c4aeb1b6a270e25756a28538712bace1a8a53895d62ed44e1c4aeb0d60a70e257586b5d38712bac61a09c3895d626d44e1c4aeb0d6a270de57586a70ee712bac35a89c3e95d646d44e1c4aeb0d62a70e2575
  | 4, 0, 1 => 0x86b50ea571fac35ca9c3895d67ed44e1c4aeb296a270e257595b5138712bac35a89c3894561ad44b9c4aeafe6a270e257586b50ea712bac35a8a43895d676d44e1fcaeaf377270e2575ad35138712bac25a89c3895d61a9c409c4aeb286a270e2575
  | 4, 0, 2 => 0xaf31538712bac358c9c3895d61afa4e1c4aeb0d50270e257586b8d38712bac35a89c3f15d61ad43f988aeb3872270e257586b5538712bab51509c3895d68ac44e1c4aeb256a270e257586b513e712bad7e049c3895d5ded44e1c4aeb0d73270fe575
  | 4, 0, 3 => 0x63a70e2672bad897e9c3895d61adb4e1c4aeb0d6a270d457586b9d38712bac35ac9c3895d628cf4e1c4aeb0d4e1c4ae39586b513857182c35a89c3d1c56bec44e1c4aeb4b5fa70e257586b2538712bac359c9c3895d61acc4e1c4aead44e1c4ae3a5
  | 4, 0, 4 => 0xa6b5138712bac35a8b23f95d61ac74e1c4aeaab53a70e25756a270f2712bad498e9c3895d674d44e1c4aeb0d4e1c4ae28586b5138712bacf9a89c3895d61ad44e198aeb4f7ca70e2575a5b5138712baafd38713595d61ad44e1c4a4b0d6a1fcea575
  | 4, 0, 5 => 0x86b6138712bac39a89c3895d5f2bf4e1c4aeb0d85a70e257586aed38712bac35a8a53895d69f034e1c4aeb648fb50ec57586b51386c2bacd5a89c3895d61ae24e1c4aeb037f270e257579a70e2642bad2d969c3895d6969c3895c8eb0d6a2e8c4575
  | 4, 0, 6 => 0xafa70e25722ad1da89c3895d632d44e1c4aeb0d68a70e257586b4d38712bac55a89c3895d5f29c3895c98b0d72270e25759635138712bab5138712d15d61af94e1c4aeb0d6a2e8ea5759bb9138712bab51789c3895d61adc4e1c4aeb5f7f270e2575
  | 4, 0, 7 => 0x9835138712bab51569c3895d61aca4e1c4aeb0d6a270f071586b51387125ab5138712b89561ae04e1c4aeb0d78a70e257586a9938712bad49f89c3895d5889c3899caeb0d53a70c65759235138712bad7d7e9c3895d696fc4e1c4aead4429d4e2575
  | 4, 0, 8 => 0x21ac34e1c4aeb0d6a188ae4456f35138712bac41a89c3895d5fc9c38990aeb0d6a2e8f85759e35138712babf5a89c3895d61a9c3895c90b0d53a70e2575
  | 5, 0, 0 => 0x86b5138712b8f9a1ad45b270e2576b247da8753895da1ad44e1c4ae19686b5138712b931a1ad458a70e257686b5138712b8d1a1ad44e234e257686b5138712b851ac8d44e1c4ae2c6b247da8a43895d8010d62a70e2575b944da89c3895dac9406a270e2576b2c7da89c3895da0b006a270e2576
  | 5, 0, 1 => 0xb23517a9c3895dad11f6a270e257686b5138712b929a1ad44e1c4d2576b2435a8ba3115dabd576a270e257686b50e2622b90daef4c6a270e2576b647da89c3895dab30d6a270e2576aa35138923895da1ad44e1c4ae02600270e2570d84d694d44e1c4c85760044da89c3895d6c91a6a270e2576
  | 5, 0, 2 => 0xb247da8752b8fda3ed458270e2576b24f5a89c3f95da3f076a270e2576b24d9a89c3895da1ad44e1c4ba576aec35a89c3895dadb0d6a270e257686b5138712b8a9a1ad44e1c4ae50600435a8712b88961ad44e254e257600435a89c388d5401176a270e2575afc360c9c3895da1af94e1c4ce576
  | 5, 0, 3 => 0x86b5138712b959ac90d6a294e2576a7d15a89c3895dae11f72270e2576b247da8a33895da1ad464270e2576b237da89c3895daf70d6a270e2576b2435909c3895dac91f6a27ce257686b51749c4595dadf1f6a270e2576bc47da89c3895da26d44e1c4ae43686b51389a3895dac91f73270fe576
  | 5, 0, 4 => 0x3f9a89c3895d6ff1f67a70e257686b51969c3895d8010d6a1d4e2575ac47da89c3895dac91f50270e257686b5138712b839ac91f71a70e25768fc35a89c3195dac91f6a1fcc457686b5138712b91dac91f68270e2576b232138713415dac91f6aa70e2576ba435a89c3895da1b056a270e2576
  | 5, 0, 5 => 0x86b5138712b849aed1f6a270e257686b5138712b911ac9316a270e2576b247d9c9c3895da1ad44e1c4ae37686b5138712b82dac70d6a270e2576b247d989c3895dae31f6a270e2576be451a89c3895dac9216a270e2576b247d8c9c3895dac8f06a270e2576b23fda89c3895da5d1f6a270e2576
  | 5, 0, 6 => 0xb247d38712b8e5ac91f6a270ae30686b5138712b88dabf4f6a270e257686b516e9c3895dae91a6a270e257686c19dc9c3895da1ad44e1d0e2576b547da89c3895da1ad44e1c4e2576b25318a9c3895da1ad44e1c4ae0f6af435a89c3895da3f186a270e257686b5138712b829a1aec6a270e2576
  | 5, 0, 7 => 0xb247da89c3515dac91f73a70e2576b7435a89c3895dac9396a270e257686ac94e9c3895da1ad44e1c4ae3f6b247dac9c3895da1ad44e1c4ca57686be5a89c3895db050d6a270e2576b2435f29c3895dac9486a270e25769cc35a89c3895daf30d67a70e25768d35138713715d9a8b255a70e2576
  | 5, 0, 8 => 0x86b5174713115da1ad44e1c4ae3d6a7c35889c3895dac91f6a1fcea57686b5138712b95da88d44e1c4ae4d6a0c7da89c3895da3ed44e220e2576b3c7da89c3895dac91f6da70e2576bd47da89c3895da1afc4e1c4c85769bc7da89c3895da3ed04e268e2576b2471a89c3895da1ad44e1c4ae3b6
  | 5, 0, 9 => 0xbec7da89c3895da1ad461270e257686b91a89c3895da1ad44e1c4b857686bcda89c3895da1ad44e1c4ae2d6b243da89c3895dac90d72270e2576a7b5138913895dae91f68270e2576a5c7da89c3895da1ad44e1c4e05760043538571586d6c9266a270e2576b247da89c38949a1ad44e1c4ae0d6
  | 5, 0, 10 => 0xb247da89c3315da1ad44e1c4ae466b2401388f3895da1ad44e26ce257686b5164712b90da1ad44e1c4ae03686afd388f3895d9eaf36a270e257686b5138712b8c9ac8f36a270e2576b247da89c3695da1ad44e1c4ae20686b5138843895dac91e6a270e25768fc1538713215da1ad44e1c4ae2f6
  | 5, 0, 11 => 0x86b5138712b905a1ad45c270e25768fc49a89c3895db010d6a270e257686b5138712b859a1ad44e1c4ae1a66a2b1569c3895dac92d6a270e25768fc35a89c3895da1ad44e1c4ae1b6b94f5a89c3895da8ad45fa70e2576bbc5da89c3895da1ad44e1c4ae18699c35a89c3895da1ad44e208e2576
  | 5, 0, 12 => 0xb22b14e9c3895dabf0d5fa70e257686b513a9c3895da1ad44e1c4ae546adc7da89c3895da1ad4529c4ae3f6b2459a89c3895dad30d6a270e257686b515c9c3895da1ac04e1c4c857686b5138712b8c5a3f0d63a70e2576b2351529c3895da1ad44e1c4ae4e6b247da89c3895da1ad44e1c4ae246
  | 5, 0, 13 => 0xafb517e9c3895da3ed44e1c4ae3c686bb5a89c3895da1ad44e1c4ae2e6b257d7e9c3895da1ad44e1fce2576a2c35a89c3895daa4d44e23ce25760052da89c3895d6c90d67a70e257686ba1a89c3895da1ad459a70e257686b5138712b955ac91f6a2c8fe576b247d8e9c3895da1ad44f270e2576
  | 5, 0, 14 => 0x435a89c3895d400d44e15c5613586b5138712b8d9ac91f6a2e8c457686b5138712b85da3ed44e1cce257686b5138712b821aa70d6a270e2576a747d8a9c3895da1ad456a70e257686b51388f3895da1ad45f270e25760043538711a86d61ad44e258e2576ae435a89c3895da38d465a70e2576
  | 5, 0, 15 => 0x4358e9c3895d5a8bf4e244e257686b5138933895dabf0d6a270e257686b5138712b84da1b026a270e2576b247dc49c3895db0b0d6a270e257686b5138712b81da1ad44e1c4ae536a7435a89c3895da5f0d6a270e257686b5138712b801a1afc6a270e2576a8c35a89c3895da1ad44e1c4ae016
  | 5, 1, 0 => 0x833f9a89c3895da1ae44e1c4ae3f686b5138712b875a850d6a270e2576b2401dc9c3895da1aee5fa70e2576b247d769c3895da1ad44e1c4ae4068fc15a89c3895dac91f6a294e2576c2435a89c3895da1add6a270e2576a4c35a89c3895da1aeb6a270e2576a2435a89c3895da8ad44e1c4ae4c6
  | 5, 1, 1 => 0xafb5138712b931a1ad469270e257686b51388a3895dac30d6a270e257686a711e712b91da1af76a270e257686b5138913895da1b046a270e2576aab5138913895dac91f4e200e25766a27114863895da1ad44e1c4c2576b247db89c3895da1ae96a270e257686b5116753895d8010d6a2e8c4575
  | 5, 1, 2 => 0xafc3538712b91dac8d455a70e2576a547da89c3895da1aee6a270e257686b5138903895da1af26a270e257600435a8a53895d400d44e1c46a13586b51569c3895dac91f7ca70e257686b5138712b841a1ad44e1c4c4576b2481a89c3895da1ad462270e2576b247da8ba3a95da1ad44e1c4ae296
  | 5, 1, 3 => 0x8e35138712b955ac91d6a270e25769e435a89c3895da651f6a270e2576b247dc89c3895daeb0d6a270e257686b5138712b889a1ad45aa70e257686b514e9c3895da1ad44e1c4ae1f6b235138712d95d9a89c489c4ae4c6b24354e9c3895dabf0d65a70e257686c1938713215da3ed4451d4e2576
  | 5, 1, 4 => 0x86bb938712b91dad31f6a270e257686b5138712c95da1ad44e1d4e2576b247da29c3895daf90d6a270e257686b51749c3895da1ad44e1c4ae266b247da69c3895daff1a6a270e2576b2451a89c3895d8010d7ca70e2575b23d1a89c3895db030d6a270e2576b24f1a89c3895da1ad466a70e2576
  | 5, 1, 5 => 0x86c21a89c3895d8010d6a15c5622500435a89c1a8ad6c91f53a70c657686b51449c3895da1ad44e1c4ae2760043538712b86d6c10d6a270e257686b5138712b871a1ad44e1c4b057686b5138712b8e1a1ad44e1c4ae0c6a1c35a89c3895da1aee65a70e25768fb51387b3895d8010d72270e2575
  | 5, 1, 6 => 0xa7c35a89c3895da1ad44e230e2576b2429a89c3895da1b0c6a270e2576b5c35a89c3895da1aea6a270e2576c3435a89c3895da1ad44e1c4be57686b85a89c3895d8015f5fa70e25758fb5138873895da1ad44e260e25768a351969c3895da1ad459270e257686b5138712b811b070d6a270e2576
  | 5, 1, 7 => 0x86b5138712b9158010d53a70e257593c35a89c3895d800d455a70e2575b247da8ba3e15da1ad45a270e2576b247d4e9c3895dabf1f65a70e257686b5138712b845800d44e1c4ae1359c35138712b8fdacd1f6a270e2576b247da89c3c1c5ae70d6a270e2576b247da89c3892da1ada6a270e2576
  | 5, 1, 8 => 0x21ad44e1c4ae1e686b51a89c3895da1ad44e1c4c0576b1435a89c3895da1b0d6a270e257686b51387c3895dac91f4e1dce257686b65a89c3895da1ad44e1c8e2576a5c35a89c3895dac91f6a188ae44686b517e9c3895da1ad44e224e257686b5138712b8d58013c6a270e2575
  | 6, 0, 0 => 0x21ad43895c44a0000435a89c388d56c91f7635138712bbd923ed44e1c4ae127b247da89c3895c88f1f6a271168a3895dec91f6a270e25705bc7e1ad44e1c4ae1270059234d44e1c4aed648fb51969c3895dc01648fb50ea712bb5923ed44e1c4dc57700435a89c3895c98d648fb5138712b839ec91f6a270e25723bd921ad44e1c4ae437
  | 6, 0, 1 => 0xbcd923ecf4e1c4aef64a347da89c3895dec90d6a30138712bbd923ed44e1c4ae237c147e1ad44e1c4aee0086b51389a3895dac91f833b938712bb8023ed458270e2576b255da89c491c4aef648fb5138743895dec96186b5138712bbd429d1f6a270e2577b2435a89c489c4aef648fb5138713895de8d1f86b5138712bbd92bd1f6a270e2577
  | 6, 0, 2 => 0xb247df89c38990aef7fb2435a89c3895dec91f6a270e2571db8021ad465a70e2576b75923ed44e1c4aef648fac94e9c3895dec91f6a270e2571fbd921aee6a270e257700435a89c3895c8ec00b247da09c3895dac91f6a270e2652bb802e90d6a270e2576b2351809c389a0aef82b247da89c3895dec9398fb5138712bbd921ad44e1c4c4577
  | 6, 0, 3 => 0xb247da89c3895c40f648fb5138843895dec91f6a270e25717b8023e9c3895c36066ba47da8cb4e1c4aee00b235138712b849ac91f7235138712bbd923ed44e1c4b8577b247da89c3895c5af6486b5138712b889ec91f6a270e2702bb802c91f4e15c561b600435a89c3895c24d648fb5174713115dec91f6a270e2571ebd923ed44e1c4ae577
  | 6, 0, 4 => 0xb2435a8ba4e1c4aee00b24e5a89c3895dac91f6a270e2570db8021ad44e1c4ae3f6b247da89c3895c30f648fb5138823895dec91f6a270e257233d923ed44e26ce2577b247da8b23895c86f648fb5138712b80dc018286b5138712bb5ea3ed44e23ce25778fc7e1ad44e1c4aef1f86b5138712b86dec9568fb5138712bbd921ad44e248e2577
  | 6, 0, 5 => 0xb241a00d44e1c4aef648fb514a712b8fded3648fb5138712bbd923ed457270e25778fc35a89c3895caaf648fb0138713215dec91f6a270e25718b802f51f6a270e2576b247da8b84e1c4aee00b2471a89c3895db01648fb5138712bbd923ed44e1c4ae167b247da89c3895c34f648fb5138712b885ef96486b5138712bbd923f1f6a270e2577
  | 6, 0, 6 => 0xb247da8be4e1c4aee00b247d38711a86dac91f6a2712c712bb8023ed44e1c4ae056b247da89c3895c12f648fbb5a89c3895dec91f6a270e257173d923ed44e1fce2577b25163ed44e1c4aef648fb519e9c3895de3f0d6a2711e712bbd923ed459a70e2577b247da89c3895caaf458fc35a89c3895dec91f6a27538712bbd923ed44e1c4ae547
  | 6, 0, 7 => 0xafc7e1ad44e1c4aef1f86b5138712b84dee9648a35138712bbd92a31f6a270e2577b247da89c3895c02e00b247da89c3895da3f0d7e35138712bbdfef31f6a270e2577b247da89c3895c6cf648fb5138712b85dc011f86b5138712bb0021ad44e1c4ae1b6b254e3ed44e1c4aee00b243538712b86dac91f6a2bd38712bbd923ed44e23ce2577
  | 6, 0, 8 => 0xb247da89c3895c80e00a2c35a89c3895db09648fb5138712bbd923edd6a270e2577b25123ed44e1c4aee0086b5138712b955ac95f8fb5138712bbd923ed44e1c4ae13700489a89c3895c0cd85b247da89c3895dec91f6a2711c712bbd921ad459270e2577b247da89c3895c0ef64a747da89c3895dec91f6a270e257003d923efc6a270e2577
  | 6, 0, 9 => 0xb247deed44e1c4aef648fb5138913895dec91f8235138712bbc7e1ad460270e2577000021ad44e1c4aeb648fb5138713095dec92a8fb5138712bbd923ee96a270e2577b247da88b3a9c4aee00b247da8ba3115dae91f6a270e2572abd923ee44e1c4ae3f7b247da8ba591c4aef7fb2471a89c3895dc010d6a2711e712bb47da89c4d1c4ae557
  | 6, 0, 10 => 0x591a89c3895c26d648fbc9a89c3895dc011f82b5138712bb002c91f6a294e2576b25421ad44e1c4aef648fb5138713115dc015f86b5138712bb0021ad44e1c4ae136b253e1ad44e1c4aef648fb51729c3895dec91f6a34938712bbd923ed44e228e2577b25863ed44e1c4aef648fa711e712b91ded31f6a270e2570938021afc6a270e2576
  | 6, 0, 11 => 0x435a89c38988aed81b247da89c3895dec91f6a33538712bb802c30d6a270e25768fc35a89c491c4aee0086b5138913895daeb648fb5138712bbd923ed44e1c4ae227b247da8a74e1c4aef648fb5138712b87dec91f6a270e257213d923ed44e188ae3f7b247e0c9c38990aef648fbb9a89c3895dec91f6a27120712bbdfac91f6a270e2577
  | 6, 0, 12 => 0xb247da89c3895c70f6486b517e9c3895dec90d6a270e2571abd92871f6a270e2577b247ddccb4e1c4aef64abb5138713415dc01648fb9138712bb5923eee4e1c4ae47700435a89c3895c44d648fb5138753895de3f0d6a270e257033df2c91f6a270e2577b247da8ba4e1c4aee0086bb9a89c3895dac91f6a270e2571338023ed44e15c56066
  | 6, 0, 13 => 0xb247e10d44e1c4aee008fb5138711a8198016486b51385715b002c91f6a15c56226005923ed44e0d456c00be435a89c3895d8010d6a2e938712bb5923ed451270e2577b247da89c3895c4ee00b247d38712b86dac91f6a27128712bbd92c11f6a270e2577b247da89c3895c38e00b2451a89c3895daff1f6a32d38712bbd923ed44e1c4b0577
  | 6, 0, 14 => 0x435a8b24e1c4aed648fb5138712b93dec90d6a270e257263d923efb6a270e2577b247e18d44e1c4aee000043538712b86d6d7648fb5138712bbe1ac91f6a270e2577b247da89c3897caef648fb85a89c3895dec90d86b5138712bb802d31f6a270e2576b247da8b24e1c4aef648fb5138712b811f07648fb5138712bbd92a1466a270e2577
  | 6, 0, 15 => 0xb251a1ad44e1c4aee000035138712b84d400d44e1c4ae120330029f0d6a270e2576b247da89c3895c66f648fb5138712f15deff1f6a270e2572abd921ad44e1c4ae477b247da8b44e1c4aef648fb5138712b925e3f0d6a270e25726bd923ed44e1c4ae117005921ad44e1c46ad73b247da89c3895dee51f6a270e25721bd929f1f6a270e2577
  | 6, 1, 0 => 0x5923ed44e1c46ac0086c35a89c3895dac91f6a270e257263d923ed44e1c4ae157b247da89c3895c3cf648fb51a89c3895dc010d6a2fd38712bb0021ad44e1c4ae356b247e1ad44e1c4aef648fb51387c3895dec91f6cb5138712bb802c91f6a270ae2b6b247da89c391c4aef648fb517e9c3895dec91f6a270e2571ab802c91f53a70e2576
  | 6, 1, 1 => 0x5923ed44e1c4ae567
  | 7, 0, 0 => 0x592c31f6a270e257700000010d6a270e2575005923efc6a270e257700002c91f6a270e2576000023f0d6a270e2576005923ed44e23ce2577005923ed44e1c4ae557005923ed44e1c4ae1b700002c8d44e1c4ae126005923ed44e1c4ae3f70060ac91f6a270e2577005928d1f6a270e2577005923ed44e1c4ae127005923ed465a70e2577005923ed44e1c4dc577005923ed44e1c4ae477
  | 7, 0, 1 => 0x2c91f6a270e2356005923f0d6a270e257700002c91f6a270ae2b6005923ed44e1c4ae357005923ed459270e257700002c91f4e1c4ae1b6005f2c91f6a270e2577005923ed45d270e2577005923ed44e1c4ae227005923eee6a270e2577005923ed44e1c4c4577
  | 8, 0, 0 => 0x2c91f6a270e2576
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 3 => 40
  | 4 => 49
  | 5 => 58
  | 6 => 67
  | 7 => 76
  | 8 => 85
  | _ => 0

def idWidth : Nat := 9
def wireAt (i : Nat) : Nat := expand (fld (dictB (i / 256) (i / 16 % 16)) 64 (i % 16))
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1024), (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1024), (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 4096)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat :=
  pickMin zs symsG zs (hk zs)
theorem ori_ok {u ys} (h : NatRun (mask 4096) (goal 4096) u ys) :
    NatRun (mask 4096) (goal 4096) u (ori ys) :=
  pickMin_run ys h symsG ys (hk ys) symsG_ok h
def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk zs) 20 0 (NN s)
def poolG : List Nat := []
def Z (s : Nat) := bar 4096 S NN idx ori poolG s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z0_0 : span (Z 0) 0 0 = true := by decide +kernel

private theorem z0 : span (Z 0) 0 0 = true := z0_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z1_0 : span (Z 1) 0 0 = true := by decide +kernel

private theorem z1 : span (Z 1) 0 0 = true := z1_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z2_0 : span (Z 2) 0 0 = true := by decide +kernel

private theorem z2 : span (Z 2) 0 0 = true := z2_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : span (Z 3) 6 0 = true := by decide +kernel

private theorem z3 : span (Z 3) 6 0 = true := z3_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : span (Z 4) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_24 : span (Z 4) 24 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_48 : span (Z 4) 24 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_72 : span (Z 4) 24 72 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_96 : span (Z 4) 24 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_120 : span (Z 4) 18 120 = true := by decide +kernel

private theorem z4_a1 : span (Z 4) 48 0 = true :=
  span_join (f := Z 4) (a := 24) (o := 0) (b := 24) z4_0 z4_24

private theorem z4_a2 : span (Z 4) 72 0 = true :=
  span_join (f := Z 4) (a := 48) (o := 0) (b := 24) z4_a1 z4_48

private theorem z4_a3 : span (Z 4) 96 0 = true :=
  span_join (f := Z 4) (a := 72) (o := 0) (b := 24) z4_a2 z4_72

private theorem z4_a4 : span (Z 4) 120 0 = true :=
  span_join (f := Z 4) (a := 96) (o := 0) (b := 24) z4_a3 z4_96

private theorem z4_a5 : span (Z 4) 138 0 = true :=
  span_join (f := Z 4) (a := 120) (o := 0) (b := 18) z4_a4 z4_120

private theorem z4 : span (Z 4) 138 0 = true := z4_a5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : span (Z 5) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_24 : span (Z 5) 24 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_48 : span (Z 5) 24 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_72 : span (Z 5) 24 72 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_96 : span (Z 5) 24 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_120 : span (Z 5) 24 120 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_144 : span (Z 5) 24 144 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_168 : span (Z 5) 24 168 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_192 : span (Z 5) 24 192 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_216 : span (Z 5) 24 216 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_240 : span (Z 5) 24 240 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_264 : span (Z 5) 24 264 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_288 : span (Z 5) 24 288 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_312 : span (Z 5) 24 312 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_336 : span (Z 5) 24 336 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_360 : span (Z 5) 24 360 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_384 : span (Z 5) 15 384 = true := by decide +kernel

private theorem z5_a1 : span (Z 5) 48 0 = true :=
  span_join (f := Z 5) (a := 24) (o := 0) (b := 24) z5_0 z5_24

private theorem z5_a2 : span (Z 5) 72 0 = true :=
  span_join (f := Z 5) (a := 48) (o := 0) (b := 24) z5_a1 z5_48

private theorem z5_a3 : span (Z 5) 96 0 = true :=
  span_join (f := Z 5) (a := 72) (o := 0) (b := 24) z5_a2 z5_72

private theorem z5_a4 : span (Z 5) 120 0 = true :=
  span_join (f := Z 5) (a := 96) (o := 0) (b := 24) z5_a3 z5_96

private theorem z5_a5 : span (Z 5) 144 0 = true :=
  span_join (f := Z 5) (a := 120) (o := 0) (b := 24) z5_a4 z5_120

private theorem z5_a6 : span (Z 5) 168 0 = true :=
  span_join (f := Z 5) (a := 144) (o := 0) (b := 24) z5_a5 z5_144

private theorem z5_a7 : span (Z 5) 192 0 = true :=
  span_join (f := Z 5) (a := 168) (o := 0) (b := 24) z5_a6 z5_168

private theorem z5_a8 : span (Z 5) 216 0 = true :=
  span_join (f := Z 5) (a := 192) (o := 0) (b := 24) z5_a7 z5_192

private theorem z5_a9 : span (Z 5) 240 0 = true :=
  span_join (f := Z 5) (a := 216) (o := 0) (b := 24) z5_a8 z5_216

private theorem z5_a10 : span (Z 5) 264 0 = true :=
  span_join (f := Z 5) (a := 240) (o := 0) (b := 24) z5_a9 z5_240

private theorem z5_a11 : span (Z 5) 288 0 = true :=
  span_join (f := Z 5) (a := 264) (o := 0) (b := 24) z5_a10 z5_264

private theorem z5_a12 : span (Z 5) 312 0 = true :=
  span_join (f := Z 5) (a := 288) (o := 0) (b := 24) z5_a11 z5_288

private theorem z5_a13 : span (Z 5) 336 0 = true :=
  span_join (f := Z 5) (a := 312) (o := 0) (b := 24) z5_a12 z5_312

private theorem z5_a14 : span (Z 5) 360 0 = true :=
  span_join (f := Z 5) (a := 336) (o := 0) (b := 24) z5_a13 z5_336

private theorem z5_a15 : span (Z 5) 384 0 = true :=
  span_join (f := Z 5) (a := 360) (o := 0) (b := 24) z5_a14 z5_360

private theorem z5_a16 : span (Z 5) 399 0 = true :=
  span_join (f := Z 5) (a := 384) (o := 0) (b := 15) z5_a15 z5_384

private theorem z5 : span (Z 5) 399 0 = true := z5_a16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : span (Z 6) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_24 : span (Z 6) 24 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_48 : span (Z 6) 24 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_72 : span (Z 6) 24 72 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_96 : span (Z 6) 24 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_120 : span (Z 6) 24 120 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_144 : span (Z 6) 24 144 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_168 : span (Z 6) 24 168 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_192 : span (Z 6) 24 192 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_216 : span (Z 6) 24 216 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_240 : span (Z 6) 24 240 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_264 : span (Z 6) 9 264 = true := by decide +kernel

private theorem z6_a1 : span (Z 6) 48 0 = true :=
  span_join (f := Z 6) (a := 24) (o := 0) (b := 24) z6_0 z6_24

private theorem z6_a2 : span (Z 6) 72 0 = true :=
  span_join (f := Z 6) (a := 48) (o := 0) (b := 24) z6_a1 z6_48

private theorem z6_a3 : span (Z 6) 96 0 = true :=
  span_join (f := Z 6) (a := 72) (o := 0) (b := 24) z6_a2 z6_72

private theorem z6_a4 : span (Z 6) 120 0 = true :=
  span_join (f := Z 6) (a := 96) (o := 0) (b := 24) z6_a3 z6_96

private theorem z6_a5 : span (Z 6) 144 0 = true :=
  span_join (f := Z 6) (a := 120) (o := 0) (b := 24) z6_a4 z6_120

private theorem z6_a6 : span (Z 6) 168 0 = true :=
  span_join (f := Z 6) (a := 144) (o := 0) (b := 24) z6_a5 z6_144

private theorem z6_a7 : span (Z 6) 192 0 = true :=
  span_join (f := Z 6) (a := 168) (o := 0) (b := 24) z6_a6 z6_168

private theorem z6_a8 : span (Z 6) 216 0 = true :=
  span_join (f := Z 6) (a := 192) (o := 0) (b := 24) z6_a7 z6_192

private theorem z6_a9 : span (Z 6) 240 0 = true :=
  span_join (f := Z 6) (a := 216) (o := 0) (b := 24) z6_a8 z6_216

private theorem z6_a10 : span (Z 6) 264 0 = true :=
  span_join (f := Z 6) (a := 240) (o := 0) (b := 24) z6_a9 z6_240

private theorem z6_a11 : span (Z 6) 273 0 = true :=
  span_join (f := Z 6) (a := 264) (o := 0) (b := 9) z6_a10 z6_264

private theorem z6 : span (Z 6) 273 0 = true := z6_a11

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : span (Z 7) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_24 : span (Z 7) 3 24 = true := by decide +kernel

private theorem z7_a1 : span (Z 7) 27 0 = true :=
  span_join (f := Z 7) (a := 24) (o := 0) (b := 3) z7_0 z7_24

private theorem z7 : span (Z 7) 27 0 = true := z7_a1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : span (Z 8) 1 0 = true := by decide +kernel

private theorem z8 : span (Z 8) 1 0 = true := z8_0

theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, Z s i = true := by
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

def RootG (s : Nat) : Bool :=
  scr 4096 s poolG xsG || found S NN idx s (ori xsG)
theorem rootChecked : span RootG 4 5 = true := by decide +kernel
theorem xsG_len : xsG.length = 6 := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : NatRun (mask 4096) (goal 4096) s xsG) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h
    rw [xsG_len] at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (Run.perm hr.2 (ori_ok h))

def CG : Circuit := ⟨[⟨GateOp.and, [4, 5]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.and, [11, 13]⟩], 14⟩
def vec (b0 b1 b2 b3 b4 b5 : Bool) : Fin 6 → Bool := fun i => [b0, b1, b2, b3, b4, b5].getD i.val false
theorem CG_mono : Monotone2 CG := by
  intro g hg
  simp only [CG, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem CG_vec : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    CG.eval (List.ofFn (vec b0 b1 b2 b3 b4 b5)) = fG (vec b0 b1 b2 b3 b4 b5) := by decide +kernel
theorem CG_eval (x : Fin 6 → Bool) : CG.eval (List.ofFn x) = fG x := by
  have hx : x = vec (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := by
    funext ⟨i, hi⟩
    interval_cases i <;> rfl
  rw [hx]
  exact CG_vec _ _ _ _ _ _

end PEqualNP.Outside.L_meta_12421

theorem PEqualNP.Outside.L_meta_12421 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132456 * 2 ^ 32 + 3903383720) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132456 * 2 ^ 32 + 3903383720) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12421.mainG PEqualNP.Outside.L_meta_12421.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12421.CG, PEqualNP.Outside.L_meta_12421.CG_mono, by
      have : PEqualNP.Outside.L_meta_12421.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12421.CG_eval⟩
