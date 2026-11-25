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
namespace PEqualNP.Outside.L_meta_12573

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (4008242920 * 2 ^ 32 + 4008241864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 3, 3, 3, 3, 3, 3, 6, 7, 3, 9, 3, 11, 3, 13, 14, 15, 3, 3, 3, 19, 3, 21, 22, 23, 3, 25, 26, 27, 3, 29, 30, 31, 3, 3, 3, 35, 3, 37, 38, 39, 3, 41, 42, 43, 3, 45, 46, 47, 3, 3, 3, 51, 3, 53, 54, 55, 3, 57, 58, 59, 3, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 6, 6, 6, 3, 6, 6, 6, 7, 6, 9, 6, 11, 6, 13, 14, 15, 6, 6, 6, 19, 6, 21, 22, 23, 6, 25, 26, 27, 6, 29, 30, 31, 6, 6, 6, 35, 6, 37, 38, 39, 6, 41, 42, 43, 6, 45, 46, 47, 6, 6, 6, 51, 6, 53, 54, 55, 6, 57, 58, 59, 6, 61, 62, 63, 7, 7, 7, 3, 7, 7, 6, 7, 7, 9, 7, 11, 7, 13, 14, 15, 7, 7, 7, 19, 7, 21, 22, 23, 7, 25, 26, 27, 7, 29, 30, 31, 7, 7, 7, 35, 7, 37, 38, 39, 7, 41, 42, 43, 7, 45, 46, 47, 7, 7, 7, 51, 7, 53, 54, 55, 7, 57, 58, 59, 7, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 9, 9, 9, 3, 9, 9, 6, 7, 9, 9, 9, 11, 9, 13, 14, 15, 9, 9, 9, 19, 9, 21, 22, 23, 9, 25, 26, 27, 9, 29, 30, 31, 9, 9, 9, 35, 9, 37, 38, 39, 9, 41, 42, 43, 9, 45, 46, 47, 9, 9, 9, 51, 9, 53, 54, 55, 9, 57, 58, 59, 9, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 11, 11, 11, 3, 11, 11, 6, 7, 11, 9, 11, 11, 11, 13, 14, 15, 11, 11, 11, 19, 11, 21, 22, 23, 11, 25, 26, 27, 11, 29, 30, 31, 11, 11, 11, 35, 11, 37, 38, 39, 11, 41, 42, 43, 11, 45, 46, 47, 11, 11, 11, 51, 11, 53, 54, 55, 11, 57, 58, 59, 11, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 13, 13, 13, 3, 13, 13, 6, 7, 13, 9, 13, 11, 13, 13, 14, 15, 13, 13, 13, 19, 13, 21, 22, 23, 13, 25, 26, 27, 13, 29, 30, 31, 13, 13, 13, 35, 13, 37, 38, 39, 13, 41, 42, 43, 13, 45, 46, 47, 13, 13, 13, 51, 13, 53, 54, 55, 13, 57, 58, 59, 13, 61, 62, 63, 14, 14, 14, 3, 14, 14, 6, 7, 14, 9, 14, 11, 14, 13, 14, 15, 14, 14, 14, 19, 14, 21, 22, 23, 14, 25, 26, 27, 14, 29, 30, 31, 14, 14, 14, 35, 14, 37, 38, 39, 14, 41, 42, 43, 14, 45, 46, 47, 14, 14, 14, 51, 14, 53, 54, 55, 14, 57, 58, 59, 14, 61, 62, 63, 15, 15, 15, 3, 15, 15, 6, 7, 15, 9, 15, 11, 15, 13, 14, 15, 15, 15, 15, 19, 15, 21, 22, 23, 15, 25, 26, 27, 15, 29, 30, 31, 15, 15, 15, 35, 15, 37, 38, 39, 15, 41, 42, 43, 15, 45, 46, 47, 15, 15, 15, 51, 15, 53, 54, 55, 15, 57, 58, 59, 15, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 19, 19, 19, 3, 19, 19, 6, 7, 19, 9, 19, 11, 19, 13, 14, 15, 19, 19, 19, 19, 19, 21, 22, 23, 19, 25, 26, 27, 19, 29, 30, 31, 19, 19, 19, 35, 19, 37, 38, 39, 19, 41, 42, 43, 19, 45, 46, 47, 19, 19, 19, 51, 19, 53, 54, 55, 19, 57, 58, 59, 19, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 21, 21, 21, 3, 21, 21, 6, 7, 21, 9, 21, 11, 21, 13, 14, 15, 21, 21, 21, 19, 21, 21, 22, 23, 21, 25, 26, 27, 21, 29, 30, 31, 21, 21, 21, 35, 21, 37, 38, 39, 21, 41, 42, 43, 21, 45, 46, 47, 21, 21, 21, 51, 21, 53, 54, 55, 21, 57, 58, 59, 21, 61, 62, 63, 22, 22, 22, 3, 22, 22, 6, 7, 22, 9, 22, 11, 22, 13, 14, 15, 22, 22, 22, 19, 22, 21, 22, 23, 22, 25, 26, 27, 22, 29, 30, 31, 22, 22, 22, 35, 22, 37, 38, 39, 22, 41, 42, 43, 22, 45, 46, 47, 22, 22, 22, 51, 22, 53, 54, 55, 22, 57, 58, 59, 22, 61, 62, 63, 23, 23, 23, 3, 23, 23, 6, 7, 23, 9, 23, 11, 23, 13, 14, 15, 23, 23, 23, 19, 23, 21, 22, 23, 23, 25, 26, 27, 23, 29, 30, 31, 23, 23, 23, 35, 23, 37, 38, 39, 23, 41, 42, 43, 23, 45, 46, 47, 23, 23, 23, 51, 23, 53, 54, 55, 23, 57, 58, 59, 23, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 25, 25, 25, 3, 25, 25, 6, 7, 25, 9, 25, 11, 25, 13, 14, 15, 25, 25, 25, 19, 25, 21, 22, 23, 25, 25, 26, 27, 25, 29, 30, 31, 25, 25, 25, 35, 25, 37, 38, 39, 25, 41, 42, 43, 25, 45, 46, 47, 25, 25, 25, 51, 25, 53, 54, 55, 25, 57, 58, 59, 25, 61, 62, 63, 26, 26, 26, 3, 26, 26, 6, 7, 26, 9, 26, 11, 26, 13, 14, 15, 26, 26, 26, 19, 26, 21, 22, 23, 26, 25, 26, 27, 26, 29, 30, 31, 26, 26, 26, 35, 26, 37, 38, 39, 26, 41, 42, 43, 26, 45, 46, 47, 26, 26, 26, 51, 26, 53, 54, 55, 26, 57, 58, 59, 26, 61, 62, 63, 27, 27, 27, 3, 27, 27, 6, 7, 27, 9, 27, 11, 27, 13, 14, 15, 27, 27, 27, 19, 27, 21, 22, 23, 27, 25, 26, 27, 27, 29, 30, 31, 27, 27, 27, 35, 27, 37, 38, 39, 27, 41, 42, 43, 27, 45, 46, 47, 27, 27, 27, 51, 27, 53, 54, 55, 27, 57, 58, 59, 27, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 29, 29, 29, 3, 29, 29, 6, 7, 29, 9, 29, 11, 29, 13, 14, 15, 29, 29, 29, 19, 29, 21, 22, 23, 29, 25, 26, 27, 29, 29, 30, 31, 29, 29, 29, 35, 29, 37, 38, 39, 29, 41, 42, 43, 29, 45, 46, 47, 29, 29, 29, 51, 29, 53, 54, 55, 29, 57, 58, 59, 29, 61, 62, 63, 30, 30, 30, 3, 30, 30, 6, 7, 30, 9, 30, 11, 30, 13, 14, 15, 30, 30, 30, 19, 30, 21, 22, 23, 30, 25, 26, 27, 30, 29, 30, 31, 30, 30, 30, 35, 30, 37, 38, 39, 30, 41, 42, 43, 30, 45, 46, 47, 30, 30, 30, 51, 30, 53, 54, 55, 30, 57, 58, 59, 30, 61, 62, 63, 31, 31, 31, 3, 31, 31, 6, 7, 31, 9, 31, 11, 31, 13, 14, 15, 31, 31, 31, 19, 31, 21, 22, 23, 31, 25, 26, 27, 31, 29, 30, 31, 31, 31, 31, 35, 31, 37, 38, 39, 31, 41, 42, 43, 31, 45, 46, 47, 31, 31, 31, 51, 31, 53, 54, 55, 31, 57, 58, 59, 31, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 35, 35, 35, 3, 35, 35, 6, 7, 35, 9, 35, 11, 35, 13, 14, 15, 35, 35, 35, 19, 35, 21, 22, 23, 35, 25, 26, 27, 35, 29, 30, 31, 35, 35, 35, 35, 35, 37, 38, 39, 35, 41, 42, 43, 35, 45, 46, 47, 35, 35, 35, 51, 35, 53, 54, 55, 35, 57, 58, 59, 35, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 37, 37, 37, 3, 37, 37, 6, 7, 37, 9, 37, 11, 37, 13, 14, 15, 37, 37, 37, 19, 37, 21, 22, 23, 37, 25, 26, 27, 37, 29, 30, 31, 37, 37, 37, 35, 37, 37, 38, 39, 37, 41, 42, 43, 37, 45, 46, 47, 37, 37, 37, 51, 37, 53, 54, 55, 37, 57, 58, 59, 37, 61, 62, 63, 38, 38, 38, 3, 38, 38, 6, 7, 38, 9, 38, 11, 38, 13, 14, 15, 38, 38, 38, 19, 38, 21, 22, 23, 38, 25, 26, 27, 38, 29, 30, 31, 38, 38, 38, 35, 38, 37, 38, 39, 38, 41, 42, 43, 38, 45, 46, 47, 38, 38, 38, 51, 38, 53, 54, 55, 38, 57, 58, 59, 38, 61, 62, 63, 39, 39, 39, 3, 39, 39, 6, 7, 39, 9, 39, 11, 39, 13, 14, 15, 39, 39, 39, 19, 39, 21, 22, 23, 39, 25, 26, 27, 39, 29, 30, 31, 39, 39, 39, 35, 39, 37, 38, 39, 39, 41, 42, 43, 39, 45, 46, 47, 39, 39, 39, 51, 39, 53, 54, 55, 39, 57, 58, 59, 39, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 41, 41, 41, 3, 41, 41, 6, 7, 41, 9, 41, 11, 41, 13, 14, 15, 41, 41, 41, 19, 41, 21, 22, 23, 41, 25, 26, 27, 41, 29, 30, 31, 41, 41, 41, 35, 41, 37, 38, 39, 41, 41, 42, 43, 41, 45, 46, 47, 41, 41, 41, 51, 41, 53, 54, 55, 41, 57, 58, 59, 41, 61, 62, 63, 42, 42, 42, 3, 42, 42, 6, 7, 42, 9, 42, 11, 42, 13, 14, 15, 42, 42, 42, 19, 42, 21, 22, 23, 42, 25, 26, 27, 42, 29, 30, 31, 42, 42, 42, 35, 42, 37, 38, 39, 42, 41, 42, 43, 42, 45, 46, 47, 42, 42, 42, 51, 42, 53, 54, 55, 42, 57, 58, 59, 42, 61, 62, 63, 43, 43, 43, 3, 43, 43, 6, 7, 43, 9, 43, 11, 43, 13, 14, 15, 43, 43, 43, 19, 43, 21, 22, 23, 43, 25, 26, 27, 43, 29, 30, 31, 43, 43, 43, 35, 43, 37, 38, 39, 43, 41, 42, 43, 43, 45, 46, 47, 43, 43, 43, 51, 43, 53, 54, 55, 43, 57, 58, 59, 43, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 45, 45, 45, 3, 45, 45, 6, 7, 45, 9, 45, 11, 45, 13, 14, 15, 45, 45, 45, 19, 45, 21, 22, 23, 45, 25, 26, 27, 45, 29, 30, 31, 45, 45, 45, 35, 45, 37, 38, 39, 45, 41, 42, 43, 45, 45, 46, 47, 45, 45, 45, 51, 45, 53, 54, 55, 45, 57, 58, 59, 45, 61, 62, 63, 46, 46, 46, 3, 46, 46, 6, 7, 46, 9, 46, 11, 46, 13, 14, 15, 46, 46, 46, 19, 46, 21, 22, 23, 46, 25, 26, 27, 46, 29, 30, 31, 46, 46, 46, 35, 46, 37, 38, 39, 46, 41, 42, 43, 46, 45, 46, 47, 46, 46, 46, 51, 46, 53, 54, 55, 46, 57, 58, 59, 46, 61, 62, 63, 47, 47, 47, 3, 47, 47, 6, 7, 47, 9, 47, 11, 47, 13, 14, 15, 47, 47, 47, 19, 47, 21, 22, 23, 47, 25, 26, 27, 47, 29, 30, 31, 47, 47, 47, 35, 47, 37, 38, 39, 47, 41, 42, 43, 47, 45, 46, 47, 47, 47, 47, 51, 47, 53, 54, 55, 47, 57, 58, 59, 47, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 51, 51, 51, 3, 51, 51, 6, 7, 51, 9, 51, 11, 51, 13, 14, 15, 51, 51, 51, 19, 51, 21, 22, 23, 51, 25, 26, 27, 51, 29, 30, 31, 51, 51, 51, 35, 51, 37, 38, 39, 51, 41, 42, 43, 51, 45, 46, 47, 51, 51, 51, 51, 51, 53, 54, 55, 51, 57, 58, 59, 51, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 53, 53, 53, 3, 53, 53, 6, 7, 53, 9, 53, 11, 53, 13, 14, 15, 53, 53, 53, 19, 53, 21, 22, 23, 53, 25, 26, 27, 53, 29, 30, 31, 53, 53, 53, 35, 53, 37, 38, 39, 53, 41, 42, 43, 53, 45, 46, 47, 53, 53, 53, 51, 53, 53, 54, 55, 53, 57, 58, 59, 53, 61, 62, 63, 54, 54, 54, 3, 54, 54, 6, 7, 54, 9, 54, 11, 54, 13, 14, 15, 54, 54, 54, 19, 54, 21, 22, 23, 54, 25, 26, 27, 54, 29, 30, 31, 54, 54, 54, 35, 54, 37, 38, 39, 54, 41, 42, 43, 54, 45, 46, 47, 54, 54, 54, 51, 54, 53, 54, 55, 54, 57, 58, 59, 54, 61, 62, 63, 55, 55, 55, 3, 55, 55, 6, 7, 55, 9, 55, 11, 55, 13, 14, 15, 55, 55, 55, 19, 55, 21, 22, 23, 55, 25, 26, 27, 55, 29, 30, 31, 55, 55, 55, 35, 55, 37, 38, 39, 55, 41, 42, 43, 55, 45, 46, 47, 55, 55, 55, 51, 55, 53, 54, 55, 55, 57, 58, 59, 55, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 57, 57, 57, 3, 57, 57, 6, 7, 57, 9, 57, 11, 57, 13, 14, 15, 57, 57, 57, 19, 57, 21, 22, 23, 57, 25, 26, 27, 57, 29, 30, 31, 57, 57, 57, 35, 57, 37, 38, 39, 57, 41, 42, 43, 57, 45, 46, 47, 57, 57, 57, 51, 57, 53, 54, 55, 57, 57, 58, 59, 57, 61, 62, 63, 58, 58, 58, 3, 58, 58, 6, 7, 58, 9, 58, 11, 58, 13, 14, 15, 58, 58, 58, 19, 58, 21, 22, 23, 58, 25, 26, 27, 58, 29, 30, 31, 58, 58, 58, 35, 58, 37, 38, 39, 58, 41, 42, 43, 58, 45, 46, 47, 58, 58, 58, 51, 58, 53, 54, 55, 58, 57, 58, 59, 58, 61, 62, 63, 59, 59, 59, 3, 59, 59, 6, 7, 59, 9, 59, 11, 59, 13, 14, 15, 59, 59, 59, 19, 59, 21, 22, 23, 59, 25, 26, 27, 59, 29, 30, 31, 59, 59, 59, 35, 59, 37, 38, 39, 59, 41, 42, 43, 59, 45, 46, 47, 59, 59, 59, 51, 59, 53, 54, 55, 59, 57, 58, 59, 59, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 61, 61, 61, 3, 61, 61, 6, 7, 61, 9, 61, 11, 61, 13, 14, 15, 61, 61, 61, 19, 61, 21, 22, 23, 61, 25, 26, 27, 61, 29, 30, 31, 61, 61, 61, 35, 61, 37, 38, 39, 61, 41, 42, 43, 61, 45, 46, 47, 61, 61, 61, 51, 61, 53, 54, 55, 61, 57, 58, 59, 61, 61, 62, 63, 62, 62, 62, 3, 62, 62, 6, 7, 62, 9, 62, 11, 62, 13, 14, 15, 62, 62, 62, 19, 62, 21, 22, 23, 62, 25, 26, 27, 62, 29, 30, 31, 62, 62, 62, 35, 62, 37, 38, 39, 62, 41, 42, 43, 62, 45, 46, 47, 62, 62, 62, 51, 62, 53, 54, 55, 62, 57, 58, 59, 62, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1117111711171537111711171117153711171117111715370000000000000000111711171117153711171117111715371117111711171537000000000000000011171117111715371117111711171537111711171117153700000000000000001117111711171537000000000000000000000000000000000000000000000000111711171117153711171117111715371117111711171537000000000000000011171117111715371117111711171537111711171117153700000000000000001117111711171537111711171117153711171117111715370000000000000000111711171117153700000000000000000000000000000000000000000000000011171117111715371117111711171537111711171117153700000000000000001117111711171537111711171117153711171117111715370000000000000000111711171117153711171117111715371117111711171537000000000000000011171117111715370000000000000000000000000000000000000000000000001117111711171537111711171117153711171117111715370000000000000000111711171117153700000000000000001117111711171537000000000000000011171117111715371117111711171537000000000000000000000000000000001117111711171537000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac80000000000000000eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac80000000000000000eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac80000000000000000eee8eee8eee8eac8000000000000000000000000000000000000000000000000eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac80000000000000000eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac80000000000000000eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac80000000000000000eee8eee8eee8eac8000000000000000000000000000000000000000000000000eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac80000000000000000eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac80000000000000000eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac80000000000000000eee8eee8eee8eac8000000000000000000000000000000000000000000000000eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac80000000000000000eee8eee8eee8eac80000000000000000eee8eee8eee8eac80000000000000000eee8eee8eee8eac8eee8eee8eee8eac800000000000000000000000000000000eee8eee8eee8eac8000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8eee8eee8eee8eac8

def cMZZ : Nat := 0x1117111711171537000000000000000000000000000000000000000000000000111711171117153700000000000000000000000000000000000000000000000011171117111715370000000000000000111711171117153711171117111715371117111711171537000000000000000000000000000000000000000000000000111711171117153700000000000000000000000000000000000000000000000011171117111715370000000000000000000000000000000000000000000000001117111711171537000000000000000011171117111715371117111711171537111711171117153700000000000000000000000000000000000000000000000011171117111715370000000000000000000000000000000000000000000000001117111711171537000000000000000000000000000000000000000000000000111711171117153700000000000000001117111711171537111711171117153711171117111715370000000000000000000000000000000000000000000000001117111711171537000000000000000011171117111715370000000000000000111711171117153700000000000000000000000000000000111711171117153711171117111715370000000000000000111711171117153711171117111715371117111711171537

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
  | 2 => 1
  | 3 => 8
  | 4 => 115
  | 5 => 350
  | 6 => 231
  | 7 => 23
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0x206b9422
  | 3, 0 => 0xa8aff7007b241fc2589bebbf500bc18b446899ef3b539ecb1a91e4a0170306aa
  | 4, 0 => 0x49a324a94858d421467da3434323c5d841c00f5c4134f222408a0a143ef4175c3bf36013394201aa38b6122d38a4abc8374fcdb637277a50370ff051369c3bc635e6547234b7c04b32d0d40e32920b4a2e6c17a62e06fb342dc6224d2b75e6bb2887bc44286857422745dd1025fa14582475a85f22aa18a5208f578220762f061fe955b51e5133051e0c184c1d75156e1c60d7a91b5b0b8d1b4527331aa357d6193653fa18881714183e6f3c17bdd57f161424df15623f0814650a561421ac5413f0f9b41307760d128f36ab114d857310119dac0ce988d50a661c8609005087074a01c307358c790532b49a02f84b8802cf66a501f40859017fb6d3006e1b99
  | 4, 1 => 0xeeb08978dbd739bfd7b5e2dbd411713ed089a79ac8b7b691c5bbdd79c215183ebfc30c86be99859dbe1a7e22b9931ddfafb89171ad16f6b4a8e70adaa5596cd0a4decc30a1560bd09577fdce950ad04a90f434858faf0ecc8e3067348b0d6dfb822e708a7fa2689e7b81374878d7284b768823e676784be0745c9b206ef08fbf6a29f21d66b6430a6618dfbf65f6525165eaa54361fbba7f6139ff7e5dc5011e5c5c70235ad8404b546b25b7521ffc6850c650774f8fdc564e8e268c4bfca6604b89d1e34a142bf649b959de
  | 5, 0 => 0x12878c2d120b660411fd1a2411399dce10d6178b10bd2a1f108788b5103a6f321002c4ad0fea11320fba5c3e0e8cc2b20e6796820e2fad920de8148e0ddc647c0cf2b8490cd8c6100cb3d6700ca401da0c3c36d80bbe6e750bba92330bafb1580b7916070b7173dc0b52675a0b434e5c0b37ac6a0ac5962d0a83c8510a6770dd09afc15209ab99a009659efc0947510e093bcd85090b447508e3aa35082ba098081585670750edfa068ac0c605a1cd9d05a00a1c0552cbd505333a7f0524e8a104659efc03c1ba5c03be815803b435eb039bf02003433e91031ee86902fa9e4402171e480204c6c40188bb44015d22e8011f1c4500f6c3eb00975576006ca414
  | 5, 1 => 0x2966fab028d2d81528acac1128ab1f452899145227a01b83279a943f2785811826dc36a226d21b8f26c5f678265a6cd7258b252d255b5a7f2556a1e324a6f5b724a3cbf5248997a323e4fd7123db806b237b93b022ceff0422ae062522a57b2322914fb32274f555225c8cda221e56d221b19798212764411f1cefc41e5133051dbed4d21ccd68321c60d7a91bc02b2a1b4527331b0890ac1afd9afd1ac01cd71a4c1e73196b3ec51942eb5f18c5c4851873650b183e6f3c17b41c95173bec9b16e4877616a0b896162a76b8161d6fb0161424df159f8b1b151bffb41506ec7914abad2a143a1b5c13f64fd613ee098f13e2b3b213c961dc137a9b44128b41fc
  | 5, 2 => 0x4e3355824cc53a754caf2e604aab7a834a5241a849a324a94896cc9b4811c360472dc6cc472b347346fd2d3446c080534449e80a440209134371697d41f918504134f222407352c53fe604e93fd8513b3fccdb413fc8dcd33fc3e1853f2146a43cf3b15a3ca056633c1c51493c0fbe613b749ff13b601a263acc1e403a56a6f339bfb033396f44653949bd0e38a4abc83867313737f778f437ccdbf13797db503743b41b36899e0e368696c6368019983625a66735d5aa8d35c3b33f34fd042234e90f173467be903439a680335d0f0032e1c1862ffee0882f3755a72e1b6b872e18176f2dba91f22bd95dbc2ba351292b1cf6c12b1a00242a7445302a31fbcc
  | 5, 3 => 0x730fa59471c48f417157df4471348dee6fac6c9d6f301ad76f00efd56e2b7de96c98af246c61ab686b664b436b347ceb6a86cdcb6a03c03a69d72990690965df6835d5776754724966b6430a66aff61e65f65251641529b061fbba7f61d6577b619fcde56164457961387519610b54f660c3509b60b34395606974955fbc51805ec5ca355dee0fad5dcf96045dc5011e5c8969f35c5d475c5c2cc9c45c0f5fc05bbef26d5b6a33a85af2995a59ff0ab359fe1ff059ebeea5597b9fbe586cd47257bbc2745790554d55e3c39b53e3dadc53b11d04539cbc6f52dccbb65280a5f65214716851446dd0503a09504fcc0a9d4fc5baba4f5e98114ee233e44e8e268c
  | 5, 4 => 0xb55a30c8b2c89149b1b17ba2b0e565aeb0c9d821ad748aa5aca985eba9d50e0ea806acf9a7d74e88a5573d84a49158c4a430894da3017124a241806ba1de7d95a0341ecfa03116be9e9691fc9e87f6209e5051dd9d6758a09cb444229a747b019a2c20e098acd01597241ed1955d8a5994a5c57594943c4b947616b4931950c592fdeb6190f43485902e75898d6380228b027be98a8b18158a0f7d6189b068628889282688866c9e8797597086f8b65186600238853f3c22844f362583717cdf834764e9814487c980543a3f7fe43d457f9fe08f7f85045d7efdae587ddaadea78ab7d78783f351f77f599e075e5575575c76d4474e11b19747c404873adf9bd
  | 5, 5 => 0xfc0e3aa0f674221cf63d1d5ef4aaa7b5f3d5884cedebbd58ed5a7469e8a087a3e50fe888e0f88e3cdfa2541dde935321de38ca8fdaaa9887d9b0f77ad7b5e2dbd7542a99d2e7088ed00420c3c8b7b691c1a91e2cc151c04bc0f0b2b0c02984bebfc30c86ba0ceca4b9d153eab7859564b6ec13cab62ce24d
  | 6, 0 => 0x1ebbc7721ce78f4f1ce559ed1bdb21421b652e1d1ac01cd719e84d0019e764fb198989bf17f11b9c17df244e178f270b1718753116832f9f15fc259915d6ea251506ec7913e2b3b213b894f40f4e82180e9810fd0e6796820df4cecb0da870b20d48c3ff0cde9b810c2600970b826bbf0b7916070b52675a0aee49240ac690540a79606609e680d309afc15209ab99a009a0f22709659efc091d726208ed8c9e08e167870875dde607b50e7907302a6c059704bf04ef2a0a04ea701304c97734049066640477fde9044da5c30439c7e103cd08a703c1ba5c0342d55001ed65de01d797220188bb440160b184015d22e8013860d30123f90900c92d17006ca414
  | 6, 1 => 0x46309abf445d5be8437fb6884326c60542dec1aa42ceb4a43feb07133fd424843e78b86b3e2ad0cf3dda637c3d9a06283c1a7bc23c075fb43bf8f3393a4da3c239d73383390e7fd537ff34aa376a86d93680199835cc8e13354bac3c349c1705347acc5d34144031335fdedf3310599931e77bac317a09203143d54d304ec6912ffee0882fbcd3d62f3d92dc2eca9f6f2d4330282a6c34c02a31fbcc294937db29189e4328fa03fd27f447e52739231b2701a4f526d21b8f26cd62a526543d11261d7a2225aed614258cda8c24d5b1d5245492152414895f23e00eba228ec3d4226592f3225a2f6121f3c24a21ea634621e84c5021b1979820a1f27b1f395687
  | 6, 2 => 0x8a221e088772ae9386600238845cf17a835c9828824f8fde8133868780a3672f7ecfb5317acca89f76c1368476afad5a75c76d447534c1d475195c7074a67a3c73467b9d730fa5946fac6c9d6f00efd56aabea3a6aa499356aa1ddad69a4d61c69142760687b7347683319aa66aff61e666aa734635ff8d862ade6a961644579606974955c9e44605c8969f35c5d475c5be7693a5a5aa62e5800c86457e2de5356fc8c28540567b853966f8353735053534ffefd52c38c615243537251c7ddac51acfc56514b8be6511c60e44fc5baba4eb420334e7d1c774e4abede4e4600164d4fedfa4c1f31494b24d6ee496fe358493103af48cb672d4811c360472dc6cc
  | 6, 3 => 0xfc0e3aa0f9cf8d9ff674221ce3a42c4ee0f88e3cde935321de29abafd9b0f77ad88f932bd81fc710cfcc9166cd273459c313ff4bc0aec430c0543b9ebfc30c86bc33129fba904aa4ba0ceca4b9d153eab502799db432a3f4b216213eb0d67573aca985eba5abf516a5573d84a3c48f3ba36d315aa28a2388a1de7d959c285db399a106739775a1d796761ec393ccecb1923db6e98f8ffbb48ec4f6fa
  | 7, 0 => 0xe3a42c4ede29abafd88f932bc0aec430bfc30c86b216213eaca985eba1de7d9596761ec38772ae93835c9828687b734757e2de5351c7ddac511c60e4437fb6883e78b86b3d9a06283bf8f339294937db198989bf15d6ea2508ed8c9e
  | 8, 0 => 0xa1de7d95
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffffffffffff0000ffff0000ffff0000ffff000000000000ff000000ff00000055550000555500000f0f00000f0f00000000ffffffff00000000ffff000000000000cccccccc00000000aaaaaaaa000000000000ffff000000000000ff00000000000000cccc00000000000055550000000000000f0f0000000000000000
  | 0, 1 => 0xf0f0f0f0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000ffff00000f00ff000f00ff000f000f00ff00ff000c0c0c0c0c0c0c0c0505050505050505030303030303030300ffffff00ffffff00ff00ff00ff00ff00ff00ff0000000000f000f000f0f0f000f000f000f000f000cc00cc00cc00cc000f000f000f000f
  | 0, 2 => 0x555500005555000050f050f050f050f044444444444444443f3f3f3f3f3f3f3f33ff33ff33ff33ff3333ffff3333ffff3333ffff000000003333333333333333330033003300330030303030303030302a2a2a2a2a2a2a2a222222222222222211111111111111110fff0fff0fff0fff0fff0fff0fff00000fff00000fff0000
  | 0, 3 => 0xa0a0a0a0a0a00000a0a00000a0a000008888888888888888888888888888000088880000888800008800880088008800777777777777777777777777777700007777000077770000707070707070707055ff55ff55ff000055ff55ff0000000055555555ffffffff555555555555ffff55555555555555555555555555550000
  | 0, 4 => 0xaaaaaaaaffffffffaaaaaaaaaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a0aaaaaaaaaaaa0000aaaaaaaa88888888aaaaa0a0aaaaa0a0aaaa0000aaaa0000aaaa000000000000aaa8aaa8aaa8aaa8aaa0aaa0aaa0aaa0aa88aa88aa88aa88aa00aa00aa00aa00aa000000aa000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0
  | 0, 5 => 0xcccc0000ffff0000cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0cc00cc00cc00cc00cc00cc0000000000c8c8c8c8c8c8c8c8c0f0c0f0c0f0c0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c0c0c000000000c000c000c000c000afafafafafafafafafaf0000afaf0000af00af00af00af00
  | 0, 6 => 0xecececec00000000eccceccceccceccceaeaeaeaeaeaeaeaeaeaeaeaaaaaaaaae0e0e0e0e0e0e0e0ddddddddddddddddcfcfcfcfcfcfcfcfccffccffccff0000ccccccccccccccccccccccccccccc8c8ccccccccccccc0c0cccccccccccc8888cccccccccccc0000ccccccccc0c0c0c0cccccccc00000000cccc8888cccc8888
  | 0, 7 => 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeecccceeeeeeeeeeee0000eeeeeeeecccccccceeeeeeee00000000eeeeaaaaeeeeaaaaeeee0000eeee0000eecceecceecceecceecceecceecccccceecceecccccccccceeaaeeaaeeaa0000eeaaeeaaaaaaaaaaee00ee00ee00ee00ee00ee00ee00aa00ececececececececececececececcccc
  | 0, 8 => 0xf0f0f0f0f0f0f0c0f0f0f0f0f0f0e0e0f0f0f0f0f0f0c0c0f0f0f0f0f0f0a0a0f0f0f0f0f0f00000f0f0f0f0c0c0c0c0f0f0f0f000000000f0f0f000f0f0f000f0f0e0e0f0f0e0e0f0f00000ffff0000f0f00000f0f00000f0e0f0e0f0e0f0e0f0a0f0a0f0a0f0a0f000f000f000f000f000f000f0000000f000f00000000000
  | 0, 9 => 0xfaf0faf0faf0faf0faf0faf0faf0f0f0faaafaaafaaafaaafa00fa00fa00fa00f8f8f8f8f8f8f8f8f8f8f8f8f0f0f0f0f8f8f0f0f8f8f0f0f8f0f8f0f8f0f8f0f5f5f5f5f5f50000f3f3f3f3f3f3f3f3f3f0f3f0f3f0f3f0f1f1f1f1f1f1f1f1f0fff0fff0fff0fff0f0f0f0f0f0fffff0f0f0f0f0f0f3f3f0f0f0f0f0f0f0f0
  | 0, 10 => 0xfefefefefefefefefefefefe00000000fcfcfcfcfcfcfcfcfcfcfcfcfcfcf0f0fcfcfcfcfcfc0000fcfcfcfcf0f0f0f0fcfc0000fcfc0000fcf0fcf0fcf0fcf0fcf0fcf0fcf0f0f0fcf0fcf0f0f0f0f0fcf00000fcf00000fafafafafafafafafafafafafafaaaaafafafafaaaaaaaaafafa0000fafa0000faf8faf8faf8faf8
  | 0, 11 => 0xff33ff3300000000ff00ffffff00ffffff00ff00ffffffffff00ff00ff00ffccff00ff00ff00ff00ff00ff00ff00f000ff00ff00ff00aa00ff00ff00ff003300ff00ff00ff000000ff00ff00cc00cc00ff00ff00aa00aa00ff00ff0000000000ff00f000ff00f000ff00cc00ff00cc00ff000000ff000000ff00000000000000
  | 0, 12 => 0xffccffccff00ff00ffccffcc00000000ffccff00ffccff00ffc0ffc0ff00ff00ffaaffaaffaaffaaffaaffaaffaaaaaaffaaffaaffaa0000ffaaffaaaaaaaaaaffaaffaa00000000ffaa0000ffaa0000ffa0ffa0ffa0ffa0ffa0ffa0ffa00000ffa0ffa0ff00ff00ff88ff88ff88ff88ff88ff88ff88ff00ff33ff33ff33ff33
  | 0, 13 => 0xfff0fff0fff0f0f0fff0fff0fff0eac0fff0fff0fff0aa00fff0fff0fff00000fff0fff0ff00ff00fff0fff0f0f0f0f0fff0fff000000000fff0ffc0fff0ffc0fff0ff00fff0ff00fff0ff00ff00ff00fff0f0f0fff0f0f0fff00000fff00000ffeeffeeffee0000ffccffccffccffccffccffccffccff00ffccffccffcc0000
  | 0, 14 => 0xffff3333ffff3333ffff00ccffff00ccffff000fffff000fffff0000ffff0000ffff0000ffaa0000ffff0000f0f00000ffff0000eeee0000ffff0000cccc0000ffff000000000000fffcfffcfffcfffcfffc0000fffc0000fffafffafffa0000fff0fff0fff0fff0fff0fff0fff0ffc0fff0fff0fff0ff00fff0fff0fff0faf0
  | 0, 15 => 0xffffeeaaffff0000ffffccccffffccccffffccccffffc0c0ffffccccffff8888ffffccccffff0000ffffc0c0ffffc0c0ffffc000ffffc000ffffaaaaffffaaaaffffaaaaffff0000ffffaaaaaaaaaaaaffffaa00ffff0000ffffa0a0ffffa0a0ffff8888ffff8888ffff8888ffff0000ffff8080ffff8080ffff3f3fffff0000
  | 1, 0 => 0xffffff33ffff0000ffffff00ffffff00ffffff00ffff0000fffffcfcfffffcfcfffffcfcffff0000fffffcf0ffff0000fffffafaffff0000fffff0f0fffff000fffff0f0ffffc0c0fffff0f0ffff0000fffff0f0f0f0f0f0fffff0c0fffff0c0fffff000fffff000fffff000ffff0000ffffeeeeffffeeeeffffeeeeffff0000
  | 1, 1 => 0xffffffff77770000ffffffff55555555ffffffff55550000ffffffff33003300ffffffff11111111ffffffff0fff0000ffffffff0f0f0f0fffffffff00ff0000ffffffff00550055ffffffff0000ffffffffffff00000000fffffff0fffffff0fffffff0ffff0000fffffff000000000ffffffccffffffccffffffaaffff0000
  | 1, 2 => 0xffffffffff000000fffffffff0f0f0f0fffffffff0f00000fffffffff000f000ffffffffeeee0000ffffffffccccccccffffffffcccc0000ffffffffcc00cc00ffffffffc8c8c8c8ffffffffc0c0c0c0ffffffffafaf0000ffffffffaaaaaaaaffffffffaaaa0000ffffffffaa00aa00ffffffffa0a00000ffffffff88888888
  | 1, 3 => 0xffffffffffff8888ffffffffffff8800ffffffffffff3333ffffffffffff3300ffffffffffff1111ffffffffffff0a0affffffffffff0303ffffffffffff00ffffffffffffff000fffffffffffff0000fffffffffffa0000fffffffffff00000ffffffffffee0000ffffffffffaaffaaffffffffffaa0000ffffffffff00ff00
  | 1, 4 => 0xfffffffffffffffffffffffffffffff0ffffffffffffffccffffffffffffff00fffffffffffffcfcfffffffffffff0f0fffffffffffff0c0fffffffffffff000ffffffffffffeeeeffffffffffffccccffffffffffffcc00ffffffffffffc8c8ffffffffffffc0c0ffffffffffffaaaaffffffffffffaa00ffffffffffffa000
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x378ce4d3
  | 3, 0, 0 => 0x9b384da6746ea40ce4d4a1b88ce4d4a6380ce4d470b7cce4d46e240f04d45daacda6745ca34ce4d4
  | 4, 0, 0 => 0x9b2ed1c6726acd976903391966c733599c9ab364819ca04d59b2ed3c6726aa40fa733393566cbb481b0ceb4c6faecce4d5a52ed1a6726ace97690339356994a7199c9ab3661a40ce4d599aed206726acd920672686966cbb481989ab0a5da40ce4d5
  | 4, 0, 1 => 0x9b2ed086726acd9ae903393568cdf5d99c9aaf05da40ce4d59b385206726ab7d768b33935656bb4819c9aabb4ba40ce4d586b6d206726acd576903393566cbb4699c9ab365da64ce4d5a0aed206726acd982903393566cbb4899c9ab366126cce4d5
  | 4, 0, 2 => 0x9b384ce5626ac7d769033935688bb4819c9ab3671240ce4d59b2ed207433ad05769f3393566cbb481c09ab425da34ce4d58d2ed206726acd9b09033935668d74819c9ab365da40dc4d55da40d06726ace57690339355f6db4819c9aab94819c9a4b5
  | 4, 0, 3 => 0xa42ed206726acd9c6903c13566cbb4a99c9ab3e5da40ce4d59b2ed0e6726ac4176903393566cbb4819c4ab365da3cce4d59daed206726acfd84903393561ebb4819c9ab365da6cce4d59b2ed406726acd920783993566cbb3393426b365da40ee4d5
  | 4, 0, 4 => 0x9b240e66726acd97890339355b8bb4819c9ab36481c8ce4d59faed206726ac0120733393566cbb339346cb36481e0b44d55da40ce4d1c2cd9989033935678bb4819c9aac95da40ce4d59b2ed306726ad0572903393566ce15219c9aadf5d99c9a4b5
  | 4, 0, 5 => 0xa1b8d766726acd976903c1355b8bb5219c9ab255da40ce4d59b3891a6726acd976a73393566cbb459b4ceadc5d99cac4d59b2ecce4d172d0d76903699d5c8bb4819c9ab365c240ce4d57faed206726ab11769033935576903e99c9aad35da40ce4d5
  | 4, 0, 6 => 0x9b349205b26acdd769033935668bb4819c9ab366b240ce4d59b2ed286726acd97690339355c2dc4819c9ab156bb54ce4d55da40ea6726aaed206726885680bb4819c9ab365da7cf04d564a40ce4d21ad2576903393566cbb569b4cead264a40ce4d5
  | 4, 0, 7 => 0x2ed2067268d5576b74699c9ab365da7cce4d5
  | 5, 0, 0 => 0x9b2ed2067268c1a58ec5da40ce4d6a1aed20672b135a2afc5da40ce4d69b3b1769f33935a6cbb4819c9a0368aaed206728935a83155da40ce4d69fc81769033935a2aec5da10ce4d6004d97690338c566cbb4819c9a4869b2ed207a33935a6cd25ba40ce4d68abb1bebb33935a2aec6ba40ce4d6
  | 5, 0, 1 => 0x8ab19769033935a85365da40ce4d69b2ed206726839a6d1570a40ce4d6a3509769033935a6cbb52240fe6769b335769033935a57155da40ce4d68abb1769037135a5ebb4819c9a486a12ed208b33935a2eec5da40ce4d69b2f5769033935a6cbb49240ce4d69b2ed206726911a6d155da34ce4d6
  | 5, 0, 2 => 0x9b2ed208833935a6cbb4599cac4d68aba5769033935a6cbb4819c9a3e69b479769033935a38ec5da40ce4d69b2ed2067269099d8bb4819c9a2969b4c1769033935a6cbb4819c9a33676365769033935a6cbb4819c9a4a69b455ae90339359d8bf5da40ce4d68abb1b09033935a2b085da40ce4d6
  | 5, 0, 3 => 0xa54d9c6bb33935a6cbb4819c9c4d68abcd8490339359c6dc5da40ce4d69b431769033935a94bb4819c9a4b68abb176903a19da6cbb48228ce4d69b2ed2067268c9a6cbb4819c9a0269b2ed429033935a6d2c5da40ce4d69b2ed20672690da6cbb56240ce4d69b2ed2067268b5a6cbb4819c9a476
  | 5, 0, 4 => 0x9b349969033935a2aec4819c9a1b69b35d769033935a6cd95da40ce4d60050576903393562af95da40ce4d68abf9aabb33935a6cbb56a40ce4d68ac25769033935a6ce15da40ce4d68abad769033935a44ec71a40ce4d69b2ed208933935a7ebb4819c9a3d69b2ed509033935a6cbb5b240ce4d6
  | 5, 0, 5 => 0x9b2ed20672681da2b045da40ce4d6004d9c2903393567b365da40ce4d6004ad76903393566cbb4819c9a3c68abb176902e135a2aec5da6cce4d68ab55a8bb33935a2aec5da80ce4d68abb1207839935a6cdf5dadcce4d6a1c99769033935801365da34ce4d5a7cd9769033935a6cf45da40ce4d6
  | 5, 0, 6 => 0x9b2ed206732135a6cbb4819caa4d68ab55768533935a2aec5da1cce4d69b2ed207933935a6cbb54a40ce4d69b2ed20672682da2aec5da40ce256a440d769033935a6d195da40ce4d69b2ed206729935a6cbb4819c9a2b69b2ed20672692da6d115da40ce4d69b3a1769033935801366ba40ce4d5
  | 5, 0, 7 => 0x9b2ed206726925a6cbb58240ce4d68ebb1769033935a6d015da40ce4d68abb1769533935a26ec5da40ce4d68abb1769a33935a6ce65da40ce4d685bb1769033935a6d2a5da40ce4d69b32d20672690da6cbb4f99c9a4369b455769b33935a2ae55da40ce4d69b2ed2067268fda6d156d2ecce4d6
  | 5, 0, 8 => 0xa12ed20672692da6cbb4819c9a2f68abb9769033935a2af15da40ce4d68abb1989033935800bb4819c9a055a42ed208233935a2b105da40ce4d68abb1769833935a44ec5da40f04d69b2ed206733935a30ec5da40ce4d6762ed206f33935976903d9e4ce4d68abb1c6903c135a52ec5da40ce4d6
  | 5, 0, 9 => 0x4d92067188555d8bb4819c9a3469b2ed206726859801365da6cce4d58abf5769033935a2abb4819c9a2069b2ed206933935a2abb52a40ce4d68aaed20672f935a91155da40ce4d68abb120782d135a2af35da40ce4d68ac1d769033935a6cbb4819c9a0c69b2ed2067268b1a6d295da40ce4d6
  | 5, 0, 10 => 0x44176903393566cbb55240ce4d694aed206726921a6cbb4819c9a2669b2ed206a339359d8db4819cc24d6762ed5c9033935a85365ca40ce4d68abb17667268d9a6cbb4819c9a1868aaed208633935a5d065da40ce4d68ab25769033935a5cf75da40ce4d69b2ed206726829a24ec5da40ce4d6
  | 5, 0, 11 => 0x9b2ed206726845a83365da40ce4d69b2ed207133935a7f155da40ce4d68abb5769033935801485da40ce4d58aaed206726871a2aec481ccce4d69b2ed206726901a56ec5da40ce4d69b2ed20672683da6cbb4819c9a0168abb176903b135a6cbb4819c9a3b69b35576b133935a6cbb48240ce4d6
  | 5, 0, 12 => 0x9b2ed208033935a56bb481fcce4d69b2ed20672688da6cbb4819c9a1d69b459769033935a2abb481f4ce4d69b45520733393580136481345015589b65769033935a6cc24819c9a3d685aed5a9033935a6cf65da40ce4d68aaed206726821a6cbb49a40ce4d68ab71769033935800c95da40ce4d5
  | 5, 0, 13 => 0x65b25769033935a6cbb51a40ce4d69b2ed2073339358013f5da40ce4d5913b1769033935801365d99c9a1e55da41166731935801365da40622859b3a9769033935a2af55da40ce4d68abb17667268b9a6cbb4819c9e4d68ac19b69033935a6cbb4fa40ce4d693bb1769033935a62c65da40ce4d6
  | 5, 0, 14 => 0x240ce4d0a81566d225da40ce4d6002ed207d3393566cbb4819c9a056004d920733393566d205da40ce4d60037176903393566cca5da40ce4d68abc9769033935a6ce75da40ce4d69b2ed206726811a6cbb4819c9a2269b4b9c6bb33935a6cbb339589a40696bb1769033935a4cfa5da40ce4d6
  | 5, 0, 15 => 0x8abb176903c135800bb4819c620559b2ed20672689da6cbb481b4ce4d69b2ed489033935a6cbb4819c9a1469b38d769033935a9d365da40ce4d69b2ed206726915a6cbb4819c9a416a5cd9769033935a6d2d5da40ce4d692419769033935a6cbb481b4ce566923dd769033935a6cbb4819c9a106
  | 5, 1, 0 => 0x9b2ed207e33935a6cbb4819c9a196a44d9769033935a2a903c9ccce4d69b2ed206732935a2abb4819c9a37695aed207933935a6d155da40f04d6983b1b4bb33935a6cc85da40ce4d69a38d769033935a6cbb4819cc44d69b2ed2067268f5a6cbb5219c9a406913b1769f33935a2b025da40ce4d6
  | 5, 1, 1 => 0x9b2ed3a9033935801365da40f04d563b19769033935a6cbb48230ce4d68abb1769f3c135976903398c9a4b697aed208533935a6cd05da40ce4d69b451769033935a6ce35d99cac4d69b2ed20672687da6cbb4819c9a0d69b2ed2067268a1a6cc95da40ce4d69b301769033935a2aec5dab4da676
  | 5, 1, 2 => 0x9b2ed2067268e5a9b365da40ce4d68dbb1769033935a6cbb51240ce4d691aed629033935a6cbb481f4ce4d69b38d76a433935a6cbb48234ce4d66cb51769033935a6cdc5da40ce4d6a2cd9769033935a6cd15da40ce4d69b41576903393580136339343c1559fcd9769033935a6cc25da40ce4d6
  | 5, 1, 3 => 0x9b2ed2c9033935a42ec5da40ce4d69b2ed2067268e9a6cbb4819c9a4c69640d769033935a6cbb4e240ce4d69b455769033935a612e7638cce4d69b2ed208333935a2aec6b240ce4d69b2ed208233935a98bb5ba40ce4d68abb1769433935976903f9f4ce4d69b240fe7333935a2aec5da40ce4d6
  | 5, 1, 4 => 0x8aaed207933935801365da7cce4d58abb1729033935a6cbb4819ca44d6a6529769033935801345da40ce4d59b2ed206726801a6cbb4819c9a1269c4d9769033935a2aec5da98ce4d6004d976903393566cbb5ba40ce4d68abb1769f33935a6cbb57a40ce4d65dadd208b33935a2aec69240b64d6
  | 5, 1, 5 => 0x9b2ed207f33935a6d365da40ce4d68abb1849b33935a2aec399acce4d6a3cd9769033935a40f35da40ce4d69b2ed749033935a2b135da40ce4d6a5519769033935a99365da40ce4d69b2ed208133935a6cbb4819c9a1e69b2ed20672685da2aec5d99cae4d6
  | 6, 0, 0 => 0x8cc55d8bb4819c9af15762ed206729935e2aec5da40ce4d153c55d8bb4819c9a2b78abb176903393496e00963b1769033935a2b11762ed206726bcda2abb56a40ce4d7953b17690339849ae00004d97690338c5401155da40ce310730026cbb4819c9a4868abb1d0bb4819c9af26762ed20672b135e6d155da41126726b8022aec6ba40ce4d6
  | 6, 0, 1 => 0x9b3b17690339343ce008b45576903393580115632ed206726b00285365da40ce4d68abb1ccbb4819c9ae009b2ed206726839a2b065da41126726bcaa2aec5da40ce4d78abb196903393486f15762ed3e672690de6515762ed206726b8026d155da409a2868abb176903c99c9af15762f9769033935e2aec5daa5206726bc55d8bb4819c9a0b7
  | 6, 0, 2 => 0x4d976ad4819c9ac009b2ed208933935a6d2a8aaed206726bc81d8bb4819c9a3d79b45576903393496e009b2ed20672690da2aec5da40ce6726bc55d8d55da40ce4d78abb17690339509af4c9b3b1769033935e2aec67aed206726bc55d8bb4819c9a497004da60bb4819c9ac0076365769033935a2aec5dac1206726bc5602ec5da40ce4d7
  | 6, 0, 3 => 0x8abb176903393430f15762ed206726829c01155da40ce4d02b0022aec4819c621568abb17690339342ce008abb1769b33935a2aec5da40d26726bc5596c65da40ce4d78abb17690339789af15762ed206726831e2aec5da40ce4d163cd9d8ec5da40ce4d794c55d8bb4819c9af15762ed2067268bde2abb481fcf26726bcba2aec5da40ce4d7
  | 6, 0, 4 => 0x8abb176903393476f15762ed649033935e2aec6aaed626726bc55d8bb56a90ce4d79b4557690339789af15762ed209033935c013676240ce4d0ab455d8bb55240ce4d79b3b176b44819c9af369b3b1769033935e2aec5da40ce4d133d1a6cec5da40ce4d78abb176903519c9ae009b2ed20672692da6d2e8aaed206726bcd9d8bb4822cce4d7
  | 6, 0, 5 => 0x17690339340ab15762ed20672c135e2abb4819cbc4d243c55d8bb481c4ce4d79b3b176903393490f3676349769033935c0129762ed206726b455d8bb4819c9a4078abb17690339341ef15762ed206726819e6cec5da40fe6726bcda2b0e5da40ce4d78abb176903e19c9ae009b4a9769033935a6d157c2ed206726bc55d8bb4819cba4d7
  | 6, 0, 6 => 0x8abb176904019c9af1577bb1769033935e2aec5da40ce4d11bcc1d8bb5a240ce4d700455e6bb4819c9ad168abb1769033935e6cec5da40ce4d0738022aec48134501568ac0d76904119c9af368aaed206726901e2aec61240ce4d1eb801d8bb339343c0968abd9d8bb4819c9af15762ed269033935e2abb4819c9a09043c55d8bb4819c9a117
  | 6, 0, 7 => 0x90455d8bb4819c9ae005da40ce4d04821a2aec73aed206726bc55d8bb4819c9a22797455d8e35d99c9af15762ecce5626901e2aec5da40e66726bbb176b448224ce4d700455d8bb339343cc008abb17690188a1a2aec752ed206726bc55d8bb4819cac4d78abb176903393c9af15762ed3e9033935e2aec5dac5206726bcd9d8bb4819c9a437
  | 6, 0, 8 => 0x8aaed62903393490f15762ed206726851e2aec71aed206726b8022abb4819c9a0868abb17690339348af15762ed206726905e6d1573aed206726bc55f6bb4819cc24d796c55d8bb4819c9af15762ed206d33959e2aec5da40ce4d083c8a2aec5da40ce4d78abb176903393448f15762ed206726815c011576240e66726b0026cbb4819c9a406
  | 6, 0, 9 => 0x4b5d8bb4819c9ad1576351769033935c0122762ed206726b00001365d99c9a1e59b455c6bb4819c9af1576321769033935e2aec5da40ce6226bc55d8bb4819c9a3d78abb176a43393480f15762ed206730135e6d155da40ce4d02bc55d8bb4819c9a2778abb176903699c9af2a762ed689033935e2aec5da40ce5926bc55d8bb52240ce4d7
  | 6, 0, 10 => 0x9b45576903393450e008abb176903c135801365da91206726b0026ce35da40ce4d68ac39f0bb4819c9af158a3b1769033935e2aec71aecce5626bca22aec5da40ce4d78abb17690339341af15762ed2067268a1e2b0e5da40ce5e26b8026cbb4819c9a0568abb180bb4819c9af15762ed206726865e6d155da40ce4d1eb8026ce75da40ce4d6
  | 6, 0, 11 => 0x8abb176904199c9af15762ed208233935c01365da40ce4d143455d8903f9ccce4d78abb176903393412f15762ed2067268e5e2aec5dacd206726bc55d8bb51240ce4d78abb1c6bb5219c9af1581bb1769033935e2b05762ed206726b8022aec339343c156004d97690339347ad1576309769033935e2aec5da75206726bcc25cec5da40ce4d7
  | 6, 0, 12 => 0x8abb1a4bb481fc9ae009b455769033935a2afe7c2ed206726b8026cbb48208ce4d68abb176903393400f15762ed206726849e2aec5dad5206726b8022aec5da40ce4d68abb176b74819c9af15762ed5e9033935e2aec5da59206726b801d8bb4819c9a0968abb176903393474f368aaed208233935e2aec5da71206726bc562aec5da40ce4d7
  | 6, 0, 13 => 0x45576903c99c9ad368abb1769033935e8d15762ed206726bc55d8ce5da40ce4d79b3b176903393412f4c8abb1769033935e2aec5da40ce4d0f3c55d8bb4819c9a177000026cbb4819c9ab1576315769033935dd8e36caed206726b8026cbb5ba40ce4d600455d8bb4f99c9ad15762ed206729135c00bb4819c9a0e04b455d8cb5da40ce4d7
  | 6, 0, 14 => 0x9b2ed207f33935a9f15762ed206726b8026d365da40ce4d600455d8bb4819c62c00a64d9769033935801365da40ce4d0f3455d8bb481fcce4d7
  | 7, 0, 0 => 0x22aec5da40ce4d600001d8bb4819c9a09600455d8bb48208ce4d700455d8bb4819c9a09700455d8bb4819c9a28700455d8bb4819c9a3d700455d8bb52240ce4d700455d8e35da40ce4d700455d8e75da40ce4d7000022aec5d99c9a1e600455d8bb4819cac4d700455d8bb58a40ce4d700455d8bb4819c9a40700455d8bb4819cbc4d7004ba2aec5da40ce4d7004aa2aec5da40ce4d7
  | 7, 0, 1 => 0x22aec5da40ce31600455d8bb481fcce4d7004da2aec5da40ce4d700455d8bb4819c9a1e70000001365da40ce4d500455d8cb5da40ce4d7000026d155da40ce4d6
  | 8, 0, 0 => 0x22aec5da40ce4d6
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 2 => 31
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

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1024), (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000, 64), (0x22222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222, 1), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000, 256), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000, 64), (0x22222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222, 1), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000, 256), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1024), (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]

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
private theorem z2_0 : span (Z 2) 1 0 = true := by decide +kernel

private theorem z2 : span (Z 2) 1 0 = true := z2_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : span (Z 3) 8 0 = true := by decide +kernel

private theorem z3 : span (Z 3) 8 0 = true := z3_0

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
private theorem z4_96 : span (Z 4) 19 96 = true := by decide +kernel

private theorem z4_a1 : span (Z 4) 48 0 = true :=
  span_join (f := Z 4) (a := 24) (o := 0) (b := 24) z4_0 z4_24

private theorem z4_a2 : span (Z 4) 72 0 = true :=
  span_join (f := Z 4) (a := 48) (o := 0) (b := 24) z4_a1 z4_48

private theorem z4_a3 : span (Z 4) 96 0 = true :=
  span_join (f := Z 4) (a := 72) (o := 0) (b := 24) z4_a2 z4_72

private theorem z4_a4 : span (Z 4) 115 0 = true :=
  span_join (f := Z 4) (a := 96) (o := 0) (b := 19) z4_a3 z4_96

private theorem z4 : span (Z 4) 115 0 = true := z4_a4

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
private theorem z5_336 : span (Z 5) 14 336 = true := by decide +kernel

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

private theorem z5_a14 : span (Z 5) 350 0 = true :=
  span_join (f := Z 5) (a := 336) (o := 0) (b := 14) z5_a13 z5_336

private theorem z5 : span (Z 5) 350 0 = true := z5_a14

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
private theorem z6_216 : span (Z 6) 15 216 = true := by decide +kernel

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

private theorem z6_a9 : span (Z 6) 231 0 = true :=
  span_join (f := Z 6) (a := 216) (o := 0) (b := 15) z6_a8 z6_216

private theorem z6 : span (Z 6) 231 0 = true := z6_a9

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : span (Z 7) 23 0 = true := by decide +kernel

private theorem z7 : span (Z 7) 23 0 = true := z7_0

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

def CG : Circuit := ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12573

theorem PEqualNP.Outside.L_meta_12573 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008242920 * 2 ^ 32 + 4008241864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008242920 * 2 ^ 32 + 4008241864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12573.mainG PEqualNP.Outside.L_meta_12573.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12573.CG, PEqualNP.Outside.L_meta_12573.CG_mono, by
      have : PEqualNP.Outside.L_meta_12573.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12573.CG_eval⟩
