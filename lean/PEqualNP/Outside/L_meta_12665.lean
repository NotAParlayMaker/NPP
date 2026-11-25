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
namespace PEqualNP.Outside.L_meta_12665

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 3974686952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 3, 3, 3, 3, 3, 5, 6, 7, 3, 3, 3, 11, 3, 13, 14, 15, 3, 3, 3, 19, 3, 21, 22, 23, 3, 3, 26, 27, 3, 29, 30, 31, 3, 33, 3, 35, 3, 37, 38, 39, 3, 41, 3, 43, 3, 45, 46, 47, 3, 49, 3, 51, 3, 53, 54, 55, 3, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 5, 5, 5, 3, 5, 5, 6, 7, 5, 5, 5, 11, 5, 13, 14, 15, 5, 5, 5, 19, 5, 21, 22, 23, 5, 5, 26, 27, 5, 29, 30, 31, 5, 33, 5, 35, 5, 37, 38, 39, 5, 41, 5, 43, 5, 45, 46, 47, 5, 49, 5, 51, 5, 53, 54, 55, 5, 57, 58, 59, 60, 61, 62, 63, 6, 6, 6, 3, 6, 5, 6, 7, 6, 6, 6, 11, 6, 13, 14, 15, 6, 6, 6, 19, 6, 21, 22, 23, 6, 6, 26, 27, 6, 29, 30, 31, 6, 33, 6, 35, 6, 37, 38, 39, 6, 41, 6, 43, 6, 45, 46, 47, 6, 49, 6, 51, 6, 53, 54, 55, 6, 57, 58, 59, 60, 61, 62, 63, 7, 7, 7, 3, 7, 5, 6, 7, 7, 7, 7, 11, 7, 13, 14, 15, 7, 7, 7, 19, 7, 21, 22, 23, 7, 7, 26, 27, 7, 29, 30, 31, 7, 33, 7, 35, 7, 37, 38, 39, 7, 41, 7, 43, 7, 45, 46, 47, 7, 49, 7, 51, 7, 53, 54, 55, 7, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 11, 11, 11, 3, 11, 5, 6, 7, 11, 11, 11, 11, 11, 13, 14, 15, 11, 11, 11, 19, 11, 21, 22, 23, 11, 11, 26, 27, 11, 29, 30, 31, 11, 33, 11, 35, 11, 37, 38, 39, 11, 41, 11, 43, 11, 45, 46, 47, 11, 49, 11, 51, 11, 53, 54, 55, 11, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 13, 13, 13, 3, 13, 5, 6, 7, 13, 13, 13, 11, 13, 13, 14, 15, 13, 13, 13, 19, 13, 21, 22, 23, 13, 13, 26, 27, 13, 29, 30, 31, 13, 33, 13, 35, 13, 37, 38, 39, 13, 41, 13, 43, 13, 45, 46, 47, 13, 49, 13, 51, 13, 53, 54, 55, 13, 57, 58, 59, 60, 61, 62, 63, 14, 14, 14, 3, 14, 5, 6, 7, 14, 14, 14, 11, 14, 13, 14, 15, 14, 14, 14, 19, 14, 21, 22, 23, 14, 14, 26, 27, 14, 29, 30, 31, 14, 33, 14, 35, 14, 37, 38, 39, 14, 41, 14, 43, 14, 45, 46, 47, 14, 49, 14, 51, 14, 53, 54, 55, 14, 57, 58, 59, 60, 61, 62, 63, 15, 15, 15, 3, 15, 5, 6, 7, 15, 15, 15, 11, 15, 13, 14, 15, 15, 15, 15, 19, 15, 21, 22, 23, 15, 15, 26, 27, 15, 29, 30, 31, 15, 33, 15, 35, 15, 37, 38, 39, 15, 41, 15, 43, 15, 45, 46, 47, 15, 49, 15, 51, 15, 53, 54, 55, 15, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 19, 19, 19, 3, 19, 5, 6, 7, 19, 19, 19, 11, 19, 13, 14, 15, 19, 19, 19, 19, 19, 21, 22, 23, 19, 19, 26, 27, 19, 29, 30, 31, 19, 33, 19, 35, 19, 37, 38, 39, 19, 41, 19, 43, 19, 45, 46, 47, 19, 49, 19, 51, 19, 53, 54, 55, 19, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 21, 21, 21, 3, 21, 5, 6, 7, 21, 21, 21, 11, 21, 13, 14, 15, 21, 21, 21, 19, 21, 21, 22, 23, 21, 21, 26, 27, 21, 29, 30, 31, 21, 33, 21, 35, 21, 37, 38, 39, 21, 41, 21, 43, 21, 45, 46, 47, 21, 49, 21, 51, 21, 53, 54, 55, 21, 57, 58, 59, 60, 61, 62, 63, 22, 22, 22, 3, 22, 5, 6, 7, 22, 22, 22, 11, 22, 13, 14, 15, 22, 22, 22, 19, 22, 21, 22, 23, 22, 22, 26, 27, 22, 29, 30, 31, 22, 33, 22, 35, 22, 37, 38, 39, 22, 41, 22, 43, 22, 45, 46, 47, 22, 49, 22, 51, 22, 53, 54, 55, 22, 57, 58, 59, 60, 61, 62, 63, 23, 23, 23, 3, 23, 5, 6, 7, 23, 23, 23, 11, 23, 13, 14, 15, 23, 23, 23, 19, 23, 21, 22, 23, 23, 23, 26, 27, 23, 29, 30, 31, 23, 33, 23, 35, 23, 37, 38, 39, 23, 41, 23, 43, 23, 45, 46, 47, 23, 49, 23, 51, 23, 53, 54, 55, 23, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 26, 26, 26, 3, 26, 5, 6, 7, 26, 26, 26, 11, 26, 13, 14, 15, 26, 26, 26, 19, 26, 21, 22, 23, 26, 26, 26, 27, 26, 29, 30, 31, 26, 33, 26, 35, 26, 37, 38, 39, 26, 41, 26, 43, 26, 45, 46, 47, 26, 49, 26, 51, 26, 53, 54, 55, 26, 57, 58, 59, 60, 61, 62, 63, 27, 27, 27, 3, 27, 5, 6, 7, 27, 27, 27, 11, 27, 13, 14, 15, 27, 27, 27, 19, 27, 21, 22, 23, 27, 27, 26, 27, 27, 29, 30, 31, 27, 33, 27, 35, 27, 37, 38, 39, 27, 41, 27, 43, 27, 45, 46, 47, 27, 49, 27, 51, 27, 53, 54, 55, 27, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 29, 29, 29, 3, 29, 5, 6, 7, 29, 29, 29, 11, 29, 13, 14, 15, 29, 29, 29, 19, 29, 21, 22, 23, 29, 29, 26, 27, 29, 29, 30, 31, 29, 33, 29, 35, 29, 37, 38, 39, 29, 41, 29, 43, 29, 45, 46, 47, 29, 49, 29, 51, 29, 53, 54, 55, 29, 57, 58, 59, 60, 61, 62, 63, 30, 30, 30, 3, 30, 5, 6, 7, 30, 30, 30, 11, 30, 13, 14, 15, 30, 30, 30, 19, 30, 21, 22, 23, 30, 30, 26, 27, 30, 29, 30, 31, 30, 33, 30, 35, 30, 37, 38, 39, 30, 41, 30, 43, 30, 45, 46, 47, 30, 49, 30, 51, 30, 53, 54, 55, 30, 57, 58, 59, 60, 61, 62, 63, 31, 31, 31, 3, 31, 5, 6, 7, 31, 31, 31, 11, 31, 13, 14, 15, 31, 31, 31, 19, 31, 21, 22, 23, 31, 31, 26, 27, 31, 29, 30, 31, 31, 33, 31, 35, 31, 37, 38, 39, 31, 41, 31, 43, 31, 45, 46, 47, 31, 49, 31, 51, 31, 53, 54, 55, 31, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 33, 33, 33, 3, 33, 5, 6, 7, 33, 33, 33, 11, 33, 13, 14, 15, 33, 33, 33, 19, 33, 21, 22, 23, 33, 33, 26, 27, 33, 29, 30, 31, 33, 33, 33, 35, 33, 37, 38, 39, 33, 41, 33, 43, 33, 45, 46, 47, 33, 49, 33, 51, 33, 53, 54, 55, 33, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 35, 35, 35, 3, 35, 5, 6, 7, 35, 35, 35, 11, 35, 13, 14, 15, 35, 35, 35, 19, 35, 21, 22, 23, 35, 35, 26, 27, 35, 29, 30, 31, 35, 33, 35, 35, 35, 37, 38, 39, 35, 41, 35, 43, 35, 45, 46, 47, 35, 49, 35, 51, 35, 53, 54, 55, 35, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 37, 37, 37, 3, 37, 5, 6, 7, 37, 37, 37, 11, 37, 13, 14, 15, 37, 37, 37, 19, 37, 21, 22, 23, 37, 37, 26, 27, 37, 29, 30, 31, 37, 33, 37, 35, 37, 37, 38, 39, 37, 41, 37, 43, 37, 45, 46, 47, 37, 49, 37, 51, 37, 53, 54, 55, 37, 57, 58, 59, 60, 61, 62, 63, 38, 38, 38, 3, 38, 5, 6, 7, 38, 38, 38, 11, 38, 13, 14, 15, 38, 38, 38, 19, 38, 21, 22, 23, 38, 38, 26, 27, 38, 29, 30, 31, 38, 33, 38, 35, 38, 37, 38, 39, 38, 41, 38, 43, 38, 45, 46, 47, 38, 49, 38, 51, 38, 53, 54, 55, 38, 57, 58, 59, 60, 61, 62, 63, 39, 39, 39, 3, 39, 5, 6, 7, 39, 39, 39, 11, 39, 13, 14, 15, 39, 39, 39, 19, 39, 21, 22, 23, 39, 39, 26, 27, 39, 29, 30, 31, 39, 33, 39, 35, 39, 37, 38, 39, 39, 41, 39, 43, 39, 45, 46, 47, 39, 49, 39, 51, 39, 53, 54, 55, 39, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 41, 41, 41, 3, 41, 5, 6, 7, 41, 41, 41, 11, 41, 13, 14, 15, 41, 41, 41, 19, 41, 21, 22, 23, 41, 41, 26, 27, 41, 29, 30, 31, 41, 33, 41, 35, 41, 37, 38, 39, 41, 41, 41, 43, 41, 45, 46, 47, 41, 49, 41, 51, 41, 53, 54, 55, 41, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 43, 43, 43, 3, 43, 5, 6, 7, 43, 43, 43, 11, 43, 13, 14, 15, 43, 43, 43, 19, 43, 21, 22, 23, 43, 43, 26, 27, 43, 29, 30, 31, 43, 33, 43, 35, 43, 37, 38, 39, 43, 41, 43, 43, 43, 45, 46, 47, 43, 49, 43, 51, 43, 53, 54, 55, 43, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 45, 45, 45, 3, 45, 5, 6, 7, 45, 45, 45, 11, 45, 13, 14, 15, 45, 45, 45, 19, 45, 21, 22, 23, 45, 45, 26, 27, 45, 29, 30, 31, 45, 33, 45, 35, 45, 37, 38, 39, 45, 41, 45, 43, 45, 45, 46, 47, 45, 49, 45, 51, 45, 53, 54, 55, 45, 57, 58, 59, 60, 61, 62, 63, 46, 46, 46, 3, 46, 5, 6, 7, 46, 46, 46, 11, 46, 13, 14, 15, 46, 46, 46, 19, 46, 21, 22, 23, 46, 46, 26, 27, 46, 29, 30, 31, 46, 33, 46, 35, 46, 37, 38, 39, 46, 41, 46, 43, 46, 45, 46, 47, 46, 49, 46, 51, 46, 53, 54, 55, 46, 57, 58, 59, 60, 61, 62, 63, 47, 47, 47, 3, 47, 5, 6, 7, 47, 47, 47, 11, 47, 13, 14, 15, 47, 47, 47, 19, 47, 21, 22, 23, 47, 47, 26, 27, 47, 29, 30, 31, 47, 33, 47, 35, 47, 37, 38, 39, 47, 41, 47, 43, 47, 45, 46, 47, 47, 49, 47, 51, 47, 53, 54, 55, 47, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 49, 49, 49, 3, 49, 5, 6, 7, 49, 49, 49, 11, 49, 13, 14, 15, 49, 49, 49, 19, 49, 21, 22, 23, 49, 49, 26, 27, 49, 29, 30, 31, 49, 33, 49, 35, 49, 37, 38, 39, 49, 41, 49, 43, 49, 45, 46, 47, 49, 49, 49, 51, 49, 53, 54, 55, 49, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 51, 51, 51, 3, 51, 5, 6, 7, 51, 51, 51, 11, 51, 13, 14, 15, 51, 51, 51, 19, 51, 21, 22, 23, 51, 51, 26, 27, 51, 29, 30, 31, 51, 33, 51, 35, 51, 37, 38, 39, 51, 41, 51, 43, 51, 45, 46, 47, 51, 49, 51, 51, 51, 53, 54, 55, 51, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 53, 53, 53, 3, 53, 5, 6, 7, 53, 53, 53, 11, 53, 13, 14, 15, 53, 53, 53, 19, 53, 21, 22, 23, 53, 53, 26, 27, 53, 29, 30, 31, 53, 33, 53, 35, 53, 37, 38, 39, 53, 41, 53, 43, 53, 45, 46, 47, 53, 49, 53, 51, 53, 53, 54, 55, 53, 57, 58, 59, 60, 61, 62, 63, 54, 54, 54, 3, 54, 5, 6, 7, 54, 54, 54, 11, 54, 13, 14, 15, 54, 54, 54, 19, 54, 21, 22, 23, 54, 54, 26, 27, 54, 29, 30, 31, 54, 33, 54, 35, 54, 37, 38, 39, 54, 41, 54, 43, 54, 45, 46, 47, 54, 49, 54, 51, 54, 53, 54, 55, 54, 57, 58, 59, 60, 61, 62, 63, 55, 55, 55, 3, 55, 5, 6, 7, 55, 55, 55, 11, 55, 13, 14, 15, 55, 55, 55, 19, 55, 21, 22, 23, 55, 55, 26, 27, 55, 29, 30, 31, 55, 33, 55, 35, 55, 37, 38, 39, 55, 41, 55, 43, 55, 45, 46, 47, 55, 49, 55, 51, 55, 53, 54, 55, 55, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 57, 57, 57, 3, 57, 5, 6, 7, 57, 57, 57, 11, 57, 13, 14, 15, 57, 57, 57, 19, 57, 21, 22, 23, 57, 57, 26, 27, 57, 29, 30, 31, 57, 33, 57, 35, 57, 37, 38, 39, 57, 41, 57, 43, 57, 45, 46, 47, 57, 49, 57, 51, 57, 53, 54, 55, 57, 57, 58, 59, 60, 61, 62, 63, 58, 58, 58, 3, 58, 5, 6, 7, 58, 58, 58, 11, 58, 13, 14, 15, 58, 58, 58, 19, 58, 21, 22, 23, 58, 58, 26, 27, 58, 29, 30, 31, 58, 33, 58, 35, 58, 37, 38, 39, 58, 41, 58, 43, 58, 45, 46, 47, 58, 49, 58, 51, 58, 53, 54, 55, 58, 57, 58, 59, 60, 61, 62, 63, 59, 59, 59, 3, 59, 5, 6, 7, 59, 59, 59, 11, 59, 13, 14, 15, 59, 59, 59, 19, 59, 21, 22, 23, 59, 59, 26, 27, 59, 29, 30, 31, 59, 33, 59, 35, 59, 37, 38, 39, 59, 41, 59, 43, 59, 45, 46, 47, 59, 49, 59, 51, 59, 53, 54, 55, 59, 57, 58, 59, 60, 61, 62, 63, 60, 60, 60, 3, 60, 5, 6, 7, 60, 60, 60, 11, 60, 13, 14, 15, 60, 60, 60, 19, 60, 21, 22, 23, 60, 60, 26, 27, 60, 29, 30, 31, 60, 33, 60, 35, 60, 37, 38, 39, 60, 41, 60, 43, 60, 45, 46, 47, 60, 49, 60, 51, 60, 53, 54, 55, 60, 57, 58, 59, 60, 61, 62, 63, 61, 61, 61, 3, 61, 5, 6, 7, 61, 61, 61, 11, 61, 13, 14, 15, 61, 61, 61, 19, 61, 21, 22, 23, 61, 61, 26, 27, 61, 29, 30, 31, 61, 33, 61, 35, 61, 37, 38, 39, 61, 41, 61, 43, 61, 45, 46, 47, 61, 49, 61, 51, 61, 53, 54, 55, 61, 57, 58, 59, 60, 61, 62, 63, 62, 62, 62, 3, 62, 5, 6, 7, 62, 62, 62, 11, 62, 13, 14, 15, 62, 62, 62, 19, 62, 21, 22, 23, 62, 62, 26, 27, 62, 29, 30, 31, 62, 33, 62, 35, 62, 37, 38, 39, 62, 41, 62, 43, 62, 45, 46, 47, 62, 49, 62, 51, 62, 53, 54, 55, 62, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x115151513171717011515151317171701151515131717170115151513171717011515151317171701151515131717170115151513171717000000000000000001151515131717170115151513171717011515151317171700000000000000000115151513171717000000000000000001151515131717170000000000000000011515151317171701151515131717170115151513171717000000000000000001151515131717170000000000000000011515151317171700000000000000000115151513171717011515151317171701151515131717170000000000000000011515151317171700000000000000000115151513171717000000000000000001151515131717170115151513171717011515151317171700000000000000000115151513171717011515151317171700000000000000000000000000000000011515151317171701151515131717170115151513171717000000000000000001151515131717170000000000000000000000000000000000000000000000000115151513171717011515151317171701151515131717170000000000000000011515151317171700000000000000000000000000000000000000000000000001151515131717170115151513171717011515151317171700000000000000000115151513171717000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xfeeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e80000000000000000feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e80000000000000000feeaeaeaece8e8e80000000000000000feeaeaeaece8e8e80000000000000000feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e80000000000000000feeaeaeaece8e8e80000000000000000feeaeaeaece8e8e80000000000000000feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e80000000000000000feeaeaeaece8e8e80000000000000000feeaeaeaece8e8e80000000000000000feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e80000000000000000feeaeaeaece8e8e8feeaeaeaece8e8e800000000000000000000000000000000feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e80000000000000000feeaeaeaece8e8e8000000000000000000000000000000000000000000000000feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e80000000000000000feeaeaeaece8e8e8000000000000000000000000000000000000000000000000feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e80000000000000000feeaeaeaece8e8e8000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xfeeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8feeaeaeaece8e8e8

def cMZZ : Nat := 0x11515151317171700000000000000000000000000000000000000000000000001151515131717170000000000000000011515151317171700000000000000000115151513171717000000000000000000000000000000000000000000000000011515151317171700000000000000000115151513171717000000000000000001151515131717170000000000000000000000000000000000000000000000000115151513171717000000000000000001151515131717170000000000000000011515151317171700000000000000000000000000000000000000000000000001151515131717170000000000000000000000000000000001151515131717170115151513171717000000000000000000000000000000000000000000000000011515151317171700000000000000000115151513171717011515151317171701151515131717170000000000000000000000000000000000000000000000000115151513171717000000000000000001151515131717170115151513171717011515151317171700000000000000000000000000000000000000000000000001151515131717170000000000000000011515151317171701151515131717170115151513171717

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
  | 2 => 9
  | 3 => 54
  | 4 => 382
  | 5 => 887
  | 6 => 493
  | 7 => 37
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xea89e5b2d4a299cacfe5c94ea0cea3897c904f1a4ff9e43c4d81b1ca366ff7191d42d22d
  | 3, 0 => 0xf9dbbc7bf87004aaeeef656ce89cf3a4e7a74f38e4c56d03e3f47093cb668c78c8ca3a82c6a9bbfcbf8c3790b7ce3f6ab6724dacb4700902b111d5c2b1025519b097a2deaf821ebaae9cca6faaae665ba96e6c299c6e7e699927cd189440cc03913b290d8d241ff97a6ed492796bdf8f7545036b71454e066ebcf2cd6b2ff0af696ed6ae5d1e7ecc5cd388934d9fd6cb4d6b1d174b94bfbc4a7e9e5e49b132ce4944c3fc3fc424be315179723114859d2a3402d0293c164e238d1aa421a101a920844ea41e443aa01de833801d42d22d17b8f63b0de0fbff
  | 4, 0 => 0x1ef665d71e05aca11df9dec21d90af941d3ed8061c43fa451c35358b1c1e70091aa2356a1a634b8d1a035ed419dd46931965ad8c18f29d07188c38cd17cb2a99173beedc17195c2517078b4f16e9c22816ac0448162a47c614a25888146c3f0d1427c6db14116a5f13e2d21813866d38134af74412ebe0f812dc535512a9aa0f12a1c0b91279e5401272573711ac3f3710864ac91037fdd60fe7d01f0f69fd690eeae0220ec751210e9d50760de832990d41120f0c6febf20bead4990b49f3e00aaa9c6609f36bc609e5003a0908a0c608f0ce7308dc2cd308b054be0827a03d06edbe9505f0a8a00394b32b0313b1df0278fd4400d8a5cd00b4185b00570865
  | 4, 1 => 0x4151498f41199a7240ef98b1407ffb3d3f9648343f4360553ed1595d3e42aa153ddd8fc33d017dc63bed93893b9deef83b71a5c63acd65a83aa7fda43a94567b39d578cc39874ee139815e423946ff583923586838e5a045381d4e4d37883fca37854cfc37721d443766da5f369db57c3698472b365c2b6e351dbb243492f5e932a743543234a9b7315179723133514e2fc147262d63bd3c2d56f55e2c71a2062c19445d2bc79d802b6b5af92b00daa129e1da2b28004ef4262cc85c25ae45fa253d7f7c2490ba812454f57d23f1a775239006a621efa34421ca0e2b218ce4af215fb86e213a5b072109b4bb20635180205ef37a204b91521f57d94f1f3b325c
  | 4, 2 => 0x6a2f36a6693dd4fc690e2e0d68f38f5c681c06d267eb816e67161c5c66b43413663e9d8064152c7563fd453d63bde3ce621c14f561cae5bc6198563b6161980a606fef5d5f64338a5f06e2dc5dbfda135d617fd05c5aed295b1ca20958beb05e57a0311957638912572ee640572a6d4256b95f185698f294560afe1255cd349d551bac8a54c70439532a0f105316eb1f52a82d1651a9423b5146c03750dc1333507d6a804fa903a54fa79fb44f383d274de8960b4d9713854d5238454d48e0424b8dc25b4b2ba8214ae7ae984a96852c49eda99f486aeb7046dac23e45b7942445232ce244b75f1942cb465342be1c3b4224add441cf0369419ded8b417f3670
  | 4, 3 => 0x8f8372fd8e8756bb8e64552f8e032a5d8d7a86d48c4665138b807bbf8b4696c98a589db68a42f3e48953aab088d1109d88ab52d2883b99ac8827f283878e7ccc85efa2d885c267d98483ba66847f27b3838bcd8a81d07fc680568bf38012802c7f917db17f3e97f47ec6ed567eb902037eb062397e88d9997d6678a77d5d7c857d592d787d4f067c7d074c9b7c98e14d7a282d6379ace06579867ce078ee0d0b77b5f92276d1c2b975f7214474e26c4374d0fb6872b664a3720f1a54716a88b370b90043705cff41703f29086faffd286faec5a76d5aeda96cd6b5166ccece646c7f0ce96bd472076b76f4b76b14581d6ad2740e6ab205e06aae50216a548854
  | 4, 4 => 0xc5fb22a3c5c42475c510fc5ec390c5ffc2d1d8cac1468427c063ac8bbec10d47be925319bdfe523abd7d136ebb96cbdcbac61cc7b9da4020b8284e2fb74c9d90b6a1ca15b26187aab22090deb10518f7b1025519b0018800afac4004af24e3b4ae7ecbefae2bd925ae237434ac7ebb86ab0d5ceaaab9cfecaa7f2e37a9cfa9a7a8b5bb56a84f7348a832e7aaa6de2de6a37cec63a334c55fa305acf9a1a07eeba17706aea081235fa0325ed7a01ce9949f78fec29e98ed699df89eec9ce6fb789c6a66629c0b4ad99b6576fd9a2238c899c2ee0a9970afaa98a7cb5e98882e5c980ce2f69672655d963a84e195b75c1b947d820a946aed4d933e670f91596ca7
  | 4, 5 => 0xfdc3c94ffcab9772fad9a2bbf73ad1e3f71a4bccf650d3a2f509cad9f20a480af0f1a8e1f0de01b8f008a124edcce33ded58a925e8e76eebe8e1a243e5a7457ae57e059fe53f1e92e3e5a13ee3c270a6e3b0a046e35daad6e262ef9ae050f98be0503b6be0478bdedf985004df14e2aedc358a63dbd8f915db6ac411db4c2a55dae57f2adab86341d9b045a0d74138b0d73c5a40d6ae9d5fd63f0fffd5b116d2d5957033d4601c1ed3a5e964d3888343d3645f56d28b9086d217566ed17b3375d046526acfce62c3cf9d522fcda61c34ccc97b0ecc9b1300cc73f303cbdce6afcba00f20ca80f4f1c8ab77e7c67dd91dc67232efc61502d6
  | 5, 0 => 0xd81c8d80d62d3230d3dad640d08dc6f0d0619470ce224170c7115970c596e4f0b43ca450b28abfe0aa1242a0a939ffe0a8393c20a475cf50a355646099da090099137c2096e1b6a0965311a09008a0508b0ebe508b054be08a7c1e7088ffd53082b925b07fa9e750739a6af0732f5c0072c353706fda58606549118061fc9c905fc5d0a05fc123105b26902059fc55f0552f759050eced104e2ed3b04a494d30491b8980488c3070480fbea0452547c03e8415e0386528302e04eb602e033d002ba3b1e02ab9bee028d3693027c3eee02693359024c9555024448170225f07b022251e50220702b020fe4c3010c718900eb4b2c00d55fe6002a977600296b26
  | 5, 1 => 0x18938f45186497e9181e9c0e17f238bc17f1e5e917ec1f9a173a150317067021164c6fcc163311e115eefe1315e32669157d357215217455150c6824150c3d4014f31f4f142e307813fd0c1313f6d6d113e2d21813b73e6c13a7cf5d13800001133d33fc12f80f6e12af4e5612a1ac52126837fd1267918b124bf4b312081ac811ff0bb111f3031211e40c5a11b3983111785606114f743e114bd01e113f79c811395832110fce0310fdb30b10e4116d10d6a14d10a384ce1098b83e1079a77f10225bbd0fe6b0b30fdee9960fc260670f42ebb70f4105ee0f18843e0f17d8420ec751210ea65dff0ea3d6730e71ebe60e2580000df98eb40ddfda6e0dc785ea
  | 5, 2 => 0x259a3467257bb04924d86ee924bb9978246414aa2454f57d2446304e242c4e2823dadf49239006a623456d262335325122bb346822abf7bb22a469ef22a054e62267a8ab2241ee4021da35ce21ca0e2b21c01b6221b72b4821aa5d7821a932ec216fba042157451b213dafc1213d64e821299bc820e519d120be4bd1203940f11fdb52471fa7a1061f2b23021ee710431e9359f11e7bcb5b1e42906f1e39f44f1e1be22c1e141b0f1e05aca11e04161b1d79fa821d73239c1d5be9901d1111a11caacf811c88c66c1c6991db1c54ca981c43fa451c16b29d1b78aef71b733ffc1aae4e4b1a32bf3a19f0e3bd194897b21940947f1933c3d718bd9ce418ac8563
  | 5, 3 => 0x32265efb3201fbd231b7c44431364031313605113119121f30d839fb30cbcc9730bfa10d307c7c15304d8ff7303df6f930339f3e303341752ff71ab52ff216d82fd082d02fc7ec412fa25e632f9a830a2e8d76a42e8380b22dcdd2cb2dbf1a7d2d9fc3f02d9f41862d80a5c82d5998b32cc6d7452cc21fbd2caaa0eb2c80cc7f2c7f4a852c7cd70f2c61abd72b8894af2b5ffa412b28036a2b109d602ae608d72adf94742ad01d912ac436f12a9d0f862a83d8b62a592af929e29ee429847b2d2975287828e8e1c228e85e7928b0ffcd2872aae42866432e2863ad062805043127dd55452741838526d927be26ae67ef2698070125ae45fa25aa66e8259d4c3b
  | 5, 4 => 0x3f16cd343f04b2eb3ec91d233e7c41033e7a44fe3dfe48433dfb11223df9f70d3db122d63d5c46e33d45d1213d2219a53d15b1f03cfebc023cace1f73c4a3c903c4089fd3c266c883c20ef4f3c0ef6393bff9e883b9be4a53b85d86a3b468dc93b04ed423affbcdc3ab62dec39cf666239b62a74397c73913945c79f3934c6f339245aab38e6c5ca3857ad3b37d6c9043777cca83766da5f372e2a0d36dc88a636b492b33696b81b368556643668aa993627c16f35ea883c359f7aec359ab925356f986534f69f5f34f287e534e7ec8234cf8a2e34ca9a71345b367433feef9b3362f1dd3361ab09330fa95d3301273332a7435432837af532833155323ead69
  | 5, 5 => 0x4fb904954f6336194e9941f94e62857e4d6cc0a14d4c8a4f4cf916fb4ce280154cdedbf54cde954d4c7792e84c3c121d4c1c3f754b8af6e74b4ae3694b11d5874ae7ae984ab9097c4aa094704a867d1e4a7d6acf4a32a79d49d9ef0949c4d3694952768a49207bcc490f258248c1f87f48bf0d9a489aeb6a488429f4481d636d47ebf3a2476787094763e2e946c5bcc4469bd3444638421245b9d65c45b5a730450baa79449ca0f744808b13445b16e94429dc5f4423e48843e11d8843b84b2243582b3f42ffac1842dea5a242b85a8f42b731c742b1600b4248598841f4c41841b6b654411d3e9241199a724111079b40c047e4408160d73fbc76073f27e383
  | 5, 6 => 0x5f9c69a05f8cf8cd5f78fb645f55d82d5f0bf20e5f0a6c2a5eea7d355ec2bce25e7cb3425e0c4e065d6cf8365d6a67985d371ce55c6c06db5c5e91495c5b0b725c5aed295c00e45d5bb9d1675bb281ef5b971b905b76fe3f5b709de05b4c79f35acaf5e05a1bf7015a0ed6ab5a0b869f59ff351959d9ad1459bd93ba59bb97b559b56265592487d159060b94589d999a588efb7e585704a758324f1157c88ffe578b8f475705f44056d9ed9855b00c43555d7e14551bac8a5510b91954c4fad2548319ef5465ad62545c0da0545778e854188e655398fff25368ff255350c07f52b4ab18528335e2522554a0519315e7514793405020586c501734485016ee0a
  | 5, 7 => 0x6e3b14c06e13f0856e04a2796dfc850c6deb52826d66a7576d5741b06d4ecd7d6ccece646cb628716c7e506b6c7aac4b6c45ce716b7fb1546b2a125f6b17fc3d6b14581d6b06bfa46aef04a16ad2740e6ab3c5d96aae50216a7f27cb6a7c3df76a6843e36a4b0a376a0bd06569f4c2ee69df92b66999264a698b6f1b694ff08c693798c2692a74d968f6717468de7f3f68cae5e268202eac67f6224b668c3620662ce1c465ecdea665e73976652f03b5652df7e36527427a64ffaaed6482757d644ae30663d01e4663c187ee63bde3ce63860c8c63823aa16312f192630b2f6f6304492762a8d9c062a535a0629630d362070f7b60859e7f5fddf3ae5fb9fb4c
  | 5, 8 => 0x81f32e7e8173ac198144fa4181440e3280f5471180f0883a80ddbe738094c33b806f4a9a7fd2fcc17f15be2f7de226db7d6678a77d20650d7cab2c787c7c9d477bf98e087bea25d67bb1dab97ba593c07ba135ba7ac304d47a4d44c57a483e3f7a23bd467a01df5379e7315079ace065798475b9797731a07949402e78faef9b78f80d9e78d9c37e78c61c5578abba4f783fedce77cde77776e2032876646657762ec55175eb70a775a8f7e3755d49b87442d15e7429f75c740975e773d04e35738f0ae57330e843722c04687213b95a71fe541471a5d7f0716244b470c07a6f704651787043ddcd703805f76f2514586ec8af786ea98a966e59e10f6e55d494
  | 5, 9 => 0x92ca820a92a91c9f92a28d2c927e9bc99278b6c491f8c31c91bd78679148269490199cf18fc8f9788fc7cdda8fb972a58f37173b8ef941908e723afa8e5b7ae48e5958ba8dc6a4258d76ebf78cff06d28ca974ab8c800f778c396d678b8530848b7958ae8b3664888ae0fd158ae0cbee8a99b4ee89eebab5899b290689745b06893a3e188934ea69891af3fd890194ac88f63b4b88a5ff7c887df88e8849c9f48840ce60883b99ac8827f28387d639c287bbff02878721288767b5e18720ae1d87081fd486d0eca28651e71b8648125b85c54af7851fa110849f8ea284914343845fbe188437b12a84240a01838bcd8a834fa9cd82f4d569827b888a82385910
  | 5, 10 => 0xac065e5aaba2d351ab0a4c2faae9e1f4aa9a2849aa7869f2a9d34dc7a9cfa9a7a8c78a80a76c4c83a73ff3e7a6f92db3a5f04ec5a5d8c76ca4c01f4fa3e5c7e3a3ddf96da3ad2db0a38b1caba371ef4ba334c55fa2c5ac8aa273d6cfa249728ba1eb14f0a1868c72a155b845a0b94e1aa07bde3b9ff206b99fd115519fa110cf9f7583219ef7e4e89e98ed699dceabf79dc206aa9dbcdb419d8b4e349cd7ab5e9cc178b09c5bdcb29c31daf19c2cde019c2b0d469c0b4ad99bd615f29b29dca49b13529a9ae20f679a93b0169a6dd3799a2dd9749a2a249699ec4f6699237992990aaa7c9843c00697cc988196e0313895fec16594064e9193d2ef3193516b1e
  | 5, 11 => 0xc4e0d6d0c4a7dacdc4362439c435d19cc426ad15c41acee3c3fdd516c3c73ed1c3a959e0c2ceda1fc2b58040c23a806ac180dfc0c11127f7bf3f877dbf00260ebe87e140be444606be1b73e3bdc2c1f3bdb0a680bd68fc67bd2c67a7bd241678bcd84b7dbc9bcf29bc267686bc225fafbbd70918bb927832bb902114badb63d5bad63db0ba508d1fb9da4020b8fc6b37b868c0fdb8179448b79d2f69b76e30b8b6cf6782b6a1ca15b65ee449b5af2630b5082dd3b50606c6b441061cb39009a6b341c3d9b2c643ddb2c29fbdb2a5cb52b29de193b15679b1b10f76ddb085533bb01d963eaf7bcbf9ae592d5fadea6f56ad52b02cad11261eacfecb1eac5658ea
  | 5, 12 => 0xe03a9896df985004df3f27cddf089188de23b196ddbfab6ddcdb1951dc2c39cedbe6f778dbd8f915dba507afdad3bff1dabbdda4da80da34da289668da092f96d9fabe29d9cb1bd9d8ee152cd88f6af0d87c0e96d763b266d72c9c4cd6d96072d6d3cae9d6d173cbd68d79ecd5f58501d56a6fa3d530bb80d4ef22a5d49421b1d428cd2ad3d134dcd3bcced9d3888343d358e6ffd217566ed2079519d0de0e8ed0481452d03679d6cfb8328ece03f274cda61c34cd515c94cc7722e7cbfb4283cbf82ccfcb60334cca50be5ac9c9a55ec9c7b24dc85cda08c7c20143c7b6c275c797aba1c77e4728c614b64ec5fb5111c5f09261c5e52154c596ca94c510fc5e
  | 5, 13 => 0xff25ec59fee62e6efebf2ea3fe77079ffccc086efbf4994cfbe8ab9ffb589c61fa73879cf9e02199f977850af8f12854f8c092bbf87f08adf8171feaf6e65a66f652e99bf650d3a2f5e1db77f569e91ff5647b08f40f438ef34f2536f2b1ad77f17f4b82f16552baf0ffd929f0f99e5bf0aada3bf0183a6cf008a124efbfc44aefa719c7eed64226ee9a39b6ee4fe506ee23de5eeb5ffe20eb3197bfeaf98545eac5b53de9ab5646e94ad270e8f311d3e8a3371fe76a4932e6eefd74e41352dde37ddbece36a34c3e2ab6d28e1d06de4e13acbd2e104aa19e0a6caf6
  | 6, 0 => 0x1d27eab31ce1314f1cba634f1caacf811c371f661ac5ffec1a62837d18bd9ce4186ea9ec1813364017de116e17a298e21768b8cb1764a1f416d2635916ba2faa16187ff514b9b462146b1ccb14475df21359d68d13460d7512b072fd11e40c5a11e00942119a4ad2118343a3115c75a3114bd01e112f1e111048490b0fe6b0b30f7c5bec0f17d8420ef7b18e0ed24beb0e4dd99e0e0886220e04e2020d47e79c0c8101420b2be2ba09c9c0aa09b848b7095bc6b6089437b008410d6307989b2f06e0c0de0604e59605fc5d0a057dedf104f3c49604b6d23d0488c307030c36a902ae8ec8023b6ff801f8748801e9f9f0016c280700d55fe60084da8500026194
  | 6, 1 => 0x35fe1fe9356ad8ad353d006e353acac934f940bb349ea395345b3674343bd5c1340f9e0d33b30662329c040a32564bbe321ba2b73213b61031bb686431b7c444313fef593137c74631364031312891093029d76d2fd663f62efe8c2f2ee8a0e92e9b29442e8380b22dfa70b52d5998b32cae9a3a2c61abd72c2050d32b8a56972afa74d32a6d90342a1ad88e29bd290729b2b7bf29b16418294634b927f362a126149f8125d358952593009f249c45b222f904ba22d9ede622c0896d22944eb32255ee162206ab7221da553121d46a0320e519d120be4bd12035174d1f5d11281f40175b1f21aa841f17bf341eeb9c251e111c641defe17f1d7cc2af1d64c903
  | 6, 2 => 0x51952be0519315e74fc34ff04fbd413c4faa1be04f5185d34ef85ad44e216c1e4e08916a4ddb80954cf916fb4cdedbf54cc18dc74c4d35524bed1c804b5a7cb14b4ae3694aba20d34a976e604a93ca4049dc7bfb4992274b496620a34767870946ec31ce46c5bcc4463bc78a45aee2eb4509a063449ca0f7449ac42c445b16e94435541843639e8742c37e7242c1d44242ac8b77424537a042430b674240a0cd4213fc50411d3e9241199a723f8bad9b3f0f0a7f3f072f833dfb43cb3d8732eb3d7d05c73d5c46e33d1956103d15b1f03c7d0e173b7cdadb3b70d7a43a816a1239e7766039cf66623965f3db3857ad3b3805b0db37e78b0d3763e69636e749f4
  | 6, 3 => 0x6c91b67e6c8e125e6c7b9a726c7aac4b6c45ce716c341d756bf75c316bbbe9bf6b14581d6b06bfa46b04a2a76a852df76a5ac67e6a5a1a826a155b726967c240694ff08c693bd0f469182e45687fefa46876c3c96702d72265d51cf764a7735a6442cc4563cf1215633ce0b561620c0960e2079f60d62fc960996e85609539995f0bf20e5dbe812e5dab75995d8cbf995d868a575d6a67985d18d61d5c5aed295c2d8d6c5c17a2265bb281ef5ba4e9765b08098c5a682e9e5a2870b35a1bf701588efb7e585704a7580e4ab35754da505736db9155c44f5e552263de5510b9195505da58546b769154336a99533caf7b524ab3bc52289cab522554a05204cfe1
  | 6, 4 => 0x8b8fd2378b8039398b0a2e8189015cbd88e2063088e183c68849c9f4880919858652dfa08606793185c61af68524e1248445e17283f00d578283c5c5827b888a825ba239821b69fe81909e8880f0883a80bdf2898094c33b8067234a803895a37ea6b7507e77a0087dfd76a87dee39fb7de297267d8430807cf15e8f7c90dab97c6118d87c275c117c008e117a6d654279d59c317984d2af797c368f797731a078e7f3c6773b552c75f0908b753325fd748ad9f273ffdf2473d5d18573a6da297330e8437319b25c717554217132ed0d712568a970bf77b27063b695704e7f807043ddcd703805f76f2cffc16f2514586eea119d6ec242416e7f763c6d354552
  | 6, 5 => 0xacc08981ac9bd233ac89d580ac5658eaac2e4ae6a9cfa9a7a8527068a78a72a3a76c4c83a75e81b5a71a9aa0a57e2414a51c3149a494b8caa462be0ca360c98fa2a9c949a2a62529a207ff04a1eb14f0a05726f09fdee3379fc2cd539f9d59299e41ee589df974079de72c6e9db3c1cb9cf8f8949cf482bc9c5f80d29c5bdcb29c2cde019ae20f679a6dd37999be8343993c394d98f365169875b15e98645be59828f57f980a765597ef24379782cc3d9768aec89741e0c892a91c9f92893ec29253379c91bd7867912cca7c91178a2a90e1bd2c90dcfb6590b1daa59011cc6e900cdcb18fc8f9788f4131db8e51eb9d8db98fe58cfa06848ccb07d38c788271
  | 6, 6 => 0xd88f6af0d8087304d7ed6eb8d6f41cf9d58f8705d57f8d86d4ef22a5d358e6ffd2244568d12db2e7cf4bb827ce732a83ccfe26dfcce81a30cc433181cb7a4837cad4adc7cac6c03ac92d94c2c8a8e997c89983f0c8910fbdc7c092abc7bcee8bc64901e4c63146e1c5c16a0bc5aa8623c54e12a5c3f710d1c3cbb9f6c3c73ed1c338648bc1596cb1bf03ca2ebf00260ebec47ce1be5533d2bdeb1c00bde777e0bd4951bbbc225fafbb927832bb902114ba981a6dba4e344eba2cbf75b94e9046b8341c4fb7a0d389b79d2f69b78c3892b743269db6d95dd0b54dc8dfb4ffd5fab466ca11b2c29fbdb0f24e83b09fc054aee10801aebeb73badf6ed58ad6796e0
  | 6, 7 => 0xff203badfecd5eebfe07eecafbfb905afb135791f9e02199f8ff1d81f819ed9ef76f2041f7185832f465bbd2f44cecbcef4890d1ee4fe506ee23de5eecffbaa7ec327b0beb0b3bb8ea7e4b6be9b47d3ae99dbd24e99b9afae76a4932e6bb9aeee678a6c8e6230e2ee530fcf5e47c8058e38c0c34e37ddbece36a34c3e2fe4142e18a549bdeee0ed8dec20830de91ec0dde3717a9ddbdcacadd3570bedc865072dc378951dbd7057bdba507afda289668d924691b
  | 7, 0 => 0xf76f2041ecffbaa7e38c0c34ddbdcacadbd7057bce732a83cb7a4837c7bcee8bc64901e4ba4e344eb79d2f69ad6796e0a2a9c949a207ff049c5f80d29c5bdcb27c275c117c008e1173ffdf246c8e125e5c17a226552263de4fc34ff04a93ca40496620a3424537a041199a723d15b1f036e749f431b7c4442e9b29442a1ad88e16d263590e04e20207989b2f04f3c49602ae8ec8
  | 8, 0 => 0x9c5bdcb2
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55550000555500000f0f00000f0f000000ff000000ff00000000ffffffff00000000ffff000000000000ff00ff0000000000ff00000000000000f0f0f0f000000000cccccccc00000000aaaaaaaa00000000555555550000000033333333000000000f0f0f0f0000000000ffffff0000000000ff00ff0000000000000000
  | 0, 1 => 0xcccccc00cccccc00aaaaaa00aaaaaa00aa00aa00aa00aa0055ffff0055ffff0055555500555555005500550055005500333333003333330033003300330033000f0f0f000f0f0f0000ffffffffffff0000ffff0000ffff0000ffff000000000000ff000000ff000000f0f00000f0f00000cccc0000cccc0000aaaa0000aaaa
  | 0, 2 => 0xf0f0f0f000000000f000f000f000f000f0000000f0000000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0505050505050505030303030303030300ffffffffffffff00ffffff00ffffff00ffffff0000000000ff55ff00ff55ff00ff00ffffffffff00ff00ff00ff00ff00ff00ff0000000000ff000000ff000000f0f0f000f0f0f0
  | 0, 3 => 0x33333333ffffffff333333333333333333333333000000003300330033003300330000003300000030f0f0f030f0f0f030303030303030302a2a2a2a2a2a2a2a22aaaaaa22aaaaaa222222222222222211111111111111110fffffff0fffffff0fff0fff0fff0fff0f0fffff0f0fffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f
  | 0, 4 => 0x550000005500000050505050f0f0f0f050505050505050504c4c4c4c4c4c4c4c44444444cccccccc44444444444444443f3f3f3f3f3f3f3f3f3f3f3f000000003f3f00003f3f00003f0000003f00000033ffffff33ffffff33ffffff0000000033ff33ff33ff33ff33ff33ff000000003333ffff3333ffff3333ffff00000000
  | 0, 5 => 0x770000007700000070707070707070705f5f5f5f5f5f5f5f5f5f5f5f000000005f005f005f005f005f0000005f00000055ffffff55ffffff55ff000055ff00005555ffff5555ffff55555555ffffffff5555555555555555555555550000000055550000ffff00005555000055550000550055005500550055000000ff000000
  | 0, 6 => 0xaa00aa00aa00aa00aa000000aa000000aa00000000000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a0a0a000000000a000a000a000a000a0000000a000000088888888888888888888888800000000888800008888000088000000880000008080808080808080777777777777777777777777000000007700770077007700
  | 0, 7 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaa00aa00aaaaaaaaaa000000aaaaaaaaa8a8a8a8aaaaaaaaa0a0a0a0aaaaaaaa88888888aaaaaaaa00000000aaaaaa00aaaaaa00aaaaa0a0aaaaa0a0aaaa8888aaaa8888aaaa0000aaaa0000aaaa000000000000aaa0aaa0aaa0aaa0aaa0a0a0aaa0a0a0aa88aa88aa88aa88aa888888aa888888
  | 0, 8 => 0xcc00cc00cc00cc00cc000000cc000000cc00000000000000c8c8c8c8c8c8c8c8c0c0c0c0c0c0c0c0c0c0c0c000000000c0c00000c0c00000c000c000c000c000c0000000c0000000bbbbbbbbbbbbbbbbbbbbbbbb00000000afafafafafafafafaaffffffaaffffffaaffaaffaaffaaffaaaaffffaaaaffffaaaaaaaaffffffff
  | 0, 9 => 0xcccccccccc000000ccccccccc0c0c0c0cccccccc88888888cccccccc00000000cccccc00cccccc00ccccc8c8ccccc8c8cccc8888cccc8888cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc8c8c8ccc8c8c8ccc0ccc0ccc0ccc0ccc0c0c0ccc0c0c0cc88cc88cc88cc88cc888888cc888888cc880000cc880000
  | 0, 10 => 0xeccccccceccccccceaeaeaeaeaeaeaeaeaeaeaeaaaaaaaaaeaaaeaaaeaaaeaaaeaaaaaaaeaaaaaaae0e0e0e0e0e0e0e0dddddddddddddddddddd0000dddd0000dd000000dd000000cfcfcfcfcfcfcfcfccffffffccffffffccffccffccffccffccccffffccccffffccccccccffffffffcccccccccccccccccccccccccc00cc00
  | 0, 11 => 0xeeeecccceeeecccceeeeaaaaeeeeaaaaeeeaeaeaeeeaeaeaeecceecceecceecceecceecccccccccceecccccceecccccceecccccccccccccceeaaeeaaeeaaeeaaeeaaaaaaeeaaaaaaeeaaaaaaaaaaaaaaee00ee00ee00ee00ee000000ee000000ececececececececececececccccccccececccccececcccceccceccceccceccc
  | 0, 12 => 0xf0f0000000000000f0e0f0e0f0e0f0e0f0e0e0e0f0e0e0e0f0c0f0c0f0c0f0c0f0c0c0c0f0c0c0c0f0a0a0a0f0a0a0a0f0a00000f0a00000f000f000f000f000f000f00000000000f0000000f0000000f000000000000000eeeeeeeeeeeeeeeeeeeeeeeeececececeeeeeeeecccccccceeeeeeeeaaaaaaaaeeeeeeee00000000
  | 0, 13 => 0xf0fffffff0fffffff0fff0fff0fff0fff0f0fffff0f0fffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0000000f0f0f0f0e0e0e0e0f0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f000f0f0f000f0f0e0e0f0f0e0e0f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0f00000f0f00000
  | 0, 14 => 0xfaf0f0f0f0f0f0f0faaafaaafaaafaaafaaafaaa00000000faaaaaaafaaaaaaafaaaaaaaaaaaaaaafaaaaaaa00000000fa000000fa000000f8f8f8f8f8f8f8f8f8f8f8f8f0f0f0f0f8f8f0f0f8f8f0f0f8f0f0f0f8f0f0f0f5f5f5f5f5f5f5f5f500f500f500f500f5000000f5000000f3f3f3f3f3f3f3f3f3f3f3f300000000
  | 0, 15 => 0xfc00a800fc00a800fc000000fc000000fc000000cc000000fafafafafafafafafafafafaf8f8f8f8fafafafaf0f0f0f0fafafafac8c8c8c8fafafafaaaaaaaaafafafafa00000000fafaf0f0fafaf0f0fafaf0f0f0f0f0f0fafaaaaafafaaaaafafa0000fafa0000faf0faf0faf0faf0faf0faf0f0f0f0f0faf0f0f0faf0f0f0
  | 1, 0 => 0xfcfcccccfcfcccccfcfca8a8fcfca8a8fcfc0000fcfc0000fcf8f8f8fcf8f8f8fcf8f0f0fcf8f0f0fcf0fcf0fcf0fcf0fcf0f0f0fcf0f0f0fcf0f0f0f0f0f0f0fcf00000fcf00000fcccfcccfcccfcccfcccccccfcccccccfcccccccccccccccfca8a8a8fca8a8a8fc00fc00fc00fc00fc00fc00cc00cc00fc00cc00fc00cc00
  | 1, 1 => 0xff00000000000000fefefefefefefefefefefefeccccccccfefefefe00000000fefeaaaafefeaaaafeeeeeeeccccccccfeaaaaaafeaaaaaafeaaaaaaeeaaaaaafe00fe00fe00fe00fe00aa00fe00aa00fe000000fe000000fcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0fcfcfcfcccccccccfcfcfcfc00000000fcfcf0f0fcfcf0f0
  | 1, 2 => 0xff000000ffff0000ff000000fff0f0f0ff000000fff00000ff000000ffaaaaaaff000000ff333333ff000000ff330000ff000000ff00aa00ff000000ff003300ff000000ff000000ff000000fc000000ff000000f0000000ff000000ee000000ff000000cc000000ff000000aa000000ff00000055000000ff0000000f000000
  | 1, 3 => 0xff00c000ff000000ff00aaaaff00aaaaff00aa00ff00aa00ff00aa00ff00a000ff00aa00ff008800ff00aa00ff000000ff00aa00cc008800ff00aa0000000000ff00a000ff00a000ff00a000ff000000ff008800ff008800ff008800ff000000ff008000ff008000ff002200ff002200ff000f00ff000f00ff000000ffffffff
  | 1, 4 => 0xff00ff00ff000000ff00ff00f000f000ff00ff00ee00ee00ff00ff00cc00cc00ff00ff00aa00aa00ff00ff0055005500ff00ff0000000000ff00f000ff00f000ff00f000ff000000ff00ee00ff00ee00ff00ea00ff00ea00ff00e000ff00e000ff00cc00ff00cc00ff00cc00ff000000ff00c800ff00c800ff00c000ff00c000
  | 1, 5 => 0xff03ff03ff03ff03ff030303ff030303ff030000ff030000ff00ffffff00ffffff00ffffff00ff00ff00fff0ff00fff0ff00ffccff00ffccff00ff55ff00ff55ff00ff0fff00ff0fff00ff00ffffffffff00ff00fff0fff0ff00ff00ff33ff33ff00ff00ff00ffffff00ff00ff00ff00ff00ff00ff00cc00ff00ff00ff00aa00
  | 1, 6 => 0xff80ff80ff80ff80ff808080ff808080ff55ff55ff55ff55ff555555ff555555ff550000ff550000ff33ff33ff33ff33ff33ff3300000000ff333333ff333333ff33333300000000ff330000ff330000ff22ff22ff22ff22ff222222ff222222ff0f0f0fff0f0f0fff0f0f0f00000000ff0a0a0aff0a0a0aff0a0000ff0a0000
  | 1, 7 => 0xffaa0000ffaa0000ffaa0000ff000000ffaa0000eeaa0000ffaa0000cc880000ffa8a8a8ffa8a8a8ffa80000ffa80000ffa0ffa0ffa0ffa0ffa0ffa0ff00ff00ffa0a0a0ffa0a0a0ffa0a0a0ff000000ffa00000ffa00000ff88ff88ff88ff88ff88ff88ff00ff00ff888888ff888888ff888888ff000000ff880000ff880000
  | 1, 8 => 0xffaaeeaaffaaeeaaffaaeaaaffaaeaaaffaaaaaaffaaaaaaffaaaaaaffa0a0a0ffaaaaaaff888888ffaaaaaaff00aa00ffaaaaaaff000000ffaaaaaaeeaaaaaaffaaaaaacc888888ffaaaaaacc880000ffaaaaaacc000000ffaaaaaaaaaaaaaaffaaaaaa00000000ffaaaa00ffaaaa00ffaaa0a0ffaaa0a0ffaa8888ffaa8888
  | 1, 9 => 0xffc0c0c0ff000000ffc0aa80ffc0aa80ffc00000ffc00000ffaaffffffaaffffffaaffaaffaaffaaffaaffaaffaaaaaaffaaffaaffaa0000ffaaffaaff88ff88ffaaffaaff00ff00ffaaffaaeeaaeeaaffaaffaacc88cc88ffaaffaacc880000ffaaffaa00000000ffaaff88ffaaff88ffaaff00ffaaff00ffaafaaaffaafaaa
  | 1, 10 => 0xffccffccff00ff00ffccffccccccccccffccffcc00000000ffccff00ffccff00ffccccccffccccccffccccccff000000ffccccccccccccccffcccccc00000000ffccaa88ffccaa88ffcc0000ffcc0000ffcc0000cccc0000ffc8c8c8ffc8c8c8ffc0ffc0ffc0ffc0ffc0ffc0ff00ff00ffc0ff00ffc0ff00ffc0c0c0ffc0c0c0
  | 1, 11 => 0xfff0f0f000000000fff0aaa0fff0aaa0fff00000fff00000ffeeffeeffeeffeeffeeffeeccccccccffeeffee00000000ffeeeeeeffeeeeeeffeeeeeeccccccccffeeeeee00000000ffeeccccffeeccccffeaffeaffeaffeaffeaeaeaffeaeaeaffeac0c0ffeac0c0ffea0000ffea0000ffe0e0e0ffe0e0e0ffccffccffccffcc
  | 1, 12 => 0xfffcfcfcfffcfcfcfffc0000fffc0000fffafffafffafffafffafffa00000000fffafafafffafafafffafafa00000000fffaf0f0fffaf0f0fffa0000fffa0000fff0fff0fff0fff0fff0fff0ff00ff00fff0fff0f0f0f0f0fff0fff000000000fff0ff00fff0ff00fff0f0f0fff0f0f0fff0f0f0ff000000fff0f0f0f0f0f0f0
  | 1, 13 => 0xffff00aaffff00aaffff0055ffff0055ffff0033ffff0033ffff0000ffffffffffff0000ffffaaaaffff0000ffff0000ffff0000fff00000ffff0000ffaa0000ffff0000ff000000ffff0000fcfc0000ffff0000eeee0000ffff0000cccc0000ffff0000cc000000ffff00000f0f0000ffff000000000000fffcfffcfffcfffc
  | 1, 14 => 0xffffaaaaaaaaaaaaffffaaaa00000000ffffaaa0ffffaaa0ffffaa00ffffaa00ffffaa00ffff0000ffffa8a8ffffa8a8ffffa0a0ffffa0a0ffffa000ffffa000ffff8888ffff8888ffff8800ffff8800ffff5555ffff5555ffff3333ffff3333ffff0f0fffff0f0fffff0f0f00000000ffff0a0affff0a0affff00ffffff00ff
  | 1, 15 => 0xffffeeeeccccccccffffeeee00000000ffffeaeaffffeaeaffffe0e0ffffe0e0ffffccccffffccccffffccccffff0000ffffccccccccccccffffc8c8ffffc8c8ffffc0c0ffffc0c0ffffaaaaffffaaaaffffaaaaffffaa00ffffaaaaffffa0a0ffffaaaaffff0000ffffaaaaeeeeaaaaffffaaaacccc8888ffffaaaacccc0000
  | 2, 0 => 0xffffffff00005555ffffffff00000000fffffff0fffffff0ffffffccffffffccffffffaaffffffaaffffffaa00000000ffffff00ffffff00ffffff00ffff0000ffffff00ff00ff00ffffff0000000000fffffafafffffafafffffafa00000000fffff0f0fffff0f0fffff0f0f0f0f0f0fffff0f000000000ffffeeeeffffeeee
  | 2, 1 => 0xffffffff55555555ffffffff44444444ffffffff33333333ffffffff0f0f0f0fffffffff0c0c0c0cffffffff05050505ffffffff00ffffffffffffff00ff00ffffffffff00f0f0f0ffffffff00f000f0ffffffff00ccccccffffffff00cc00ccffffffff00555555ffffffff00550055ffffffff0000f0f0ffffffff0000cccc
  | 2, 2 => 0xffffffffc0c00000ffffffffc000c000ffffffffc0000000ffffffffaaaaaaaaffffffffaaaa0000ffffffffaa00aa00ffffffffaa000000ffffffffa8a8a8a8ffffffffa0a0a0a0ffffffffa000a000ffffffffa0000000ffffffff88888888ffffffff88880000ffffffff88008800ffffffff88000000ffffffff80808080
  | 2, 3 => 0xffffffffeeeeeeeeffffffffececececffffffffe0e0e0e0ffffffffccccccccffffffffcccccc00ffffffffccccc0c0ffffffffcccc8888ffffffffcccc0000ffffffffccc0c0c0ffffffffcc88cc88ffffffffcc888888ffffffffcc00cc00ffffffffcc008800ffffffffcc000000ffffffffc8c8c8c8ffffffffc0c0c0c0
  | 2, 4 => 0xffffffffffffccccffffffffffffaaaaffffffffffff0000fffffffffff0fff0fffffffffff0f0f0ffffffffffccccccffffffffffaaffaaffffffffffaaaaaaffffffffffaa0000ffffffffff00ff00ffffffffff000000fffffffffcfcfcfcfffffffffafafafafffffffff0f0f0f0fffffffff000f000fffffffff0000000
  | 2, 5 => 0xffffffffffffffffffffffffffffff00fffffffffffff0f0
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x1b84247f36e10c1fcd83430c43620fa284d883eca13620db308db836cb7348cfb310d8736cc43
  | 3, 0, 0 => 0x48cfb2847f48d58d36cc44611273e8a148b18d3e8a1461cdb2847f48f18b36cc447694c3ecc44614db2847f461cdb310a14618db2847f46358736cc4449cd72847c448cdb3087f40018736cc438f18836cc447698736cc44
  | 3, 0, 1 => 0x620db2847948398736cc4448cdb2847c483927450bd4839273f0c3448cdb3107a47d99536cc4489d8d3f0a1448cfa2847f48f1273ecc448391836ca1461cdb3107f460cdb2dca14839a94247f48398d3f0b348f1ab36cb74
  | 3, 0, 2 => 0x60d0c2847f46e0db2447f449d1a36c7f460cdb310914620db2847a461d2736cc446e18d36cc448f1a04507f46e0db2387f48f18d36cc44839a936cb748f18736cc448398d36cc348f127450ae48398d430c4460cdb2547f4
  | 3, 0, 3 => 0x60d092847f46112736cc248b18d36cc248f1ab4247f4838ca2547f48f12736cbd4
  | 4, 0, 0 => 0x8c12736cae2855d4548fa2847f58392736cad28556949cdb2847f58393336ca11fd60e49cdb2843758397536ca11fd60e36ca72847f57699436ca11fd63c76952450ae58391636ca11fd6384f4db2847f584d8d36ca11fd60e5c8e82847f58c92336ca11fd63c49cdb24c7f5
  | 4, 0, 1 => 0x8398d36ca120560e480db2847f58892736ca11fd5da530db3087f58398836ca11fd5ca49cdb2847f58392734ca11fd60e464db2847f58392736cb91fd63c5fcdb2847f583927450fc31163c49cdb2887f58392736c951fd63749cdb2847f58c98d36ca11fd63c49cdb2cc7f5
  | 4, 0, 2 => 0x839353a0a11fd63c7d99b36cc458bd2736ca11fd62c49cfa2847f58f12a36ca11fd57f36ca11fc3d57515236cc41e9630680db2847f5839a936c8e1fd60e574db2847f589d2736ca11fd63a49cdb2847f58394536ca11fd60e49cdb2aca156557f36ca11fd60e608db2847f5
  | 4, 0, 3 => 0x7098336ca11fd60e674db2847f58394036cae2855fe4f4db2847f560d7f36ca11fd60e5c8db2847f58392936ca11fd5c864cdb2847f58397e36cc21fd60e388db2847f58393d36cb31fd60e624db3087f58396136ca11fd60e634fc2846b5839b436cae2855f1530db2847f5
  | 4, 0, 4 => 0x8392736c9a1fd60e49cfc2cc7f58397e36ca11fd63c5d4db2847f58398936ca11fd5da61cdb2847f57c55236ca11fd5b749cdb2847f58397f338a11fd5d149cdb3087f5838fd36ca11fd5273b4db2847f57892736ca11fd6244f4db2847f5634f736ca11fd5ee5fcdb2847f5
  | 4, 0, 5 => 0x8393536ca11fd62649cdb2847f50018736ca11fd20a5fcdb2847f58c92736cb72855ff49cdb2847f5839a436ca11fd5d4548db2847c58c17f36ca11fd63c620db2847f58399f36ca11fd60e5fd0b2847f58398b36ca11fd63c8398d36cc455892736ca11fd60e49ce82847f5
  | 4, 0, 6 => 0x64d8d36ca11fd60e4dcdb2cc7f58398e36ca11fd63c674db2847f58f127414db1fd60e504db2847f58b18d36ca11e564449cd72847f58f17236ca11fd60e49cef2847f58392736cc21fd60e6acdb2dca158e12336ca11fd60e634db2dca1572d8336ca11fd58d61cdb2847f5
  | 4, 0, 7 => 0x8d97f36ca11fd60e49cdb2847f58f1273a0a11fd60e510db2847f58f17e36ca11fd60e49cdb2c07f58f18936ca11fd5da530fb2847f589d3d36ca11fd52736ca11fc5c58392b36ca11fd60e49cdb2ec7f549d1f36cc21fd60e634db2b8a158397f3e8a11fd63c5fcdb3107f5
  | 4, 0, 8 => 0x8f18d49cdb31160e47d092847f58d12736ca11fd63c49cdb1fc4a58f12736cbc1fd62749cfc2847f58393936ca11fd60e36ca11fc5a58f18b36ca11fd60e454db2847f58398d450db31160e6ccdb2847f58917036ca11fd638634db2847f56112736ca11e560e49ce72847f5
  | 4, 0, 9 => 0x838fe36ca11fd60e49d0c2847f58393236ca11fd63149cdb2847f58f12736cc21fd60e5e8db2847f56ed7f36ca11fd60e5c4db2847f5839b236cae28560e4f4e82847f549cdb2847f18560e4f4db2687f58f13536ca11fd5f1548db3107f5839272847f0e958960cdb2847f5
  | 4, 0, 10 => 0x6552736ca11fd60e49ce52847f58918d36ca11fd635634db2847f589d3736ca11fd63c49cdb2847f549cf936ca11fd60e634db2cc7f58393636ca11fd60e49cdb2b0a158f12b36ca11fd60e3fcdb2847f59092336ca11fd630674db2847f583927334a11fd63e49cdb2cc7f5
  | 4, 0, 11 => 0x839c2328a11fd60e5f4db2847f55fcf736ca11fd61a49cdb2847f58395e36ca11fd60e5ecdb2847f548cdb2847f1e560e4fcdb2847f58f1273f0db31160e580db2847f5839273eca11fd52736ca11fc3d58f13936ca11fd5b849cdb2847f58412736ca11fd60e4f4db3087f5
  | 4, 0, 12 => 0x8792736ca11fd63c3f8db2847f58393b36ca11fd52736ca11fc4258112736ca11fd60e634f836ca15839a036cae2855ee49cdb2847f57b93a36ca11fd60e6c4db2847f58397e3e8a11fd60e4f4db2847f560d2736ca11fd60e624fa2847f583927424a11fd63c49d1422c7f5
  | 4, 0, 13 => 0x83909318a11fd60e4f8db2847f559d2736ca11fd627634db2847f549d1d36ca11fd63049cdb2847f57695235ca11f15ca634db2847f58393436ca11fd5cc5fcdb2847f58398d36c951fd6344f4db2847f58390336ca11fd62149cdb2847f5745273e8a11fd61649cdb2847f5
  | 4, 0, 14 => 0x8f127424a11fd60e49cdb30c7f58397f36cae28563c5f4db2847f564d7f36ca11fd6125fcdb2847f5839cb328a11fd60e5fcdb2dca158e52736ca11fd63c49cfb2847f58292736ca11fd62d49cdb2847f5839093f8a11fd60e49cfa3087f5838db2847f13d60e634db2f8a15
  | 4, 0, 15 => 0x49cdb2847f12160e5dcdb2cc7f58398d3a0a11fd60e36ca11fc5f548cdb2847f1e952747cfa2847f58f13b36ca11fd60e36ca11fc465839273acdb2855b7634db2847f57d99536ca11fd62049cdb2847f57c15236ca11fd60e49cfa2847f58f12736cc41fd60e6d0db2847f5
  | 4, 1, 0 => 0x8399e36ca11fd60e634db310a158392736cb628561b49cdb2847f584d2736ca11fd60e4b8db2847f58f0db2847f13d60e484db2847f549cdb354c21fd60e5b8db2847f58397636ca11fd60e49d142b8a15839273f0a11ed60e490db2847f5838db2847f14162549cdb2847f5
  | 4, 1, 1 => 0x83927450931fd60e61cdb2847f549cea36ca11fd63e49cdb2847f58f1273e8a11fd63249cdb2847f5839273d4a11fd63c7698d36cc458393c36ca11fd60e600db2847f58398d36cc424560e634db3087f5839a0450a11fd60e48cdb2847f58f12736cba1fd60e498db2847f5
  | 4, 1, 2 => 0x49cf736ca11fd6275dcdb2847f58392736c7f1315ee520db2847f50023c634db31120e49ca11fc4e58f12436ca11fd63c6acdb2387f58392c36ca11fd63c49cdb3107a58391f36cb72855955f0db2847f58398136ca11fd60e49cdb2847c59112336ca11fd60e634db2847f5
  | 4, 1, 3 => 0x8f12736ca11f158d60cdb310a158f18d36ca11fd63c61cdb2847f589d2736cb31fd60e49cdb1fc4b560cdb2848e1fd60e634cd2847f58cd3d36ca11fd5ba49cdb2847f58398d430a11fd5ee548db2687f585d2736ca11fd63c48cdb2847f58f12636ca11fd63c634db310a15
  | 4, 1, 4 => 0x8392736cae2856245c8db2847f58392736ca10e160e49cdb2f4a158f52736ca11fd60e49cdb2dca158c927424a11fd62849cdb2847f5634db2847f0f558749cdb2847f58398d36ca10d95b8634db2847f58398d36ca11ed60f49cdb2847f58f1da548fb31162c49cdb3087f5
  | 4, 1, 5 => 0x8552736ca11fd60e590db2847f5891273a0a11fd58336ca12447f583927398a11fd52736ca12147f583927420a11fd60e49cdb2bc7f58398a36ca11fd60e769523f0c3583927410db1fd60e49ca11fc5e5839ab424a11fd58d60cdb2847f58398d424a11fd60e49cd82847f5
  | 4, 1, 6 => 0x49cfa354a11fd63c48cdb3107f58392736cb21fd63c49cdb2507f549d1c36ca11fd64249cd72847f58398d36cc128560e4b4db2847f58c18d36ca11fd60e36cc62dca158398c36ca11fd52736ca11fc4458397736ca11fd60e4a0db2847f549ce036ca11fd60e680db2847f5
  | 4, 1, 7 => 0x49cfa3dca11fd60e634db2848358f17736ca11fd60e49d092dca158f1a036ca11fd62449cdb2847f58d52736ca11fd63b49cdb2847f58398d3e8a11fd63c634db3107f58392736cb31fd63c49cd82847f58f12736cae28563c49cdb2dca15
  | 5, 0, 0 => 0x839da534db2847f68f12736ca11fc2768c1f7548db2847f68392736ca11fc516839e349cdb2847f67515236ca11fc7968f19b49cdb2847f6839143f8db2847f6839f666cdb310a168f9da548db2847f68395241cdb2847f68395236ca11fc5368392736cd12847f68392736cd02847f6839f6548db2b8a168396349cdb2847f6
  | 5, 0, 1 => 0x839fb49cdb2847f6839da548db2847c6839da528db2847f68393d49cdb2847f6839273a0a11fc6768393736ca11fc6b68398d36ca11fc306839da66cdb2848268397f36ca11fc6f6839f649cdb2847f689dda49cdb2847f6839da45cdb2847f691a3c49cdb2847f6839f5548db2847f68392736cc52847f69220e634db2847f6
  | 5, 0, 2 => 0x8f12736cc62847f68f1da548db3107a68f127450db2847f68394e49cdb2847f6839a636ca123c7f60020e5d4db2847f5839795d4db2847f6839da5e0db2847f68398d36cca2847f68e12736ca12607f68392736ca11fc6d6845da548db2847f68e1f6548db2847f6769c764cdb2847f67b95236ca12607f68392736ca12187f6
  | 5, 0, 3 => 0x8392736cb72847f6839da548db1fc4c683927448db2847f68392736ca11fc0268f1f3548db2847f6839da5c8db2847f68392736ca11fc266839e9548db2cc7f6839da548a11fc4e6839f6408db2847f6839d1634db2847f68b9da548db2847f68395246cdb2847f68f1f2548db2847f683a0b4f4db2847f68397f36ca11fc1c6
  | 5, 0, 4 => 0x9360e634db2847f6839f666cdb2847f689dda66cdb2847f68f12736ca11fc2368b12736ca11fc7968f1da5d0db2847f6839273a0db2847f68392736ca11fc6e60023c5fcdb2847f5839cb634db2847f6839da674db2847f6839da51cdb2847f68392736ca62847f68720e49cdb2847f683975548db2847f6839ee4f4db2847f6
  | 5, 0, 5 => 0x839da554db2847f68392736cae2847f6769523dcdb2847f68391f36ca12387f68397f3f0db2847f60012736c7f0f80c50012736ca11fc0c5839da550db2847f6839c349cdb2847f6839f6540db2847f68399b4f4db2847f6839da548f12847f68395236ca82847f6839da66cdb2f8a168394f49cdb2847f6839ad49cdb2847f6
  | 5, 0, 6 => 0x839da5f8db2847f6839da624db2847f68397f36ca11fc1a68f17f548db2847f60022749cdb2847f583927440db2847f683a0649cdb2847f6839273ccdb2847f68395c49cdb2847f6839da65cdb3087f6839da684db2847f691a0e4f4db2847f67c5da548db2847f6839b0634db2847f68393536ca11fc676839df548db2847f6
  | 5, 0, 7 => 0x8392736ca11fc1268392736ca12787f68393d450db2847f6839c149cdb2847f68392736ca11fc4f6839915fcdb2847f6839dc49cdb2847f683a0249cdb2847f6839da49ce82847f68394349cdb2847f683966548db2847f68392736ca11fc1168392736ca11fc2b68f20949cdb2847f68398d36ca11fc5568392736cd72847f6
  | 5, 0, 8 => 0x839da65cdb2847f6839da548db1fc4b6839b949cdb2847f6839da548db2c47f60020e5c8db2847f58f12736cd02847f60020e634a11fc305839d6548db2847f68392736ca12307f68ca0e49cdb2847f683927450db3107f68392736ca11fc656769ba548db2847f68f1d5548db2847f68392736cd52847f68396b548db2847f6
  | 5, 0, 9 => 0x8394849cdb2847f6769cc548db2847f68392736ca11fc0160020e5fcdb2845558392736ca11fc0e68393d36ca11fc2368392736ca12747f693a0e49cdb2847f6839f6548db2cc7f689dda548db2cc7f60020e674db2847f5839c95fcdb2847f67cdee548db2847f68397f36ca123c7f6839d8548db2847f6000db2847f09c0c5
  | 5, 0, 10 => 0x8397f36ca12607f6839ef49cdb2847f6839da5ccdb2847f6001f1548db2847f583dda548db2847f69260e5fcdb2847f6839da66ce82847f67f9f6548db2847f6839da688db2847f68b1da548db3087f68f1fb49cdb2847f68f1da548db2847c6839da6d4db2847f6839c749cdb2847f68392736ca11fc676839da640db2847f6
  | 5, 0, 11 => 0x8393d36ca12647f6839c649cdb2847f68398d47cdb2847f6839b65fcdb2847f6891f6548db2847f60020e5f8db2847f58398d36ca11fc6b683927414db2847f683a094f4db2847f60020e624db2847f5839da4d4db2847f68399d548db2847f68392736cae2848b683927450fc2847f690a0e5fcdb2847f68392736ca11fc086
  | 5, 0, 12 => 0x66d935fcdb2847f6839da508db2847f6839da548db2dca167515236ca11fc7a68392736ca12247f69020e49cdb2847f683a035fcdb2847f6839da49cdb3087f68a1da548db2847f68394b49cdb2847f68392736ca11fc786839d3548db2847f68395236ca11fc5860020e49ce82847f588dda548db2847f68397f36cc42847f6
  | 5, 0, 13 => 0x8392743cdb2847f6839a036ca122c7f676993548db2847f6839da548db284386839f636ca11fc5168f1f666cdb2847f68392744cdb2847f68393d36cd12847f68f5da548db2847f68393d36cd02847f68392736ca11fc7468392736ccc2847f68392736cdb2847f68f12736ca11fc6e68392736ca11fc0568397e548db2847f6
  | 5, 0, 14 => 0x839d4530db2847f687e0e49cdb2847f6839da548a11fc5e68393d4f4db2847f6839273a4db2847f6839f64f4db2847f6839da548d82847f6839d049cdb2847f6839273dcdb2847f683927478db2847f6839da654db2847f6839da548db2b8a168392736ca11fc076839eb548db2847f6839d448cdb2847f68f1da550db2847f6
  | 5, 0, 15 => 0x839e1548db2847f6839c866cdb2847f6839da49cdb2847f68392736ca12387f68392736ca121c7f6839da4c4db2847f68f20e48cdb2847f6839da648db2847f6851da548db2847f68d1d3548db2847f68f12736cd72847f67d9ee49cdb2847f689de9548db2847f6839e75d0db2847f6839fb4f4db2847f68392736ca11fc726
  | 5, 1, 0 => 0x8392736ca11fc2c68392736cbc2847f6839da548e62847f68397f36ca12707f68392736cd62847f68392736ca11fc6a68e1da548db2847f68f12736cd52847f6839da66cdb3087f68397f36ca11fc7f68392736ca11fc0f68397f36ca11fc7960020e4d4db2847f57695236ca12147f6839da56cdb2847f6839f6560db2847f6
  | 5, 1, 1 => 0x8392748cdb2847f6839f3548fa2847f6839da408db2847f6839524d4db2847f676952380db2847f60020e49cdb3087f58392736ccf2847f68392736ca11fc7768f1d6548db2847f68398d49cdb310a168396a49cdb2847f6839273d8db2847f6891da548e82847f6839ac49cdb2847f68392736ca11fc4a68392736ca11fc2e6
  | 5, 1, 2 => 0x90e0e49cdb2847f68f1c749cdb2847f6839f6570db2847f68f20e634db2847f68f12736ca11fc6767d9ee66cdb2847f68d1da49cdb2847f60013d36ca11fc0c583a0049cdb2847f68397f36ca11fc7568397f36ca11fc0c6839d4548db2847f6839d2548db2847f6839f653cdb2847f60020e36ca120c7f5839da548db2587f6
  | 5, 1, 3 => 0x839f650cdb2847f6909da548d72847f6838db2847f1444f68392736ca11fc046839da660db2847f68397f36ca12407f6839f6548d32847f68392736ca11fc2a68392736cc22847f6839d7548db2847f6839ce548db2847f68392736ca11fc626839da66cdb2847f6839bf49cdb2847f60012736ca11540c58394c49cdb2847f6
  | 5, 1, 4 => 0x8392736ca11fc1968392736ca11fc0069160e634db2847f68393d36cd52847f68392736ca12287f6839db548db2847f6839da63cdb2847f68392736cb42847f68392736ca12807f60020e49cdb1fc3e50020e49cdb2847f58397949cdb2847f6839da548db2c87f68f1da548db2507f6839a7548db2847f676952470db2847f6
  | 5, 1, 5 => 0x8f1d448cdb2847f68392736ca11fc3e68392736ca12847f68b20e49cdb2847f683927494db2847f6839a849cdb2847f6839da3f8db2847f6911d4548db2847f68394836cd02847f6839ab49cdb2847f6839273e0db2847f68398d49cdb2847f68397f36ca122c7f6769523e8d52847f6838db318a12387f6839273c0db2847f6
  | 5, 1, 6 => 0x23449cdb2847f58393d36ca11fc676839a3674db2847f68398d60cdb2847f6909da530db2847f6839fb520db2847f69060e49cdb2847f68f1f64f4db2847f68392736ca11fc0d68392736ca12007f68f1da548d82847f68f1da654db2847f6839f6520db2847f68f1da548db2b8a168392736ca12087f68399349cdb2847f6
  | 5, 1, 7 => 0x8399b634db2847f68392736ca11fc2d68397f36ca11fc306839da57cdb2847f6839de548db2847f68edda548db2847f68f1da49cdb2847f60020e36c7f0f82750020e36ca11fc2758f1da548db2fc7f68f12736ca12387f6838db2847f1485168392736ca11fc3c68392736ca12447f6839da548db2cc7f68f1d4530db2847f6
  | 5, 1, 8 => 0x8392736cbe2847f68f12748cdb2847f67692736ca11fc3d6839d15fcdb2847f683927424db2847f68f1da408db2847f6839c249d142847f6839f6548db2687f68392736ca11fc6668392736ccb2847f68392736ca11fc6f6891da548db2847f6839273f0db310a168398d36ca11fc2768d15249cdb2847f68e20e49cdb2847f6
  | 5, 1, 9 => 0x8392736ca11fc1f6839ec49cdb2847f6769523e8f72847f68f1d7548db2847f6839da36ca11fc5168f1da66cdb2847f6839e95e4db2847f6839524bcdb2847f68f14c49cdb2847f68398d36cc62847f68398d450db2847f683927444db2847f683927450a122c7f60020e3f8db2847f58f1d4548db2847f6839da68cdb2b8a16
  | 5, 1, 10 => 0x23c49cdb2847f58392736ca11fc4d60020e36ca11fc255839da4f4db2847f68392736ca11fc5667fdf6548db2847f67698349cdb2847f6839da49d092847f683927424a12387f6839bd548db2847f68397736ca11fc6b6909d149cdb2847f67695236ca11fc40683952438db2847f68f12736ca11fc0468f1da660db2847f6
  | 5, 1, 11 => 0x8f18d49cdb2847f683927434db2847f6839e74d4db2847f6839f749cdb2847f6839273f0db2847f6839f6518db2847f68392736ca11fc1868397f36ca11fc556839fa49cdb2847f68392736cda2847f67b9da49cdb2847f6839e9548db2847f68398d36ca11fc2367699b654db2847f60023c49cdb1fc3e5839da36ca11fc606
  | 5, 1, 12 => 0x76969548db2847f68397e36ca11fc7960012736c7f0f83d50012736ca11fc3d58395236ca11fc4768392736cb52847f68392736ca11fc5468398936ca11fc79683a0549cdb2847f68f12736ca11fc3e68f12736ca12847f683a09634db2847f68f22c49cdb2847f6839ea548db2847f68f1ab49cdb2847f67699b36ca11fc3d6
  | 5, 1, 13 => 0x8392736ca11fc3468f1da548db2887f68392736cd92847f6839da668db2847f67b9da66cdb2847f60023c36ca11fc2759460e49cdb2847f68f1da548db2cc7f68390d408db2847f68c1da548db2b8a168392736ca42847f60020e5fca11fc305839f6530db2847f6839da548db2b4a1683a004f4db2847f6839ec66cdb2847f6
  | 5, 1, 14 => 0x20e4f4db2847f58392736ca123c7f68392736ca11fc3160018349cdb2847f5839f766cdb2847f60020e49d092847f58392736cb31fc6b69320e49cdb2847f67452736ca11fc7968c1da49cdb2847f649cdb2847f0f83d6839f65e4db2847f6839da549143f0c46839da55cdb2847f68398d36cd02847f6839da570db2847f6
  | 5, 1, 15 => 0x8392736ca11fc6866358349cdb2847f6839da36ca11fc4f68397f36ca11fc6b6839e749cdb2847f68f12736ca11fc6f68392736ca11fc6c68920e49cdb2847f6001ee49cdb2847f5839fd548db2b8a160020e49cdb1543e50020e49cdb284555839da50cdb2847f68392736ca11fc226839da548d32847f60020e4f4db1fc3e5
  | 5, 2, 0 => 0x8390d3f8db2847f68392736cc42847f68b1da548fa2847f6839f365cdb2847f67b95249cdb2847f6839273e8db2847f68393d36ca11fc3e68b20e4f4db2847f6839c247cdb2847f6839524f4db2847f690a0e49cdb2847f689dda548db2847f68e9da548db2847f68399d36ca122c7f68392736ca11fc3368398d4f4db2847f6
  | 5, 2, 1 => 0x8392736ca11fc7d6839da49cfa2847f68f1da49cdb3107f68f1e9548db2847f60020e36ca11542758398d36ca11fc6e68392736cc21fc796839a049cdb2847f6839c049cdb2847f68392736ca11fc5768c1da66cdb2847f68f1bd548db2847f69092747cdb2847f6769935fcdb2847f68392736ca125c7f68f1da36ca11fc516
  | 5, 2, 2 => 0x839f4548db2847f68aa0e49cdb2847f68392736caa2847f6769523b4db2847f6789da548db2847f6829da66cdb2847f68f1273f0db2847f6839da5bcdb2847f68397749cdb2847f60018d36ca11fc0c58397f36cc92847f60023049cdb2847f58392736ca11fc4368392736ca11fc156839e766cdb2847f68d1f6548db2847f6
  | 5, 2, 3 => 0x12736ca22847f58398d36cd52847f68397f524db2847f68392736ca92847f68392736ca11fc7f6839da548e82847f68f1d4548db3107f68392736ca11fc7968f1f6530db2847f6839da548fc2cc7f692e0e49cdb2847f693e0e49cdb2847f60020e36ca11fc4f5839e549cdb2847f68760e49cdb2847f6769d1548db3087f6
  | 5, 2, 4 => 0x92a0e49cdb2847f6839f34e8db2847f6839ed548db2847f68f12736ca123c7f68f20e5fcdb2847f6839b9634db2847f649d1f36ca11fc7968f1da570db2847f6839da544db2847f6839da66cfa2847f68f1da66cdb3107f6001935fcdb2847f58392736cc02847f6001272847f0c00c58392736ca12707f6839273b8db2847f6
  | 5, 2, 5 => 0x8392736ca11fc6968396849cdb2847f6839da564db2847f68392736cba2847f6839f949cdb2847f67fdda548db2847f68392736ca127c7f68392736ca11fc0c683927374db2847f60020e49cfa2847f50023c49cdb3107f58a60e49cdb2847f60023c49cdb2845558f1da50cdb2847f67b9da4f4db2847f6839f349cdb2847f6
  | 5, 2, 6 => 0x89d2736ca11fc6b6891e7548db2847f6899da548db2847f683a054f4db2847f6839da634db310a16839be548db2847f6839da518db2847f68f1524f4db2847f690a3c49cdb2847f683927384db2847f68d9da66cdb2847f689e0e49cdb2847f683a0849cdb2847f68392736ca11fc2f6839c7634db2847f68398d36ca11fc676
  | 5, 2, 7 => 0x911da548d72847f6839da548db3087f68392736ca11fc1b6839f366cdb2847f6839da404db2847f67b95236ca12647f68392736ca122c7f6839c8548db2847f68392736ca11fc246839c249cdb2847f6839524dcdb2847f691e0e5fcdb2847f6839da48cdb2847f68392736ca11fc2168f12736cc42847f68392736ca11fc5d6
  | 5, 2, 8 => 0x91a0e5fcdb2847f67d9ee548db2847f68392736ca11fc106839da634db2847f6839ab36ca12387f69220e49cdb2847f68398d36ca12387f693e3c49cdb2847f694a0e49cdb2847f67695236ca11fc5c68393049cdb2847f6839da548db2ec7f6839da670db2847f68392736ca11fc3968c9da49cdb2847f68c92736ca12387f6
  | 5, 2, 9 => 0x8392736cca2847f68392736ca11fc2860020e48cdb2847f5839c449cdb2847f6811f6548db2847f68f12736ca12707f68392736ca11fc71683927370db2847f6839da548e72847f6839da548db2847f68f1da548e82847f68392736ca11fc3068d1da530db2847f60020e634db310a158f12736ca11fc796839f8548db2847f6
  | 5, 2, 10 => 0x83927390db2847f689dda548fc2847f68f12736ca11fc0c68393d36ca11fc1560023249cdb2847f58392736ca11fc366839c236cc62847f692a3c49cdb2847f6839d149cdb2847f6839da38cdb2847f6839273b0db2847f68392736ca126c7f68660e49cdb2847f683a034f4db2847f68392736ca11fc7b68f1da544db2847f6
  | 5, 2, 11 => 0x8393d4e0db2847f68396c49cdb2847f68f1c249cdb2847f67695236ca11fc616839cf49cdb2847f68f1da48cdb2847f60020e634db1fc3e50020e634db2847f50020e36ca11544f59360e49cdb2847f6769273dcdb2847f68392736ca11fc7a6839cb49cdb2847f68f1da548db1fc4a690a0e49cfc2847f68392736ca11fc0b6
  | 5, 2, 12 => 0x8397f36cd02847f60020e49c7f0f83050020e49ca11fc305839da548db2b0a167699b3dcdb2847f6839fc548db2847f68f9da548db2cc7f683a0350cdb2847f68398d36ca11fc3e68b20e634db2847f68c5da548db2847f68f1da548db3087f6839ab634db2847f68398d634db2847f68f12736ca122c7f68392736ca11fc556
  | 5, 2, 13 => 0x8392736cc12847f68392736ca11fc5960023c48cdb2847f58398449cdb2847f6839fb5fcdb2847f683a0e49cdb2847f68f1da548db2847f68f12736ca11fc3068397249cdb2847f6001273dcdb2847f5769523e4db2847f68f1da634db2847f6839da664db2847f68392736cd42847f68398d36ca12447f68620e49cdb2847f6
  | 5, 2, 14 => 0x20e2847f0c0275839da49cdb2dca168398949cdb2847f68392736cb72848e6839e6548db2847f6839da400db2847f68f1d149cdb2847f6839e7548e82847f68392736ca11fc0968392736ca11fc7e68392736ca12107f68392747cdb2847f68392737cdb2847f6839da644db2847f68392736ca11fc6b68398d36ca11fc6f6
  | 5, 2, 15 => 0x839a949cdb2847f6839aa49cdb2847f68392736ca52847f6869da548db2847f67698d60cdb2847f68392736ca11fc0669120e49cdb2847f6839da68cdb2847f68392736ca11fc3f68392736ca12487f6839da49cdb2b8a168f12736ca11fc7a68f1da548fc36cc468392736ca11fc1e6839da548fb2847f67695236ca11fc3d6
  | 5, 3, 0 => 0x839dd548db2847f6849da66cdb2847f68c12736ca122c7f68392736ca11fc6468392736ca11fc176839da594db2847f68398d3f0db2847f6839273e8a11fc7968f12736ca11fc5560012736ca11fc04576983548db2847f6839a5548db2847f6839da549092847f6839e8548db2847f68f1da5491422c7f60023c634db2847f5
  | 5, 3, 1 => 0x8392736ca11fc3b68392736ca120c7f68398d36ca123c7f60018d60cdb2847f58f20e49cdb2847f60020e49cdb2b8a15839da54cdb2847f69092736cd52847f68392736ca12507f6839da5dcdb2847f68fe0e49cdb2847f60023c49ca11fc3050020e49cdb2dca15769d1548fa2847f6839da680db2847f6879da548db2847f6
  | 5, 3, 2 => 0x8392736ca11fc296839da548fa3087f690a0e634db2847f6839e7548db2847f68392736ca11fc4568f12747cdb2847f6839da36ca11fc5b68392736ca11fc6368f1da644db2847f68f12736ca11fc6b68392736ca12347f68912736ca11fc67676952474db2847f60020e634db2845558c1da548db2847f649cfc3dcdb2847f6
  | 5, 3, 3 => 0x83a0b49cdb2847f60020e5dcdb2847f59123c49cdb2847f68f1da68cdb2847f60020e49ca1154305839da568db2847f6769cd64cdb2847f6839da658db2847f68398d36cc42847f60020e680db2847f58392749cdb2847f68e5da548db2847f68392736ca11fc3d68f1da548fb2847f69160e49cdb2847f6829da548db2847f6
  | 5, 3, 4 => 0x8fe3c49cdb2847f67695236ca11fc4868398d36ca11fc7f68398d36ca11fc7968392736ca11fc036838db2847f1544f68392736ca11fc276891da49cdb2847f6881da548db2847f6839da548fa2847f68f1da548db3107f6839bd524db2847f68398349cdb2847f649cdb354a11fc796839da548db30c7f6839da49cdb2cc7f6
  | 5, 3, 5 => 0x8392736ca11fc7068392736ca11fc496839f768cdb2847f68398d36ca11fc0c6839da549142b8a168c20e49cdb2847f6839273f0a11fc6b60020e49cdb2cc7f5839da548fc2847b6839273f8db2847f6839d9548db2847f68f23c49cdb2847f68392736cc62847f683927450db2847f68392736ca124c7f68398d36ca12707f6
  | 5, 3, 6 => 0x8398d36ca11fc1b68398d36ca122c7f683a0949cdb2847f68392736ca11fc2068392736ca22847f6839c26acdb2847f6839c2634db2847f60020e36ca11fc1b58f12749cdb2847f68392736cb32847f60022449cdb2847f583927488db2847f69163c49cdb2847f686dda548db2847f683a0c49cdb2847f67695236cd53087f6
  | 5, 3, 7 => 0x8f20e49cdb3107f690a2c49cdb2847f68f1da548fa2847f68c9da548db2847f683a0d49cdb2847f68392736ca11fc3568397236ca11fc676
  | 6, 0, 0 => 0x839da548db2847f1cde0e5492736cd02847f70020e7ed2736ca11fda0e791da548db2847f7839da6c15236ca11fde0e769c7524db2847f70020e7d92736ca11fda0e7699136ca11fc7579360e7695236ca11fde0e7695236ca11fc7a7839fb7699b36ca11fdc007692736ca11fc0c68f20e7d95236ca11fdc008392736cd02847f6839f67699b36ca11fde42839da548fc2847f7
  | 6, 0, 1 => 0x20e548db284550558008392736ca11fc6e6839da548db2847f029e18839da548db2847f783a0b7d95236ca11fdc00839da5487f0f83060020e769522847f0c18007699b36ca11fc0c6839da548db2e0a11fde0e7ed5249cdb2847f78f1da548db320a11fde0e7d95249cdb2847f7839da49cdb354a11fde2b839da548db2847f78f1da548db2848b1fde0e7695236ca11fc557
  | 6, 0, 2 => 0x839da548db304a11fde0e7699b36cd52847f7839da68cdb2848b1fde0e5492736ca11fc6e783a0e7695236ca11fde0e768db320a123c7f78f1da548db2847f0c1c00769523dcdb2847f6839f67b95236ca11fde0e7697936ca11fc6b7839da71d2736ca11fde0e7692736ca11fc6770000049cdb2847f03160e7695236cd22847f7839da548db350a11fdc00839f666cdb2847f6
  | 6, 0, 3 => 0x8d20e7695236ca11fde0e769c766cdb2847f7839da66cdb2847f19dc00839da65cdb2847f6839f65491436ca11fdc00768db2847f08c0c6839da5595236ca11fdc008392736cd52847f68f1da7455236ca11fde0e7695236ca11fc417839da548db2847f1f9e0e769c5548db2847f7839da548db284841fde0e7695247cdb2847f7839da548db2847f1ade46839f6548db2847f7
  | 6, 0, 4 => 0x839da7692736ca11fde0e805da548db2847f7839da65d5236ca11fde0e7692736ca12387f70020e71d2736ca11fd8008392736ca11fc6768f1da6c15236ca11fde0e7695236ca11fc0679120e7695236ca11fde0e7d9da4f4db2847f7839da5490636ca11fde0e7695236ca11fc3f7839da548db284921fde4d8f1da548db2847f78f1da548db2847f1e9c00839f636ca11fc236
  | 6, 0, 5 => 0x8fe0e7695236ca11fde0e769d4548db2847f7839da5494936ca11fde50839da548db2847f7839f6548db284991fde0e769b036ca123c7f70023c769522847f0c1a0e825f6548db2847f7839c75492736ca11fde0e769bc548db2847f78c1da548db2848b1fde3c839da530db2847f7839da548fa2847f1e5e3c7695236ca11fc557001da548db2847f011a0e7d95236ca11fc237
  | 6, 0, 6 => 0x839f3548db2847f1e5e247695236ca11fc6770020e49cdb2848e1fda0e7edda50cdb2847f7839da548db2847f04ddda548fc3dcdb2847f7839f6548db344a11fde0e7d95236cd02847f78f20e7695236ca11fdc00839f64f4db2847f6839da75d5236ca11fdc00839da548db2b8a16839da5b55236ca11fdc0076993548db2847f6909da548db354a11fde0e7695236ca12507f7
  | 6, 0, 7 => 0x839da548db2847f0f5e45839da548db2847f7839da548db2847f0a5e0e769ab49cdb2847f7839da6352736ca11fde0e7695236ca11fc1d7002387695236ca11fda0e769523d0db2847f7839fb7d95236ca11fde0e7d9524f4db2847f7839f67d95236ca11fde0e769523c8db2847f7839da548db2847f18de3c7695236ca11fc6b70020e7692736c7f0f9800839da49cdb2847f6
  | 6, 0, 8 => 0x20e768db2847f09d800839d7548db2847f60020e7699b36c7f0f9800839da66cdb2847f67695236cd52847f1e5e0e82dda548db2847f7839d1548db284981fde448f1da548db2847f7839c76f55236ca11fdc00839d4548db2847f60020e76952284550c1800839da408db2847f6839da49cdb2847f0f9e0e7695236cbf2847f78b20e7692736ca11fde0e7695249cdb2847f7
  | 6, 0, 9 => 0x839da548db2847f00de0e7699b36ca11fc3e7839da49cdb2847f1bde2c839da66cdb2847f7839da548db2847f09de0e7699b548db2847f7839da548db2847f051e0e7695236ca12207f7839da548db28ca11fdc000020e49cdb1fc3e5000008392736ca11fd4008395236ca11fc136839ee7695236ca11fde0e7695236ca11fc167839da548db31ca11fde0e76952408db2847f7
  | 6, 0, 10 => 0x20e7695236cb31fda0e769bd548db2847f70020e768db1fc3e08d800839da36ca11fc2368f23c7695236ca11fde0e7695236cc62847f7839da5491436ca11fdc008392736ca11fc3e6839da548db2847f0c9c008b20e49cdb2847f68fe3c7695236ca11fde3c769d4548db2847f7839da548db284811fdc00839ab49cdb2847f683a077695236ca11fdc008398d49cdb2847f6
  | 6, 0, 11 => 0x839da548db2cca11fdc00891da548db2847f6839da548db2847f08de0e769ae548db2847f7839da49cfc36ca11fde0e831da548db2847f7839f671d5236ca11fde0e7699b36ca11fc6f7839e97695236ca11fde0e76952378db2847f70023c7692736ca11fd8000020e36ca11fc275839da548db2847f125e4e839f6548db2847f78c20e7695236ca11fde0e769523f0a11fc6b7
  | 6, 0, 12 => 0x20e768db2847f1458008f1da66cdb2847f683a0d7695236ca11fde0e5492736ca11fc6f7839da548db2847f0d5c00839522847f0c015683a097695236ca11fdc008f1d4548db2847f6839da548db2847f1d9c008395236ca12047f6839da548db288a11fde0e76952428db2847f7839da6bd5236ca11fde3c7695249cdb2847f70020e49cdb2847f1bda0e769cd548db2847f7
  | 6, 0, 13 => 0x20e49cfc36ca11fda0e7695236ca11fc517839e37695236ca11fde0e7699b36ca11fc1a78f1da66d5236ca11fdc00839e9548db2847f60020e7692736ca11558000023c49cdb2847f5839da548db344a11fde0e7695236cd02847f70020e7693d36ca11fda0e7692736ca123c7f7839da66cfc36ca11fde3c839da548db3107f790a2c7695236ca11fdc00839bd548db2847f6
  | 6, 0, 14 => 0x20e7695c36ca11fda1c839da548db2847f783a007d95236ca11fde0e76952448db2847f70020e7699b36ca1155a0e7699b36ca123c7f70023c768db2847f08da3c76952450db2847f7839da5494e36ca11fde0e7692736cc42847f78e1da548db284981fde0e7695236ca12187f7839da5493d36ca11fde42839da49cdb2847f7839da49cdb284981fde0e769523a0a11fc677
  | 6, 0, 15 => 0x1da548db1fc3e0318007695236ca11fc0c6839da70d5236ca11fdc000020e49cdb2845550020e7694336ca11fda42839da66cdb2847f7839da66cdb284981fde0e769ad548db2847f7000008393d36ca11fd4008392736ca123c7f68f1da548db2847f08de2c7695236ca11fc797839da548e836ca11fde0e7695236ca11fc6e7839da49cdb2847f055e0e7695236ca62847f7
  | 6, 1, 0 => 0x20e49cdb310a11fda0e7692736ca12707f7839da5494336ca11fde0e7692736ca11fc797839da548db2847f045e0e7695236ca11fc2b78f2097695236ca11fde0e7695236cd72847f70020e5493d36ca11fd80090a0e49cdb2847f6839da66cdb310a11fdc0089dda548db2847f683a067695236ca11fde0e769523ccdb2847f7839da5715236ca11fde0e7695236cae2847f7
  | 6, 1, 1 => 0x20e780db2847f08da0e769c7548db2847f7839da548db2847f19de0e7695236ca11fc017839da548db2847f039e0e7695236ca12747f793a0e7695236ca11fdc008392736ca11fc156839da49cdb2847f031e0e54914434db2847f7839da548db2848c1fde0e76952450db3107f7839da548db2847f195e0e7695236cd52847f7839da548db2847f049e0e7695236ca12787f7
  | 6, 1, 2 => 0x839da49cdb2848b1fde0e7695236ca11fc787839e0548db2847f08dc00839da548e82847f6839da7195236ca11fdc008392736ca11fc796839da7092736ca11fde0e7d95236ca11fc6f78395249cdb2847f055e0e7699b36ca12707f7839da548db2b8a122de0e76952450fc2847f7839da548db2847f021e0e7bdda548db2847f7839da66cdb2847f1fde0e7699b36ca11fc797
  | 6, 1, 3 => 0x8f1da548db35ca11fddf67b9da548db2847f787e0e7695236ca11fde0e769d0548db2847f7839da548f736ca11fde0e76952478db2847f70020e49cdb2847f031a0e7695236ca11fc077839da5491336ca11fde0e7695236ca11fc747839da548db36ca11fde0e7695236ca11fc057839da66cdb2847f031c00839da36ca1154516839da5494b36ca11fdc008392736ca12707f6
  | 6, 1, 4 => 0x20e36ca11fc230558008392736ca122c7f6839da6b15236ca11fde0e815f6548db2847f7839da548db2847f129e0e7695236ca11fc2e7839da548db2847f0b1e0e7695236cd62847f7839da548db2847f1a9c00839c249cdb2847f68f1da548db354a11fde0e7695236ca11fc0f7839da66cdb2848b1fde0e769da548db2847f7839da49cdb2847f0c1e0e7695236ca12387f7
  | 6, 1, 5 => 0x20e49cdb2847f0c18007d9ee548db2847f60020e7698d36ca11fda0e7695236ca11fc047839da548db2847f0a9e0e7695236cc22847f78395249cdb320a11fde0e7695236ca11fc627839da66cdb2847f0c1e4d839da49cdb2847f7001da548db28455031a43839da548db2847f78f1da71d5236ca11fde3c7695236ca11fc6770020e7695236cc21fda0e769d149cdb2847f7
  | 6, 1, 6 => 0x839da548db2847f0f9e0e7695236ca12847f78b20e7695236ca11fdc00839d149cdb2847f683a03548db340a11fde0e769ab548db2847f7839da548f836ca11fde0e7698d548db2847f7839da548db2847f001e0e7695236ca12287f7839da7459b36ca11fdc008395236ca11fc0f6839da548db284a01fde0e7692736ca11fc5570020e7695236c7f0f9800839da548db2847f6
  | 6, 1, 7 => 0x839da49d1f36ca11fde4d8395249cdb2847f7839da548fc36cc4285c008392736ca11fc556839da49cdb2847f1adc000020e634db2847f5839da66cdb2847f155e0e7d95236ca11fc1570024d8392736ca11fda0e7695236ca11fc3c7839d15492736ca11fde0e80dfb548db2847f79060e7695236ca11fde0e7695236ca11fc0d7839da548db284801fdc00839da49ca11fc306
  | 6, 1, 8 => 0x839e7548db2847f19dc008f1da548db1fc3e60023c7695236ca11fda0e7699b36ca11fc6b7839da548db2847f135e0e7695236ca11fc567909da7455236ca11fde3c7695236ca11fc047839ec7695236ca11fdc000020e49ca11fc305839da5491136ca11fde0e76952450a122c7f7839b05492736ca11fdc00839da66ca11fc306839da548db2847f199e0e7695236ca11fc6f7
  | 6, 1, 9 => 0x9460e7695236ca11fde0e7d95236cc82847f7001da548db1fc3e0f58007695236ca11fc3d6839da548db2d4a11fde0e7695236ca11fc5478f1da548db2847f0f9e3c7695236ca12847f78f22c7695236ca11fdc008392747cdb2847f60020e7699136ca11fd8008392736ca11fc6b6839f77695236ca11fde0e769523f0db2847f7839da548db2847f061e0e7695236cda2847f7
  | 6, 1, 10 => 0x839da66d4936ca11fde45839da49cdb2847f7839e77695236ca11fde3c7695236ca11fc6f7839da548db2847f1b1e24839da548db2847f70020e7695236c550f9800839da548db284556839da548db2848f1fde0e7695236ca11fc317839da548db2cc7f1addda7455236ca11fc7977695236ca11fc3e0f5e3c839da49cdb2847f7839da36ca11fc55145c00839da68cdb2847f6
  | 6, 1, 11 => 0x20e79d5236ca11fda0e7692736ca11fc2778760e7695236ca11fde0e7695236caa2847f78f1da548fc36ca11fde4d839f6548db2847f7002307695236ca11fd8008f20e49cdb2847f6839da548db3087f1e5e0e7695236ca11fc577839da548db284971fde0e7695236cc42847f79360e7694f36ca11fde0e769523e8db2847f7839da49d2736ca11fde42839da548db2847f7
  | 6, 1, 12 => 0x20e769523e8a11fd8008f1da548db3107f60023c7695236ca1155a3c7695236ca123c7f7839da49cdb318a11fde0e76927450db2847f7839da548db300a11fdc00769522847f0c00c6839da548db2849c1fdc007695236ca22847f6839da548db2a4a11fde0e7695236ca11fc7f7839da548db2847f1e5c008392749cdb2847f6002458392736ca11fda4f839da548db2847f7
  | 6, 1, 13 => 0x20e49cdb318a11fd80083927450db2847f6839da548db2848b1fde0e66d5249cdb2847f7839da7095236ca11fde0e825da49cdb2847f78f1da548db310a11fde0e7695236ca11fc5d789dda548db2847f1adc008392736ca11fc27690a3c7695236ca11fde0e76952384db2847f789e0e7695236ca11fde0e7695236ca11fc2f7839da548db2847f1a5e0e7695236ca11fc0c7
  | 6, 1, 14 => 0x20e76952390db2847f78f1da548db2847f031e0e7695236ca11fc367839da548db2849b1fde0e7695236ca11fc7b70020e8252736ca11fda3c7695236ca12707f7839da548dc36ca11fde0e7695236ca11fc3078f1da548db2847f1e5e4f8f1da548db2847f794a0e7695236ca11fde0e7695236ca11fc397
  | 7, 0, 0 => 0x20e825da548db2847f70020e7695236ca11fc23700000839da36ca11fc2360020e76952450db2847f70020e7699b548db2847f7000000020e49cdb2847f500000839da66cdb2847f60020e7695249cdb2847f700000839da49cdb2847f60023c839da548db2847f70020e76952524db2847f70020e7695236ca11fc6b700000839da548a11fc3060020e7695236ca11fc5570020e769b0548db2847f70024d839da548db2847f7
  | 7, 0, 1 => 0x20e7695236cc42847f700242839da548db2847f700000839da548db2845560020e7695236ca123c7f70020e769523f0db2847f7000008f1da548db2847f60020e7695236ca11fc6f70020e7695236ca11fc3e70022c839da548db2847f700000839da548db1fc3e600000839da548db2847f60020e769c7548db2847f70020e7695236ca11fc6770020e7695236cd52847f7000007695236ca11fc0c60020e7695236cd02847f7
  | 7, 0, 2 => 0x20e7695236ca11fc3070020e7695236ca122c7f70020e7695236ca11fc0c70020e7695236ca12707f70020e7695236ca11fc797
  | 8, 0, 0 => 0x839da548db2847f6
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 2 => 34
  | 3 => 44
  | 4 => 54
  | 5 => 64
  | 6 => 74
  | 7 => 84
  | 8 => 94
  | _ => 0

def idWidth : Nat := 10
def wireAt (i : Nat) : Nat := expand (fld (dictB (i / 256) (i / 16 % 16)) 64 (i % 16))
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 512), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]

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
private theorem z2_0 : span (Z 2) 9 0 = true := by decide +kernel

private theorem z2 : span (Z 2) 9 0 = true := z2_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : span (Z 3) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_24 : span (Z 3) 24 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_48 : span (Z 3) 6 48 = true := by decide +kernel

private theorem z3_a1 : span (Z 3) 48 0 = true :=
  span_join (f := Z 3) (a := 24) (o := 0) (b := 24) z3_0 z3_24

private theorem z3_a2 : span (Z 3) 54 0 = true :=
  span_join (f := Z 3) (a := 48) (o := 0) (b := 6) z3_a1 z3_48

private theorem z3 : span (Z 3) 54 0 = true := z3_a2

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
private theorem z4_120 : span (Z 4) 24 120 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_144 : span (Z 4) 24 144 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_168 : span (Z 4) 24 168 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_192 : span (Z 4) 24 192 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_216 : span (Z 4) 24 216 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_240 : span (Z 4) 24 240 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_264 : span (Z 4) 24 264 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_288 : span (Z 4) 24 288 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_312 : span (Z 4) 24 312 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_336 : span (Z 4) 24 336 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_360 : span (Z 4) 22 360 = true := by decide +kernel

private theorem z4_a1 : span (Z 4) 48 0 = true :=
  span_join (f := Z 4) (a := 24) (o := 0) (b := 24) z4_0 z4_24

private theorem z4_a2 : span (Z 4) 72 0 = true :=
  span_join (f := Z 4) (a := 48) (o := 0) (b := 24) z4_a1 z4_48

private theorem z4_a3 : span (Z 4) 96 0 = true :=
  span_join (f := Z 4) (a := 72) (o := 0) (b := 24) z4_a2 z4_72

private theorem z4_a4 : span (Z 4) 120 0 = true :=
  span_join (f := Z 4) (a := 96) (o := 0) (b := 24) z4_a3 z4_96

private theorem z4_a5 : span (Z 4) 144 0 = true :=
  span_join (f := Z 4) (a := 120) (o := 0) (b := 24) z4_a4 z4_120

private theorem z4_a6 : span (Z 4) 168 0 = true :=
  span_join (f := Z 4) (a := 144) (o := 0) (b := 24) z4_a5 z4_144

private theorem z4_a7 : span (Z 4) 192 0 = true :=
  span_join (f := Z 4) (a := 168) (o := 0) (b := 24) z4_a6 z4_168

private theorem z4_a8 : span (Z 4) 216 0 = true :=
  span_join (f := Z 4) (a := 192) (o := 0) (b := 24) z4_a7 z4_192

private theorem z4_a9 : span (Z 4) 240 0 = true :=
  span_join (f := Z 4) (a := 216) (o := 0) (b := 24) z4_a8 z4_216

private theorem z4_a10 : span (Z 4) 264 0 = true :=
  span_join (f := Z 4) (a := 240) (o := 0) (b := 24) z4_a9 z4_240

private theorem z4_a11 : span (Z 4) 288 0 = true :=
  span_join (f := Z 4) (a := 264) (o := 0) (b := 24) z4_a10 z4_264

private theorem z4_a12 : span (Z 4) 312 0 = true :=
  span_join (f := Z 4) (a := 288) (o := 0) (b := 24) z4_a11 z4_288

private theorem z4_a13 : span (Z 4) 336 0 = true :=
  span_join (f := Z 4) (a := 312) (o := 0) (b := 24) z4_a12 z4_312

private theorem z4_a14 : span (Z 4) 360 0 = true :=
  span_join (f := Z 4) (a := 336) (o := 0) (b := 24) z4_a13 z4_336

private theorem z4_a15 : span (Z 4) 382 0 = true :=
  span_join (f := Z 4) (a := 360) (o := 0) (b := 22) z4_a14 z4_360

private theorem z4 : span (Z 4) 382 0 = true := z4_a15

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
private theorem z5_384 : span (Z 5) 24 384 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_408 : span (Z 5) 24 408 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_432 : span (Z 5) 24 432 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_456 : span (Z 5) 24 456 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_480 : span (Z 5) 24 480 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_504 : span (Z 5) 24 504 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_528 : span (Z 5) 24 528 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_552 : span (Z 5) 24 552 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_576 : span (Z 5) 24 576 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_600 : span (Z 5) 24 600 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_624 : span (Z 5) 24 624 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_648 : span (Z 5) 24 648 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_672 : span (Z 5) 24 672 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_696 : span (Z 5) 24 696 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_720 : span (Z 5) 24 720 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_744 : span (Z 5) 24 744 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_768 : span (Z 5) 24 768 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_792 : span (Z 5) 24 792 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_816 : span (Z 5) 24 816 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_840 : span (Z 5) 24 840 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_864 : span (Z 5) 23 864 = true := by decide +kernel

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

private theorem z5_a16 : span (Z 5) 408 0 = true :=
  span_join (f := Z 5) (a := 384) (o := 0) (b := 24) z5_a15 z5_384

private theorem z5_a17 : span (Z 5) 432 0 = true :=
  span_join (f := Z 5) (a := 408) (o := 0) (b := 24) z5_a16 z5_408

private theorem z5_a18 : span (Z 5) 456 0 = true :=
  span_join (f := Z 5) (a := 432) (o := 0) (b := 24) z5_a17 z5_432

private theorem z5_a19 : span (Z 5) 480 0 = true :=
  span_join (f := Z 5) (a := 456) (o := 0) (b := 24) z5_a18 z5_456

private theorem z5_a20 : span (Z 5) 504 0 = true :=
  span_join (f := Z 5) (a := 480) (o := 0) (b := 24) z5_a19 z5_480

private theorem z5_a21 : span (Z 5) 528 0 = true :=
  span_join (f := Z 5) (a := 504) (o := 0) (b := 24) z5_a20 z5_504

private theorem z5_a22 : span (Z 5) 552 0 = true :=
  span_join (f := Z 5) (a := 528) (o := 0) (b := 24) z5_a21 z5_528

private theorem z5_a23 : span (Z 5) 576 0 = true :=
  span_join (f := Z 5) (a := 552) (o := 0) (b := 24) z5_a22 z5_552

private theorem z5_a24 : span (Z 5) 600 0 = true :=
  span_join (f := Z 5) (a := 576) (o := 0) (b := 24) z5_a23 z5_576

private theorem z5_a25 : span (Z 5) 624 0 = true :=
  span_join (f := Z 5) (a := 600) (o := 0) (b := 24) z5_a24 z5_600

private theorem z5_a26 : span (Z 5) 648 0 = true :=
  span_join (f := Z 5) (a := 624) (o := 0) (b := 24) z5_a25 z5_624

private theorem z5_a27 : span (Z 5) 672 0 = true :=
  span_join (f := Z 5) (a := 648) (o := 0) (b := 24) z5_a26 z5_648

private theorem z5_a28 : span (Z 5) 696 0 = true :=
  span_join (f := Z 5) (a := 672) (o := 0) (b := 24) z5_a27 z5_672

private theorem z5_a29 : span (Z 5) 720 0 = true :=
  span_join (f := Z 5) (a := 696) (o := 0) (b := 24) z5_a28 z5_696

private theorem z5_a30 : span (Z 5) 744 0 = true :=
  span_join (f := Z 5) (a := 720) (o := 0) (b := 24) z5_a29 z5_720

private theorem z5_a31 : span (Z 5) 768 0 = true :=
  span_join (f := Z 5) (a := 744) (o := 0) (b := 24) z5_a30 z5_744

private theorem z5_a32 : span (Z 5) 792 0 = true :=
  span_join (f := Z 5) (a := 768) (o := 0) (b := 24) z5_a31 z5_768

private theorem z5_a33 : span (Z 5) 816 0 = true :=
  span_join (f := Z 5) (a := 792) (o := 0) (b := 24) z5_a32 z5_792

private theorem z5_a34 : span (Z 5) 840 0 = true :=
  span_join (f := Z 5) (a := 816) (o := 0) (b := 24) z5_a33 z5_816

private theorem z5_a35 : span (Z 5) 864 0 = true :=
  span_join (f := Z 5) (a := 840) (o := 0) (b := 24) z5_a34 z5_840

private theorem z5_a36 : span (Z 5) 887 0 = true :=
  span_join (f := Z 5) (a := 864) (o := 0) (b := 23) z5_a35 z5_864

private theorem z5 : span (Z 5) 887 0 = true := z5_a36

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
private theorem z6_264 : span (Z 6) 24 264 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_288 : span (Z 6) 24 288 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_312 : span (Z 6) 24 312 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_336 : span (Z 6) 24 336 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_360 : span (Z 6) 24 360 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_384 : span (Z 6) 24 384 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_408 : span (Z 6) 24 408 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_432 : span (Z 6) 24 432 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_456 : span (Z 6) 24 456 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_480 : span (Z 6) 13 480 = true := by decide +kernel

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

private theorem z6_a11 : span (Z 6) 288 0 = true :=
  span_join (f := Z 6) (a := 264) (o := 0) (b := 24) z6_a10 z6_264

private theorem z6_a12 : span (Z 6) 312 0 = true :=
  span_join (f := Z 6) (a := 288) (o := 0) (b := 24) z6_a11 z6_288

private theorem z6_a13 : span (Z 6) 336 0 = true :=
  span_join (f := Z 6) (a := 312) (o := 0) (b := 24) z6_a12 z6_312

private theorem z6_a14 : span (Z 6) 360 0 = true :=
  span_join (f := Z 6) (a := 336) (o := 0) (b := 24) z6_a13 z6_336

private theorem z6_a15 : span (Z 6) 384 0 = true :=
  span_join (f := Z 6) (a := 360) (o := 0) (b := 24) z6_a14 z6_360

private theorem z6_a16 : span (Z 6) 408 0 = true :=
  span_join (f := Z 6) (a := 384) (o := 0) (b := 24) z6_a15 z6_384

private theorem z6_a17 : span (Z 6) 432 0 = true :=
  span_join (f := Z 6) (a := 408) (o := 0) (b := 24) z6_a16 z6_408

private theorem z6_a18 : span (Z 6) 456 0 = true :=
  span_join (f := Z 6) (a := 432) (o := 0) (b := 24) z6_a17 z6_432

private theorem z6_a19 : span (Z 6) 480 0 = true :=
  span_join (f := Z 6) (a := 456) (o := 0) (b := 24) z6_a18 z6_456

private theorem z6_a20 : span (Z 6) 493 0 = true :=
  span_join (f := Z 6) (a := 480) (o := 0) (b := 13) z6_a19 z6_480

private theorem z6 : span (Z 6) 493 0 = true := z6_a20

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : span (Z 7) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_24 : span (Z 7) 13 24 = true := by decide +kernel

private theorem z7_a1 : span (Z 7) 37 0 = true :=
  span_join (f := Z 7) (a := 24) (o := 0) (b := 13) z7_0 z7_24

private theorem z7 : span (Z 7) 37 0 = true := z7_a1

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

def CG : Circuit := ⟨[⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.and, [12, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12665

theorem PEqualNP.Outside.L_meta_12665 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 3974686952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 3974686952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12665.mainG PEqualNP.Outside.L_meta_12665.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12665.CG, PEqualNP.Outside.L_meta_12665.CG_mono, by
      have : PEqualNP.Outside.L_meta_12665.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12665.CG_eval⟩
