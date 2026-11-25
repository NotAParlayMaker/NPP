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
namespace PEqualNP.Outside.L_meta_12463

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (3941263872 * 2 ^ 32 + 3934300672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 11, 9, 13, 9, 15, 9, 9, 9, 9, 9, 9, 9, 23, 9, 25, 9, 27, 9, 29, 30, 31, 9, 9, 9, 9, 9, 9, 9, 9, 9, 41, 9, 43, 9, 45, 46, 47, 9, 49, 9, 51, 9, 53, 54, 55, 9, 57, 9, 59, 9, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 11, 11, 11, 11, 11, 11, 11, 11, 11, 9, 11, 11, 11, 13, 11, 15, 11, 11, 11, 11, 11, 11, 11, 23, 11, 25, 11, 27, 11, 29, 30, 31, 11, 11, 11, 11, 11, 11, 11, 11, 11, 41, 11, 43, 11, 45, 46, 47, 11, 49, 11, 51, 11, 53, 54, 55, 11, 57, 11, 59, 11, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 13, 13, 13, 13, 13, 13, 13, 13, 13, 9, 13, 11, 13, 13, 13, 15, 13, 13, 13, 13, 13, 13, 13, 23, 13, 25, 13, 27, 13, 29, 30, 31, 13, 13, 13, 13, 13, 13, 13, 13, 13, 41, 13, 43, 13, 45, 46, 47, 13, 49, 13, 51, 13, 53, 54, 55, 13, 57, 13, 59, 13, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 15, 15, 15, 15, 15, 15, 15, 15, 15, 9, 15, 11, 15, 13, 15, 15, 15, 15, 15, 15, 15, 15, 15, 23, 15, 25, 15, 27, 15, 29, 30, 31, 15, 15, 15, 15, 15, 15, 15, 15, 15, 41, 15, 43, 15, 45, 46, 47, 15, 49, 15, 51, 15, 53, 54, 55, 15, 57, 15, 59, 15, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 23, 23, 23, 23, 23, 23, 23, 23, 23, 9, 23, 11, 23, 13, 23, 15, 23, 23, 23, 23, 23, 23, 23, 23, 23, 25, 23, 27, 23, 29, 30, 31, 23, 23, 23, 23, 23, 23, 23, 23, 23, 41, 23, 43, 23, 45, 46, 47, 23, 49, 23, 51, 23, 53, 54, 55, 23, 57, 23, 59, 23, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 25, 25, 25, 25, 25, 25, 25, 25, 25, 9, 25, 11, 25, 13, 25, 15, 25, 25, 25, 25, 25, 25, 25, 23, 25, 25, 25, 27, 25, 29, 30, 31, 25, 25, 25, 25, 25, 25, 25, 25, 25, 41, 25, 43, 25, 45, 46, 47, 25, 49, 25, 51, 25, 53, 54, 55, 25, 57, 25, 59, 25, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 27, 27, 27, 27, 27, 27, 27, 27, 27, 9, 27, 11, 27, 13, 27, 15, 27, 27, 27, 27, 27, 27, 27, 23, 27, 25, 27, 27, 27, 29, 30, 31, 27, 27, 27, 27, 27, 27, 27, 27, 27, 41, 27, 43, 27, 45, 46, 47, 27, 49, 27, 51, 27, 53, 54, 55, 27, 57, 27, 59, 27, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 29, 29, 29, 29, 29, 29, 29, 29, 29, 9, 29, 11, 29, 13, 29, 15, 29, 29, 29, 29, 29, 29, 29, 23, 29, 25, 29, 27, 29, 29, 30, 31, 29, 29, 29, 29, 29, 29, 29, 29, 29, 41, 29, 43, 29, 45, 46, 47, 29, 49, 29, 51, 29, 53, 54, 55, 29, 57, 29, 59, 29, 61, 62, 63, 30, 30, 30, 30, 30, 30, 30, 30, 30, 9, 30, 11, 30, 13, 30, 15, 30, 30, 30, 30, 30, 30, 30, 23, 30, 25, 30, 27, 30, 29, 30, 31, 30, 30, 30, 30, 30, 30, 30, 30, 30, 41, 30, 43, 30, 45, 46, 47, 30, 49, 30, 51, 30, 53, 54, 55, 30, 57, 30, 59, 30, 61, 62, 63, 31, 31, 31, 31, 31, 31, 31, 31, 31, 9, 31, 11, 31, 13, 31, 15, 31, 31, 31, 31, 31, 31, 31, 23, 31, 25, 31, 27, 31, 29, 30, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 41, 31, 43, 31, 45, 46, 47, 31, 49, 31, 51, 31, 53, 54, 55, 31, 57, 31, 59, 31, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 41, 41, 41, 41, 41, 41, 41, 41, 41, 9, 41, 11, 41, 13, 41, 15, 41, 41, 41, 41, 41, 41, 41, 23, 41, 25, 41, 27, 41, 29, 30, 31, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 43, 41, 45, 46, 47, 41, 49, 41, 51, 41, 53, 54, 55, 41, 57, 41, 59, 41, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 43, 43, 43, 43, 43, 43, 43, 43, 43, 9, 43, 11, 43, 13, 43, 15, 43, 43, 43, 43, 43, 43, 43, 23, 43, 25, 43, 27, 43, 29, 30, 31, 43, 43, 43, 43, 43, 43, 43, 43, 43, 41, 43, 43, 43, 45, 46, 47, 43, 49, 43, 51, 43, 53, 54, 55, 43, 57, 43, 59, 43, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 45, 45, 45, 45, 45, 45, 45, 45, 45, 9, 45, 11, 45, 13, 45, 15, 45, 45, 45, 45, 45, 45, 45, 23, 45, 25, 45, 27, 45, 29, 30, 31, 45, 45, 45, 45, 45, 45, 45, 45, 45, 41, 45, 43, 45, 45, 46, 47, 45, 49, 45, 51, 45, 53, 54, 55, 45, 57, 45, 59, 45, 61, 62, 63, 46, 46, 46, 46, 46, 46, 46, 46, 46, 9, 46, 11, 46, 13, 46, 15, 46, 46, 46, 46, 46, 46, 46, 23, 46, 25, 46, 27, 46, 29, 30, 31, 46, 46, 46, 46, 46, 46, 46, 46, 46, 41, 46, 43, 46, 45, 46, 47, 46, 49, 46, 51, 46, 53, 54, 55, 46, 57, 46, 59, 46, 61, 62, 63, 47, 47, 47, 47, 47, 47, 47, 47, 47, 9, 47, 11, 47, 13, 47, 15, 47, 47, 47, 47, 47, 47, 47, 23, 47, 25, 47, 27, 47, 29, 30, 31, 47, 47, 47, 47, 47, 47, 47, 47, 47, 41, 47, 43, 47, 45, 46, 47, 47, 49, 47, 51, 47, 53, 54, 55, 47, 57, 47, 59, 47, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 49, 49, 49, 49, 49, 49, 49, 49, 49, 9, 49, 11, 49, 13, 49, 15, 49, 49, 49, 49, 49, 49, 49, 23, 49, 25, 49, 27, 49, 29, 30, 31, 49, 49, 49, 49, 49, 49, 49, 49, 49, 41, 49, 43, 49, 45, 46, 47, 49, 49, 49, 51, 49, 53, 54, 55, 49, 57, 49, 59, 49, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 51, 51, 51, 51, 51, 51, 51, 51, 51, 9, 51, 11, 51, 13, 51, 15, 51, 51, 51, 51, 51, 51, 51, 23, 51, 25, 51, 27, 51, 29, 30, 31, 51, 51, 51, 51, 51, 51, 51, 51, 51, 41, 51, 43, 51, 45, 46, 47, 51, 49, 51, 51, 51, 53, 54, 55, 51, 57, 51, 59, 51, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 53, 53, 53, 53, 53, 53, 53, 53, 53, 9, 53, 11, 53, 13, 53, 15, 53, 53, 53, 53, 53, 53, 53, 23, 53, 25, 53, 27, 53, 29, 30, 31, 53, 53, 53, 53, 53, 53, 53, 53, 53, 41, 53, 43, 53, 45, 46, 47, 53, 49, 53, 51, 53, 53, 54, 55, 53, 57, 53, 59, 53, 61, 62, 63, 54, 54, 54, 54, 54, 54, 54, 54, 54, 9, 54, 11, 54, 13, 54, 15, 54, 54, 54, 54, 54, 54, 54, 23, 54, 25, 54, 27, 54, 29, 30, 31, 54, 54, 54, 54, 54, 54, 54, 54, 54, 41, 54, 43, 54, 45, 46, 47, 54, 49, 54, 51, 54, 53, 54, 55, 54, 57, 54, 59, 54, 61, 62, 63, 55, 55, 55, 55, 55, 55, 55, 55, 55, 9, 55, 11, 55, 13, 55, 15, 55, 55, 55, 55, 55, 55, 55, 23, 55, 25, 55, 27, 55, 29, 30, 31, 55, 55, 55, 55, 55, 55, 55, 55, 55, 41, 55, 43, 55, 45, 46, 47, 55, 49, 55, 51, 55, 53, 54, 55, 55, 57, 55, 59, 55, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 57, 57, 57, 57, 57, 57, 57, 57, 57, 9, 57, 11, 57, 13, 57, 15, 57, 57, 57, 57, 57, 57, 57, 23, 57, 25, 57, 27, 57, 29, 30, 31, 57, 57, 57, 57, 57, 57, 57, 57, 57, 41, 57, 43, 57, 45, 46, 47, 57, 49, 57, 51, 57, 53, 54, 55, 57, 57, 57, 59, 57, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 59, 59, 59, 59, 59, 59, 59, 59, 59, 9, 59, 11, 59, 13, 59, 15, 59, 59, 59, 59, 59, 59, 59, 23, 59, 25, 59, 27, 59, 29, 30, 31, 59, 59, 59, 59, 59, 59, 59, 59, 59, 41, 59, 43, 59, 45, 46, 47, 59, 49, 59, 51, 59, 53, 54, 55, 59, 57, 59, 59, 59, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 61, 61, 61, 61, 61, 61, 61, 61, 61, 9, 61, 11, 61, 13, 61, 15, 61, 61, 61, 61, 61, 61, 61, 23, 61, 25, 61, 27, 61, 29, 30, 31, 61, 61, 61, 61, 61, 61, 61, 61, 61, 41, 61, 43, 61, 45, 46, 47, 61, 49, 61, 51, 61, 53, 54, 55, 61, 57, 61, 59, 61, 61, 62, 63, 62, 62, 62, 62, 62, 62, 62, 62, 62, 9, 62, 11, 62, 13, 62, 15, 62, 62, 62, 62, 62, 62, 62, 23, 62, 25, 62, 27, 62, 29, 30, 31, 62, 62, 62, 62, 62, 62, 62, 62, 62, 41, 62, 43, 62, 45, 46, 47, 62, 49, 62, 51, 62, 53, 54, 55, 62, 57, 62, 59, 62, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x151515ff157f55ff151515ff157f55ff151515ff157f55ff0000000000000000151515ff157f55ff0000000000000000151515ff157f55ff0000000000000000151515ff157f55ff151515ff157f55ff151515ff157f55ff0000000000000000151515ff157f55ff0000000000000000151515ff157f55ff0000000000000000151515ff157f55ff151515ff157f55ff151515ff157f55ff0000000000000000151515ff157f55ff0000000000000000151515ff157f55ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000151515ff157f55ff151515ff157f55ff151515ff157f55ff0000000000000000151515ff157f55ff0000000000000000151515ff157f55ff0000000000000000151515ff157f55ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000151515ff157f55ff0000000000000000151515ff157f55ff0000000000000000151515ff157f55ff0000000000000000151515ff157f55ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa000000000000000000eaeaea00ea80aa000000000000000000eaeaea00ea80aa000000000000000000eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa000000000000000000eaeaea00ea80aa000000000000000000eaeaea00ea80aa000000000000000000eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa000000000000000000eaeaea00ea80aa000000000000000000eaeaea00ea80aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa000000000000000000eaeaea00ea80aa000000000000000000eaeaea00ea80aa000000000000000000eaeaea00ea80aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000eaeaea00ea80aa000000000000000000eaeaea00ea80aa000000000000000000eaeaea00ea80aa000000000000000000eaeaea00ea80aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00eaeaea00ea80aa00

def cMZZ : Nat := 0x151515ff157f55ff0000000000000000151515ff157f55ff0000000000000000151515ff157f55ff000000000000000000000000000000000000000000000000151515ff157f55ff0000000000000000151515ff157f55ff0000000000000000151515ff157f55ff000000000000000000000000000000000000000000000000151515ff157f55ff0000000000000000151515ff157f55ff0000000000000000151515ff157f55ff151515ff157f55ff151515ff157f55ff151515ff157f55ff151515ff157f55ff151515ff157f55ff151515ff157f55ff151515ff157f55ff151515ff157f55ff000000000000000000000000000000000000000000000000151515ff157f55ff0000000000000000151515ff157f55ff0000000000000000151515ff157f55ff0000000000000000151515ff157f55ff151515ff157f55ff151515ff157f55ff151515ff157f55ff151515ff157f55ff151515ff157f55ff151515ff157f55ff0000000000000000151515ff157f55ff0000000000000000151515ff157f55ff0000000000000000151515ff157f55ff0000000000000000151515ff157f55ff151515ff157f55ff151515ff157f55ff151515ff157f55ff151515ff157f55ff151515ff157f55ff151515ff157f55ff151515ff157f55ff151515ff157f55ff

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
  | 2 => 3
  | 3 => 18
  | 4 => 207
  | 5 => 586
  | 6 => 382
  | 7 => 35
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xc07a911a21b107f40e776d08
  | 3, 0 => 0xfefd8f5ef3e16c53eb595b9bdf4caa44d825fd86cd325a41bef4ac1eb9f8bf55b17eecaf9dc71889840697de6be0c3f45ef81c935b4496cc5325fcd927aa68200f2b0be40d433581
  | 4, 0 => 0x41bec4b441411dd33fbd4f4d3cbaa0583c44a4023c3f2bd23bde8a3f3bc9c09b39ed59063995aa33391209bd384ed7103739b02a37178e0c3610800a331113f130d13b9a308eb89c2fdb1b602f87ea302da4ea762cd277c32b809b0e2b1d1d282adb50152a9bb4a92a50bdc829b7226f271d8c47260ca38b2405989f21f7498d21e65ea120e4792f20bc5ef51f559b9f1f4dd2301be6feac1b6fb7bc1b00d17d1ad285731a566e2a19bdcc7118ea2ba9161df3e3147834f20fb71f1a0f7c48290e9c55f00e59e0dc0d19cf3f0c201f6a0bd5c3e70baa902b0b28ce250a5e4f6d0a5dd6b006a0fa15065a51980633da3c0249cb5c01a0677101274a1a00681b95
  | 4, 1 => 0x8e575b138de442608be2b4778a921c1389d749ea8969b32387eb9fe3874aa9c686fdaee7863bd5e8860f475185f356d285c0e2a283a74fd8806e922f7e5060ac7da1892f7aa187bd78d9c69678b1451c78724d5a76ced32275ed64dd750ff8a57419d86b704634f26f5437046f25b5836ee628016e385ab16c72ca536b1a5468697240a2663d471c660ef7606404e9ad6334b9a261531f4d5f84535b5cfa746d5b6978e55ae86c405ac92cf95aa447d15a747e0a5a6ceab259ad690d596950315919fab558c9e0c856c5430555274c2a53d19f2152c5baab5192fe304fe9cb604e009f6c4d9e4cc94ce276f04a2e9af1484762e44551d3ff433442bc427bdfa1
  | 4, 2 => 0xe3611f8ae0a667cfdc04934edbd4d87bd827a736d80e2a0cd7e97d1fd76eaa38d755d9d1d6fdb77bd67ba54bd532ac24d454f29bd32bba6dd2b8f4b6d12df3c2d05736afcf26588ece6688c0ce609881ce118f9ecc5151a2cc25d952cabef9fbca90076fca81de0ec7ecd78cc6bfd8c3c55073ebc4f46248c3363f77c322c6a4c2762e4cc1409a6bc06e61b2c020b4f7be6e0110bc9740d1badaddd9ba9fc706b9bd654fb9068152b903ed25b886b467b230ff9cb0199062af65208aae06ff7fac0c2a32aa7ee1b0a8004bd7a5544a89a2bf1d34a19b6a2b9e27c42c9df143cd9d07c6d69c9bed859c66035297f9b0e097b47c0d9436b6e293dcb4f58f151ebf
  | 4, 3 => 0xfeecc60bfe745787f82e9724f7dbf475f7d74ba2f5e9a8a1f549d488f3cc7c91f37db9eef37bd286f03f96b1ee815d63ece36f74e9fd8c90e8305cc2
  | 5, 0 => 0x13ad41ae13a93de812f1406c129b6c77122fe08911bad86910f8b20210cc874e10a454441014ae3d0fb2afbc0fa429060f408af60ec13efd0e5941920de702950dd1fd7b0db7ffd10d91a9360d53bdbf0d1dce8f0d0b535a0cd87d410cd8418a0cd4719f0bf0171a0bd5b53b0ba4c5b60ba082cf0b8846200a9082aa0a8adb580a67640e0a608fcb0a43c9a109b756db08e7208a089afa11085b48740846928e078db7240749150f0746095f05b4365a05613cdc048b9b3e046a4dcd0450573203e01f0a039bad7a038a8853037a49b303161ebd0249cb5c02469557021f692b01a0ca84017bc8e601655524011c95ab01088b6e008c7ab0005f4b68002f17bd
  | 5, 1 => 0x28d8871628d03a0428cbe9462833dc472805428f27e0f13527d732ed27ca446f275459ed2707b8652702fe53261ff83125e4be3225ccf36025c861be25b6d1752529d7f724a037c72477aa4f244865f42401bd7723db461b232f1c3a23172d82226889e62237e1cb223649a822287525220af1b921f6ae1321ce933c20913f3f2002cd441ff1373b1fd715801f861cc01eceb5f91ec60a9b1e53ffe41de6bce41dd020941d78c02c1d09d6bc1c4411061c34ee841b7093a41b2eec6f1afefb9f1ac89354199c70311991dbe618ea2ba9183861a417960152175d4f681705bc2416f55f14162d5f191605b232156c0ade14bf520b14b7c6bf147d8da613cc3082
  | 5, 2 => 0x41a349a7412853a340bce71240174e8d3f9eb56c3f8dca803f08a43f3e82f5083e63cad43e0d392f3de3d3833d9e73623d7caed53cfd077e3c671c113bc9c09b3b90d74e3b12aa1b3a77f11539dc6ebe39a58372399a85b9397be2533917239b38c44f6238a83d5c3825a6f6381069b1370084d736cf547536919788365e19ea362ad35435c8e6963561173133db563b33c55fc2331113f1330a090032b74d403217797631ac526b315f539330f54f9d30d13b9a30108cdf2fdb1b602ec0b0332e2eb5f92d72804d2d5ffe7a2c1b12b02c0a975b2c014cbb2b2b912e2b1d1d282ac13b1e2aa2dc952a87f10329ac231f29a9c0cb299fcbb22954399c2951fc0a
  | 5, 3 => 0x55ff56175577be745526fb5354e11c0954a9b9aa5437013e53efc27753d653535392e2f85376760950f8bcbc50f60e0350de4dea50b87fd050b4e39b509d017e50430f574fd8bf664ee23e364e8155874e78a7794e56bf8d4e36247b4d9297d24d82873f4d5ad4764d540d314d4543d74d3aea044c71f8794c2b53394bd0c8da4bbc12d44b60e9074b192c664b056b804acaa9704a3fece4492806ed4890dd2147f829a747ddeccb47be0e7a475e8e4e470d82b7466d0271465886b545c6a31c4569086d44f0a4c544c4f8264489774644715d9844154ff143bbe50443314168431e2bf742900c384284ea8541e844ed41d51f1c41d0e87641c5034141a6dad4
  | 5, 4 => 0x6e2777436d91373f6d8094606d2612136cb4ec0e6bf98bfe6ba80b4b6b4f7a516b45b8a86b19fd0a6abee9806a90f8ad6984f51a6971571b68ed9b5467c2e1a167790d42668ce9326688c3a8665c302b664232816621195865eecec365a004566589d6216501f82c64a7a95e647dc3ca644de01564351fd26400d8626376ed8c637657b46334b9a262ea88f262c1e03d629bb7ce627b4a136236191a613163eb60a32b076019ea645fec2fd15f9873ac5ee889b25ea253725e6cc3215cfa56245c2618915baa39815b06867f5ac16aa05a76bad05a620c375a012d6859a8e89e59712c7a5939a51a58f9433157dfb14157a2499e578d7c845749a70056b9759c
  | 5, 5 => 0x857ac24c84dc34a183b6633f82f3aead82c1b21382be717c8263ea5581ac558c81378150810a82c880dc25817fbdf78f7fa986cb7eecf6e67ede35cd7e23ec1a7d69ae747d55d45f7b1cd2cb7b1976057afedfa57ae38e227ad905177aa187bd7a5a945479e5c96d79b4cb057999cc817910e4c479009fdc78f9b01a77ffdf8277f4dd857754d4ec76ced322769a8aeb7691954876714ca77607380775ae29b2750ff8a574d9077374d33603746caee4745e5f1173b37e9273663b4572ceb809728e50e671833e51716756917114f5cd70beac01709d024b70553d27704634f27034e38e6fdd9b306fa012e96f3a6a0f6f25b5836eb791c96e4a5be76e2e8a29
  | 5, 6 => 0xa5f8296ea5930bc2a45c3232a44786a1a3e341c7a3b6b330a39ac2b1a1b0c541a1a6eb77a19bc30aa0f7bf099fb468049fa631ff9f3ca71e9f163e029e8d21da9e580c0d9e294f8d9e27c42c9e15fe0e9e15ca519d07c6d69cfce9d89b43a0979b332e819a096b6099276621984c2d2c9848f39c984153d997f9b0e0977ebbae96bdcd869658b0fb9619b9399575b3e194c14409948d546194763f0193a9b57b9394d0bc92fc138d92b764849113062190015f7a8ef98b548e575b138cffd90f8cf047838becae228b2fdf638af14dbd8a9053138a12420689ceb00b8960571188c24ba487f1afbc87bc9f8e874ba391873b413c8719ac8185f356d285e5d24a
  | 5, 7 => 0xd250b7dcd1340f9bcff5cfd4cff24e7ecf7e65b6ce6688c0cdc0fc41cd0c8c69ccf155e6cc6f1a72cb8f5836cafffc8bc9b39611c739fa97c6c6cc33c6c06975c619e510c53f1ebec36d2ce5c349927bc3363f77c2336ad4c103c509c0668913bf88b549befe04dabdf31265bd87940ebd836c9fbc3c4936bc0b381abb98afacbb8a1f5dbab30a14baaf32b5ba0d6f31b87764a1b8532ff8b73fca3cb7167caeb6d7a59ab5e991bfb5a11cbfb51ac3e7b4abab80b44a3eeab35abd6db2f690bab230ff9cb022c3e3b0199062af65208aaeb29c8aadc411dead778186ad0625d6abfec6f2ab8bae3faab48023aa6d201fa8e89d0ea881574ca727914ba64ccb16
  | 5, 8 => 0xf6f4eb7df665d4e5f6253741f5cf1315f5b595ebf4a5235af470a628f437dad0f37bd286f2da1803f1fd7789f1fc5e7af0da2a3df0d3264cf0a7195ff0606095f0568338ef5290f1ef0a6364eeda06c1edfea28eed2528d3ece36f74eb8763f4ea33b5e5ea182817e9e6e6c2e9224b51e8ffdfffe86665dae837734ee6ec196fe68b393fe5e20c7ce5c2165de4229cb1e3fd064ae3a23425e36839a3e2f7dfcae21fad9ae197a4dbe18cbe8ee0ddab56e0d5e8eae0ca3283ddee15b3ddc820d6ddb77ad4db5fbfb0da97947cda3eacb0d8907bfed88249b8d7e30393d6fdb77bd6ab5904d627f40ed5aecf1cd57483dbd4178ad4d3665e7bd363a9e9d2978c00
  | 5, 9 => 0xffe341fdff0349cffa4dbe4af981f1b9f9407c3af89abf5ef80730a3f7e6dba5f7a0dbd5f74cf2fd
  | 6, 0 => 0x2121b59220f86fd320bd8a9c2002cd441ff1373b1fee01361f4836631f0cc1031ec4018a1dd6839c1d78c02c1d602e541cefc3571caab5b31c98c7fe1c55edaa1bedbb071ac508c51a7e71af1a245c601a078acf1912899117f52a2e1763402817295d9d16e7e81e168f0ab2156d534c154847b914f45ee114bf520b149c5761140d40c913cca32512bd752210f8b2020fa4e36d0f9af64d0dd1fd7b0db7ffd10d26e8f00c8172a50c80d3820bb475790b028d3e0acc94b708c1f0e608516fd107bf93fb078e52a606a74be30656cf50063c65a1061d193005b4365a05791e6305613cdc0432a52303187fd501ca089501a4722e0149a009010fa58700d24802
  | 6, 1 => 0x3fcfe1043fb25d983f75ff1b3e82f5083d7e815f3d614ba33d2d889f3b8e28c339eb7ce53917ff8338d6584e38a6677e3825a6f637b74aa83786319c36919788358f6a0c3504bb47349ccaf333d4caf833d1b19f331376bd329dfe48325f329e31bdef7630f4e4aa30d13b9a3042d8562ec0b0332ea01de12dbc1a1c2ce7f6d52c68aadc2c00ad712b79695a2b5f6bb02b3915152ac53a6e297d211a2947eeae292fb1ff280ecfed27eb358027d732ed27a42e93275ec2ba273ac94c2702fe5326e1ab6e268e8c69261ff83125edfe6d2535230324f080ee24ed753e24384f21238fa4912308a8bb2305dc1e2237e1cb2233071d2211b9ac21888a5921431959
  | 6, 2 => 0x671b377a6645536266384900658558aa64b4ee96629810a46230e32561bcbbd06183951a616350e360d8ad47602c56645f9564ee5f6c6f205f4e46b35f4ab5865dbfbb6c5d8578b35bb4a50e5b45df4158b5e98856e193cc55cd12d555b7d59055b1e38d54a7f0b65477e407540585c953d6535353d23f3353c8b7995385d6c050fa481d50b174df505eb91f4e78a7794d82873f4bfb292f4b1d25bc4b076a594b056b8049b2033a4949e0df48d2fd0d484a4874482f5ce2467ff2f546735525466d027145f13d5a45db4826457e9ecc44af244444aa6a324441800643bbe50443745f3f436fcd9d435e3d544247a3a6421f162e41a6dad440d688193fddb587
  | 6, 3 => 0x8c5efda88bf1c7c68bd5f6088bcee3228acd7df28ab3fc238a9053138866555f872c60f98718c2fa869507338637570b856a4d80852079218434551184302f8784039c0a83938fa78331420082be717c811e596b80dc258180a0c2e77eecf6e67e23ec1a7dc156437d3fdf8b7c49bf517b1cd2cb7aa1c20378eadda077a899477750547d75871d207549b57d7534e86374f112df74d33603742517ad7348275772ce67327251258971de6d1d71cefd6a7167569170beac017034e38e6edc30aa6eb791c96e9d79e26e85b9c96e5c4f7a6e2777436dea7b366cb4ec0e6c89aa156bfe2b6c6984f51a697834b969637eb3690854e668acd75f67e758c3677675ca
  | 6, 4 => 0xbefe04dabe9f2ae8bd4d9ddebcbda9e1bc0b381abbff77ecbbd0bb6cbbbd3630baa455b7b8323567b5f3990bb5a11cbfb526278db44a3eeab31d1fc0b1d4425faeb29c8aaca21123ac1174caabfec6f2aab48023aa71d465aa1deb8da936cd75a8d74b42a837bef2a669b783a5991b9ba4e2ad1ba38d3e29a1a6eb77a0f7bf09a0c4eff7a09b1a8ca0691df2a065dd5b9eb1eea79e294f8d9d65636e9c9462c59b111a539afd403e995c31cf984c2d2c9848f39c98020033978d354c975c36e496732cb595a74b61959c496494763f01943901279355959193422ce692b76484927aa1e29205caf0915aea718f0ec2708e6617e08e446e2a8dfca9068ddc4f6d
  | 6, 5 => 0xff342a6dff0349cff9407c3af9072b8ff83f005bf7a0dbd5f74cf2fdf66b7634f665d4e5f58a6f72f3cf5fedf3563afbf1bef6b3f10dca5af10b15c8f03ef7dfed99ba5deaf69f81ea168651e936c415e8a7686ae68b393fe4e16676e467d554e3c150efe3a23425e0ddab56deab30e8dd302128dcdb6f7ddca570b9db9a7e44d9e3b515d9d3f6ded9b2a3f9d9318b3cd7e30393d61ed080d4bde88dd421717dd3665e7bd253175fd1f1aac9d102294ccdca2fc2cdc0fc41cc5a0869cb6b7dbdcb1eed65c85bec02c8148bfec69008edc628c32bc619e510c4cefd2ac44e4d3dc3c9aa8dc1eef280c0f5a9b8c0a2f606bf583120bf4e5756
  | 7, 0 => 0xf10dca5ae3c150efe3a23425dca570b9d9b2a3f9cc5a0869c85bec02bf4e5756be9f2ae8bbd0bb6cb5f3990ba837bef2a065dd5b9c9462c58ddc4f6d8c5efda8872c60f9616350e35f4e46b34e78a779457e9ecc44aa6a3230d13b9a2ea01de12b79695a2b5f6bb026e1ab6e1d602e541caab5b31a078acf16e7e81e154847b914f45ee1140d40c90432a523
  | 8, 0 => 0x4e78a779
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55550000555500003f3f00003f3f00000f0f00000f0f000000ff000000ff00000000ffffffff00000000ffff000000000000ff00ff0000000000f0f0f0f000000000c0c0c0c000000000aaaaaaaa0000000055555555000000003f3f3f3f000000000f0f0f0f0000000000ff00ff000000000000ffff0000000000000000
  | 0, 1 => 0xff0000ffff000000ff000000ff000000f000f000f000f000c000c000c000c000aa00aa00aa00aa0055005500550055003f003f003f003f00330033003300330000ffffffffffff0000ffff0000ffff0000ffff000000000000ff00ff00ff000000ff000000ff000000cccc0000cccc0000c0c00000c0c00000aaaa0000aaaa
  | 0, 2 => 0x2222222222222222151515151515151511111111111111110fff0fff0fff0fff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f00000f0f00000f000f000f000f000c0c0c0c0c0c0c0c030303030303030300ffffff00ffffff00ffffff0000000000ff00ffffffffff00ff00ff00ff00ff00ff00ff00000000
  | 0, 3 => 0x40c040c040c040c040404040c0c0c0c040404040404040403fff3fff3fff3fff3f3fffff3f3fffff3f3f3f3fffffffff3f3f3f3f3f3f3f3f3f3f3f3f000000003f3f00003f3f00003f003f003f003f003333ffff3333ffff3333333333333333333300003333000030303030303030302a2a2a2aaaaaaaaa2a2a2a2a2a2a2a2a
  | 0, 4 => 0x80008000800080007f7f7f7f7f7f7f7f7f7f7f7f00000000777777777777777755ff55ff55ff55ff55ff55ff0000000055ff000055ff00005555ffff5555ffff55555555ffffffff555555555555555555555555000000005555000055550000550055005500550050f050f050f050f050505050f0f0f0f04444444444444444
  | 0, 5 => 0xaaaa8080aaaa8080aaaa0000aaaa0000aaaa000000000000aa88aa88aa88aa88aa80aa80aa80aa80aa00aa00aa00aa00aa00aa0000000000aa000000aa000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a00000a0a00000a000a000a000a0008888888800000000808080808080808080808080000000008080000080800000
  | 0, 6 => 0xaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00aaaaaaaaaaaa0000aaaaaaaaaaa0aaa0aaaaaaaaaa88aa88aaaaaaaaaa80aa80aaaaaaaaaa00aa00aaaaaaaaa0a0a0a0aaaaaaaa80808080aaaaaaaa00000000aaaaaaa0aaaaaaa0aaaaaa80aaaaaa80aaaaaa00aaaaaa00aaaaa0a0aaaaa0a0aaaa8888aaaa8888
  | 0, 7 => 0xc0c0c080c0c0c080c0c0c000c0c0c000c0c0c000c0c00000c0c08080c0c08080c0c04040c0c04040c0c00000c0c00000c0c0000000000000c080c080c080c080c000c000c000c000c000c00000000000c0000000c0000000bfbfbfbfbfbfbfbfafafafafafafafafaaffaaffaaffaaffaaaaffffaaaaffffaaaaaaffaaaaaaff
  | 0, 8 => 0xc0c0e0e0c0c0e0e0c0c0ccccc0c0ccccc0c0c0ffc0c0c0ffc0c0c0f0c0c0c0f0c0c0c0c0ffffffffc0c0c0c0ccccccccc0c0c0c0c0c0ffffc0c0c0c0c0c0ccccc0c0c0c0c0c0c0c0c0c0c0c0c0c0c000c0c0c0c0c0c08080c0c0c0c0c0c00000c0c0c0c0c080c080c0c0c0c0c000c000c0c0c0c080808080c0c0c0c000000000
  | 0, 9 => 0xccc0cc00ccc0cc00cc00cc00cc00cc00cc00cc0000000000cc000000cc000000c8c8c8c8c8c8c8c8c8c8c8c8c8c0c8c0c8c8c8c8c0c0c0c0c8c0c8c0c8c0c8c0c8c0c8c0c0c0c0c0c4c4c4c4c4c4c4c4c0ffc0ffc0ffc0ffc0ffc0ff00000000c0ff0000c0ff0000c0ccc0ccc0ccc0ccc0c0ffffc0c0ffffc0c0eaeac0c0eaea
  | 0, 10 => 0xccccccccc0c0c0c0ccccccccc0c00000cccccccc00000000ccccccc0ccccccc0cccccc88cccccc88cccccc00cccccc00cccccc00cccc0000ccccc8c8ccccc8c8ccccc0c0ccccc0c0ccccc0c0cccc0000ccccc000ccccc000cccc8888cccc8888cccc4444cccc4444cccc0000cccc0000cccc000000000000ccc0ccc0ccc0ccc0
  | 0, 11 => 0xddddddddddddddddd5d5d5d5d5d5d5d5cfcfcfcfcfcfcfcfccffccffccffccffccffccff00000000cccceeeecccceeeecccccfcfcccccfcfccccccccccccffffcccccccccccccccccccccccccccccc00ccccccccccccc0c0cccccccccccc8888cccccccccccc0000cccccccccc88cc88cccccccccc00cc00ccccccccc8c8c8c8
  | 0, 12 => 0xeaeaaaaaaaaaaaaaeaea0000eaea0000eaea0000c0c00000eac0eac0eac0eac0eac0eac0c0c0c0c0eac0c0c0eac0c0c0eaaaeaaaeaaaeaaaeaaaeaaaaaaaaaaaeaaaaaaaeaaaaaaaea00ea00ea00ea00e0e0e0e0e0e0e0e0e0e0e0e0c0c0c0c0e0e0c0c0e0e0c0c0e0e0c0c0c0c0c0c0e0c0e0c0e0c0e0c0e0c0c0c0e0c0c0c0
  | 0, 13 => 0xeeeeaaaaeeeeaaaaeeee0000eeee0000eeee0000cccc0000eecceecceecceecceecccccceeccccccee00ee00ee00ee00ececececececececeaeaeaeaeaeaeaeaeaeaeaeaeac0eac0eaeaeaeac0c0c0c0eaeaeaeaaaaaaaaaeaeaeaea00000000eaeac0c0eaeac0c0eaeac0c0c0c0c0c0eaeac0c000000000eaeaaaaaeaeaaaaa
  | 0, 14 => 0xf0f0c0c0f0f0c0c0f0f0c0c0c0c0c0c0f0f0a0a0f0f0a0a0f0f00000f0f00000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0c0f0c0c0c0c0c0f0c0c0c0f0c0c0c0f0a0f0a0f0a0f0a0f000f000f000f000eeeeeeeeeeeeeeeeeeeeeeeecccccccceeeeeeeeaaaaaaaaeeeeeeee00000000eeeecccccccccccceeeecccc00000000
  | 0, 15 => 0xf2f2f2f2f2f2f2f2f1f1f1f1f1f1f1f1f0ff0000f0ff0000f0f3f0f3f0f3f0f3f0f0fffff0f0fffff0f0f0fff0f0f0fff0f0f0f0fffffffff0f0f0f0f3f3f3f3f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0c0f0c0f0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f000f0f0f000f0f0f000f0f00000
  | 1, 0 => 0xfafafafaaaaaaaaafafafafa00000000fafaf0f0fafaf0f0fafaaaaafafaaaaafafa0000fafa0000fafa0000f0f00000faf0faf0faf0faf0faf0faf0f0f0f0f0faaafaaafaaafaaafa00fa00fa00fa00f8f8f8f8f8f8f8f8f8f8f8f8f0f0f0f0f8f0f8f0f8f0f8f0f3f3f3f3f0f0f0f0f3f3f0f0f3f3f0f0f3f0f3f0f3f0f3f0
  | 1, 1 => 0xff000000ff000000ff00000000000000fefefefefefefefefefefefe00000000fefe0000fefe0000fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcccccccccfcfcfcfc00000000fcfcccccfcfcccccfcfc0000fcfc0000fcf0fcf0fcf0fcf0fc00fc00fc00fc00fafafafafafafafafafafafafaf0faf0fafafafaf0f0f0f0
  | 1, 2 => 0xff00ffffff00ffffff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00aa00ff00ff00ff000000ff00ff00fa00fa00ff00ff00f000f000ff00ff00ea00ea00ff00ff00c000c000ff00ff00aa00aa00ff00ff0000000000ff00ee00ff00ee00ff00ea00ff00ea00ff00cc00ff00cc00ff00c000ff00c000ff00aa00ff00aa00
  | 1, 3 => 0xffaaffaaffaaffaaffaaffaaff00ff00ffaaffaaaaaaaaaaffaaffaa00000000ffaaff00ffaaff00ffaaff00ff00ff00ffaaaaaaffaaaaaaffaa0000ffaa0000ffa0ffa0ffa0ffa0ff80ff80ff80ff80ff80ff00ff80ff00ff55ff55ff55ff55ff3fff3fff3fff3fff33ff33ff33ff33ff15ff15ff15ff15ff11ff11ff11ff11
  | 1, 4 => 0xffeaffea00000000ffea0000ffea0000ffccffccffccffccffccffccccccccccffccffcc00000000ffccff00ffccff00ffccff00ff00ff00ffcc0000ffcc0000ffc0ffc0ffc0ffc0ffc0ffc0ff00ff00ffc0ffc0c0c0c0c0ffc0ffc000000000ffc0ff00ffc0ff00ffc0ff00ff00ff00ffc0c0c0ffc0c0c0ffc00000ffc00000
  | 1, 5 => 0xffff0000fafa0000ffff0000f0f00000ffff0000eaea0000ffff0000cccc0000ffff0000c0c00000ffff0000aaaa0000ffff000000000000fffcfffcfffcfffcfffafffafffafffafffafffa00000000fff0fff0fff0fff0fff0fff0ff00ff00fff0fff0f0f0f0f0fff0f0f0fff0f0f0ffee0000ffee0000ffeaffeaffeaffea
  | 1, 6 => 0xffff3f3fffff3f3fffff3f00ffff3f00ffff3333ffff3333ffff1515ffff1515ffff0f00ffff0f00ffff0505ffff0505ffff00ffffff00ffffff0000ffffffffffff0000ffff3f3fffff0000ffff3333ffff0000ffff0000ffff0000fff00000ffff0000ffc00000ffff0000ffaa0000ffff0000ff000000ffff0000fcfc0000
  | 1, 7 => 0xffffc0c000000000ffffc000ffffc000ffffc000ffff0000ffffc00000000000ffffaaaaffffaaaaffffaaaaffff0000ffffaaaaaaaaaaaaffffaaaa00000000ffffaa00ffffaa00ffffaa00ffff0000ffffa000ffffa000ffff8888ffff8888ffff8080ffff8080ffff8000ffff8000ffff5555ffff5555ffff555500000000
  | 1, 8 => 0xfffff0f0f0f0f0f0fffff0f000000000fffff000fffff000ffffeeee00000000ffffeaeaffffeaeaffffeaea00000000ffffccccffffccccffffccccffff0000ffffccccccccccccffffcccc00000000ffffcc00ffffcc00ffffcc00ffff0000ffffcc0000000000ffffc0c0ffffc0c0ffffc0c0ffff0000ffffc0c0c0c0c0c0
  | 1, 9 => 0xffffffccffffffccffffffcc00000000ffffffc0ffffffc0ffffffc000000000ffffffaaffffffaaffffffaa00000000ffffff00ffffff00ffffff00ffffaa00ffffff00ffff0000ffffff00ff00ff00ffffff0000000000fffffcfcfffffcfcfffffcfc00000000fffffafafffffafafffffafa00000000fffff0f0fffff0f0
  | 1, 10 => 0xffffffff55555555ffffffff3f3f3f3fffffffff3f003f00ffffffff33333333ffffffff33003300ffffffff15151515ffffffff11111111ffffffff0f000f00ffffffff00ff00ffffffffff0000ffffffffffff0000aaaaffffffff00003f3fffffffff00000f0fffffffff000000ffffffffff00000000fffffff0fffffff0
  | 1, 11 => 0xffffffffcc00cc00ffffffffcc000000ffffffffc0c0c0c0ffffffffc0c00000ffffffffc000c000ffffffffc0000000ffffffffaaaaaaaaffffffffaaaa0000ffffffffaa80aa80ffffffffaa00aa00ffffffffaa000000ffffffff88888888ffffffff88008800ffffffff80808080ffffffff80800000ffffffff80008000
  | 1, 12 => 0xffffffffffffaaaaffffffffffff0000fffffffffff0fff0ffffffffffc0ffc0ffffffffffaaffaaffffffffff00ff00ffffffffff00aa00ffffffffff000000fffffffffcfcfcfcfffffffffafafafafffffffff0f0f0f0fffffffff0f00000fffffffff000f000ffffffffeaeaeaeaffffffffccccccccffffffffcccc0000
  | 1, 13 => 0xffffffffffffffffffffffffffffff00ffffffffffffccccffffffffffffc0c0
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x12d6ab34f2cd53d1e58fa6e3
  | 3, 0, 0 => 0xdcd965ad74e5665086e4cb595086e4accb5aa7a4cacb4fa6e4accb4fa6e4e4e650e6e496b35006e4cb595aa87496b519a6e4b2cb5acd54dbd965ad84dcd6e5ad84cbe590e6e4e56610e6e4cb3dd526e4
  | 3, 0, 1 => 0xcb200f46e4adcb5aa874
  | 4, 0, 0 => 0xd0d965a7f372d965abb439b97432d6ea1cdcba1b2cb5966e5ded965ad543ae87092d439b9743659521cdcb6596b59a86e5d0cb5d887312e865afd439b9743658d21cdcba9b2cb50e6e5d0dde5a87372e86cb2d691b97436a96a1cdcba1b2cb5846e5
  | 4, 0, 1 => 0xcacb5d887372f2b32f7599b972d95b2a1cdcb6596c710e6e5d0d965a89372ee6b72d439b96cb5696a1cdcba1b24b50e6e5d45965a87372e86cb2d601b972d657baccdcb6596b890e6e5d0d465a87372e565af05b9b972b65969f8dcb5996bc16e6e5
  | 4, 0, 2 => 0xd0d965a87372d95c4da439b9743658321cdcb65accb5aa875d0d965a90372f2b30f75b9b976b6596a1cdcba1b2cb5086e5b2cb5acad372d6e5af2439b97919996a1cdcba1b14b50e6e5d0d950e6e0a2e86cac63d1b976f6596a1cdcba1b2cb50e645
  | 4, 0, 3 => 0xd0dde5ac1372e86cb24439b97956596b550eba1b5cb50e6e5b2cb5ac80372e86cb2d439a57436596b1d0eba1b2b190e6e5dd5965a87372e86bd2d4d9b96cb2d7021cdcba4b2cb50e6e5d0cb50e6e24ae86cf2d439b97436596a0cdcba1adcb50e6e5
  | 4, 0, 4 => 0x96b519c87372e86c12d439b9743967621cdcbcee56650e6e5b2d3e5a87372e86dd2d439b97676596a1cdcb96b2ab50e6e5e765aca87372dc2cb2d439b972cf756a88dcba1b2cb5106e5d0dde5a87312e5f2cf75b9b96cb2d6ab510eb2d874296e6e5
  | 4, 0, 5 => 0xdb5de5a87372d965ae2621b97936596a1cdcba1afcb50e6e5c35965a87372e5aca87401b974365a121cdcbb2b2cb5b06e5c1d965a87372d965a94439b97436596a68dcbb6b2cb5986e5d0d965a97372e865add621b97436596a1ce0ba196b350e6e5
  | 4, 0, 6 => 0xd0d965a87352e872f2d439b97436596b5cdcba1b2cc10e6e5d0d9a5a87372e86cb2d439897356596a1cdcba196c2d0e6e5d0c2e0c87372e86cb2d609b974365969ecdcba1b2cb5326e5d0d965aca372e865a873d1897196596a1cdcbbddcd965ad85
  | 4, 0, 7 => 0xcad965a87372e7acb2d439b96cb2d439b89aba1b2cb5186e5d0d8e5a87372eaacb2d439b97736596a1cd0b6596b50f46e5dcd965ad6372efacb2d439b9743659621cdcb7fb2cb50e6e5cacb50e7a372d96b32d421b97476596a1cdcba1b2c19306e5
  | 4, 0, 8 => 0xdce5aca87372d665a803d1b96cad46321cdcba1cccb5086e5d0dda5a87372e86cb2d370fd7436596b58dcba196a1cdc1f5b2cb5a887372e86cb35439b9743999021cdcbb6b2cb50e6e5d0d965a8731ad965ad5439957956596a10dcba1b2cb59e875
  | 4, 0, 9 => 0xd0d965ac843ae86cb2d6a9e97156596a1cdcb2d713790e6e5ce5965a87372e86cb49439b972d6592a1cdcba1cb21cf46e5be5965a87372e86cb2d479b97456596a1cdcba1b2ca10e6e5d0d965a7e372f22cb2d439b97656596a1cdcba1b2cb4fa6e5
  | 4, 0, 10 => 0xb2cb50e6e11af2732f75b9b97435c96a1cdcba1b64b50e6e5d0d765a87372e86cb31439b96cb2d68a1cdcb93b2cb50e6e5d0d967487372e86cb2d431b97436596a34dcba196b599a6e5d0d965a8736ae86ef2d661b974396b2a1cdcba1bacb50e6e5
  | 4, 0, 11 => 0xe565e5a87372e86b72d6c1b97436591a1cdcba1b2cb50e315cbe565a87372f2acb26439b975b6596a1cdcbb6b2cb5826e5d8d965a87372e86cb2d6aa1d7436596b60b6ba1cc4b50e6e5cad965a87312e5eb32d439b97432d8da1cdcb5b96a1d006e5
  | 4, 0, 12 => 0x6869d2d439b97436566318dcba1b2cb4fc625d0b398c87372e872f2d3e9b97436596a14dcb6596a1cdc4a5d0df65a87372ec2cb2d439b97436596b30dcba5b2cb50e6e5d0dca5a87372e865ace439b974365969b87cba196a4d0e6e5
  | 5, 0, 0 => 0xd0d965afa5b9b9b436596a1cdc2f6d0d965af05b9b9b436596c590e6e6e6e86cb2d439b9801a1bbcb50e6e5d0d665aec439b9b436596bddb66e6d0d965a8737115b436596a6cdc566d0d965a9c439b9b4396b2d650e6e6e565e5af75b9b9b436596af90e6e6d0d958cb7439b9b436596a1cdc536
  | 5, 0, 1 => 0xd0d965ae7439b9b436596bd9086e6d0e4acb2d439b9b9dcab2cb50e6e6d0d965afb439b9b436596b71826e6d0d965ac35b9b9b4365a54b50e6e6d0d965a9d439b9b436596a1cdc486d0d965a8737175b436596bbd6e6e6d0d968f2d439b9b4fa1b2cb50e6e6d0d96af2d439b9b236596bdd6e6e6
  | 5, 0, 2 => 0xd0d965b25439b9b436596bc90e6e6d0d96692d439b9b42f76f3696e6e6d0d965a8737005b43656d2dd0e6e6d0d965af75d1b9b436596b650e6e6b2d665a87401b9b436596a1cfc6e6d0d965a8737089b436596bdd246e6e55965aad439b9ba3a1b2cb50e6e6d0d965af74b1b9b432d7bb396e6e6
  | 5, 0, 3 => 0xd0d965a87370f1b436596a550e6e6b2cb5eeb737129b436596bc50e6e6d5d965af75b9b9b436596a64dc656d0d965aec439b9b436596a1d046e6d0d965ad0439b9b436596bd90e6e6d0d965a8737141b436596a1cdc4e6d0d96732d439b9b436596a1cdc4b6d0d965a87370d5b4b6596bdd6e6e6
  | 5, 0, 4 => 0xd0d965af85b9b9b436596bdd6e6b6d0d965b045b9b98016596b890e6e5d0d96a12d439b9b436596bb50e6e6d0d95cada439b9b99a1b2cb50e6e6e56873365439b9b43a1b2cb50e6e6c35965af7439b9b436596a1cdc686d0d7a5af75b9b9b436596a1cdc446d0d965ae85b9b9b436596a1cdc616
  | 5, 0, 5 => 0xd0d965af7501b9b437796bdd6e6e6d0d965b09439b9b43654f21cdc5a6d0daa5af75b9b9b436fb2cb50e6e6d0d965ad837149b8fa1b2cb50e6e6d0d96892d439b9b436596bdd546e6e55965a87401b9b436596a1cdc036d0d965ac9439b9b4388b2cb50e6e6e7687332d439b9b4365ae4b50e6e6
  | 5, 0, 6 => 0xd0d960cf74d9b9b436596b790e6e6d0d965b29439b9b432d7ebdd6e6e6d0d9634f75b9b9b536596bdd6e6e6d0d96972d439b9b436596bdd826e6d0d965ad83d1b9b436596bddb86e6d0d96a52d439b9b43659e4b50e6e6d0d965abd439b9b436596bdd326e6d7e86cb2d439b9b436596c0d6e6e6
  | 5, 0, 7 => 0xd0d965a87370a5b4365953dd6e6e6d0de2cb2d439b9b436596c610e6e6d0cb5eeec5b989b432d85bdd0e6e6d0e26cb2d439b9b0d6596add0e6e6d0d965b104c9b9b4365ac4b50e6e6d0d965a873702db436596bdd366e6d0d965af7581b9b8da1b2cb50e6e6d0d96772d439b9b436596ba90e6e6
  | 5, 0, 8 => 0xdde86cb2d439b9b439796bdd0e6e6d0d965a8737151b436596adcdc426d0d965a87391b9acb2d7baed6e6e6c863acb2d439b9801a1b2cb5086e5d0cb5eedd5b9b9b43659bcb50e6e6d0e52cb2d439b9b436596bdd586e6d0d965af55b9b9b436596bdd0e626d0d965af74f9b9b438496bdd6e6e6
  | 5, 0, 9 => 0xd0d965b0d439b9b4380b2cb50e6e6d0d965aee5b9b9b7bb9b2cb50e6e6d0d465af75b9b9801a1adcb50e6e5d0d965a8737019b436596a1cdc006d0d965af74c1b9b432d7bb91ba6e6d0d96a72d439b9b436596bdd886e600686cb2d439b96cb2d873dd0e6e600686cb06439b97436596bdd5e6e6
  | 5, 0, 10 => 0xd0d965a8737199b436596bfd6e6e6d0d965b21439b9b43657bb71b46e6d0cb616b7439b9b436596bddc26e6d0d965ace439b9acb5696bdd6e6e6bfd965af7439b9b436496bdd6e6e6d0d965ad8439b9b4365994b50e6e6d0d967d2d439b9b1d6596bdd4e6e6b2cb5eee25b9b9b436596c1d0e6e6
  | 5, 0, 11 => 0xd3686cb2d439b9b2b6596bdd0e6e6d0d965ad637195b43659b4b50e6e6d0d965af75b991b2b2d7bbb16e6e6d0d965af75a1b9b436596c490e6e6cb656caf75b9b9b436596cad0e6e6d0d965a8737065b4399b2cb50e626b2cb5eee4711b9acb2d8e3dd6e6e6d0d965a873717d801a1b2b190e6e5
  | 5, 0, 12 => 0xd0d965acc37169b69a1b2cb50e6e6d0d95eeb737051b436596a1cdc156d0d965ae95b9b9b436596c5d0e6e6d0deecb2d439b9b436596a1cdc576d0d95b0c6439b9b7b6596bc90e6e6d0d965af9439b9b436596a1cdc076b2cb61cb7439b9b436596bdd706e6d0d965a87370b18016596a1cdc0b5
  | 5, 0, 13 => 0xd0d965aa7439b9b436596afd0e6e6d0d965aeb5b9b9b7ba1b2cb50e6e6db5965af7439b9b436596a1cdc096dad965af75b9b9b4386b2cb50e6e6e46665af75b9b9b436596a1cdc206d0d965a8737145b436296bdd6e6e6d0d965a87399b9b436596b990e6e6d0d965af75c9b9b436596aa8fc6e6
  | 5, 0, 14 => 0xd0d965a8737165acb2d7bb510e6e6d0ddecb2d439b9b436596bf96e6e6d0d965af75b9b9b436596a1cdc4c6b2bddc4da5b9b9b436596bd1ca6e6d0d960cf75b9b9b439796bc16e6e6d0d965ad5439b9b7ba1adcb50e6e6d0d965acc439b9b436596bc5546e6d0dfacb2d439b9b436596a1cdc0d6
  | 5, 0, 15 => 0xe8686cb2d439b9b4365a1cb50e6e6cce56cb2d439b9b432d7badcdc496d0d965a87370adb437796a1cdc5a6d0d965a8737039b436596c416e6e6d0d965b115b9b9b436596bb1366e6d0d965af76b1b9b436596c810e6e6d0d965a8737101b435b96bdd6e6e6d0d965ac5439b9b436596adcdc416
  | 5, 1, 0 => 0xd0dde5b095b9b9b4365969e8ee6e6d0d965a8b439b9b436596c41c86e6d0d965ad543a01b436b96bdd6e6e6d0d96b52d439b9b432d7621cdc5e6d0d95eec65b9b9b436596bdd646e6d0d96812d439b9b436596a1cdc2d6d0e5e5b25439b9b7365accb50e6e6d0dd2cb2d439b9acb2d7bb816e6e6
  | 5, 1, 1 => 0xd0d965af75518980186b2cb50e6e5e45965af7439b9b432d6f3156e6e6d0d965b0e439b9acb2d7bb89446e6d95965af7439b9b439fb2cb50e6e6d0d965b0f439b9acb2d56a1cdc656d0d965afc5b9b9b436596cb50e6e6d0d9648f75b9b9b436596c190e6e6d0d965b096e1b9b436596a1cdc5c6
  | 5, 1, 2 => 0xd0db6cb2d439b9b436596a1cdc086d0d965ab1439b9acb5996c950e6e6b2d665af2439b9b435996a1cf46e6d0dde5af75b989b436596bdd566e6d0d965a87389b9b436596bdcfc6e6accb5e4ec5b9b9b436596a1cdc3a6d0d969b2d629b9b436596c096e6e6d0d965b085b9b9b436596a1cdc056
  | 5, 1, 3 => 0xd0e0acb2d439b9b2d657badd5a6e6d0d965b015b9b9b436596a1cdc1d6d0d965af7599b9b436596bdd506e6e765acaf75b9b9b437fb2cb50e6e6b85965af75b9b9b436596a1cea6e6d0d965b22439b9b436596b190e6e600686ca87370857436596a1cdc0f6d0d965b1d439b9b95b9b2cb50e6e6
  | 5, 1, 4 => 0xb2cb61cf74d9b9acb2d43a00dc656d0d965a873b9b9b436596a1cec6e6d0d965a8737149b439996c7d0e6e6d0d96712d439b9801a1b2cb5826e500686cb2d439197436596a1cdc3d6d0d7a5b125b9b9b676596bdd6e6e600686cb2d4c9b974365accb50e6e6d0d965a8737091b83a1ae4b50e6e6
  | 5, 1, 5 => 0xd0d96a92d439b9b436596bdd6e70600686cb2d43989785a1b2cb50e6e6e55965b25439b9b436096bdd6e6e6d0e5acaf7439b9b916596c7d0e6e6006865b0b439b97436596bdd466e6d0d965a873d1b9b43967bbb16e6e6d0d965a8737099b4395b2cb50e6e6d0d965af75b1b9b9dcaccbdd6e6e6
  | 5, 1, 6 => 0xd0d96cb2d439b9b6da1b2cb50e6e6d0d965af75e9b9b436596bdd1c6e6cad965af7551b9b436596c49406e6d0d960cec5b9b9801a1cbcb50e6e5005950e6e1082d74365a44b50e6e6d0d965abc439b9b438db2cb50e6e6c1d965af75b9b9b4399b2cb4fc6e6d0e3ecb2d439b9b436596a1cdc186
  | 5, 1, 7 => 0xd0d965af7531b9b436596a1d086e6e4d965af75b9b9b4365974b50e6e6d0cb6250b439b9b436596a1cdc5a6d0d965ad4439b9b435f96bdd6e6e6d0d725af7439b98016596a1c8c0b5c35965af75b9b9b436596a1cdc106d0d96b72d439b9b95a1b2cb50e6e6d0d965a873e1b9801a1b2cb4dc395
  | 5, 1, 8 => 0xd0d965a873c9b9b436596a1cdc116d0e665aec439b9acb2d894390e6e6d0d965a87439b9b436596bdd6a6e6d0d965af76aa1db6d6596bddb86e6e9e86cb2d439b9b436596a1cdc6c6d0e76cb2d439b9b436596bdd4a6e6d0d965a8737095b6d7796bdd6e6e6005fecb2d439b9759a1b2cb50e6e6
  | 5, 1, 9 => 0xe0e86cb2d629b9b4365983dd6e6e6d0d9a5af75b9b9b91a1b2cb50e6e6d9686cb2d439b9b4365439dcdc5a6d0d965af75b989b436596c016e6e6cd5965af75b9b9b435c96add0e6e6d0cb616f75b9b9b436596a1cdc3b6dce86cb2d6c21d80165969b8720b500656cb2d439b97436596bdd146e6
  | 5, 1, 10 => 0xd0d965a8737029b4365a6cb50e6e600686cb2d6b1b97476596bdd6e6e6d0d965b26439b98016596b510e6e5d0d965a873705db9da1b2cb5086e6d0d965a87370ddb436596a1cdc366d0d965af6599b9b436596a1cdc216d0e5e5af75b9b9b436599cb50e6e6006dacb2d439b97436596a1cdc276
  | 5, 1, 11 => 0xd0d965a873a1b9b736596bdd6e686b2cb5b0d4439b9b436596c550e6e6df5965af75b9b9b4365963dd6e6e6bfd965af75b9b9b436596a1cbc5a6d0d967f2d439b9b87a1b2cb50e6e6e7686cb2d439b9b432d7bb390e6e6e5e86cb2d439b9b436596a1cdc5b6d0d965a8737155b436596a00f46e6
  | 5, 1, 12 => 0x686cb2d3f1b979fa1b2cb50e6e600722cb2d439b9401b2b2cb50e6e5e2e86cb2d439b9b436596bcd0e6e6d0d965aa1439b9b436596bdd5c6e6cad965af75b9b9b3d6596bdd6e6e6006865a873705974369b2cb50e6e600686ca87230857436596a1cdc1e6d0d965a87371b9b436596bdd986e6
  | 5, 1, 13 => 0x4b50e6e0b02d7436596a1cdc306b2cb5eed45b9b9b4399903dd6e6e6d0d965b13439b9b5da1b2cb50e6e6d0d965a91439b9b436596a1cdc0c600686ca6e1c885779a1b2cb50e6e6db5965af75b9b9b437796bdd0e6e6d0de6cb2d439b9b436596a1d006e6d0d965a873706db4365a3cb5b06e6
  | 5, 1, 14 => 0xd0d965a8737179acb5996bdd666e6d0d965a873713db057fb2cb50e6e6006872d65439b97436596b04dc5a6d0d965b14439b9b437696bdd6e6e6d0e6ecb2d439b9b436596a1cdc566d0e66f72d439b9801a1b2cb48c395d0cb50e7a37179b736596a1cdc656d0d965a87370a9b432d7badcdc1f6
  | 5, 1, 15 => 0xd0d965a8737071b436596b7d0e6e6d0d968d2d439b9b436596a1cde6e6e0686cb2d439b9801a1ae4b50e6e5e45965af75b9b9b656596bdd6e6e6d0e2ecb2d439b9b4365b0cb50e6e6d0d965a8737049b4368b2cb50e6e6dce5acaf75b9b9b4397b2cb50e6e6d0d965b27439b9b437ab2cb50e6e6
  | 5, 2, 0 => 0xd0d965a87370cdb436596a1cdc026d0d965a873704db4365a4bdd6e6e6d0d965ad3439b9b2d6592bdd6e6e6d0d965a87370e5801a1b2cb5aa875d15965af75b9b9b436596a1cdc676d0d965aaf439b9b956596bdd666e6d0d965f2d439b9b436596a1cdc656e9686cb2d439b9b4371b2cb50e6e6
  | 5, 2, 1 => 0xd0d965a8737119b435b96bdd0e6e6d0d965a87370b9b436596a1cdc1a6d0d965a8737161b436596bdd0e6e6006850e6e108597436596bdd6e6d6d0d96832d439b9b4381b2cb50e6e6dc686cb2d439b9b4396b2bdd6e6e6d0d725af45b9b9b437596bdd6e6e6d0d965af7421b9a5af7713796e6e6
  | 5, 2, 2 => 0xd0d965a8737011b656596a1cdc526d0e665a873d1b9b436596a1cdc476b2cb5eeb73708db436596a1cdc626006865ace439b974373b2cb50e6e6d0d965a87370e1801a196a1c8c165db5965a8737169b7b6596a1d006e6d0d965b10439b9b276596bdd6e6e6d0d9674f75b9b9b439996bdd666e6
  | 5, 2, 3 => 0xd0d967b2d439b9b436596c7d0e6e6d0d965b1e439b9b2f9596bdd6e6e6e55964cf75b9b9b436596bddaab76d0d960cb7439b9b432d6c3390e6e600686cb2d661b97439896bdd6e6e6d0e5acb2d439b9b2b6596bdd6e626d0d965a873c1b9b2f5996bdd6e6e6d0d965a87409b9b432d8dbdd6e6e6
  | 5, 2, 4 => 0xd0d968b2d439b9b73a1b2cb50e6e6d0d965a873710db9d65accb50e6e6d0d965b19439b9b7ba1b2cb5b06e6006865a6e1c8597436596b590e6e6d0e66cb2d439b9b436596a1cdc166
  | 6, 0, 0 => 0x6865af75b9182cdb6b2cb5eeb737169f436596c41eeb7373e86cb2d7baf4dc2a7005965ab7439b816da1b2d325af75b9b9c01a1b2cb5deb73735965af772b896e6e700686cb4796a1cdcda1b2cb5eeb737119f436596c496e87373e86cb2d7badcdc1a7d0d965af75b9b8b0fa1b2cb5eef75b9b9c01a17badcdc210b3686cb2d7bb8d6e6e7
  | 6, 0, 1 => 0xd0d965b1f7badcdcfa1b2cb63cf75b9b9f7fa1b2cb5eeb7373803436596bb10e6e6d0e5acb2d7badcdcfbdd0d965ab7439b9c01a1b2cb64a87373003436596bc90e6e6d0e42cb2d7ba9cdcfa1b2cb5eeb73711dc01a1b2cb4dc34153686cb2d7badcdc287d0d965ae65ba1cdcfa1b2cb5eeb737189f43a0b2cb5eeb7373e86f76596add0e6e7
  | 6, 0, 2 => 0xd0d965af7712dcdcfa1c3d965af75b9b9f89a1b2cb5eeb7373e86cb2d82bdd6e6e7d0d965af75ba78dcf65accb5eeb7569b9f436596bdd6e6e21be86cb2d863dd6e6e7e7596b32d7badcdcfa1b2cb632f75b9b9f436596bdd6ea4373e86cb2d7badcdc607d0e66cb2d7badcdcfa1b2cb5eeb737059c01a1af4b5eeb7373686cb3d96bdd6e6e7
  | 6, 0, 3 => 0xd0d965b167badcdcfa1c15965af7439b9f9ba1b2cb5eeb7373803436596bdd406e600686ef2d7badcdcda1accb5eeec5b9b9f436596bdd6e6e22be86cb2d7badd386e7d0e5acb597badcdcfa1b2cb5eeb73714dc01a1b2cb5eeaa373686cb2d7bb956e6e7d0e16cb2d7badcdcfb9d0d965af75b9b9f4365aacb624b737380343657ba1cdc216
  | 6, 0, 4 => 0x686cb2d5b9b854da1b2cb5f6f75b9b9c01a1b2cb5ee9b373686cb4a96bdd6e6e7d0d965af75ba74dcfa1b2cb5eeb737121f436596bdd6e6e2ebe86cb2d7ba1cee6e7d0d965af7439b8a4fa1b2d1e5af75b9b9c01a1b2cb5ee87233003436596bddb86e6d3e86cb2d7badcdcfa1b2d5e5af75b9b9f4365accb5ee87373e86cb2d7badcdc2f7
  | 6, 0, 5 => 0xd0d965af75b9b896fa1b2cb5eeb7370d5f436596c95eeb7373e86cb2d7bbc96e6e7d0d96692d7badcdcfa1b2cb5eeb737005f436596bdd6e6e113f2acb2d7badd5a6e7e8e86cb2d7badcdcfa1b2cb5eee75b9b9f4392b2cb5eeb73738034389b2cb50e6e6d0d965af7439e8dcfcee55965af75b9b9f8ba1b2cb624b7373803436596a1cdc0b6
  | 6, 0, 6 => 0xd0d965af7439b8b4fa1b2bddcada5b9b9f95a1ccd95eeb7373e87436596bdd6e6e7d0d965b127ba6cdcfa1b2cb5eeb7371a1c01a1b2cb5ee6e193686cb2d7badcdc447e5686cb2d7ba1cdce00d0d965af7370e580000d0d965a87372e86cb2d7bbc56e6e700686cb2d7babcdcda1b2cb5eeec5b9b9f436596bddecb7373e86cb3996bdd6e6e7
  | 6, 0, 7 => 0xd0d96792d7badcdcfa1b2cb5eebd5b9b9f5fa1b2cb5eeb7373803436596c490e6e6d0d965b097badcdcfa1b2cb5ee87439b9f43657badd3c6e2d3f1f436596bdd6e6e7d0d965af75b9b806fa1c45965af75b9b9f9da1cccb5eeb7373e86cb5c96bdd6e6e700686cb2d6c21cdcc00b2cb56e6e1502db436596c496e6e2b3802cb2d7bb896e6e6
  | 6, 0, 8 => 0x686cb2d7321cdcda1b2cb5eea24f1b9f436596c61eeb7373e87136596bdd6e6e7d0d96b12d7badcdcfa1b2cb5eeb73702df4399b2cb5e2b7373803437bb2cb50e6e6e3686cb2d7badcdcfa1b2cee5af75b9b9f436596bddd4b7373e86cb2d7bb796e6e7d0d965b297badcdce00005965a873702d74365a5cb5eeb7373e86cb5296bdd6e6e7
  | 6, 0, 9 => 0xd0d969b2d7ba1cdcfa1b2cb5eeb737019f436596bdd6e6e003803436596bdd6e6e600686cb067badcdcda1c85965af7439b9f436596bdd0e6e10be86cb2d7badcdc547006f7436596a1cdcda1b2cb5eeb7391b9f436596bddcaa2373e431d6596bdd6e6e7d0d966f2d7badcdcfa1ca5965af75b9b9f436596bdd6e6e14be86f16596bdd6e6e7
  | 6, 0, 10 => 0xd0e42cb2d5ba1cdce00d0cb5ee8737059b436596cadeeb7373e87336596bdd6e627d0d965af2762dcdcfa1b2d565af7439b9f436596bddb0b7373e86cb3296bdd6e6e7d0d965af756a1cdcfa1b2cfa5af75b9b9f43659fcb5ee87373e86cb2d83bdd6e6e700686cb2d882dcdcda1b2cb61af75b9b9f9da1b2cb5ee87373803436596af4dc2a6
  | 6, 0, 11 => 0xd0d965af743a00dce00d0d965ab7230a9b4386b2cb5eeb7373e86cb2d7badcdc207d0d965af75b9ccdcfb4d0d965af75b9b9f436596bdd6e6e0abe86cb2d8bbdd6e6e7e2e86cb2d7ba1cdcfa1bdd965af75b9b9f436596bdd6e6e2bbe86cb2d7cbdd6e6e700686cab7370a842da1b2cb5eeb7370b1c016596bdd6e6e05b69b436596bdd6e6e7
  | 6, 0, 12 => 0x686cb5996a1cdcda1b2cb640f75b9b9f436596bdd6e6e203e86cb2d7bb156e6e700687056596a1cdcda1b2cb5eeb737165c01a1b2cb5eeb3373686ef6596bdd6e6e7d0d965af75b9b898e0000686ca87370857436596bdd6e6e06be86cb2d7badd4e6e7d0d965af75fadcdcfbdd0d965af75b9b9f436596bdd6e6e04be86cb2d5bab50e6e7
  | 6, 0, 13 => 0xd0cb5eeec5b9b8bcfa1b2cb5eeb7370b5f439796c95eeb7373ee6cb5996bdd6e6e7d0dd2cb2d7badcdce00d0d965a873d1b9b436596bddb86e2d3f17436596add0e6e7cce56cb2d7badcdcfa1b2cb5eeb7370adf437796bdd6e6e2d3e86cb2d7ba1cdc56700686cb2d439dcdcc00d0d965a873714980000d0d965a87232e86cb2d7ba1cdc2a7
  | 6, 0, 14 => 0xb2d665b257badcdcfa1b2cb56e8737159f436596bdd6e71373803436596a1cdc5a6d0d965af75b9b80ae00c35965af75b9b9b436596add0e6e15380395a1b2cb50e6e6000034365969b872b6596bdd6ead37195f436596cb5eeb7373e86cb2d833dd6e6e700686cb2d7baf4dcda1b2cb5eeb737171f436596bdd0e6e2f3e86cb5a96bdd6e6e7
  | 6, 0, 15 => 0xd0d96b32d7badcdcfa1b2cb5eeb737091f83a1ae4b5eeb7373e87056596bdd6e6e7d0d965af75b9b83afa1b2cb5ee87370e5c01a1b2cb50e87373686cb2d913dd6e6e700686caf75b9b842da1b2cb5eeb73703df436596c75eeb7373e86cb2d7ba1cdc657e56e6cb2d7badcdcfa1b6d965af75b9b9f436596bdd6e6e043e86cb2d7badd626e7
  | 6, 1, 0 => 0xd0d965af77ba1cdcfa1b2cb5eeb737061f4365aa4b5eeb7373803436596bdd6e626e55965b257badcdcfc8b2cb63ef75b9b9f4365aacb5eea0373803432d85bdd6e6e6d0d965af75b9e8dcfa1b2cb5eeb737099f4395b2cb5eeb7373e86cb2d7badcee6e7d0d965af75b9b8a4fa1cccb63ef75b9b9f43659c4b5eeb7373803436596bdd6e466
  | 6, 1, 1 => 0x6865ab7370a82cda1b2cba5af75b9b9f432d8942deeb7373e86cb2d7badcdc5a7005965af75b91816c00d0d969b2d439b9b436596bdd6e6e083f2b436596bdd6e6e7d0d96cb2d7badcdcfb6d0d965af75b9b9f436596bdd0e6e233803436596a1cdc216006872f2d7badcdcc00b2bdd6e6e1082db4365a44b5eeb7373e86cb2d7baf16e6e7
  | 6, 1, 2 => 0x717436596a1cdcdc5d0d965af7579b9f436596c65ee873738032b6596bdd6e6e600003432d439b82cba1ccd965af7439b9f436596bdd0e6e0b3e86cb2d8fbdd0e6e7d0e665af7762dcdcfa1b2cb5eeb7439b9fa7a1b2cb5eeb7373e86cb2d7badcdc6c7d0d965af75b9b84afacd0d965af75b9b9c01a1b2cfe5a873730039da1b2cb50e6e6
  | 6, 1, 3 => 0x686cb2d439b8acdced0d965af75b9b9f97a1b2cb5eeb7373e86cb2d7badcdc55700686cb2d439b854da1b2cb5eeb737029f4365a6cb5eeb7373e86cb2d933dd6e6e7d0d965af75b9b82efa1b2d1e5af7439b9f436596bdd6e6e10b8036d6596bdd6e6e6d0d965af75b9b84ee00d0d965a87401b9b91a1b2cb5eeb7373ee7436596bdd0e6e7
  | 6, 1, 4 => 0xe2e86cb2d7badcdcfa1b2cb5eef35b9b9f436596bdd6ea1373803432d7badcdc166d0da6cb2d7badcdce00d0d95eeb723085b436596bdd6e6e0f3803436596a1cdc5e6d0d965af75b9b8dcfa1b2cb5cab7439b9f436596bddd887373e86cb2d8abdd6e6e7d0d965ab74f21cdcfa1b2cb64af7439b9f436596bdd6e5e2d3e86cb3f96bdd6e6e7
  | 6, 1, 5 => 0xd0d965af75b9b8acfa1ccdee5af75b9b9f736596bdd6e6e32be86cb2d7ba1cdc0b7d0d965af75b9b854e0096bdd6e6e0b02d801a1b2cb50e6e1cb686cb2d89bdd6e6e7d0d965af75b9b818fa1b2cb5eea2439b9c01a1b2cb50e6e32b686f36596bdd6e6e7d0d965af75ba00dcfa1b2cb5eeb73706df9fa1b2cb5eeb7373803916596bdd6e6e6
  | 6, 1, 6 => 0xe9686cb2d7badcdcfa1b8d965af75b9b9f436596bdd6e6f373e86cb2d7bb610e6e7d0d96c32d7badcdcfa1b2cb5eeb737049f4368b2cb5eeb7373803436596a1cdc466d0e5ecb2d7badcdcfa1bd5965af75b9b9f436596bdd6e6e2f3803436596bdd0e6e6006872d657badcdcda1b2cb628f75b9b9f439bb2cb5eeb7373f3b436596bdd666e7
  | 6, 1, 7 => 0x371a1b2cb5eeb737380373a1b2cb50e6e600686cb2d8ca1cdcda1b2cb5eeb737009f436596bdd6e6e09b8034399b2cb50e6e600686cb2d439b82cda1b2cb620b737195c01a1b2cb63e87373686cb2d7badcdc397d0d965af75b9b8cefa1b2cb5eeb7579b9f436597cb5eeb7373e86cb2d7badcdc657
  | 7, 0, 0 => 0x3436596bdd6e6e600687136596bdd6e6e700686cb2d7badcdc0b70000001a1b2cb50e6e500686cb2d7bbb16e6e700686cb2d92bdd6e6e700686cb2d7bbc96e6e700003436596adcdc2a600686cb2d7bb956e6e7006e7436596bdd6e6e700686cb2d7badd3c6e700686cb2d8cbdd6e6e700687336596bdd6e6e700686cb2d7badcdc16700686cb2d8fbdd6e6e700686cb2d7badcdc467
  | 7, 0, 1 => 0x686cb2d7badcdc56700686cb2d7badcdc2a700717436596bdd6e6e700003432d7badcdc16600686cb3f96bdd6e6e70073b436596bdd6e6e700686cb4d96bdd6e6e700686cb2d7badcdc21700686cb2d7badd0e6e700686cb2d7badcdc5a70072b436596bdd6e6e700003436596bdd6e46600686cb5996bdd6e6e70000343657badcdc21600686f76596bdd6e6e700002cb2d7badcdc0b6
  | 7, 0, 2 => 0x686cb2d7badcdc65700686cb2d7badcdc5e700003436596bdd0e6e6
  | 8, 0, 0 => 0x3436596bdd6e6e6
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

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]

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
private theorem z2_0 : span (Z 2) 3 0 = true := by decide +kernel

private theorem z2 : span (Z 2) 3 0 = true := z2_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : span (Z 3) 18 0 = true := by decide +kernel

private theorem z3 : span (Z 3) 18 0 = true := z3_0

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
private theorem z4_192 : span (Z 4) 15 192 = true := by decide +kernel

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

private theorem z4_a8 : span (Z 4) 207 0 = true :=
  span_join (f := Z 4) (a := 192) (o := 0) (b := 15) z4_a7 z4_192

private theorem z4 : span (Z 4) 207 0 = true := z4_a8

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
private theorem z5_576 : span (Z 5) 10 576 = true := by decide +kernel

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

private theorem z5_a24 : span (Z 5) 586 0 = true :=
  span_join (f := Z 5) (a := 576) (o := 0) (b := 10) z5_a23 z5_576

private theorem z5 : span (Z 5) 586 0 = true := z5_a24

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
private theorem z6_360 : span (Z 6) 22 360 = true := by decide +kernel

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

private theorem z6_a15 : span (Z 6) 382 0 = true :=
  span_join (f := Z 6) (a := 360) (o := 0) (b := 22) z6_a14 z6_360

private theorem z6 : span (Z 6) 382 0 = true := z6_a15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : span (Z 7) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_24 : span (Z 7) 11 24 = true := by decide +kernel

private theorem z7_a1 : span (Z 7) 35 0 = true :=
  span_join (f := Z 7) (a := 24) (o := 0) (b := 11) z7_0 z7_24

private theorem z7 : span (Z 7) 35 0 = true := z7_a1

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

def CG : Circuit := ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 8]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [6, 10]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.and, [12, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12463

theorem PEqualNP.Outside.L_meta_12463 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941263872 * 2 ^ 32 + 3934300672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941263872 * 2 ^ 32 + 3934300672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12463.mainG PEqualNP.Outside.L_meta_12463.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12463.CG, PEqualNP.Outside.L_meta_12463.CG_mono, by
      have : PEqualNP.Outside.L_meta_12463.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12463.CG_eval⟩
