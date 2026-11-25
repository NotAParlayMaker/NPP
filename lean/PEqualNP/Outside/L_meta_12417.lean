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
namespace PEqualNP.Outside.L_meta_12417

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (3941132288 * 2 ^ 32 + 3892373504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 13, 14, 15, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 27, 11, 29, 30, 31, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 43, 11, 45, 46, 47, 11, 11, 11, 51, 11, 53, 54, 55, 11, 57, 11, 59, 11, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 11, 13, 13, 14, 15, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 27, 13, 29, 30, 31, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 43, 13, 45, 46, 47, 13, 13, 13, 51, 13, 53, 54, 55, 13, 57, 13, 59, 13, 61, 62, 63, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 11, 14, 13, 14, 15, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 27, 14, 29, 30, 31, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 43, 14, 45, 46, 47, 14, 14, 14, 51, 14, 53, 54, 55, 14, 57, 14, 59, 14, 61, 62, 63, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 11, 15, 13, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 27, 15, 29, 30, 31, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 43, 15, 45, 46, 47, 15, 15, 15, 51, 15, 53, 54, 55, 15, 57, 15, 59, 15, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 11, 27, 13, 14, 15, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 29, 30, 31, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 43, 27, 45, 46, 47, 27, 27, 27, 51, 27, 53, 54, 55, 27, 57, 27, 59, 27, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 11, 29, 13, 14, 15, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 27, 29, 29, 30, 31, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 43, 29, 45, 46, 47, 29, 29, 29, 51, 29, 53, 54, 55, 29, 57, 29, 59, 29, 61, 62, 63, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 11, 30, 13, 14, 15, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 27, 30, 29, 30, 31, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 43, 30, 45, 46, 47, 30, 30, 30, 51, 30, 53, 54, 55, 30, 57, 30, 59, 30, 61, 62, 63, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 11, 31, 13, 14, 15, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 27, 31, 29, 30, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 43, 31, 45, 46, 47, 31, 31, 31, 51, 31, 53, 54, 55, 31, 57, 31, 59, 31, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 11, 43, 13, 14, 15, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 27, 43, 29, 30, 31, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 45, 46, 47, 43, 43, 43, 51, 43, 53, 54, 55, 43, 57, 43, 59, 43, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 11, 45, 13, 14, 15, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 27, 45, 29, 30, 31, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 43, 45, 45, 46, 47, 45, 45, 45, 51, 45, 53, 54, 55, 45, 57, 45, 59, 45, 61, 62, 63, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 11, 46, 13, 14, 15, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 27, 46, 29, 30, 31, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 43, 46, 45, 46, 47, 46, 46, 46, 51, 46, 53, 54, 55, 46, 57, 46, 59, 46, 61, 62, 63, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 11, 47, 13, 14, 15, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 27, 47, 29, 30, 31, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 43, 47, 45, 46, 47, 47, 47, 47, 51, 47, 53, 54, 55, 47, 57, 47, 59, 47, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 11, 51, 13, 14, 15, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 27, 51, 29, 30, 31, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 43, 51, 45, 46, 47, 51, 51, 51, 51, 51, 53, 54, 55, 51, 57, 51, 59, 51, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 11, 53, 13, 14, 15, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 27, 53, 29, 30, 31, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 43, 53, 45, 46, 47, 53, 53, 53, 51, 53, 53, 54, 55, 53, 57, 53, 59, 53, 61, 62, 63, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 11, 54, 13, 14, 15, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 27, 54, 29, 30, 31, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 43, 54, 45, 46, 47, 54, 54, 54, 51, 54, 53, 54, 55, 54, 57, 54, 59, 54, 61, 62, 63, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 11, 55, 13, 14, 15, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 27, 55, 29, 30, 31, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 43, 55, 45, 46, 47, 55, 55, 55, 51, 55, 53, 54, 55, 55, 57, 55, 59, 55, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 11, 57, 13, 14, 15, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 27, 57, 29, 30, 31, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 43, 57, 45, 46, 47, 57, 57, 57, 51, 57, 53, 54, 55, 57, 57, 57, 59, 57, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 11, 59, 13, 14, 15, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 27, 59, 29, 30, 31, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 43, 59, 45, 46, 47, 59, 59, 59, 51, 59, 53, 54, 55, 59, 57, 59, 59, 59, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 11, 61, 13, 14, 15, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 27, 61, 29, 30, 31, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 43, 61, 45, 46, 47, 61, 61, 61, 51, 61, 53, 54, 55, 61, 57, 61, 59, 61, 61, 62, 63, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 11, 62, 13, 14, 15, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 27, 62, 29, 30, 31, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 43, 62, 45, 46, 47, 62, 62, 62, 51, 62, 53, 54, 55, 62, 57, 62, 59, 62, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff0000000000000000151717ff17ff17ff0000000000000000151717ff17ff17ff0000000000000000151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff0000000000000000151717ff17ff17ff000000000000000000000000000000000000000000000000151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff0000000000000000151717ff17ff17ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff0000000000000000151717ff17ff17ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff0000000000000000151717ff17ff17ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeae8e800e800e800eae8e800e800e800eae8e800e800e8000000000000000000eae8e800e800e8000000000000000000eae8e800e800e8000000000000000000eae8e800e800e800eae8e800e800e800eae8e800e800e8000000000000000000eae8e800e800e800000000000000000000000000000000000000000000000000eae8e800e800e800eae8e800e800e800eae8e800e800e8000000000000000000eae8e800e800e80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000eae8e800e800e800eae8e800e800e800eae8e800e800e8000000000000000000eae8e800e800e80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000eae8e800e800e800eae8e800e800e800eae8e800e800e8000000000000000000eae8e800e800e80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800eae8e800e800e800

def cMZZ : Nat := 0x151717ff17ff17ff0000000000000000151717ff17ff17ff0000000000000000151717ff17ff17ff000000000000000000000000000000000000000000000000151717ff17ff17ff0000000000000000151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff000000000000000000000000000000000000000000000000151717ff17ff17ff0000000000000000151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff000000000000000000000000000000000000000000000000151717ff17ff17ff0000000000000000151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff000000000000000000000000000000000000000000000000151717ff17ff17ff0000000000000000151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff151717ff17ff17ff

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
  | 3 => 14
  | 4 => 116
  | 5 => 362
  | 6 => 262
  | 7 => 27
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xcb46f5239ea771a73b98a67c
  | 3, 0 => 0xfa1703c1ebc4d2a89c85b0dc970838968eb32e0c8a0343006a68b51a69dd850d65f5e44660d8590747f5b8592de019c52a7cde3409bed72b
  | 4, 0 => 0x5d6431685c59b0725be18ef758b832a1579d2642578d54a655c4867354e3e7295362a9e352d8e06251c48b854cb1dd0d4c5a74dc49b8e71049a3beb04748b45a471511f446b6acfa45a6d45143c9b4da43b44f4140d324833aa08bce39e2988f38cb229737d67dad375030a136396fe03570268c3561a6333507a0ff348979bf329c9c4f324315b72fe221942f876d252d018d5b2c999c7a2c212f4b29efbf48284f3fc02675c08c24f8e91024b2322323a869e622455fcb1fa664cd1ec62d8a1e8599a31c9101dd1a03705c17facbdb160aff42104a2c9e10221d8f0fe7ecf80f70b2ae0c508c450b1755f70a26d8d00a1ce88b079d166006fc324a0657e087
  | 4, 1 => 0xfb2053def7f542f6f600ff55ebc4d2a8e0cd140fdafd92dfd6611886d5801a99d4462f1dd1b5cb82cddd248ccd65221dccc67faacb55bf7ac87b2503be9c054dbdbd4eb8bc0cc1eab8d3519eb86b72e6b605290ab3ca3690b2f8c671b26a919aac0b12ccaae8cb8baa812085a41b7609a386a6d0a27dbf1398cd194894b4ed66935d90dd90f9b3fc88679b138377bc958095f25f7fdb494b7e98a6d67b0a37ce7769863973a24078722746ca6ef0d3716c35a9276c2ffef36b1800926a8f0127619a0f5e5f086ab35eb6983c5e22c54d
  | 5, 0 => 0x1518d30514fda49814ae166d13a160051365ab471362a0b0130ccf4a130addb71302bd921293c1f9121ef7c01200323f11b5faba11952e3f1122077210f9fd9e10b1b71710114b7e0f8de7050e1fcd120e1ea2130dede8310da1dac80d9e10ca0cde9c7d0c729a920b6e2aea0b6dfdde0b3114de0b16c2b90aec5f940926bcc907f9a44507d4e250075c1bc7073586140682439d06625d94065e0e6e064df6e9064cb350063f1a63060a060d05feef8605fdd4ee0572fad70566e93c0566b9b5054a3ca304f3784a0463222e03f8cb5703ef5c5302b469a60261c51e021fdfd101cab57001b613cc01a228fc018928e600e7515d009fc288009665550001c2bf
  | 5, 1 => 0x3023f3772fdfb78a2f610ccc2f3ed0b72f302ebd2f02e0982eb190f62e6e1fc12e181a742dc882ab2dad214e2d628b232cd0cee62cad1d1e2ca7c8652c2993442bdc35bc2b4ae2782aec4cd02ac74f132a58ec7b29d44e6f29a6e673294b4f04287cba102844994726c08c77267a7d9825f21d0525d57a4e24f8e91024e53db124952c51229d10f8226abbb7220bccea208725c91ffe26ae1f6915fa1f2b6e7d1f19ad8e1e70470f1d6b28c81c2655cd1bb699241bb3cb8f1b9a196f1b82942c1b15fe4f1ad945db1acec0cc1a9ddcd41a80eb391a1dd8ad1a0ac10e19db1acf1967323e18b93c951889e63f184ad8ba17facbdb1784af4617625372160ba5b7
  | 5, 2 => 0x569c8e1155ce6a2c54dde4685384200353713b435362a9e353529c5051ea120b51e1b29b50d0d8da507d5a4a4f3f15a54f3cff5d4ed43f1f4e5335664d8d2f194cb1dd0d4b01aa754a9efbc24a95075247fe1a554748b45a4614f8634587cd0145485c4644a976a2449a81f943fec60b42733e3c4240f870416e79ab40ff2e7940ee01683fe4a32d3f24c1243e5879343dde7b7a3dadc8a93d88f3c43d58dcb63d54f4b33cfbb8963c319d4a3b1d294b3ac79dc639e2988f39da6eaa39d3847139b6ce8e3997e6c039179c80366d24fe360f029e3570268c356f612234b8593a339cdf82336a02aa32d53baf31cf560231a165eb310ee45330e394a730e13e1f
  | 5, 3 => 0x7db0ee0c7da8d6787d58532a7d007aca7cba485e7cb36b0e7c799c957c4ded077ac90fc779e104a6795213c578b342f276f809a2765966037621df597564e1d074c176e774a768ef73851a45735ec1087286846d726dd1b971e355fe71b5144e717b1162709184786fdcbc2d6fb5abbc6f0c58cc6e5429046e01e0396d3c11bc6c3045e96c2ffef36a8f01276926681f685bb0a767bf6dbf66454b2e65b4c8de6431a10c62dec0696233d1c4622565bb61b8011c618a95f160b866645fdb24e45faf43205fa5dcfc5f335fc25e3fc2185dbfa4af5cb3610a5c5ba4395c59b0725b817e9f5a9a0aa5599ae804594dace359061b5158b832a158316490579866a3
  | 5, 4 => 0xbdd177e8bb9140eabb7c1a88ba761a8bba59c05ab84c78fdb786064cb76f33ddb6b190d3b66776a9b44ac07cb2fa6ff3b273487db126b52bae590694ad477f3cac4f4d28ac0f0fc1ab3f54f4ab1dd7bbaa812085aa2175e0a98dbd53a97bb7a3a8fc83eca8ded36ba7664c01a73a17a9a62c1bfda5d800faa527d85aa4fc5fdea45c45b1a35551a6a2b4cb6b9d998e619d34bfda9a248b629944a8e996fcfb32959e9219943c6876922f80579021917e90033f538fd20b118eb21a188c216ffa89bb4b7788ef4afe88a4d2b688a15d148842682987860953869fdd0783b124d3832a696b82ef6d8a824cc35c822a05ec800561e67fdb494b7e98a6d67e8c9c4a
  | 5, 5 => 0xfee1ca9afd8bdd22fb233ae3fb1d0f65f44214dbef20384cee69638dedb41343e9924568e9665340e8734146e68fd4ace155e96ee1044fd7e02c3693df85b136dd827b62dc42316edb5ad56fdb3bfa62d6b719b3d577d8d1d41f82c5d2b6d9d3cfddddd1ce53c7e1cdd85782cdcdea11cd65221dcd0f562cccc67faacc8e78e6cbcb83e8cb079530ca2a9ef1ca28617fc6bcefcac6596438c4352de5c24e81d3c107d519bfd9b9ee
  | 6, 0 => 0x1b6faee71b17f2161b15fe4f1afccdcd1acec0cc1a3dcc7c19db1acf19725d61185cb0b31809fac017fa3fdd17c2692e17a1a3541762537216f467cf16edb26d16aededc1654b4801558dbee146b7fbf141b3882121ef7c0120eea2d11f2c26f1143d31810e2fed8109e00780f39a8270e1fcd120d908cfc0d4e991b0cf92db20cc0f76a0c497cf60b6e2aea0b4913790adb82090a716bcd09cbddd0088fc6740615f7d605feef8605a102090583c59d0566b9b5054a3ca3051fd72804dfcf4904d1464004441ade0404aa2303fa499b03f8cb570365c47f0356cfd602bcc98b0275789602413bc601f2d7d4018928e60159351400f4dbe800e87dbf00b25873
  | 6, 1 => 0x4761209346feb60646425730455c2ae44514ed61449a81f944214764433bac5141abbb674109113940e653c9400f48a83d54f4b33c3a5a1a3bbcc8a73b76963b3b0a3ae439b6ce8e389d52833865f9a73740760536b8a93b364d5dec3515b3e034de2d3634212fad339cdf823363b6cc3349b89a312a1f962face64a2f9069382f4dd2552f3ed0b72e990a0a2e3ef7ec2d56575d2d1076e12c29934429f9fcbe296669d6294b4f042927f73428f161f328d4304a28b708b8287cba1027e2b5fc27ba2cd0272d6b9b26d1935725f030f4219b0e4620f01fa120e1b39820d5e0971ffe26ae1fba27a31f19ad8e1e04bc391defad9f1cfc0ff51c7bf28c1c197b53
  | 6, 2 => 0x8bb5d9688ad6bfdc8abc430289c3e30d88e6ecce88e4af5c869fdd0785793da7842cbe5582f17bc27e9607cb7dca4c987a8fcbfb7a4d8ec7793268687708c6da7621df5975fbfecf7523c48673b3ed4b73070e5971b6bdd06fe303086fdcbc2d6c03cd1969fba2d1684a0b3067b8d1c9677b6cfb662299de65f6658665c34e486437dd3463fcfb2363b8adbb61e0d2936181732f617119485df922f35de30c175ccfc9b15ca51bf05c59b0725bf10db75afdb3095984fd4c58e0d93f588c54505800f6c6579866a3566fbfd954a460215458334f538420034f8e91674ed43f1f4ebf8d304c9bf18b4c6ce2134c3b2d694b08eb964b01aa754a445343495cacba
  | 6, 3 => 0xeae5e11ce491c826df85b136deba7486dc2776a0db5ad56fd89768a7d7072692d3d3e9e8d21eee88d0724892cfb64b76ccdc1aeacc5e28a0cb079530c7e30aa1c6bcefcac4352de5c423078dc4068a7bc2b5192fc0dc2da9bfd9b9eebd9e1877bc75acecbc482affba761a8bb9d95d42b9630356b8879624b71085ccb66776a9b288545cb2709e22b0e6099cb08f9c96ac706120ac06584ea98dbd53a84e9345a822a11da73a17a9a72f8f23a6303600a62c1bfda54c2289a527d85aa45c45b1a0680beea012374b9fc09db49f51a34c9e41ff139a22e8c29a17234c99f8483f96d3a9ab96cba002922f80578ee3204b8e9a2bae8c94a55f8c8a37ee8c216ffa
  | 6, 4 => 0xfee1ca9afc45419cf8731c66f52972d6edfb1e8fedb41343
  | 7, 0 => 0xf8731c66edfb1e8feae5e11cdeba7486ccdc1aeac2b5192fbd9e1877b08f9c96ac7061209f51a34c9e41ff13869fdd0785793da77e9607cb793268687523c486684a0b3065f665865c59b07234de2d361fba27a31b15fe4f1654b4800d908cfc0d4e991b0356cfd602413bc6
  | 8, 0 => 0x1b15fe4f
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcccc0000cccc0000aaaaaaaaaaaa0000aaaa0000aaaa000055555555555500005555000055550000333333333333000000ff00ff00ff000000ff000000ff00000000ffffffff00000000ffff000000000000aaaaaaaa0000000033333333000000000f0f0f0f0000000000ff00ff000000000000ffff0000000000000000
  | 0, 1 => 0x30303030303030300ffffffffffffff00ffffff00ffffff00ff00ff00ff00ff00ff00ff0000000000ff00000000000000cc00cc00cc00cc00aa00aa00aa00aa005500550055005500330033003300330000ffffffffffff0000ffff0000ffff0000ffff000000000000ff00ff00ff000000ff000000ff000000cccccccccccc
  | 0, 2 => 0x33333333ffffffff333333333333333333333333000000003300ff00ff00ff00330033003300330030303030303030302a2a2a2a2a2a2a2a222222222222222211111111111111110fff0000000000000f0fffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0000000000000a0a0a0a0a0a0a0a0505050505050505
  | 0, 3 => 0x70707070707070705f5f5f5f5f5f5f5f55ff55ff55ff55ff5555ffffffffffff5555ffff5555ffff555555555555555555555555000000005555000000000000550055005500550050505050505050504c4c4c4c4c4c4c4c44444444444444443f3f3f3f3f3f3f3f33ff33ff33ff33ff33ff000033ff00003333ffff3333ffff
  | 0, 4 => 0xaaaa000000000000aaa8aaa8aaa8aaa8aaa0aaa0aaa0aaa0aa88aa88aa88aa88aa00ff00ff00ff00aa00aa00aa00aa00aa00aa0000000000aa00000000000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a0a0a000000000a0a0000000000000a000a000a000a000888888888888888880808080808080807777777777777777
  | 0, 5 => 0xaaaaaaaaaaaaaa00aaaaaaaaaaaa0000aaaaaaaaaa88aa88aaaaaaaaaa00aa00aaaaaaaaa8a8a8a8aaaaaaaa00000000aaaaaaa0aaa0aaa0aaaaaa88aaaaaa88aaaaaa00aaaaaa00aaaaaa00aa00aa00aaaaa8a8aaaaa8a8aaaaa8a8a8a8a8a8aaaaa0a0aaaaa0a0aaaa8888aaaa8888aaaa888888888888aaaa0000aaaa0000
  | 0, 6 => 0xc8c8c8c8c8c8c8c8c0c0c0c0c0c0c0c0c0c00000c0c00000c0c0000000000000c000c000c000c000afafafafafafafafaaffaaffaaffaaffaaffaaff00000000aaff000000000000aaaaffffffffffffaaaaffffaaaaffffaaaaaaffaaffaaffaaaaaaffaaaaaaffaaaaaaaaffffffffaaaaaaaaaaffaaffaaaaaaaaaaaaaaaa
  | 0, 7 => 0xccccccccc8c8c8c8ccccccccc0c0c0c0cccccccc00000000cccccc00cccccc00cccccc00cc00cc00ccccc0c0ccccc0c0ccccc0c0c0c0c0c0cccc8888cccc8888cccc888888888888cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0cc00cc00cc00cc00cc00cc0000000000cc00000000000000
  | 0, 8 => 0xeaeaaaaaaaaaaaaaeaea0000eaea0000eaea000000000000eaaaeaaaeaaaeaaaea00ea00ea00ea00e8e8e8e8e8e8e8e8e0e0e0e0e0e0e0e0cfcfcfcfcfcfcfcfcdcdcdcdcdcdcdcdccffccffccffccffccccffffffffffffcccccccccccccccccccccccccccccc00cccccccccccc0000cccccccccc88cc88cccccccccc00cc00
  | 0, 9 => 0xeeeeeeeeaaaaaaaaeeeeeeee00000000eeeecccceeeecccceeeecccccccccccceeeeaaaaaaaaaaaaeeeeaaaa00000000eeee0000eeee0000eeee000000000000eecceecceecceecceeccccccccccccccee00ee00ee00ee00ececececececececececececcccccccceaeaeaeaeaeaeaeaeaeaeaea00000000eaeaaaaaeaeaaaaa
  | 0, 10 => 0xf0f0f0f0f000f000f0f0f0f0e0e0e0e0f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f0c0f0c0f0c0f0f0f0a0f0a0f0a0f0f0f000f0f0f000f0f0f000f000f000f0f0e0e0e0e0e0e0f0f00000f0f00000f0f0000000000000f0e0f0e0f0e0f0e0f0a0f0a0f0a0f0a0f000f000f000f000f0000000f0000000eeeeeeeeeeeeeeee
  | 0, 11 => 0xfafa000000000000faaafaaafaaafaaafa00fa00fa00fa00f8f8f8f8f8f8f8f8f8f8f0f0f8f8f0f0f8f8f0f0f0f0f0f0f8f0f8f0f8f0f8f0f5f5f5f5f5f5f5f5f1f1f1f1f1f1f1f1f0fff0fff0fff0fff0f0fffff0f0fffff0f0f0fff0fff0fff0f0f0fff0f0f0fff0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f0f0f0c0f0c0
  | 0, 12 => 0xfefefefe00000000fefe000000000000fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfc00000000fcfcf0f0f0f0f0f0fcfcccccfcfcccccfcfc0000fcfc0000fcfc000000000000fcf0fcf0fcf0fcf0fcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafafafafafaaaaaaaaafafafafa00000000fafa0000f0f00000
  | 0, 13 => 0xff00ff00ff000000ff00ff00ee00ee00ff00ff00cc00cc00ff00ff00aa00aa00ff00ff0000000000ff00fc00ff00fc00ff00fc00fc00fc00ff00fa00ff00fa00ff00fa00fa00fa00ff00cc00ff00cc00ff00cc00cc00cc00ff00aa00ff00aa00ff00aa00aa00aa00ff000000ff000000ff00000000000000fefefefefefefefe
  | 0, 14 => 0xffaaaaaaaaaaaaaaffaa0000ffaa0000ffaa000000000000ffa0ffa0ffa0ffa0ffa0ff00ff00ff00ff88ff88ff88ff88ff55ff55ff55ff55ff55ff00ff00ff00ff33ff33ff33ff33ff11ff11ff11ff11ff0fff0fff0fff0fff05ff05ff05ff05ff00ffffffffffffff00ffffff00ffffff00ff00ffffffffff00ff00ff00ff00
  | 0, 15 => 0xfff0ff00ff00ff00fff0f0f0f0f0f0f0fff00000fff00000fff0000000000000ffccffccffccffccffccff00ffccff00ffccff00ff00ff00ffccccccffccccccffcc0000ffcc0000ffc0ffc0ffc0ffc0ffc0ff00ff00ff00ffaaffaaffaaffaaffaaffaaaaaaaaaaffaaffaa00000000ffaaff00ffaaff00ffaaff00ff00ff00
  | 1, 0 => 0xffff0000aaaa0000ffff000088000000ffff000055550000ffff000055000000ffff000033330000ffff000000000000fffcfffcfffcfffcfffcfffc00000000fffcff00ff00ff00fffc000000000000fffafffafffafffafffa0000fffa0000fffa000000000000fff0fff0fff0fff0fff0fff0ff00ff00fff0fff0f0f0f0f0
  | 1, 1 => 0xffff00ff00ff00ffffff00ff00000000ffff0000ffffffffffff0000ffffff00ffff0000ffff3333ffff0000ffff00ffffff0000ffff0000ffff0000ffcc0000ffff0000ffaa0000ffff0000ff000000ffff0000fcfc0000ffff0000f0f00000ffff0000f0000000ffff0000eeee0000ffff0000cccc0000ffff0000cc000000
  | 1, 2 => 0xffffaa00aa00aa00ffffaa0000000000ffffa0a0ffffa0a0ffffa0a000000000ffffa000ffffa000ffffa000a000a000ffff888888888888ffff5555ffff5555ffff555555555555ffff550055005500ffff3333ffff3333ffff1111ffff1111ffff111100000000ffff0f0f0f0f0f0fffff050505050505ffff00ffffff00ff
  | 1, 3 => 0xfffff00000000000ffffeeeeeeeeeeeeffffccccffffccccffffccccffff0000ffffcccc00000000ffffcc00ffffcc00ffffc0c0ffffc0c0ffffc0c0c0c0c0c0ffffc0c000000000ffffc000ffffc000ffffc000c000c000ffffc00000000000ffffaaaaffffaaaaffffaaaaffff0000ffffaaaaaaaaaaaaffffaa00ffffaa00
  | 1, 4 => 0xffffffff0000aaaaffffffff00005555ffffffff00000000fffffff0fffffff0fffffff0fff0fff0ffffffaaffaaffaaffffff00ffffff00ffffff00ffff0000ffffff00ff00ff00ffffff0000000000fffffcfcfcfcfcfcfffffc00fc00fc00fffffc0000000000fffff0f0fffff0f0fffff0f0f0f0f0f0fffff000f000f000
  | 1, 5 => 0xfffffffffc00fc00fffffffffafafafafffffffff0f0f0f0fffffffff000f000ffffffffeeeeeeeeffffffffccccccccffffffffcccc0000ffffffffcc00cc00ffffffffcc000000ffffffffaaaaaaaaffffffff88888888ffffffff55555555ffffffff55005500ffffffff0f0f0f0fffffffff0000ffffffffffff0000cccc
  | 1, 6 => 0xffffffffffffffffffffffffffffff00fffffffffffff0f0ffffffffffffaaaaffffffffffff0000fffffffffff0fff0ffffffffffaaffaaffffffffff00ff00ffffffffff000000fffffffffcfcfcfc
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x10a45a28dc08d451b311a8b3
  | 3, 0, 0 => 0x85381248a48538198924592351684485331248b48cb31228b4a6c65168a470331248d468aa0f66048538178924a6b811c8a468ac8f6564a3ac92c604542109e4a48538114604
  | 4, 0, 0 => 0x853815c84302c29c0cc44981614e05920cc0b0a702c9085658cc29c0cc492c29c08930109626e057a10c0abf5eac9086058538164842dac29c0b249981614e05e280c0b0c702c908605853816484322c29648b42181614e06624908b03702c908605
  | 4, 0, 1 => 0x853812484232c29c084300fd614eb59210c0b477e2c908605853916484302d35c0cc49239614e059258c0b0a702dd086058538164842c2c29c09437181614bd59210c0b4d8cb817892591b816484302bfd64843013d614e05e1bcc0b0a702c9085f5
  | 4, 0, 2 => 0x953816484302c29c0b240981614e05921052b0a702c908595a1b816484302c29b0b242181614e0549f0c0b0a702a108605852c9086025ad11c0b242181614e0591d0c0b0a702a5085758538164842e2d1da2b23d9815c0b2421804cb0a702c908615
  | 4, 0, 3 => 0xa03815084302c29c0b242181614da59210c0b3f702c908605853815484302d1d64843012169b196624916ae04c22508605853816494302c29c0b342181614e05a210c0b0a702c9248458538198c3502c29fea84218161ce059210c0ae05fac908605
  | 4, 0, 4 => 0x85381647b2b2d01c0b242181614e0661b8c0ae0591ecc04f59a3816484302d1daab242181614e058210c0b0a70331246e5853815684302c29feb242181614cd59210c0b0a702c900605a3bf96484302c29c0ba4218169ab24722d08b0a54210c04a5
  | 4, 0, 5 => 0x853817284302c297ab237981614e0371808eb0a702c91e845853814e84302c2a0eb24218169b197033124b4059210c04a5702c90867302c29c0a83d981614d759210c0b0a702c920845853a16484302cd5c0b24218168ed159210acb0a59210c02c5
  | 4, 0, 6 => 0x853656484302b81648d421815c0ce59210c0b0a7033124605933816484302c29eab242181642e059210c0b0a7022508605a3b456484302b81649246a1169b1970228c0b0a702c9084e5853812489422c29c0b24621169b197024914b0a702c908545
  | 4, 0, 7 => 0x833816484302c29649245a1168eb24213c94a008538198924
  | 5, 0, 0 => 0x85381648430055a14f959210ea606a6c65c0b2420a58010a702c9083a591429c0b242181a9b0b702c908606a6c65c0b240171a14e059210c0326a6c65c0b23f981a14e059210c0566a6c49c0b242181a14e061ac908606a6c71c0b242181a14e059210c02f6ac465c0b240181aaf19702c908606
  | 5, 0, 1 => 0x8cb81649a42181a9b47692c90860685381648430145a9b197030d286068538196b242181a14e059210de606a6c65bcb242181ab110702c9086068538182b242181a9b1a702c9086068538164843e181a32e05927908606a6c6dc0b242181a9b19702c90260685385c0b242181a8f0a702c908606
  | 5, 0, 2 => 0x8cc29c0b24215da14e0632c908606a4429c0b242181a150a702c9086068cb81649842181aa719702c9086068538164a342181a32e060ac8de6069e429c0b242181a14e0592c908606a6c65c0b249211a14e059210f0606a6c29c0b23d981a9b197033186a06a7c65c0b242181a14e059210c03b6
  | 5, 0, 3 => 0x8cc29c0b23e1819c0b24f26108606ad459c0b242181a9b0a70225086068cac93c9542181a14e059221086068cc41c0b242181a14e059210c00d6a6d1da2b242181a14ee702c908606a6c65c0b24a181a14e059210e260687c29c0b242181a9b19702cd08606a3d05c0b2421818010a591805c1c5
  | 5, 0, 4 => 0xa6c65c0b242181a5919702c908606853edc0b242181a9b196d2c908606853817ab242181a14ec702c90860685381a8b242181a830a702c908606a5429c0b242181a14e059210c0036853818eb242181a14e059210c049600429c0b242159614e059210f4606a1429c0b242181aa50a702c908606
  | 5, 0, 5 => 0x8b381b6b242181a14e06eac90860685381646e30109a14e052a8908606aa429c0b242181a14f4702c9086069dc29c0b242181a14e059210c05c6a6c45c0b242181a32e0592492284685425c0b242181a14e059210c04068cc29f2b242181a14e059210c0256853816484300b5a14e059210c0366
  | 5, 0, 6 => 0xa3429c0b242181a14e059210c0536a6c65feb242181800e0591805c15585381a6b242181a9b1966ac908606a3c29648430129a9b19702c900606a6c65649542181a14e059210c4606a6c5dc0b242181a1501702c908606702c908753013d8010a701805c245004297ab24218169b04702c908606
  | 5, 0, 7 => 0x8cb81648434181a9ae0602c90860696c29c0b242181a14e059210c01c6a8c29c0b242181a9b10702c9086068538198b237181a8d19702c9085768cb81649142181a14fc702c908606a6c65c0cc491b9a9b24702c908606853b5c0b242181ab70a702c908606a6c29c0b24215daad0a702c908606
  | 5, 0, 8 => 0x429648430071614e059210c04c685381647639181a14e0592490860685401c0b2421818010a702c9085c585395c0b242181a14e059280c042600429c0b2300b96bf19702c908606a3465c0b23e181a990a702c908606a0429c0b242181a9b0a702c8f8606a6c65c0b042181800b24218038155
  | 5, 0, 9 => 0x8538178b242181a9b19702bd0060685381648430029a14e059210c02068538184b242181a3308702c9086068538188b242181ac514702c908606a6c65c0cc37181a14e059210c0026853ddc0b242181a9b19732c908606853816486421818010a702a108605853816484300a1a14e3702c908606
  | 5, 0, 10 => 0x429c0b2492116b919702c908606a6c65c0b24218da14e0652c908606ac4e9c0b242181800e05fac90860585381648430181a14e9702c9086068538164843003da14e059210c033685381648430169a14ef702c908606a6cadc0b242181a330a702c90856688381648439181a14e0662c940606
  | 5, 0, 11 => 0xb0429c0b242181a14e059210c04868538164843c981800e059210c0155a6c65c0b2482118010a702c928605b3429c0b242181a3d19702c90860685381c0b242181a9b19702c50860685381648430115a330a5eac908606a6c65c0b242175a14e059210c02e6a6c65c0b249109a14e05f2c908606
  | 5, 0, 12 => 0xa2c29c0b242181a9b19702c8c035685381648430005a14e059210c00068538164843006da14e05aac908606853816484300658010a702c90860585381649d42181a9b19703316492685381649b42181a14e059210e6606853816484300458013f702c90860585381648430179a930a702c908606
  | 5, 0, 13 => 0xa6c65c0a4421818010a7fac90860500429c0b2401816cf0a702c90860685381648430025a9b19702ed0860685381648430079a6f19702c908606a6c65c0cc37981a14e05022508606853cdc0b242181ac70a702c908606853fdc0b242181a32e067ac908606702c93c9942181a14fe702c908606
  | 5, 0, 14 => 0xa6c65c0b942181a14e059210b44a685381648430039a8f0a692c908606a6c657ab237981a14e059210c039685381aab242181a9b19701b8c0476a6c65c0b242155a14e064ac9086068538164843a981a14e059210e0606a8465c0b242181a14e059210c0166a3c29c0b23d981a9ae059210c0316
  | 5, 0, 15 => 0xa7465c0b242181a330a702c928606a6c65c0b242139a14f1702c908606853816484300ada7d0a702c908606a6c65c09244a11a14e059210c0066a6c65c0b246211ab10a702c908606702c9409842181a2ce059210c05a68cc29c0b249211a14e059210c037685381648430129a14e06fac908606
  | 5, 1, 0 => 0x85381648542181a14e059210c00c68538170b242181a530a702c90860685381648430105ad10a702c9086068cc29c0b242181a9b19702c8f6606a6c65c09444981a14e059210c01f6853d9c0b242181a14e059210da6068538164843004180140702c90860500429c0cc3718168f0a68ac908606
  | 5, 1, 1 => 0xa3465c0b242181a14e059210ee60685381648434981a9b19702c90e60685381648435181a14e059210c00b69cc29c0b242181a14e059210c03c685381649842181a9b197033124606a6c75c0b242181a9b18702c90860685381648430075a9b19701bcc046685381648430111a9b197022508606
  | 5, 1, 2 => 0x8fc29c0b242181a14e059210c0226853816484300f5a5d19702c9086060053632e06624968119702c9086068538164a242181a14e059210c03868538164843010da330a70330dc606a4c29c0a942181a14e059210c0076a6c3dc0b242181a5f0a702c908606a6c65c0b24215da610a702c908606
  | 5, 1, 3 => 0x93c29c0b242181ac50a702c9085c6a3b8164843013da14e059210c042685381649c42181a14e059210c02a6a6c65c0bc37181a970a702c908606a6c65649245a11a14e059210fa606b4c29c0b242181a1505702c908606a6b81528430141a14e05925d0860685381648430069a14e061ac940846
  | 5, 1, 4 => 0x99429c0b242181a14b251210c04a600429c08942181680e059289086060051da2b242181614e059210c0126a6cd9c0b242181a14e068ac90860685381648441181a14c35eac9086068538198b242181a9b195922d086068538164843013da8ee068ac908606a3c29c0b242159a14e0692c908606
  | 5, 1, 5 => 0x8538164843005da410a702c9086060042964841d071614e059210c01868538164843d981a14e059210dc606a6c65c0b24217da14f0702c90860698c29c0b2421818010a702c8742e5a6c65c0b242159a710a702c90860685381648436181a9b0d702c908606853816492421b9a8f0a7dac908606
  | 5, 1, 6 => 0xb2c29c0b242181a14e059210d66060038164841d055614e059210c047685381648427929a14e059210cc606a6c55c0b242181a14e059210c03a685381a0b242181a14e059250c0466
  | 6, 0, 0 => 0xa6c65c0b242180c0f4d8cba5c0b242181e9b19702c9086007bd3632fa702c9086070000214e05921074b4d8cb816484300cde9b19702c908602d3d669b19702c908607a6c29c0b256210c0f4d8cc09c0b242181e9ae059210ec6028380214e061ac908606a6c29c0b253210c0f4d8cc59c0b242181e9b19703596484303d3614e059210c0427
  | 6, 0, 1 => 0xb146614e059210c0f4d8cb817cb242181c014d8cb816492423535c0b25026508607ad46614e059210c0f4d8538164843013de330a702c9086e303d364b19702c908607a6c29c0d259210c0e008cb81649e42181a6319853816484303d7a9b19702c9086070051e14e059210c0c0085381648430055a9b19702c90860293c6614e059210c0147
  | 6, 0, 2 => 0x535c0b2420e828d4da4c65c0b242181ec14d8cb816484303d3614e059210c0507a6c65c0c559210c0e00a6c65c0b24a181acd4d8cb81648430380232e04218048076a6c29c0d159210c0f4d8cb81b8b242181e9b19703816484303d3632e059210c04570042a14e059210c0d4d8cb816484300b9c014d8cb81086012353614e0662c908607
  | 6, 0, 3 => 0xa6c65c0b559210c0f4d8cb81648430065c014d8cb81648430353632e0592a50860700429f6e059210c0d4d8cb81649d42181c014185381648430353632e05927d08607a6c65fae059210c0f4d8cb81648439981e330a702c908601d3d3632e059210c0117a6c65c0b24218008e00a1429c0b242181a9b19702994484303d3632e059210c05e7
  | 6, 0, 4 => 0xa6c6628e059210c0f4d8cb816cb242181eb54d853816484303d4632e059210c0147a6c65c0a044a10c0f4d8cbcdc0b242181ec74d8cb816484303d3614e059210c014700429e8e059210c0c008cb8164843001d8014d88b81648430353632e05925508607a6c65c0b24218002f4d8cb81648430001e9b19702c908600dbc6614e05928108607
  | 6, 0, 5 => 0xa6c65c0c959210c0e0085381648430071a9b19702c90875303802330a702c9083a6a6c65c0b24a210c0f4d8cb81648430059c015685381648430353632e0592b508607a6c65c0b24218046e00a6c65c0b240181acb19853816484303c6614e059210c0247a6c65f0e059210c0f62a6c29c0b242181c014d8cac92a8430359e9b19702c908607
  | 6, 0, 6 => 0xa6c65c0b2421800ce00004296484300716b14d8cb816484303c66150a702c908607b157632e059210c0f4d85381b6b242181e9b19702c90884303d3632e059210c0377a6c65c0b24218094f4d8cb81beb242181c0000853816460172d3632e059210b44a7a6c65c0b24218042f4d8cb816484300e5e8f19853816484303c6614e059210c0157
  | 6, 0, 7 => 0xa6c65c0b859210c0f4d8cb81648430105ed14d8cb816484303d363319702c9086078cc29f6e059210c0e0085381648430169a8319853816484303d8a32e059210c05a7a6c65c0b2421803ef4d8cbd9c0b242181e9b19702c9086d303d3632e059210c03070053632e0661b8c0d4d8cb81648942181e9b1978b816484303d3632e059210c02b7
  | 6, 0, 8 => 0xa6ce632e059210c0e00a4c29c0b242181aad19853816484303d3632e059210fc607aad3632e059210c0e000038164843005569b4970349648430380214e059210c02e6a6c65c0b2421803af4d8cb81648430021c014d59210c01c0a353632e05927908607ac465c0b2421c8c0e00ae465c0b242181a330a7a3816484303d3632e059210ca607
  | 6, 0, 9 => 0x99c6614e059210c0e008cc29648430071a9b308cb816484303d3632e059285086079ecee32e059210c0f4d8cb81648434981c014d702c9086009b002330a702c8c02e6b15362ce059210c0f4d8cb8164843009dc0000853816484302d3632e059210d4607a6c65c0b2421807cf1985381648430071e9b19702c9086005bd3632e066210dc607
  | 6, 0, 10 => 0x429c0b24218094d56a6c3dc0b242181e9b19702c9087d303801c0b24218028076b4d3632e059210c0f4d8cc15c0b242181e9b19702c92e8430380214e059210ea606a6c65c0c35928108f4d8cb816484300f5e9b19702c94484303d3632e059210c0437b253632e059210c0f4da4c65c0a942181e9b19702c9086003bd3632e0642c908607
  | 6, 0, 11 => 0xa6c65c0b2421809af4d85381648430169e9b19713816484303d3632e068ac908607a6c65c0b242208c0f4d8cb0d7ab242181c011985381648430353632e0662c908607a6c65c084371808cf4d8cb8164843013de9b1970349648430380232e059210c0156a6c65c0cc61a10c0f62a6c65c0b242171e9b19702c90860213d3632e059210c02a7
  | 6, 0, 12 => 0x8cc29c0b24218094e00a6c6564841d071a9b19702c908600c3d6a9b19702c908607a6c65c0b2421b8c0f198538164843a981e9b318cb8164843038029b19702c8742e600475c0b2421800ed4d8cba9c0b242181c014d8eb81648430353632e059210c0577a6c65c0b249210dcf4d99465c0b242181e9b195928908602538029b197022508606
  | 6, 0, 13 => 0xa6ca232e059210c0f61a6c65c0b242181e3319853816484303d3632e05928108607a6c65c0b24218074f4d8cb9dc0b242181c010a702c9448430353632e0682c908607a6c65c0b24a1808ce008538164843001da9b19702c908600bbd3632e061a10c0467005361ee059210c0d4d90465c0b242181c014d8cb8164842bb0028d19702c908606
  | 6, 0, 14 => 0x429c0cc59210c0c008538164843013da9b478cb816484303d3632e059210c01570053632e05921074d4d8cb816484300c9c010a7034964843035969b19702c908607a6c7632e059210c0f4d8cb81648435981c010a702c9086021353632e059210c0477a6c65e4e059210c0f4d8cb816484300d1e9b19702c9086002b80214e059210fa606
  | 6, 0, 15 => 0xab53632e059210c0e00a6c65c060170918010a702c9086e30353632f4702c908607a6c6612e059210c0e0098c29c0b242181a9b418cb816484303d3632e059210c04978cc29c0b251210c0f4d8cb81648842181e9b1987b8164843038029b19591805c1c6a6c6614e059210c0f4d8cb8164a342181c010a70345648430353632e059210c03b7
  | 6, 1, 0 => 0x16585381648430353632e0622c9086070053632b24218038d4d8cb81649242181e9b19702c908600e380214e059210c03a6
  | 7, 0, 0 => 0x2330a702c9086060053632e0662c9086070053632e0692c9086070053632e059210c04270053632e059210fa6070053632e059289086070053632e059210c007700000010a702c9086050053632e059210c04a70000232e059210c0076000029b19702c908606005369319702c9086070053632e059210c02e7000029b1970210c02460053632e059210c05a7005363302702c908607
  | 7, 0, 1 => 0x29b1959210c01c60053632e059210c01c70055a9b19702c9086070053632f4702c90860700536330a702c908607000029b19702c9083a6005969b19702c9086070053632e059281086070053632e059210c03a70056a9b19702c9086070053632e059210dc607
  | 8, 0, 0 => 0x29b19702c908606
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
private theorem z2_0 : span (Z 2) 3 0 = true := by decide +kernel

private theorem z2 : span (Z 2) 3 0 = true := z2_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : span (Z 3) 14 0 = true := by decide +kernel

private theorem z3 : span (Z 3) 14 0 = true := z3_0

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
private theorem z4_96 : span (Z 4) 20 96 = true := by decide +kernel

private theorem z4_a1 : span (Z 4) 48 0 = true :=
  span_join (f := Z 4) (a := 24) (o := 0) (b := 24) z4_0 z4_24

private theorem z4_a2 : span (Z 4) 72 0 = true :=
  span_join (f := Z 4) (a := 48) (o := 0) (b := 24) z4_a1 z4_48

private theorem z4_a3 : span (Z 4) 96 0 = true :=
  span_join (f := Z 4) (a := 72) (o := 0) (b := 24) z4_a2 z4_72

private theorem z4_a4 : span (Z 4) 116 0 = true :=
  span_join (f := Z 4) (a := 96) (o := 0) (b := 20) z4_a3 z4_96

private theorem z4 : span (Z 4) 116 0 = true := z4_a4

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
private theorem z5_360 : span (Z 5) 2 360 = true := by decide +kernel

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

private theorem z5_a15 : span (Z 5) 362 0 = true :=
  span_join (f := Z 5) (a := 360) (o := 0) (b := 2) z5_a14 z5_360

private theorem z5 : span (Z 5) 362 0 = true := z5_a15

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
private theorem z6_240 : span (Z 6) 22 240 = true := by decide +kernel

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

private theorem z6_a10 : span (Z 6) 262 0 = true :=
  span_join (f := Z 6) (a := 240) (o := 0) (b := 22) z6_a9 z6_240

private theorem z6 : span (Z 6) 262 0 = true := z6_a10

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

def CG : Circuit := ⟨[⟨GateOp.and, [4, 5]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.and, [12, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12417

theorem PEqualNP.Outside.L_meta_12417 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132288 * 2 ^ 32 + 3892373504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132288 * 2 ^ 32 + 3892373504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12417.mainG PEqualNP.Outside.L_meta_12417.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12417.CG, PEqualNP.Outside.L_meta_12417.CG_mono, by
      have : PEqualNP.Outside.L_meta_12417.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12417.CG_eval⟩
