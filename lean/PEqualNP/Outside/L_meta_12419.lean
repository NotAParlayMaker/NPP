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
namespace PEqualNP.Outside.L_meta_12419

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (3941132424 * 2 ^ 32 + 3901286536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 22, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 38, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 3, 3, 3, 3, 3, 3, 3, 7, 3, 3, 3, 11, 3, 13, 14, 15, 3, 3, 3, 19, 3, 3, 3, 23, 3, 3, 3, 27, 3, 29, 30, 31, 3, 3, 3, 35, 3, 3, 3, 39, 3, 3, 3, 43, 3, 45, 46, 47, 3, 3, 3, 51, 3, 53, 54, 55, 3, 57, 3, 59, 3, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 7, 7, 7, 3, 7, 7, 7, 7, 7, 7, 7, 11, 7, 13, 14, 15, 7, 7, 7, 19, 7, 7, 7, 23, 7, 7, 7, 27, 7, 29, 30, 31, 7, 7, 7, 35, 7, 7, 7, 39, 7, 7, 7, 43, 7, 45, 46, 47, 7, 7, 7, 51, 7, 53, 54, 55, 7, 57, 7, 59, 7, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 11, 11, 11, 3, 11, 11, 11, 7, 11, 11, 11, 11, 11, 13, 14, 15, 11, 11, 11, 19, 11, 11, 11, 23, 11, 11, 11, 27, 11, 29, 30, 31, 11, 11, 11, 35, 11, 11, 11, 39, 11, 11, 11, 43, 11, 45, 46, 47, 11, 11, 11, 51, 11, 53, 54, 55, 11, 57, 11, 59, 11, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 13, 13, 13, 3, 13, 13, 13, 7, 13, 13, 13, 11, 13, 13, 14, 15, 13, 13, 13, 19, 13, 13, 13, 23, 13, 13, 13, 27, 13, 29, 30, 31, 13, 13, 13, 35, 13, 13, 13, 39, 13, 13, 13, 43, 13, 45, 46, 47, 13, 13, 13, 51, 13, 53, 54, 55, 13, 57, 13, 59, 13, 61, 62, 63, 14, 14, 14, 3, 14, 14, 14, 7, 14, 14, 14, 11, 14, 13, 14, 15, 14, 14, 14, 19, 14, 14, 14, 23, 14, 14, 14, 27, 14, 29, 30, 31, 14, 14, 14, 35, 14, 14, 14, 39, 14, 14, 14, 43, 14, 45, 46, 47, 14, 14, 14, 51, 14, 53, 54, 55, 14, 57, 14, 59, 14, 61, 62, 63, 15, 15, 15, 3, 15, 15, 15, 7, 15, 15, 15, 11, 15, 13, 14, 15, 15, 15, 15, 19, 15, 15, 15, 23, 15, 15, 15, 27, 15, 29, 30, 31, 15, 15, 15, 35, 15, 15, 15, 39, 15, 15, 15, 43, 15, 45, 46, 47, 15, 15, 15, 51, 15, 53, 54, 55, 15, 57, 15, 59, 15, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 19, 19, 19, 3, 19, 19, 19, 7, 19, 19, 19, 11, 19, 13, 14, 15, 19, 19, 19, 19, 19, 19, 19, 23, 19, 19, 19, 27, 19, 29, 30, 31, 19, 19, 19, 35, 19, 19, 19, 39, 19, 19, 19, 43, 19, 45, 46, 47, 19, 19, 19, 51, 19, 53, 54, 55, 19, 57, 19, 59, 19, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 23, 23, 23, 3, 23, 23, 23, 7, 23, 23, 23, 11, 23, 13, 14, 15, 23, 23, 23, 19, 23, 23, 23, 23, 23, 23, 23, 27, 23, 29, 30, 31, 23, 23, 23, 35, 23, 23, 23, 39, 23, 23, 23, 43, 23, 45, 46, 47, 23, 23, 23, 51, 23, 53, 54, 55, 23, 57, 23, 59, 23, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 27, 27, 27, 3, 27, 27, 27, 7, 27, 27, 27, 11, 27, 13, 14, 15, 27, 27, 27, 19, 27, 27, 27, 23, 27, 27, 27, 27, 27, 29, 30, 31, 27, 27, 27, 35, 27, 27, 27, 39, 27, 27, 27, 43, 27, 45, 46, 47, 27, 27, 27, 51, 27, 53, 54, 55, 27, 57, 27, 59, 27, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 29, 29, 29, 3, 29, 29, 29, 7, 29, 29, 29, 11, 29, 13, 14, 15, 29, 29, 29, 19, 29, 29, 29, 23, 29, 29, 29, 27, 29, 29, 30, 31, 29, 29, 29, 35, 29, 29, 29, 39, 29, 29, 29, 43, 29, 45, 46, 47, 29, 29, 29, 51, 29, 53, 54, 55, 29, 57, 29, 59, 29, 61, 62, 63, 30, 30, 30, 3, 30, 30, 30, 7, 30, 30, 30, 11, 30, 13, 14, 15, 30, 30, 30, 19, 30, 30, 30, 23, 30, 30, 30, 27, 30, 29, 30, 31, 30, 30, 30, 35, 30, 30, 30, 39, 30, 30, 30, 43, 30, 45, 46, 47, 30, 30, 30, 51, 30, 53, 54, 55, 30, 57, 30, 59, 30, 61, 62, 63, 31, 31, 31, 3, 31, 31, 31, 7, 31, 31, 31, 11, 31, 13, 14, 15, 31, 31, 31, 19, 31, 31, 31, 23, 31, 31, 31, 27, 31, 29, 30, 31, 31, 31, 31, 35, 31, 31, 31, 39, 31, 31, 31, 43, 31, 45, 46, 47, 31, 31, 31, 51, 31, 53, 54, 55, 31, 57, 31, 59, 31, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 35, 35, 35, 3, 35, 35, 35, 7, 35, 35, 35, 11, 35, 13, 14, 15, 35, 35, 35, 19, 35, 35, 35, 23, 35, 35, 35, 27, 35, 29, 30, 31, 35, 35, 35, 35, 35, 35, 35, 39, 35, 35, 35, 43, 35, 45, 46, 47, 35, 35, 35, 51, 35, 53, 54, 55, 35, 57, 35, 59, 35, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 39, 39, 39, 3, 39, 39, 39, 7, 39, 39, 39, 11, 39, 13, 14, 15, 39, 39, 39, 19, 39, 39, 39, 23, 39, 39, 39, 27, 39, 29, 30, 31, 39, 39, 39, 35, 39, 39, 39, 39, 39, 39, 39, 43, 39, 45, 46, 47, 39, 39, 39, 51, 39, 53, 54, 55, 39, 57, 39, 59, 39, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 43, 43, 43, 3, 43, 43, 43, 7, 43, 43, 43, 11, 43, 13, 14, 15, 43, 43, 43, 19, 43, 43, 43, 23, 43, 43, 43, 27, 43, 29, 30, 31, 43, 43, 43, 35, 43, 43, 43, 39, 43, 43, 43, 43, 43, 45, 46, 47, 43, 43, 43, 51, 43, 53, 54, 55, 43, 57, 43, 59, 43, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 45, 45, 45, 3, 45, 45, 45, 7, 45, 45, 45, 11, 45, 13, 14, 15, 45, 45, 45, 19, 45, 45, 45, 23, 45, 45, 45, 27, 45, 29, 30, 31, 45, 45, 45, 35, 45, 45, 45, 39, 45, 45, 45, 43, 45, 45, 46, 47, 45, 45, 45, 51, 45, 53, 54, 55, 45, 57, 45, 59, 45, 61, 62, 63, 46, 46, 46, 3, 46, 46, 46, 7, 46, 46, 46, 11, 46, 13, 14, 15, 46, 46, 46, 19, 46, 46, 46, 23, 46, 46, 46, 27, 46, 29, 30, 31, 46, 46, 46, 35, 46, 46, 46, 39, 46, 46, 46, 43, 46, 45, 46, 47, 46, 46, 46, 51, 46, 53, 54, 55, 46, 57, 46, 59, 46, 61, 62, 63, 47, 47, 47, 3, 47, 47, 47, 7, 47, 47, 47, 11, 47, 13, 14, 15, 47, 47, 47, 19, 47, 47, 47, 23, 47, 47, 47, 27, 47, 29, 30, 31, 47, 47, 47, 35, 47, 47, 47, 39, 47, 47, 47, 43, 47, 45, 46, 47, 47, 47, 47, 51, 47, 53, 54, 55, 47, 57, 47, 59, 47, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 51, 51, 51, 3, 51, 51, 51, 7, 51, 51, 51, 11, 51, 13, 14, 15, 51, 51, 51, 19, 51, 51, 51, 23, 51, 51, 51, 27, 51, 29, 30, 31, 51, 51, 51, 35, 51, 51, 51, 39, 51, 51, 51, 43, 51, 45, 46, 47, 51, 51, 51, 51, 51, 53, 54, 55, 51, 57, 51, 59, 51, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 53, 53, 53, 3, 53, 53, 53, 7, 53, 53, 53, 11, 53, 13, 14, 15, 53, 53, 53, 19, 53, 53, 53, 23, 53, 53, 53, 27, 53, 29, 30, 31, 53, 53, 53, 35, 53, 53, 53, 39, 53, 53, 53, 43, 53, 45, 46, 47, 53, 53, 53, 51, 53, 53, 54, 55, 53, 57, 53, 59, 53, 61, 62, 63, 54, 54, 54, 3, 54, 54, 54, 7, 54, 54, 54, 11, 54, 13, 14, 15, 54, 54, 54, 19, 54, 54, 54, 23, 54, 54, 54, 27, 54, 29, 30, 31, 54, 54, 54, 35, 54, 54, 54, 39, 54, 54, 54, 43, 54, 45, 46, 47, 54, 54, 54, 51, 54, 53, 54, 55, 54, 57, 54, 59, 54, 61, 62, 63, 55, 55, 55, 3, 55, 55, 55, 7, 55, 55, 55, 11, 55, 13, 14, 15, 55, 55, 55, 19, 55, 55, 55, 23, 55, 55, 55, 27, 55, 29, 30, 31, 55, 55, 55, 35, 55, 55, 55, 39, 55, 55, 55, 43, 55, 45, 46, 47, 55, 55, 55, 51, 55, 53, 54, 55, 55, 57, 55, 59, 55, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 57, 57, 57, 3, 57, 57, 57, 7, 57, 57, 57, 11, 57, 13, 14, 15, 57, 57, 57, 19, 57, 57, 57, 23, 57, 57, 57, 27, 57, 29, 30, 31, 57, 57, 57, 35, 57, 57, 57, 39, 57, 57, 57, 43, 57, 45, 46, 47, 57, 57, 57, 51, 57, 53, 54, 55, 57, 57, 57, 59, 57, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 59, 59, 59, 3, 59, 59, 59, 7, 59, 59, 59, 11, 59, 13, 14, 15, 59, 59, 59, 19, 59, 59, 59, 23, 59, 59, 59, 27, 59, 29, 30, 31, 59, 59, 59, 35, 59, 59, 59, 39, 59, 59, 59, 43, 59, 45, 46, 47, 59, 59, 59, 51, 59, 53, 54, 55, 59, 57, 59, 59, 59, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 61, 61, 61, 3, 61, 61, 61, 7, 61, 61, 61, 11, 61, 13, 14, 15, 61, 61, 61, 19, 61, 61, 61, 23, 61, 61, 61, 27, 61, 29, 30, 31, 61, 61, 61, 35, 61, 61, 61, 39, 61, 61, 61, 43, 61, 45, 46, 47, 61, 61, 61, 51, 61, 53, 54, 55, 61, 57, 61, 59, 61, 61, 62, 63, 62, 62, 62, 3, 62, 62, 62, 7, 62, 62, 62, 11, 62, 13, 14, 15, 62, 62, 62, 19, 62, 62, 62, 23, 62, 62, 62, 27, 62, 29, 30, 31, 62, 62, 62, 35, 62, 62, 62, 39, 62, 62, 62, 43, 62, 45, 46, 47, 62, 62, 62, 51, 62, 53, 54, 55, 62, 57, 62, 59, 62, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 63, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 63, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1517177717771777151717771777177715171777177717770000000000000000151717771777177700000000000000001517177717771777000000000000000015171777177717771517177717771777151717771777177700000000000000001517177717771777000000000000000000000000000000000000000000000000151717771777177715171777177717771517177717771777000000000000000015171777177717770000000000000000000000000000000000000000000000001517177717771777000000000000000000000000000000000000000000000000151717771777177700000000000000000000000000000000000000000000000015171777177717771517177717771777151717771777177700000000000000001517177717771777000000000000000000000000000000000000000000000000151717771777177700000000000000000000000000000000000000000000000015171777177717770000000000000000000000000000000000000000000000001517177717771777151717771777177715171777177717770000000000000000151717771777177700000000000000000000000000000000000000000000000015171777177717770000000000000000000000000000000000000000000000001517177717771777000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeae8e888e888e888eae8e888e888e888eae8e888e888e8880000000000000000eae8e888e888e8880000000000000000eae8e888e888e8880000000000000000eae8e888e888e888eae8e888e888e888eae8e888e888e8880000000000000000eae8e888e888e888000000000000000000000000000000000000000000000000eae8e888e888e888eae8e888e888e888eae8e888e888e8880000000000000000eae8e888e888e888000000000000000000000000000000000000000000000000eae8e888e888e888000000000000000000000000000000000000000000000000eae8e888e888e888000000000000000000000000000000000000000000000000eae8e888e888e888eae8e888e888e888eae8e888e888e8880000000000000000eae8e888e888e888000000000000000000000000000000000000000000000000eae8e888e888e888000000000000000000000000000000000000000000000000eae8e888e888e888000000000000000000000000000000000000000000000000eae8e888e888e888eae8e888e888e888eae8e888e888e8880000000000000000eae8e888e888e888000000000000000000000000000000000000000000000000eae8e888e888e888000000000000000000000000000000000000000000000000eae8e888e888e888000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888eae8e888e888e888

def cMZZ : Nat := 0x1517177717771777000000000000000015171777177717770000000000000000151717771777177700000000000000000000000000000000000000000000000015171777177717770000000000000000151717771777177715171777177717771517177717771777000000000000000000000000000000000000000000000000151717771777177700000000000000001517177717771777151717771777177715171777177717770000000000000000151717771777177715171777177717771517177717771777000000000000000015171777177717771517177717771777151717771777177700000000000000000000000000000000000000000000000015171777177717770000000000000000151717771777177715171777177717771517177717771777000000000000000015171777177717771517177717771777151717771777177700000000000000001517177717771777151717771777177715171777177717770000000000000000000000000000000000000000000000001517177717771777000000000000000015171777177717771517177717771777151717771777177700000000000000001517177717771777151717771777177715171777177717770000000000000000151717771777177715171777177717771517177717771777

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
  | 2 => 2
  | 3 => 15
  | 4 => 183
  | 5 => 556
  | 6 => 380
  | 7 => 35
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xe64ab731b52875fa
  | 3, 0 => 0xf5db8dc1ef2ac9a7e75249f1cd564e35cad8a662ba9c5354ac5d89c69f8d055f9270be258d0570017b63966372d892a66eacf3782642b73725caac87
  | 4, 0 => 0x46f756a346a2ae6942ff68d642bd25ad416e61073f73a63e3f0fe5c03e3be1b93c4bc5703ae7dd3b373ced52366a19593615a7d735d5b74133611b953007cc792f7891282f56955b2f2e94352f14c9182c1ae0d42aebbf0029a97b0c2964411e28f45a5428eb749c28ce551527ef41a625fd8e3c249c00c2242ac39d1fa8f6e01f0a0bca1eebc50e1e63bc541e1933e61c5b8d2a1bed0a751b46994d1ae8094f192461e518823610176aa6e8174e8d481631da3f1472524e122e1533109d4e900fa64abe0f725e600f370d8e0efe19980e951b5d0cf367570b8402000b6ac4a708d238320827048604f2a0ba033d6adb02d6c4840249d7f1023da77500b7f23c
  | 4, 1 => 0x9b23e8939a0fae499920556397d1b98294b428b7944bd8d09335caa892ac71f592476aa591770c0f905646918cea14918920211f88c61a3d86989c63844da87382584d858083bc997fe224607dee58d578f96c99780d13127605c94c75c39c2475bfd04b73dea18273ac31dc7379c76272d892a6729bf83a7219f71371b8f58e6fc7769d6e54ff456df74ae569f173346335f4c460a29e5b60918fae5ffd9c835fe8c4525fb638fc5f38081e5d3869295c91eb105b4de1ea59a2c6435756b45b5743be4d563891115475080d52865619521496bd515d976650df65274f9a57104d752ff54d3535834d28b9614a3766114a226ad74914bfab485a6aef480d31f4
  | 4, 2 => 0xffe17cb3fd5cb642fa897e6ff96d9945f8b03e0ff767380ef631aa34ef13ee28ee57605eee2abda9e96cd2c3e5e726a5e30accdee1dd0f7fe12b03fbdf850560deb83669ddc0cec9dbc6b03ed99cd475d95d1f8ad7c6a2c1d5ed483fd426b5e6d2820563d1c2f1a7ce58bc75c85c065ac71fa3d4c6d17288c6a11562c5955b59c55d6129c26472cbc218ad9fc1a88f81bff70cecbf52458fba10802db9e1f4b3b9b0dd0db9a6be0ab922cab9b6aa8f66b1e261e0afb4fdefaf1ddbefa86d17d5a7f2d9e7a558e2caa30cecc0a27e12b9a1a012489fb9f2699e741923
  | 5, 0 => 0x1444850e14413ad1143deca314025c3913959da11348c6c8127c71cb124ed709122a92cb120c105b11db3d0f11993160118064be11320eab10c8b20a10a3d1311062c07e104b90990ff9f6800eba6a6f0eb94c4d0e9251660e4a9d820dfe5cfb0d11a3c70d083ea30ca8b9270c8d99530c5da7de0bf735f90b6ac4a70b1c1b940ac1985a0a9a71100a3e34ec091e641408c8fc5d075c21e5074797fc07469d2d072d45fc069aa992067966d405f75c1205cfc0f205a32674057c133905079d8604c7ba9b033e4b26032fefd702fb834102e3fda402e1be8b02d34b4802b1616502aaedf0029a9ffd014f802201476135007a268f00774cc40039a6b300158ee8
  | 5, 1 => 0x2afb43bc2a3b09ac29dbd8bb29bd827a2986ddcd291b99fa28eb749c285f8e0a283c80f127cbd78427c3d472278c7c312749360b272d789726eab1de26d0592525ea212725bde0bf25ae27ea24c0ea3e2445099e2396b9f62367e65522a9cf43226bc946225d58af219c96db21986758210240b9207c5851206267c520384e7d1ff393cc1f88ac351f62cda71f53b75e1f1b18e11e979c851e1933e61db582821d3f5c711d3b4ffe1d02e8bf1be6212b1b9dba741b32625a1b02f68019d11acc193ee19b19236acc18c89abb18b6670718823610183b854717dd34ae179e717d1797c46d173b1762172876cd16ff912416aff2df1697ab5b1689bcd515ad2078
  | 5, 2 => 0x4012c4b93f70a7993f0fe5c03d2aea543d11b5103cecfa2c3c6e2c353c5ee5f03c4bc5703c1e7c193c0f2d4d3b70bb7b3abf83433a81ae0e3a54d9233a2450f0396d0245388afb4e383e1500380f948837e10d5f37df87ad376e9014370620d836b2423f36ad467d36aa9c7e3690e07d35e49e003569f3843414cc1233c644f533b770f4337784113305d20b32fa928832e9cfc93295b41732875fe932766486321fbf92313ee1853117c0bb30f75b382ff05fd42fc353122fa2c13d2f0c468c2eef4e2b2ed765912e7c9b9e2d9ac4ce2d84cd572d6722572d64afb22c661de22c2420712c1ae0d42c0381b12bff8a462bde46682b7214972b6d305f2b67f0a2
  | 5, 3 => 0x59664614594fb40058b1dc62586bd928581ea2b7579cddbd572caec2570a9eef56ff9bfd56d9c5cd563891115607f08a558c84b0554f66b5553383e25518f3f954fbc2075492820e542eb78b539c0fa05371dbbc5355e1ef5351fc7752fc4b1e529e04b65262a391521496bd4f17a59c4ec32d7a4e0b6c544dab7a334d85c8e34d752ff54d28b9614cd27d734c7228124c221f244c091c494beec0234bc6e4c24bac1d164b0e65964af0f9e04ac811114a0c571348ff4f1c488c7c3e488ac5d647de9dfa46ff968746aeac5946566ebd464786ea454f81cd4522470c45097f17437cde6642ddbceb42dadccb42a3442a42581def421e25624102ecb840f6b7ad
  | 5, 4 => 0x77206832760c70607579f71b7554af3a741b52a973be3b61732442e17225f3d571e8760c71e6033f704026ae6f8e1e996f7167936f394fac6e35c0296dd2e00f6d490f446ca7a6736c1818776b8ddc406b3ee0336b287b356b2515166a74cace6a59030a69c89ddd691ea66768a1a65868844b16682b2cec678f144f677b40cb66d7fee366102ad065d8b6aa6519f8d264dea1136472541362e3ee3162a847886246a979621eb3df617580566109979860d74a5960c64ae3605978f65ee3c50f5e10cb5d5dc9d47e5d3869295d2347ab5d1527ee5cf74c8e5bcaba5d5bb617215b9465085b8da7fc5b487a305a7408525a52d9a45a43faff59a2c643596eb743
  | 5, 5 => 0x9123473f9017563590072a938fd903768fca9a5f8f32f67c8ea784348e7125f08e24e2bb8e1371788ddea8608d939c738d6de3648d6904148d0a2ef68cefb1258cea14918c0ac5878bca77798b6926c38aa25fde8a827ae589857bf38945818189452b3888d742b888b30537884ac2de87f5375c866fbed785db3ede8583252a857ed474846ab6ed83d5437e835d4bc183123353824add598225bd8581936d837f5ce00e7f0fb4d47eee38ff7edf3dcc7ecd71ab7e3e45a87d6be99c7cb457d17c19cb2f7c05085d7b5afbcd7b2031be7a7df8557a5247b27a4c2db77a1c8fcd79bb12bb79b0424c7977385f785c116e77fec46077cdfa8b772b55c37726c045
  | 5, 6 => 0xb9493b14b88720f2b78bffa5b4880806b41d5f10b1ed83ecb1e261e0b1859cc9b11c4304b1115783b0c2c4c8afbc7ddaaf8bc489ae826858ae29a11bad7bc9c7ac7a1294ab79a07eaa72fd8ea97ca26ca851033ea74e0150a6943cc3a6593c54a62f58c0a5f7b5e9a5e2bc78a54e7412a407a87fa30cecc0a29d3a31a2414704a1a01248a0d0d81da090506ca06378b39ff3631d9fee66179f0fbc669eeb41389e5251eb9cc1e9559c349d909bc684fa9b1f5dad9b13cb589968ef2a992ddc4b987cff05982994a3975e2de896cb0e84969704749694a88c95b3124194e14b4d94b5f6fe94b428b793f0fa9493c338669352c6009248dd0f912e294a91243b27
  | 5, 7 => 0xddc0cec9ddb05e46dd66d8dedbb2ef70dba147f8db5f6328d9ff1d58d94c4664d8cf2ffbd8b2801ad877e877d7343491d6dd5225d5cb391ed502bc9ad4faa484d477950fd3d05939d3c50b92d2ce3145d2820563d20083c8d1d7a1efd0c474b5cfcf423ecfc1c246cef51af0ce58bc75ce57b6a3cdebb615cda27f3acda009a3cd391f5dcc82e222cc66928fcc4ad4edcaf48779ca51b1a8ca45c933c9dd3719c8467532c838b3a7c67fe1ffc6414af1c478283fc3ae11dac2ec21dbc2e0cc0fc166f57ac0771f31bfc022fdbfa9cb2cbf36db73bf24441abe689983bd427270bcb0ad1ebab6cbfabab13985baab1cf9b9fea4d3b9c3b6d3b9a6be0ab979fffa
  | 5, 8 => 0xfe02700dfc1d67f7f96b052bf83c556af7cdd469f767380ef620cc2bf5c1290bf58e1399f53316b7f4e0edfef3a29fa3f33d612cf2dfc296f255e4b2f0b8680af08533b5f07c6710ef085b7beee82400ee509dfaee3572d3edfdf24cecf3e46fecce0bf6ecbe9d63ec3f522fea91fa24e9a3d2aae80afa11e76ae6dee6f04a92e5215f5de281f377e23102abe182ff50e09f63f0e03a1a1adff04f58df933d5adf8faf73df1d38bedf16b048de3fc603
  | 6, 0 => 0x1abc2eec1a56e65a1a50120619d11acc198f18f3193ee19b18d9ce7117e2c46317a993891688b6b7162b56fb155c926714f1e14714df7bfe14c2cc1d14a546e714a09d7d1414bd5413df1fc613559f251348c6c812ed9e28127c71cb1246545e1236223111db3d0f115249f11135b01b1113089d110af0871087e11210158ff30fe0a53c0fd557950ede7d480eb94c4d0e3300740e10cfcb0d0d097c0d0689680bdf8e410bd20e490b3bf2be0b072a970b0566f309a7457c0992a64e08932e25085949ce083a7159067380d30661fdab0656153605ed831c05a326740529cadd04c2ecd30456c1350448ffaa0423ed79035b419002722d2b0158bfbf00a1cfad
  | 6, 1 => 0x37ef101737e9a492358e184434999f9033de206c3377841133743076335e8ed73305d20b32955ed3323ef1bf31a0a436319e5f9c313ee18530f13a0130eab66f302081c42fdad9f52fb2eba62ef00e992eef4e2b2e5a5d942e339c392cc8b40d2c957fb82c8cb3132c7a9d4f2c2420712b6d305f2b18a77e2af870032a4d93472a45bed62a0e3e4f29cad1e4297574ba29043072284f9e32271da97a26a2462726332ece25b41ead24c0ea3e241b461423f7ccc8231ae6632300969521b65f65218c50e42131ab6020384e7d1f7882e01f403de01ea829cf1e923f7a1d934b531d3f5c711d02e8bf1c4a661d1be6212b1ba3895d1b9ffb761b9dba741b26fc4b
  | 6, 2 => 0x595eaf40594fa86f5864b8855846d2a157f66d2957ae06725742ae585713427e56389111554f2d995533b6ca5518f3f95492820e54669f4d544bd14553ed80ac534b6360530fdd2252aff40c52a7f759529a08d35246a722504c3ad4503381e94ec32d7a4e8cbdc94deb890d4da97d5e4d0299d94cd8fe084c0a427e4ae3fdd74acab66d4ac9984b4a894e8848b90525486df3dc46aabd0e465957b745ff2d314522470c42aaf5904289b2d241e00cf0418c5f374117e98440f6b7ad3fa96a1c3f70a7993ef449a23ebb39ee3e8b3f983d57ad333d11b5103c49f2b13c2356873ac6c4493a12bc1039c1538d398c68d6388a40e23888dc6b38430a12382db3fa
  | 6, 3 => 0x857ed474849cc83c83eee9f8838d4d0583123353830fe28582bef8578257d2e881936d838159ca0c8132930a7eee08e97e6869ed7d0703ab7c2310b77922010e7904d660786f31ee7838816377cdfa8b77974ca7778107797691fa0c766525217554af3a749b474c74755be572bae87c6f161e096e300b906d4f2d836d07a7366c00abd26aff9a296a74cace69776e556974fbb0693e5560687669e06813cdaf680fd644677d7c5d6769b60d674beb076658da75644cccef63d42070633dc49562e0a52361fa6d2561ce2cbd6195682c60d1363c60b7601f609dc611605978f65eb5b46a5c8ca44f5c72b3c35c489a7b5c03dfca5bb617215b4a23365a9cfd9b
  | 6, 4 => 0xb330b430b21cbc5eb1ed83ecb18a4319b164fb38b02b9ea7afce875fadf8c20aac7a1294ab79a07ea9e32c0da9595b42a939e33ea8b7f271a7102701a68516cca468c748a43b78eaa38b8cc9a29d3a31a1b058ada082a0119f06dd369ef43a2f9eeb41389e93bfec9e56f5779968ef2a97c6631f966325a2965446fd95b31241957f03419576921294c2286094b5f6fe942eeeb59352c60093319810931aeaed92ea11cb9248dd0f915fb2b39143cfe0912e294a91293ff791243b27910c0e058f8227ba8f662ded8f3184528f0c971c8e24e2bb8e20b9808c0ac5878b6926c38ad379788a7cf9d68a1bb85289857bf388e2c97186d85d0f861ca31185f45e15
  | 6, 5 => 0xfefc6dd9fd774178fc876b2ff6bb68f7f58e1399f58a4bf8f4e0edfef3a29fa3f0985404edfdcfeaed95e8c7ecf3e46fea92b456ea39ed19e88a5e92e789ec7ce60dacafe4ee0f97e4614f3ce23fa4bee1f30876e15ec010de519302ddb05e46dce1241bdc73c4b1da629de9d8cf2ffbd6e0c801d5793b28d53e2849d439e0a1d3d05939d2ce3145d2a75072d2a4f48ad0c474b5cfd38464cf6311fecda27f3acd348725cc82e222cc27a233ca8171eec77972c1c6b2abdcc4c35135c2882b76c1937128c0771f31bf227f51bec469c9be360983bafe84fdbaef89cab82a172db699e95cb587845db3de4689b33ba1c1
  | 7, 0 => 0xfc876b2fe88a5e92e60dacafd5793b28cf6311fecd348725bf227f51b3de4689b164fb38a68516cc97c6631f9248dd0f91293ff78ad379788132930a7d0703ab7922010e6f161e096aff9a2960d1363c5c489a7b594fa86f57f66d2957ae067256389111554f2d994e8cbdc94deb890d37e9a49230f13a012fb2eba62b6d305f14df7bfe10158ff30fe0a53c
  | 8, 0 => 0x9248dd0f
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0x555500005555000033333333333300000f0f0f0f0f0f00000f0f00000f0f000000ff00ff00ff000000ff000000ff00000000ffffffff00000000ffff000000000000ff00ff0000000000cccccccc00000000aaaaaaaa00000000555555550000000033333333000000000f0f0f0f000000000000ffff0000000000000000
  | 0, 1 => 0xff00000000000000f000f000f000f000cc00cc00cc00cc00aa00aa00aa00aa00550055005500550033003300330033000f000f000f000f0000ffffffffffff0000ffff0000ffff0000ffff000000000000ff00ff00ff000000f0f0f0f0f0f00000f0f00000f0f00000cccccccccccc0000aaaaaaaaaaaa0000555555555555
  | 0, 2 => 0xf0fffffffffffff0f0fffff0f0fffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0000000000000f00ff00ff00ff000f000f000f000f000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0505050505050505030303030303030300ffffffffffffff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00000000
  | 0, 3 => 0x33ff33ff33ff33ff33ff000033ff000033ff0000000000003333ffffffffffff3333ffff3333ffff3333333333333333333333330000000033330000000000003300ff00ff00ff0033003300330033003030303030303030222222222222222211111111111111110fff0fff0fff0fff0fff0fff000000000fff000000000000
  | 0, 4 => 0x777777777777777777770000777700007777000000000000770077007700770070707070707070705f5f5f5f5f5f5f5f55ff55ff55ff55ff5555ffffffffffff5555ffff5555ffff5555555555555555555555550000000055550000000000005500550055005500505050505050505044444444444444443f3f3f3f3f3f3f3f
  | 0, 5 => 0xaa88aa88aa88aa88aa00ff00ff00ff00aa00aa00aa00aa00aa00aa0000000000aa00000000000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a0a0a000000000a0a00000a0a00000a0a0000000000000a000a000a000a00088888888888888888888000088880000888800000000000088008800880088008080808080808080
  | 0, 6 => 0xaaaaaaaaa0a0a0a0aaaaaaaa88888888aaaaaaaa00000000aaaaaa88aaaaaa88aaaaaa88aa88aa88aaaaaa00aa00aa00aaaaa8a8aaaaa8a8aaaaa8a8a8a8a8a8aaaaa0a0aaaaa0a0aaaaa0a0a0a0a0a0aaaa8888aaaa8888aaaa888888888888aaaa0000aaaa0000aaaa000000000000aaa8aaa8aaa8aaa8aaa0aaa0aaa0aaa0
  | 0, 7 => 0xc0c0c0c0c0c0c0c0c0c0c0c000000000c0c00000c0c00000c0c0000000000000c000c000c000c000bbbbbbbbbbbbbbbbafafafafafafafafaaffaaffaaffaaffaaff0000aaff0000aaff000000000000aaaaffffffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaa88aa88aaaaaaaaaa00aa00
  | 0, 8 => 0xcccccc00cc00cc00ccccc8c8ccccc8c8ccccc8c8c8c8c8c8ccccc0c0ccccc0c0ccccc0c0c0c0c0c0cccc8888cccc8888cccc888888888888cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0cc88cc88cc88cc88cc00cc00cc00cc00cc00cc0000000000cc00000000000000c8c8c8c8c8c8c8c8
  | 0, 9 => 0xe0e0e0e0e0e0e0e0ddddddddddddddddcfcfcfcfcfcfcfcfcdcdcdcdcdcdcdcdccffccffccffccffccccffffffffffffccccccccffffffffcccccccccccccccccccccccccccc0000cccccccccc88cc88cccccccccc00cc00ccccccccc0c0c0c0cccccccc00000000cccccc88cccccc88cccccc88cc88cc88cccccc00cccccc00
  | 0, 10 => 0xeeee0000eeee0000eeee0000aaaa0000eeee000000000000eecceecceecceecceecccccccccccccceeaaeeaaeeaaeeaaee00ee00ee00ee00ececececececececececcccccccccccceccceccceccceccceaeaeaeaeaeaeaeaeaeaaaaaaaaaaaaaeaea0000eaea0000eaea000000000000eaaaeaaaeaaaeaaaea00ea00ea00ea00
  | 0, 11 => 0xf0f00000f0f00000f0f0000000000000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f000f000f000f000f0000000f0000000f000000000000000eeeeeeeeeeeeeeeeeeeeeeeecccccccceeeeeeeeaaaaaaaaeeeeeeee00000000eeeecccceeeecccceeeecccccccccccceeeecccc00000000eeeeaaaaaaaaaaaa
  | 0, 12 => 0xf0f0f0f0f0f00000f0f0f0f0f0a0f0a0f0f0f0f0f000f000f0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f0c0f0f0f0c0f0f0f0c0f0c0f0c0f0f0f0a0f0a0f0a0f0f0f000f0f0f000f0f0f000f000f000f0f0e0e0f0f0e0e0f0f0e0e0e0e0e0e0f0f0c0c0c0c0c0c0f0f0a0a0f0f0a0a0f0f0a0a0a0a0a0a0
  | 0, 13 => 0xf8f8f0f0f8f8f0f0f8f8f0f0f0f0f0f0f8f0f8f0f8f0f8f0f5f5f5f5f5f5f5f5f3f3f3f3f3f3f3f3f3f3f3f300000000f3f3000000000000f300f300f300f300f1f1f1f1f1f1f1f1f0fff0fff0fff0fff0f0fffffffffffff0f0f0fff0fff0fff0f0f0f0fffffffff0f0f0f0f0fff0fff0f0f0f0f0f0f0f0f0f0f0f0f0f0f000
  | 0, 14 => 0xfafaaaaaaaaaaaaafafaaaaa00000000fafa0000fafa0000fafa0000f0f00000fafa000000000000faf0faf0faf0faf0faf0f0f0f0f0f0f0faf0f000f000f000faf00000faf00000faf0000000000000faaafaaafaaafaaafa00fa00fa00fa00fa00fa00f000f000fa00f000fa00f000fa00f000f000f000f8f8f8f8f8f8f8f8
  | 0, 15 => 0xfcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0fcfcfcfc00000000fcfcf0f0f0f0f0f0fcfcccccfcfcccccfcfcccccccccccccfcfc0000fcfc0000fcfc000000000000fcf0fcf0fcf0fcf0fcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafafafafafaaaaaaaaafafafafa00000000fafaf0f0fafaf0f0fafaf0f0f0f0f0f0
  | 1, 0 => 0xff00fc00fc00fc00ff00fa00fa00fa00ff00f000ff00f000ff00f000f000f000ff00ee00ff00ee00ff00ee00ee00ee00ff00cc00ff00cc00ff00cc00cc00cc00ff00aa00ff00aa00ff00aa00aa00aa00ff000000ff000000ff00000000000000fefefefefefefefefefefefe00000000fefe000000000000fe00fe00fe00fe00
  | 1, 1 => 0xff05ff05ff05ff05ff00ffffffffffffff00ffffff00ffffff00ff0fff0fff0fff00ff00ffffffffff00ff00ff0fff0fff00ff00ff00ff00ff00ff00ff00f000ff00ff00ff000000ff00ff00fc00fc00ff00ff00fa00fa00ff00ff00f000f000ff00ff00ee00ee00ff00ff00aa00aa00ff00ff0000000000ff00fc00ff00fc00
  | 1, 2 => 0xffaaaaaaffaaaaaaffaaaaaaaaaaaaaaffaa0000ffaa0000ffaa000000000000ffa0ffa0ffa0ffa0ffa0ff00ff00ff00ff88ff88ff88ff88ff88ff00ff88ff00ff88ff00ff00ff00ff80ff80ff80ff80ff55ff55ff55ff55ff55ff00ff00ff00ff33ff33ff33ff33ff11ff11ff11ff11ff0fff0fff0fff0fff0cff0cff0cff0c
  | 1, 3 => 0xffee000000000000ffccffccffccffccffccffccff00ff00ffccff88ff88ff88ffccff00ff00ff00ffccccccffccccccffccccccccccccccffcc0000ffcc0000ffcc000000000000ffc0ffc0ffc0ffc0ffc0ff00ff00ff00ffaaffaaffaaffaaffaaffaaaaaaaaaaffaaffaa00000000ffaaff00ffaaff00ffaaff00ff00ff00
  | 1, 4 => 0xfffafffa00000000fffa000000000000fff0fff0fff0fff0fff0fff0ff00ff00fff0fff000000000fff0ff00fff0ff00fff0ff00ff00ff00fff0ff0000000000fff0f0f0fff0f0f0fff0f0f0f0f0f0f0fff0f0f000000000fff0f000f000f000fff00000fff00000fff0000000000000ffeeffeeffeeffeeffeeffee00000000
  | 1, 5 => 0xffff0000eeee0000ffff0000cccc0000ffff0000cc000000ffff0000aaaa0000ffff000088880000ffff000055550000ffff000055000000ffff000011110000ffff000000ff0000ffff0000000f0000ffff000000000000fffcfffcfffcfffcfffcff00ff00ff00fffc0000fffc0000fffc000000000000fffafffafffafffa
  | 1, 6 => 0xffff050505050505ffff050500000000ffff00ff00ff00ffffff000f000f000fffff0000ffffffffffff0000ffffff00ffff0000fffff0f0ffff0000ffff5555ffff0000ffff00ffffff0000ffff0000ffff0000fff00000ffff0000ffcc0000ffff0000ff000000ffff0000fafa0000ffff0000f0f00000ffff0000f0000000
  | 1, 7 => 0xffff808000000000ffff5555ffff5555ffff555555555555ffff5500ffff5500ffff550055005500ffff3333ffff3333ffff333333333333ffff333300000000ffff1111ffff1111ffff111111111111ffff0f0fffff0f0fffff0f0f0f0f0f0fffff0f0f00000000ffff0c0cffff0c0cffff0c0c0c0c0c0cffff0c0c00000000
  | 1, 8 => 0xffffaa00ffffaa00ffffaa00aa00aa00ffffaa0000000000ffffa0a0ffffa0a0ffffa0a0a0a0a0a0ffffa0a000000000ffffa000ffffa000ffffa000a000a000ffffa00000000000ffff8888ffff8888ffff888888888888ffff888800000000ffff8800ffff8800ffff880088008800ffff880000000000ffff808080808080
  | 1, 9 => 0xffffccccccccccccffffcccc00000000ffffcc88ffffcc88ffffcc88cc88cc88ffffcc8800000000ffffcc00ffffcc00ffffcc00cc00cc00ffffcc0000000000ffffc0c0ffffc0c0ffffc0c0c0c0c0c0ffffc0c000000000ffffc000c000c000ffffc00000000000ffffaaaaffffaaaaffffaaaaaaaaaaaaffffaaaa00000000
  | 1, 10 => 0xfffffc00fc00fc00fffffc0000000000fffffafafffffafafffffafafafafafafffff0f0fffff0f0fffff0f0ffff0000fffff0f0f0f0f0f0fffff0f000000000fffff000fffff000fffff000ffff0000fffff000f000f000fffff00000000000ffffeeeeffffeeeeffffeeeeeeeeeeeeffffccccffffccccffffccccffff0000
  | 1, 11 => 0xffffffff00000f0fffffffff00000000fffffff0fffffff0fffffff0fff0fff0ffffffccffffffccffffffccffccffccffffffaaffffffaaffffffaaffaaffaaffffffaa00000000ffffff00ffffff00ffffff00ff00ff00ffffff0000000000fffffcfcfffffcfcfffffcfcfcfcfcfcfffffcfc00000000fffffc00fffffc00
  | 1, 12 => 0xffffffffc000c000ffffffffaaaaaaaaffffffffaaaa0000ffffffffaa00aa00ffffffffa0a0a0a0ffffffff88888888ffffffff88880000ffffffff80808080ffffffff0f0f0f0fffffffff05050505ffffffff00ff00ffffffffff000f000fffffffff0000ffffffffffff0000ccccffffffff0000aaaaffffffff00003333
  | 1, 13 => 0xfffffffffffff0f0ffffffffffffccccffffffffffffaaaaffffffffffff0000fffffffffff0fff0ffffffffffccffccffffffffffaaffaaffffffffff00ff00ffffffffff000000fffffffff0f0f0f0fffffffff000f000ffffffffeeeeeeeeffffffffccccccccffffffffcccc0000ffffffffcc00cc00ffffffffcc000000
  | 1, 14 => 0xffffffffffffffffffffffffffffff00
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x18aab399ba130733
  | 3, 0, 0 => 0x8431530734a131530734732e93073462a60e65b4daba5307349cb1530734a234530734dab4556734a231530734d2ba93073470af93073482315307349bb15307348631530734a4bc130734
  | 4, 0, 0 => 0xcccf9a29839ac655a9f4c1cd7271968a60e6b558cb1130735a1345749839ae1e32d14c1cd6e11968a60e6b5d8cb45307359db453073312c65a298398c16ab194f9cca8b6c8cb4530735aac65a28d39ac65ccd14c1cd7511963260e6b768cb4530735
  | 4, 0, 1 => 0xcdc65a29839ad5632d1559cd6ab1f68a60e6ba48cb4530735aac65929839ad5632de4c1cd75d1968a60e6b55a9b4530735b0451a29839ad56329f4c1cd74b3e68a60e6b7f8cb4530735aac65a298342c65d6d1401cd76b0462a60e6b1968a60ec735
  | 4, 0, 2 => 0xccb4530732eae7e76d14c1cd6ab195ea60e6b55752e930735dac11a29839ad5632d1522616ab2768a60e6b818cb4530735df4158a9839ad0a32d14c1cd6ab196fa60e6bb59bb4530735aac91a29839ad6232d14c1cd6aae368a60e6b559ab4530735
  | 4, 0, 3 => 0xdf4358c9839aebe32d14c1cd6ab2868a60e6b556c34530735b04659a9839ae960ad14c1cd6ab0c68a60e6b558cb5d30735aac658a9839aea692d14c1cd74ad14c1ccbab1968a60e63d5aac65a29834ad5630d14c1cd6ab19401ccb2b558d34530735
  | 4, 0, 4 => 0xaac65a89839ad5632d14c1cd6b72968a60e6b598cb4530735aab91a29839ad5632d1471cd6ab2970260e6b6f8cb4530735aaca5a29839ad5632d04c1cd632d156a60e6b558cba530735822f9749839ad5632c34c1cd6ab1568a60e6b668231530735
  | 4, 0, 5 => 0xaac658e9839ae2232d14c1cd632d968a60e6b558cb45306b5aac41a29839ad6e32e04c1cd76b4668a60e6bb486b4530735c1465a29839ad5632ff401cd74b4d68a60e6b5b8cb4530735aac65a298362d5632d14e1cd6ab1970260e6b558734530735
  | 4, 0, 6 => 0xaac65a2a52a2d5638d14c1cd7291968a60e6b558cb3930735df39d749839ad5632983992d6ab1968a58e6b3f8cb4530735a4d09a29839aed672d14c1cd6ab1968a8530b0468b1530735004118a9839a4658a983998969d1968a60e6b558231530735
  | 4, 0, 7 => 0xaac65a2a639ad567cc54c1cd73f1962a60e6b5568a60e65e5aac35a29839ad5616d14c1cd73d1963260e6b198231530735aab453073262c65e0be4c1cd6aad150260e6b1975b4530735aad258a9839abadc8d14c1cd76ad14c1ccb6b6e8cb4530735
  | 4, 0, 8 => 0xaab1530732ead55529f4c1cd74b1968a60e6b558cb7530735ce465a29839ae6632d14c1cd6ab0f68a60e6bb58434530735dad09a29839ae0232d14c1cd6ab1964260e6b55a4b4530735d2c31a29839ad5632c64c1cd74b1962a60e6b5568a60e6375
  | 4, 0, 9 => 0xd4c658a9839ad5676d14c1cd70b1970260e6b858cb4530735aacf1a29839ad5632d24c1cd6ab2068a60e6b558cb4530615c2ca5a29839ad4632d14c1cd6aae168a60e6b5582b1530735ab465a29839ac65a2a24c1cd6e31968a60e6b559134530735
  | 4, 0, 10 => 0xd2c11a29839ab455aa94c1cd6ab0068a60e6b558534530735aaca9a29839ad564cd14c1cd6ab4d62a60e6b558cb8100735dac31a29839ad55a298398a56ab1968a00e6b558cb454e735aab91a28039ad25a298399896330168a60e6b1968a60e64d5
  | 4, 0, 11 => 0x67e92d14c1cd6ab1968a18e6b558cb4522735a4c11a29839ac31a2be4c1cd6aad154a60e6b7b8cb4530735
  | 5, 0, 0 => 0xaac65a298459cdaab1968a6112736df59a32d24c1cdb7d578cb4530736aac65a29839941b7d669034530736b346604d14c1cdb7d668cb4530616d6d5632d14c1cdac71968a60e66d6dad9a08d14c1cdaab4d68ae930736b6d5632d14c1cdb7d668b34530736aac65a2983994db7d558a34530736
  | 5, 0, 1 => 0xdf599c4d14c1cdaab197a34500736aac7632d14c1cda32d14c21ce6626df55692d14c1cdb7d558cb1930736e859a32d14c1cdb7d1968a60e64e6aac65a29839959bbd558cb4530736aac65e4d14c1cdaab1968a60e65b6aacf632d14c1cdb7d638cb4530736aac65cad14c1cdaab197fbd130736
  | 5, 0, 2 => 0xaac660cd14c1cdb7d778cb4530736aacea32d14c1cdaaad14c20ce65d6aac65a2be4c1cdb7d669db4530736d8d9a32d14c1cdaab1968a60e66f6df465a298398f9b65558cb4530736aac65a2b739951aab1968a60f8736eed5632d14c1cdb7d838cb45307360057632d14c1cd775558cb4530736
  | 5, 0, 3 => 0xb355618d14c1cdaab1968a60e6106e4d9a32d14c1cdaab1968a60e6116aac657cba4c1cdaab1988b4530736aac65a298398b1aab2e8cb4530736aacc232d14c1cdaab1968a60e60b6005563298398b16ab1968a60e6036b355632c54c1cdb7d9d8cb4530736bd55632d14c1cdabd1968b2930736
  | 5, 0, 4 => 0xaac65a298499cdaab1968a7d30736e259a32d14c1cdb7d1976b450073600556329f4c1cd6ab1968a60e8736aac65a29839971b7d998cb4530736e555632d14c1cdaab1968aa5307368cb456ead4c1cdaab1968a60e63b6bcd5632d14c1cdb2f558cb4530736aac65a2ac4c1cdb7d667234500736
  | 5, 0, 5 => 0xaacc632d14c1cdbab668cb3530736df69632d14c1cdb7da68cb4530736df59a4cd14c1cdb955b8cb45307360069232d14c1cd6ab1968a60e61f6e9d5632d14c1cdb7d668cb8100736cf59a32d14c1cdaab1968a60e6096aad3632d14c1cdaab1968a60f6736aac65a2983981db7d668cb4500736
  | 5, 0, 6 => 0xaac65a29e4c1cdaab1968aed30736b3465a298398c5bb9558cb4530736e7d9a32d14c1cdb491968ae930736df68632c64c1cdacd5594b4530736aac65a2b64c1cdacd1968ab530736aac65a2b24c1cdb7d528cb4530736e3d5632d14c1cdaab508cb4530736da55632d14c1cdaab1968add30736
  | 5, 0, 7 => 0xdad5608d14c1cdb7d668034530736df58628d14c1cda87428cb4530736e8d5632d14c1cdab91968a60e66d60050a32d14c1cd77d558cb3530736aac65a2b94c1cdaab428cb4530736aac65a29839871b59558cb4530736b3555c8d14c1cdb67558cb4530736df435a2bf4c1cdaab1979b4530736
  | 5, 0, 8 => 0x555a298398856cd558cb8130736aac6610d14c1cda32d157ab530736aac65a298479cdaab19689fce6546aad0632d14c1cdaab1968aa130736df57232d14c1cd801b58234530735aac65fcd14c1cdaab198bb4530736dac65a29839989b7d658cb4530736b355632d14c1cdb7d728cb4530736
  | 5, 0, 9 => 0xe0d9a32d14c1cdb7d6668aa530736eb55632d14c1cdacd458cb4530736cf465a298441cdb7d7c8cb4530736df5a632d14c1cdacd1968ac530736aac65a2983993db23558cb4530736df61232d14c1cd801558c9cc742c5aac65e2d14c1cdb15668cb4530736cfc65a298439cdaab338cb4530736
  | 5, 0, 10 => 0xdf59a32d1431cdaab1968a60f2736df55676d14c1cdb4f558cb453073600465a2982306171d558cb4530736df6da1ad14c1cdb7d6a8cb4530736cd66232d14c1cdb7d8694b4530736aac65a2af4c1cdb7d668cb4530716b334568a94c1cdb7d1968a8d30736df61632d14c1cdb7d668cb4524736
  | 5, 0, 11 => 0xaac65a29d4c1cdb7d868cb45307360055618d14c1cd632f275b4530736ec55632d14c1cdaab1968b1530736da68632d14c1cdaab2968a60e65460055632c54c1cd6ab1968a60e6486df62632d14c1cdaab1968a60e6706df58232d14c1cdaab2b8cb4530736aac65a2983986db7d6689b4530736
  | 5, 0, 12 => 0xaacda32d14c1cdaab1968a60e6476cf55632d14c1cdabb1968a6106736bf55632d14c1cdaab1968a60e63c6aac65a29839951a32d15f260e6626df55632d1401cdb8b558cb4530736df61a32e04c1cdb7d5a8cb4530736aac65a298421cdb69668cb1930736df59a329f39951aab1968a60fe736
  | 5, 0, 13 => 0x55652d14c1cd4011968ab530735aac65a2983d1cdacd11652e930736adc65a29839951aab1968ab530736dac6608d14c1cdb7d1968a60ee736df4658c983998db7d668cb1130736df59232d14c1cdb9b558cb4530736aac65d4d14c1cdaab1968a60e6026aac65c09839951acd197734530736
  | 5, 0, 14 => 0xaac65a29839881b7d668ca7d30736aacb232d14c1cdb7d678cb4530736efd5632d14c1cdaab1968ad530736dad567cd14c1cdaab1968a60e6276df58a32d14c1cdb6b9f8cb453073600555c8d14c1cd6ab3b68a610e736aac65a2983988580155689cc74215aac65a29839835b97558cb4530736
  | 5, 0, 15 => 0xaac65a29839815ba9558cb4530736aac65a2984c1cdb7d668cb2530736aac65a29839801b7d1968ab930736aac65a2983983daab438cb4530736b3465689f4c1cdaab1968b45307360055632d14c1cd6cd1988b3530736e359a32d14c1cdaab1968a6114736aac65a298411cdaab558cb4530736
  | 5, 1, 0 => 0xc855632d14c1cdaab4c8cb45307360056e32d14c1cd77d5568aa530736aac65a2983e9cdac71988b4530736dbd9a32d14c1cdaab1968ae930736ead8232d14c1cdaab4968af930736aac65aad14c1cdb7d668fb4530736aac65a2cc4c1cdaab1970345307360055632e04c1cd6ab1968a6d30736
  | 5, 1, 1 => 0xec58632d14c1cdba5558cb4530736aac65a29839961a330468af930736df59a32df4c1cdaab478cb4530736aac65a298398a1ad7558cb4530736aac65b6d14c1cdacd1975b4530736c6d9a32d14c1cdb7d197634530736aac65a2c24c1cdaab1968ae130736df66a32d14c1cdaab198634530736
  | 5, 1, 2 => 0xaaca632d14c1cdaab1968a60e6396df59a34d14c1cdb3f1968af930736df59a32bd4c1cdacd4b68ae930736df599d4ba4c1cdaab348cb4530736c7d5632d14c1cdaab1968a60e6156dad9a22d14c1cdb31668cb4530736dc55632d14c1cdaab1968a60e6556c8c65a29839989aab197b34530736
  | 5, 1, 3 => 0xaac65a2bc4c1cdaab198cb4530736aac65a29839879801558cb44e63a5aac65a29839819aab1968a60f0736dad55a29839975b7d668cb4530696aac65c8d14c1cdb7d668c34530736df6ae32c64c1cdacd558a34530736df59a328039965b7b558cb4530736aac65a2cb4c1cdaab1981b4530736
  | 5, 1, 4 => 0x5563298230b16ab1968a60e6446dad560ad14c1cdb7d668634530736b353e32d14c1cdb17558cb4530736df59a32d74c1cdb43908cb4530736df6c232d14c1cdbb15e8cb4530736aac65a29839869b7d668cb1530736aac65a29839949aab1968a60e63a6f055632d14c1cdbad558a34530736
  | 5, 1, 5 => 0xb352e32d14c1cdb7d668ab4530736df69232d14c1cdaab1968a60e6126aac65e8d14c1cdae7668cb4530736ebd5632d14c1cdaab1968afd30736d155632d14c1cdb7d669434530736aabd1c8d14c1cdac3558cb4530736df599b0d14c1cdb7d558ca7d30736e059a32d14c1cdbad638cb4530736
  | 5, 1, 6 => 0x465d6d14c1cd751668cb4530736aac65d6d14c1cdaab1968a60e6626aac65a298399cdb91668cb4530736df59a52d14c1cdb7d668cb4130736004653073160616cd408cb4530736aac65a29839925acd488cb4530736aac65a2984a1cdaab195fae930736aac6624d14c1cdaab218cb4530736
  | 5, 1, 7 => 0xaac11a2ba4c1cdaab1968a610a736bc59a32d14c1cdaab1968a60e62e6df5a232d14c1cdaab1968a60e60e6df50a32d14c1cdaab1968a612e736df599c8d14c1cdb3f918cb4530736aac65f4d14c1cdb7f668cb4530736df59a32d1471cdb6ba98cb4530736df3b5c8d14c1cdb7d6694b8130736
  | 5, 1, 8 => 0xaac65a2984a9cdaab1968a60e65f6df59a32d14e1cdaab1968a60e6166aac65307f39965aab388cb4530736df59a32e04c1cdaab1968a60e62a6b3465a2b44c1cd8015586b4530735df465ced14c1cdaab197ab4530736e755632d14c1cdb7d668cb4530736df465dad14c1cdaab1968a6106736
  | 5, 1, 9 => 0x55632c64c1cd6ab258cb4530736c259a32d14c1cdaab1968a65307368cb4568af4c1cdb3d928cb4530736aac65a2983a9cdb7da78cb4530736aac65b8d14c1cdb73558cb4530736aac65f8d14c1cdb7d668cbfd00736dad569ad14c1cdb95868cb4530736aac65a2983998d8015568a608c215
  | 5, 1, 10 => 0xaac65a29839965aab198234530736aac65a2c04c1cdbb1558cb3530736aac65a2aa4c1cdaab378cb4530736d4c65a2be4c1cd800d14c1cc42185aac65a29839865b7d5f8cb4530736aac65a298398adaab1968a60e6366b3465b4d14c1cd80155a4b4530735e1d9a32d14c1cdaab1968b1930736
  | 5, 1, 11 => 0xaac65a29839995b4b558cb4530736bed5632d14c1cdaab1986b4530736df59a32983992db3f558cb45307360066632d14c1cd6ab197bb4530736a5d0e32d14c1cdaab1968a60e6666ccd5632d14c1cdb7d668cb4542986aacca32d14c1cdaab1968a60e6326f0d5632d14c1cdb2b668cb4530736
  | 5, 1, 12 => 0xaab456ea94c1cd801558cb4530465eae9e32d14c1cdaab197c34530736aac65f2d14c1cdb4b1968ae930736df59a32d152951b0b1968a60e6546ddd5632d14c1cdaab1968ac130736ba55632d14c1cdaab1968a60e6136df59a32ce4c1cda32f475b45307360069632d14c1cd6ab3e68ae930736
  | 5, 1, 13 => 0xc2d5632d14c1cdaab1968a60e6186df599a2a04c1cdb79558cb4530736aac65a29839851aab1968a9530736aac65a29839889aab1968a60e65a6aac65a29839909aab3e9a34530736e159a32d14c1cdaab1e8cb4530736aac65a298398e1aab1968a6102736aac65fe983f9cdaab498cb4530736
  | 5, 1, 14 => 0xaac65a298399c9aab3e8cb4530736aac65a29839981aab1968a610e7360055676d14c1cd6ab1968a60e6436aac65a298398bdb7d6686b4530736aac65f6d14c1cdaab1984b4530736aac65a298398cd801858cb4530735df599a29839931ba39a8cb453073600465a298398616ab1968a60e6646
  | 5, 1, 15 => 0x55632d1401cd77d668cb1930736df69e1ad14c1cda32f276b4530736dad5632c54c1cdb2d558cb4530736aac65a298399a9aaad15d260e65d6aac65fed14c1cdaab197a260e6596aac65e0d14c1cdb7d668cb454c736aac65a2cf4c1cdb53558634530736aac65a29839895aab1968a60e6246
  | 5, 2, 0 => 0xaac8e32d14c1cdaab3468a60e65d6aac65a2983988daab196b34530736aac65a6d14c1cdaab195ba7d30736d4465a2bf4c1cdaab0568ae930736b357632d14c1cdaab1968a6100736aad1a32d14c1cd801558cb448c3a5aac65a29839915b7d66a4b4530736aac65a29839901aab1968a60e6356
  | 5, 2, 1 => 0xaace632d14c1cdaab1968a60e63f6aacee32d14c1cdaab1968a60e60a6aac65a29839929aab1968a60e6416aac65a29839875aab3e68a6106736a6d0a32d14c1cdaab1968a60e6016d555632d14c1cdb53558cb4530736ccc65a298419cd80119689cc74185aac65a29839899801554c1cc58215
  | 5, 2, 2 => 0xaad5232d14c1cdaab1968a60e6346aac65ded14c1cdaab1968a6930736aac65a298399458015568aa530735df59a44d14c1cdb7d6654a7d30736dad5632d14c1cdb7d668cb7530736aac65a29839919aab1968a60e65d6
  | 6, 0, 0 => 0xe1efacd1968a60e6fd6b355632d14c1cdf2366aac65a29839befacd1968a9530737df59a32d14c1cc44fbeb3465a29839969c01beb1c65a29839b0037d19689cc74176df59a32d14c1cc10fbeb3465a29839909f7d669f4d1a29839b802cd5568a60e6216df68632d15fa60e6fbebad9a32d14c1cdf7d66ae465a29839bd9acd558cb4530737
  | 6, 0, 1 => 0xdf59a7d1968a60e6fbeb3465a29839981f7d668cb45308739b802ab1968af930736df59a32d14c240e6fbeb3465a2983990decd1968b29307336bf337d668cb4530737df59a32fb68a60e6fbeb346612d14c1cdf7d668dc65a29839befacd2d8cb4530737df59a32d14c1cc66f668cbd1e4d14c1cdf7d668cb4530732bbefacd1968a60e6187
  | 6, 0, 2 => 0xed6facd1968a60e6fbec955632d14c1cdf7db6d0c65a29839befacd197eb453073700556331168a60e6dbeb3465a2cf4c1cdc01558cb453073163762cd558cb4530737df55632d14c1ccb2e00005563298398b177d668cb45669839befaab198234530737df59a32d14c1cc4afbeb3465a29839891f7d668cb453073393efacd1968b2930737
  | 6, 0, 3 => 0xdf59a330768a60e6f66aac65a29839951f7d668cb4530731ab8037d668cb4500736df6dacd1963260e6e00aac65a298499cdbabbeb3465a29839befacd1968a60e62d7df67eab1968a60e6f66aac65a298441cdecd558cb45307f39befaccd15d260e65d7df59a32ca5d260e6fbeb3465fed14c1cdf7d668cbd130732cbefb0d668cb4530737
  | 6, 0, 4 => 0xdf59a32d14c1cccefbeb3465a6d14c1cdc01558cb456e9839b76f7d668cb4530737df59a32d14c1f8e6fbeaac65a298399b5f7d668cadd3e9839befacd0568ae9307370074eab1968a60e6c00cf59a32d14c1cdb7d668cb45308039b802ab1968a60e6096006facd196891874dbeb3465a29839915c0155a6c65a29839b6facd1968a60e6407
  | 6, 0, 5 => 0xdf59a32d14c1cc02fbed559a32d14c1cdf7d668cb453073023802d71968a60e6096df6a6cd1968a60e6fbeb3465a29839899f7d8cb3465a29839b8037d664c1cc58216006faab1968a608cdbeb348e32d14c1cdc01dcaac65a29839b6facd3468a60e65d7b355632d14c1cc42fbeb3465a29839831f7d668cb59a29839befb47668cb4530737
  | 6, 0, 6 => 0xdf687251968a60e6fbeb3465a298399b9f7d668cb4530732ebefacd1968a60e63f700002aad14c1cc42bbec3465a29839951f7d6697c65a29839befacd1968a60e60a7df59a32d14c1cc94fbeb3465a29839905f7d66a5465a29839b8037d5c8cb45307360059aab1968a60e6dbeb3465a29839875f7d669f345308339bd9aab558cb4530737
  | 6, 0, 7 => 0xd0e7acd1968a60e6fbeb34660ad14c1cdf7d9ab3465a29839befacd1968a6118737df59a32d14c1cca2e00df599a2a94c1cdbb3beb3465a29839b8037d1968a60e61860075aab1968a60e6db6da59a32d14c1cdf7d558cb4530730c3efacd1968b0530737df6d6cd1968a60e6e00c8d5632d14c1cdb7d668cb453073233d9aab1968ae930737
  | 6, 0, 8 => 0x6fb0d1968a60e6dbeb3465a29839941f7dadb3465a29839befaab197fb4530737df59a9ad15d260e6e00ec55632d14c1cdb7d668cb45307329befb6d1968a60e6637e8d9a32d14c20ce6fbeb355232d14c1cdf7d558cb45949839befaab3e8cb4530737df55632d14c21ce6fbed5d9a1ad14c1cdf7da0b3465a29839befacd1968a60e6347
  | 6, 0, 9 => 0xdf599a298419ccbafbeb3465a2be4c1cdc0166aac65a2731d36facd1968adce6547eeefacd1968a60e6fbeb3465e8d1401cdf4366aac65a29839b80232d14c1cc2e0960055632d14c1cca8ddedf59a32d14c1cdf7d668cbc9a29839befacd3d8cb4530737df59a32e568a60e6fbeb3465fef44c1cdc01558cb45307f39b59aab348cb4530737
  | 6, 0, 10 => 0xdf59a32d154a60e6fbeb3465a298398edf7da9aac65a29839befb2f668cb4530737df59a32d156260e6f668cb453093399b5c01be8cb4530460bb6fb571968afd307370055632d14c1cc42dbeb3465a298398b1c01beb346530731636facd1968a60e6037b355632d14c1cc74fbebd59a32d14c1cdf7d669d465a29839bd9a9b4b8cb4530737
  | 6, 0, 11 => 0xdf55632d14c1ccbafd3df59a32d14c1cdf7d928cb45307331bd9aab197a34530737df59a32d14c1cc12fbeb353632d14c1cdf7d668cb45307b39befacd1968a60e607700002ab1968a60e6bbeb3465a298499cdf7d668cb453e9839b802ab558cb4530736006facd194fa60e6d66aac65a2983985df7d668cb45307439befacd1968a60e65c7
  | 6, 0, 12 => 0xdf59a32f368a60e6fbeb3465a29e4c1cdf7d668cb45769839befaab1982b4530737ee6facd1968a60e6fbedb6ae32d14c1cdecd558cb4530733138037d9a8cb4530736b3465a2b75a260e6fbeb354232d14c1cdf7db4b3465a29839befacd1968add30737df59a631968a60e6e00aac65a2ba4c1cdb7db5aac65a29839befaab1968a60e6467
  | 6, 0, 13 => 0xdf59a32f168a60e6e00df599a29839885801559a465a29839b6facd19689fce6547df59a831968a60e6fcedf57232d14c1cdf7d668cb45509839befacd197f34530737df59a331768a60e6fbeb359a32d14c1cdecd1988b45949839bedacd558cb4530737b355632d14c20ce6fbeb3465a2b94c1cdf7d668cb4530730e3efb67668cb4530737
  | 6, 0, 14 => 0xdf556331168a60e6fbeb34a5a29839951f7d558cb453073163802ab1968a60e63a6006faab194c1cc58dbeb3465a298399c1f7d6695c65a29839befacd1968a60e61b700002ab19689cc74bbeb3465a2983c9cdf7d558cb457c9839befacd1968abd30737eb6facd1968a60e6fbeb3465a2983993df7d91b3465a29839b8037d668c9cc742c6
  | 6, 0, 15 => 0x59a971968a60e6dbeb3465c09839951f7d669b465a29839be4acd558cb45307370055632f468a60e6dbeb3465a2983991df7d9eb3465a29839befafd668cb45307370055632d15fa60e6dbeaad3632d14c1cdf7d668cb4530732a3f177d668cb4530737df59a32d14c210e6fbeb3465a2983f9cdf7d668cb453a9839bf637d668cb4530737
  | 6, 1, 0 => 0xefefacd1968a60e6fbeb3465a2b54c1cdf7d6b8cb45307304befacd1968a60e6277006facce468a60e6d66aac65a298399b5c01a8b3465a29839b002ab1968a60e6626df59a32d14c1cc42fdcdf55632d14c1cdc01beb3344e63a10b0037d6694b4530736df59a32d14c1e8e6fcddf59a32d14c1cdf7d668cba9a29839befaab1968add30737
  | 6, 1, 1 => 0xdf59a32d14da60e6fbeb3465a29839815f7d668cb45309839b802cd1968ad130736df59a32d14c1cc00e00e755632d14c1cdb5766aac65a29839befacd438cb4530737df59a32d168a60e6e00df59a32d14c1cdb7d668cb45308a39befacd1968a6104737006fa32ed68a60e6dbeb355632d14c1cdc01558cb45308339b6facd1968a60e6207
  | 6, 1, 2 => 0xdf69e32d15d260e6fbeb3465a29839955f7d668cbd9a29839b80387668cb4530736006fa3298398b02edbeb351e32d14c1cdc01668cb4530730436facd1968a60e6287006fb4f1968a60e6dbedb4660ad14c1cdf7d668cb6da29839b802ab1968a60e6636df59a32d15d260e6fbeb3465a2cc4c1cdf7d668cb81a29839b8037d668cb8130736
  | 6, 1, 3 => 0xdf59a32d15e260e6fbeb346632d14c1cdc019faac65a29839b6facd1968a60e61e7006facd19689cc74dbeb3465a29839819f7d668cb45307839befacd1972345307370055632d14c1ccb2c00aac6608d14c1cdb7d668cc0da29839befacd298cb4530737b355632d165260e6fbeb3465a298398e5f7d558cb45308839befacd348cb4530737
  | 6, 1, 4 => 0xdf59a32d14c1ccc4fbeb3465a298399cdf7d668cb45307324bf5b7d618cb4530737df59a431968a60e6e000055632d14c11977d668cbd1a29839b8037cd14c1cc42176ebefacd1968a60e6fbeb33d1c8d14c1cdf7d66b0c65a29839b8037d668ca608c2c6e9d9a32d14c24ce6fbeb3465a29839869f7d668cb4530731d3f837d668cb4530737
  | 6, 1, 5 => 0xdf686ab1968a60e6fbeb3465a2983998dc01beb3345304610b6facd1968a60e65f7005567d1968a60e6c00aac65a298439cdb7d668ca60fe732cbefacd388cb4530737006facd0d68a60e6dbeb3465ead14c1cdf9dbeb3465a29839b800011968a60e6185df59a32d14c20ce6e00aac65a29839861b7d668cb45308539befacd1968a612e737
  | 6, 1, 6 => 0xdf59a32d14c1cc64fe1df59a32d14c1cdf7d668cb4530732cbefacd198234530737006fa32d14c1cc2edbeaac65a2983985df7d668cb45549839befacd1968a60e6197df59a32d14c1cc56fbeb3465a298398d9f7d668cb458c9839b8037d668cb1930736df59a4b1968a60e6fbeb3465a2994c1cdf7d668cb71a29839b802ab197fb4530736
  | 6, 1, 7 => 0xdf59a32ff4c1fce6fbeb33456ea94c1cdc01beb3465a2982336facd1968a60e6137006d6ab1968a60e6dbeb34f9a2ba4c1cdc01558cb453073233002ab1968a60e65d6df59a330d68a60e6fbecfd9a32d14c1cdf7d668cbdda29839b80353558cb4530736
  | 7, 0, 0 => 0x7737d668cb4530737006facd1968add307370074f7d668cb4530737006facd1968a60e6097006facd4d8cb45307370000001558cb4530735006facd1968a6126737006facd1968a60e62c7000037d668ca60e62c6006facd1982b4530737006facd1968a60e6467006facd1968a60e65d700002cd558cb4530736006facd197fb4530737006facd1968b2930737006facd3e8cb4530737
  | 7, 0, 1 => 0x6facd1968a60e66370073b7d668cb4530737006facd1968a6106737006facd197a34530737006facd1968a60e63a7000037d668cb44e63a6006facd348cb4530737006facd1968ae930737000037d668cb4530736006facd558cb4530737006facd1968a60e6217006facd1968a60e6547006facd1968a60fe737007637d668cb45307370075b7d668cb4530737000037d6668a60e6216
  | 7, 0, 2 => 0x37d668cb4530466006facd1968a60e6597000037d1968a60e6176
  | 8, 0, 0 => 0x37d668cb4530736
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

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1024), (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]

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
private theorem z2_0 : span (Z 2) 2 0 = true := by decide +kernel

private theorem z2 : span (Z 2) 2 0 = true := z2_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : span (Z 3) 15 0 = true := by decide +kernel

private theorem z3 : span (Z 3) 15 0 = true := z3_0

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
private theorem z4_168 : span (Z 4) 15 168 = true := by decide +kernel

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

private theorem z4_a7 : span (Z 4) 183 0 = true :=
  span_join (f := Z 4) (a := 168) (o := 0) (b := 15) z4_a6 z4_168

private theorem z4 : span (Z 4) 183 0 = true := z4_a7

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
private theorem z5_552 : span (Z 5) 4 552 = true := by decide +kernel

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

private theorem z5_a23 : span (Z 5) 556 0 = true :=
  span_join (f := Z 5) (a := 552) (o := 0) (b := 4) z5_a22 z5_552

private theorem z5 : span (Z 5) 556 0 = true := z5_a23

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
private theorem z6_360 : span (Z 6) 20 360 = true := by decide +kernel

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

private theorem z6_a15 : span (Z 6) 380 0 = true :=
  span_join (f := Z 6) (a := 360) (o := 0) (b := 20) z6_a14 z6_360

private theorem z6 : span (Z 6) 380 0 = true := z6_a15

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

def CG : Circuit := ⟨[⟨GateOp.and, [4, 5]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.and, [11, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12419

theorem PEqualNP.Outside.L_meta_12419 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132424 * 2 ^ 32 + 3901286536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132424 * 2 ^ 32 + 3901286536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12419.mainG PEqualNP.Outside.L_meta_12419.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12419.CG, PEqualNP.Outside.L_meta_12419.CG_mono, by
      have : PEqualNP.Outside.L_meta_12419.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12419.CG_eval⟩
