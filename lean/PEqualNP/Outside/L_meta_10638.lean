import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10638

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
namespace Restrict
abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool
/-! Section 1: Self-contained circuit simplification, relabeling, and gate elimination -/
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]
theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp
theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]
theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp
theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp
def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅
theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]
theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _
def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}
def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false
theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj
theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card
theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega
theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this
theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g
theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]
def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)
theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega
theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]
abbrev Stat := Sum Bool ℕ
def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false
def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m
def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)
def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)
def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)
def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])
theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega
def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g
theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg
theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg
theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]
theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc
theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]
theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega
theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)
theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp
theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)
theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega
theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega
theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h
theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false
theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2
theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)
def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]
theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)
theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩
theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp
theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj
theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]
theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this
def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m
def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩
def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false
theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)
theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]
theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this
end Restrict

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

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (ka : Bool) := 2 * ws.idxOf a + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j * (j + 1) / 2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && (f (tagU ws a false) ((a ^^^ m) :: ra) || (slack ≥ 2 && f (tagU ws a true) ((a ^^^ m) :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) ||
            (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {m y a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun m y s ((a ^^^ m) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ t ys, NatRun m y s ys → f t ys = true) :
    next m (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s + 2 - ws.length := by omega
    simp [ht, hsl2]

theorem next_two_sorted {m y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ t ys, NatRun m y s ys → f t ys = true) :
    next m (s + 2 - ws.length) ws f = true := by
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
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem next_two {m y a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ t ys, NatRun m y s ys → f t ys = true) :
    next m (s + 2 - ws.length) ws f = true := by
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

theorem next_complete {m y t ws} (h : NatRun m y t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ tag ys, NatRun m y s ys → f tag ys = true) →
      next m (s + 2 - zs.length) zs f = true := by
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
  · simp [h, invF]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h, meetF]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h, joinF]
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
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;> grind
    · exact hw _ (by simp [ht])

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
  | perm hp _ ih =>
    rw [← (hp.map v).sum_eq]
    exact ih (hp.length_eq.trans hl)
  | one save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    rename_i s' a b rest
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have h1 := ih (by simp [kept]; omega)
    simp only [kept, Bool.false_eq_true, ite_false, List.map_cons, List.sum_cons] at h1 ⊢
    cases conj
    · have := hor a b; simp only [Bool.false_eq_true, ite_false] at h1; omega
    · have := hand a b; simp only [ite_true] at h1; omega

def scoreV6 (tp : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (w : ℕ) : ℕ :=
  value6 (w.testBit tp.1) (w.testBit tp.2.1) (w.testBit tp.2.2.1)
    (w.testBit tp.2.2.2.1) (w.testBit tp.2.2.2.2.1) (w.testBit tp.2.2.2.2.2)

theorem scoreV6_and (tp : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (a b : ℕ) :
    scoreV6 tp (a &&& b) ≤ scoreV6 tp a + scoreV6 tp b := by
  simp only [scoreV6, Nat.testBit_and]
  exact value6_and _ _ _ _ _ _ _ _ _ _ _ _

theorem scoreV6_or (tp : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (a b : ℕ) :
    scoreV6 tp (a ||| b) ≤ scoreV6 tp a + scoreV6 tp b := by
  simp only [scoreV6, Nat.testBit_or]
  exact value6_or _ _ _ _ _ _ _ _ _ _ _ _

def v6OK (v6 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) (ws : List ℕ) : Bool :=
  v6.all fun tp => Nat.ble 3 ((ws.map (scoreV6 tp)).sum)

def v6PrsOK (y : ℕ) (v6 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) : Bool :=
  v6.all fun tp => Nat.ble 3 (scoreV6 tp y)

def isort (l : List ℕ) : List ℕ := l.insertionSort (· ≤ ·)

inductive BT where
  | e : BT
  | n : BT → List ℕ → List ℕ → BT → BT

def leqL : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: s, b :: t => Nat.beq a b && leqL s t
  | _, _ => false

theorem leqL_eq : ∀ a b : List ℕ, leqL a b = true → a = b
  | [], [], _ => rfl
  | a :: s, b :: t, h => by
      simp only [leqL, Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1, leqL_eq s t h.2]
  | [], _ :: _, h => by simp [leqL] at h
  | _ :: _, [], h => by simp [leqL] at h

theorem leqL_self : ∀ a : List ℕ, leqL a a = true
  | [] => rfl
  | a :: s => by simp [leqL, leqL_self s]

def ltL : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => Nat.blt a b || (Nat.beq a b && ltL s t)

def BT.mem : BT → List ℕ → Bool
  | .e, _ => false
  | .n l k _ r, x => leqL x k || (if ltL x k then l.mem x else r.mem x)

def BT.allOK (p : List ℕ → List ℕ → Bool) : BT → Bool
  | .e => true
  | .n l k h r => l.allOK p && p k h && r.allOK p

theorem BT.allOK_n {p l k h r} (hl : l.allOK p = true) (hm : p k h = true) (hr : r.allOK p = true) :
    (BT.n l k h r).allOK p = true := by simp [BT.allOK, hl, hm, hr]

theorem BT.mem_allOK : ∀ (T : BT) (p : List ℕ → List ℕ → Bool), T.allOK p = true →
    ∀ x, T.mem x = true → ∃ h, p x h = true
  | .e, _, _, _, hx => by simp [BT.mem] at hx
  | .n l k h r, p, hall, x, hx => by
    simp only [BT.allOK, Bool.and_eq_true] at hall
    simp only [BT.mem, Bool.or_eq_true] at hx
    rcases hx with he | hm
    · exact ⟨h, leqL_eq x k he ▸ hall.1.2⟩
    · split at hm
      · exact BT.mem_allOK l p hall.1.1 x hm
      · exact BT.mem_allOK r p hall.2 x hm

def accD (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => Nat.lor (Nat.xor w (Nat.shiftRight w d)) (accD d t)

def accM (q : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => bif Nat.testBit w q then accM q t else Nat.lor w (accM q t)

theorem accD_of (d i : ℕ) : ∀ (ws : List ℕ) (w : ℕ), w ∈ ws → w.testBit i ≠ w.testBit (d + i) →
    (accD d ws).testBit i = true
  | [], w, hw, _ => by simp at hw
  | u :: t, w, hw, hne => by
      have e : accD d (u :: t) = (u ^^^ (u >>> d)) ||| accD d t := rfl
      rw [e, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_shiftRight, Bool.or_eq_true]
      rcases List.mem_cons.1 hw with rfl | hw'
      · left; cases h1 : w.testBit i <;> cases h2 : w.testBit (d + i) <;> simp_all
      · right; exact accD_of d i t w hw' hne

theorem accM_of (q p : ℕ) : ∀ (ws : List ℕ) (w : ℕ), w ∈ ws → w.testBit p = true →
    w.testBit q = false → (accM q ws).testBit p = true
  | [], w, hw, _, _ => by simp at hw
  | u :: t, w, hw, hp, hq => by
      rcases List.mem_cons.1 hw with rfl | hw'
      · have e : accM q (w :: t) = w ||| accM q t := by simp [accM, hq]
        rw [e, Nat.testBit_or, hp, Bool.true_or]
      · have ih := accM_of q p t w hw' hp hq
        cases hu : Nat.testBit u q
        · have e : accM q (u :: t) = u ||| accM q t := by simp [accM, hu]
          rw [e, Nat.testBit_or, ih, Bool.or_true]
        · have e : accM q (u :: t) = accM q t := by simp [accM, hu]
          rw [e, ih]

theorem land_sub {R X i : ℕ} (h : Nat.beq (Nat.land R X) R = true) (hi : R.testBit i = true) :
    X.testBit i = true := by
  have he : (R &&& X) = R := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and] at h2
  exact h2

theorem land_of {R X : ℕ} (h : ∀ i, R.testBit i = true → X.testBit i = true) :
    Nat.beq (Nat.land R X) R = true := by
  have he : (R &&& X) = R := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : R.testBit i
    · rfl
    · rw [h i hi]; rfl
  exact Nat.beq_eq_true_eq _ _ ▸ he

theorem land_zero {R X i : ℕ} (h : Nat.beq (Nat.land R X) 0 = true) (hi : R.testBit i = true) :
    X.testBit i = false := by
  have he : (R &&& X) = 0 := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and, Nat.zero_testBit] at h2
  exact h2

def distOK (pD : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pD.all fun dr => Nat.beq (Nat.land dr.2 (accD dr.1 ws)) dr.2

def monoOK (pM : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pM.all fun qp => Nat.beq (Nat.land qp.2 (accM qp.1 ws)) qp.2

def via (y : ℕ) (pD pM : List (ℕ × ℕ)) (v6 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) (t : ℕ) (ws : List ℕ) : Bool :=
  Nat.ble ws.length (t + 1) && (t != 0 || leqL ws [y]) && distOK pD ws &&
    (ws.length != t + 1 || (monoOK pM ws && v6OK v6 ws))

def prsOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (v6 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) : Bool :=
  pD.all (fun dr => Nat.beq (Nat.land dr.2 (Nat.xor y (Nat.shiftRight y dr.1))) dr.2 &&
    Nat.beq (Nat.land dr.2 (Nat.xor m (Nat.shiftRight m dr.1))) 0) &&
  pM.all (fun qp => Nat.beq (Nat.land qp.2 y) qp.2 && !Nat.testBit y qp.1) &&
  v6PrsOK y v6

theorem via_sound {m y : ℕ} {pD pM : List (ℕ × ℕ)} {v6 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hp : prsOK m y pD pM v6 = true) {t : ℕ} {ws : List ℕ} (h : NatRun m y t ws) :
    via y pD pM v6 t ws = true := by
  simp only [prsOK, v6PrsOK, Bool.and_eq_true, List.all_eq_true] at hp
  have hl := run_len h
  simp only [via, Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨⟨⟨by rw [Nat.ble_eq]; exact hl, ?_⟩, ?_⟩, ?_⟩
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · right; rw [zero_done h rfl]; exact leqL_self _
    · left; simp only [bne_iff_ne, ne_eq]; omega
  · simp only [distOK, List.all_eq_true]
    intro dr hdr
    apply land_of
    intro i hi
    have h12 := hp.1.1 dr hdr
    have hy : (y ^^^ (y >>> dr.1)).testBit i = true := land_sub h12.1 hi
    have hmx : (m ^^^ (m >>> dr.1)).testBit i = false := land_zero h12.2 hi
    simp only [Nat.testBit_xor, Nat.testBit_shiftRight] at hy hmx
    have hmm : m.testBit i = m.testBit (dr.1 + i) := by
      cases h1 : m.testBit i <;> cases h2 : m.testBit (dr.1 + i) <;> simp_all
    by_contra hc
    have hall : ∀ w ∈ ws, w.testBit i = w.testBit (dr.1 + i) := by
      intro w hw
      by_contra hne
      exact hc (accD_of dr.1 i ws w hw hne)
    have := run_bits h i (dr.1 + i) hmm hall
    rw [this] at hy; simp at hy
  · by_cases hlen : ws.length = t + 1
    · right
      constructor
      · simp only [monoOK, List.all_eq_true]
        intro qp hqp
        have h1 := hp.1.2 qp hqp
        simp only [Bool.not_eq_true'] at h1
        apply land_of
        intro p hpP
        have hyp : y.testBit p = true := land_sub h1.1 hpP
        by_contra hc
        have hle : ∀ w ∈ ws, w.testBit p ≤ w.testBit qp.1 := by
          intro w hw
          cases h2 : w.testBit p
          · exact Bool.false_le _
          · cases h3 : w.testBit qp.1
            · exact absurd (accM_of qp.1 p ws w hw h2 h3) hc
            · exact le_refl _
        have := bits_le h hlen p qp.1 hle
        rw [hyp, h1.2] at this
        exact absurd this (by decide)
      · simp only [v6OK, List.all_eq_true]
        intro tp htp
        have h3 : 3 ≤ scoreV6 tp y := by
          have := hp.2 tp htp
          rwa [Nat.ble_eq] at this
        have hb := score_bound h hlen (scoreV6 tp) (scoreV6_and tp) (scoreV6_or tp)
        rw [Nat.ble_eq]
        omega
    · left; simpa using hlen

def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

theorem run_act {m y : ℕ} (pi : List ℕ) (hm : actL pi m = m) (hy : actL pi y = y) {t : ℕ}
    {ws : List ℕ} (h : NatRun m y t ws) : NatRun m y t (ws.map (actL pi)) := by
  have h2 := Run.map (actL pi) (inv' := (· ^^^ m)) (meet' := (· &&& ·)) (join' := (· ||| ·))
    (fun a => by simp only [actL_xor, hm]) (fun a b => actL_and pi a b) (fun a b => actL_or pi a b) h
  rwa [hy] at h2

def symOK (m y : ℕ) (G : List (List ℕ)) : Bool :=
  G.all fun pi => Nat.beq (actL pi m) m && Nat.beq (actL pi y) y

theorem symOK_mem {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) {pi : List ℕ}
    (hpi : pi ∈ G) : actL pi m = m ∧ actL pi y = y := by
  have := List.all_eq_true.1 hG pi hpi
  simp only [Bool.and_eq_true] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

def hlookup (tag : ℕ) : List ℕ → Option ℕ
  | [] => none
  | p :: ps => if Nat.beq (p / 16) tag then some (p % 16) else hlookup tag ps

def hfind (G : List (List ℕ)) (T : BT) (t : ℕ) (h : List ℕ) (tag : ℕ) (ys : List ℕ) : Bool :=
  match hlookup tag h with
  | some j =>
    match G[j]? with
    | some pi => T.mem (t :: isort (ys.map (actL pi)))
    | none => false
  | none => false

theorem hfind_false {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) (T : BT) (t : ℕ)
    (ih : ∀ ws, NatRun m y t ws → T.mem (t :: isort ws) = false)
    (h : List ℕ) (tag : ℕ) {ys : List ℕ} (hys : NatRun m y t ys) : hfind G T t h tag ys = false := by
  unfold hfind
  split
  · split
    · rename_i pi hpi
      have hmem : pi ∈ G := List.mem_of_getElem? hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hmem
      exact ih _ (run_act pi hm hy hys)
    · rfl
  · rfl

def stepOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (v6 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) (G : List (List ℕ)) (T : BT) :
    List ℕ → List ℕ → Bool
  | [], _ => false
  | 0 :: _, _ => false
  | (t + 1) :: es, h => !(next m (t + 2 - es.length) es
      (fun tag ys => via y pD pM v6 t ys && !T.mem (t :: isort ys) && !hfind G T t h tag ys))

theorem closure_sound {m y : ℕ} {pD pM : List (ℕ × ℕ)} {v6 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)} {G : List (List ℕ)} (T : BT)
    (hp : prsOK m y pD pM v6 = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM v6 G T x h = true) :
    ∀ t ws, NatRun m y t ws → T.mem (t :: isort ws) = false := by
  intro t
  induction t with
  | zero =>
    intro ws _
    cases hm : T.mem (0 :: isort ws)
    · rfl
    · obtain ⟨h, hs⟩ := hT _ hm
      simp [stepOK] at hs
  | succ t ih =>
    intro ws hw
    cases hm : T.mem ((t + 1) :: isort ws)
    · rfl
    · obtain ⟨h, hs⟩ := hT _ hm
      simp only [stepOK, Bool.not_eq_true'] at hs
      have hperm : (isort ws).Perm ws := List.perm_insertionSort _ _
      have hr : NatRun m y (t + 1) (isort ws) := Run.perm hperm.symm hw
      have hn := next_complete hr t rfl (isort ws) (List.Perm.refl _)
        (fun tag ys => via y pD pM v6 t ys && !T.mem (t :: isort ys) && !hfind G T t h tag ys)
        (fun tag ys hys => by simp [via_sound hp hys, ih ys hys, hfind_false hG T t ih h tag hys])
      rw [hn] at hs; cases hs

def rootOK (y : ℕ) (pD pM : List (ℕ × ℕ)) (v6 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (t : ℕ) (zs : List ℕ) : Bool :=
  !via y pD pM v6 t zs || T.mem (t :: isort zs) || G.any (fun pi => T.mem (t :: isort (zs.map (actL pi))))

theorem cert_core {m y : ℕ} {xs : List ℕ} {pD pM : List (ℕ × ℕ)} {v6 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)} {G : List (List ℕ)} {T : BT} {cap : ℕ}
    (hp : prsOK m y pD pM v6 = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM v6 G T x h = true)
    (hi : (List.range (cap + 1)).all (fun s' => xs.sublists.all (rootOK y pD pM v6 G T s')) = true)
    {s' : ℕ} (hs' : s' ≤ cap) {ws : List ℕ} (hsub : ws.Sublist xs) (hr : NatRun m y s' ws) : False := by
  have hs1 := List.all_eq_true.1 hi s' (List.mem_range.2 (by omega))
  have hmem := List.all_eq_true.1 hs1 ws (List.mem_sublists.2 hsub)
  have hd := via_sound hp hr
  have hc := closure_sound T hp hG hT s' ws hr
  have hg : (G.any fun pi => T.mem (s' :: isort (ws.map (actL pi)))) = false := by
    rw [List.any_eq_false]
    intro pi hpi
    obtain ⟨hm, hy⟩ := symOK_mem hG hpi
    rw [closure_sound T hp hG hT s' _ (run_act pi hm hy hr)]
    simp
  unfold rootOK at hmem
  rw [hd, hc, hg] at hmem
  simp at hmem

theorem lb_cert {n : ℕ} (f : BFn n) (l : List ℕ) (m y : ℕ) (xs : List ℕ)
    (pD pM : List (ℕ × ℕ)) (v6 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap lb : ℕ)
    (hlb : cap + 1 = lb)
    (hm : m = 2 ^ l.length - 1)
    (hy : encL f l = y)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map
      (fun a => encL a l) = xs)
    (hnc : ∃ a b : Fin n → Bool, f a ≠ f b)
    (hp : prsOK m y pD pM v6 = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM v6 G T x h = true)
    (hi : (List.range (cap + 1)).all (fun s' => xs.sublists.all (rootOK y pD pM v6 G T s')) = true) :
    ∀ s, HasCircuitSize n f s → lb ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run f hnc s h
  have hr : NatRun m (encL f l) s' (ws.map fun a => encL a l) :=
    Run.map (fun a : BFn n => encL a l) (fun a => by rw [hm]; exact encL_inv a l)
      (fun a b => encL_and a b l) (fun a b => encL_or a b l) hrun
  rw [hy] at hr
  have hsub' : (ws.map fun a => encL a l).Sublist xs := by rw [← hxs]; exact hsub.map _
  exact cert_core hp hG hT hi (by omega) hsub' hr

def L_ : List ℕ := [3,12,17,18,20,24,33,34,36,40,48,63,0,1,2,4,5,6,8,9,10,16,32]
def M_ : ℕ := 8388607
def Y_ : ℕ := 4095
def XS_ : List ℕ := [600133,1198217,231698,1837602,2100284,4198336]
def PD_ : List (ℕ × ℕ) := [(1,2048),(2,3072),(3,3584),(4,3840),(5,3968),(6,4032),(7,4064),(8,4080),(9,4088),(10,4092),(11,4094),(12,2047),(13,1023),(14,511),(15,255),(16,127),(17,63),(18,31),(19,15),(20,7),(21,3),(22,1)]
def PM_ : List (ℕ × ℕ) := [(16,4095),(17,4095),(19,4095),(20,4095),(21,4095),(22,4095)]
def V6_ : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [(0,2,3,21,16,20),(0,2,3,21,17,19),(0,6,7,22,16,20),(0,6,7,22,17,19),(1,4,5,21,16,20),(1,4,5,21,17,19),(1,8,9,22,16,20),(1,8,9,22,17,19),(2,0,4,17,16,21),(2,0,5,20,19,21),(3,0,4,16,17,21),(3,0,5,19,20,21),(4,1,2,19,16,21),(4,1,3,20,17,21),(5,1,2,16,19,21),(5,1,3,17,20,21),(6,0,8,17,16,22),(6,0,9,20,19,22),(7,0,8,16,17,22),(7,0,9,19,20,22),(8,1,6,19,16,22),(8,1,7,20,17,22),(9,1,6,16,19,22),(9,1,7,17,20,22),(2,6,10,22,16,21),(2,6,10,22,19,21),(3,7,10,22,17,21),(3,7,10,22,20,21),(4,8,10,22,16,21),(4,8,10,22,17,21),(5,9,10,22,19,21),(5,9,10,22,20,21),(6,2,10,21,16,22),(6,2,10,21,19,22),(7,3,10,21,17,22),(7,3,10,21,20,22),(8,4,10,21,16,22),(8,4,10,21,17,22),(9,5,10,21,19,22),(9,5,10,21,20,22)]
def G_ : List (List ℕ) := [[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22],[0,1,6,7,8,9,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,22,21],[1,0,4,5,2,3,8,9,6,7,10,11,12,15,18,13,16,19,14,17,20,21,22],[1,0,8,9,6,7,4,5,2,3,10,11,12,15,18,13,16,19,14,17,20,22,21],[0,1,2,3,5,4,6,7,9,8,10,11,12,13,14,18,19,20,15,16,17,21,22],[0,1,6,7,9,8,2,3,5,4,10,11,12,13,14,18,19,20,15,16,17,22,21],[1,0,5,4,2,3,9,8,6,7,10,11,12,18,15,13,19,16,14,20,17,21,22],[1,0,9,8,6,7,5,4,2,3,10,11,12,18,15,13,19,16,14,20,17,22,21],[0,1,3,2,4,5,7,6,8,9,10,11,12,14,13,15,17,16,18,20,19,21,22],[0,1,7,6,8,9,3,2,4,5,10,11,12,14,13,15,17,16,18,20,19,22,21],[1,0,4,5,3,2,8,9,7,6,10,11,12,15,18,14,17,20,13,16,19,21,22],[1,0,8,9,7,6,4,5,3,2,10,11,12,15,18,14,17,20,13,16,19,22,21],[0,1,3,2,5,4,7,6,9,8,10,11,12,14,13,18,20,19,15,17,16,21,22],[0,1,7,6,9,8,3,2,5,4,10,11,12,14,13,18,20,19,15,17,16,22,21],[1,0,5,4,3,2,9,8,7,6,10,11,12,18,15,14,20,17,13,19,16,21,22],[1,0,9,8,7,6,5,4,3,2,10,11,12,18,15,14,20,17,13,19,16,22,21]]
abbrev e := BT.e
abbrev n := BT.n
abbrev s (k h : List ℕ) := BT.n BT.e k h BT.e
abbrev w0 : ℕ := 2100284
abbrev w1 : ℕ := 4198336
abbrev w2 : ℕ := 231698
abbrev w3 : ℕ := 1837602
abbrev w4 : ℕ := 600133
abbrev w5 : ℕ := 1198217
def T_0 : BT := (n (n (n (n (n (n (s [3,2092031,w0,4198339] []) [3,2092031,2100285,4198338] [] (s [4,2049,2092031,w0,4198338] [])) [4,2051,2092031,w0,w1] [1153] (n (s [4,8261,2083771,w0,4198338] []) [4,10311,2083771,w0,w1] [] e)) [4,67585,2092031,w0,4263874] [] (n (n (s [4,67993,1911399,w0,4427730] []) [4,106839,1985195,w0,w1] [] e) [4,106839,w0,w1,6403412] [] (n (s [4,w2,600813,3296445,6033378,6295548] []) [4,w2,1796301,1838626,6295549] [] e))) [4,w2,1796301,3935806,6033378,6295549] [] (n (n (n (s [4,w2,1796301,3935806,6033379,6295549] []) [4,w2,1797325,w3,6295549] [] e) [4,w2,1837807,w0,4198337] [] (n (s [4,w2,1862383,w0,4198337] []) [4,w2,1911399,3149246,5394377] [] e)) [4,w2,1911399,3149246,5492699] [] (n (n (s [4,w2,2058991,w0,4198339] []) [4,w2,2058991,w0,4394945] [] e) [4,w2,2058991,w0,6033378,6295549] [] (n (s [4,w2,2058991,w0,6033379,6295549] []) [4,w2,2058991,2100285,4198338] [] e)))) [4,w2,2058991,2100285,4394944] [] (n (n (n (n (s [4,w2,2058991,2100285,6033378,6295548] []) [4,w2,2058991,2100285,6033378,6295549] [] (s [4,231699,1862383,w0,w1] [])) [4,231699,2058991,w0,4394944] [] (n (s [4,237909,1985195,w0,4329410] []) [4,239959,1854123,w0,w1] [] e)) [4,239959,1985195,w0,4329408] [] (n (n (s [4,239959,w0,w1,6534484] []) [4,256479,w0,4198337,6551005] [] e) [4,764247,1985195,w0,w1,6617087] [] (n (s [4,764247,1985195,w0,4198339] []) [4,764247,1985195,w0,4853696] [] e))) [4,764247,1985195,2100285,4198338] [] (n (n (n (s [4,764247,1985195,2231356,4722624] []) [4,764247,1985195,2231357,4722625] [] e) [4,764247,1985195,2231677,4796357] [] (n (s [4,764247,w0,w1,7060820] []) [4,764247,w0,4329409,6929749] [] e)) [4,1796301,2067250,w0,4198339] [] (n (n (s [4,1796301,2067250,w0,4853699] []) [4,1796301,2067250,2100285,4198338] [] e) [4,1829343,2058991,w0,w1,6594355] [] (n (s [4,1829343,2058991,w0,4198337,6592306] []) [4,1829343,w0,4198337,8125917] [] e))))) [5,2049,2050,2092031,w0,w1] [1539,1665,2050] (n (n (n (n (n (s [5,2049,33042,2058991,w0,w1] [898,1539,2050]) [5,2049,w2,1796301,1838626,6295548] [] (s [5,2049,w2,1796301,3935806,6033378,6295548] [])) [5,2049,w2,1797325,w3,6295548] [] (n (s [5,2049,w2,1837806,w0,w1] []) [5,2049,w2,1862383,w0,w1] [1537] e)) [5,2049,w2,2058991,w0,4198338] [] (n (n (s [5,2049,w2,2058991,w0,4394944] []) [5,2049,w2,2058991,w0,6033378,6295548] [] e) [5,2049,256479,w0,w1,6551005] [1153] (n (s [5,2049,w4,2083771,w0,4198338] [1539,2050]) [5,2049,764247,1985195,w0,4198338] [] e))) [5,2049,1796301,2067250,w0,4198338] [] (n (n (n (s [5,2049,1829343,2058991,w0,w1,6592306] [1537]) [5,2049,1829343,w0,w1,8125917] [1153] e) [5,2051,w2,2058991,w0,w1] [1537] (n (s [5,2051,764247,1985195,w0,w1] [1537]) [5,2051,1796301,2067250,w0,w1] [1537] e)) [5,2117,w2,w5,1838626,6295548] [] (n (n (s [5,2117,w2,w5,3935806,6033378,6295548] []) [5,2117,w2,1199241,w3,6295548] [] e) [5,2117,w2,1837738,w0,w1] [] (n (s [5,2117,w2,1985195,w0,6033378,6295548] []) [5,2253,w2,w3,w0,w1] [] e)))) [5,2253,w2,w3,w0,4198337] [900] (n (n (n (n (s [5,2388,w5,w3,2329918,4796357,6295548] [909,1166]) [5,3072,w2,1796301,w3,6295549] [900] e) [5,3073,w2,1796301,w3,6295548] [] (n (s [5,3141,w2,w5,w3,6295548] []) [5,3145,w2,1796301,w3,6295548] [] e)) [5,8261,w2,1854123,w0,w1] [] (n (n (s [5,8261,w5,2067250,w0,4198338] []) [5,8261,w5,w0,4198338,6321357] [] e) [5,10311,w5,2067250,w0,w1] [] (n (s [5,10311,w5,w0,w1,6321357] []) [5,67584,248219,1911399,w0,w1] [1545,2056] e))) [5,67584,1296795,1911399,w0,5246912] [1541,2052] (n (n (n (s [5,67585,67586,2092031,w0,w1] [1539,1665,2050]) [5,67585,860774,1296795,w0,w1] [1543,2054] e) [5,67585,1296795,1911399,w0,4263874] [] (n (s [5,67585,1296795,1911399,w0,5246913] [1541]) [5,67585,1296795,w0,w1,7527833] [1161,1544] e)) [5,67609,w5,1911399,2329918,w1] [2063] (n (n (s [5,67609,w5,1911399,3395007,w1] [2063]) [5,67609,1296795,1911399,2329918,w1] [] e) [5,67609,1296795,1911399,3296445,w1] [2057] (n (s [5,67993,w2,1911399,w0,w1] [1665]) [5,67993,w4,w3,w0,4427730] [] e))))))
def T_1 : BT := (n (n (n (n (n (n (s [5,73797,98578,w0,w1,6403412] []) [5,73797,w2,w5,1838626,6295548] [] (s [5,73797,w2,w5,6295548,6549981] [])) [5,73797,w2,1199241,w3,6295548] [] (n (s [5,73797,w2,1199241,6295548,6551005] []) [5,73797,w2,1854123,w0,w1] [] e)) [5,73797,w2,1985195,w0,4198338] [] (n (n (s [5,73797,w2,1985195,w0,4329408] []) [5,73797,w2,w0,w1,6534484] [] e) [5,73797,232722,w5,w3,6295548] [] (n (s [5,73797,232722,w5,6295548,6551005] []) [5,73797,w5,2067250,w0,4198338] [] e))) [5,73797,1854123,w0,w1,8156909] [] (n (n (n (s [5,73797,1985195,w0,w1,8290029] []) [5,74821,w2,w5,w3,6295548] [] e) [5,74821,w2,w5,6295548,6551005] [] (n (s [5,75847,w2,1985195,w0,w1] []) [5,76869,w2,w5,w3,6295548] [] e)) [5,76869,w2,w5,6295548,6551005] [] (n (n (s [5,106839,w5,w3,w0,w1] []) [5,106839,w5,w0,w1,6551005] [] e) [5,106839,w0,w1,6551005,7190390] [] (n (s [5,198656,w2,2058991,w0,4198337] [1537]) [5,198656,231699,2058991,w0,w1] [1537] e)))) [5,198657,w2,2058991,w0,w1] [1537] (n (n (n (n (s [5,204869,w2,1985195,w0,w1] []) [5,206917,w2,1985195,w0,w1] [] e) [5,221389,w2,w3,w0,4198337] [900] (n (s [5,221389,w2,1837603,w0,w1] [900]) [5,221389,w2,w0,4198337,6551005] [] e)) [5,229648,239959,1985195,w0,w1] [] (n (n (s [5,229650,w4,w5,1838626,6295548] []) [5,229650,w4,1199241,w3,6295548] [] e) [5,229650,1796301,w3,w0,4198337] [] (n (s [5,w2,237909,1985195,w0,4190271] []) [5,w2,237909,1985195,w0,w1] [] e))) [5,w2,237909,2083771,w0,w1] [] (n (n (n (s [5,w2,237909,w0,w1,6403412] []) [5,w2,239957,1985195,w0,w1] [] e) [5,w2,239957,w0,w1,6403412] [] (n (s [5,w2,w4,w5,1838626,2093059] []) [5,w2,w4,w5,1838626,6295548] [] e)) [5,w2,w4,w5,1838626,6295549] [] (n (n (s [5,w2,w4,w5,1838626,6295550] [1538]) [5,w2,w4,w5,1838626,6361084] [] e) [5,w2,w4,w5,1838626,6819836] [] (n (s [5,w2,w4,w5,1838627,6295548] []) [5,w2,w4,w5,1838630,2093059] [] e))))) [5,w2,w4,w5,1838630,6295548] [] (n (n (n (n (n (s [5,w2,w4,w5,1838638,6295548] []) [5,w2,w4,w5,1838642,2093059] [] (s [5,w2,w4,w5,1838642,6295548] [])) [5,w2,w4,w5,1838646,6295548] [] (n (s [5,w2,w4,w5,1838694,6295548] []) [5,w2,w4,w5,1838699,6295548] [] e)) [5,w2,w4,w5,1838898,6295548] [] (n (n (s [5,w2,w4,w5,1904162,6295548] []) [5,w2,w4,w5,1904242,6295548] [] e) [5,w2,w4,w5,1912423,2093059] [] (n (s [5,w2,w4,w5,1912423,6295548] []) [5,w2,w4,w5,1912431,6295548] [] e))) [5,w2,w4,w5,1912439,6295548] [] (n (n (n (s [5,w2,w4,w5,2060015,6295548] []) [5,w2,w4,w5,2093059,6549981] [] e) [5,w2,w4,w5,2100796,4198370] [] (n (s [5,w2,w4,w5,2100798,4198370] []) [5,w2,w4,w5,2100988,6033378] [] e)) [5,w2,w4,w5,2100988,6107111] [] (n (n (s [5,w2,w4,w5,2100988,6254575] []) [5,w2,w4,w5,2625213,6033378] [906] e) [5,w2,w4,w5,2625213,6180843] [906] (n (s [5,w2,w4,w5,3673660,6033378] []) [5,w2,w4,w5,3935806,6033378,6295549] [] e)))) [5,w2,w4,w5,3935806,6033379,6295549] [] (n (n (n (n (s [5,w2,w4,w5,6295548,6402388] []) [5,w2,w4,w5,6295548,6549725] [] e) [5,w2,w4,w5,6295548,6549853] [] (n (s [5,w2,w4,w5,6295548,6549981] []) [5,w2,w4,w5,6295548,7076317] [] e)) [5,w2,w4,1198219,1838626,6295548] [] (n (n (s [5,w2,w4,1198221,1838626,6295548] []) [5,w2,w4,1198233,1838626,6295548] [] e) [5,w2,w4,1198249,1838626,6295548] [] (n (s [5,w2,w4,1198249,2100798,w1] []) [5,w2,w4,1198285,1838626,6295548] [] e))) [5,w2,w4,1198489,1838626,6295548] [] (n (n (n (s [5,w2,w4,1198761,1838626,6295548] []) [5,w2,w4,1198761,w0,4198338] [] e) [5,w2,w4,1198763,w0,4198338] [] (n (s [5,w2,w4,1198763,w0,4198370] []) [5,w2,w4,1198829,w0,6033378,6295548] [1672] e)) [5,w2,w4,1199241,1838626,2093059] [] (n (n (s [5,w2,w4,1199241,1838626,6295548] []) [5,w2,w4,1199241,1838634,6295548] [] e) [5,w2,w4,1199241,1838762,6295548] [] (n (s [5,w2,w4,1199241,1903138,6295548] []) [5,w2,w4,1199241,1911399,2093059] [] e))))))
def N_2 : BT := n T_0 [5,73797,98578,1985195,w0,w1] [] T_1
def T_3 : BT := (n (n (n (n (n (n (s [5,w2,w4,1199241,1912423,6295548] []) [5,w2,w4,1199241,1968674,6295548] [] (s [5,w2,w4,1199241,1985195,2093059] [])) [5,w2,w4,1199241,1985195,6295548] [] (n (s [5,w2,w4,1199241,1986219,2093059] []) [5,w2,w4,1199241,1986219,6295548] [] e)) [5,w2,w4,1199241,2058991,6295548] [] (n (n (s [5,w2,w4,1199241,2060015,6295548] []) [5,w2,w4,1199241,2093059,6551005] [] e) [5,w2,w4,1199241,6295548,6402388] [] (n (s [5,w2,w4,1199241,6295548,6403412] []) [5,w2,w4,1199241,6295548,6477208] [] e))) [5,w2,w4,1199241,6295548,6549981] [] (n (n (n (s [5,w2,w4,1199241,6295548,6551005] []) [5,w2,w4,1199241,6295548,6553053] [] e) [5,w2,w4,1199241,6295548,7077341] [] (n (s [5,w2,w4,1199241,6295548,7601629] []) [5,w2,w4,1199245,1838630,6295548] [] e)) [5,w2,w4,1199245,1911399,6295548] [] (n (n (s [5,w2,w4,1199245,1985195,6295548] []) [5,w2,w4,1199245,1986223,6295548] [] e) [5,w2,w4,1199245,6295548,6551005] [] (n (s [5,w2,w4,1199257,1911399,6295548] []) [5,w2,w4,1199257,1985195,6295548] [] e)))) [5,w2,w4,1199257,1986235,6295548] [] (n (n (n (n (s [5,w2,w4,1199257,6295548,6551005] []) [5,w2,w4,1199273,1911399,6295548] [] e) [5,w2,w4,1199273,1985195,6295548] [] (n (s [5,w2,w4,1199273,1986219,6295548] []) [5,w2,w4,1199273,6295548,6551005] [] e)) [5,w2,w4,1199277,1911399,6295548] [] (n (n (s [5,w2,w4,1296795,1912423,6295548] []) [5,w2,w4,1296795,6295548,6549981] [] e) [5,w2,w4,1297819,6295548,6551005] [] (n (s [5,w2,w4,1460907,w0,4198338] []) [5,w2,w4,1460907,w0,4329408] [910] e))) [5,w2,w4,1985195,w0,3665981] [] (n (n (n (s [5,w2,w4,1985195,w0,w1,6617087] []) [5,w2,w4,1985195,w0,4198339] [1154] e) [5,w2,w4,1985195,w0,4329409] [] (n (s [5,w2,w4,1985195,w0,4329417] []) [5,w2,w4,1985195,w0,4329429] [1543] e)) [5,w2,w4,1985195,w0,4853696] [] (n (n (s [5,w2,w4,1985195,w0,5394377,6295550] [1154]) [5,w2,w4,1985195,w0,5394379,6295550] [1154] e) [5,w2,w4,1985195,2100285,4198338] [1155] (n (s [5,w2,w4,1985195,2100285,4329408] []) [5,w2,w4,1985195,2100285,6033378,6295548] [] e))))) [5,w2,w4,1985195,2100285,6033378,6295549] [] (n (n (n (n (n (s [5,w2,w4,1985195,2100924,2355229] []) [5,w2,w4,1985195,2100924,5394377] [] (s [5,w2,w4,1985195,2100988,5394377] [])) [5,w2,w4,1985195,2100988,6033378] [] (n (s [5,w2,w4,1985195,2231356,4722624] []) [5,w2,w4,1985195,2231357,4190271] [] e)) [5,w2,w4,1985195,2231357,4329409] [] (n (n (s [5,w2,w4,1985195,2231998,5394377] []) [5,w2,w4,1985195,2231998,6033378] [910] e) [5,w2,w4,1985195,3296445,4190231] [] (n (s [5,w2,w4,1985195,6295548,6549981] []) [5,w2,w4,1986219,3296445,6295548] [] e))) [5,w2,w4,1986219,6295548,6549981] [] (n (n (n (s [5,w2,w4,1986219,6295548,6551005] []) [5,w2,w4,1986219,6295548,7491581] [] e) [5,w2,w4,2058991,w0,4329409] [] (n (s [5,w2,w4,2058991,w0,5394377,6594546] []) [5,w2,w4,2058991,2100924,5394377] [] e)) [5,w2,w4,2058991,2100988,5394377] [] (n (n (s [5,w2,w4,w0,w1,7060820] []) [5,w2,w4,w0,4329409,6403412] [] e) [5,w2,w4,2100924,5394377,6033378] [] (n (s [5,w2,w4,2100924,5394377,6403412] []) [5,w2,w4,6295548,6549981,7190390] [] e)))) [5,w2,600135,1199241,w3,6295548] [] (n (n (n (n (s [5,w2,600135,1460907,w0,w1] []) [5,w2,600135,w3,3296445,5394377,6295548] [] e) [5,w2,600135,1985195,w0,4198337] [] (n (s [5,w2,600135,1985195,w0,4722624] []) [5,w2,600135,1985195,w0,4722626] [] e)) [5,w2,600135,1985195,w0,5394377,6295548] [] (n (n (s [5,w2,600141,1199241,w3,6295548] []) [5,w2,600141,w3,2100413,w1] [] e) [5,w2,600149,1199241,w3,6295548] [] (n (s [5,w2,600173,1985195,3296445,4190271] []) [5,w2,600173,1985195,3296445,w1] [] e))) [5,w2,600173,1985195,3296445,4198376] [] (n (n (n (s [5,w2,600173,1985195,3935806,4198376] []) [5,w2,600173,1985195,w1,5092162] [] e) [5,w2,600173,2058991,3296445,w1] [] (n (s [5,w2,600173,3296445,3935806,w1] []) [5,w2,600173,3296445,w1,6403412] [] e)) [5,w2,600189,w3,3296445,w1] [] (n (n (s [5,w2,600189,1985195,3296445,w1] []) [5,w2,600269,1199241,w3,6295548] [] e) [5,w2,600269,w3,w0,4198337] [] (n (s [5,w2,600269,w3,w0,4198345] []) [5,w2,600405,1199241,w3,6295548] [] e))))))
def T_4 : BT := (n (n (n (n (n (n (s [5,w2,600679,1198763,w0,w1] []) [5,w2,600813,1985195,w0,5394377] [] (s [5,w2,601157,1199241,w3,2093059] [])) [5,w2,601157,1199241,w3,6295548] [] (n (s [5,w2,601157,1199241,1838626,6295548] []) [5,w2,601157,1199241,1911399,6295548] [] e)) [5,w2,601157,1199241,1912423,6295548] [] (n (n (s [5,w2,601157,1199241,6295548,6551005] []) [5,w2,601157,1199245,w3,6295548] [] e) [5,w2,601157,1199309,w3,6295548] [] (n (s [5,w2,601157,1263753,w3,6295548] []) [5,w2,601157,1296795,w3,2093059] [] e))) [5,w2,601157,1296795,w3,6295548] [] (n (n (n (s [5,w2,601157,1296795,1838626,6295548] []) [5,w2,601157,1296795,1911399,6295548] [] e) [5,w2,601157,1296795,1912423,6295548] [] (n (s [5,w2,601157,1296795,6295548,6551005] []) [5,w2,601157,1297819,w3,6295548] [] e)) [5,w2,601157,w3,2083771,6295548] [] (n (n (s [5,w2,601157,w3,2093059,7190390] []) [5,w2,601157,w3,6295548,6403412] [] e) [5,w2,601157,w3,6295548,7189366] [] (n (s [5,w2,601157,w3,6295548,7190390] []) [5,w2,601157,w3,6295548,7192438] [] e)))) [5,w2,601157,w3,6295548,7323510] [] (n (n (n (n (s [5,w2,601157,1838626,1985195,6295548] []) [5,w2,601157,1838626,1986219,6295548] [] e) [5,w2,601157,1838626,6295548,7190390] [] (n (s [5,w2,601157,1911399,6295548,7190390] []) [5,w2,601157,1912423,6295548,7190390] [] e)) [5,w2,601157,1985195,3296445,6295548] [] (n (n (s [5,w2,601157,1985195,3935806,6295548] []) [5,w2,601157,1985195,6295548,6551005] [] e) [5,w2,601157,1985195,6295548,7190390] [] (n (s [5,w2,601157,1985195,6295548,7491581] []) [5,w2,601157,1985195,6295548,8130558] [] e))) [5,w2,601157,6295548,6551005,7190390] [] (n (n (n (s [5,w2,601165,1296795,w3,6295548] []) [5,w2,601165,w3,6295548,7190390] [] e) [5,w2,601165,1985195,5394377,6295548] [] (n (s [5,w2,601173,1199257,w3,6295548] []) [5,w2,601173,1296795,w3,6295548] [] e)) [5,w2,601173,w3,1985195,6295548] [] (n (n (s [5,w2,601173,w3,6295548,7190390] []) [5,w2,601181,1296795,w3,6295548] [] e) [5,w2,601189,1985195,6033378,6295548] [] (n (s [5,w2,601197,1985195,3296445,w1] []) [5,w2,731205,1460907,w0,w1] [] e))))) [5,w2,731205,1985195,w0,4198337] [] (n (n (n (n (n (s [5,w2,731205,1985195,w0,4329409] []) [5,w2,731205,1985195,w0,4722624] [] (s [5,w2,731207,1985195,w0,4329409] [])) [5,w2,731207,1985195,w0,4722626] [] (n (s [5,w2,731247,w3,3296445,w1] []) [5,w2,731247,1985195,3296445,w1] [] e)) [5,w2,747725,w3,w0,4198337] [] (n (n (s [5,w2,747725,w0,4198337,6551005] []) [5,w2,764247,1296795,1838626,6295548] [] e) [5,w2,764247,1297819,w3,6295548] [] (n (s [5,w2,764247,w3,1986219,6295548] []) [5,w2,764247,w3,6295548,7189366] [] e))) [5,w2,764247,1838626,1985195,6295548] [] (n (n (n (s [5,w2,764247,1838626,1986219,6295548] []) [5,w2,764247,1838626,6295548,7190390] [] e) [5,w2,764247,1985195,w0,3665981] [] (n (s [5,w2,764247,1985195,w0,4059198] []) [5,w2,764247,1985195,w0,4329409] [] e)) [5,w2,764247,1985195,w0,4329417] [] (n (n (s [5,w2,764247,1985195,w0,4329429] []) [5,w2,764247,1985195,w0,4722626] [] e) [5,w2,764247,1985195,w0,4722646] [1539,1673] (n (s [5,w2,764247,1985195,w0,4722658] []) [5,w2,764247,1985195,2100924,5394377] [] e)))) [5,w2,764247,1985195,2100924,6033378] [] (n (n (n (n (s [5,w2,764247,1985195,2231357,4190271] []) [5,w2,764247,1985195,2624574,4190271] [] e) [5,w2,764247,1985195,2624574,4722626] [] (n (s [5,w2,764247,2083771,w0,4722626] []) [5,w2,764247,w0,4329409,6403412] [] e)) [5,w2,764247,w0,4722626,6403412] [2050] (n (n (s [5,w2,764287,1985195,3296445,w1] []) [5,w2,765271,1297819,w3,6295548] [] e) [5,w2,765271,w3,6295548,7190390] [] (n (s [5,w2,862821,w0,w1,8142438] []) [5,w2,862823,w0,w1,7124854] [] e))) [5,w2,862823,w0,4198338,7190390] [] (n (n (n (s [5,w2,862823,w0,4263872,7190390] []) [5,w2,1779789,w3,3296445,w1] [] e) [5,w2,1796301,w3,2092031,w0,4198337] [] (n (s [5,w2,1796301,w3,2098236,4198337] []) [5,w2,1796301,w3,w0,3141694] [] e)) [5,w2,1796301,w3,w0,4190262] [] (n (n (s [5,w2,1796301,w3,w0,4190270] []) [5,w2,1796301,w3,w0,4198337] [] e) [5,w2,1796301,w3,w0,4198339] [900] (n (s [5,w2,1796301,w3,w0,4198341] []) [5,w2,1796301,w3,w0,4198349] [] e))))))
def N_5 : BT := n T_3 [5,w2,600541,w3,w0,5394377,6295548] [1541] T_4
def N_6 : BT := n N_2 [5,w2,w4,1199241,1911399,6295548] [] N_5
def T_7 : BT := (n (n (n (n (n (n (s [5,w2,1796301,w3,w0,4263873] []) [5,w2,1796301,w3,w0,4263877] [] (s [5,w2,1796301,w3,w0,4263897] [])) [5,w2,1796301,w3,w0,4394945] [] (n (s [5,w2,1796301,w3,w0,4427730,6295549] [900,1540]) [5,w2,1796301,w3,w0,4427731,6295549] [900,1540] e)) [5,w2,1796301,w3,w0,4788161] [] (n (n (s [5,w2,1796301,w3,w0,4853699] []) [5,w2,1796301,w3,2100285,4190270] [] e) [5,w2,1796301,w3,2100285,4190271] [] (n (s [5,w2,1796301,w3,2100285,4192319] []) [5,w2,1796301,w3,2100285,4198337] [] e))) [5,w2,1796301,w3,2100285,4198338] [900] (n (n (n (s [5,w2,1796301,w3,2100285,4198340] []) [5,w2,1796301,w3,2100285,4198341] [] e) [5,w2,1796301,w3,2100285,4198348] [] (n (s [5,w2,1796301,w3,2100285,4198349] []) [5,w2,1796301,w3,2100285,4198352] [] e)) [5,w2,1796301,w3,2100285,4263872] [] (n (n (s [5,w2,1796301,w3,2100285,4394944] []) [5,w2,1796301,w3,2100285,4427730,6295548] [900] e) [5,w2,1796301,w3,2100285,4427730,6295549] [900,1541] (n (s [5,w2,1796301,w3,2100349,4190271] []) [5,w2,1796301,w3,2165821,4190271] [] e)))) [5,w2,1796301,w3,2165821,4263873] [] (n (n (n (n (s [5,w2,1796301,w3,4190270,6288323] []) [5,w2,1796301,1837603,w0,4190270] [] (s [5,w2,1796301,1837603,w0,4198337] [])) [5,w2,1796301,1837603,w0,5771200] [900] (n (s [5,w2,1796301,1837603,2100285,4190271] []) [5,w2,1796301,1837603,2100285,4198337] [] e)) [5,w2,1796301,1837606,w0,4198337] [] (n (n (s [5,w2,1796301,1837606,2100285,w1] []) [5,w2,1796301,1837607,w0,4198341] [] e) [5,w2,1796301,1837607,2100285,w1] [] (n (s [5,w2,1796301,1837614,w0,4198337] []) [5,w2,1796301,1837614,2100285,w1] [] e))) [5,w2,1796301,1837615,2100285,w1] [] (n (n (n (s [5,w2,1796301,1837618,w0,4198337] []) [5,w2,1796301,1837618,2100285,w1] [] e) [5,w2,1796301,1838626,w0,4198337] [] (n (s [5,w2,1796301,1903138,w0,4198337] []) [5,w2,1796301,1903139,w0,4263873] [] e)) [5,w2,1796301,1911399,w0,4190270] [] (n (n (s [5,w2,1796301,1911399,w0,4198337] []) [5,w2,1796301,1911399,w0,4198341] [] e) [5,w2,1796301,1911399,w0,4198345] [] (n (s [5,w2,1796301,1911399,w0,4263873] []) [5,w2,1796301,1911399,w0,4329409] [] e))))) [5,w2,1796301,1911399,2100285,4190271] [] (n (n (n (n (n (s [5,w2,1796301,1911399,2100285,4198337] []) [5,w2,1796301,2034210,w0,4198337] [] (s [5,w2,1796301,2056942,w0,w1] [])) [5,w2,1796301,2058990,w0,w1] [] (n (s [5,w2,1796301,2058991,w0,4190270] []) [5,w2,1796301,2058991,w0,w1,6594355] [] e)) [5,w2,1796301,2058991,w0,4198337] [] (n (n (s [5,w2,1796301,2058991,w0,4198337,6592306] []) [5,w2,1796301,2058991,w0,4198341] [] e) [5,w2,1796301,2058991,w0,4263873] [] (n (s [5,w2,1796301,2058991,2100285,4190271] []) [5,w2,1796301,2058991,2100285,4198337] [] e))) [5,w2,1796301,w0,3935806,4198337,6033378] [] (n (n (n (s [5,w2,1796301,w0,3935806,4198337,6033379] []) [5,w2,1796301,w0,4190270,6551005] [] e) [5,w2,1796301,w0,w1,6331665] [] (n (s [5,w2,1796301,w0,4198337,6329616] []) [5,w2,1796301,w0,4198337,6403412] [] e)) [5,w2,1796301,w0,4198337,6551004] [] (n (n (s [5,w2,1796301,w0,4198337,6551005] []) [5,w2,1796301,w0,4198337,6553053] [] e) [5,w2,1796301,w0,4198337,7077341] [] (n (s [5,w2,1796301,w0,4198337,8125917] []) [5,w2,1796301,w0,4198341,6551005] [] e)))) [5,w2,1796301,w0,4263873,6551005] [] (n (n (n (n (s [5,w2,1796301,w0,4722625,6551005] []) [5,w2,1796301,2100285,4190271,6551005] [] e) [5,w2,1796301,2100285,4198337,6551005] [] (n (s [5,w2,1796303,w3,w0,4198337] []) [5,w2,1796317,w3,w0,4198337] [] e)) [5,w2,1796317,w3,2100285,w1] [] (n (n (s [5,w2,1797325,w3,w0,4198337] []) [5,w2,1829343,w3,2058991,w0,4198337] [] e) [5,w2,1829343,w3,2092031,w0,4198337] [] (n (s [5,w2,1829343,w3,w0,4190270] []) [5,w2,1829343,w3,w0,w1,6295549] [1541,2052] e))) [5,w2,1829343,w3,w0,4198337] [] (n (n (n (s [5,w2,1829343,w3,w0,4198337,6295548] [1541]) [5,w2,1829343,w3,w0,4198337,6295549] [1541,2052] e) [5,w2,1829343,w3,w0,4198341] [] (n (s [5,w2,1829343,w3,w0,4722625] []) [5,w2,1829343,w3,2100285,4190271] [] e)) [5,w2,1829343,w3,2100285,4198337] [] (n (n (s [5,w2,1829343,w3,2165821,4263873] []) [5,w2,1829343,1837603,w0,4198337] [] e) [5,w2,1829343,1903139,w0,4263873] [] (n (s [5,w2,1829343,1911399,w0,4263873] []) [5,w2,1829343,w0,4198337,6551005] [] e))))))
def T_8 : BT := (n (n (n (n (n (n (s [5,w2,w3,2092031,w0,4796357,5394377] []) [5,w2,w3,w0,4190270,6592306] [] (s [5,w2,w3,w0,4198337,6329616] [])) [5,w2,w3,w0,4198337,6592306] [] (n (s [5,w2,w3,w0,4198337,6790962] []) [5,w2,w3,w0,4198341,6592306] [] e)) [5,w2,w3,w0,4263873,6592306] [] (n (n (s [5,w2,w3,2100285,4190271,6592306] []) [5,w2,w3,2100285,4198337,6592306] [] e) [5,w2,w3,6295548,7189366,7788474] [] (n (s [5,w2,1837603,2058991,w0,4198337] []) [5,w2,1837603,w0,w1,8167218] [] e))) [5,w2,1837603,w0,4198337,6592306] [] (n (n (n (s [5,w2,1838626,1911399,1985195,6295548] []) [5,w2,1838626,1911399,1986219,6295548] [] e) [5,w2,1838626,1911399,6295548,7190390] [] (n (s [5,w2,1838626,1912423,1986219,6295548] []) [5,w2,1838626,1912423,6295548,7190390] [] e)) [5,w2,1838626,6295548,7190390,7788474] [] (n (n (s [5,w2,1845863,2083771,w0,w1,6321357] []) [5,w2,1845863,w0,w1,8241014] [] e) [5,w2,1910887,1985195,w0,6033378] [] (n (s [5,w2,1911399,1985195,w0,4190270] []) [5,w2,1911399,1985195,w0,w1,6295549] [] e)))) [5,w2,1911399,1985195,w0,4198337] [] (n (n (n (n (s [5,w2,1911399,1985195,w0,4198337,6295548] []) [5,w2,1911399,1985195,w0,4198337,6295549] [] e) [5,w2,1911399,1985195,w0,4198341] [] (n (s [5,w2,1911399,1985195,w0,4263873] []) [5,w2,1911399,1985195,2100285,4190271] [] e)) [5,w2,1911399,1985195,2100285,4198337] [] (n (n (s [5,w2,1911399,1985195,2100796,6033378] []) [5,w2,1911399,1985195,2100860,6033378] [] e) [5,w2,1911399,2058991,w0,4263873] [] (n (s [5,w2,1911399,2083771,w0,4263873] []) [5,w2,1911399,2092031,w0,4263873] [962] e))) [5,w2,1911399,w0,3894525,4198345] [] (n (n (n (s [5,w2,1911399,w0,4190271,8142438] []) [5,w2,1911399,w0,w1,8142438] [] e) [5,w2,1911399,w0,w1,8175478] [] (n (s [5,w2,1911399,w0,4198337,6403412] []) [5,w2,1911399,w0,4198337,6592306] [] e)) [5,w2,1911399,w0,4198338,8241014] [] (n (n (s [5,w2,1911399,w0,4263872,8241014] []) [5,w2,1911399,w0,4263873,7091812] [] e) [5,w2,1911399,w0,4263873,7190390] [] (n (s [5,w2,1911399,w0,4796357,7189814] []) [5,w2,1911399,w0,5246914,7091812] [] e))))) [5,w2,1911399,w0,5246914,7190390] [] (n (n (n (n (n (s [5,w2,1911399,2100412,4796357,5394377] []) [5,w2,1911399,2100413,4796357,5394377] [] (s [5,w2,1911399,2100860,4796357,7190390] [])) [5,w2,1911399,2100860,6033378,7190390] [] (n (s [5,w2,1911399,3148988,5394377,6033378] []) [5,w2,1911399,3296445,5394377,6893565] [] e)) [5,w2,1911399,3296445,5394377,8130558] [] (n (n (s [5,w2,1911407,2698365,3296445,w1] []) [5,w2,2058991,w0,2100285,w1,6033378] [] e) [5,w2,2058991,w0,2994230,4796357] [] (n (s [5,w2,2058991,w0,3894525,4198337] []) [5,w2,2058991,w0,3935806,4198337] [2321] e))) [5,w2,2058991,w0,4198337,5992397] [] (n (n (n (s [5,w2,2058991,w0,4198337,6033378] []) [5,w2,2058991,w0,4198337,6033379] [] e) [5,w2,2058991,w0,4198337,6551005] [] (n (s [5,w2,2058991,w0,4198337,6592306] [2114]) [5,w2,2058991,w0,4796357,5394377] [] e)) [5,w2,2058991,w0,4796357,5394377,6592306] [] (n (n (s [5,w2,2058991,w0,4796357,7491581] []) [5,w2,2058991,2698365,3296445,4190271] [] e) [5,w2,2058991,2698365,5394377,6295548] [] (n (s [5,w2,2075511,w0,w1,8142438] []) [5,w2,w0,w1,6403412,8150698] [] e)))) [5,w2,w0,4198337,6551005,6592306] [] (n (n (n (n (s [5,w2,w0,4796357,5394377,6329616] []) [5,231699,600135,1985195,w0,w1] [] e) [5,231699,1796301,1837603,w0,4190271] [] (n (s [5,231699,1796301,1837603,w0,w1] []) [5,231699,1796301,1837603,w0,4198337] [] e)) [5,231699,1796301,1911399,w0,4198337] [] (n (n (s [5,231699,1796301,2034210,w0,w1] []) [5,231699,1796301,2058991,w0,4198337] [] e) [5,231699,1796301,w0,w1,6551004] [] (n (s [5,231699,1796301,w0,4198337,6551005] []) [5,231699,1829343,1837603,w0,w1] [] e))) [5,231699,1837603,w0,w1,6592306] [] (n (n (n (s [5,231699,1911399,1985195,w0,4190271] []) [5,231699,1911399,1985195,w0,w1] [] e) [5,231699,1911399,1985195,w0,w1,6295548] [] (n (s [5,231699,1911399,1985195,w0,4198337] []) [5,231699,1911399,w0,w1,6403412] [] e)) [5,231702,1985195,2698365,3296445,w1] [] (n (n (s [5,231703,1796301,1837607,w0,w1] []) [5,231703,1911399,1985195,w0,w1] [] e) [5,231703,1985195,2698365,3296445,w1] [] (n (s [5,231730,1911399,1985195,3935806,w1] []) [5,231734,1198253,1911399,2698365,w1] [] e))))))
def N_9 : BT := n T_7 [5,w2,w3,2092031,w0,4198337] [962] T_8
def T_10 : BT := (n (n (n (n (n (n (s [5,231734,1296795,1911399,3935806,w1] []) [5,231734,1296831,1911399,3935806,w1] [] (s [5,231734,1911399,1985195,3935806,w1] [])) [5,231734,1911399,3935806,w1,7190390] [] (n (s [5,237909,1985195,w0,2329918,w1] []) [5,237909,1985195,w0,w1,8156909] [] e)) [5,239959,1911399,1985195,w0,w1] [] (n (n (s [5,239959,w0,w1,6551005,7323510] []) [5,657408,764247,1985195,w0,w1] [1537] e) [5,657411,1296795,1911399,w0,w1] [] (n (s [5,657411,1796301,2067250,w0,w1] [1537]) [5,731205,755986,1985195,w0,w1] [] e))) [5,731221,1985195,2329918,3296445,w1] [] (n (n (n (s [5,764247,1296795,1911399,1985195,w0,w1] []) [5,764247,1296795,1911399,w0,4263872] [] e) [5,764247,1296795,2067250,w0,4198338] [] (n (s [5,764247,1296795,2067250,w0,4722626] []) [5,764247,1296795,w0,w1,6551004] [] e)) [5,764247,1296795,w0,4198337,6551005] [] (n (n (s [5,764247,1771520,1985195,w0,w1] []) [5,764247,1796301,1985195,w0,4198337] [] e) [5,764247,1796301,2058991,w0,4198337] [] (n (s [5,764247,1796301,w0,4198337,6551005] []) [5,764247,1985195,w0,2329918,4329409] [] e)))) [5,764247,1985195,w0,2329918,4722626] [] (n (n (n (n (s [5,764247,1985195,w0,2355229,4427730] []) [5,764247,1985195,w0,2355229,4796357] [] e) [5,764247,1985195,w0,4329409,4427730] [] (n (s [5,764247,1985195,w0,4329409,4796357] []) [5,764247,1985195,w0,4329409,7788474] [2254] e)) [5,764247,1985195,w0,4329409,8156909] [] (n (n (s [5,764247,1985195,w0,4427730,5394377] []) [5,764247,1985195,w0,4427730,6033378] [] e) [5,764247,1985195,w0,4427730,7491581] [2120] (n (s [5,764247,1985195,w0,4427730,8130558] []) [5,764247,1985195,2329918,3296445,4190271] [] e))) [5,764247,1985195,2329918,3935806,4190271] [] (n (n (n (s [5,764247,1985195,2329918,5394377,6295548] []) [5,764247,1985195,2329918,6033378,6295548] [] e) [5,764247,2058991,w0,4796357,5394377] [] (n (s [5,764247,w0,3296445,w1,6929749] []) [5,764247,w0,w1,6536534,6551005] [] e)) [5,764247,w0,w1,6536534,7601629] [] (n (n (s [5,764247,w0,w1,7077341,7323510] []) [5,764247,w0,4427730,5394377,6403412] [] e) [5,764247,w0,4427730,6033378,6403412] [] (n (s [5,1796301,1829343,2058991,w0,4198337] []) [5,1796301,1829343,w0,4198337,6551005] [] e))))) [5,1796301,w0,4198337,6551005,8156909] [] (n (n (n (n (n (s [5,1829343,2058991,w0,4796357,5394377] []) [5,1829343,w0,4796357,5394377,6551005] [] (s [6,1,w2,w4,1854123,w0,w1] [898,2051,2690])) [6,1,w2,747725,w3,w0,w1] [2049] (n (s [6,1,w2,747725,w0,w1,6551005] [1537]) [6,1,w2,1796301,w3,w0,4190271] [] e)) [6,1,w2,1796301,w3,w0,w1] [2049] (n (n (s [6,1,w2,1796301,w0,w1,6551005] [1537]) [6,1,239959,w5,w0,w1,6551005] [1547,2058] e) [6,1024,w2,w4,w5,w3,6295548] [900,1162,1538] (n (s [6,1024,w2,w4,w5,6295548,6551005] [898,1160]) [6,2048,w2,w4,w5,1838626,6295548] [] e))) [6,2048,w2,1796301,w3,w0,4198337] [] (n (n (n (s [6,2049,2050,w2,2058991,w0,w1] [2051,2177,2690]) [6,2049,2050,764247,1985195,w0,w1] [2051,2177,2690] e) [6,2049,2050,1796301,2067250,w0,w1] [2051,2177,2690] (n (s [6,2049,2252,w2,w3,w0,w1] [1284]) [6,2049,3072,w2,1796301,w3,6295548] [1284] e)) [6,2049,33042,1796301,w3,w0,w1] [898,2051,2690] (n (n (s [6,2049,33042,w3,w0,w1,6592306] [898,1539,2050]) [6,2049,98578,w4,1985195,w0,w1] [898,2051,2690] e) [6,2049,98578,1796301,w3,w0,w1] [2051,2690] (n (s [6,2049,198656,w2,2058991,w0,w1] [2049,2177]) [6,2049,221389,w2,w3,w0,w1] [1284,2049] e)))) [6,2049,221389,w2,w0,w1,6551005] [1537] (n (n (n (n (s [6,2049,229650,1796301,w3,w0,w1] [2049]) [6,2049,w2,w4,w5,1838626,6295548] [898] e) [6,2049,w2,w4,w5,3935806,6033378,6295548] [898] (n (s [6,2049,w2,w4,1199241,w3,6295548] [902,1154,1538,2050,2690]) [6,2049,w2,w4,1837738,w0,w1] [2051,2690] e)) [6,2049,w2,w4,1854123,w0,w1] [898,2051,2690] (n (n (s [6,2049,w2,w4,1985195,w0,4198338] [898]) [6,2049,w2,w4,1985195,w0,4329408] [898] e) [6,2049,w2,w4,1985195,w0,6033378,6295548] [898,3458] (n (s [6,2049,w2,600135,1985195,w0,w1] [2049]) [6,2049,w2,600269,w3,w0,w1] [2049] e))) [6,2049,w2,731205,1985195,w0,w1] [2049] (n (n (n (s [6,2049,w2,747725,w3,w0,w1] [2049]) [6,2049,w2,747725,w0,w1,6551005] [1537] e) [6,2049,w2,1794252,w3,w0,w1] [] (n (s [6,2049,w2,1796301,w3,2092031,w0,w1] [2689]) [6,2049,w2,1796301,w3,2098236,w1] [2049] e)) [6,2049,w2,1796301,w3,w0,4190270] [900] (n (n (s [6,2049,w2,1796301,w3,w0,4190271] []) [6,2049,w2,1796301,w3,w0,4192319] [] e) [6,2049,w2,1796301,w3,w0,w1] [2049] (n (s [6,2049,w2,1796301,w3,w0,4198337] [900]) [6,2049,w2,1796301,w3,w0,4198338] [1284] e))))))
def T_11 : BT := (n (n (n (n (n (n (s [6,2049,w2,1796301,w3,w0,4198348] []) [6,2049,w2,1796301,w3,w0,4198352] [] (s [6,2049,w2,1796301,w3,w0,4263872] [])) [6,2049,w2,1796301,w3,w0,4394944] [900] (n (s [6,2049,w2,1796301,w3,w0,4427730,6295548] [1284,2180]) [6,2049,w2,1796301,w3,2100285,4190271] [900] e)) [6,2049,w2,1796301,w3,2100285,4198337] [900] (n (n (s [6,2049,w2,1796301,w3,4190271,6288323] []) [6,2049,w2,1796301,1837603,w0,4190271] [] e) [6,2049,w2,1796301,1837603,w0,w1] [2049] (n (s [6,2049,w2,1796301,1837603,w0,4198337] []) [6,2049,w2,1796301,1837606,w0,w1] [] e))) [6,2049,w2,1796301,1837614,w0,w1] [] (n (n (n (s [6,2049,w2,1796301,1837618,w0,w1] []) [6,2049,w2,1796301,1838626,w0,w1] [2049] e) [6,2049,w2,1796301,1903138,w0,w1] [2049] (n (s [6,2049,w2,1796301,1911399,w0,4190271] []) [6,2049,w2,1796301,1911399,w0,w1] [2049] e)) [6,2049,w2,1796301,1911399,w0,4198337] [] (n (n (s [6,2049,w2,1796301,2034210,w0,w1] [2049]) [6,2049,w2,1796301,2058991,w0,4190271] [] e) [6,2049,w2,1796301,2058991,w0,w1] [2049] (n (s [6,2049,w2,1796301,2058991,w0,w1,6592306] [2049]) [6,2049,w2,1796301,2058991,w0,4198337] [] e)))) [6,2049,w2,1796301,w0,3935806,w1,6033378] [1537] (n (n (n (n (s [6,2049,w2,1796301,w0,4190271,6551005] []) [6,2049,w2,1796301,w0,w1,6329616] [1537] e) [6,2049,w2,1796301,w0,w1,6403412] [1537] (n (s [6,2049,w2,1796301,w0,w1,6551004] [1537]) [6,2049,w2,1796301,w0,w1,6551005] [1537] e)) [6,2049,w2,1796301,w0,w1,6553053] [1537] (n (n (s [6,2049,w2,1796301,w0,w1,7077341] [1537]) [6,2049,w2,1796301,w0,w1,8125917] [1537] e) [6,2049,w2,1796301,w0,4198337,6551005] [] (n (s [6,2049,w2,1796303,w3,w0,w1] [2049]) [6,2049,w2,1796317,w3,w0,w1] [] e))) [6,2049,w2,1797325,w3,w0,w1] [2049] (n (n (n (s [6,2049,w2,1829343,w3,2058991,w0,w1] [2689]) [6,2049,w2,1829343,w3,2092031,w0,w1] [2689] e) [6,2049,w2,1829343,w3,w0,4190271] [] (n (s [6,2049,w2,1829343,w3,w0,w1] [2049]) [6,2049,w2,1829343,w3,w0,w1,6295548] [2049,2181,2820] e)) [6,2049,w2,1829343,w3,w0,4198337] [900] (n (n (s [6,2049,w2,1829343,1837603,w0,w1] [2049]) [6,2049,w2,1829343,w0,w1,6551005] [1537] e) [6,2049,w2,w3,2092031,w0,w1] [2049] (n (s [6,2049,w2,w3,w0,4190271,6592306] []) [6,2049,w2,w3,w0,w1,6329616] [1537] e))))) [6,2049,w2,w3,w0,w1,6592306] [1537] (n (n (n (n (n (s [6,2049,w2,w3,w0,w1,6594355] []) [6,2049,w2,w3,w0,w1,6790962] [900,1537] (s [6,2049,w2,w3,w0,4198337,6592306] [900])) [6,2049,w2,1837603,2058991,w0,w1] [900,2049] (n (s [6,2049,w2,1837603,w0,w1,6592306] [1537]) [6,2049,w2,1911399,1985195,w0,4190271] [] e)) [6,2049,w2,1911399,1985195,w0,w1] [2049] (n (n (s [6,2049,w2,1911399,1985195,w0,w1,6295548] [2049]) [6,2049,w2,1911399,1985195,w0,4198337] [] e) [6,2049,w2,1911399,w0,w1,6403412] [1537] (n (s [6,2049,w2,1911399,w0,w1,6592306] [1537]) [6,2049,w2,2058991,w0,3894525,w1] [1537] e))) [6,2049,w2,2058991,w0,3935806,w1] [1537,2705,3089] (n (n (n (s [6,2049,w2,2058991,w0,w1,6551005] [1537]) [6,2049,w2,2058991,w0,w1,6592306] [1537] e) [6,2049,w2,w0,w1,6551005,6592306] [1153] (n (s [6,2049,231699,1796301,1837603,w0,w1] [2049]) [6,2049,231699,1796301,1911399,w0,w1] [2049] e)) [6,2049,231699,1796301,2058991,w0,w1] [2049] (n (n (s [6,2049,231699,1796301,w0,w1,6551005] [1537]) [6,2049,231699,1911399,1985195,w0,w1] [2049] e) [6,2049,239959,w5,w0,w1,6551005] [1547,2058] (n (s [6,2049,w4,w5,2067250,w0,4198338] [898,1154,1538,1672,2051,2690]) [6,2049,w4,1296795,w0,w1,7601629] [1539,2050] e)))) [6,2049,764247,1296795,w0,w1,6551005] [1537] (n (n (n (n (s [6,2049,764247,1796301,1911399,w0,w1] [2051,2690]) [6,2049,764247,1796301,1985195,w0,w1] [2049] e) [6,2049,764247,1796301,2058991,w0,w1] [2049] (n (s [6,2049,764247,1796301,w0,w1,6551005] [1537]) [6,2049,1796301,1829343,2058991,w0,w1] [2049] e)) [6,2049,1796301,1829343,w0,w1,6551005] [1537] (n (n (s [6,2049,1796301,w0,w1,6551005,8156909] [1153]) [6,2051,w2,w4,1985195,w0,w1] [1666,2049] e) [6,2051,w2,1796301,w3,w0,w1] [1284,2049] (n (s [6,2052,w2,w4,w5,1838626,6295548] [898]) [6,2052,w2,w4,1199241,w3,6295548] [902,1154,1538,2050,2690] e))) [6,2052,w2,601157,w5,w3,6295548] [910,1162,1544,2058,2698] (n (n (n (s [6,2052,w2,w5,w3,2100349,w1] [910,1160,1546,2699]) [6,2052,w2,1796301,w3,w0,4198337] [900] e) [6,2052,w2,1796301,w3,2100285,w1] [900,1153,2049] (n (s [6,2052,w2,1985195,2698365,3296445,w1] [1160,2697]) [6,2052,w4,w5,2067250,w0,4198338] [898,1154,1538,2050,2690] e)) [6,2052,w4,w5,2067250,2100286,w1] [899,1154,1538,2051,2690] (n (n (s [6,2052,764247,w5,1911399,2698365,w1] [1162,2699]) [6,2053,w2,w5,w3,2100348,w1] [2698] e) [6,2053,w2,w5,1837666,w0,w1] [2699] (n (s [6,2053,w2,1198281,w3,w0,w1] [2697]) [6,2053,w2,1796301,w3,w0,4190271] [] e))))))
def N_12 : BT := n T_10 [6,2049,w2,1796301,w3,w0,4198340] [] T_11
def N_13 : BT := n N_9 [5,231734,1296795,1911399,2698365,w1] [] N_12
def N_14 : BT := n N_6 [5,w2,1796301,w3,w0,4198353] [] N_13
def T_15 : BT := (n (n (n (n (n (n (s [6,2053,w2,1796301,w3,w0,4198341] [900]) [6,2053,w2,1796301,w3,2100285,w1] [900,1153,2049] (s [6,2053,w2,1796301,w3,w1,6288323] [2049])) [6,2053,w2,1796301,1837607,w0,w1] [] (n (s [6,2053,w2,1796301,1911399,w0,w1] [2049]) [6,2053,w2,1796301,1985195,w0,w1] [2057,2696] e)) [6,2053,w2,1796301,2058991,w0,w1] [2049] (n (n (s [6,2053,w2,1796301,w0,w1,6551005] [1537]) [6,2053,w2,1829343,w3,w0,w1] [2049] e) [6,2053,w2,w3,w0,w1,6592306] [1537] (n (s [6,2053,w2,1911399,1985195,w0,w1] [2049]) [6,2053,w2,1985195,w0,3894525,w1] [2696] e))) [6,2053,w2,1985195,2698365,3296445,w1] [1160,2697] (n (n (n (s [6,2054,w4,w5,2067250,w0,w1] [2051,2690]) [6,2060,w2,1796301,w3,w0,4198337] [900] e) [6,2060,w2,1796301,w3,2100285,w1] [900,1153,2049] (n (s [6,2061,w2,1796301,w3,w0,w1] [2049]) [6,2061,w2,1796301,w3,2100285,w1] [900,1153,2049] e)) [6,2068,764247,w5,w3,2329918,4190271] [1550] (n (n (s [6,2068,764247,w5,w3,2329918,w1] [1550,2703]) [6,2068,764247,w5,w3,2329918,4198356] [911,1164,1550,2063,2703] e) [6,2068,764247,w5,w3,w1,5690242] [1164,2063] (n (s [6,2068,764247,w5,1837622,2329918,w1] [910,1162,1550,2062,2702]) [6,2068,764247,w5,1837622,2698365,w1] [1156,2702] e)))) [6,2068,764247,w5,1911399,2698365,w1] [1162,2699] (n (n (n (n (s [6,2068,764247,w5,1985195,2329918,w1] [1162,1550,2703]) [6,2068,764247,w5,1985195,2698365,w1] [1162,2703] (s [6,2068,764247,w5,2329918,w1,6551005] [2059])) [6,2068,764247,w5,2698365,w1,6551005] [1162,2059] (n (s [6,2068,w5,1829343,w3,2698365,w1] [908,2701]) [6,2068,w5,w3,2329918,2698365,w1] [908,1166,2701] e)) [6,2068,w5,w3,2329918,w1,7624360] [1166,2063] (n (n (s [6,2076,w4,w5,w3,2329918,w1] [1542,2693]) [6,2076,w4,w5,w3,2862463,w1] [2693] e) [6,2076,w4,w5,w3,3927551,w1] [2693] (n (s [6,2076,w4,1296795,w3,2329918,w1] [1542,2693]) [6,2076,w4,1296795,w3,3296445,w1] [900,2693] e))) [6,2076,w4,1829343,w3,3296445,w1] [900,2693] (n (n (n (s [6,2116,2185,w2,w3,w0,w1] [1164,1544]) [6,2116,w2,w4,w5,1838626,6295548] [898] e) [6,2116,w2,w4,1199241,w3,6295548] [902,1154,1538,2050,2690] (n (s [6,2116,w2,601157,w5,w3,6295548] [910,1162,1544,2058,2698]) [6,2116,w2,w5,w3,w0,4198337] [910,1160,1546] e)) [6,2117,3072,w2,w5,w3,6295548] [1284] (n (n (s [6,2117,w2,w5,w3,w0,4190271] []) [6,2117,w2,w5,w3,w0,w1] [] e) [6,2117,w2,w5,w3,w0,4198337] [910,1160,1546] (n (s [6,2117,w2,w5,w3,w0,4198340] [2059]) [6,2117,w2,w5,w3,w0,4198341] [910,1160,1546,2058] e))))) [6,2117,w2,w5,w3,w0,4427730,6295548] [1284,2180] (n (n (n (n (n (s [6,2117,w2,w5,1837671,w0,w1] [906,2059,2698]) [6,2117,w2,w5,1985195,w0,w1] [] (s [6,2117,w2,w5,w0,w1,6551005] [])) [6,2117,w2,1198221,w3,w0,w1] [2056] (n (s [6,2117,w2,1198285,w3,w0,w1] [2057,2696]) [6,2117,w2,1296795,w3,w0,w1] [] e)) [6,2117,w2,1296795,w3,w0,w1,6295548] [2181,2820] (n (n (s [6,2117,w2,1796301,w3,w0,w1] [2049]) [6,2117,w2,w3,w0,w1,7190390] [] e) [6,2117,w2,1985195,w0,3296445,w1] [] (n (s [6,2117,w2,1985195,w0,w1,7491581] []) [6,2388,w2,w5,w3,w0,4796357,6295548] [1160,1546] e))) [6,2388,764247,w5,w3,w0,4427730] [1550,2062] (n (n (n (s [6,3072,73797,w2,w5,w3,6295548] []) [6,3072,73797,w2,w5,6295548,6551005] [] e) [6,3072,229650,w4,w5,w3,6295548] [900,1160] (n (s [6,3072,w2,w4,w5,w3,2093059] [900,1162,1538]) [6,3072,w2,w4,w5,w3,2096131] [] e)) [6,3072,w2,w4,w5,w3,6292476] [] (n (n (s [6,3072,w2,w4,w5,w3,6295548] [900,1162,1538]) [6,3072,w2,w4,w5,w3,6295549] [900,1162,1538] e) [6,3072,w2,w4,w5,w3,6361084] [900,1162,1538] (n (s [6,3072,w2,w4,w5,1837603,6295548] [902,1162,1538]) [6,3072,w2,w4,w5,1837606,6295548] [902,1162,1538] e)))) [6,3072,w2,w4,w5,1837618,6295548] [902,1162,1538] (n (n (n (n (s [6,3072,w2,w4,w5,1837670,6295548] [902,1162,1538]) [6,3072,w2,w4,w5,1837874,6295548] [902,1162,1538] e) [6,3072,w2,w4,w5,1838626,2093059] [898,1160] (n (s [6,3072,w2,w4,w5,1838626,6295548] [898,1160]) [6,3072,w2,w4,w5,1903138,6295548] [898,1160] e)) [6,3072,w2,w4,w5,1911399,2093059] [898,1160] (n (n (s [6,3072,w2,w4,w5,1911399,6295548] [898,1160]) [6,3072,w2,w4,w5,1912423,6295548] [898,1160] e) [6,3072,w2,w4,w5,2058991,6295548] [898,1160] (n (s [6,3072,w2,w4,w5,2093059,6551005] [898,1160]) [6,3072,w2,w4,w5,6295548,6403412] [898,1160] e))) [6,3072,w2,w4,w5,6295548,6549981] [898,1160] (n (n (n (s [6,3072,w2,w4,w5,6295548,6551005] [898,1160]) [6,3072,w2,w4,w5,6295548,6553053] [898,1160] e) [6,3072,w2,w4,w5,6295548,7077341] [898,1160] (n (s [6,3072,w2,w4,1199241,1838626,6295548] [898]) [6,3072,w2,w4,1199241,1911399,6295548] [898] e)) [6,3072,w2,w4,1199241,1985195,6295548] [898,1160] (n (n (s [6,3072,w2,w4,1199241,1986219,6295548] [898,1160]) [6,3072,w2,w4,1199241,6295548,6551005] [898] e) [6,3072,w2,w4,1296795,1911399,6295548] [898,1538] (n (s [6,3072,w2,w4,1296795,6295548,6551005] [898]) [6,3072,w2,w4,1985195,3296445,6295548] [898] e))))))
def T_16 : BT := (n (n (n (n (n (n (s [6,3072,w2,w4,1985195,6295548,7491581] [898]) [6,3072,w2,w4,6295548,6551005,7190390] [898] (s [6,3072,w2,601157,1199241,w3,6295548] [900])) [6,3072,w2,601157,1296795,w3,6295548] [900] (n (s [6,3072,w2,601157,w3,6295548,7190390] [900]) [6,3072,w2,764247,1296795,w3,6295548] [900,1160] e)) [6,3072,w2,764247,w3,1985195,6295548] [908,1164] (n (n (s [6,3072,w2,764247,w3,6295548,7190390] [900]) [6,3072,w2,1796301,w3,w0,4198337] [900] e) [6,3072,w2,w3,6295548,7190390,7788474] [900] (n (s [6,3073,w2,w4,w5,w3,6295548] [900,1162,1538]) [6,3073,w2,1796301,w3,w0,w1] [2049] e))) [6,3076,w2,w4,w5,w3,2093059] [900,1162,1538] (n (n (n (s [6,3076,w2,w4,w5,w3,6295548] [900,1162,1538]) [6,3076,w2,w4,w5,1838630,6295548] [898,1160] e) [6,3076,w2,w4,w5,1911399,6295548] [898,1160] (n (s [6,3076,w2,w4,w5,1985195,6295548] [898,1160,2056]) [6,3076,w2,w4,w5,6295548,6551005] [898,1160] e)) [6,3076,w2,w4,1199245,w3,6295548] [900,1538,2690] (n (n (s [6,3076,w2,w4,1296795,w3,6295548] [902,1538,2050]) [6,3076,w2,w4,w3,6295548,7190390] [902,1538] e) [6,3076,w2,601157,w5,w3,6295548] [908,1162,2056,2698] (n (s [6,3076,w2,764247,w5,w3,6295548] [910,1162,1544,2058]) [6,3076,w2,w5,w3,6295548,7788474] [910,1160,1546] e)))) [6,3076,w2,w5,1911399,4796357,6295548] [906,1160,1545] (n (n (n (n (s [6,3084,w2,w4,w5,w3,6295548] [900,1162,1538]) [6,3092,w2,w4,w5,w3,6295548] [900,1162,1538] e) [6,3092,w2,764247,w5,w3,6295548] [910,1162,1544,2058] (n (s [6,3092,764247,w5,w3,2329918,w1] [1550,2703]) [6,3140,w2,w4,w5,w3,6295548] [900,1162,1538] e)) [6,3140,w2,601157,w5,w3,6295548] [908,1162,2056,2698] (n (n (s [6,3145,w2,w4,w5,w3,6295548] [900,1162,1539]) [6,3145,w2,1796301,w3,w0,w1] [2049,2696] e) [6,8261,16521,w2,w3,2067250,w0,w1] [] (n (s [6,8261,16521,w2,w3,w0,w1] [1164,1284,1544]) [6,8261,w2,w5,w3,2083771,w0,w1] [] e))) [6,8261,w2,w5,w3,w0,4190271] [] (n (n (n (s [6,8261,w2,w5,w3,w0,w1] []) [6,8261,w2,w5,1845863,w0,w1] [] e) [6,8261,w2,w5,1985195,w0,w1] [] (n (s [6,8261,w2,w5,w0,w1,6551005] []) [6,8261,w2,1296795,w3,w0,w1] [] e)) [6,8261,w2,w3,2083771,w0,w1] [1346] (n (n (s [6,8261,w2,w3,2083771,w0,w1,6321357] [900]) [6,8261,w2,w3,w0,w1,7190390] [] e) [6,8261,w5,w0,w1,6551005,8156909] [] (n (s [6,10309,w2,w5,w3,w0,w1] []) [6,67584,147593,w2,1911399,w0,w1] [904,2057,2696] e))))) [6,67584,w2,w4,w5,1838626,6295548] [1538] (n (n (n (n (n (s [6,67584,w2,601157,w5,w3,6295548] [906,1162,2056,2698]) [6,67584,w2,862823,w5,w0,w1] [1544,1666,2057,2696] (s [6,67584,w2,862823,w0,w1,7190390] [1537])) [6,67584,w2,w5,1911399,w0,4198337] [1160,2057,2696] (n (s [6,67584,w2,w5,1911399,w0,5246912] [1160,2056,2696]) [6,67584,w2,1796301,w3,w0,4198337] [2049] e)) [6,67584,w2,1911399,w0,w1,8241014] [1537] (n (n (s [6,67584,231699,w5,1911399,w0,w1] [2059,2698]) [6,67584,764247,1296795,1911399,w0,w1] [2049] e) [6,67584,1050624,1296795,1911399,w0,w1] [900,2061,2177,2700] (n (s [6,67584,w5,1280274,1911399,w0,w1] [904,2059,2698]) [6,67585,67586,1296795,1911399,w0,w1] [2051,2177,2690] e))) [6,67585,w2,w5,1911399,w0,4190271] [2056] (n (n (n (s [6,67585,w2,w5,1911399,w0,w1] [2057,2696]) [6,67585,w2,w5,1911399,w0,4263873] [906,1160,1544,2056,2696] e) [6,67585,w2,w5,2058991,w0,w1] [2057,2696] (n (s [6,67585,w2,w5,w0,w1,6477208] [1545,2056]) [6,67585,w2,1263753,1911399,w0,w1] [2057,2696] e)) [6,67585,w2,1263755,1911399,w0,w1] [2057,2696] (n (n (s [6,67585,w2,1296795,1911399,w0,4190271] [2056]) [6,67585,w2,1296795,1911399,w0,w1] [2057,2696] e) [6,67585,w2,1296795,1911399,w0,4263873] [1160,1544,2696] (n (s [6,67585,w2,1296795,w0,w1,6477208] [1545,2056]) [6,67585,w2,1796301,w3,w0,4190271] [] e)))) [6,67585,w2,1796301,w3,w0,w1] [2049] (n (n (n (n (s [6,67585,w2,1796301,w3,w0,4263873] []) [6,67585,w2,1796301,1903139,w0,w1] [2049] e) [6,67585,w2,1796301,1911399,w0,w1] [2049] (n (s [6,67585,w2,1796301,1985195,w0,w1] [2057,2696]) [6,67585,w2,1796301,2058991,w0,w1] [2049] e)) [6,67585,w2,1796301,w0,w1,6551005] [1537] (n (n (s [6,67585,w2,1829343,w3,w0,4190271] []) [6,67585,w2,1829343,w3,w0,w1] [] e) [6,67585,w2,1829343,w3,w0,4263873] [] (n (s [6,67585,w2,1829343,1903139,w0,w1] [2049]) [6,67585,w2,1829343,1911399,w0,w1] [2049] e))) [6,67585,w2,1829343,w0,w1,6551005] [] (n (n (n (s [6,67585,w2,w3,2058991,w0,w1] [2053,2692]) [6,67585,w2,w3,2092031,w0,w1] [] e) [6,67585,w2,w3,w0,w1,6559264] [] (n (s [6,67585,w2,w3,w0,w1,6592306] [1537]) [6,67585,w2,1911399,1985195,w0,w1] [2049] e)) [6,67585,w2,1911399,2058991,w0,w1] [2049] (n (n (s [6,67585,w2,1911399,2083771,w0,w1] [2049]) [6,67585,w2,1911399,2092031,w0,w1] [2049] e) [6,67585,w2,1911399,w0,w1,7091812] [1537] (n (s [6,67585,w2,1911399,w0,w1,7190390] [1537]) [6,67585,231699,w5,1911399,w0,w1] [2059,2698] e))))))
def N_17 : BT := n T_15 [6,3072,w2,w4,1985195,6295548,6551005] [898] T_16
def T_18 : BT := (n (n (n (n (n (n (s [6,67585,w5,1280275,1911399,w0,w1] [2059,2698]) [6,67585,w5,1296795,1911399,w0,4190271] [2058] (s [6,67585,w5,1296795,1911399,w0,w1] [2059,2698])) [6,67585,w5,1296795,1911399,w0,4263873] [1162,1546,2058,2698] (n (s [6,67585,w5,1296795,2058991,w0,w1] [2059,2698]) [6,67585,w5,1296795,w0,w1,6477208] [1547,2058] e)) [6,67585,w5,1911399,w0,w1,7091812] [1551,2062,2702] (n (n (s [6,67585,w5,1911399,w0,w1,8156909] [1551,2062]) [6,67585,1296795,1796301,1985195,w0,w1] [2059,2698] e) [6,67585,1296795,1911399,w0,2329918,w1] [1545,2696] (n (s [6,67585,1296795,1911399,w0,3296445,w1] [1545,2698]) [6,67585,1296795,1911399,w0,w1,7190390] [1545,2056] e))) [6,67585,1296795,1911399,w0,w1,8156909] [1545,2056] (n (n (n (s [6,67585,1796301,w3,w0,w1,8156909] [1541,2052]) [6,67585,1829343,w3,w0,2329918,w1] [] e) [6,67585,1829343,w3,w0,w1,8156909] [] (n (s [6,67588,1296795,w3,2329918,2698365,w1] [1158,2701]) [6,67589,w2,w5,1911399,w0,w1] [2057,2696] e)) [6,67589,w2,1296795,1911399,w0,w1] [2057,2696] (n (n (s [6,67589,w2,1796301,w3,w0,w1] [2049]) [6,67589,w2,1829343,w3,w0,w1] [] e) [6,67589,w5,1296795,1911399,w0,w1] [2059,2698] (n (s [6,67609,w2,w5,1911399,w0,w1] [2057,2696]) [6,67609,w2,1296795,1911399,w0,w1] [2057,2696] e)))) [6,67609,w2,1796301,w3,w0,w1] [2049] (n (n (n (n (s [6,67609,w2,1829343,w3,w0,w1] []) [6,67609,w4,w5,w3,2329918,w1] [1542,2693] e) [6,67609,w4,w5,w3,3395007,w1] [2693] (n (s [6,67609,w4,1296795,w3,2329918,w1] [1542,2695]) [6,67609,w4,1296795,w3,3296445,w1] [900,2695] e)) [6,67609,w5,1296795,1911399,w0,w1] [2059,2698] (n (n (s [6,67653,w2,w5,w3,w0,w1] []) [6,67653,w2,1296795,w3,w0,w1] [] e) [6,67653,w5,1296795,w3,w0,w1] [] (n (s [6,67993,w2,w4,w3,w0,w1] [2177]) [6,68608,w2,w4,w5,w3,6295548] [900,1162,1538] e))) [6,68688,w2,w4,w5,w3,6295548] [901,1162,1539] (n (n (n (s [6,73733,w2,w5,1837666,w0,w1] []) [6,73733,w2,w5,1911399,w0,w1] [] e) [6,73733,w2,w5,w0,w1,6550941] [] (n (s [6,73796,w2,w5,w0,w1,6929749] [906]) [6,73797,98578,w5,w3,w0,w1] [] e)) [6,73797,98578,w5,w0,w1,6551005] [] (n (n (s [6,73797,98578,w0,w1,6551005,7190390] []) [6,73797,147593,w2,w3,w0,4190271] [] e) [6,73797,147593,w2,w3,w0,w1] [] (n (s [6,73797,147593,w2,1911399,w0,w1] []) [6,73797,147593,w2,w0,4190271,6551005] [] e))))) [6,73797,147593,w2,w0,w1,6551005] [] (n (n (n (n (n (s [6,73797,147593,w2,w0,w1,7077341] []) [6,73797,147593,239959,w3,w0,w1] [] (s [6,73797,147593,239959,w0,w1,6551005] [])) [6,73797,147593,w3,w0,w1,8156909] [] (n (s [6,73797,147593,w0,w1,6551005,8156909] []) [6,73797,149641,w2,w3,w0,w1] [] e)) [6,73797,149641,w2,w0,w1,6551005] [] (n (n (s [6,73797,149641,w2,w0,w1,7077341] []) [6,73797,164114,w5,w3,w0,w1] [] e) [6,73797,164114,w5,w0,w1,6551005] [] (n (s [6,73797,166162,w5,w3,w0,w1] []) [6,73797,166162,w5,w0,w1,6551005] [] e))) [6,73797,229648,w2,1985195,w0,w1] [] (n (n (n (s [6,73797,229650,w5,w3,w0,w1] []) [6,73797,w2,246169,w3,w0,w1] [1544] e) [6,73797,w2,246169,w0,w1,6551005] [] (n (s [6,73797,w2,248219,w3,w0,w1] []) [6,73797,w2,248219,w0,w1,6551005] [] e)) [6,73797,w2,1065097,w3,w0,w1] [908] (n (n (s [6,73797,w2,1065097,w0,w1,6551005] [908]) [6,73797,w2,1196169,w3,w0,w1] [] e) [6,73797,w2,w5,1311266,w0,w1] [] (n (s [6,73797,w2,w5,w3,2098236,w1] []) [6,73797,w2,w5,w3,w0,4190271] [] e)))) [6,73797,w2,w5,w3,w0,w1] [] (n (n (n (n (s [6,73797,w2,w5,w3,w0,4198337] [910,1160]) [6,73797,w2,w5,w3,w0,4198338] [] e) [6,73797,w2,w5,w3,w0,4198340] [] (n (s [6,73797,w2,w5,w3,w0,4198344] []) [6,73797,w2,w5,w3,w0,4198352] [] e)) [6,73797,w2,w5,w3,w0,4198368] [] (n (n (s [6,73797,w2,w5,w3,w0,4263872] []) [6,73797,w2,w5,w3,w0,4329408] [910] e) [6,73797,w2,w5,w3,w0,5246912] [] (n (s [6,73797,w2,w5,w3,4190271,6288323] []) [6,73797,w2,w5,1837603,w0,w1] [910] e))) [6,73797,w2,w5,1837606,w0,w1] [] (n (n (n (s [6,73797,w2,w5,1837610,w0,w1] []) [6,73797,w2,w5,1837618,w0,w1] [] e) [6,73797,w2,w5,1838626,w0,w1] [] (n (s [6,73797,w2,w5,1903138,w0,w1] []) [6,73797,w2,w5,1911399,w0,4190271] [] e)) [6,73797,w2,w5,1911399,w0,w1] [] (n (n (s [6,73797,w2,w5,1968674,w0,w1] [910]) [6,73797,w2,w5,1985195,w0,4190271] [] e) [6,73797,w2,w5,1985195,w0,w1] [] (n (s [6,73797,w2,w5,2058991,w0,w1] []) [6,73797,w2,w5,w0,4190271,6551005] [] e))))))
def T_19 : BT := (n (n (n (n (n (n (s [6,73797,w2,w5,w0,4190271,7601629] []) [6,73797,w2,w5,w0,w1,6403412] [] (s [6,73797,w2,w5,w0,w1,6419933] [906])) [6,73797,w2,w5,w0,w1,6477208] [] (n (s [6,73797,w2,w5,w0,w1,6549981] []) [6,73797,w2,w5,w0,w1,6550749] [] e)) [6,73797,w2,w5,w0,w1,6550877] [] (n (n (s [6,73797,w2,w5,w0,w1,6551005] []) [6,73797,w2,w5,w0,w1,6553053] [] e) [6,73797,w2,w5,w0,w1,7077341] [] (n (s [6,73797,w2,w5,w0,w1,7601629] []) [6,73797,w2,w5,w0,w1,8125917] [] e))) [6,73797,w2,w5,w0,4198337,6551005] [906,1160] (n (n (n (s [6,73797,w2,w5,w0,4198338,6551005] []) [6,73797,w2,w5,w0,4198340,6551005] [] e) [6,73797,w2,w5,w0,4198344,6551005] [] (n (s [6,73797,w2,w5,w0,4198352,6551005] []) [6,73797,w2,w5,w0,4198368,6551005] [] e)) [6,73797,w2,w5,w0,4263872,6551005] [] (n (n (s [6,73797,w2,w5,w0,4329408,6551005] [906]) [6,73797,w2,w5,w0,5246912,6551005] [] e) [6,73797,w2,w5,4190271,6288323,6551005] [] (n (s [6,73797,w2,1198219,w3,w0,w1] []) [6,73797,w2,1198219,w0,w1,6551005] [] e)))) [6,73797,w2,1198221,w3,w0,w1] [] (n (n (n (n (s [6,73797,w2,1198221,w0,w1,6551005] []) [6,73797,w2,1198233,w3,w0,w1] [] e) [6,73797,w2,1198233,w0,w1,6551005] [] (n (s [6,73797,w2,1198249,w3,w0,w1] []) [6,73797,w2,1198249,w0,w1,6551005] [] e)) [6,73797,w2,1199241,w3,w0,w1] [] (n (n (s [6,73797,w2,1199241,w0,w1,6551005] []) [6,73797,w2,1263753,w3,w0,w1] [] e) [6,73797,w2,1263753,w0,w1,6551005] [] (n (s [6,73797,w2,1272013,1985195,w0,w1] []) [6,73797,w2,1296793,w3,w0,w1] [] e))) [6,73797,w2,1296793,w0,w1,6551005] [] (n (n (n (s [6,73797,w2,1296795,w3,w0,4190271] []) [6,73797,w2,1296795,w3,w0,w1] [] e) [6,73797,w2,1296795,1911399,w0,w1] [] (n (s [6,73797,w2,1296795,w0,4190271,6551005] []) [6,73797,w2,1296795,w0,w1,6551005] [] e)) [6,73797,w2,1296795,w0,w1,7077341] [] (n (n (s [6,73797,w2,1296795,w0,w1,7601629] []) [6,73797,w2,1722505,w3,w0,w1] [] e) [6,73797,w2,1722505,w0,w1,6551005] [] (n (s [6,73797,w2,1796301,1985195,w0,w1] []) [6,73797,w2,w3,1985195,w0,4190271] [] e))))) [6,73797,w2,w3,1985195,w0,w1] [] (n (n (n (n (n (s [6,73797,w2,w3,2083771,w0,w1] []) [6,73797,w2,w3,w0,4190271,7190390] [] (s [6,73797,w2,w3,w0,w1,6403412] [])) [6,73797,w2,w3,w0,w1,7091812] [] (n (s [6,73797,w2,w3,w0,w1,7190390] []) [6,73797,w2,w3,w0,w1,7323510] [900] e)) [6,73797,w2,w3,w0,w1,8241014] [] (n (n (s [6,73797,w2,1911399,1985195,w0,w1] []) [6,73797,w2,1911399,w0,w1,7190390] [] e) [6,73797,w2,1985195,w0,3296445,w1] [] (n (s [6,73797,w2,1985195,w0,3935806,w1] []) [6,73797,w2,1985195,w0,4190271,6551005] [] e))) [6,73797,w2,1985195,w0,w1,6551005] [] (n (n (n (s [6,73797,w2,1985195,w0,w1,6553085] []) [6,73797,w2,1985195,w0,w1,7077341] [] e) [6,73797,w2,1985195,w0,w1,7190390] [] (n (s [6,73797,w2,1985195,w0,w1,7601629] []) [6,73797,w2,2083771,w0,w1,6551005] [] e)) [6,73797,w2,w0,4190271,6551005,7190390] [] (n (n (s [6,73797,w2,w0,w1,6403412,6551005] []) [6,73797,w2,w0,w1,6403412,7190390] [] e) [6,73797,w2,w0,w1,6551005,7091812] [] (n (s [6,73797,w2,w0,w1,6551005,7190390] []) [6,73797,w2,w0,w1,6551005,7323510] [] e)))) [6,73797,w2,w0,w1,6551005,8241014] [] (n (n (n (n (s [6,73797,w2,w0,w1,7077341,7190390] []) [6,73797,w2,w0,w1,7190390,7601629] [] e) [6,73797,231699,w5,w3,w0,w1] [] (n (s [6,73797,231699,w5,w0,w1,6551005] []) [6,73797,231702,w5,w3,w0,w1] [] e)) [6,73797,231702,w5,w0,w1,6551005] [] (n (n (s [6,73797,231706,w5,w3,w0,w1] []) [6,73797,231706,w5,w0,w1,6551005] [] e) [6,73797,231730,w5,w3,w0,w1] [] (n (s [6,73797,231730,w5,w0,w1,6551005] []) [6,73797,232722,w5,w3,w0,w1] [] e))) [6,73797,232722,w5,w0,w1,6551005] [] (n (n (n (s [6,73797,239959,w5,w3,w0,4190271] []) [6,73797,239959,w5,w3,w0,w1] [] e) [6,73797,239959,w5,1911399,w0,w1] [] (n (s [6,73797,239959,w5,1985195,w0,w1] []) [6,73797,239959,w5,w0,4190271,6551005] [] e)) [6,73797,239959,w5,w0,w1,6551005] [] (n (n (s [6,73797,239959,w5,w0,w1,7077341] []) [6,73797,239959,w5,w0,w1,7601629] [] e) [6,73797,239959,w3,1985195,w0,w1] [] (n (s [6,73797,239959,w3,w0,w1,7190390] []) [6,73797,239959,1985195,w0,w1,6551005] [] e))))))
def N_20 : BT := n T_18 [6,73797,w2,w5,w0,4190271,7077341] [] T_19
def N_21 : BT := n N_17 [6,67585,1050625,1296795,1911399,w0,w1] [2061,2177,2700] N_20
def T_22 : BT := (n (n (n (n (n (n (s [6,73797,248219,w5,w3,w0,w1] []) [6,73797,248219,w5,w0,w1,6551005] [] (s [6,73797,764247,w5,w0,w1,7077341] [])) [6,73797,1065097,w0,w1,6551005,8156909] [] (n (s [6,73797,w5,1280274,w3,w0,w1] []) [6,73797,w5,1280274,w0,w1,6551005] [] e)) [6,73797,w5,1296795,w3,w0,4190271] [] (n (n (s [6,73797,w5,1296795,w3,w0,w1] []) [6,73797,w5,1296795,1911399,w0,w1] [] e) [6,73797,w5,1296795,1985195,w0,w1] [] (n (s [6,73797,w5,1296795,w0,4190271,6551005] []) [6,73797,w5,1296795,w0,w1,6551005] [] e))) [6,73797,w5,1296795,w0,w1,7077341] [] (n (n (n (s [6,73797,w5,1296795,w0,w1,7601629] []) [6,73797,w5,1305055,w3,w0,w1] [] e) [6,73797,w5,1305055,w0,w1,6551005] [] (n (s [6,73797,w5,w3,w0,4190271,8156909] []) [6,73797,w5,w3,w0,w1,7091812] [] e)) [6,73797,w5,w3,w0,w1,8148648] [] (n (n (s [6,73797,w5,w3,w0,w1,8156909] []) [6,73797,w5,w3,w0,w1,8222445] [] e) [6,73797,w5,w3,w0,w1,8224493] [] (n (s [6,73797,w5,w3,w0,w1,8290029] []) [6,73797,w5,1911399,w0,w1,8156909] [] e)))) [6,73797,w5,1985195,w0,w1,8156909] [] (n (n (n (n (s [6,73797,w5,w0,4190271,6551005,8156909] []) [6,73797,w5,w0,w1,6551005,7091812] [] e) [6,73797,w5,w0,w1,6551005,8148648] [] (n (s [6,73797,w5,w0,w1,6551005,8156909] []) [6,73797,w5,w0,w1,6551005,8222445] [] e)) [6,73797,w5,w0,w1,6551005,8224493] [] (n (n (s [6,73797,w5,w0,w1,6551005,8290029] []) [6,73797,w5,w0,w1,7077341,8156909] [] e) [6,73797,w5,w0,w1,7601629,8156909] [] (n (s [6,73797,1296795,w3,w0,2329918,w1] []) [6,73797,1296795,w3,w0,3296445,w1] [] e))) [6,73797,1296795,w3,w0,w1,7190390] [] (n (n (n (s [6,73797,1296795,w3,w0,w1,8156909] []) [6,73797,1296795,w0,2329918,w1,6551005] [] e) [6,73797,1296795,w0,3296445,w1,6551005] [] (n (s [6,73797,1296795,w0,w1,6551005,7190390] []) [6,73797,1296795,w0,w1,6551005,8156909] [] e)) [6,73797,w3,1985195,w0,w1,8156909] [] (n (n (s [6,73797,w3,w0,w1,7190390,8156909] []) [6,73797,1985195,w0,w1,6551005,8156909] [] e) [6,73797,w0,w1,6551005,7190390,8156909] [] (n (s [6,73805,w2,w5,w3,w0,w1] []) [6,73805,w2,w5,w0,w1,6551005] [] e))))) [6,73813,w2,w5,w3,w0,w1] [] (n (n (n (n (n (s [6,73813,w2,w5,w0,w1,6551005] []) [6,74821,w2,w5,w3,w0,w1] [] (s [6,74821,w2,w5,w0,w1,6551005] [])) [6,75845,149641,w2,w3,w0,w1] [] (n (s [6,75845,149641,w2,w0,w1,6551005] []) [6,75845,w2,w5,w3,w0,4190271] [] e)) [6,75845,w2,w5,w3,w0,w1] [] (n (n (s [6,75845,w2,w5,1911399,w0,w1] []) [6,75845,w2,w5,1985195,w0,w1] [] e) [6,75845,w2,w5,w0,4190271,6551005] [] (n (s [6,75845,w2,w5,w0,4190271,7601629] []) [6,75845,w2,w5,w0,w1,6403412] [] e))) [6,75845,w2,w5,w0,w1,6551005] [] (n (n (n (s [6,75845,w2,w5,w0,w1,6553053] []) [6,75845,w2,w5,w0,w1,7077341] [] e) [6,75845,w2,w5,w0,w1,7601629] [] (n (s [6,75845,w2,w5,w0,w1,8125917] []) [6,75845,w2,1296795,w3,w0,w1] [] e)) [6,75845,w2,1296795,w0,w1,6551005] [] (n (n (s [6,75845,w2,1296795,w0,w1,7601629] []) [6,75845,w2,w3,1985195,w0,w1] [] e) [6,75845,w2,w3,w0,w1,6403412] [] (n (s [6,75845,w2,w3,w0,w1,7190390] []) [6,75845,w2,1985195,w0,w1,6551005] [] e)))) [6,75845,w2,1985195,w0,w1,6553085] [] (n (n (n (n (s [6,75845,w2,1985195,w0,w1,7601629] []) [6,75845,w2,w0,w1,6403412,7601629] [] e) [6,75845,w2,w0,w1,6551005,7190390] [] (n (s [6,75845,w2,w0,w1,7190390,7601629] []) [6,75845,239959,w5,w3,w0,w1] [] e)) [6,75845,239959,w5,w0,w1,6551005] [] (n (n (s [6,75845,239959,w5,w0,w1,7601629] []) [6,75845,w5,1296795,w3,w0,w1] [] e) [6,75845,w5,1296795,w0,w1,6551005] [] (n (s [6,75845,w5,1296795,w0,w1,7601629] []) [6,75845,w5,w3,w0,w1,8156909] [] e))) [6,75845,w5,w0,w1,6551005,8156909] [] (n (n (n (s [6,75845,w5,w0,w1,7601629,8156909] []) [6,75847,w2,w5,w3,w0,w1] [] e) [6,75847,w2,w5,w0,w1,6551005] [] (n (s [6,75853,w2,w5,w3,w0,w1] []) [6,75853,w2,w5,w0,w1,6551005] [] e)) [6,75861,w2,w5,w3,w0,w1] [] (n (n (s [6,75861,w2,w5,w0,w1,6551005] []) [6,75877,w2,w5,w3,w0,w1] [] e) [6,75877,w2,w5,1911399,w0,w1] [] (n (s [6,75877,w2,w5,w0,w1,6551005] []) [6,75877,w2,w5,w0,w1,6553085] [] e))))))
def T_23 : BT := (n (n (n (n (n (n (s [6,76869,w2,w5,w0,w1,6551005] []) [6,198656,w2,1796301,w3,w0,4198337] [2049] (s [6,198656,231699,1796301,w3,w0,w1] [2053,2692])) [6,198657,w2,1796301,w3,w0,w1] [2049] (n (s [6,198658,w4,w5,2067250,w0,w1] [2051,2690]) [6,198658,w4,w5,2075511,w0,w1] [] e)) [6,198658,w4,w5,2092031,w0,w1] [] (n (n (s [6,198658,w4,1296795,w3,w0,w1] []) [6,198658,w4,1296795,1911399,w0,w1] [] e) [6,198658,w4,w3,2083771,w0,w1] [] (n (s [6,198658,764247,w3,1985195,w0,w1] []) [6,198672,w4,w5,w3,2329918,w1] [1542,2693] e))) [6,204869,w2,w5,w3,w0,w1] [] (n (n (n (s [6,204869,w2,w5,w0,w1,6551005] []) [6,206917,w2,w5,w3,w0,w1] [] e) [6,206917,w2,w5,w0,w1,6551005] [] (n (s [6,221389,w2,w4,1985195,w0,w1] []) [6,229378,w4,1296795,w3,w0,w1] [] e)) [6,229394,w4,w5,w3,2100540,4190271] [] (n (n (s [6,229394,w4,w5,w3,2100540,w1] []) [6,229394,w4,w5,1837858,w0,4190271] [] e) [6,229394,w4,w5,1837858,w0,w1] [] (n (s [6,229394,w4,1198473,w3,w0,4190271] []) [6,229394,w4,1198473,w3,w0,w1] [] e)))) [6,229394,w4,1296795,w3,w0,4190271] [] (n (n (n (n (s [6,229394,w4,1296795,w3,w0,w1] []) [6,229394,w4,1296795,w3,w0,4427730] [900] e) [6,229394,w4,1296795,w3,4190271,6288323] [] (n (s [6,229394,w4,1296795,w3,w1,6288323] []) [6,229394,w4,1296795,1911399,w0,4190271] [] e)) [6,229394,w4,1296795,1911399,w0,w1] [] (n (n (s [6,229394,w4,1296795,w0,4190271,6551005] []) [6,229394,w4,1296795,w0,w1,6551005] [] e) [6,229394,w4,w3,2083771,w0,4190271] [] (n (s [6,229394,w4,w3,2083771,w0,w1] []) [6,229394,w4,w3,w0,4190271,7091812] [] e))) [6,229394,w4,w3,w0,w1,7091812] [] (n (n (n (s [6,229394,763991,1296795,w3,w0,4190271] []) [6,229394,763991,1296795,w3,w0,w1] [2692] e) [6,229394,764247,1296795,w3,w0,4190271] [] (n (s [6,229394,764247,1296795,w3,w0,w1] []) [6,229394,764247,w3,1985195,w0,4190271] [] e)) [6,229394,764247,w3,1985195,w0,w1] [] (n (n (s [6,229394,764247,w3,w0,4190271,7190390] []) [6,229394,764247,w3,w0,w1,7190390] [] e) [6,229648,239959,w5,w3,w0,w1] [] (n (s [6,229648,239959,w5,w0,w1,6551005] []) [6,229648,w4,w5,w3,w0,4198338] [1538] e))))) [6,229648,w4,w5,w0,4198338,6551005] [] (n (n (n (n (n (s [6,229648,w4,1296795,w0,w1,7601629] []) [6,229648,764247,1296795,w3,w0,w1] [] (s [6,229648,764247,1296795,w0,w1,6551005] [])) [6,229650,598085,w5,w3,w0,w1] [] (n (s [6,229650,w4,w5,1835554,w0,w1] []) [6,229650,w4,w5,w3,2098236,w1] [] e)) [6,229650,w4,w5,w3,w0,4190271] [] (n (n (s [6,229650,w4,w5,w3,w0,w1] []) [6,229650,w4,w5,w3,w0,4198337] [] e) [6,229650,w4,w5,w3,w0,4198340] [] (n (s [6,229650,w4,w5,w3,w0,4198368] []) [6,229650,w4,w5,w3,w0,4722624] [] e))) [6,229650,w4,w5,w3,4190271,6288323] [] (n (n (n (s [6,229650,w4,w5,w3,6295548,8385535] []) [6,229650,w4,w5,1837603,w0,w1] [] e) [6,229650,w4,w5,1837606,w0,w1] [] (n (s [6,229650,w4,w5,1838626,w0,w1] []) [6,229650,w4,w5,1911399,w0,w1] [] e)) [6,229650,w4,w5,w0,4190271,6551005] [] (n (n (s [6,229650,w4,w5,w0,w1,6551005] []) [6,229650,w4,1198221,w3,w0,w1] [] e) [6,229650,w4,1198249,w3,w0,w1] [] (n (s [6,229650,w4,1199241,w3,w0,w1] []) [6,229650,w4,1296795,w3,w0,w1] [] e)))) [6,229650,w4,1722505,w3,w0,w1] [] (n (n (n (n (s [6,229650,w4,w3,1985195,w0,w1] []) [6,229650,w4,w3,w0,4190271,7190390] [] e) [6,229650,w4,w3,w0,w1,7190390] [] (n (s [6,229650,w4,w0,w1,6551005,7190390] []) [6,229650,1796301,w3,w0,w1,8386558] [] e)) [6,229650,w3,w0,w1,7190390,7788474] [] (n (n (s [6,231442,w4,1296795,w3,w0,4190271] []) [6,231442,w4,1296795,w3,w0,w1] [] e) [6,231696,w4,1296795,w0,w1,7601629] [] (n (s [6,w2,231699,1796301,w3,w0,4190271] []) [6,w2,231699,1796301,w3,w0,w1] [] e))) [6,w2,231699,1796301,w3,w0,4198337] [900,1156] (n (n (n (s [6,w2,231699,1796301,1837603,w0,w1] []) [6,w2,231699,1796301,1911399,w0,w1] [] e) [6,w2,231699,1796301,2058991,w0,w1] [] (n (s [6,w2,231699,1796301,w0,w1,6551005] []) [6,w2,231699,1829343,w3,w0,w1] [] e)) [6,w2,231699,w3,2058991,w0,w1] [] (n (n (s [6,w2,231699,w3,w0,w1,6592306] [2692]) [6,w2,231699,1911399,1985195,w0,w1] [] e) [6,w2,231703,1796301,w3,w0,w1] [] (n (s [6,w2,231734,w5,1911399,2698365,w1] [1288]) [6,w2,231734,w5,1911399,3935806,w1] [906,1546] e))))))
def N_24 : BT := n T_22 [6,76869,w2,w5,w3,w0,w1] [] T_23
def T_25 : BT := (n (n (n (n (n (n (s [6,w2,232722,w4,w5,w3,2093059] [900,1166,1290,1542,1666]) [6,w2,232722,w4,w5,w3,6295548] [900,1166,1290,1542,1666] (s [6,w2,232722,w4,w5,1838626,6295548] [898,1162,1290,1538,1666])) [6,w2,232722,w4,w5,1911399,6295548] [898,1538,1666] (n (s [6,w2,232722,w4,w5,6295548,6551005] [898,1162,1288,1538]) [6,w2,232722,w4,1199241,w3,6295548] [900,962,1164,1288,1542,1666] e)) [6,w2,232722,w4,1296795,w3,6295548] [902,1156,1288,1542,1666] (n (n (s [6,w2,232722,w4,1297819,w3,6295548] [902,962,1156,1542,1666]) [6,w2,232722,w4,w3,1985195,6295548] [902,1164,1292,2054,2178] e) [6,w2,232722,w4,w3,6295548,7190390] [902,1156,2694] (n (s [6,w2,232726,w4,w5,w3,6295548] [900,1166,1290,1542,1666]) [6,w2,232754,w4,w5,w3,6295548] [900,1166,1290,1542,1666] e))) [6,w2,237909,w4,1985195,w0,w1] [] (n (n (n (s [6,w2,237909,764247,1985195,w0,w1] []) [6,w2,237909,w5,w3,w0,4190271] [] e) [6,w2,237909,w5,w3,w0,w1] [] (n (s [6,w2,237909,w5,1911399,w0,w1] []) [6,w2,237909,w5,1985195,w0,w1] [] e)) [6,w2,237909,w5,2067250,w0,w1] [] (n (n (s [6,w2,237909,w5,2075511,w0,w1] []) [6,w2,237909,w5,w0,4190271,6551005] [] e) [6,w2,237909,w5,w0,w1,6551005] [] (n (s [6,w2,237909,w5,w0,w1,6553055] []) [6,w2,237909,w5,w0,w1,7077341] [] e)))) [6,w2,237909,w5,w0,w1,7077343] [] (n (n (n (n (s [6,w2,237909,w5,w0,w1,7601629] []) [6,w2,237909,1296795,w3,w0,w1] [] e) [6,w2,237909,1296795,w0,w1,6551005] [] (n (s [6,w2,237909,w3,1985195,w0,w1] []) [6,w2,237909,w3,w0,w1,7190390] [] e)) [6,w2,237909,1985195,w0,w1] [40,97,1242,2065] (n (n (s [6,w2,237909,1985195,w0,w1,6551005] []) [6,w2,237909,w0,w1,6551005,7190390] [] e) [6,w2,237911,w5,w3,w0,w1] [] (n (s [6,w2,239957,w5,w3,w0,w1] []) [6,w2,239957,w5,w0,w1,6551005] [] e))) [6,w2,239957,w5,w0,w1,7601629] [] (n (n (n (s [6,w2,239959,w5,w3,w0,4190271] []) [6,w2,239959,w5,w3,w0,w1] [] e) [6,w2,239959,w5,1985195,w0,w1] [1224] (n (s [6,w2,239959,w5,w0,4190271,6551005] []) [6,w2,239959,w5,w0,w1,6551005] [] e)) [6,w2,239959,w5,w0,w1,7077341] [] (n (n (s [6,w2,239959,w5,w0,w1,7601629] []) [6,w2,239959,1296795,w3,w0,w1] [] e) [6,w2,239959,1296795,w0,w1,6551005] [] (n (s [6,w2,239959,w3,1985195,w0,w1] []) [6,w2,239959,w3,w0,w1,7190390] [2692] e))))) [6,w2,239959,1985195,w0,w1,6551005] [] (n (n (n (n (n (s [6,w2,239959,w0,w1,6551005,7190390] []) [6,w2,258049,w4,1985195,w0,w1] [] (s [6,w2,w4,657408,1985195,w0,w1] [2305])) [6,w2,w4,673929,w3,w0,w1] [] (n (s [6,w2,w4,673929,w0,w1,6551005] []) [6,w2,w4,764247,w5,1838626,6295548] [1158,1290] e)) [6,w2,w4,764247,1985195,w0,4329409] [1154] (n (n (s [6,w2,w4,765271,w5,w3,6295548] [1156,1290]) [6,w2,w4,934571,w5,w0,w1] [] e) [6,w2,w4,1116163,1985195,w0,w1] [900] (n (s [6,w2,w4,1116163,2058991,w0,w1] []) [6,w2,w4,1116163,2092031,w0,w1] [] e))) [6,w2,w4,w5,1796301,1838626,6295548] [1542] (n (n (n (s [6,w2,w4,w5,1796301,3935806,6033378,6295548] []) [6,w2,w4,w5,1797325,w3,6295548] [1540] e) [6,w2,w4,w5,w3,2092031,w0,w1] [] (n (s [6,w2,w4,w5,w3,2093059,2096131] []) [6,w2,w4,w5,w3,2093059,8385535] [] e)) [6,w2,w4,w5,w3,2096131,w0] [] (n (n (s [6,w2,w4,w5,w3,2096131,6295548] []) [6,w2,w4,w5,w3,2098204,4198368] [] e) [6,w2,w4,w5,w3,2098236,4190271] [] (n (s [6,w2,w4,w5,w3,2098236,4196288] []) [6,w2,w4,w5,w3,2098236,w1] [] e)))) [6,w2,w4,w5,w3,2098236,4198337] [] (n (n (n (n (s [6,w2,w4,w5,w3,2098236,4263872] []) [6,w2,w4,w5,w3,w0,2357789] [] e) [6,w2,w4,w5,w3,w0,2617407] [] (n (s [6,w2,w4,w5,w3,w0,3141663] []) [6,w2,w4,w5,w3,w0,3141693] [1538,1672] e)) [6,w2,w4,w5,w3,w0,3141695] [] (n (n (s [6,w2,w4,w5,w3,w0,4190223] []) [6,w2,w4,w5,w3,w0,4190231] [] e) [6,w2,w4,w5,w3,w0,4190237] [1538] (n (s [6,w2,w4,w5,w3,w0,4190239] []) [6,w2,w4,w5,w3,w0,4190269] [1538] e))) [6,w2,w4,w5,w3,w0,4190271] [] (n (n (n (s [6,w2,w4,w5,w3,w0,4192319] []) [6,w2,w4,w5,w3,w0,w1] [] e) [6,w2,w4,w5,w3,w0,w1,6617087] [908,1156,1672] (n (s [6,w2,w4,w5,w3,w0,4198337] []) [6,w2,w4,w5,w3,w0,4198339] [908,1156,1538,1672] e)) [6,w2,w4,w5,w3,w0,4198340] [] (n (n (s [6,w2,w4,w5,w3,w0,4198341] []) [6,w2,w4,w5,w3,w0,4198342] [1538] e) [6,w2,w4,w5,w3,w0,4198348] [] (n (s [6,w2,w4,w5,w3,w0,4198356] []) [6,w2,w4,w5,w3,w0,4198364] [2053] e))))))
def T_26 : BT := (n (n (n (n (n (n (s [6,w2,w4,w5,w3,w0,4263873] [1672]) [6,w2,w4,w5,w3,w0,4263876] [] (s [6,w2,w4,w5,w3,w0,4263877] [1672])) [6,w2,w4,w5,w3,w0,4263880] [] (n (s [6,w2,w4,w5,w3,w0,4263897] [1672,2053]) [6,w2,w4,w5,w3,w0,4394944] [] e)) [6,w2,w4,w5,w3,w0,4394946] [1538] (n (n (s [6,w2,w4,w5,w3,w0,4394956] []) [6,w2,w4,w5,w3,w0,4394960] [2053] e) [6,w2,w4,w5,w3,w0,4425426] [] (n (s [6,w2,w4,w5,w3,w0,4427730,6295549] [910,1158,2052]) [6,w2,w4,w5,w3,w0,4427731,6295549] [910,1158,2052] e))) [6,w2,w4,w5,w3,w0,4853696] [908] (n (n (n (s [6,w2,w4,w5,w3,w0,4853699] [1538]) [6,w2,w4,w5,w3,w0,5967808] [] e) [6,w2,w4,w5,w3,w0,6292476] [] (n (s [6,w2,w4,w5,w3,2100285,4190270] []) [6,w2,w4,w5,w3,2100285,4190271] [] e)) [6,w2,w4,w5,w3,2100285,4192319] [] (n (n (s [6,w2,w4,w5,w3,2100285,4198337] []) [6,w2,w4,w5,w3,2100285,4198338] [908,1156,1539,1672] e) [6,w2,w4,w5,w3,2100285,4198340] [] (n (s [6,w2,w4,w5,w3,2100285,4198341] []) [6,w2,w4,w5,w3,2100285,4198352] [] e)))) [6,w2,w4,w5,w3,2100285,4263872] [1672] (n (n (n (n (s [6,w2,w4,w5,w3,2100285,4427730,6295548] [908,1156]) [6,w2,w4,w5,w3,2100285,4427730,6295549] [908,1156,2053] e) [6,w2,w4,w5,w3,2100348,3592250] [] (n (s [6,w2,w4,w5,w3,2100348,4190271] []) [6,w2,w4,w5,w3,2100348,4192383] [] e)) [6,w2,w4,w5,w3,2100348,4198340] [] (n (n (s [6,w2,w4,w5,w3,2100348,4198344] []) [6,w2,w4,w5,w3,2100348,4198352] [] e) [6,w2,w4,w5,w3,2100348,4263872] [] (n (s [6,w2,w4,w5,w3,2100348,4329408] []) [6,w2,w4,w5,w3,2100348,4796357] [] e))) [6,w2,w4,w5,w3,2100349,4190271] [] (n (n (n (s [6,w2,w4,w5,w3,2100349,4796357] []) [6,w2,w4,w5,w3,2100476,4190271] [] e) [6,w2,w4,w5,w3,2100476,4796357] [] (n (s [6,w2,w4,w5,w3,2100476,5992397] []) [6,w2,w4,w5,w3,2100604,4190271] [] e)) [6,w2,w4,w5,w3,2100604,4427730] [910] (n (n (s [6,w2,w4,w5,w3,2100604,4960215] []) [6,w2,w4,w5,w3,2165820,4124735] [] e) [6,w2,w4,w5,w3,2165820,4190271] [] (n (s [6,w2,w4,w5,w3,2165820,4192319] []) [6,w2,w4,w5,w3,2165820,4263872] [] e))))) [6,w2,w4,w5,w3,2165820,4263876] [] (n (n (n (n (n (s [6,w2,w4,w5,w3,2165820,4329408] []) [6,w2,w4,w5,w3,2165820,5246912] [1157,1672] (s [6,w2,w4,w5,w3,2165821,4190271] [1672])) [6,w2,w4,w5,w3,2165821,4263873] [1672] (n (s [6,w2,w4,w5,w3,2165884,4190271] []) [6,w2,w4,w5,w3,2165884,4796357] [] e)) [6,w2,w4,w5,w3,2296892,4190271] [] (n (n (s [6,w2,w4,w5,w3,2296892,4394944] []) [6,w2,w4,w5,w3,2329918,4190255] [] e) [6,w2,w4,w5,w3,3141695,6288323] [] (n (s [6,w2,w4,w5,w3,4190239,6288323] []) [6,w2,w4,w5,w3,4190269,6288323] [1538] e))) [6,w2,w4,w5,w3,4190271,6288323] [] (n (n (n (s [6,w2,w4,w5,w3,4190271,6290371] []) [6,w2,w4,w5,w3,6292476,6295548] [] e) [6,w2,w4,w5,w3,6292476,8385535] [] (n (s [6,w2,w4,w5,w3,6295548,6549981] [1672]) [6,w2,w4,w5,w3,6295548,8385023] [] e)) [6,w2,w4,w5,w3,6295548,8385535] [] (n (n (s [6,w2,w4,w5,w3,6295548,8387583] []) [6,w2,w4,w5,1837603,2098236,w1] [] e) [6,w2,w4,w5,1837603,w0,4190270] [] (n (s [6,w2,w4,w5,1837603,w0,4190271] []) [6,w2,w4,w5,1837603,w0,4192319] [] e)))) [6,w2,w4,w5,1837603,w0,w1] [] (n (n (n (n (s [6,w2,w4,w5,1837603,w0,4198337] []) [6,w2,w4,w5,1837603,w0,4198338] [910,1158,1538] e) [6,w2,w4,w5,1837603,w0,4198340] [] (n (s [6,w2,w4,w5,1837603,w0,4198352] []) [6,w2,w4,w5,1837603,w0,4198368] [] e)) [6,w2,w4,w5,1837603,w0,4263872] [] (n (n (s [6,w2,w4,w5,1837603,w0,4427730,6295548] [910,1158,2054]) [6,w2,w4,w5,1837603,w0,4722624] [910] e) [6,w2,w4,w5,1837603,w0,4722625] [910] (n (s [6,w2,w4,w5,1837603,2100285,4190271] []) [6,w2,w4,w5,1837603,2100285,4198337] [] e))) [6,w2,w4,w5,1837603,4190271,6288323] [] (n (n (n (s [6,w2,w4,w5,1837606,w0,4190267] []) [6,w2,w4,w5,1837606,w0,4190271] [] e) [6,w2,w4,w5,1837606,w0,4192319] [] (n (s [6,w2,w4,w5,1837606,w0,4196288] []) [6,w2,w4,w5,1837606,w0,w1] [] e)) [6,w2,w4,w5,1837606,w0,4198337] [] (n (n (s [6,w2,w4,w5,1837606,w0,4198338] [1538]) [6,w2,w4,w5,1837606,w0,4198340] [] e) [6,w2,w4,w5,1837606,w0,4198344] [] (n (s [6,w2,w4,w5,1837606,w0,4198352] []) [6,w2,w4,w5,1837606,w0,4198368] [] e))))))
def N_27 : BT := n T_25 [6,w2,w4,w5,w3,w0,4263872] [] T_26
def N_28 : BT := n N_24 [6,w2,231767,w5,w3,w0,w1] [] N_27
def N_29 : BT := n N_21 [6,73797,239959,w0,w1,6551005,7190390] [] N_28
def N_30 : BT := n N_14 [6,2053,w2,1796301,w3,w0,w1] [2049] N_29
def T_31 : BT := (n (n (n (n (n (n (s [6,w2,w4,w5,1837606,w0,4263872] []) [6,w2,w4,w5,1837606,w0,4329408] [] (s [6,w2,w4,w5,1837606,w0,4722624] [])) [6,w2,w4,w5,1837606,w0,4722628] [] (n (s [6,w2,w4,w5,1837606,w0,5246912] []) [6,w2,w4,w5,1837606,2100285,w1] [] e)) [6,w2,w4,w5,1837606,2100286,w1] [1538] (n (n (s [6,w2,w4,w5,1837606,2100348,w1] []) [6,w2,w4,w5,1837606,2100412,w1] [] e) [6,w2,w4,w5,1837606,2100540,w1] [] (n (s [6,w2,w4,w5,1837606,2100796,w1] []) [6,w2,w4,w5,1837606,2165820,w1] [] e))) [6,w2,w4,w5,1837606,2231356,w1] [] (n (n (n (s [6,w2,w4,w5,1837606,2698365,4198340] []) [6,w2,w4,w5,1837606,3148860,w1] [] e) [6,w2,w4,w5,1837606,4190271,6288323] [] (n (s [6,w2,w4,w5,1837606,w1,6288323] []) [6,w2,w4,w5,1837606,4198340,6288323] [] e)) [6,w2,w4,w5,1837607,w0,4190271] [] (n (n (s [6,w2,w4,w5,1837607,w0,w1] []) [6,w2,w4,w5,1837607,w0,4198341] [] e) [6,w2,w4,w5,1837607,2100285,w1] [] (n (s [6,w2,w4,w5,1837607,w1,6288323] []) [6,w2,w4,w5,1837614,w0,4190271] [] e)))) [6,w2,w4,w5,1837614,w0,w1] [] (n (n (n (n (s [6,w2,w4,w5,1837614,w0,4198348] []) [6,w2,w4,w5,1837614,w1,6288323] [] (s [6,w2,w4,w5,1837618,2098220,w1] [])) [6,w2,w4,w5,1837618,w0,4190255] [] (n (s [6,w2,w4,w5,1837618,w0,4190271] []) [6,w2,w4,w5,1837618,w0,4192319] [] e)) [6,w2,w4,w5,1837618,w0,4196288] [] (n (n (s [6,w2,w4,w5,1837618,w0,w1] []) [6,w2,w4,w5,1837618,w0,4198337] [] e) [6,w2,w4,w5,1837618,w0,4198338] [1538] (n (s [6,w2,w4,w5,1837618,w0,4198340] []) [6,w2,w4,w5,1837618,w0,4198352] [] e))) [6,w2,w4,w5,1837618,w0,4198354] [1538] (n (n (n (s [6,w2,w4,w5,1837618,w0,4198368] []) [6,w2,w4,w5,1837618,w0,4198384] [] e) [6,w2,w4,w5,1837618,w0,4263872] [] (n (s [6,w2,w4,w5,1837618,w0,4722624] []) [6,w2,w4,w5,1837618,2100285,w1] [] e)) [6,w2,w4,w5,1837618,2100286,w1] [1539] (n (n (s [6,w2,w4,w5,1837618,2100348,w1] []) [6,w2,w4,w5,1837618,2100540,w1] [] e) [6,w2,w4,w5,1837618,2100796,w1] [] (n (s [6,w2,w4,w5,1837618,2165820,w1] []) [6,w2,w4,w5,1837618,2329918,4190271] [] e))))) [6,w2,w4,w5,1837618,2329918,w1] [] (n (n (n (n (n (s [6,w2,w4,w5,1837618,2329918,4198352] []) [6,w2,w4,w5,1837618,2624572,w1] [] (s [6,w2,w4,w5,1837618,4190271,6288323] [])) [6,w2,w4,w5,1837618,w1,6058689] [] (n (s [6,w2,w4,w5,1837618,w1,6288323] []) [6,w2,w4,w5,1837618,w1,6290387] [] e)) [6,w2,w4,w5,1837618,4198352,6288323] [] (n (n (s [6,w2,w4,w5,1837619,w0,w1] []) [6,w2,w4,w5,1837622,w0,4190271] [] e) [6,w2,w4,w5,1837622,w0,w1] [] (n (s [6,w2,w4,w5,1837622,w0,4198356] []) [6,w2,w4,w5,1837622,2329918,w1] [910] e))) [6,w2,w4,w5,1837622,w1,6288323] [] (n (n (n (s [6,w2,w4,w5,1837630,w0,w1] [2054]) [6,w2,w4,w5,1837670,w0,4190271] [] e) [6,w2,w4,w5,1837670,w0,w1] [] (n (s [6,w2,w4,w5,1837670,w0,4198340] []) [6,w2,w4,w5,1837671,w0,w1] [] e)) [6,w2,w4,w5,1837674,w0,w1] [] (n (n (s [6,w2,w4,w5,1837682,w0,w1] []) [6,w2,w4,w5,1837806,w0,w1] [] e) [6,w2,w4,w5,1837874,w0,4190271] [] (n (s [6,w2,w4,w5,1837874,w0,w1] []) [6,w2,w4,w5,1837874,w0,4198352] [] e)))) [6,w2,w4,w5,1837874,w0,4427730] [] (n (n (n (n (s [6,w2,w4,w5,1837942,w0,w1] []) [6,w2,w4,w5,1837942,w0,w1,6295548] [2055,2187,2694,2826] e) [6,w2,w4,w5,1838626,1838626,6295548] [1674,1794] (n (s [6,w2,w4,w5,1838626,1911399,6295548] [2186]) [6,w2,w4,w5,1838626,1912423,6295548] [2186] e)) [6,w2,w4,w5,1838626,2067250,6295548] [2186,2306] (n (n (s [6,w2,w4,w5,1838626,2068274,6295548] [1602,2186,2306]) [6,w2,w4,w5,1838626,2093059] [6,42,66,918,938,1182,1186,1690,1810,1832] e) [6,w2,w4,w5,1838626,2093059,w0] [] (n (s [6,w2,w4,w5,1838626,2093059,6295548] []) [6,w2,w4,w5,1838626,2097212,4190271] [] e))) [6,w2,w4,w5,1838626,2097212,w1] [] (n (n (n (s [6,w2,w4,w5,1838626,w0,4190271] []) [6,w2,w4,w5,1838626,w0,4193343] [] e) [6,w2,w4,w5,1838626,w0,w1] [] (n (s [6,w2,w4,w5,1838626,w0,4198337] []) [6,w2,w4,w5,1838626,w0,4198338] [1538] e)) [6,w2,w4,w5,1838626,w0,4198340] [] (n (n (s [6,w2,w4,w5,1838626,w0,4198352] []) [6,w2,w4,w5,1838626,w0,4198368] [] e) [6,w2,w4,w5,1838626,w0,4263872] [] (n (s [6,w2,w4,w5,1838626,w0,4722624] []) [6,w2,w4,w5,1838626,w0,6295548] [] e))))))
def T_32 : BT := (n (n (n (n (n (n (s [6,w2,w4,w5,1838626,2698365,6295548] [910,1672]) [6,w2,w4,w5,1838626,3935806,6295548] [1674,1794] (s [6,w2,w4,w5,1838626,4190271,6288323] [])) [6,w2,w4,w5,1838626,4190271,6295548] [] (n (s [6,w2,w4,w5,1838626,6295548] [6,42,66,918,938,1182,1186,1690,1810,1832]) [6,w2,w4,w5,1838626,6295548,6295548] [] e)) [6,w2,w4,w5,1838626,6295548,6524926] [910,1158,3142] (n (n (s [6,w2,w4,w5,1838626,6295548,6549981] [1672,3016]) [6,w2,w4,w5,1838626,6295548,6551005] [1672,3016] e) [6,w2,w4,w5,1838626,6295548,6893565] [910,1672,3016] (n (s [6,w2,w4,w5,1838626,6295548,7190390] [1158,1794,2754,3142]) [6,w2,w4,w5,1838626,6295548,8130558] [1674,1794,2754] e))) [6,w2,w4,w5,1838626,6295548,8156909] [910,1158,2884,3020] (n (n (n (s [6,w2,w4,w5,1838626,6295548,8385535] [2882,3018]) [6,w2,w4,w5,1838627,w0,w1] [] e) [6,w2,w4,w5,1838630,w0,4190271] [] (n (s [6,w2,w4,w5,1838630,w0,w1] []) [6,w2,w4,w5,1838630,w0,4198340] [] e)) [6,w2,w4,w5,1838630,w0,6295548] [] (n (n (s [6,w2,w4,w5,1838630,w1,6288323] []) [6,w2,w4,w5,1838630,w1,6295548] [] e) [6,w2,w4,w5,1838630,4796357,6295548] [910,1673] (n (s [6,w2,w4,w5,1838630,6295548] [6,42,66,105,918,938,1174,1186,1690,1810,1832]) [6,w2,w4,w5,1838638,w0,w1] [] e)))) [6,w2,w4,w5,1838642,w0,4190271] [] (n (n (n (n (s [6,w2,w4,w5,1838642,w0,w1] []) [6,w2,w4,w5,1838642,w0,4198352] [] e) [6,w2,w4,w5,1838642,w0,6295548] [] (n (s [6,w2,w4,w5,1838642,2329918,w1] []) [6,w2,w4,w5,1838642,w1,6288323] [] e)) [6,w2,w4,w5,1838642,w1,6295548] [] (n (n (s [6,w2,w4,w5,1838642,w1,6524926] []) [6,w2,w4,w5,1838642,4427730,6295548] [910,1158] e) [6,w2,w4,w5,1838642,6295548] [6,42,66,97,918,938,1182,1186,1690,1810,1832] (n (s [6,w2,w4,w5,1838646,w0,w1] []) [6,w2,w4,w5,1838699,w0,w1] [] e))) [6,w2,w4,w5,1843815,w0,w1] [] (n (n (n (s [6,w2,w4,w5,1845799,w0,w1] []) [6,w2,w4,w5,1845862,w0,w1] [] e) [6,w2,w4,w5,1845863,w0,4190271] [] (n (s [6,w2,w4,w5,1845863,w0,w1] []) [6,w2,w4,w5,1862383,w0,w1] [] e)) [6,w2,w4,w5,1866275,w0,w1] [] (n (n (s [6,w2,w4,w5,1903138,2098236,w1] []) [6,w2,w4,w5,1903138,w0,4124735] [] e) [6,w2,w4,w5,1903138,w0,4190271] [] (n (s [6,w2,w4,w5,1903138,w0,4192319] []) [6,w2,w4,w5,1903138,w0,w1] [] e))))) [6,w2,w4,w5,1903138,w0,4198337] [] (n (n (n (n (n (s [6,w2,w4,w5,1903138,w0,4198338] [1158,1538]) [6,w2,w4,w5,1903138,w0,4198340] [] (s [6,w2,w4,w5,1903138,w0,4198344] [])) [6,w2,w4,w5,1903138,w0,4198352] [] (n (s [6,w2,w4,w5,1903138,w0,4198368] []) [6,w2,w4,w5,1903138,w0,4263872] [] e)) [6,w2,w4,w5,1903138,w0,4263874] [1158,1538] (n (n (s [6,w2,w4,w5,1903138,w0,4329408] []) [6,w2,w4,w5,1903138,w0,4722624] [] e) [6,w2,w4,w5,1903138,w0,4788160] [] (n (s [6,w2,w4,w5,1903138,w0,5246912] [1158]) [6,w2,w4,w5,1903138,2165820,4190271] [] e))) [6,w2,w4,w5,1903138,2165820,4263872] [] (n (n (n (s [6,w2,w4,w5,1903138,4190271,6288323] []) [6,w2,w4,w5,1903139,w0,4190271] [] e) [6,w2,w4,w5,1903139,w0,w1] [] (n (s [6,w2,w4,w5,1903139,w0,4263873] [1672]) [6,w2,w4,w5,1903142,w0,4190271] [] e)) [6,w2,w4,w5,1903142,w0,w1] [] (n (n (s [6,w2,w4,w5,1903142,w0,4263876] []) [6,w2,w4,w5,1903142,2165820,w1] [] e) [6,w2,w4,w5,1903142,w1,6288323] [] (n (s [6,w2,w4,w5,1903143,w0,w1] []) [6,w2,w4,w5,1903146,w0,w1] [] e)))) [6,w2,w4,w5,1903154,w0,4190271] [] (n (n (n (n (s [6,w2,w4,w5,1903154,w0,w1] []) [6,w2,w4,w5,1903154,w0,4263888] [] e) [6,w2,w4,w5,1903154,2165820,w1] [] (n (s [6,w2,w4,w5,1903154,2329918,w1] []) [6,w2,w4,w5,1903154,w1,6288323] [] e)) [6,w2,w4,w5,1903163,w0,w1] [2054] (n (n (s [6,w2,w4,w5,1903206,w0,w1] []) [6,w2,w4,w5,1903410,w0,w1] [] e) [6,w2,w4,w5,1904162,w0,w1] [] (n (s [6,w2,w4,w5,1904242,w0,w1] []) [6,w2,w4,w5,1909287,w0,w1] [] e))) [6,w2,w4,w5,1909350,w0,w1] [] (n (n (n (s [6,w2,w4,w5,1909351,w0,w1] []) [6,w2,w4,w5,1911331,w0,w1] [] e) [6,w2,w4,w5,1911334,w0,w1] [] (n (s [6,w2,w4,w5,1911335,w0,4190271] []) [6,w2,w4,w5,1911335,w0,4192383] [] e)) [6,w2,w4,w5,1911335,w0,w1] [] (n (n (s [6,w2,w4,w5,1911335,w0,4796357] [910]) [6,w2,w4,w5,1911335,4190271,6288323] [] e) [6,w2,w4,w5,1911335,w1,6288323] [] (n (s [6,w2,w4,w5,1911398,w0,4190271] []) [6,w2,w4,w5,1911398,w0,w1] [] e))))))
def N_33 : BT := n T_31 [6,w2,w4,w5,1838626,2329918,6295548] [910,1158] T_32
def T_34 : BT := (n (n (n (n (n (n (s [6,w2,w4,w5,1911399,2098236,w1] []) [6,w2,w4,w5,1911399,w0,3141694] [1158] (s [6,w2,w4,w5,1911399,w0,3141695] [])) [6,w2,w4,w5,1911399,w0,4059199] [] (n (s [6,w2,w4,w5,1911399,w0,4124733] [1158]) [6,w2,w4,w5,1911399,w0,4124735] [] e)) [6,w2,w4,w5,1911399,w0,4190235] [2184] (n (n (s [6,w2,w4,w5,1911399,w0,4190239] []) [6,w2,w4,w5,1911399,w0,4190255] [] e) [6,w2,w4,w5,1911399,w0,4190263] [] (n (s [6,w2,w4,w5,1911399,w0,4190267] []) [6,w2,w4,w5,1911399,w0,4190269] [906,1538] e))) [6,w2,w4,w5,1911399,w0,4190270] [] (n (n (n (s [6,w2,w4,w5,1911399,w0,4190271] []) [6,w2,w4,w5,1911399,w0,4192319] [] e) [6,w2,w4,w5,1911399,w0,w1] [] (n (s [6,w2,w4,w5,1911399,w0,w1,6295550] [906,1538,2185,2824]) [6,w2,w4,w5,1911399,w0,4198337] [] e)) [6,w2,w4,w5,1911399,w0,4198338] [906,1538] (n (n (s [6,w2,w4,w5,1911399,w0,4198338,6295548] [906,1538,2187]) [6,w2,w4,w5,1911399,w0,4198338,6295550] [906,1538,2187,2824] e) [6,w2,w4,w5,1911399,w0,4198340] [] (n (s [6,w2,w4,w5,1911399,w0,4198341] []) [6,w2,w4,w5,1911399,w0,4198344] [] e)))) [6,w2,w4,w5,1911399,w0,4198345] [] (n (n (n (n (s [6,w2,w4,w5,1911399,w0,4198348] []) [6,w2,w4,w5,1911399,w0,4198352] [] e) [6,w2,w4,w5,1911399,w0,4198354] [906,1538] (n (s [6,w2,w4,w5,1911399,w0,4198356] []) [6,w2,w4,w5,1911399,w0,4198360] [] e)) [6,w2,w4,w5,1911399,w0,4198368] [] (n (n (s [6,w2,w4,w5,1911399,w0,4198370] [910,1542]) [6,w2,w4,w5,1911399,w0,4198372] [2185] e) [6,w2,w4,w5,1911399,w0,4198376] [] (n (s [6,w2,w4,w5,1911399,w0,4198380] [2185,2433]) [6,w2,w4,w5,1911399,w0,4198384] [] e))) [6,w2,w4,w5,1911399,w0,4198388] [2187] (n (n (n (s [6,w2,w4,w5,1911399,w0,4263872] []) [6,w2,w4,w5,1911399,w0,4263873] [1672] e) [6,w2,w4,w5,1911399,w0,4263874] [1158] (n (s [6,w2,w4,w5,1911399,w0,4263876] []) [6,w2,w4,w5,1911399,w0,4263888] [] e)) [6,w2,w4,w5,1911399,w0,4263890] [1158] (n (n (s [6,w2,w4,w5,1911399,w0,4263910] [1158,2185]) [6,w2,w4,w5,1911399,w0,4329408] [] e) [6,w2,w4,w5,1911399,w0,4329409] [] (n (s [6,w2,w4,w5,1911399,w0,4329410] [906,1538]) [6,w2,w4,w5,1911399,w0,4329416] [] e))))) [6,w2,w4,w5,1911399,w0,4329424] [] (n (n (n (n (n (s [6,w2,w4,w5,1911399,w0,4394944] []) [6,w2,w4,w5,1911399,w0,4394946] [] (s [6,w2,w4,w5,1911399,w0,5246912] [])) [6,w2,w4,w5,1911399,w0,5246913] [1158] (n (s [6,w2,w4,w5,1911399,w0,5246914] [910,1542,1674]) [6,w2,w4,w5,1911399,w0,5246920] [] e)) [6,w2,w4,w5,1911399,w0,5246921] [1158] (n (n (s [6,w2,w4,w5,1911399,w0,5246944] []) [6,w2,w4,w5,1911399,w0,5246949] [1158,2187,2441] e) [6,w2,w4,w5,1911399,w0,5312451] [] (n (s [6,w2,w4,w5,1911399,w0,5377984] []) [6,w2,w4,w5,1911399,w0,5377985] [] e))) [6,w2,w4,w5,1911399,2100285,4190271] [] (n (n (n (s [6,w2,w4,w5,1911399,2100285,4198337] []) [6,w2,w4,w5,1911399,2100286,4190271] [906,1538] e) [6,w2,w4,w5,1911399,2100286,4198338] [906,1538] (n (s [6,w2,w4,w5,1911399,2100348,4190271] []) [6,w2,w4,w5,1911399,2100348,4796357] [906] e)) [6,w2,w4,w5,1911399,2100412,4190271] [] (n (n (s [6,w2,w4,w5,1911399,2100412,5394377] []) [6,w2,w4,w5,1911399,2100540,4190271] [] e) [6,w2,w4,w5,1911399,2100540,4427730] [] (n (s [6,w2,w4,w5,1911399,2100796,4190271] []) [6,w2,w4,w5,1911399,2100860,4190271] [] e)))) [6,w2,w4,w5,1911399,2100860,4796357] [910,1672,2824] (n (n (n (n (s [6,w2,w4,w5,1911399,2100860,6033378] [1674]) [6,w2,w4,w5,1911399,2100860,6107111] [] e) [6,w2,w4,w5,1911399,2165820,4190271] [] (n (s [6,w2,w4,w5,1911399,2165820,4263872] []) [6,w2,w4,w5,1911399,2165822,4190271] [1158] e)) [6,w2,w4,w5,1911399,2165822,4263874] [1538] (n (n (s [6,w2,w4,w5,1911399,2231356,4190271] []) [6,w2,w4,w5,1911399,2231356,4329408] [] e) [6,w2,w4,w5,1911399,2624572,4722624] [] (n (s [6,w2,w4,w5,1911399,3148860,4190271] []) [6,w2,w4,w5,1911399,3148860,5246912] [] e))) [6,w2,w4,w5,1911399,3148861,4190271] [1158] (n (n (n (s [6,w2,w4,w5,1911399,3148861,5246913] [1158]) [6,w2,w4,w5,1911399,4190271,6288323] [] e) [6,w2,w4,w5,1911399,6295548,8385535] [] (n (s [6,w2,w4,w5,1911407,w0,4190271] []) [6,w2,w4,w5,1911407,w0,w1] [] e)) [6,w2,w4,w5,1911407,w0,4198344] [] (n (n (s [6,w2,w4,w5,1911407,w1,6288323] []) [6,w2,w4,w5,1911415,w0,4190271] [] e) [6,w2,w4,w5,1911415,w0,w1] [] (n (s [6,w2,w4,w5,1911415,w0,4198352] []) [6,w2,w4,w5,1911415,2329918,w1] [] e))))))
def T_35 : BT := (n (n (n (n (n (n (s [6,w2,w4,w5,1911423,w0,w1] []) [6,w2,w4,w5,1911535,w0,w1] [] (s [6,w2,w4,w5,1911671,w0,w1] [])) [6,w2,w4,w5,1912423,w0,4190271] [] (n (s [6,w2,w4,w5,1912423,w0,w1] []) [6,w2,w4,w5,1912423,w0,6295548] [2184] e)) [6,w2,w4,w5,1912423,6295548] [6,42,66,104,914,1178,2200] (n (n (s [6,w2,w4,w5,1912431,w0,w1] []) [6,w2,w4,w5,1912439,w0,w1] [] e) [6,w2,w4,w5,1927919,w0,w1] [] (n (s [6,w2,w4,w5,2034210,w0,4190271] []) [6,w2,w4,w5,2034210,w0,w1] [] e))) [6,w2,w4,w5,2034210,w0,4394944] [] (n (n (n (s [6,w2,w4,w5,2034222,w0,w1] []) [6,w2,w4,w5,2034226,w0,w1] [2054] e) [6,w2,w4,w5,2042471,w0,4190271] [] (n (s [6,w2,w4,w5,2042471,w0,w1] []) [6,w2,w4,w5,2042471,w0,4329408] [] e)) [6,w2,w4,w5,2042479,w0,w1] [] (n (n (s [6,w2,w4,w5,2042487,w0,w1] []) [6,w2,w4,w5,2058799,w0,4190271] [] e) [6,w2,w4,w5,2058799,w0,w1] [] (n (s [6,w2,w4,w5,2058863,w0,4190271] []) [6,w2,w4,w5,2058863,w0,w1] [] e)))) [6,w2,w4,w5,2058991,w0,4190271] [] (n (n (n (n (s [6,w2,w4,w5,2058991,w0,w1] []) [6,w2,w4,w5,2058991,w0,w1,6592306] [] e) [6,w2,w4,w5,2058991,w0,w1,6594366] [2185,2305] (n (s [6,w2,w4,w5,2058991,w0,4198337] []) [6,w2,w4,w5,2058991,w0,4198338] [1538] e)) [6,w2,w4,w5,2058991,w0,4198340] [] (n (n (s [6,w2,w4,w5,2058991,w0,4198348] []) [6,w2,w4,w5,2058991,w0,4198352] [] e) [6,w2,w4,w5,2058991,w0,4198368] [] (n (s [6,w2,w4,w5,2058991,w0,4198372] [2185]) [6,w2,w4,w5,2058991,w0,4198380] [2185,2305,2433] e))) [6,w2,w4,w5,2058991,w0,4263872] [] (n (n (n (s [6,w2,w4,w5,2058991,w0,4263874] [1154]) [6,w2,w4,w5,2058991,w0,4394944] [] e) [6,w2,w4,w5,2058991,w0,4394946] [] (n (s [6,w2,w4,w5,2058991,w0,4427730,6033378] [1538]) [6,w2,w4,w5,2058991,w0,6033378,6295548] [] e)) [6,w2,w4,w5,2058991,4190271,6288323] [] (n (n (s [6,w2,w4,w5,2059007,w0,w1] []) [6,w2,w4,w5,2060015,w0,w1] [] e) [6,w2,w4,w5,2065200,w0,w1] [] (n (s [6,w2,w4,w5,2067250,w0,4190269] [906,1154,1538]) [6,w2,w4,w5,2067250,w0,4198338] [906,1154,1538] e))))) [6,w2,w4,w5,2067250,w0,4198354] [906,1154,1538] (n (n (n (n (n (s [6,w2,w4,w5,2067250,w0,4198370] [906,1154,1542]) [6,w2,w4,w5,2067250,w0,4263874] [1154,1538] (s [6,w2,w4,w5,2067250,w0,4722626] [1154,1542,1794])) [6,w2,w4,w5,2067250,w0,6033378,6324173] [1674,1794] (n (s [6,w2,w4,w5,2067250,2100286,4190271] [906,1154,1538]) [6,w2,w4,w5,2067250,2100286,4198338] [906,1154,1538] e)) [6,w2,w4,w5,2067250,2100796,6033378] [] (n (n (s [6,w2,w4,w5,2067250,2101052,6033378] []) [6,w2,w4,w5,2075511,w0,4198338] [1538] e) [6,w2,w4,w5,2075511,w0,4263874] [1154] (n (s [6,w2,w4,w5,2092031,w0,3935806,w1] [2051]) [6,w2,w4,w5,2093059,3935806,6033378] [] e))) [6,w2,w4,w5,2098204,4198368,6551005] [] (n (n (n (s [6,w2,w4,w5,2098236,4190271,6551005] []) [6,w2,w4,w5,2098236,w1,6551005] [] e) [6,w2,w4,w5,w0,2357789,w1] [] (n (s [6,w2,w4,w5,w0,3141695,6551005] []) [6,w2,w4,w5,w0,3933726,w1] [] e)) [6,w2,w4,w5,w0,3935806,4190239] [] (n (n (s [6,w2,w4,w5,w0,3935806,4198337,6033378] []) [6,w2,w4,w5,w0,3935806,4198337,6033379] [] e) [6,w2,w4,w5,w0,3935806,4198368] [] (n (s [6,w2,w4,w5,w0,3935806,4198370] []) [6,w2,w4,w5,w0,3935806,4198372] [1673] e)))) [6,w2,w4,w5,w0,3935806,4198384] [] (n (n (n (n (s [6,w2,w4,w5,w0,3935806,4722656] []) [6,w2,w4,w5,w0,4009599,4198368] [] e) [6,w2,w4,w5,w0,4009599,4198372] [] (n (s [6,w2,w4,w5,w0,4059199,6551005] []) [6,w2,w4,w5,w0,4165438,4198370] [906,1154] e)) [6,w2,w4,w5,w0,4190239,6551005] [] (n (n (s [6,w2,w4,w5,w0,4190255,6551005] []) [6,w2,w4,w5,w0,4190263,6551005] [] e) [6,w2,w4,w5,w0,4190269,6551005] [] (n (s [6,w2,w4,w5,w0,4190270,6551005] []) [6,w2,w4,w5,w0,4190271,6329616] [] e))) [6,w2,w4,w5,w0,4190271,6403412] [] (n (n (n (s [6,w2,w4,w5,w0,4190271,6403540] []) [6,w2,w4,w5,w0,4190271,6419933] [] e) [6,w2,w4,w5,w0,4190271,6549981] [] (n (s [6,w2,w4,w5,w0,4190271,6550749] []) [6,w2,w4,w5,w0,4190271,6550877] [] e)) [6,w2,w4,w5,w0,4190271,6550989] [] (n (n (s [6,w2,w4,w5,w0,4190271,6550997] []) [6,w2,w4,w5,w0,4190271,6551004] [] e) [6,w2,w4,w5,w0,4190271,6551005] [] (n (s [6,w2,w4,w5,w0,4190271,6553053] []) [6,w2,w4,w5,w0,4190271,6929749] [906] e))))))
def N_36 : BT := n T_34 [6,w2,w4,w5,1911415,w1,6288323] [] T_35
def N_37 : BT := n N_33 [6,w2,w4,w5,1911399,1912423,6295548] [] N_36
def T_38 : BT := (n (n (n (n (n (n (s [6,w2,w4,w5,w0,4190271,7077341] []) [6,w2,w4,w5,w0,4190271,8125917] [] (s [6,w2,w4,w5,w0,4192319,6551005] [])) [6,w2,w4,w5,w0,w1,6323407] [] (n (s [6,w2,w4,w5,w0,w1,6329616] []) [6,w2,w4,w5,w0,w1,6337876] [] e)) [6,w2,w4,w5,w0,w1,6354397] [] (n (n (s [6,w2,w4,w5,w0,w1,6402388] []) [6,w2,w4,w5,w0,w1,6403156] [] e) [6,w2,w4,w5,w0,w1,6403348] [] (n (s [6,w2,w4,w5,w0,w1,6403412] []) [6,w2,w4,w5,w0,w1,6403413] [] e))) [6,w2,w4,w5,w0,w1,6403420] [] (n (n (n (s [6,w2,w4,w5,w0,w1,6405460] []) [6,w2,w4,w5,w0,w1,6405461] [] e) [6,w2,w4,w5,w0,w1,6405468] [] (n (s [6,w2,w4,w5,w0,w1,6419677] []) [6,w2,w4,w5,w0,w1,6419805] [] e)) [6,w2,w4,w5,w0,w1,6419932] [] (n (n (s [6,w2,w4,w5,w0,w1,6419933] []) [6,w2,w4,w5,w0,w1,6522332] [] e) [6,w2,w4,w5,w0,w1,6534484] [] (n (s [6,w2,w4,w5,w0,w1,6536532] []) [6,w2,w4,w5,w0,w1,6549725] [] e)))) [6,w2,w4,w5,w0,w1,6549853] [] (n (n (n (n (s [6,w2,w4,w5,w0,w1,6549981] []) [6,w2,w4,w5,w0,w1,6550621] [] e) [6,w2,w4,w5,w0,w1,6550733] [] (n (s [6,w2,w4,w5,w0,w1,6550749] []) [6,w2,w4,w5,w0,w1,6550813] [] e)) [6,w2,w4,w5,w0,w1,6550869] [] (n (n (s [6,w2,w4,w5,w0,w1,6550876] []) [6,w2,w4,w5,w0,w1,6550877] [] e) [6,w2,w4,w5,w0,w1,6551004] [] (n (s [6,w2,w4,w5,w0,w1,6551005] []) [6,w2,w4,w5,w0,w1,6553053] [] e))) [6,w2,w4,w5,w0,w1,6927700] [] (n (n (n (s [6,w2,w4,w5,w0,w1,6929748] []) [6,w2,w4,w5,w0,w1,6929749] [906] e) [6,w2,w4,w5,w0,w1,6946269] [906] (n (s [6,w2,w4,w5,w0,w1,7003544] []) [6,w2,w4,w5,w0,w1,7075293] [] e)) [6,w2,w4,w5,w0,w1,7076317] [] (n (n (s [6,w2,w4,w5,w0,w1,7077085] []) [6,w2,w4,w5,w0,w1,7077213] [] e) [6,w2,w4,w5,w0,w1,7077341] [] (n (s [6,w2,w4,w5,w0,w1,8125917] []) [6,w2,w4,w5,w0,w1,8386013] [] e))))) [6,w2,w4,w5,w0,4198337,6403412] [] (n (n (n (n (n (s [6,w2,w4,w5,w0,4198337,6551004] []) [6,w2,w4,w5,w0,4198337,6551005] [] (s [6,w2,w4,w5,w0,4198337,6553053] [])) [6,w2,w4,w5,w0,4198337,7077341] [906] (n (s [6,w2,w4,w5,w0,4198338,6321357] [906,1154]) [6,w2,w4,w5,w0,4198338,6403412] [1154] e)) [6,w2,w4,w5,w0,4198338,6551005] [] (n (n (s [6,w2,w4,w5,w0,4198338,6553055] []) [6,w2,w4,w5,w0,4198338,7077341] [] e) [6,w2,w4,w5,w0,4198340,6403412] [] (n (s [6,w2,w4,w5,w0,4198340,6477208] []) [6,w2,w4,w5,w0,4198340,6551001] [] e))) [6,w2,w4,w5,w0,4198340,6551005] [] (n (n (n (s [6,w2,w4,w5,w0,4198340,6553053] []) [6,w2,w4,w5,w0,4198340,7077341] [] e) [6,w2,w4,w5,w0,4198340,7601629] [] (n (s [6,w2,w4,w5,w0,4198341,6551005] []) [6,w2,w4,w5,w0,4198348,6551005] [] e)) [6,w2,w4,w5,w0,4198352,6403412] [] (n (n (s [6,w2,w4,w5,w0,4198352,6550989] []) [6,w2,w4,w5,w0,4198352,6551005] [] e) [6,w2,w4,w5,w0,4198352,6553053] [] (n (s [6,w2,w4,w5,w0,4198352,7077341] []) [6,w2,w4,w5,w0,4198354,6551005] [] e)))) [6,w2,w4,w5,w0,4198356,6551005] [] (n (n (n (n (s [6,w2,w4,w5,w0,4198368,4452801] []) [6,w2,w4,w5,w0,4198368,6403412] [] e) [6,w2,w4,w5,w0,4198368,6551005] [] (n (s [6,w2,w4,w5,w0,4198368,6553085] []) [6,w2,w4,w5,w0,4198368,7077341] [] e)) [6,w2,w4,w5,w0,4198370,6551005] [] (n (n (s [6,w2,w4,w5,w0,4198372,6477208] [1673]) [6,w2,w4,w5,w0,4198372,6551005] [] e) [6,w2,w4,w5,w0,4198384,6551005] [] (n (s [6,w2,w4,w5,w0,4263872,6403412] []) [6,w2,w4,w5,w0,4263872,6477208] [] e))) [6,w2,w4,w5,w0,4263872,6485469] [] (n (n (n (s [6,w2,w4,w5,w0,4263872,6551005] []) [6,w2,w4,w5,w0,4263872,6553053] [] e) [6,w2,w4,w5,w0,4263872,7077341] [] (n (s [6,w2,w4,w5,w0,4263872,7601629] [1154]) [6,w2,w4,w5,w0,4263873,6551005] [] e)) [6,w2,w4,w5,w0,4263874,6477208] [1154] (n (n (s [6,w2,w4,w5,w0,4263874,6551005] [1154]) [6,w2,w4,w5,w0,4263876,6551005] [] e) [6,w2,w4,w5,w0,4263888,6551005] [] (n (s [6,w2,w4,w5,w0,4394944,6551005] []) [6,w2,w4,w5,w0,4427730,6550749] [] e))))))
def T_39 : BT := (n (n (n (n (n (n (s [6,w2,w4,w5,w0,4722624,6551005] []) [6,w2,w4,w5,w0,4722624,7601629] [] (s [6,w2,w4,w5,w0,4722625,6403412] [906])) [6,w2,w4,w5,w0,4722625,6551005] [906] (n (s [6,w2,w4,w5,w0,4722626,6551005] []) [6,w2,w4,w5,w0,4722628,6551005] [] e)) [6,w2,w4,w5,w0,4722656,6551005] [] (n (n (s [6,w2,w4,w5,w0,4788160,6551005] []) [6,w2,w4,w5,w0,5771200,6551005] [] e) [6,w2,w4,w5,w0,6295548,6549981] [] (n (s [6,w2,w4,w5,2100285,4190271,6551005] []) [6,w2,w4,w5,2100285,4198337,6551005] [] e))) [6,w2,w4,w5,2100286,4190271,6551005] [] (n (n (n (s [6,w2,w4,w5,2100286,4198338,6551005] []) [6,w2,w4,w5,2100348,4190271,6551005] [] e) [6,w2,w4,w5,2100348,4796357,6551005] [] (n (s [6,w2,w4,w5,2100540,4190271,6551005] []) [6,w2,w4,w5,2100540,4427730,6551005] [] e)) [6,w2,w4,w5,2100796,3935806,6033378] [] (n (n (s [6,w2,w4,w5,2100796,4190271,6033378] []) [6,w2,w4,w5,2100796,4190271,6551005] [] e) [6,w2,w4,w5,2100796,4427730,6033378] [906,1154] (n (s [6,w2,w4,w5,2100796,6033378,6295548] []) [6,w2,w4,w5,2100796,6033378,6551005] [] e)))) [6,w2,w4,w5,2100798,4427730,6033378] [906,1154] (n (n (n (n (s [6,w2,w4,w5,2165820,4190271,6551005] []) [6,w2,w4,w5,2165820,4263872,6551005] [] e) [6,w2,w4,w5,2355229,3935806,6033378,6295548] [] (n (s [6,w2,w4,w5,2355229,3935806,6295548] []) [6,w2,w4,w5,2624572,4190271,6551005] [] e)) [6,w2,w4,w5,2624572,4722624,6551005] [] (n (n (s [6,w2,w4,w5,2625084,4796357,6033378] [906]) [6,w2,w4,w5,3935806,6033378,6295548] [] e) [6,w2,w4,w5,3935806,6033378,6295548,6551005] [] (n (s [6,w2,w4,w5,3935806,6033378,6295548,6893565] [3784]) [6,w2,w4,w5,3935806,6033378,6524926] [906,1154] e))) [6,w2,w4,w5,3935806,6033378,6893565] [906] (n (n (n (s [6,w2,w4,w5,3935806,6107111,6295548] []) [6,w2,w4,w5,3935806,6262770,6295548] [] e) [6,w2,w4,w5,4009599,6107111,6295548] [] (n (s [6,w2,w4,w5,4190271,6288323,6403412] []) [6,w2,w4,w5,4190271,6288323,6551005] [] e)) [6,w2,w4,w5,4190271,6288323,7077341] [] (n (n (s [6,w2,w4,w5,6295548,6549981] [2,40,914,936,1178,2344,2392]) [6,w2,w4,w5,6295548,6551005,8385535] [] e) [6,w2,w4,1198219,1837603,w0,w1] [908] (n (s [6,w2,w4,1198219,1837606,w0,w1] []) [6,w2,w4,1198219,1837610,w0,w1] [] e))))) [6,w2,w4,1198219,1837618,w0,w1] [] (n (n (n (n (n (s [6,w2,w4,1198219,1838626,w0,w1] []) [6,w2,w4,1198219,1903138,w0,w1] [] (s [6,w2,w4,1198219,1911399,w0,4190271] [906])) [6,w2,w4,1198219,1911399,w0,w1] [906] (n (s [6,w2,w4,1198219,1911399,w0,w1,6295548] [906,2185,2824]) [6,w2,w4,1198219,1911399,w0,4198338] [906,1538] e)) [6,w2,w4,1198219,1985195,w0,4198338] [1154,1538] (n (n (s [6,w2,w4,1198219,2067250,w0,4198338] [906,1154,1538]) [6,w2,w4,1198219,w0,4190271,6551005] [] e) [6,w2,w4,1198219,w0,w1,6477208] [906] (n (s [6,w2,w4,1198219,w0,w1,6551005] []) [6,w2,w4,1198219,w0,w1,7077341] [] e))) [6,w2,w4,1198219,w0,w1,7601629] [] (n (n (n (s [6,w2,w4,1198219,w0,4198338,6551005] []) [6,w2,w4,1198221,1837606,w0,4190271] [] e) [6,w2,w4,1198221,1837606,w0,w1] [] (n (s [6,w2,w4,1198221,1837606,w0,4198340] []) [6,w2,w4,1198221,1837606,2698365,w1] [] e)) [6,w2,w4,1198221,1837606,w1,6288323] [] (n (n (s [6,w2,w4,1198221,1837607,w0,w1] []) [6,w2,w4,1198221,1837610,w0,w1] [] e) [6,w2,w4,1198221,1837614,w0,w1] [] (n (s [6,w2,w4,1198221,1837618,w0,w1] []) [6,w2,w4,1198221,1837666,w0,w1] [] e)))) [6,w2,w4,1198221,1837730,w0,w1] [] (n (n (n (n (s [6,w2,w4,1198221,1837858,w0,w1] []) [6,w2,w4,1198221,1838626,w0,w1] [] e) [6,w2,w4,1198221,1903138,w0,w1] [] (n (s [6,w2,w4,1198221,1911399,w0,4190271] []) [6,w2,w4,1198221,1911399,w0,w1] [] e)) [6,w2,w4,1198221,1911399,w0,4198340] [] (n (n (s [6,w2,w4,1198221,1911399,2698365,w1] [906]) [6,w2,w4,1198221,1911399,w1,6288323] [] e) [6,w2,w4,1198221,1968674,w0,w1] [] (n (s [6,w2,w4,1198221,1985195,w0,4190271] []) [6,w2,w4,1198221,1985195,w0,w1] [] e))) [6,w2,w4,1198221,1985195,w0,4198340] [] (n (n (n (s [6,w2,w4,1198221,1985195,2698365,w1] []) [6,w2,w4,1198221,1985195,w1,6288323] [] e) [6,w2,w4,1198221,1985199,w0,4190271] [] (n (s [6,w2,w4,1198221,1985199,w0,w1] []) [6,w2,w4,1198221,1985199,w0,4198340] [] e)) [6,w2,w4,1198221,1985199,2698365,w1] [] (n (n (s [6,w2,w4,1198221,1985199,w1,6288323] []) [6,w2,w4,1198221,2058991,w0,w1] [] e) [6,w2,w4,1198221,w0,4190271,6551005] [] (n (s [6,w2,w4,1198221,w0,w1,6403408] []) [6,w2,w4,1198221,w0,w1,6403412] [] e))))))
def N_40 : BT := n T_38 [6,w2,w4,w5,w0,4722624,6403412] [] T_39
def T_41 : BT := (n (n (n (n (n (n (s [6,w2,w4,1198221,w0,w1,6551001] []) [6,w2,w4,1198221,w0,w1,6551005] [] (s [6,w2,w4,1198221,w0,w1,6553053] [])) [6,w2,w4,1198221,w0,w1,7077341] [] (n (s [6,w2,w4,1198221,w0,w1,7601629] []) [6,w2,w4,1198221,w0,4198340,6551005] [] e)) [6,w2,w4,1198221,2698365,w1,6551005] [] (n (n (s [6,w2,w4,1198221,w1,6288323,6551005] []) [6,w2,w4,1198233,1837606,w0,w1] [] e) [6,w2,w4,1198233,1837610,w0,w1] [] (n (s [6,w2,w4,1198233,1837626,w0,w1] []) [6,w2,w4,1198233,1837666,w0,w1] [] e))) [6,w2,w4,1198233,1837730,w0,w1] [] (n (n (n (s [6,w2,w4,1198233,1838626,w0,w1] []) [6,w2,w4,1198233,1903138,w0,w1] [] e) [6,w2,w4,1198233,1911399,w0,4190271] [] (n (s [6,w2,w4,1198233,1911399,w0,w1] []) [6,w2,w4,1198233,1911399,w0,4198352] [] e)) [6,w2,w4,1198233,1911399,w1,6288323] [] (n (n (s [6,w2,w4,1198233,1911415,w0,w1] []) [6,w2,w4,1198233,1968674,w0,w1] [] e) [6,w2,w4,1198233,1968690,w0,w1] [] (n (s [6,w2,w4,1198233,1985195,w0,4190271] []) [6,w2,w4,1198233,1985195,w0,w1] [] e)))) [6,w2,w4,1198233,1985195,w0,4198352] [] (n (n (n (n (s [6,w2,w4,1198233,1985195,2329918,w1] []) [6,w2,w4,1198233,1985195,w1,6288323] [] e) [6,w2,w4,1198233,1985211,w0,4190271] [] (n (s [6,w2,w4,1198233,1985211,w0,w1] []) [6,w2,w4,1198233,1985211,w0,4198352] [] e)) [6,w2,w4,1198233,1985211,w1,6288323] [] (n (n (s [6,w2,w4,1198233,2058991,w0,w1] []) [6,w2,w4,1198233,2059007,w0,w1] [] e) [6,w2,w4,1198233,w0,4190271,6551005] [] (n (s [6,w2,w4,1198233,w0,w1,6403396] []) [6,w2,w4,1198233,w0,w1,6403412] [] e))) [6,w2,w4,1198233,w0,w1,6477208] [] (n (n (n (s [6,w2,w4,1198233,w0,w1,6550989] []) [6,w2,w4,1198233,w0,w1,6551005] [] e) [6,w2,w4,1198233,w0,w1,6553053] [] (n (s [6,w2,w4,1198233,w0,w1,7077341] []) [6,w2,w4,1198233,w0,w1,7601629] [] e)) [6,w2,w4,1198233,w0,4198352,6551005] [] (n (n (s [6,w2,w4,1198233,w1,6288323,6551005] []) [6,w2,w4,1198235,1911399,w0,w1] [906] e) [6,w2,w4,1198235,w0,w1,6551005] [] (n (s [6,w2,w4,1198237,1837622,w0,w1] []) [6,w2,w4,1198237,1911399,w0,w1] [] e))))) [6,w2,w4,1198237,1985195,w0,w1] [] (n (n (n (n (n (s [6,w2,w4,1198237,1985215,w0,w1] []) [6,w2,w4,1198237,w0,w1,6551005] [] (s [6,w2,w4,1198249,1837610,w0,w1] [])) [6,w2,w4,1198249,1837730,w0,w1] [] (n (s [6,w2,w4,1198249,1838626,w0,w1] []) [6,w2,w4,1198249,1903138,w0,w1] [] e)) [6,w2,w4,1198249,1911399,w0,4190271] [] (n (n (s [6,w2,w4,1198249,1911399,w0,w1] []) [6,w2,w4,1198249,1911399,w0,4198368] [] e) [6,w2,w4,1198249,1911399,w1,6288323] [] (n (s [6,w2,w4,1198249,1968674,w0,w1] []) [6,w2,w4,1198249,1985195,w0,4190271] [] e))) [6,w2,w4,1198249,1985195,w0,w1] [] (n (n (n (s [6,w2,w4,1198249,1985195,w0,4198368] []) [6,w2,w4,1198249,1985195,w0,4198376] [2305] e) [6,w2,w4,1198249,1985195,w1,6288323] [] (n (s [6,w2,w4,1198249,2058991,w0,w1] []) [6,w2,w4,1198249,w0,3935806,4190271] [] e)) [6,w2,w4,1198249,w0,3935806,w1] [] (n (n (s [6,w2,w4,1198249,w0,3935806,4198368] []) [6,w2,w4,1198249,w0,4009599,w1] [] e) [6,w2,w4,1198249,w0,4083391,w1] [] (n (s [6,w2,w4,1198249,w0,4190271,6551005] []) [6,w2,w4,1198249,w0,w1,4452801] [] e)))) [6,w2,w4,1198249,w0,w1,6403412] [] (n (n (n (n (s [6,w2,w4,1198249,w0,w1,6477208] []) [6,w2,w4,1198249,w0,w1,6551005] [] e) [6,w2,w4,1198249,w0,w1,6553085] [] (n (s [6,w2,w4,1198249,w0,w1,7077341] []) [6,w2,w4,1198249,w0,w1,7601629] [] e)) [6,w2,w4,1198249,w0,w1,7601661] [] (n (n (s [6,w2,w4,1198249,w0,4198368,6551005] []) [6,w2,w4,1198249,2329918,3935806,w1] [910,1154] e) [6,w2,w4,1198249,3935806,w1,6288323] [] (n (s [6,w2,w4,1198249,3935806,w1,6295548] []) [6,w2,w4,1198249,w1,6288323,6551005] [] e))) [6,w2,w4,1198251,1911399,w0,w1] [910] (n (n (n (s [6,w2,w4,1198251,w0,3935806,w1] []) [6,w2,w4,1198251,w0,w1,6551005] [] e) [6,w2,w4,1198251,2329918,3935806,w1] [910,1154] (n (s [6,w2,w4,1198253,1911399,w0,4190271] [2184]) [6,w2,w4,1198253,1911399,w0,w1] [2184] e)) [6,w2,w4,1198253,1911399,w0,4198372] [2184] (n (n (s [6,w2,w4,1198253,1911399,2698365,w1] [910,1672,2184]) [6,w2,w4,1198253,1911399,w1,6288323] [] e) [6,w2,w4,1198253,1985195,w0,w1] [] (n (s [6,w2,w4,1198253,1985199,w0,w1] []) [6,w2,w4,1198253,2058991,w0,w1] [2184] e))))))
def T_42 : BT := (n (n (n (n (n (n (s [6,w2,w4,1198253,w0,4009599,w1] []) [6,w2,w4,1198253,w0,w1,6477208] [1672] (s [6,w2,w4,1198253,w0,w1,6551005] [])) [6,w2,w4,1198265,1911399,w0,w1] [] (n (s [6,w2,w4,1198265,1985195,w0,w1] []) [6,w2,w4,1198265,1985211,w0,w1] [] e)) [6,w2,w4,1198265,w0,3935806,w1] [] (n (n (s [6,w2,w4,1198265,w0,w1,6551005] []) [6,w2,w4,1198269,1911399,w0,w1] [2184] e) [6,w2,w4,1198285,1837670,w0,w1] [] (n (s [6,w2,w4,1198285,1911399,w0,w1] []) [6,w2,w4,1198285,1985195,w0,w1] [] e))) [6,w2,w4,1198285,1985263,w0,w1] [] (n (n (n (s [6,w2,w4,1198285,w0,w1,6551005] []) [6,w2,w4,1198489,1911399,w0,w1] [] e) [6,w2,w4,1198489,1985195,w0,w1] [] (n (s [6,w2,w4,1198489,1985467,w0,w1] []) [6,w2,w4,1198489,w0,w1,6551005] [] e)) [6,w2,w4,1198761,1911399,w0,w1] [] (n (n (s [6,w2,w4,1198761,1985195,w0,w1] []) [6,w2,w4,1198761,w0,3935806,w1] [] e) [6,w2,w4,1198761,w0,w1,6551005] [] (n (s [6,w2,w4,1198761,w0,w1,8130558] [2754]) [6,w2,w4,1198761,w0,6033378,6295548] [] e)))) [6,w2,w4,1198829,1911399,w0,w1] [2185,2824] (n (n (n (n (s [6,w2,w4,1199241,1838626,w0,4190271] []) [6,w2,w4,1199241,1838626,w0,w1] [] e) [6,w2,w4,1199241,1838626,w0,6295548] [] (n (s [6,w2,w4,1199241,1838626,6295548] [6,40,66,918,936,1174,1186,1688,1810]) [6,w2,w4,1199241,1838634,w0,w1] [] e)) [6,w2,w4,1199241,1903138,w0,w1] [] (n (n (s [6,w2,w4,1199241,1911399,w0,4190271] []) [6,w2,w4,1199241,1911399,w0,w1] [] e) [6,w2,w4,1199241,1911399,w0,6295548] [2184] (n (s [6,w2,w4,1199241,1911399,6295548] [6,40,66,914,1174,1186,2200]) [6,w2,w4,1199241,1912423,w0,w1] [] e))) [6,w2,w4,1199241,1968674,w0,w1] [] (n (n (n (s [6,w2,w4,1199241,1985195,w0,4190271] []) [6,w2,w4,1199241,1985195,w0,w1] [] e) [6,w2,w4,1199241,1985195,w0,6295548] [] (n (s [6,w2,w4,1199241,1985195,6295548] [6,40,66,914,936,1174]) [6,w2,w4,1199241,1986219,w0,4190271] [] e)) [6,w2,w4,1199241,1986219,w0,w1] [] (n (n (s [6,w2,w4,1199241,1986219,w0,6295548] []) [6,w2,w4,1199241,1986219,6295548] [6,40,66,914,936,1170] e) [6,w2,w4,1199241,2058991,w0,w1] [] (n (s [6,w2,w4,1199241,2060015,w0,w1] []) [6,w2,w4,1199241,w0,4190271,6551005] [] e))))) [6,w2,w4,1199241,w0,w1,6402388] [] (n (n (n (n (n (s [6,w2,w4,1199241,w0,w1,6403412] []) [6,w2,w4,1199241,w0,w1,6477208] [] (s [6,w2,w4,1199241,w0,w1,6549981] [])) [6,w2,w4,1199241,w0,w1,6551005] [] (n (s [6,w2,w4,1199241,w0,w1,6553053] []) [6,w2,w4,1199241,w0,w1,7077341] [] e)) [6,w2,w4,1199241,w0,w1,7601629] [] (n (n (s [6,w2,w4,1199241,w0,6295548,6551005] []) [6,w2,w4,1199241,6295548,6551005] [2,40,66,130,914,936,1170,2392] e) [6,w2,w4,1199245,1838630,w0,w1] [] (n (s [6,w2,w4,1199245,1911399,w0,w1] []) [6,w2,w4,1199245,1985195,w0,w1] [] e))) [6,w2,w4,1199245,1986223,w0,w1] [] (n (n (n (s [6,w2,w4,1199245,w0,w1,6551005] []) [6,w2,w4,1199257,1911399,w0,w1] [] e) [6,w2,w4,1199257,1985195,w0,w1] [] (n (s [6,w2,w4,1199257,1986235,w0,w1] []) [6,w2,w4,1199257,w0,w1,6551005] [] e)) [6,w2,w4,1199273,1911399,w0,w1] [] (n (n (s [6,w2,w4,1199273,1985195,w0,w1] []) [6,w2,w4,1199273,1986219,w0,w1] [] e) [6,w2,w4,1199273,w0,3935806,w1] [] (n (s [6,w2,w4,1199273,w0,w1,6551005] []) [6,w2,w4,1199277,1911399,w0,w1] [2184] e)))) [6,w2,w4,1231257,1911399,w0,w1] [] (n (n (n (n (s [6,w2,w4,1231257,w0,w1,6477208] []) [6,w2,w4,1231259,1911399,w0,w1] [906] e) [6,w2,w4,1231259,w0,w1,6551005] [] (n (s [6,w2,w4,1263753,1903138,w0,4190271] []) [6,w2,w4,1263753,1903138,w0,w1] [] e)) [6,w2,w4,1263753,1903138,w0,4263872] [] (n (n (s [6,w2,w4,1263753,1903139,w0,w1] []) [6,w2,w4,1263753,1911399,w0,4190271] [] e) [6,w2,w4,1263753,1911399,w0,w1] [] (n (s [6,w2,w4,1263753,1911399,w0,4263872] []) [6,w2,w4,1263753,1968674,w0,w1] [] e))) [6,w2,w4,1263753,1985195,w0,4190271] [] (n (n (n (s [6,w2,w4,1263753,1985195,w0,w1] []) [6,w2,w4,1263753,1985195,w0,4263872] [] e) [6,w2,w4,1263753,2034210,w0,w1] [] (n (s [6,w2,w4,1263753,2050731,w0,4190271] []) [6,w2,w4,1263753,2050731,w0,w1] [] e)) [6,w2,w4,1263753,2050731,w0,4263872] [] (n (n (s [6,w2,w4,1263753,2058991,w0,w1] []) [6,w2,w4,1263753,w0,4190271,6551005] [] e) [6,w2,w4,1263753,w0,w1,6337876] [] (n (s [6,w2,w4,1263753,w0,w1,6403412] []) [6,w2,w4,1263753,w0,w1,6477208] [] e))))))
def N_43 : BT := n T_41 [6,w2,w4,1198253,w0,3935806,w1] [1672] T_42
def N_44 : BT := n N_40 [6,w2,w4,1198221,w0,w1,6477208] [] N_43
def N_45 : BT := n N_37 [6,w2,w4,w5,w0,4190271,7075293] [] N_44
def T_46 : BT := (n (n (n (n (n (n (s [6,w2,w4,1263753,w0,w1,6551005] []) [6,w2,w4,1263753,w0,w1,6553053] [] (s [6,w2,w4,1263753,w0,w1,7077341] [])) [6,w2,w4,1263753,w0,w1,7601629] [] (n (s [6,w2,w4,1263753,w0,4263872,6551005] []) [6,w2,w4,1263755,1911399,w0,4190271] [] e)) [6,w2,w4,1263755,1911399,w0,w1] [] (n (n (s [6,w2,w4,1263755,1911399,w0,4263874] [1158,1538]) [6,w2,w4,1263755,w0,w1,6477208] [] e) [6,w2,w4,1263755,w0,w1,6551005] [] (n (s [6,w2,w4,1263757,1903142,w0,w1] []) [6,w2,w4,1263757,1911399,w0,w1] [] e))) [6,w2,w4,1263757,1985195,w0,w1] [] (n (n (n (s [6,w2,w4,1263757,2050735,w0,w1] []) [6,w2,w4,1263757,w0,w1,6551005] [] e) [6,w2,w4,1263769,1911399,w0,w1] [] (n (s [6,w2,w4,1263769,1985195,w0,w1] []) [6,w2,w4,1263769,2050747,w0,w1] [] e)) [6,w2,w4,1263769,w0,w1,6551005] [] (n (n (s [6,w2,w4,1263771,1911399,w0,w1] []) [6,w2,w4,1263791,1911399,w0,w1] [2184] e) [6,w2,w4,1272013,1985195,w0,w1] [] (n (s [6,w2,w4,1272013,w0,w1,6403412] []) [6,w2,w4,1296539,1911399,w0,4190271] [] e)))) [6,w2,w4,1296539,1911399,w0,w1] [] (n (n (n (n (s [6,w2,w4,1296539,w0,4190271,6551005] []) [6,w2,w4,1296539,w0,w1,6551005] [] (s [6,w2,w4,1296793,1911399,w0,w1] [])) [6,w2,w4,1296793,1985195,w0,w1] [] (n (s [6,w2,w4,1296793,2067250,w0,w1] []) [6,w2,w4,1296793,2083771,w0,w1] [] e)) [6,w2,w4,1296793,w0,4190271,6551005] [] (n (n (s [6,w2,w4,1296793,w0,w1,6403412] []) [6,w2,w4,1296793,w0,w1,6551005] [] e) [6,w2,w4,1296793,w0,w1,6553055] [] (n (s [6,w2,w4,1296793,w0,w1,7077341] []) [6,w2,w4,1296793,w0,w1,7601629] [] e))) [6,w2,w4,1296795,1854123,w0,w1] [908] (n (n (n (s [6,w2,w4,1296795,1911399,1985195,w0,w1] []) [6,w2,w4,1296795,1911399,w0,4190271] [] e) [6,w2,w4,1296795,1911399,w0,w1] [] (n (s [6,w2,w4,1296795,1911399,w0,4198337] []) [6,w2,w4,1296795,1911399,w0,4198340] [] e)) [6,w2,w4,1296795,1911399,w0,4198344] [] (n (n (s [6,w2,w4,1296795,1911399,w0,4198360] [2055]) [6,w2,w4,1296795,1911399,w0,4263872] [] e) [6,w2,w4,1296795,1911399,w0,4263873] [1672] (n (s [6,w2,w4,1296795,1911399,w0,5246912] []) [6,w2,w4,1296795,1911399,w0,5246913] [1158] e))))) [6,w2,w4,1296795,1911399,w0,5312451] [] (n (n (n (n (n (s [6,w2,w4,1296795,1911399,4190271,6288323] []) [6,w2,w4,1296795,1911407,w0,w1] [] (s [6,w2,w4,1296795,1911415,w0,w1] [])) [6,w2,w4,1296795,1911423,w0,w1] [2054] (n (s [6,w2,w4,1296795,1912423,w0,w1] []) [6,w2,w4,1296795,1968674,w0,4329408] [] e)) [6,w2,w4,1296795,1985195,w0,4198338] [1154] (n (n (s [6,w2,w4,1296795,1985195,w0,4329408] [904]) [6,w2,w4,1296795,2067250,w0,4198338] [1154,1538] e) [6,w2,w4,1296795,2067250,w0,5246914] [904,1672] (n (s [6,w2,w4,1296795,2083771,w0,4198338] []) [6,w2,w4,1296795,w0,3935806,4198368] [1539] e))) [6,w2,w4,1296795,w0,4190271,6477208] [] (n (n (n (s [6,w2,w4,1296795,w0,4190271,6551005] []) [6,w2,w4,1296795,w0,4190271,7077341] [] e) [6,w2,w4,1296795,w0,4190271,7601629] [] (n (s [6,w2,w4,1296795,w0,w1,6477208] []) [6,w2,w4,1296795,w0,w1,6485468] [] e)) [6,w2,w4,1296795,w0,w1,6485469] [] (n (n (s [6,w2,w4,1296795,w0,w1,6549981] []) [6,w2,w4,1296795,w0,w1,6550621] [2050] e) [6,w2,w4,1296795,w0,w1,6550749] [] (n (s [6,w2,w4,1296795,w0,w1,6550877] []) [6,w2,w4,1296795,w0,w1,6550941] [] e)))) [6,w2,w4,1296795,w0,w1,6551004] [] (n (n (n (n (s [6,w2,w4,1296795,w0,w1,6551005] []) [6,w2,w4,1296795,w0,w1,6553053] [] e) [6,w2,w4,1296795,w0,w1,7077341] [] (n (s [6,w2,w4,1296795,w0,w1,7527833] [1154]) [6,w2,w4,1296795,w0,w1,7601629] [] e)) [6,w2,w4,1296795,w0,w1,8125917] [] (n (n (s [6,w2,w4,1296795,w0,4198337,6551005] []) [6,w2,w4,1296795,w0,4198338,6551005] [] e) [6,w2,w4,1296795,w0,4198340,6551005] [] (n (s [6,w2,w4,1296795,w0,4198344,6551005] []) [6,w2,w4,1296795,w0,4198352,6551005] [] e))) [6,w2,w4,1296795,w0,4198360,6551005] [1539] (n (n (n (s [6,w2,w4,1296795,w0,4198368,6551005] []) [6,w2,w4,1296795,w0,4263872,6551005] [] e) [6,w2,w4,1296795,w0,4263873,6551005] [] (n (s [6,w2,w4,1296795,w0,4722624,6551005] []) [6,w2,w4,1296795,w0,5246912,6551005] [] e)) [6,w2,w4,1296795,w0,5246914,6551005] [] (n (n (s [6,w2,w4,1296795,3935806,6033378,6295548] [2498,2690]) [6,w2,w4,1296795,4190271,6288323,6551005] [] e) [6,w2,w4,1296799,w0,w1,6551005] [] (n (s [6,w2,w4,1296827,w0,3935806,w1] [1538]) [6,w2,w4,1296827,w0,w1,6551005] [] e))))))
def T_47 : BT := (n (n (n (n (n (n (s [6,w2,w4,1458858,w0,3296445,w1] [910]) [6,w2,w4,1458858,w0,w1,7190390] [910] (s [6,w2,w4,1460907,1796301,w0,w1] [])) [6,w2,w4,1460907,1796301,w0,w1,6592306] [1542] (n (s [6,w2,w4,1460907,w0,3296445,w1] []) [6,w2,w4,1460907,w0,3411518,w1] [] e)) [6,w2,w4,1460907,w0,3935806,w1] [] (n (n (s [6,w2,w4,1460907,w0,w1,6551005] []) [6,w2,w4,1460907,w0,w1,6592306] [2754] e) [6,w2,w4,1460907,w0,w1,7077341] [] (n (s [6,w2,w4,1460907,w0,w1,7190390] [2754]) [6,w2,w4,1722505,1968674,w0,w1] [908] e))) [6,w2,w4,1722505,1985195,w0,4722624] [] (n (n (n (s [6,w2,w4,1722505,w0,4190271,6551005] []) [6,w2,w4,1722505,w0,w1,6551005] [] e) [6,w2,w4,1722505,w0,w1,7601629] [] (n (s [6,w2,w4,1722505,w0,4722624,6551005] []) [6,w2,w4,1722507,w0,w1,6551005] [] e)) [6,w2,w4,1722509,w0,w1,6551005] [] (n (n (s [6,w2,w4,1722537,w0,3935806,w1] []) [6,w2,w4,1722537,w0,w1,6551005] [] e) [6,w2,w4,1722537,2698365,3935806,w1] [908] (n (s [6,w2,w4,1771520,1985195,w0,w1] []) [6,w2,w4,1788041,w0,w1,6551005] [] e)))) [6,w2,w4,1796301,1985195,w0,4198337] [1288] (n (n (n (n (s [6,w2,w4,1796301,1985195,w0,4722624] []) [6,w2,w4,1796301,2058991,w0,4198337] [] e) [6,w2,w4,1796301,w0,w1,7527833] [1154] (n (s [6,w2,w4,1796301,w0,4198337,6551005] []) [6,w2,w4,1821083,w0,w1,6551005] [] e)) [6,w2,w4,1982507,1985195,w0,5394377] [] (n (n (s [6,w2,w4,1984683,w0,3935806,4190271] []) [6,w2,w4,1984683,w0,3935806,w1] [] e) [6,w2,w4,1984683,w0,4190271,6551005] [] (n (s [6,w2,w4,1984683,w0,w1,6551005] []) [6,w2,w4,1985193,w0,3935806,w1] [] e))) [6,w2,w4,1985193,w0,w1,6551005] [] (n (n (n (s [6,w2,w4,1985195,2093059,w0,5394377] []) [6,w2,w4,1985195,2097212,3296445,4190271] [] e) [6,w2,w4,1985195,2097212,3296445,w1] [] (n (s [6,w2,w4,1985195,2098220,3296445,w1] []) [6,w2,w4,1985195,2098220,3935806,w1] [] e)) [6,w2,w4,1985195,w0,2100285,w1,6033378] [3202] (n (n (s [6,w2,w4,1985195,w0,2100924,5394377] []) [6,w2,w4,1985195,w0,2231357,w1] [2433] e) [6,w2,w4,1985195,w0,2245789,w1] [] (n (s [6,w2,w4,1985195,w0,2247869,w1] []) [6,w2,w4,1985195,w0,2355229,4190271] [] e))))) [6,w2,w4,1985195,w0,2355229,w1] [] (n (n (n (n (n (s [6,w2,w4,1985195,w0,2355229,4427730] [1154]) [6,w2,w4,1985195,w0,2355229,4796357] [] (s [6,w2,w4,1985195,w0,2355229,6033378,6295548] [])) [6,w2,w4,1985195,w0,2355229,6295548] [] (n (s [6,w2,w4,1985195,w0,2355229,6553565] []) [6,w2,w4,1985195,w0,2358333,w1] [] e)) [6,w2,w4,1985195,w0,3293245,4190271] [] (n (n (s [6,w2,w4,1985195,w0,3293245,w1] []) [6,w2,w4,1985195,w0,3295421,4190271] [] e) [6,w2,w4,1985195,w0,3295421,w1] [] (n (s [6,w2,w4,1985195,w0,3296317,4190271] []) [6,w2,w4,1985195,w0,3296317,w1] [] e))) [6,w2,w4,1985195,w0,3296413,w1] [] (n (n (n (s [6,w2,w4,1985195,w0,3296429,w1] []) [6,w2,w4,1985195,w0,3296441,w1] [] e) [6,w2,w4,1985195,w0,3296445,4190271] [] (n (s [6,w2,w4,1985195,w0,3296445,w1] []) [6,w2,w4,1985195,w0,3296445,4198337] [] e)) [6,w2,w4,1985195,w0,3296445,4198338] [1154,3091] (n (n (s [6,w2,w4,1985195,w0,3296445,4198340] [1673]) [6,w2,w4,1985195,w0,3296445,4198341] [1673,2184] e) [6,w2,w4,1985195,w0,3296445,4198344] [] (n (s [6,w2,w4,1985195,w0,3296445,4198352] []) [6,w2,w4,1985195,w0,3296445,4198368] [] e)))) [6,w2,w4,1985195,w0,3296445,4198376] [2433] (n (n (n (n (s [6,w2,w4,1985195,w0,3296445,4263872] []) [6,w2,w4,1985195,w0,3296445,4329408] [] e) [6,w2,w4,1985195,w0,3296445,4329410] [910] (n (s [6,w2,w4,1985195,w0,3296445,4329424] [1543]) [6,w2,w4,1985195,w0,3296445,4722624] [] e)) [6,w2,w4,1985195,w0,3296445,4722625] [910] (n (n (s [6,w2,w4,1985195,w0,3296509,w1] []) [6,w2,w4,1985195,w0,3296701,w1] [] e) [6,w2,w4,1985195,w0,3296957,w1] [] (n (s [6,w2,w4,1985195,w0,3361981,w1] []) [6,w2,w4,1985195,w0,3405981,w1] [] e))) [6,w2,w4,1985195,w0,3592250,5394377] [910,1288] (n (n (n (s [6,w2,w4,1985195,w0,3592250,6033378] [910]) [6,w2,w4,1985195,w0,4190271,4452801] [] e) [6,w2,w4,1985195,w0,4190271,5394377] [] (n (s [6,w2,w4,1985195,w0,4190271,6551005] []) [6,w2,w4,1985195,w0,4190271,6553085] [] e)) [6,w2,w4,1985195,w0,4190271,6553565] [] (n (n (s [6,w2,w4,1985195,w0,4190271,7491581] []) [6,w2,w4,1985195,w0,4190271,7601629] [] e) [6,w2,w4,1985195,w0,4192383,5394377] [] (n (s [6,w2,w4,1985195,w0,4192383,6033378] []) [6,w2,w4,1985195,w0,4193343,5394377] [] e))))))
def N_48 : BT := n T_46 [6,w2,w4,1297819,w0,w1,6551005] [] T_47
def T_49 : BT := (n (n (n (n (n (n (s [6,w2,w4,1985195,w0,w1,6549981] []) [6,w2,w4,1985195,w0,w1,6550749] [] (s [6,w2,w4,1985195,w0,w1,6550877] [])) [6,w2,w4,1985195,w0,w1,6550941] [] (n (s [6,w2,w4,1985195,w0,w1,6551005] []) [6,w2,w4,1985195,w0,w1,6553053] [] e)) [6,w2,w4,1985195,w0,w1,6553085] [] (n (n (s [6,w2,w4,1985195,w0,w1,6553597] []) [6,w2,w4,1985195,w0,w1,7491581] [] e) [6,w2,w4,1985195,w0,w1,7503053] [] (n (s [6,w2,w4,1985195,w0,w1,7527833] []) [6,w2,w4,1985195,w0,w1,7601629] [] e))) [6,w2,w4,1985195,w0,w1,7601661] [] (n (n (n (s [6,w2,w4,1985195,w0,w1,7757481] []) [6,w2,w4,1985195,w0,w1,7862269] [] e) [6,w2,w4,1985195,w0,4198337,5394377] [] (n (s [6,w2,w4,1985195,w0,4198337,6033378] [2466]) [6,w2,w4,1985195,w0,4198337,6033379] [2466] e)) [6,w2,w4,1985195,w0,4198337,6551005] [] (n (n (s [6,w2,w4,1985195,w0,4198337,7190390] [2754]) [6,w2,w4,1985195,w0,4198340,5394377] [] e) [6,w2,w4,1985195,w0,4198340,5394381] [] (n (s [6,w2,w4,1985195,w0,4198340,6033378] []) [6,w2,w4,1985195,w0,4198340,6033382] [] e)))) [6,w2,w4,1985195,w0,4198340,6551005] [] (n (n (n (n (s [6,w2,w4,1985195,w0,4198340,7190390] []) [6,w2,w4,1985195,w0,4198344,5394377] [] e) [6,w2,w4,1985195,w0,4198344,6033378] [] (n (s [6,w2,w4,1985195,w0,4198344,6033386] []) [6,w2,w4,1985195,w0,4198344,6551005] [] e)) [6,w2,w4,1985195,w0,4198344,7190390] [] (n (n (s [6,w2,w4,1985195,w0,4198376,5394377] []) [6,w2,w4,1985195,w0,4198376,5394409] [] e) [6,w2,w4,1985195,w0,4198376,6551005] [] (n (s [6,w2,w4,1985195,w0,4263872,5394377] []) [6,w2,w4,1985195,w0,4263872,5459913] [] e))) [6,w2,w4,1985195,w0,4263872,6551005] [] (n (n (n (s [6,w2,w4,1985195,w0,4329408,5394377] []) [6,w2,w4,1985195,w0,4329408,6033378] [] e) [6,w2,w4,1985195,w0,4329408,6164450] [] (n (s [6,w2,w4,1985195,w0,4329408,6551005] []) [6,w2,w4,1985195,w0,4329408,7190390] [] e)) [6,w2,w4,1985195,w0,4329409] [6,40,97,130,914,1304] (n (n (s [6,w2,w4,1985195,w0,4329410,5394377] [910]) [6,w2,w4,1985195,w0,4329410,6033378] [910] e) [6,w2,w4,1985195,w0,4329410,6551005] [910] (n (s [6,w2,w4,1985195,w0,4329410,7190390] [910]) [6,w2,w4,1985195,w0,4427730,5394377] [] e))))) [6,w2,w4,1985195,w0,4427730,6033378] [1154] (n (n (n (n (n (s [6,w2,w4,1985195,w0,4427730,7491581] [1542]) [6,w2,w4,1985195,w0,4427730,8130558] [1154,1542] (s [6,w2,w4,1985195,w0,4960215,5394377] [])) [6,w2,w4,1985195,w0,5394377,6033378,6295548] [] (n (s [6,w2,w4,1985195,w0,5394377,6295548] []) [6,w2,w4,1985195,w0,5394377,6295548,7190390] [] e)) [6,w2,w4,1985195,w0,5394377,6295548,8130558] [3522] (n (n (s [6,w2,w4,1985195,w0,5394377,6406100] []) [6,w2,w4,1985195,w0,5394377,6524926] [910,3018] e) [6,w2,w4,1985195,w0,5394377,6893565] [910,1288] (n (s [6,w2,w4,1985195,w0,5394377,7192566] []) [6,w2,w4,1985195,w0,5394377,8385919] [] e))) [6,w2,w4,1985195,2100924,5394377] [6,40,97,130,914] (n (n (n (s [6,w2,w4,1985195,2329918,3296445,4190271] []) [6,w2,w4,1985195,2329918,3935806,4190271] [1154] e) [6,w2,w4,1985195,2329918,5394377,6295548] [] (n (s [6,w2,w4,1985195,2329918,6033378,6295548] [1154]) [6,w2,w4,1985195,3296445,4190271,6288323] [] e)) [6,w2,w4,1985195,3296445,4190271,6295548] [] (n (n (s [6,w2,w4,1985195,3296445,5394377,6295548] []) [6,w2,w4,1985195,3296445,6033378,6295548] [3037] e) [6,w2,w4,1985195,3296445,6180843,6295548] [3265] (n (s [6,w2,w4,1985195,4190271,6288323,6551005] []) [6,w2,w4,1985199,w0,3296445,w1] [1672] e)))) [6,w2,w4,1985199,w0,3935806,w1] [] (n (n (n (n (s [6,w2,w4,1985199,w0,w1,5394377] []) [6,w2,w4,1985199,w0,w1,5394381] [] e) [6,w2,w4,1985199,w0,w1,6033378] [] (n (s [6,w2,w4,1985199,w0,w1,6033382] []) [6,w2,w4,1985199,w0,w1,6551001] [] e)) [6,w2,w4,1985199,w0,w1,6551005] [] (n (n (s [6,w2,w4,1985199,w0,w1,7190386] []) [6,w2,w4,1985199,w0,w1,7190390] [] e) [6,w2,w4,1986219,w0,3296445,w1] [] (n (s [6,w2,w4,1986219,w0,w1,6549981] []) [6,w2,w4,1986219,w0,w1,6551005] [] e))) [6,w2,w4,2050731,w0,3296445,w1] [] (n (n (n (s [6,w2,w4,2050731,w0,3361981,w1] []) [6,w2,w4,2050731,w0,w1,6485469] [] e) [6,w2,w4,2050731,w0,w1,6551005] [] (n (s [6,w2,w4,2058991,w0,2994230,w1] []) [6,w2,w4,2058991,w0,3296445,4190271] [] e)) [6,w2,w4,2058991,w0,3296445,w1] [1665] (n (n (s [6,w2,w4,2058991,w0,3296445,w1,6592306] [1665,3841]) [6,w2,w4,2058991,w0,4190271,5394377] [] e) [6,w2,w4,2058991,w0,4190271,7190390] [] (n (s [6,w2,w4,2058991,w0,w1,7190390] []) [6,w2,w4,2058991,w0,w1,7192446] [] e))))))
def T_50 : BT := (n (n (n (n (n (n (s [6,w2,w4,2058991,w0,w1,7527833] []) [6,w2,w4,2058991,w0,w1,8241014] [] (s [6,w2,w4,2058991,w0,4427730,5394377] [])) [6,w2,w4,2058991,w0,4796357,5394377] [] (n (s [6,w2,w4,2058991,w0,5394377,6295548] [2824]) [6,w2,w4,2098236,w1,6551005,7190390] [] e)) [6,w2,w4,w0,2355229,w1,6403412] [] (n (n (s [6,w2,w4,w0,3296413,w1,6403412] []) [6,w2,w4,w0,3296445,4190271,6403412] [] e) [6,w2,w4,w0,3296445,w1,6329616] [1281] (n (s [6,w2,w4,w0,3296445,w1,6403412] []) [6,w2,w4,w0,3296445,w1,6550997] [] e))) [6,w2,w4,w0,3296445,w1,6929749] [] (n (n (n (s [6,w2,w4,w0,3296445,4198344,6551005] []) [6,w2,w4,w0,4190271,5394377,6403412] [] e) [6,w2,w4,w0,4190271,6403412,6551005] [] (n (s [6,w2,w4,w0,4190271,6403412,7601629] []) [6,w2,w4,w0,4190271,6477208,7190390] [] e)) [6,w2,w4,w0,4190271,6551005,7190390] [] (n (n (s [6,w2,w4,w0,4190271,6551005,7323510] []) [6,w2,w4,w0,4190271,6551005,8241014] [] e) [6,w2,w4,w0,w1,6304836,6551005] [] (n (s [6,w2,w4,w0,w1,6304836,8142438] []) [6,w2,w4,w0,w1,6403412,6551005] [] e)))) [6,w2,w4,w0,w1,6403412,6553085] [] (n (n (n (n (s [6,w2,w4,w0,w1,6403412,7491581] []) [6,w2,w4,w0,w1,6403412,7601629] [] e) [6,w2,w4,w0,w1,6403412,7601661] [] (n (s [6,w2,w4,w0,w1,6403413,7190390] []) [6,w2,w4,w0,w1,6403420,7190390] [] e)) [6,w2,w4,w0,w1,6419933,7190390] [] (n (n (s [6,w2,w4,w0,w1,6477208,7091812] []) [6,w2,w4,w0,w1,6477208,7190390] [] e) [6,w2,w4,w0,w1,6477208,7323510] [] (n (s [6,w2,w4,w0,w1,6477208,8241014] []) [6,w2,w4,w0,w1,6477209,7190390] [] e))) [6,w2,w4,w0,w1,6485469,7190390] [] (n (n (n (s [6,w2,w4,w0,w1,6534484,6551005] []) [6,w2,w4,w0,w1,6534484,7190390] [] e) [6,w2,w4,w0,w1,6534484,7323510] [] (n (s [6,w2,w4,w0,w1,6536534,6551005] []) [6,w2,w4,w0,w1,6536534,7601629] [] e)) [6,w2,w4,w0,w1,6549981,7190390] [] (n (n (s [6,w2,w4,w0,w1,6550749,7190390] []) [6,w2,w4,w0,w1,6550877,7190390] [] e) [6,w2,w4,w0,w1,6550941,7190390] [] (n (s [6,w2,w4,w0,w1,6551004,7190390] []) [6,w2,w4,w0,w1,6551005,7190390] [] e))))) [6,w2,w4,w0,w1,6551005,7192438] [] (n (n (n (n (n (s [6,w2,w4,w0,w1,6551005,7321462] []) [6,w2,w4,w0,w1,6551005,7323510] [] (s [6,w2,w4,w0,w1,6551005,8140388] [])) [6,w2,w4,w0,w1,6551005,8142438] [] (n (s [6,w2,w4,w0,w1,6551005,8238966] []) [6,w2,w4,w0,w1,6551005,8241014] [] e)) [6,w2,w4,w0,w1,6551005,8372086] [] (n (n (s [6,w2,w4,w0,w1,7077341,7323510] []) [6,w2,w4,w0,w1,7077341,8238966] [] e) [6,w2,w4,w0,w1,7077341,8241014] [] (n (s [6,w2,w4,w0,w1,7601629,8241014] []) [6,w2,w4,w0,4198337,6551005,7190390] [] e))) [6,w2,w4,w0,4198340,6551005,7190390] [] (n (n (n (s [6,w2,w4,w0,4198344,6551005,7190390] []) [6,w2,w4,w0,4263872,6551005,7190390] [] e) [6,w2,w4,w0,4329408,6551005,7190390] [] (n (s [6,w2,w4,w0,4427730,5394377,6403412] []) [6,w2,w4,w0,4427730,6033378,6403412] [] e)) [6,w2,w4,w0,5246912,6551005,7190390] [] (n (n (s [6,w2,w4,w0,5394377,6295548,6403412] []) [6,w2,w4,w0,5394377,6403412,6406100] [] e) [6,w2,w4,3296445,5394377,6295548,6551005] [] (n (s [6,w2,w4,4190271,6288323,6551005,7190390] []) [6,w2,600135,1198219,w3,w0,4190271] [1538] e)))) [6,w2,600135,1198219,w3,w0,w1] [1538] (n (n (n (n (s [6,w2,600135,1198219,w3,w0,4198338] [1538]) [6,w2,600135,1198219,1911399,w0,w1] [906,1538] e) [6,w2,600135,1198219,2067250,w0,w1] [1538] (n (s [6,w2,600135,1198219,w0,w1,6551005] []) [6,w2,600135,1198221,w3,w0,w1] [] e)) [6,w2,600135,1198233,w3,w0,w1] [] (n (n (s [6,w2,600135,1199241,w3,w0,w1] []) [6,w2,600135,1263753,w3,w0,w1] [] e) [6,w2,600135,1263755,w3,w0,w1] [] (n (s [6,w2,600135,1296795,w3,w0,4190271] []) [6,w2,600135,1296795,w3,w0,w1] [] e))) [6,w2,600135,1296795,w3,w0,4198338] [1538] (n (n (n (s [6,w2,600135,1296795,1985195,w0,w1] [1154]) [6,w2,600135,1296795,w0,w1,6551005] [] e) [6,w2,600135,w3,2083771,w0,w1] [] (n (s [6,w2,600135,w3,w0,3296445,w1,5394377] []) [6,w2,600135,w3,w0,4190271,7190390] [] e)) [6,w2,600135,w3,w0,w1,6403412] [] (n (n (s [6,w2,600135,w3,w0,w1,7190388] [1154]) [6,w2,600135,w3,w0,w1,7190390] [] e) [6,w2,600135,w3,w0,w1,7192438] [] (n (s [6,w2,600135,w3,w0,w1,7323510] []) [6,w2,600135,w3,w0,4198338,7190390] [1154] e))))))
def N_51 : BT := n T_49 [6,w2,w4,2058991,w0,w1,7491581] [1665] T_50
def N_52 : BT := n N_48 [6,w2,w4,1985195,w0,w1,6485469] [] N_51
def T_53 : BT := (n (n (n (n (n (n (s [6,w2,600135,1985195,w0,3296445,w1] [3089]) [6,w2,600135,1985195,w0,3935806,w1] [] (s [6,w2,600135,1985195,w0,w1,6551005] [])) [6,w2,600135,1985195,w0,w1,7190390] [] (n (s [6,w2,600135,w0,w1,6551005,7190390] []) [6,w2,600141,1198221,w3,w0,w1] [] e)) [6,w2,600141,1198233,w3,w0,w1] [] (n (n (s [6,w2,600141,1198281,w3,w0,w1] []) [6,w2,600141,1198473,w3,w0,w1] [] e) [6,w2,600141,1199241,w3,w0,w1] [] (n (s [6,w2,600141,1263753,w3,w0,w1] []) [6,w2,600141,1296795,w3,w0,4190271] [] e))) [6,w2,600141,1296795,w3,w0,w1] [] (n (n (n (s [6,w2,600141,1296795,w3,w0,4198344] []) [6,w2,600141,1296795,w3,w1,6288323] [] e) [6,w2,600141,1296795,1837610,w0,w1] [] (n (s [6,w2,600141,1296795,1911399,w0,w1] []) [6,w2,600141,1296795,1911407,w0,w1] [] e)) [6,w2,600141,1296795,w0,w1,6551005] [] (n (n (s [6,w2,600141,1796301,w3,3296445,w1] []) [6,w2,600141,w3,2083771,w0,w1] [] e) [6,w2,600141,w3,2098228,w1,7190390] [] (n (s [6,w2,600141,w3,w0,3296445,4190271] []) [6,w2,600141,w3,w0,3296445,w1] [] e)))) [6,w2,600141,w3,w0,3296445,4198344] [] (n (n (n (n (s [6,w2,600141,w3,w0,3395007,w1] []) [6,w2,600141,w3,w0,4190271,7190390] [] e) [6,w2,600141,w3,w0,w1,5092162] [] (n (s [6,w2,600141,w3,w0,w1,6403412] []) [6,w2,600141,w3,w0,w1,7190390] [] e)) [6,w2,600141,w3,w0,w1,7192446] [] (n (n (s [6,w2,600141,w3,w0,w1,7323510] []) [6,w2,600141,w3,w0,4198344,7190390] [] e) [6,w2,600141,w3,2698365,3296445,w1] [900] (n (s [6,w2,600141,w3,3296445,w1,5394377] []) [6,w2,600141,w3,3296445,w1,6288323] [] e))) [6,w2,600141,w3,3296445,w1,6295548] [] (n (n (n (s [6,w2,600141,w3,3296445,w1,7190390] []) [6,w2,600141,w3,w1,6288323,7190390] [] e) [6,w2,600141,1837610,1985195,w0,w1] [] (n (s [6,w2,600141,1837610,w0,3296445,w1] []) [6,w2,600141,1837610,w0,w1,7190390] [] e)) [6,w2,600141,1911399,w0,3296445,w1] [] (n (n (s [6,w2,600141,1911399,w0,w1,7190390] []) [6,w2,600141,1911407,w0,3296445,w1] [] e) [6,w2,600141,1911407,w0,w1,7190390] [] (n (s [6,w2,600141,1985195,w0,3296445,w1] []) [6,w2,600141,1985195,w0,3935806,w1] [] e))))) [6,w2,600141,1985195,w0,w1,5394377] [] (n (n (n (n (n (s [6,w2,600141,1985195,w0,w1,6033378] []) [6,w2,600141,1985195,w0,w1,6551005] [] (s [6,w2,600141,1985195,w0,w1,7190390] [])) [6,w2,600141,w0,3296445,w1,6551005] [] (n (s [6,w2,600141,w0,w1,6551005,7190390] []) [6,w2,600149,1198233,w3,w0,4190271] [] e)) [6,w2,600149,1198233,w3,w0,w1] [] (n (n (s [6,w2,600149,1198233,w3,w0,4198352] []) [6,w2,600149,1198233,w3,2329918,w1] [] e) [6,w2,600149,1198233,w3,w1,6288323] [] (n (s [6,w2,600149,1198233,1837618,w0,w1] []) [6,w2,600149,1198233,1911399,w0,w1] [] e))) [6,w2,600149,1198233,1911415,w0,w1] [] (n (n (n (s [6,w2,600149,1198233,w0,w1,6551005] []) [6,w2,600149,1198237,w3,w0,w1] [] e) [6,w2,600149,1198249,w3,w0,w1] [] (n (s [6,w2,600149,1198473,w3,w0,w1] []) [6,w2,600149,1198729,w3,w0,w1] [] e)) [6,w2,600149,1199241,w3,w0,w1] [] (n (n (s [6,w2,600149,1263753,w3,w0,w1] []) [6,w2,600149,1263769,w3,w0,w1] [] e) [6,w2,600149,1296795,w3,w0,4190271] [] (n (s [6,w2,600149,1296795,w3,w0,w1] []) [6,w2,600149,1296795,w3,w0,4198352] [] e)))) [6,w2,600149,1296795,w3,w1,6288323] [] (n (n (n (n (s [6,w2,600149,1296795,1837618,w0,w1] []) [6,w2,600149,1296795,1911399,w0,w1] [] e) [6,w2,600149,1296795,1911415,w0,w1] [] (n (s [6,w2,600149,1296795,w0,w1,6551005] []) [6,w2,600149,1722505,w3,w0,w1] [] e)) [6,w2,600149,w3,1985195,w0,4190271] [] (n (n (s [6,w2,600149,w3,1985195,w0,w1] []) [6,w2,600149,w3,1985195,w0,4198352] [] e) [6,w2,600149,w3,1985195,w1,6288323] [] (n (s [6,w2,600149,w3,1985211,w0,w1] []) [6,w2,600149,w3,2083771,w0,w1] [] e))) [6,w2,600149,w3,w0,4190271,7190390] [] (n (n (n (s [6,w2,600149,w3,w0,w1,6403412] []) [6,w2,600149,w3,w0,w1,7091812] [] e) [6,w2,600149,w3,w0,w1,7190374] [] (n (s [6,w2,600149,w3,w0,w1,7190390] []) [6,w2,600149,w3,w0,w1,7192438] [] e)) [6,w2,600149,w3,w0,w1,7323510] [] (n (n (s [6,w2,600149,w3,w0,w1,8241014] []) [6,w2,600149,w3,w0,4198352,7190390] [] e) [6,w2,600149,w3,w1,6288323,7190390] [] (n (s [6,w2,600149,1837618,1985195,w0,w1] []) [6,w2,600149,1837618,1985211,w0,w1] [] e))))))
def T_54 : BT := (n (n (n (n (n (n (s [6,w2,600149,1911399,w0,w1,7190390] []) [6,w2,600149,1911415,w0,w1,7190390] [] (s [6,w2,600149,1985195,w0,3296445,w1] [])) [6,w2,600149,1985195,w0,3935806,w1] [1538] (n (s [6,w2,600149,1985195,w0,w1,5394377] []) [6,w2,600149,1985195,w0,w1,6033378] [] e)) [6,w2,600149,1985195,w0,w1,6551005] [] (n (n (s [6,w2,600149,1985195,w0,w1,7190390] []) [6,w2,600149,w0,w1,6551005,7190390] [] e) [6,w2,600151,1198235,w3,w0,w1] [1538] (n (s [6,w2,600151,1296795,w3,w0,w1] []) [6,w2,600151,w3,1985195,w0,w1] [] e))) [6,w2,600151,w3,w0,w1,7190390] [] (n (n (n (s [6,w2,600151,1985195,w0,3935806,w1] [1538]) [6,w2,600157,1296795,w3,w0,4190271] [] e) [6,w2,600157,1296795,w3,w0,w1] [] (n (s [6,w2,600157,1296795,w3,w0,4198360] [2052]) [6,w2,600157,1296795,w3,3296445,w1] [1156] e)) [6,w2,600157,1296795,w3,w1,6288323] [] (n (n (s [6,w2,600157,1296795,1837626,w0,w1] [2050]) [6,w2,600157,1296795,1911399,w0,w1] [2050] e) [6,w2,600157,1296795,1911423,w0,w1] [] (n (s [6,w2,600157,1296795,w0,w1,6551005] []) [6,w2,600157,w3,1985195,w0,w1] [] e)))) [6,w2,600157,w3,2083771,w0,w1] [] (n (n (n (n (s [6,w2,600157,w3,w0,3296445,w1] [1540]) [6,w2,600157,w3,w0,3395007,w1] [] e) [6,w2,600157,w3,w0,w1,7091812] [] (n (s [6,w2,600157,w3,w0,w1,7190390] []) [6,w2,600165,1198249,1911399,w0,w1] [] e)) [6,w2,600165,1198249,w0,3935806,w1] [] (n (n (s [6,w2,600165,1198249,w0,w1,6551005] []) [6,w2,600165,1198253,1911399,w0,w1] [2184] e) [6,w2,600165,1296795,1911399,w0,w1] [] (n (s [6,w2,600165,1296795,w0,3935806,w1] [1542]) [6,w2,600165,1296795,w0,w1,6551005] [] e))) [6,w2,600165,1911399,w0,w1,7190390] [] (n (n (n (s [6,w2,600165,1985195,w0,3296445,w1] []) [6,w2,600165,1985195,w0,3935806,w1] [] e) [6,w2,600165,1985195,w0,w1,5394377] [] (n (s [6,w2,600165,1985195,w0,w1,6033378] []) [6,w2,600165,1985195,w0,w1,6551005] [] e)) [6,w2,600165,1985195,w0,w1,7190390] [] (n (n (s [6,w2,600165,w0,3935806,w1,7190390] []) [6,w2,600165,w0,w1,6551005,7190390] [] e) [6,w2,600173,1837610,1985195,w0,w1] [] (n (s [6,w2,600173,1985195,w0,3296445,w1] []) [6,w2,600173,1985195,w0,3935806,w1] [] e))))) [6,w2,600173,1985195,w0,w1,5394377] [] (n (n (n (n (n (s [6,w2,600173,1985195,w0,w1,6033378] []) [6,w2,600173,1985195,w0,w1,6551005] [] (s [6,w2,600173,1985195,w0,w1,7190390] [])) [6,w2,600173,1985195,3296445,w1] [6,41,918] (n (s [6,w2,600181,1198265,w3,w0,w1] []) [6,w2,600181,1296795,w3,w0,w1] [] e)) [6,w2,600181,w3,2083771,w0,w1] [] (n (n (s [6,w2,600181,w3,w0,w1,7190390] []) [6,w2,600189,1296795,w3,w0,w1] [] e) [6,w2,600189,w3,2083771,w0,w1] [] (n (s [6,w2,600269,1296795,w3,w0,w1] []) [6,w2,600269,w3,w0,3296445,w1] [] e))) [6,w2,600269,w3,w0,w1,7190390] [] (n (n (n (s [6,w2,600269,w3,w0,w1,7491581] []) [6,w2,600269,w3,w0,5394377,6295548] [] e) [6,w2,600405,1198489,w3,w0,w1] [] (n (s [6,w2,600405,1296795,w3,w0,w1] []) [6,w2,600405,w3,1985195,w0,w1] [] e)) [6,w2,600405,w3,w0,w1,7190390] [] (n (n (s [6,w2,600541,1296795,w3,w0,w1] []) [6,w2,601157,1199241,w3,w0,4190271] [] e) [6,w2,601157,1199241,w3,w0,w1] [] (n (s [6,w2,601157,1199241,w3,w0,6295548] []) [6,w2,601157,1199241,w3,6295548] [4,40,916,936,1180,1692,1812,1832] e)))) [6,w2,601157,1199241,1838626,w0,w1] [] (n (n (n (n (s [6,w2,601157,1199241,1911399,w0,w1] []) [6,w2,601157,1199241,1912423,w0,w1] [] e) [6,w2,601157,1199241,w0,w1,6551005] [] (n (s [6,w2,601157,1199245,w3,w0,w1] []) [6,w2,601157,1263753,w3,w0,w1] [] e)) [6,w2,601157,1296795,w3,w0,4190271] [] (n (n (s [6,w2,601157,1296795,w3,w0,w1] []) [6,w2,601157,1296795,w3,w0,6295548] [2052] e) [6,w2,601157,1296795,w3,6295548] [4,40,68,936,1688,2068] (n (s [6,w2,601157,1296795,1838626,w0,w1] []) [6,w2,601157,1296795,1911399,w0,w1] [] e))) [6,w2,601157,1296795,1912423,w0,w1] [] (n (n (n (s [6,w2,601157,1296795,w0,w1,6551005] []) [6,w2,601157,1297819,w3,w0,w1] [] e) [6,w2,601157,w3,2083771,w0,w1] [] (n (s [6,w2,601157,w3,w0,4190271,7190390] []) [6,w2,601157,w3,w0,w1,6403412] [] e)) [6,w2,601157,w3,w0,w1,7189366] [] (n (n (s [6,w2,601157,w3,w0,w1,7190390] []) [6,w2,601157,w3,w0,w1,7192438] [] e) [6,w2,601157,w3,w0,w1,7323510] [] (n (s [6,w2,601157,w3,w0,6295548,7190390] []) [6,w2,601157,w3,6295548,7190390] [4,40,138,916,1300,2130,2340,2390] e))))))
def N_55 : BT := n T_53 [6,w2,600149,1837618,w0,w1,7190390] [] T_54
def T_56 : BT := (n (n (n (n (n (n (s [6,w2,601157,1838626,1986219,w0,w1] []) [6,w2,601157,1838626,w0,w1,7190390] [] (s [6,w2,601157,1911399,w0,w1,7190390] [])) [6,w2,601157,1912423,w0,w1,7190390] [] (n (s [6,w2,601157,1985195,w0,3296445,w1] []) [6,w2,601157,1985195,w0,3935806,w1] [] e)) [6,w2,601157,1985195,w0,w1,6551005] [] (n (n (s [6,w2,601157,1985195,w0,w1,7190390] []) [6,w2,601157,w0,w1,6551005,7190390] [] e) [6,w2,601165,1296795,w3,w0,w1] [] (n (s [6,w2,601165,w3,w0,3296445,w1] []) [6,w2,601165,w3,w0,w1,7190390] [] e))) [6,w2,601165,w3,3296445,w1,5394377] [] (n (n (n (s [6,w2,601165,1985195,w0,w1,5394377] []) [6,w2,601173,1199257,w3,w0,w1] [] e) [6,w2,601173,1296795,w3,w0,w1] [] (n (s [6,w2,601173,w3,1985195,w0,w1] []) [6,w2,601173,w3,w0,w1,7190390] [] e)) [6,w2,601181,1296795,w3,w0,w1] [] (n (n (s [6,w2,601189,1985195,w0,w1,6033378] []) [6,w2,631126,764247,1985195,w0,w1] [] e) [6,w2,633173,w3,1985195,w0,w1] [] (n (s [6,w2,633173,w3,w0,w1,6403412] [2692]) [6,w2,633175,1296795,w3,w0,w1] [] e)))) [6,w2,633175,w3,1985195,w0,w1] [] (n (n (n (n (s [6,w2,633175,w3,w0,4190271,7190390] []) [6,w2,633175,w3,w0,w1,7190390] [] e) [6,w2,633175,w3,w0,w1,7323510] [] (n (s [6,w2,633175,w3,w0,w1,8241014] []) [6,w2,633175,1985195,w0,w1,7190390] [] e)) [6,w2,633175,w0,w1,6551005,7190390] [] (n (n (s [6,w2,657411,1796301,w3,w0,w1] [2177]) [6,w2,657411,1829343,w3,w0,w1] [] e) [6,w2,657411,w3,2092031,w0,w1] [] (n (s [6,w2,731205,1263753,w3,w0,w1] []) [6,w2,731205,1296795,w3,w0,4190271] [] e))) [6,w2,731205,1296795,w3,w0,w1] [] (n (n (n (s [6,w2,731205,1296795,w3,w0,4329408] []) [6,w2,731205,1296795,1911399,w0,w1] [] e) [6,w2,731205,1296795,1968674,w0,w1] [] (n (s [6,w2,731205,1296795,1985195,w0,w1] []) [6,w2,731205,1296795,2042471,w0,w1] [] e)) [6,w2,731205,1296795,w0,w1,6551005] [] (n (n (s [6,w2,731205,1722505,w3,w0,w1] []) [6,w2,731205,w3,1985195,w0,4190271] [] e) [6,w2,731205,w3,1985195,w0,w1] [] (n (s [6,w2,731205,w3,1985195,w0,4329408] []) [6,w2,731205,w3,2083771,w0,w1] [] e))))) [6,w2,731205,w3,w0,4190271,7190390] [] (n (n (n (n (n (s [6,w2,731205,w3,w0,w1,6403412] []) [6,w2,731205,w3,w0,w1,7091812] [] (s [6,w2,731205,w3,w0,w1,7190390] [])) [6,w2,731205,w3,w0,w1,7323510] [] (n (s [6,w2,731205,w3,w0,w1,8241014] []) [6,w2,731205,w3,w0,4329408,7190390] [] e)) [6,w2,731205,1911399,w0,w1,7190390] [] (n (n (s [6,w2,731205,1968674,1985195,w0,w1] []) [6,w2,731205,1968674,w0,w1,7190390] [] e) [6,w2,731205,1985195,2067250,w0,w1] [] (n (s [6,w2,731205,1985195,w0,3296445,w1] []) [6,w2,731205,1985195,w0,3935806,w1] [] e))) [6,w2,731205,1985195,w0,w1,6551005] [] (n (n (n (s [6,w2,731205,1985195,w0,w1,7190390] []) [6,w2,731205,2042471,w0,w1,7190390] [] e) [6,w2,731205,w0,w1,6551005,7190390] [] (n (s [6,w2,731207,1296795,w3,w0,w1] []) [6,w2,731207,w3,1985195,w0,4190271] [] e)) [6,w2,731207,w3,1985195,w0,w1] [] (n (n (s [6,w2,731207,w3,1985195,w0,4329410] [908]) [6,w2,731207,w3,2083771,w0,w1] [] e) [6,w2,731207,w3,w0,w1,6403412] [] (n (s [6,w2,731207,w3,w0,w1,7190390] []) [6,w2,731207,1985195,w0,3296445,w1] [] e)))) [6,w2,731207,1985195,w0,3935806,w1] [] (n (n (n (n (s [6,w2,731207,1985195,w0,w1,6551005] []) [6,w2,731207,1985195,w0,w1,7190390] [] e) [6,w2,731213,1296795,w3,w0,w1] [] (n (s [6,w2,731213,w3,1985195,w0,w1] []) [6,w2,731213,w3,w0,3296445,w1] [] e)) [6,w2,731213,w3,w0,3395007,w1] [] (n (n (s [6,w2,731213,w3,w0,w1,7190390] []) [6,w2,731213,w3,2329918,3296445,w1] [] e) [6,w2,731221,1296795,w3,w0,w1] [] (n (s [6,w2,731221,w3,1985195,w0,w1] []) [6,w2,731221,w3,w0,w1,7190390] [] e))) [6,w2,731221,1985195,w0,3296445,w1] [] (n (n (n (s [6,w2,731223,w3,1985195,w0,w1] []) [6,w2,731247,w3,1985195,w0,w1] [] e) [6,w2,755987,1796301,w3,w0,w1] [] (n (s [6,w2,755987,w3,2058991,w0,w1] []) [6,w2,763991,1296539,w3,w0,4190271] [] e)) [6,w2,763991,1296539,w3,w0,w1] [] (n (n (s [6,w2,763991,1296795,w3,w0,4190271] []) [6,w2,763991,1296795,w3,w0,w1] [2692] e) [6,w2,763991,w3,1985195,w0,4190271] [] (n (s [6,w2,763991,w3,1985195,w0,w1] []) [6,w2,763991,w3,w0,4190271,7190390] [] e))))))
def T_57 : BT := (n (n (n (n (n (n (s [6,w2,764245,1296793,w3,w0,w1] []) [6,w2,764245,1296793,w0,w1,6551005] [] (s [6,w2,764245,1296795,w3,w0,w1] [])) [6,w2,764245,1296795,w0,w1,6551005] [] (n (s [6,w2,764245,w3,1985195,w0,w1] []) [6,w2,764245,w3,w0,w1,7190390] [] e)) [6,w2,764245,1985195,w0,w1,6551005] [] (n (n (s [6,w2,764245,w0,w1,6551005,7190390] []) [6,w2,764247,1296795,w3,w0,4190271] [] e) [6,w2,764247,1296795,w3,w0,w1] [] (n (s [6,w2,764247,1296795,w3,w0,4198337] [900,1156]) [6,w2,764247,1296795,w3,w0,4198338] [] e))) [6,w2,764247,1296795,w3,w0,4198340] [] (n (n (n (s [6,w2,764247,1296795,w3,w0,4198352] [2053]) [6,w2,764247,1296795,w3,w0,4198356] [2053] e) [6,w2,764247,1296795,w3,w0,4198368] [] (n (s [6,w2,764247,1296795,w3,w0,4722624] []) [6,w2,764247,1296795,w3,w0,4722626] [] e)) [6,w2,764247,1296795,w3,4190271,6288323] [] (n (n (s [6,w2,764247,1296795,1837603,w0,w1] [900,1156]) [6,w2,764247,1296795,1837606,w0,w1] [] e) [6,w2,764247,1296795,1837618,w0,w1] [2052] (n (s [6,w2,764247,1296795,1837622,w0,w1] [2052]) [6,w2,764247,1296795,1838626,w0,w1] [] e)))) [6,w2,764247,1296795,1911399,1985195,w0,w1] [] (n (n (n (n (s [6,w2,764247,1296795,w0,4190271,6551005] []) [6,w2,764247,1296795,w0,w1,6551005] [] e) [6,w2,764247,1296795,w0,w1,7077341] [] (n (s [6,w2,764247,1296799,w3,w0,w1] []) [6,w2,764247,1296827,w3,w0,w1] [] e)) [6,w2,764247,1297819,w3,w0,w1] [] (n (n (s [6,w2,764247,1722505,w0,w1,6551005] []) [6,w2,764247,1722507,w0,w1,6551005] [] e) [6,w2,764247,1788041,w3,w0,w1] [] (n (s [6,w2,764247,1796301,w3,w0,4198337] [900]) [6,w2,764247,1796301,w3,w0,4329409] [968] e))) [6,w2,764247,1821083,w3,w0,w1] [] (n (n (n (s [6,w2,764247,1829343,w3,w0,4198337] []) [6,w2,764247,w3,1985195,w0,4190271] [] e) [6,w2,764247,w3,1985195,w0,w1] [] (n (s [6,w2,764247,w3,1985195,w0,w1,6321357] []) [6,w2,764247,w3,1985195,w0,4198337] [1218] e)) [6,w2,764247,w3,1985195,w0,4198338] [1154] (n (n (s [6,w2,764247,w3,1985195,w0,4198340] []) [6,w2,764247,w3,1985195,w0,4198352] [] e) [6,w2,764247,w3,1985195,w0,4198356] [2061] (n (s [6,w2,764247,w3,1985195,w0,4329408] []) [6,w2,764247,w3,1985195,w0,4329409] [1288] e))))) [6,w2,764247,w3,1985195,w0,4329410] [908] (n (n (n (n (n (s [6,w2,764247,w3,1985195,w0,4796357,5394377] []) [6,w2,764247,w3,1985195,w0,4853699] [] (s [6,w2,764247,w3,1985195,4190271,6288323] [])) [6,w2,764247,w3,1985199,w0,w1] [] (n (s [6,w2,764247,w3,1985211,w0,w1] []) [6,w2,764247,w3,1985215,w0,w1] [] e)) [6,w2,764247,w3,1986219,w0,w1] [] (n (n (s [6,w2,764247,w3,2050731,w0,w1] []) [6,w2,764247,w3,2083771,w0,4190271] [] e) [6,w2,764247,w3,2083771,w0,w1] [] (n (s [6,w2,764247,w3,2083771,w0,w1,6321357] []) [6,w2,764247,w3,w0,3296445,4198344] [] e))) [6,w2,764247,w3,w0,4190271,6403412] [2692] (n (n (n (s [6,w2,764247,w3,w0,4190271,7091812] []) [6,w2,764247,w3,w0,4190271,7190390] [] e) [6,w2,764247,w3,w0,4190271,7323510] [] (n (s [6,w2,764247,w3,w0,4190271,8241014] []) [6,w2,764247,w3,w0,w1,6304836] [2692] e)) [6,w2,764247,w3,w0,w1,6403412] [2692] (n (n (s [6,w2,764247,w3,w0,w1,6536534] [900,2692]) [6,w2,764247,w3,w0,w1,6666100] [2692] e) [6,w2,764247,w3,w0,w1,6666102] [2692] (n (s [6,w2,764247,w3,w0,w1,7091812] []) [6,w2,764247,w3,w0,w1,7124854] [] e)))) [6,w2,764247,w3,w0,w1,7189366] [] (n (n (n (n (s [6,w2,764247,w3,w0,w1,7189878] []) [6,w2,764247,w3,w0,w1,7190070] [] e) [6,w2,764247,w3,w0,w1,7190134] [] (n (s [6,w2,764247,w3,w0,w1,7190326] []) [6,w2,764247,w3,w0,w1,7190388] [] e)) [6,w2,764247,w3,w0,w1,7190390] [] (n (n (s [6,w2,764247,w3,w0,w1,7192438] []) [6,w2,764247,w3,w0,w1,7323510] [] e) [6,w2,764247,w3,w0,w1,8142438] [] (n (s [6,w2,764247,w3,w0,w1,8241014] []) [6,w2,764247,w3,w0,w1,8372086] [] e))) [6,w2,764247,w3,w0,4198337,7190390] [] (n (n (n (s [6,w2,764247,w3,w0,4198338,7190390] [1154,2692]) [6,w2,764247,w3,w0,4198340,7190390] [] e) [6,w2,764247,w3,w0,4198344,7190390] [] (n (s [6,w2,764247,w3,w0,4198352,7190390] []) [6,w2,764247,w3,w0,4198356,7190390] [1541] e)) [6,w2,764247,w3,w0,4198368,7190390] [] (n (n (s [6,w2,764247,w3,w0,4329408,7190390] []) [6,w2,764247,w3,w0,4329409,7190390] [] e) [6,w2,764247,w3,w0,4722624,7190390] [2692] (n (s [6,w2,764247,w3,w0,4722626,7190390] []) [6,w2,764247,w3,w0,5246912,7190390] [] e))))))
def N_58 : BT := n T_56 [6,w2,763991,w3,w0,w1,7190390] [] T_57
def N_59 : BT := n N_55 [6,w2,601157,1838626,1985195,w0,w1] [] N_58
def N_60 : BT := n N_52 [6,w2,600135,1985195,2067250,w0,w1] [] N_59
def N_61 : BT := n N_45 [6,w2,w4,1263753,w0,w1,6485469] [] N_60
def N_62 : BT := n N_30 [6,w2,w4,w5,1837606,w0,4198372] [] N_61
def T_63 : BT := (n (n (n (n (n (n (s [6,w2,764247,w3,4190271,6288323,7190390] []) [6,w2,764247,1837603,w0,w1,7190390] [] (s [6,w2,764247,1837606,1985195,w0,w1] [])) [6,w2,764247,1837606,1985199,w0,w1] [] (n (s [6,w2,764247,1837606,w0,w1,7190390] []) [6,w2,764247,1837610,1985195,w0,w1] [] e)) [6,w2,764247,1837610,w0,3296445,w1] [] (n (n (s [6,w2,764247,1837610,w0,w1,7190390] []) [6,w2,764247,1837618,1985195,w0,w1] [] e) [6,w2,764247,1837618,1985211,w0,w1] [] (n (s [6,w2,764247,1837618,w0,w1,7190390] []) [6,w2,764247,1837622,1985195,w0,w1] [2052] e))) [6,w2,764247,1837622,1985215,w0,w1] [2052] (n (n (n (s [6,w2,764247,1837622,w0,w1,7190390] [1540]) [6,w2,764247,1838626,1985195,w0,w1] [] e) [6,w2,764247,1838626,1986219,w0,w1] [] (n (s [6,w2,764247,1838626,w0,w1,7190390] []) [6,w2,764247,1903138,1985195,w0,w1] [] e)) [6,w2,764247,1911399,1985195,w0,3296445,w1] [] (n (n (s [6,w2,764247,1968674,w0,w1,7190390] []) [6,w2,764247,1968675,w0,w1,7190390] [] e) [6,w2,764247,1985195,w0,2231357,w1] [1537,2433] (n (s [6,w2,764247,1985195,w0,2355229,w1] []) [6,w2,764247,1985195,w0,2624574,w1] [1539,2433] e)))) [6,w2,764247,1985195,w0,2994230,w1] [2690] (n (n (n (n (s [6,w2,764247,1985195,w0,3296445,4190271] []) [6,w2,764247,1985195,w0,3296445,w1] [1537] (s [6,w2,764247,1985195,w0,3935806,4190271] [])) [6,w2,764247,1985195,w0,3935806,w1] [1537] (n (s [6,w2,764247,1985195,w0,4190271,5394377] []) [6,w2,764247,1985195,w0,4190271,6033378] [] e)) [6,w2,764247,1985195,w0,4190271,6551005] [] (n (n (s [6,w2,764247,1985195,w0,4190271,7190390] []) [6,w2,764247,1985195,w0,w1,6551005] [] e) [6,w2,764247,1985195,w0,w1,6553085] [] (n (s [6,w2,764247,1985195,w0,w1,7190390] []) [6,w2,764247,1985195,w0,w1,7192446] [] e))) [6,w2,764247,1985195,w0,w1,7491581] [1537,2888] (n (n (n (s [6,w2,764247,1985195,w0,w1,7601629] []) [6,w2,764247,1985195,w0,w1,7757481] [] e) [6,w2,764247,1985195,w0,w1,7862269] [] (n (s [6,w2,764247,1985195,w0,w1,8130558] [1537]) [6,w2,764247,1985195,w0,w1,8150698] [968] e)) [6,w2,764247,1985195,w0,w1,8241014] [] (n (n (s [6,w2,764247,1985195,w0,w1,8255486] []) [6,w2,764247,1985195,w0,4329409] [40,97,1242,1304] e) [6,w2,764247,1985195,w0,4427730,5394377] [] (n (s [6,w2,764247,1985195,w0,4427730,6033378] [1154]) [6,w2,764247,1985195,w0,4722626] [2,40,97,1242] e))))) [6,w2,764247,1985195,w0,4796357,5394377] [898] (n (n (n (n (n (s [6,w2,764247,1985195,w0,4796357,6033378] [898,2887]) [6,w2,764247,1985195,w0,4960215,5394377] [] (s [6,w2,764247,1985195,w0,4960215,6033378] [2887])) [6,w2,764247,1985195,w0,5394377,6295548] [2702] (n (s [6,w2,764247,1985195,w0,6033378,6295548] [2700]) [6,w2,764247,2083771,w0,3935806,w1] [1539] e)) [6,w2,764247,2083771,w0,w1,6551005] [] (n (n (s [6,w2,764247,w0,3296445,w1,6403412] [1153]) [6,w2,764247,w0,3935806,w1,6403412] [1153,2690] e) [6,w2,764247,w0,4190271,6551005,7190390] [] (n (s [6,w2,764247,w0,w1,6403412,6551005] []) [6,w2,764247,w0,w1,6403412,7190390] [] e))) [6,w2,764247,w0,w1,6403412,7601629] [] (n (n (n (s [6,w2,764247,w0,w1,6403412,8241014] []) [6,w2,764247,w0,w1,6551005,7091812] [] e) [6,w2,764247,w0,w1,6551005,7190390] [] (n (s [6,w2,764247,w0,w1,6551005,7323510] []) [6,w2,764247,w0,w1,6551005,8241014] [] e)) [6,w2,764247,w0,w1,7077341,7190390] [] (n (n (s [6,w2,764247,w0,w1,7190390,7601629] []) [6,w2,764255,w3,w0,3296445,w1] [] e) [6,w2,764255,w3,w0,w1,7190390] [] (n (s [6,w2,764279,1296827,w3,w0,w1] []) [6,w2,764279,w3,w0,w1,7190390] [] e)))) [6,w2,765271,1297819,w3,w0,w1] [] (n (n (n (n (s [6,w2,765271,w3,w0,w1,7190390] []) [6,w2,860774,w0,2698365,w1,7190390] [] e) [6,w2,860774,w0,w1,7190390,7788474] [] (n (s [6,w2,862823,1796301,w0,w1,7190390] []) [6,w2,862823,1985195,w0,w1,7190390] [] e)) [6,w2,862823,w0,2698365,w1,7190390] [] (n (n (s [6,w2,862823,w0,2887230,w1,7190390] []) [6,w2,862823,w0,3935806,w1,7190390] [] e) [6,w2,862823,w0,w1,6551005,7190390] [] (n (s [6,w2,862823,w0,w1,7190390,7601629] []) [6,w2,862823,w0,w1,7190390,7788474] [2762] e))) [6,w2,895863,w3,w0,w1,7190390] [1218] (n (n (n (s [6,w2,1026935,w3,w0,w1,7190390] []) [6,w2,1648709,1985195,w0,3935806,w1] [] e) [6,w2,1648709,1985195,w0,w1,6551005] [] (n (s [6,w2,1648709,w0,w1,6551005,7190390] []) [6,w2,1648717,1985195,w0,3935806,w1] [] e)) [6,w2,1779781,w3,2083771,w0,w1] [] (n (n (s [6,w2,1779781,w3,w0,w1,7190390] []) [6,w2,1779781,1985195,2067250,w0,w1] [] e) [6,w2,1794252,1796301,w3,w0,w1] [900] (n (s [6,w2,1794252,w3,w0,w1,8386558] []) [6,w2,1796301,1796301,w3,w0,4198337] [900] e))))))
def T_64 : BT := (n (n (n (n (n (n (s [6,w2,1796301,w3,2067250,w0,4198337] [1218]) [6,w2,1796301,w3,2067250,w0,4796357,5394377] [] (s [6,w2,1796301,w3,2067251,w0,w1] [])) [6,w2,1796301,w3,2098236,w1,8386558] [] (n (s [6,w2,1796301,w3,w0,2100285,4190271] []) [6,w2,1796301,w3,w0,2100285,w1] [2433] e)) [6,w2,1796301,w3,w0,2100285,w1,4427730] [900,1541] (n (n (s [6,w2,1796301,w3,w0,2100285,4198337] []) [6,w2,1796301,w3,w0,2100349,w1] [2433] e) [6,w2,1796301,w3,w0,2165821,w1] [2433] (n (s [6,w2,1796301,w3,w0,2329918,4198337] [900,2708,3089]) [6,w2,1796301,w3,w0,2329919,w1] [] e))) [6,w2,1796301,w3,w0,2698365,4198337] [] (n (n (n (s [6,w2,1796301,w3,w0,2698365,4198345] [2504]) [6,w2,1796301,w3,w0,2994230,4796357] [900] e) [6,w2,1796301,w3,w0,3894525,4198337] [900] (n (s [6,w2,1796301,w3,w0,4190270] [4,916,1300]) [6,w2,1796301,w3,w0,4190270,w1] [] e)) [6,w2,1796301,w3,w0,4190270,4198337] [] (n (n (s [6,w2,1796301,w3,w0,4190271,4198337] []) [6,w2,1796301,w3,w0,4190271,8386558] [] e) [6,w2,1796301,w3,w0,w1,6295549] [1300,1569,1829,2340] (n (s [6,w2,1796301,w3,w0,w1,6551004] []) [6,w2,1796301,w3,w0,w1,6594355] [916] e)))) [6,w2,1796301,w3,w0,w1,7337982] [] (n (n (n (n (s [6,w2,1796301,w3,w0,w1,8386430] []) [6,w2,1796301,w3,w0,w1,8386558] [] e) [6,w2,1796301,w3,w0,w1,8388606] [] (n (s [6,w2,1796301,w3,w0,4198337] [4,97,916,1300]) [6,w2,1796301,w3,w0,4198337,4198337] [] e)) [6,w2,1796301,w3,w0,4198337,4427730] [900,1556] (n (n (s [6,w2,1796301,w3,w0,4198337,4427731] [900,1556]) [6,w2,1796301,w3,w0,4198337,4796357] [] e) [6,w2,1796301,w3,w0,4198337,5992397] [900] (n (s [6,w2,1796301,w3,w0,4198337,6288323] []) [6,w2,1796301,w3,w0,4198337,6295548] [1300,1569,1829] e))) [6,w2,1796301,w3,w0,4198337,6295549] [1300,1569,1829,2340] (n (n (n (s [6,w2,1796301,w3,w0,4198337,6551005] []) [6,w2,1796301,w3,w0,4198337,6592306] [900,916,2754,3014] e) [6,w2,1796301,w3,w0,4198337,7190390] [2754,3014] (n (s [6,w2,1796301,w3,w0,4198337,8386558] [3012]) [6,w2,1796301,w3,w0,4198341] [4,97,136,916,1300] e)) [6,w2,1796301,w3,w0,4263873] [4,97,140,1300] (n (n (s [6,w2,1796301,w3,w0,4796357,5394377] [900]) [6,w2,1796301,w3,w0,4796357,5394377,6592306] [900] e) [6,w2,1796301,w3,w0,4796357,5492699] [] (n (s [6,w2,1796301,w3,w0,4796357,7491581] [900]) [6,w2,1796301,w3,2100285,4190271] [4,97,129,916,1300] e))))) [6,w2,1796301,w3,2100285,4198337] [4,97,916,1300] (n (n (n (n (n (s [6,w2,1796301,w3,2698365,3296445,4190271] [900]) [6,w2,1796301,w3,2698365,5394377,6295548] [900] (s [6,w2,1796301,1837603,2067250,w0,w1] [])) [6,w2,1796301,1837603,w0,2100285,w1] [2433] (n (s [6,w2,1796301,1837603,w0,3935806,w1] []) [6,w2,1796301,1837603,w0,w1,6551005] [] e)) [6,w2,1796301,1837603,w0,w1,8386558] [] (n (n (s [6,w2,1796301,1837603,w0,4198337] [4,97,916]) [6,w2,1796301,1911399,w0,2100285,w1] [2433] e) [6,w2,1796301,1911399,w0,w1,8241014] [] (n (s [6,w2,1796301,1911399,w0,w1,8386558] []) [6,w2,1796301,1911399,w0,4198337] [4,72,97,916] e))) [6,w2,1796301,1911399,w0,4796357,5394377] [900] (n (n (n (s [6,w2,1796301,2058991,w0,2100285,w1] [1665,2433]) [6,w2,1796301,2058991,w0,w1,8386558] [] e) [6,w2,1796301,2058991,w0,4198337] [4,97] (n (s [6,w2,1796301,2058991,w0,4796357,5394377] []) [6,w2,1796301,w0,2100285,w1,6551005] [1793] e)) [6,w2,1796301,w0,w1,6551005,8386558] [] (n (n (s [6,w2,1796301,w0,4198337,6551005] [65]) [6,w2,1796301,w0,4796357,5394377,6551005] [] e) [6,w2,1812823,w3,w0,w1,7190390] [] (n (s [6,w2,1829343,w3,w0,2100285,w1] [1541,2433,2708,3089]) [6,w2,1829343,w3,w0,2165821,w1] [] e)))) [6,w2,1829343,w3,w0,w1,8255486] [] (n (n (n (n (s [6,w2,1829343,w3,w0,w1,8386558] []) [6,w2,1829343,w3,w0,4198337] [4,36,97,1238,1556,2068] e) [6,w2,1829343,w3,w0,4796357,5394377] [900] (n (s [6,w2,w3,2075511,2083771,w0,4190271] []) [6,w2,w3,2075511,2083771,w0,w1] [] e)) [6,w2,w3,2075511,2083771,w0,w1,6321357] [962] (n (n (s [6,w2,w3,2075511,w0,4190271,7190390] []) [6,w2,w3,2075511,w0,w1,6304836] [2692] e) [6,w2,w3,2075511,w0,w1,6403412] [2692] (n (s [6,w2,w3,2075511,w0,w1,7190390] []) [6,w2,w3,2075511,w0,w1,7323510] [] e))) [6,w2,w3,2075511,w0,w1,8372086] [962] (n (n (n (s [6,w2,w3,2098236,w1,7190390,7788474] []) [6,w2,w3,w0,2100285,w1,6592306] [1793] e) [6,w2,w3,w0,2698365,w1,7190386] [] (n (s [6,w2,w3,w0,2698365,4198340,7190390] []) [6,w2,w3,w0,3894525,4796357,5394377] [] e)) [6,w2,w3,w0,4190271,6403412,7788474] [] (n (n (s [6,w2,w3,w0,4190271,7190390,7788474] []) [6,w2,w3,w0,4190271,7190390,7856058] [] e) [6,w2,w3,w0,w1,6304836,7788474] [] (n (s [6,w2,w3,w0,w1,6403412,6477208] []) [6,w2,w3,w0,w1,6403412,7624360] [2060] e))))))
def N_65 : BT := n T_63 [6,w2,1796301,1829343,w3,w0,4198337] [1156] T_64
def T_66 : BT := (n (n (n (n (n (n (s [6,w2,w3,w0,w1,6403412,7856058] []) [6,w2,w3,w0,w1,6403412,8314810] [] (s [6,w2,w3,w0,w1,6536534,7788474] [])) [6,w2,w3,w0,w1,6592306,6594355] [] (n (s [6,w2,w3,w0,w1,6592306,8386558] []) [6,w2,w3,w0,w1,6666102,7788474] [] e)) [6,w2,w3,w0,w1,6927700,7788474] [] (n (n (s [6,w2,w3,w0,w1,7189366,7788474] []) [6,w2,w3,w0,w1,7189878,7788474] [] e) [6,w2,w3,w0,w1,7190326,7788474] [] (n (s [6,w2,w3,w0,w1,7190388,7788474] []) [6,w2,w3,w0,w1,7190390,7788474] [] e))) [6,w2,w3,w0,w1,7190390,7790522] [] (n (n (n (s [6,w2,w3,w0,w1,7190390,7854010] []) [6,w2,w3,w0,w1,7190390,7856058] [] e) [6,w2,w3,w0,w1,7190390,8380346] [] (n (s [6,w2,w3,w0,w1,7323510,7856058] []) [6,w2,w3,w0,w1,7323510,8314810] [] e)) [6,w2,w3,w0,4198337,6592306] [4,65,2130,2212,2262] (n (n (s [6,w2,w3,w0,4198337,7190390,7788474] []) [6,w2,w3,w0,4198338,7190390,7788474] [898] e) [6,w2,w3,w0,4198340,7190390,7788474] [] (n (s [6,w2,w3,w0,4198352,7190390,7788474] []) [6,w2,w3,w0,4263872,7190390,7788474] [] e)))) [6,w2,w3,w0,4796357,5394377,6592306] [] (n (n (n (n (s [6,w2,w3,2698365,3296445,4796357,5394377] []) [6,w2,w3,2698365,4796357,6295548,7190390] [] e) [6,w2,w3,4190271,6288323,7190390,7788474] [] (n (s [6,w2,1837603,w0,w1,7190390,7788474] []) [6,w2,1837606,1911399,1985195,w0,w1] [] e)) [6,w2,1837606,1911399,1985199,w0,w1] [] (n (n (s [6,w2,1837606,1911399,w0,w1,7190390] []) [6,w2,1837606,1985195,w0,2698365,w1] [] e) [6,w2,1837606,1985195,w0,w1,7788474] [] (n (s [6,w2,1837606,1985199,w0,2698365,w1] []) [6,w2,1837606,1985199,w0,w1,7788474] [] e))) [6,w2,1837606,w0,2698365,w1,7190390] [] (n (n (n (s [6,w2,1837606,w0,w1,7190390,7788474] []) [6,w2,1837618,1911399,1985195,w0,w1] [] e) [6,w2,1837618,1911399,1985211,w0,w1] [] (n (s [6,w2,1837618,1911399,w0,w1,7190390] []) [6,w2,1837618,1911415,1985211,w0,w1] [] e)) [6,w2,1837618,1911415,w0,w1,7190390] [] (n (n (s [6,w2,1837618,w0,w1,7190390,7788474] []) [6,w2,1838626,1911399,1985195,w0,w1] [] e) [6,w2,1838626,1911399,1986219,w0,w1] [] (n (s [6,w2,1838626,1911399,w0,w1,7190390] []) [6,w2,1838626,1912423,1986219,w0,w1] [] e))))) [6,w2,1838626,1912423,w0,w1,7190390] [] (n (n (n (n (n (s [6,w2,1838626,w0,w1,7190390,7788474] []) [6,w2,1903138,1911399,1985195,w0,w1] [] (s [6,w2,1903138,1985195,w0,w1,7788474] [])) [6,w2,1903138,2050731,w0,w1,7788474] [] (n (s [6,w2,1903138,w0,w1,7190390,7788474] []) [6,w2,1911398,w0,2698365,w1,7190390] [] e)) [6,w2,1911398,w0,w1,7190390,7788474] [] (n (n (s [6,w2,1911399,1985195,2067250,w0,4190271] []) [6,w2,1911399,1985195,2067250,w0,w1] [] e) [6,w2,1911399,1985195,2067250,w0,w1,6321357] [] (n (s [6,w2,1911399,1985195,w0,2100285,w1] [2433,3089]) [6,w2,1911399,1985195,w0,2355229,w1] [] e))) [6,w2,1911399,1985195,w0,3935806,4190271] [] (n (n (n (s [6,w2,1911399,1985195,w0,3935806,w1] []) [6,w2,1911399,1985195,w0,4165438,w1] [] e) [6,w2,1911399,1985195,w0,4190271,6033378] [] (n (s [6,w2,1911399,1985195,w0,4190271,6551005] []) [6,w2,1911399,1985195,w0,w1,6295548,6551005] [] e)) [6,w2,1911399,1985195,w0,w1,6321357] [] (n (n (s [6,w2,1911399,1985195,w0,w1,6551005] []) [6,w2,1911399,1985195,w0,w1,6553055] [3016] e) [6,w2,1911399,1985195,w0,w1,6553085] [] (n (s [6,w2,1911399,1985195,w0,w1,8130558] []) [6,w2,1911399,1985195,w0,w1,8241014] [] e)))) [6,w2,1911399,1985195,w0,w1,8386558] [] (n (n (n (n (s [6,w2,1911399,1985195,w0,4198337] [4,40,97]) [6,w2,1911399,1985195,w0,4427730,6033378] [910,1158] e) [6,w2,1911399,1985195,w0,4796357,5394377] [] (n (s [6,w2,1911399,1985195,w0,6033378,6295548] []) [6,w2,1911399,1985199,w0,3935806,w1] [] e)) [6,w2,1911399,2058991,w0,4796357,5394377] [3017] (n (n (s [6,w2,1911399,2067250,w0,w1,6403412] []) [6,w2,1911399,2083771,w0,3935806,w1] [1543] e) [6,w2,1911399,2083771,w0,w1,6551005] [3016] (n (s [6,w2,1911399,2098228,2698365,w1,7190390] []) [6,w2,1911399,2098228,3935806,w1,7190390] [] e))) [6,w2,1911399,w0,2355229,w1,7190390] [] (n (n (n (s [6,w2,1911399,w0,2698357,w1,7190390] []) [6,w2,1911399,w0,2698365,4190271,7190390] [] e) [6,w2,1911399,w0,2698365,w1,7091812] [1159] (n (s [6,w2,1911399,w0,2698365,w1,7190390] []) [6,w2,1911399,w0,2698365,w1,7323510] [] e)) [6,w2,1911399,w0,2698365,w1,8241014] [] (n (n (s [6,w2,1911399,w0,3296445,4796357,5394377] []) [6,w2,1911399,w0,3296445,5394377,6033378] [] e) [6,w2,1911399,w0,3592250,w1,7190390] [] (n (s [6,w2,1911399,w0,3935798,w1,7190390] []) [6,w2,1911399,w0,3935806,4190271,7190390] [] e))))))
def T_67 : BT := (n (n (n (n (n (n (s [6,w2,1911399,w0,3935806,w1,7091812] [1157]) [6,w2,1911399,w0,3935806,w1,7190390] [] (s [6,w2,1911399,w0,3935806,w1,7323510] [])) [6,w2,1911399,w0,3935806,w1,8241014] [] (n (s [6,w2,1911399,w0,4190271,4796357,7190390] []) [6,w2,1911399,w0,4190271,6033378,7190390] [] e)) [6,w2,1911399,w0,4190271,6551005,7190390] [] (n (n (s [6,w2,1911399,w0,4190271,7190390,7788474] []) [6,w2,1911399,w0,w1,6403412,6551005] [] e) [6,w2,1911399,w0,w1,6403412,8241014] [] (n (s [6,w2,1911399,w0,w1,6551005,7091812] []) [6,w2,1911399,w0,w1,6551005,7190390] [] e))) [6,w2,1911399,w0,w1,6551005,7323510] [] (n (n (n (s [6,w2,1911399,w0,w1,6551005,8241014] []) [6,w2,1911399,w0,w1,6553085,7190390] [] e) [6,w2,1911399,w0,w1,6893565,7190390] [] (n (s [6,w2,1911399,w0,w1,7077341,7190390] []) [6,w2,1911399,w0,w1,7091812,7159397] [2054] e)) [6,w2,1911399,w0,w1,7091812,7788474] [] (n (n (s [6,w2,1911399,w0,w1,7091812,8142438] []) [6,w2,1911399,w0,w1,7190390,7788474] [] e) [6,w2,1911399,w0,w1,7190390,7790526] [] (n (s [6,w2,1911399,w0,w1,7190390,8130558] []) [6,w2,1911399,w0,w1,7190390,8314810] [] e)))) [6,w2,1911399,w0,w1,7323510,7788474] [] (n (n (n (n (s [6,w2,1911399,w0,w1,7788474,8241014] [2122]) [6,w2,1911399,w0,w1,8142438] [4,40,65,136,978,1174,1559] e) [6,w2,1911399,w0,4427730,4796357,7190390] [] (n (s [6,w2,1911399,w0,4427730,6033378,7190390] [898]) [6,w2,1911399,w0,4796357,5394377,7190390] [] e)) [6,w2,1911399,w0,4796357,6295548,7190390] [] (n (n (s [6,w2,1911399,w0,5394377,6033378,7190390] []) [6,w2,1911399,w0,6033378,6295548,7190390] [] e) [6,w2,2058991,w0,2698365,3296445,w1] [1793,2305] (n (s [6,w2,2058991,w0,2698365,w1,5394377] [2440,2945]) [6,w2,2058991,w0,2698365,w1,7190390] [] e))) [6,w2,2058991,w0,w1,7190390,7788474] [] (n (n (n (s [6,w2,2058991,w0,4796357,5394377] [4,65,104,1761,1832,2281]) [6,w2,2075511,2083771,w0,3935806,w1] [1539] e) [6,w2,2075511,2083771,w0,w1,6551005] [3016] (n (s [6,w2,2075511,w0,3935806,w1,7190390] [1155]) [6,w2,2075511,w0,w1,6551005,7190390] [] e)) [6,w2,w0,2698365,w1,6477208,7190390] [] (n (n (s [6,w2,w0,3935806,w1,6403412,7788474] []) [6,w2,w0,4190271,6551005,7190390,7788474] [] e) [6,w2,w0,w1,6403412,6551005,7788474] [] (n (s [6,w2,w0,w1,6403412,7190390,7788474] []) [6,w2,w0,w1,6403412,7601629,7788474] [] e))))) [6,w2,w0,w1,6403412,7788474,8241014] [] (n (n (n (n (n (s [6,w2,w0,w1,6551005,7091812,7788474] []) [6,w2,w0,w1,6551005,7190390,7788474] [] (s [6,w2,w0,w1,6551005,7190390,7856058] [])) [6,w2,w0,w1,6551005,7190390,8314810] [] (n (s [6,w2,w0,w1,7077341,7190390,7788474] []) [6,231699,1796301,1837603,w0,w1] [4,97,1300] e)) [6,231699,1911399,1985195,w0,w1] [4,40,97] (n (n (s [6,764247,1296795,1911399,1985195,w0,w1] [1218,1348,1738,1860]) [6,764247,1296795,2067250,w0,3935806,w1] [] e) [6,764247,1296795,2067250,w0,w1,6551005] [] (n (s [6,764247,1296795,w0,2329918,w1,6551005] []) [6,764247,1296795,w0,w1,6551005,8156909] [] e))) [6,764247,1796301,1985195,2067250,w0,w1] [] (n (n (n (s [6,764247,1985195,w0,2329918,3296445,w1] [1793,2305]) [6,764247,1985195,w0,2329918,3935806,w1] [1793,2305] e) [6,764247,1985195,w0,2329918,w1,5394377] [2446,2945] (n (s [6,764247,1985195,w0,2329918,w1,6033378] [2444,2945]) [6,764247,1985195,w0,2329918,w1,6551005] [] e)) [6,764247,1985195,w0,2329918,w1,7190390] [] (n (n (s [6,764247,1985195,w0,w1,6551005,7788474] []) [6,764247,1985195,w0,w1,6551005,8156909] [2892] e) [6,764247,1985195,w0,4427730,5394377] [14,65,108,130,1771,1838,2153] (n (s [6,764247,1985195,w0,4427730,6033378] [12,65,108,1771,1836,2151]) [6,764247,w0,2329918,w1,6551005,7190390] [] e)))) [6,764247,w0,w1,6551005,7190390,7788474] [] (n (n (n (n (s [6,w0,w1,6551005,7190390,7788474,8156909] []) [7,0,73797,w2,w5,w3,w0,w1] [] e) [7,0,73797,w2,w5,w0,w1,6551005] [] (n (s [7,0,w2,w4,w5,w3,w0,4190271] []) [7,0,w2,w4,w5,w3,w0,w1] [] e)) [7,0,w2,w4,w5,w3,4190271,6288323] [] (n (n (s [7,0,w2,w4,w5,1911399,w0,4190271] []) [7,0,w2,w4,w5,1911399,w0,w1] [] e) [7,0,w2,w4,w5,w0,4190271,6551005] [] (n (s [7,0,w2,w4,w5,w0,w1,6403412] []) [7,0,w2,w4,w5,w0,w1,6551005] [] e))) [7,0,w2,w4,w5,w0,w1,7077341] [] (n (n (n (s [7,0,w2,w4,1296795,w0,w1,6551005] []) [7,0,w2,w4,1985195,w0,w1,6551005] [] e) [7,0,w2,w4,w0,w1,6551005,7190390] [] (n (s [7,0,w2,764247,w3,w0,w1,7190390] []) [7,0,w2,w3,w0,w1,7190390,7788474] [] e)) [7,1,73797,w2,w5,w3,w0,w1] [1292,1672,2689] (n (n (s [7,1,73797,w2,w5,w0,w1,6551005] [1672,2049]) [7,1,w2,w4,w5,w3,w0,4190271] [900] e) [7,1,w2,w4,w5,w3,w0,w1] [900,2689] (n (s [7,1,w2,w4,w5,w0,w1,6551005] [898,2049]) [7,4,73797,w2,w5,w3,w0,w1] [] e))))))
def N_68 : BT := n T_66 [6,w2,1911399,w0,3935806,w1,6403412] [] T_67
def N_69 : BT := n N_65 [6,w2,w3,w0,w1,6403412,7788474] [] N_68
def T_70 : BT := (n (n (n (n (n (n (s [7,4,w2,w4,w5,w3,w0,4190271] [900,1538]) [7,4,w2,w4,w5,w3,w0,w1] [900,1538] (s [7,4,w2,w4,w5,w0,w1,6551005] [898])) [7,4,w2,w4,w3,w0,w1,7190390] [902,1154,1538,2050,2690,3458] (n (s [7,1024,w2,w4,w5,w3,w0,w1] [900,1162,1538]) [7,1024,w2,w4,w5,w0,w1,6551005] [898,1160] e)) [7,2048,2049,w2,1796301,w3,w0,w1] [2817] (n (n (s [7,2048,3072,w2,w4,w5,w3,6295548] [1284,1674,2178]) [7,2048,w2,w4,w5,w3,w0,4190271] [] e) [7,2048,w2,w4,w5,w3,w0,w1] [] (n (s [7,2048,w2,w4,w5,w3,w0,4198337] []) [7,2048,w2,w4,w5,w3,w0,4198340] [] e))) [7,2048,w2,w4,w5,w3,w0,4263872] [] (n (n (n (s [7,2048,w2,w4,w5,1837603,w0,w1] []) [7,2048,w2,w4,w5,1837606,w0,w1] [] e) [7,2048,w2,w4,w5,1837618,w0,w1] [] (n (s [7,2048,w2,w4,w5,1838626,w0,w1] []) [7,2048,w2,w4,w5,1903138,w0,w1] [] e)) [7,2048,w2,w4,w5,1911399,w0,w1] [] (n (n (s [7,2048,w2,w4,w5,w0,w1,6551005] []) [7,2049,2049,w2,1796301,w3,w0,w1] [1156,2689] e) [7,2049,2050,w2,w4,1985195,w0,w1] [1154,2306,2691,2817,3458] (n (s [7,2049,2050,w2,1796301,w3,w0,w1] [1796,2691,2817,3458]) [7,2049,2052,w2,1796301,w3,w0,w1] [1284] e)))) [7,2049,2060,w2,1796301,w3,w0,w1] [1284] (n (n (n (n (s [7,2049,2064,w2,1796301,w3,w0,w1] [898,2690,3458]) [7,2049,2116,w2,w5,w3,w0,w1] [1292,1672,2184,2689] e) [7,2049,3072,w2,w4,w5,w3,6295548] [1156,1284,1672] (n (s [7,2049,3072,w2,1796301,w3,w0,w1] [1284,2689]) [7,2049,67584,w2,w5,1911399,w0,w1] [1672,2689,2825,3592] e)) [7,2049,67584,w2,1796301,w3,w0,w1] [2689,2817] (n (n (s [7,2049,73797,w2,w5,w3,w0,w1] [1292,1672,2689]) [7,2049,73797,w2,w5,w0,w1,6551005] [1672,2049] e) [7,2049,98578,w4,w5,w3,w0,w1] [898,1154,1538,2050,2691,3458] (n (s [7,2049,98578,w4,w3,w0,w1,7190390] [898,1154,1538,2051,2690]) [7,2049,198656,w2,1796301,w3,w0,w1] [2689,2817] e))) [7,2049,229650,w4,w5,w3,w0,w1] [900,2689] (n (n (n (s [7,2049,w2,231699,1796301,w3,w0,w1] [1284,1668,2689]) [7,2049,w2,598084,w5,w3,w0,w1] [2691,3458] e) [7,2049,w2,598084,w3,w0,w1,7190390] [1154,2051,2690] (n (s [7,2049,w2,w4,w5,w3,2098236,w1] [900,2689]) [7,2049,w2,w4,w5,w3,w0,4190270] [900,1154,1538] e)) [7,2049,w2,w4,w5,w3,w0,4190271] [900] (n (n (s [7,2049,w2,w4,w5,w3,w0,4192319] [900]) [7,2049,w2,w4,w5,w3,w0,w1] [900,2689] e) [7,2049,w2,w4,w5,w3,w0,4198337] [900] (n (s [7,2049,w2,w4,w5,w3,w0,4198338] [900,1154,1292,1538,1668,2312]) [7,2049,w2,w4,w5,w3,w0,4198340] [900] e))))) [7,2049,w2,w4,w5,w3,w0,4198352] [900,1154,1538,3458] (n (n (n (n (n (s [7,2049,w2,w4,w5,w3,w0,4263872] [900,2312]) [7,2049,w2,w4,w5,w3,w0,4427730,6295548] [1292,1668,2820] (s [7,2049,w2,w4,w5,w3,2100285,4190271] [900])) [7,2049,w2,w4,w5,w3,2100285,4198337] [900] (n (s [7,2049,w2,w4,w5,w3,4190271,6288323] [900,2689]) [7,2049,w2,w4,w5,1837603,w0,4190271] [898] e)) [7,2049,w2,w4,w5,1837603,w0,w1] [898,2689] (n (n (s [7,2049,w2,w4,w5,1837603,w0,4198337] [898]) [7,2049,w2,w4,w5,1837606,w0,w1] [898] e) [7,2049,w2,w4,w5,1837618,w0,w1] [898] (n (s [7,2049,w2,w4,w5,1838626,w0,w1] [898,2689]) [7,2049,w2,w4,w5,1903138,w0,w1] [898,2689] e))) [7,2049,w2,w4,w5,1911399,w0,4190271] [898] (n (n (n (s [7,2049,w2,w4,w5,1911399,w0,w1] [898,2689]) [7,2049,w2,w4,w5,1911399,w0,4198337] [898] e) [7,2049,w2,w4,w5,2058991,w0,w1] [898,2689] (n (s [7,2049,w2,w4,w5,w0,3935806,w1,6033378] [898,2049]) [7,2049,w2,w4,w5,w0,4190271,6551005] [898] e)) [7,2049,w2,w4,w5,w0,w1,6403412] [898,2049] (n (n (s [7,2049,w2,w4,w5,w0,w1,6551004] [898,2049]) [7,2049,w2,w4,w5,w0,w1,6551005] [898,2049] e) [7,2049,w2,w4,w5,w0,w1,6553053] [898,2049] (n (s [7,2049,w2,w4,w5,w0,w1,7077341] [898,1288,2049]) [7,2049,w2,w4,w5,w0,4198337,6551005] [898] e)))) [7,2049,w2,w4,1198219,w3,w0,w1] [900,1154,1292,1538,2312,2691,3458] (n (n (n (n (s [7,2049,w2,w4,1198221,w3,w0,w1] [902,1154,1538,2050,2690,3458]) [7,2049,w2,w4,1198233,w3,w0,w1] [902,1154,1538,2050,2690,3458] e) [7,2049,w2,w4,1199241,w3,w0,w1] [902,1154,1538,2050,2691,3458] (n (s [7,2049,w2,w4,1263753,w3,w0,w1] [1154,1538,2050,2312,2691,3458]) [7,2049,w2,w4,1296795,w3,w0,4190271] [1154,1284,1538,2050,2690,3458] e)) [7,2049,w2,w4,1296795,w3,w0,w1] [1154,1284,1538,2050,2691,3458] (n (n (s [7,2049,w2,w4,1296795,w3,w0,w1,6295548] [1284,2050,2691,2821,3458,3588,4354]) [7,2049,w2,w4,1296795,w3,w0,4198337] [902,1154,1284,1538,2050,2690,3458] e) [7,2049,w2,w4,1296795,1837603,w0,w1] [898,1154,1284,1538,2050,2691,3458] (n (s [7,2049,w2,w4,1296795,1911399,w0,w1] [2689]) [7,2049,w2,w4,1296795,w0,w1,6551005] [2049] e))) [7,2049,w2,w4,1796301,w3,w0,4190271] [1284,2690] (n (n (n (s [7,2049,w2,w4,1796301,w3,w0,w1] [1284,2691,3458]) [7,2049,w2,w4,1796301,w3,w0,4198337] [902,1154,1284,1538,2050,2690,3458] e) [7,2049,w2,w4,1796301,1837603,w0,w1] [898,1284,2691,3458] (n (s [7,2049,w2,w4,1796301,1911399,w0,w1] [2691,3458]) [7,2049,w2,w4,1796301,1985195,w0,w1] [898,1224,1800,2689] e)) [7,2049,w2,w4,1796301,2058991,w0,w1] [2689] (n (n (s [7,2049,w2,w4,1796301,w0,w1,6551005] [2049]) [7,2049,w2,w4,1829343,w3,w0,w1] [2691,3458] e) [7,2049,w2,w4,w3,2083771,w0,w1] [1154,1730,2050,2691,3458] (n (s [7,2049,w2,w4,w3,w0,4190271,7190390] [902,1154,1538,2050,2690]) [7,2049,w2,w4,w3,w0,w1,6403412] [902,1154,2051,2690] e))))))
def T_71 : BT := (n (n (n (n (n (n (s [7,2049,w2,w4,w3,w0,w1,7190390] [902,1154,1538,2051,2690]) [7,2049,w2,w4,w3,w0,w1,7192439] [2051,2690] (s [7,2049,w2,w4,w3,w0,w1,7323510] [902,1154,1538,2051,2690])) [7,2049,w2,w4,w3,w0,4198337,7190390] [902,1154,1538,2050,2690,3458] (n (s [7,2049,w2,w4,1837603,1985195,w0,w1] [902,2691,3458]) [7,2049,w2,w4,1837603,w0,w1,7190390] [898,1154,1538,2051,2690] e)) [7,2049,w2,w4,1911399,1985195,w0,w1] [898,2691,3458] (n (n (s [7,2049,w2,w4,1911399,2058991,w0,w1] [2691,3458]) [7,2049,w2,w4,1911399,w0,w1,7190390] [898,1154,1538,2051,2690] e) [7,2049,w2,w4,1985195,w0,3296445,w1] [898,2049] (n (s [7,2049,w2,w4,1985195,w0,3935806,w1] [898,1154,1538,2049,3458,3473,3985]) [7,2049,w2,w4,1985195,w0,w1,6551005] [898,2049] e))) [7,2049,w2,w4,1985195,w0,w1,7190390] [898,1154,1538,2049] (n (n (n (s [7,2049,w2,w4,w0,w1,6551005,7190390] [898,1537,2690]) [7,2049,w2,764247,1296795,w3,w0,w1] [1284,1668,2689] e) [7,2049,w2,764247,1796301,w3,w0,w1] [1284,2689] (n (s [7,2049,w2,764247,1829343,w3,w0,w1] [2689]) [7,2049,w2,764247,w3,1985195,w0,w1] [2689] e)) [7,2049,w2,764247,w3,w0,w1,7190390] [2049] (n (n (s [7,2049,w2,1796301,1796301,w3,w0,w1] [1284,2689]) [7,2049,w2,1796301,1829343,w3,w0,w1] [1668,2689] e) [7,2049,w2,1796301,w3,2067250,w0,w1] [900,2689] (n (s [7,2049,w2,1796301,w3,w0,2100285,w1] [900,2049,2113,3201]) [7,2049,w2,1796301,w3,w0,2329918,w1] [900,1284,2049,3473,3604,3985] e)))) [7,2049,w2,1796301,w3,w0,2698365,w1] [2049] (n (n (n (n (s [7,2049,w2,1796301,w3,w0,3894525,w1] [1284,2049]) [7,2049,w2,1796301,w3,w0,4190271] [36,932,1300,1556,1812] e) [7,2049,w2,1796301,w3,w0,4190271,w1] [2049] (n (s [7,2049,w2,1796301,w3,w0,w1] [36,129,932,1300,1556,1812,2049,2081,2705]) [7,2049,w2,1796301,w3,w0,w1,6295548] [1812,2049,2209,2469,3108] e)) [7,2049,w2,1796301,w3,w0,w1,6551005] [2049] (n (n (s [7,2049,w2,1796301,w3,w0,w1,6592306] [1284,1300,2049,3908]) [7,2049,w2,1796301,w3,w0,w1,7190390] [2049,3908] e) [7,2049,w2,1796301,w3,w0,w1,8386558] [900,2049,3908,4161] (n (s [7,2049,w2,1796301,w3,w0,4198337] [36,129,900,932,1300,1556,1812]) [7,2049,w2,1796301,1837603,w0,w1] [36,129,1300,2049,2081,2705] e))) [7,2049,w2,1796301,1911399,w0,w1] [36,104,129,1300,2049,2081,2705] (n (n (n (s [7,2049,w2,1796301,2058991,w0,w1] [36,129,2049,2081,2705,2961]) [7,2049,w2,1796301,w0,w1,6551005] [97,1537,1569,2065] e) [7,2049,w2,1829343,w3,w0,w1] [36,68,129,932,1556,1748,2049,2081,2196,2705,2837] (n (s [7,2049,w2,w3,w0,w1,6592306] [36,97,932,1172,1537,1569,2065,2980,3028]) [7,2049,w2,w3,w0,w1,7190390,7788474] [900,1537] e)) [7,2049,w2,1911399,1985195,w0,w1] [36,72,129,2049,2081,2705] (n (n (s [7,2049,231699,w4,w5,1837603,w0,w1] [898,1154,1538,2050,2691,3458]) [7,2049,231699,w4,w5,1911399,w0,w1] [898,1154,1538,2050,2691,3458] e) [7,2049,231699,w4,w5,w0,w1,6551005] [898,1154,1538,2051,2690,3458] (n (s [7,2049,w4,764247,w5,1911399,w0,w1] [898,1154,1538,2050,2691,3458]) [7,2049,w4,764247,w5,1985195,w0,w1] [898,1154,1538,2050,2691,3458] e))))) [7,2049,w4,764247,w5,w0,w1,6551005] [898,1154,1538,2051,2690,3458,3592] (n (n (n (n (n (s [7,2049,w4,w5,w0,w1,6551005,8156909] [898,1154,1539,2050,2694,3458]) [7,2051,w2,w4,w5,w3,w0,w1] [900,1162,1292,1538,1668,2178,2312,2689] (s [7,2052,2113,w2,w5,w3,w0,w1] [1157,1537,2049,3457])) [7,2052,3072,w2,w4,w5,w3,6295548] [1156,1284,2050] (n (s [7,2052,73797,w2,w5,w3,w0,w1] []) [7,2052,73797,w2,w5,w0,w1,6551005] [] e)) [7,2052,98578,w4,w5,w3,w0,w1] [898,1154,1538,2050,2690,3458] (n (n (s [7,2052,98578,w4,w3,w0,w1,7190390] [898,1154,1538,2050,2690,3458]) [7,2052,147593,w2,w4,w3,w0,w1] [904,1160,1544,2056,2696,3464] e) [7,2052,147593,w2,w4,w0,w1,6551005] [904,1160,1544,2056,2696,3464] (n (s [7,2052,164114,w4,w5,w3,w0,w1] [906,1162,1546,2058,2698,3466]) [7,2052,164114,w5,w3,w0,w1,7788474] [906,1162,1546,2058,2698] e))) [7,2052,229650,w4,w5,w3,w0,w1] [900] (n (n (n (s [7,2052,w2,598081,w5,w3,w0,w1] [903,1539,2051,3459]) [7,2052,w2,598081,w5,w3,w1,6288323] [903,1153,1539,2051,2691] e) [7,2052,w2,w4,1196169,w3,w0,w1] [910,1162,1538,2058,2698,3466] (n (s [7,2052,w2,w4,w5,w3,2098232,w1] [1538,3466]) [7,2052,w2,w4,w5,w3,w0,4190267] [900,1162,1538,2698] e)) [7,2052,w2,w4,w5,w3,w0,4190271] [900,1538] (n (n (s [7,2052,w2,w4,w5,w3,w0,4192319] [900,1538]) [7,2052,w2,w4,w5,w3,w0,4196288] [900,1153,1538,2689] e) [7,2052,w2,w4,w5,w3,w0,w1] [900,1538] (n (s [7,2052,w2,w4,w5,w3,w0,4198337] [900,1538]) [7,2052,w2,w4,w5,w3,w0,4198338] [900,1154,1538,2690] e)))) [7,2052,w2,w4,w5,w3,w0,4198340] [900,1538] (n (n (n (n (s [7,2052,w2,w4,w5,w3,w0,4198344] [900,1160,1538,2696]) [7,2052,w2,w4,w5,w3,w0,4198352] [900,1154,1538,2690] e) [7,2052,w2,w4,w5,w3,w0,4263872] [900,1538] (n (s [7,2052,w2,w4,w5,w3,w0,4329408] [900,1160,1538,2696,3464]) [7,2052,w2,w4,w5,w3,2100285,w1] [900,1153,1538,2689] e)) [7,2052,w2,w4,w5,w3,2100286,w1] [900,1155,1538,2691,3458] (n (n (s [7,2052,w2,w4,w5,w3,2100348,w1] [900,1153,1538,2689]) [7,2052,w2,w4,w5,w3,2100412,w1] [900,1161,1538,2697,3457] e) [7,2052,w2,w4,w5,w3,2100540,w1] [900,1155,1538,2691,3457] (n (s [7,2052,w2,w4,w5,w3,2165820,w1] [1153,1538,2689,3457]) [7,2052,w2,w4,w5,w3,2231356,w1] [900,1161,1538,2697,3457] e))) [7,2052,w2,w4,w5,w3,2698365,4190271] [1538] (n (n (n (s [7,2052,w2,w4,w5,w3,2698365,w1] [1538,3457]) [7,2052,w2,w4,w5,w3,2698365,4198340] [900,1153,1538,2689,3457] e) [7,2052,w2,w4,w5,w3,4190271,6288323] [900,1538,2689] (n (s [7,2052,w2,w4,w5,w3,w1,5690242] [1538,2689,3467]) [7,2052,w2,w4,w5,w3,w1,6288323] [900,1153,1538,2689] e)) [7,2052,w2,w4,w5,w3,w1,6290375] [1538,2689] (n (n (s [7,2052,w2,w4,w5,w3,4198340,6288323] [900,1153,1538,2689,3457]) [7,2052,w2,w4,w5,1837603,w0,w1] [902,1538] e) [7,2052,w2,w4,w5,1837606,w0,4190271] [898] (n (s [7,2052,w2,w4,w5,1837606,w0,w1] [898]) [7,2052,w2,w4,w5,1837606,w0,4198340] [898] e))))))
def N_72 : BT := n T_70 [7,2049,w2,w4,w3,w0,w1,6592306] [1284,2051,2690,3458] T_71
def T_73 : BT := (n (n (n (n (n (n (s [7,2052,w2,w4,w5,1837606,w1,6288323] [898]) [7,2052,w2,w4,w5,1837610,w0,w1] [898,1160,2696,3464] (s [7,2052,w2,w4,w5,1837618,w0,w1] [902])) [7,2052,w2,w4,w5,1837666,w0,w1] [898,1153,2689,3457] (n (s [7,2052,w2,w4,w5,1837730,w0,w1] [898,1161,2049,2697,3465]) [7,2052,w2,w4,w5,1837858,w0,w1] [903,1153,2049,2689,3457] e)) [7,2052,w2,w4,w5,1838626,w0,w1] [898] (n (n (s [7,2052,w2,w4,w5,1903138,w0,w1] [898]) [7,2052,w2,w4,w5,1911399,w0,4190271] [898] e) [7,2052,w2,w4,w5,1911399,w0,w1] [898] (n (s [7,2052,w2,w4,w5,1911399,w0,4198340] [898]) [7,2052,w2,w4,w5,1911399,2698365,w1] [3457] e))) [7,2052,w2,w4,w5,1911399,w1,6288323] [898,1153,2049,2689] (n (n (n (s [7,2052,w2,w4,w5,1968674,w0,w1] [898,1160,2056,2696,3464]) [7,2052,w2,w4,w5,1985195,w0,4190271] [898,1160,2056,2696,3464] e) [7,2052,w2,w4,w5,1985195,w0,w1] [898,1160,2056,2696,3464] (n (s [7,2052,w2,w4,w5,1985195,w0,4198340] [898,1160,2056,2696,3464]) [7,2052,w2,w4,w5,1985195,2698365,w1] [3465] e)) [7,2052,w2,w4,w5,1985195,w1,6288323] [898,1161,2056,2697] (n (n (s [7,2052,w2,w4,w5,1985199,w0,w1] [898,1160,2056,2696,3464]) [7,2052,w2,w4,w5,2058991,w0,w1] [898] e) [7,2052,w2,w4,w5,w0,4190271,6551005] [898] (n (s [7,2052,w2,w4,w5,w0,w1,6403412] [898]) [7,2052,w2,w4,w5,w0,w1,6477208] [898,1160,2056,3464] e)))) [7,2052,w2,w4,w5,w0,w1,6551001] [898,1161,2057] (n (n (n (n (s [7,2052,w2,w4,w5,w0,w1,6551005] [898]) [7,2052,w2,w4,w5,w0,w1,6553053] [898] e) [7,2052,w2,w4,w5,w0,w1,7077341] [898] (n (s [7,2052,w2,w4,w5,w0,w1,7601629] [898,1160,2056,3464]) [7,2052,w2,w4,w5,w0,4198340,6551005] [898] e)) [7,2052,w2,w4,w5,2698365,w1,6551005] [2689] (n (n (s [7,2052,w2,w4,w5,w1,6288323,6551005] [898,1153,2049,3457]) [7,2052,w2,w4,1198219,w3,w0,w1] [900,1154,1538,2690,3458] e) [7,2052,w2,w4,1198221,w3,w0,4190271] [900,1154,1538,2690,3458] (n (s [7,2052,w2,w4,1198221,w3,w0,w1] [900,1154,1538,2690,3458]) [7,2052,w2,w4,1198221,w3,w0,4198340] [900,1154,1538,2690,3458] e))) [7,2052,w2,w4,1198221,w3,2698365,w1] [900,1154,1538,2690,3458] (n (n (n (s [7,2052,w2,w4,1198221,w3,w1,6288323] [900,1154,1538,2690,3458]) [7,2052,w2,w4,1198221,1837606,w0,w1] [898] e) [7,2052,w2,w4,1198221,1911399,w0,w1] [898] (n (s [7,2052,w2,w4,1198221,1985195,w0,w1] [898]) [7,2052,w2,w4,1198221,1985199,w0,w1] [898] e)) [7,2052,w2,w4,1198221,w0,w1,6551005] [898] (n (n (s [7,2052,w2,w4,1198233,w3,w0,w1] [902,1154,1538,2690,3458]) [7,2052,w2,w4,1198281,w3,w0,w1] [901,1155,1538,2049,2691,3459] e) [7,2052,w2,w4,1198473,w3,w0,w1] [902,1155,1538,2049,2691,3459] (n (s [7,2052,w2,w4,1199241,w3,w0,w1] [902,1154,1538,2050,2690,3458]) [7,2052,w2,w4,1263753,w3,w0,w1] [902,1154,1538,2050,2690,3458] e))))) [7,2052,w2,w4,1296795,w3,w0,4190271] [902,1154,1538,2050,2690,3458] (n (n (n (n (n (s [7,2052,w2,w4,1296795,w3,w0,w1] [902,1154,1538,2050,2690,3458]) [7,2052,w2,w4,1296795,w3,w0,4198340] [902,1154,1538,2050,2690,3458] (s [7,2052,w2,w4,1296795,w3,2698365,w1] [902,1538,3459])) [7,2052,w2,w4,1296795,w3,w1,6288323] [902,1155,1538,2050,2691] (n (s [7,2052,w2,w4,1296795,1837606,w0,w1] [898,1154,1538,2050,2690,3458]) [7,2052,w2,w4,1296795,1911399,w0,w1] [898,1538] e)) [7,2052,w2,w4,1296795,w0,w1,6551005] [898] (n (n (s [7,2052,w2,w4,1296799,w3,w0,w1] [902,1154,1538,2050,2690,3458]) [7,2052,w2,w4,w3,2083771,w0,w1] [902,1154,1538,2050,2690,3458] e) [7,2052,w2,w4,w3,w0,4190271,7190390] [902,1154,1538,2050,2690,3458] (n (s [7,2052,w2,w4,w3,w0,w1,6403412] [902,1154,1538,2050,2690,3458]) [7,2052,w2,w4,w3,w0,w1,7190386] [902,1155,1538,2051,2690,3458] e))) [7,2052,w2,w4,w3,w0,w1,7190390] [902,1154,1538,2050,2690,3458] (n (n (n (s [7,2052,w2,w4,w3,w0,w1,7192438] [902,1154,1538,2050,2690,3458]) [7,2052,w2,w4,w3,w0,w1,7323510] [902,1154,1538,2050,2690,3458] e) [7,2052,w2,w4,w3,w0,4198340,7190390] [902,1154,1538,2050,2690,3458] (n (s [7,2052,w2,w4,w3,2698365,w1,7190390] [2691]) [7,2052,w2,w4,w3,w1,6288323,7190390] [902,1155,1538,2051,3459] e)) [7,2052,w2,w4,1837606,1985195,w0,w1] [902,1154,1538,2050,2690,3458] (n (n (s [7,2052,w2,w4,1837606,1985199,w0,w1] [902,1154,1538,2050,2690,3458]) [7,2052,w2,w4,1837606,w0,w1,7190390] [898,1154,1538,2050,2690,3458] e) [7,2052,w2,w4,1911399,w0,w1,7190390] [898,1154,1538,2050,2690,3458] (n (s [7,2052,w2,w4,1985195,w0,3296445,w1] [898]) [7,2052,w2,w4,1985195,w0,3935806,w1] [898,1154,2050,2690,3458] e)))) [7,2052,w2,w4,1985195,w0,w1,5394377] [898,1153,2049,3457] (n (n (n (n (s [7,2052,w2,w4,1985195,w0,w1,6033378] [898,1155,2051,3459]) [7,2052,w2,w4,1985195,w0,w1,6551005] [898] e) [7,2052,w2,w4,1985195,w0,w1,7190390] [898,1154,2050,3458] (n (s [7,2052,w2,w4,w0,w1,6551005,7190390] [898,2690]) [7,2052,w2,600135,w5,w3,w0,w1] [908,1162,2056,2698,3466] e)) [7,2052,w2,600141,w5,w3,w0,w1] [908,1162,2056,2698,3466] (n (n (s [7,2052,w2,600149,w5,w3,w0,w1] [908,1162,1544,2056,2698,3466]) [7,2052,w2,600261,w5,w3,w0,w1] [909,1163,1537,2057,2699,3467] e) [7,2052,w2,600389,w5,w3,w0,w1] [909,1163,1544,2057,2699,3467] (n (s [7,2052,w2,601157,w5,w3,w0,w1] [910,1162,1544,2058,2698,3466]) [7,2052,w2,731205,w5,w3,w0,w1] [910,1162,1544,2058,2698,3466] e))) [7,2052,w2,764247,w5,w3,w0,4190271] [910,1162,1544,2058,2698,3466] (n (n (n (s [7,2052,w2,764247,w5,w3,w0,w1] [910,1162,1544,2058,2698,3466]) [7,2052,w2,764247,w5,w3,w0,4198340] [910,1162,1544,2058,2698,3466] e) [7,2052,w2,764247,w5,w3,w1,6288323] [910,1163,1544,2058,2699] (n (s [7,2052,w2,764247,w5,1837606,w0,w1] [906,1162,1544,2058,2698,3466]) [7,2052,w2,764247,w5,1985195,w0,w1] [906,1160,1544,2056,2696,3464] e)) [7,2052,w2,764247,w5,w0,w1,6551005] [906,1160,1544,2056,2696,3464] (n (n (s [7,2052,w2,764247,1198221,w3,w0,w1] [908,1160,1544,2056,2696,3464]) [7,2052,w2,764247,1296795,w3,w0,w1] [900] e) [7,2052,w2,764247,w3,1985195,w0,w1] [908] (n (s [7,2052,w2,764247,w3,w0,w1,7190390] [900]) [7,2052,w2,w5,1796301,w3,2698365,w1] [1160,3467] e))))))
def T_74 : BT := (n (n (n (n (n (n (s [7,2052,w2,w5,w3,2098232,w1,7788474] [1160,2058,2698]) [7,2052,w2,w5,w3,w0,2698365,4190271] [910,1160,1546] (s [7,2052,w2,w5,w3,w0,2698365,w1] [910,1160,1546,3466])) [7,2052,w2,w5,w3,w0,2698365,4198340] [910,1160,1546,2058,2698,3466] (n (s [7,2052,w2,w5,w3,w0,2862463,w1] [910,1160,1546,3466]) [7,2052,w2,w5,w3,w0,4190271,7788474] [910,1160,1546,2058,2698] e)) [7,2052,w2,w5,w3,w0,w1,5690242] [910,1160,1546,2698,3467] (n (n (s [7,2052,w2,w5,w3,w0,w1,6477208] [910,1160,1546,2058,2698]) [7,2052,w2,w5,w3,w0,w1,7788474] [910,1160,1546,2058,2698] e) [7,2052,w2,w5,w3,w0,w1,7790526] [910,1160,1546,2698] (n (s [7,2052,w2,w5,w3,w0,w1,7856058] [910,1160,1546,2058,2698]) [7,2052,w2,w5,w3,w0,4198340,7788474] [910,1160,1546,2058,2698,3466] e))) [7,2052,w2,w5,w3,2698365,3296445,w1] [910,1160,1284,1546,3467] (n (n (n (s [7,2052,w2,w5,w3,2698365,w1,4796357] [1160,2699]) [7,2052,w2,w5,w3,2698365,w1,6288323] [910,1160,1546,2699] e) [7,2052,w2,w5,w3,2698365,w1,6295548] [910,1160,1546,2699] (n (s [7,2052,w2,w5,w3,2698365,w1,7788474] [1160,2699]) [7,2052,w2,w5,w3,w1,6288323,7788474] [910,1160,1546,2059] e)) [7,2052,w2,w5,1837606,1911399,w0,w1] [910,1160,1546,2058,2698,3466] (n (n (s [7,2052,w2,w5,1837606,w0,2698365,w1] [906,1160,1546,2058,2698,3466]) [7,2052,w2,w5,1837606,w0,w1,7788474] [906,1160,1546,2058,2698,3466] e) [7,2052,w2,w5,1911399,w0,2698365,w1] [906,1160,1544,2056,2696,3464] (n (s [7,2052,w2,w5,1911399,w0,3935806,w1] [906,1160,1546,2058,2698,3466]) [7,2052,w2,w5,1911399,w0,w1,4796357] [906,1160,1545,2057,2696,3465] e)))) [7,2052,w2,w5,1911399,w0,w1,6033378] [906,1160,1547,2059,2696,3467] (n (n (n (n (s [7,2052,w2,w5,1911399,w0,w1,6551005] [906,1160,1544,2056,2696,3464]) [7,2052,w2,w5,1911399,w0,w1,7788474] [906,1160,1546,2058,2696,3466] e) [7,2052,w2,w5,1985195,w0,2698365,w1] [906,1160,1546,3466] (n (s [7,2052,w2,w5,1985195,w0,w1,7788474] [906,1160,1546,2058,2698]) [7,2052,w2,w5,w0,2698365,w1,6551005] [906,1160,2696] e)) [7,2052,w2,w5,w0,w1,6551005,7788474] [906,1160,1544,2056,2698] (n (n (s [7,2052,w2,1198221,w3,w0,2698365,w1] [908,1160,1544,2056,2696,3464]) [7,2052,w2,1198221,w3,w0,w1,7788474] [908,1160,1544,2056,2696,3464] e) [7,2052,w2,1296795,w3,w0,2698365,w1] [900,1160,1544,3464] (n (s [7,2052,w2,1296795,w3,w0,w1,7788474] [900,1160,1544,2056,2696]) [7,2052,w2,w3,w0,2698365,w1,7190390] [900] e))) [7,2052,w2,w3,w0,w1,7190390,7788474] [900,2696] (n (n (n (s [7,2052,231702,w4,w5,1837606,w0,w1] [898,1154,1538,2050,2690,3458]) [7,2052,231702,w4,w5,1911399,w0,w1] [898,1154,1538,2050,2690,3458] e) [7,2052,231702,w4,w5,1985195,w0,w1] [898,1154,1538,2050,2690,3458] (n (s [7,2052,231702,w4,w5,w0,w1,6551005] [898,1154,1538,2050,2690,3458]) [7,2052,w4,764247,w5,1911399,w0,w1] [898,1154,1538,2050,2690,3458] e)) [7,2052,w4,764247,w5,1985195,w0,w1] [898,1154,1538,2050,2690,3458] (n (n (s [7,2052,w4,764247,w5,w0,w1,6551005] [898,1154,1538,2050,2690,3458]) [7,2052,w4,w5,1296795,1985195,w0,w1] [906,1154,1550,2058,2698,3466] e) [7,2052,w4,w5,1296795,w0,w1,6551005] [906,1154,1546,2058,2698,3466] (n (s [7,2052,w4,w5,w0,w1,6551005,8156909] [898,1154,1538,2050,2694,3458]) [7,2053,w2,w4,w5,w3,w0,4190271] [900,1538] e))))) [7,2053,w2,w4,w5,w3,w0,w1] [900,1538,2689] (n (n (n (n (n (s [7,2053,w2,w4,w5,w3,w0,4198341] [900,1538]) [7,2053,w2,w4,w5,w3,2100285,w1] [900,1153,1538,2689] (s [7,2053,w2,w4,w5,w3,2698365,w1] [1538,3457])) [7,2053,w2,w4,w5,w3,w1,6288323] [900,1153,1538,2689] (n (s [7,2053,w2,w4,w5,1837607,w0,w1] [898]) [7,2053,w2,w4,w5,1911399,w0,w1] [898,2689] e)) [7,2053,w2,w4,w5,1985195,w0,w1] [898,1160,2056,2697,3464] (n (n (s [7,2053,w2,w4,w5,w0,w1,6551005] [898,2049]) [7,2053,w2,w4,1198221,w3,w0,w1] [900,1154,1538,2690,3458] e) [7,2053,w2,w4,1296795,w3,w0,w1] [1154,1284,1538,2050,2691,3458] (n (s [7,2053,w2,w4,1796301,w3,w0,w1] [1284,2691,3458]) [7,2053,w2,w4,w3,w0,w1,7190390] [902,1154,1538,2051,2690] e))) [7,2053,w2,w4,1985195,w0,3296445,w1] [898,2049] (n (n (n (s [7,2053,w2,764247,w5,w3,w0,w1] [1162,1544,1668,2058,2699,3466]) [7,2053,w2,w5,1796301,w3,w0,w1] [1284,2699,3466] e) [7,2053,w2,w5,w3,w0,2698365,w1] [910,1160,1546,3466] (n (s [7,2053,w2,w5,w3,w0,3894525,w1] [1284,3466]) [7,2053,w2,w5,w3,w0,w1,7788474] [910,1160,1546,2059,2698] e)) [7,2053,w2,w5,w3,2698365,3296445,w1] [910,1160,1284,1546,3467] (n (n (s [7,2053,w2,1796301,w3,w0,3296445,w1] [2057,3464]) [7,2053,w2,1796301,w3,w0,w1] [9,36,932,1300,1556,1812,2049,2705] e) [7,2054,w2,w4,w5,w3,w0,w1] [900,1162,1538,2691] (n (s [7,2060,w2,w4,w5,w3,w0,4190271] [900,1162,1538]) [7,2060,w2,w4,w5,w3,w0,w1] [900,1162,1538] e)))) [7,2060,w2,w4,w5,w3,w0,4198348] [900,1162,1538] (n (n (n (n (s [7,2060,w2,w4,w5,w3,2698365,w1] [1538,3457]) [7,2060,w2,w4,w5,w3,3894525,w1] [3457] e) [7,2060,w2,w4,w5,w3,w1,6288323] [900,1162,1538,2689] (n (s [7,2060,w2,w4,w5,1837614,w0,w1] [898,1160]) [7,2060,w2,w4,w5,1911399,w0,w1] [898,1160] e)) [7,2060,w2,w4,w5,2058991,w0,w1] [898,1160] (n (n (s [7,2060,w2,w4,w5,w0,w1,6551005] [898,1160]) [7,2060,w2,w4,1198221,w3,w0,w1] [900,1538,2690,3458] e) [7,2060,w2,w4,1296795,w3,w0,w1] [902,1538,2050,2690,3458] (n (s [7,2060,w2,w4,1796301,w3,3296445,w1] [3459]) [7,2060,w2,w4,w3,w0,3296445,w1] [902,1538,3458] e))) [7,2060,w2,w4,w3,w0,w1,7190390] [902,1538,2050,2690] (n (n (n (s [7,2068,w2,w4,w5,w3,w0,4190271] [900,1162,1538]) [7,2068,w2,w4,w5,w3,w0,w1] [900,1162,1538] e) [7,2068,w2,w4,w5,w3,w0,4198356] [900,1162,1538] (n (s [7,2068,w2,w4,w5,w3,2329918,w1] [3457]) [7,2068,w2,w4,w5,w3,2862463,w1] [3457] e)) [7,2068,w2,w4,w5,w3,w1,6288323] [900,1162,1538,2689] (n (n (s [7,2068,w2,w4,w5,1837622,w0,w1] [898,1160]) [7,2068,w2,w4,w5,1911399,w0,w1] [898,1160] e) [7,2068,w2,w4,w5,1985195,w0,w1] [898,1160,2056,2696,3464] (n (s [7,2068,w2,w4,w5,w0,w1,6551005] [898,1160]) [7,2068,w2,600149,w5,w3,w0,w1] [908,1162,2056,2698,3466] e))))))
def N_75 : BT := n T_73 [7,2052,w2,w5,w3,2075511,w0,w1] [910,1160,1546,2058,2698,3466] T_74
def N_76 : BT := n N_72 [7,2052,w2,w4,w5,1837606,2698365,w1] [898] N_75
def N_77 : BT := n N_69 [7,4,73797,w2,w5,w0,w1,6551005] [] N_76
def T_78 : BT := (n (n (n (n (n (n (s [7,2068,w2,764247,w5,w3,w0,w1] [910,1162,1544,2058,2698,3466]) [7,2068,w2,764247,w5,w3,w0,4198356] [910,1162,1544,2058,2698,3466] (s [7,2068,w2,764247,w5,w3,2329918,w1] [1666,2058,3467])) [7,2068,w2,764247,w5,w3,2698365,w1] [1282,1544,3467] (n (s [7,2068,w2,764247,w5,w3,2862463,w1] [3467]) [7,2068,w2,764247,w5,w3,w1,6288323] [910,1163,1544,2058,2699] e)) [7,2068,w2,764247,w5,1837622,w0,w1] [906,1162,1544,2058,2698,3466] (n (n (s [7,2068,w2,764247,w5,1985195,w0,w1] [906,1160,1544,2056,2696,3464]) [7,2068,w2,764247,w5,w0,w1,6551005] [906,1160,1544,2056,2696,3464] e) [7,2068,w2,764247,1198237,w3,w0,w1] [908,1160,1544,2056,2696,2818,3464] (n (s [7,2068,w2,764247,1296795,w3,w0,w1] [900,2818]) [7,2068,w2,764247,w3,1985195,w0,w1] [908,2818] e))) [7,2068,w2,764247,w3,w0,w1,7190390] [900,2178] (n (n (n (s [7,2068,w2,w5,w3,1911399,w0,w1] [910,1160,1546,2062,2702,3470]) [7,2068,w2,w5,w3,2075511,w0,w1] [910,1160,1546,2058,2698,2818,3466] e) [7,2068,w2,w5,w3,w0,2698365,w1] [910,1160,1546,3466] (n (s [7,2068,w2,w5,w3,w0,2862463,w1] [910,1160,1546,3466]) [7,2068,w2,w5,w3,w0,w1,7624360] [910,1160,1546,2062,2698] e)) [7,2068,w2,w5,w3,w0,w1,7788474] [910,1160,1546,2058,2698] (n (n (s [7,2068,231702,764247,w5,w3,w0,w1] [910,1166,1548,2058,2702,3470]) [7,2068,764247,w5,w3,w0,2329918,w1] [910,1164,1550,2062,2702,3470] e) [7,2068,764247,w5,w3,w0,w1,4427730] [911,1164,1550,2063,2702,3471] (n (s [7,2068,764247,w5,w3,w0,w1,7788474] [910,1164,1550,2062,2702,3470]) [7,2068,764247,w5,w3,2329918,w1] [15,66,130,1178,1186,1550,1556,1682,1810,2703,2719] e)))) [7,2076,w2,w4,w5,w3,w0,w1] [900,1162,1538] (n (n (n (n (s [7,2076,w2,w4,1296795,w3,w0,w1] [902,1538,2050,2690,3458]) [7,2076,w4,764247,w5,w3,w0,w1] [908,1156,1540,2054,2692,2824,3460] (s [7,2076,w4,w5,1829343,w3,w0,w1] [908,1156,1540,2054,2692,2824,3460])) [7,2116,3072,w2,w4,w5,w3,6295548] [1156,1284,2050] (n (s [7,2116,w2,w4,w5,w3,w0,4190271] [900,1538]) [7,2116,w2,w4,w5,w3,w0,w1] [900,1538,2689] e)) [7,2116,w2,w4,w5,w3,w0,4198340] [900,1538] (n (n (s [7,2116,w2,w4,w5,w3,w0,4796357] [1538]) [7,2116,w2,w4,w5,1837670,w0,w1] [898,2689] e) [7,2116,w2,w4,w5,1911399,w0,w1] [898,2689] (n (s [7,2116,w2,w4,w5,1985195,w0,w1] [898,1160,2056,2697,3464]) [7,2116,w2,w4,w5,w0,w1,6551005] [898,2049] e))) [7,2116,w2,w4,1198285,w3,w0,w1] [900,1154,1538,2691,3458] (n (n (n (s [7,2116,w2,w4,1296795,w3,w0,w1] [902,1154,1538,2050,2691,3458]) [7,2116,w2,w4,w3,w0,w1,7190390] [902,1154,1538,2051,2690,3458] e) [7,2116,w2,764247,w5,w3,w0,w1] [910,1162,1544,2058,2699,3466] (n (s [7,2116,w2,w5,w3,w0,2698365,w1] [910,1160,1546,3466]) [7,2116,w2,w5,w3,w0,w1,6893565] [910,1160,1546] e)) [7,2116,w2,w5,w3,w0,w1,7788474] [910,1160,1546,2059,2698] (n (n (s [7,2116,w2,w5,w3,w0,4796357,6295548] [910,1160,1546,2058]) [7,2117,w2,w4,w5,w3,w0,w1] [900,1538,2689] e) [7,2117,w2,w5,w3,w0,3296445,w1] [1284] (n (s [7,2117,w2,w5,w3,w0,w1] [10,36,129,932,1300,1556,1812,2081]) [7,2117,w2,w5,w3,w0,w1,6295548] [1812,2209,2469,3108,3784] e))))) [7,2117,w2,w5,w3,w0,w1,7491581] [1284] (n (n (n (n (n (s [7,2120,w2,w4,w5,w3,w0,w1] [900,1162,1539,2689,3464]) [7,2128,w2,w4,w5,w3,w0,w1] [901,1162,1539,2689,3458] (s [7,2252,w2,w4,w5,w3,w0,w1] [900,1162,1538,2689])) [7,2388,w2,w4,w5,w3,w0,w1] [900,1162,1538,2689] (n (s [7,2388,w2,w4,w5,w3,w0,w1,6295548] [1538,2819,2945,3586]) [7,2388,w2,764247,w5,w3,w0,w1] [910,1162,1544,2058,2699,2817,3466] e)) [7,3072,3072,w2,w4,w5,w3,6295548] [1156,1546,2050] (n (n (s [7,3072,67584,w2,w4,w5,w3,6295548] [1154,2050,2178]) [7,3072,73797,w2,w5,w3,w0,w1] [] e) [7,3072,73797,w2,w5,w0,w1,6551005] [] (n (s [7,3072,229650,w4,w5,w3,w0,w1] [900,1160]) [7,3072,w2,232722,w4,w5,w3,6295548] [900,964,1284,1544,1678,1802,2182,2306] e))) [7,3072,w2,w4,764247,w5,w3,6295548] [900,1162,1668,1802,2050] (n (n (n (s [7,3072,w2,w4,w5,1796301,w3,6295548] [900,1162,1538,2180]) [7,3072,w2,w4,w5,w3,2093059] [36,74,98,900,932,1162,1170,1194,1300,1322,1538,1562,1570,1692,1698,2068,2334,2454,2472] e) [7,3072,w2,w4,w5,w3,2093059,w0] [900,1162,1538] (n (s [7,3072,w2,w4,w5,w3,2093059,6295548] [900,1162,1538]) [7,3072,w2,w4,w5,w3,2097212,4190271] [900,1162,1538] e)) [7,3072,w2,w4,w5,w3,2097212,w1] [900,1162,1538] (n (n (s [7,3072,w2,w4,w5,w3,w0,4190271] [900,1162,1538]) [7,3072,w2,w4,w5,w3,w0,4193343] [900,1162,1538] e) [7,3072,w2,w4,w5,w3,w0,w1] [900,1162,1538] (n (s [7,3072,w2,w4,w5,w3,w0,4198337] [900,1162,1538]) [7,3072,w2,w4,w5,w3,w0,4198340] [900,1162,1538] e)))) [7,3072,w2,w4,w5,w3,w0,4263872] [900,1162,1538] (n (n (n (n (s [7,3072,w2,w4,w5,w3,w0,6295548] [900,1162,1538]) [7,3072,w2,w4,w5,w3,2329918,6295548] [900,1162,1294,1538,1670] e) [7,3072,w2,w4,w5,w3,4190271,6288323] [900,1162,1538] (n (s [7,3072,w2,w4,w5,w3,4190271,6295548] [900,1162,1538]) [7,3072,w2,w4,w5,w3,6295548] [36,74,98,900,932,1162,1170,1194,1300,1322,1538,1562,1570,1692,1698,2068,2334,2454,2472] e)) [7,3072,w2,w4,w5,w3,6295548,6295548] [900,1162,1538] (n (n (s [7,3072,w2,w4,w5,w3,6295548,6524926] [900,1162,1294,1538,1670,4038]) [7,3072,w2,w4,w5,w3,6295548,6551005] [900,1162,1538,2312,3912] e) [7,3072,w2,w4,w5,w3,6295548,8385535] [900,1162,1538,3778,3914,4036] (n (s [7,3072,w2,w4,w5,1837603,w0,w1] [902,1162,1538]) [7,3072,w2,w4,w5,1837606,w0,w1] [902,1162,1538] e))) [7,3072,w2,w4,w5,1837618,w0,w1] [902,1162,1538] (n (n (n (s [7,3072,w2,w4,w5,1838626,w0,4190271] [898,1160]) [7,3072,w2,w4,w5,1838626,w0,w1] [898,1160] e) [7,3072,w2,w4,w5,1838626,w0,6295548] [898,1160] (n (s [7,3072,w2,w4,w5,1838626,6295548] [38,74,98,898,930,1160,1170,1192,1302,1322,1562,1694,1698,2330,2450,2472]) [7,3072,w2,w4,w5,1903138,w0,w1] [898,1160] e)) [7,3072,w2,w4,w5,1911399,w0,4190271] [898,1160] (n (n (s [7,3072,w2,w4,w5,1911399,w0,w1] [898,1160]) [7,3072,w2,w4,w5,1911399,w0,6295548] [898,1160,2952] e) [7,3072,w2,w4,w5,1911399,6295548] [38,74,98,136,898,930,1160,1170,1192,1298,1562,1686,2968] (n (s [7,3072,w2,w4,w5,1912423,w0,w1] [898,1160]) [7,3072,w2,w4,w5,2058991,w0,w1] [898,1160] e))))))
def T_79 : BT := (n (n (n (n (n (n (s [7,3072,w2,w4,w5,w0,w1,6403412] [898,1160]) [7,3072,w2,w4,w5,w0,w1,6549981] [898,1160] (s [7,3072,w2,w4,w5,w0,w1,6551005] [898,1160])) [7,3072,w2,w4,w5,w0,w1,6553053] [898,1160] (n (s [7,3072,w2,w4,w5,w0,w1,7077341] [898,1160]) [7,3072,w2,w4,w5,w0,6295548,6551005] [898,1160] e)) [7,3072,w2,w4,w5,6295548,6551005] [34,72,898,930,1160,1170,1192,1298,1320,1562,1690,3112,3160] (n (n (s [7,3072,w2,w4,1199241,1838626,w0,w1] [898]) [7,3072,w2,w4,1199241,1911399,w0,w1] [898] e) [7,3072,w2,w4,1199241,1985195,w0,w1] [898,1160] (n (s [7,3072,w2,w4,1199241,1986219,w0,w1] [898,1160]) [7,3072,w2,w4,1199241,w0,w1,6551005] [898] e))) [7,3072,w2,w4,1296795,1911399,w0,w1] [898,1538] (n (n (n (s [7,3072,w2,w4,1296795,w0,w1,6551005] [898]) [7,3072,w2,w4,1985195,w0,3296445,w1] [898] e) [7,3072,w2,w4,1985195,w0,w1,6551005] [898] (n (s [7,3072,w2,w4,w0,w1,6551005,7190390] [898,2690]) [7,3072,w2,601157,1199241,w3,w0,w1] [900] e)) [7,3072,w2,601157,1296795,w3,w0,w1] [900] (n (n (s [7,3072,w2,601157,w3,w0,w1,7190390] [900]) [7,3072,w2,764247,1296795,w3,w0,w1] [900,1160] e) [7,3072,w2,764247,w3,1985195,w0,w1] [908,1164] (n (s [7,3072,w2,764247,w3,w0,w1,7190390] [900]) [7,3072,w2,w3,w0,w1,7190390,7788474] [900,2696] e)))) [7,3073,w2,w4,w5,w3,w0,w1] [900,1162,1538,2689] (n (n (n (n (s [7,3076,w2,w4,w5,w3,w0,4190271] [900,1162,1538]) [7,3076,w2,w4,w5,w3,w0,w1] [900,1162,1538] e) [7,3076,w2,w4,w5,w3,w0,4198340] [900,1162,1538] (n (s [7,3076,w2,w4,w5,w3,w0,6295548] [900,1162,1538]) [7,3076,w2,w4,w5,w3,2698365,w1] [1538,3457] e)) [7,3076,w2,w4,w5,w3,w1,6288323] [900,1163,1538,2689] (n (n (s [7,3076,w2,w4,w5,w3,w1,6295548] [900,1163,1538]) [7,3076,w2,w4,w5,w3,w1,6893565] [1538] e) [7,3076,w2,w4,w5,w3,4796357,6295548] [900,1163,1284,1538] (n (s [7,3076,w2,w4,w5,w3,6295548] [11,36,900,932,1162,1170,1300,1538,1562,1684,2068,2324,2452]) [7,3076,w2,w4,w5,1838630,w0,w1] [898,1160] e))) [7,3076,w2,w4,w5,1911399,w0,w1] [898,1160] (n (n (n (s [7,3076,w2,w4,w5,1985195,w0,w1] [898,1160,2056,2696,3464]) [7,3076,w2,w4,w5,w0,w1,6551005] [898,1160] e) [7,3076,w2,w4,1199245,w3,w0,w1] [900,1538,2690,3458] (n (s [7,3076,w2,w4,1296795,w3,w0,w1] [902,1538,2050,2690,3458]) [7,3076,w2,w4,w3,w0,w1,7190390] [902,1538,2050,2690,3458] e)) [7,3076,w2,601157,w5,w3,w0,w1] [908,1162,2056,2698,3466] (n (n (s [7,3076,w2,764247,w5,w3,w0,w1] [910,1162,1544,2058,2698,3466]) [7,3076,w2,w5,w3,w0,2698365,w1] [910,1160,1546,3466] e) [7,3076,w2,w5,w3,w0,w1,7788474] [910,1160,1546,2058,2698] (n (s [7,3076,w2,w5,w3,2698365,w1,4796357] [1160,2699]) [7,3076,w2,w5,1911399,w0,w1,4796357] [906,1160,1545,2057,2696,3465] e))))) [7,3084,w2,w4,w5,w3,w0,w1] [900,1162,1538] (n (n (n (n (n (s [7,3092,w2,w4,w5,w3,w0,w1] [900,1162,1538]) [7,3092,w2,764247,w5,w3,w0,w1] [910,1162,1544,2058,2698,3466] (s [7,3145,w2,w4,w5,w3,w0,w1] [900,1162,1539,2689,3464])) [7,8261,w2,w4,w5,w3,w0,w1] [900] (n (s [7,8261,w2,w5,w3,2067250,w0,w1] [910,1546,1730,2058]) [7,8261,w2,w5,w3,2067250,w0,w1,6321357] [910,1546,2058] e)) [7,8261,w2,w5,w3,w0,w1] [10,36,129,932,1300,1556,1812] (n (n (s [7,8261,w2,w5,w3,w0,w1,6321357] [910,1546,1730]) [7,65536,73797,w2,w5,w3,w0,w1] [2689] e) [7,65536,73797,w2,w5,w0,w1,6551005] [2049] (n (s [7,65536,w2,w4,w5,w3,w0,4190271] [1538]) [7,65536,w2,w4,w5,w3,w0,w1] [1538,2689] e))) [7,65536,w2,w4,w5,w0,w1,6551005] [2049] (n (n (n (s [7,67584,73797,w2,w5,w3,w0,w1] [2689]) [7,67584,73797,w2,w5,w0,w1,6551005] [2049] e) [7,67584,147593,w2,w4,w3,w0,w1] [904,1160,1282,1544,2056,2697,3464] (n (s [7,67584,147593,w2,w4,w0,w1,6551005] [904,1160,1282,1544,2057,2696,3464]) [7,67584,164114,w4,w5,w3,w0,w1] [1162,2058] e)) [7,67584,164114,w5,w3,w0,w1,7788474] [906,1546,3466] (n (n (s [7,67584,w2,w4,1065097,w3,w0,w1] [908,1164,1540,2060,2701,3468]) [7,67584,w2,w4,1196169,w3,w0,w1] [906,1162,1538,2058,2699,3466] e) [7,67584,w2,w4,w5,w3,2098236,w1] [1538,2689] (n (s [7,67584,w2,w4,w5,w3,w0,4124735] [908,1164,1538]) [7,67584,w2,w4,w5,w3,w0,4190271] [1538] e)))) [7,67584,w2,w4,w5,w3,w0,4192319] [1538] (n (n (n (n (s [7,67584,w2,w4,w5,w3,w0,w1] [1538,2689]) [7,67584,w2,w4,w5,w3,w0,4198337] [1538,2689] e) [7,67584,w2,w4,w5,w3,w0,4198340] [1538,2689] (n (s [7,67584,w2,w4,w5,w3,w0,4198344] [904,1160,1538,2697]) [7,67584,w2,w4,w5,w3,w0,4263872] [1538] e)) [7,67584,w2,w4,w5,w3,w0,4329408] [904,1160,1538] (n (n (s [7,67584,w2,w4,w5,w3,w0,5246912] [908,1164,1538,1666,3460]) [7,67584,w2,w4,w5,w3,2165820,4190271] [1538] e) [7,67584,w2,w4,w5,w3,2165820,4263872] [1538] (n (s [7,67584,w2,w4,w5,w3,4190271,6288323] [1538,2689]) [7,67584,w2,w4,w5,1837603,w0,w1] [1538,2689] e))) [7,67584,w2,w4,w5,1837606,w0,w1] [1538] (n (n (n (s [7,67584,w2,w4,w5,1837610,w0,w1] [904,1160,1538,2696,3464]) [7,67584,w2,w4,w5,1837618,w0,w1] [1538] e) [7,67584,w2,w4,w5,1838626,w0,w1] [1538,2689] (n (s [7,67584,w2,w4,w5,1903138,w0,4190271] []) [7,67584,w2,w4,w5,1903138,w0,w1] [2689] e)) [7,67584,w2,w4,w5,1903138,w0,4263872] [] (n (n (s [7,67584,w2,w4,w5,1911399,w0,4190271] []) [7,67584,w2,w4,w5,1911399,w0,w1] [2689] e) [7,67584,w2,w4,w5,1911399,w0,4263872] [] (n (s [7,67584,w2,w4,w5,1968674,w0,w1] [904,1160,2697,3464]) [7,67584,w2,w4,w5,1985195,w0,4190271] [904,1160,2056,2696,3464] e))))))
def N_80 : BT := n T_78 [7,3072,w2,w4,w5,w0,4190271,6551005] [898,1160] T_79
def T_81 : BT := (n (n (n (n (n (n (s [7,67584,w2,w4,w5,1985195,w0,4263872] [904,1160,2056,2696,3464]) [7,67584,w2,w4,w5,2050731,w0,w1] [904,1160,2056,2697,3464] (s [7,67584,w2,w4,w5,2058991,w0,w1] [2689])) [7,67584,w2,w4,w5,w0,4190271,6551005] [] (n (s [7,67584,w2,w4,w5,w0,w1,6403412] [2049]) [7,67584,w2,w4,w5,w0,w1,6477208] [904,1160,2049,3464] e)) [7,67584,w2,w4,w5,w0,w1,6485469] [904,1160,2049] (n (n (s [7,67584,w2,w4,w5,w0,w1,6551005] [2049]) [7,67584,w2,w4,w5,w0,w1,6553053] [2049] e) [7,67584,w2,w4,w5,w0,w1,7077341] [2049] (n (s [7,67584,w2,w4,w5,w0,w1,7601629] [904,1160,1666,2049,3464]) [7,67584,w2,w4,w5,w0,4263872,6551005] [] e))) [7,67584,w2,w4,1263753,1903138,w0,w1] [2689] (n (n (n (s [7,67584,w2,w4,1263753,1911399,w0,w1] [2689]) [7,67584,w2,w4,1263753,1985195,w0,w1] [2689] e) [7,67584,w2,w4,1263753,2050731,w0,w1] [2689] (n (s [7,67584,w2,w4,1263753,w0,w1,6551005] [2049]) [7,67584,w2,w4,1296795,1911399,w0,w1] [2689] e)) [7,67584,w2,w4,1296795,w0,w1,6551005] [2049] (n (n (s [7,67584,w2,w4,1985195,w0,3296445,w1] [2049]) [7,67584,w2,w4,1985195,w0,w1,6551005] [2049] e) [7,67584,w2,w4,w0,w1,6551005,7190390] [1537,2690] (n (s [7,67584,w2,600135,w5,w3,w0,w1] [906,1162,1666,2699,3466]) [7,67584,w2,600141,w5,w3,w0,w1] [906,1162,2056,2698,3466] e)))) [7,67584,w2,600149,w5,w3,w0,w1] [906,1162,2056,3466] (n (n (n (n (s [7,67584,w2,600165,w5,w3,w0,w1] [910,1166,1540,2056,2702,3470]) [7,67584,w2,601157,w5,w3,w0,w1] [906,1162,2056,2699,3466] e) [7,67584,w2,731205,w5,w3,w0,w1] [906,1162,2056,2699,3466] (n (s [7,67584,w2,764247,w5,w3,w0,4190271] [906,1162,1544,3466]) [7,67584,w2,764247,w5,w3,w0,w1] [906,1162,1544] e)) [7,67584,w2,764247,w5,w3,w0,4263872] [1544,2056,2698] (n (n (s [7,67584,w2,764247,w5,1903138,w0,w1] [1544,2697,3464]) [7,67584,w2,764247,w5,1911399,w0,w1] [1544,2697,3464] e) [7,67584,w2,764247,w5,1985195,w0,w1] [904,1160,1544] (n (s [7,67584,w2,764247,w5,w0,w1,6551005] [904,1160,1544,3464]) [7,67584,w2,764247,1263753,w3,w0,w1] [904,1160,1544,2056,2697,3464] e))) [7,67584,w2,764247,1296795,w3,w0,w1] [] (n (n (n (s [7,67584,w2,764247,w3,1985195,w0,w1] []) [7,67584,w2,764247,w3,w0,w1,7190390] [] e) [7,67584,w2,1050624,w5,1911399,w0,w1] [1160,1550,2703,2945,3470] (n (s [7,67584,w2,w5,1311266,w0,w1,7788474] [910,1166,1546,2063,2702,3470]) [7,67584,w2,w5,1648709,w3,w0,w1] [910,1156,1282,1550,2056,2703,3470] e)) [7,67584,w2,w5,w3,1911399,w0,4190271] [910,1160,2062,2702,3470] (n (n (s [7,67584,w2,w5,w3,1911399,w0,w1] [910,1160,2062,2703,3470]) [7,67584,w2,w5,w3,1911399,w0,4263872] [910,1160,1546,2062,2702,3470] e) [7,67584,w2,w5,w3,2075511,w0,w1] [906,1160,2058] (n (s [7,67584,w2,w5,w3,w0,4190271,7788474] [906,1160,1546,2058,2698,3466]) [7,67584,w2,w5,w3,w0,w1,6477208] [906,1160,2059,2698,3466] e))))) [7,67584,w2,w5,w3,w0,w1,7624360] [910,1160,3466] (n (n (n (n (n (s [7,67584,w2,w5,w3,w0,w1,7788474] [906,1160,1546,2059,2698,3466]) [7,67584,w2,w5,w3,w0,w1,7856058] [906,1160,3466] (s [7,67584,w2,w5,w3,w0,w1,8314810] [910,1160,1546,2059,2698,3466])) [7,67584,w2,w5,w3,w0,4263872,7788474] [906,1160,1546,2058,2698] (n (s [7,67584,w2,w5,1903138,1911399,w0,w1] [1160,2699,3466]) [7,67584,w2,w5,1903138,w0,w1,7788474] [906,1160,1546,2059,2698] e)) [7,67584,w2,w5,1911399,2067250,w0,w1] [1160,2699,3466] (n (n (s [7,67584,w2,w5,1911399,w0,2698365,w1] [904,1160,1544,2057,2696,3464]) [7,67584,w2,w5,1911399,w0,3935806,w1] [906,1160,1546,2057,3466] e) [7,67584,w2,w5,1911399,w0,w1,6551005] [904,1160,1544,2057,2696,3464] (n (s [7,67584,w2,w5,1911399,w0,w1,7788474] [906,1160,1546,2057,2696]) [7,67584,w2,w5,1985195,w0,w1,7788474] [906,1160,1546,2059,2698,3466] e))) [7,67584,w2,w5,w0,w1,6551005,7788474] [904,1160,1545,2056,2698,3464] (n (n (n (s [7,67584,w2,1263753,w3,1911399,w0,w1] [904,1160,1544,2056,2697,3464]) [7,67584,w2,1263753,w3,w0,w1,7788474] [904,1160,1544,2057,2696,3464] e) [7,67584,w2,1296795,w3,1911399,w0,w1] [900,1156,2052,2697,3464] (n (s [7,67584,w2,1296795,w3,w0,w1,7788474] [904,1160,1544,2057,2696,3464]) [7,67584,w2,w3,1911399,1985195,w0,w1] [900,1540,2052,2693,3460] e)) [7,67584,w2,w3,1911399,w0,w1,7190390] [900,1540,2053,2692,3460] (n (n (s [7,67584,w2,w3,1985195,w0,w1,7788474] [908,1548,2061,2700,3468]) [7,67584,w2,w3,w0,w1,7190390,7788474] [1537,2696] e) [7,67584,764247,w5,w3,w0,2329918,w1] [910,1164,2702] (n (s [7,67584,764247,w5,w3,w0,w1,7788474] [910,1550,3470]) [7,67584,w5,1296795,w3,1911399,w0,w1] [1164,2060,2701,3468] e)))) [7,67584,w5,1296795,w3,w0,w1,7788474] [1166,1546,2063,2702,3470] (n (n (n (n (s [7,67584,w5,w3,w0,w1,7788474,8156909] [908,1166,1549,2060,2700,3470]) [7,67585,w2,w4,w5,w3,w0,4190271] [900,1538] e) [7,67585,w2,w4,w5,w3,w0,w1] [900,1538,2689] (n (s [7,67585,w2,w4,w5,w3,w0,4263873] [900,1538]) [7,67585,w2,w4,w5,1903139,w0,w1] [898,2689] e)) [7,67585,w2,w4,w5,1911399,w0,w1] [898,2689] (n (n (s [7,67585,w2,w4,w5,1985195,w0,w1] [906,1160,2056,2697,3464]) [7,67585,w2,w4,w5,w0,w1,6551005] [898,2049] e) [7,67585,w2,w4,1263753,w3,w0,w1] [1154,1538,2691,3458] (n (s [7,67585,w2,w4,1296795,w3,w0,4190271] [1154,1538,2050,2690,3458]) [7,67585,w2,w4,1296795,w3,w0,w1] [1154,1538,2050,2691,3458] e))) [7,67585,w2,w4,1296795,w3,w0,4263873] [1154,1538,2050,2690,3458] (n (n (n (s [7,67585,w2,w4,1296795,1903139,w0,w1] [1154,1538,2050,2691,3458]) [7,67585,w2,w4,1296795,1911399,w0,w1] [2689] e) [7,67585,w2,w4,1296795,w0,w1,6551005] [2049] (n (s [7,67585,w2,w4,1796301,w3,w0,w1] [2691,3458]) [7,67585,w2,w4,1829343,w3,w0,w1] [2691,3458] e)) [7,67585,w2,w4,w3,1985195,w0,w1] [902,1158,2054,2695,3462] (n (n (s [7,67585,w2,w4,w3,2083771,w0,w1] [1154,2050,2691,3458]) [7,67585,w2,w4,w3,w0,w1,7091812] [1158,1538,2051,2690] e) [7,67585,w2,w4,w3,w0,w1,7190390] [902,1154,1538,2051,2690] (n (s [7,67585,w2,764247,w5,w3,w0,w1] [1162,1544]) [7,67585,w2,764247,1296795,w3,w0,w1] [] e))))))
def T_82 : BT := (n (n (n (n (n (n (s [7,67585,w2,w5,1796301,w3,w0,w1] [2699,3466]) [7,67585,w2,w5,1829343,w3,w0,w1] [] (s [7,67585,w2,w5,w3,1911399,w0,w1] [910,1160,2062,2703,3470])) [7,67585,w2,w5,w3,w0,w1,7788474] [910,1160,1546,2059,2698] (n (s [7,67585,w2,w5,1911399,w0,w1] [10,129,2057,2072,2081,2696,2713]) [7,67585,w2,1296795,1796301,w3,w0,w1] [2697,3464] e)) [7,67585,w2,1296795,1829343,w3,w0,w1] [] (n (n (s [7,67585,w2,1296795,w3,1911399,w0,w1] [1156,2052,2697,3464]) [7,67585,w2,1296795,w3,w0,w1,7788474] [1160,1544,2057,2696] e) [7,67585,w2,1296795,1911399,w0,w1] [8,129,2057,2072,2081,2696,2713,2833] (n (s [7,67585,w2,1796301,w3,w0,w1] [12,129,1556,2049,2081,2705]) [7,67585,w2,1829343,w3,w0,w1] [8,129,1556,2081,2705,2833] e))) [7,67585,231699,w4,w5,w3,w0,w1] [900,1156,2050,2693,3460] (n (n (n (s [7,67585,w4,764247,w5,w3,w0,w1] [900,1156,2054]) [7,67585,w4,w5,1296795,w3,w0,4190271] [908,1548,2054,2700,3468] e) [7,67585,w4,w5,1296795,w3,w0,w1] [908,1548,2054,2701,3468] (n (s [7,67585,w4,w5,1296795,w3,w0,4263873] [908,1548,2054,2700,3468]) [7,67585,w4,w5,1296795,1903139,w0,w1] [902,1542,2054,2695,3462] e)) [7,67585,w4,w5,1296795,1911399,w0,w1] [902,1542,2054,2695,3462] (n (n (s [7,67585,w4,w5,1296795,1985195,w0,w1] [906,1154,1546,2058,2699,3466]) [7,67585,w4,w5,1296795,w0,w1,6551005] [906,1546,2059,2698,3466] e) [7,67585,w4,w5,1829343,w3,w0,w1] [900,1540,2054] (n (s [7,67585,w4,w5,w3,w0,w1,7091812] [900,1542,2053,2692,3460]) [7,67585,w4,w5,w3,w0,w1,8156909] [900,1156,1542,2053,2692,3460] e)))) [7,67585,w4,1296795,w3,w0,2329918,w1] [902,1158,1542,2055,3462] (n (n (n (n (s [7,67585,w4,1296795,w3,w0,3296445,w1] [900,1156,1542,2055,3460]) [7,67585,w4,1296795,w3,w0,w1,7190390] [902,1158,1542,2055,2694] e) [7,67585,w4,1296795,w3,w0,w1,8156909] [900,1156,1542,2055,2694] (n (s [7,67585,764247,w5,1296795,w3,w0,w1] [1220]) [7,67585,w5,1296795,1796301,w3,w0,w1] [972,2703,3470] e)) [7,67585,w5,1296795,1829343,w3,w0,w1] [] (n (n (s [7,67585,w5,1296795,w3,1911399,w0,w1] [1164,2060,2701,3468]) [7,67585,w5,1296795,w3,w0,w1,7788474] [1166,1546,2063,2702] e) [7,67585,w5,1296795,1911399,w0,w1] [10,129,2059,2074,2081,2698,2715,2833] (n (s [7,67588,w2,w4,w5,w3,w0,4190271] [900,1538]) [7,67588,w2,w4,w5,w3,w0,w1] [900,1538,2689] e))) [7,67588,w2,w4,w5,w3,w0,4263876] [900,1538] (n (n (n (s [7,67588,w2,w4,w5,w3,2165820,w1] [1153,1538,2689]) [7,67588,w2,w4,w5,w3,2698365,w1] [1538,3457] e) [7,67588,w2,w4,w5,w3,w1,6288323] [900,1153,1538,2689] (n (s [7,67588,w2,w4,w5,1903142,w0,w1] [898]) [7,67588,w2,w4,w5,1911399,w0,w1] [898,2689] e)) [7,67588,w2,w4,w5,1985195,w0,w1] [898,1160,2056,2697,3464] (n (n (s [7,67588,w2,w4,w5,w0,w1,6551005] [898,2049]) [7,67588,w2,w4,1263757,w3,w0,w1] [902,1154,1538,2690,3458] e) [7,67588,w2,w4,1296795,w3,w0,w1] [902,1154,1538,2050,2691,3458] (n (s [7,67588,w2,w4,w3,1985195,w0,w1] [902,1158,1538,2054,2695,3462]) [7,67588,w2,w4,w3,w0,w1,7190390] [902,1154,1538,2051,2690,3458] e))))) [7,67588,w2,764247,w5,w3,w0,w1] [910,1162,1544] (n (n (n (n (n (s [7,67588,w2,w5,w3,1911399,w0,w1] [910,1160,2062,2703,3470]) [7,67588,w2,w5,w3,w0,2698365,w1] [910,1160,1546,3466] (s [7,67588,w2,w5,w3,w0,2862463,w1] [910,1160])) [7,67588,w2,w5,w3,w0,w1,7788474] [910,1160,1546,2059,2698] (n (s [7,67588,w2,w5,w3,2329918,2698365,w1] [1160,1546,3467]) [7,67588,231702,w4,w5,w3,w0,w1] [900,1156,1542,2050,3460] e)) [7,67588,w4,764247,w5,w3,w0,w1] [900,1156,2054] (n (n (s [7,67588,w4,w5,1296795,w3,w0,w1] [908,1548,2054,2701,3468]) [7,67588,w4,w5,w3,w0,w1,8156909] [900,1156,1542,2053,2692,3460] e) [7,67588,w4,1296795,w3,w0,2329918,w1] [902,1156,1542,2055,2694,3462] (n (s [7,67588,764247,w5,w3,w0,2329918,w1] [910,1164,2702]) [7,67589,w2,w4,w5,w3,w0,w1] [900,1538,2689] e))) [7,67589,w2,w4,1296795,w3,w0,w1] [1154,1538,2050,2691,3458] (n (n (n (s [7,67589,w4,w5,1296795,w3,w0,w1] [908,1548,2054,2701,3468]) [7,67592,w2,w4,w5,w3,w0,w1] [908,1162,1538,2689] e) [7,67609,w2,w4,w5,w3,w0,w1] [908,1162,1538,2689] (n (s [7,67609,w2,w4,1296795,w3,w0,w1] [1538,2050,2691,3458]) [7,67609,w4,w5,1296795,w3,w0,w1] [908,1548,2054,2701,3468] e)) [7,67652,w2,w4,w5,w3,w0,w1] [900,1538,2689] (n (n (s [7,68608,w2,w4,w5,w3,w0,w1] [900,1162,1538,2689]) [7,68688,w2,w4,w5,w3,w0,w1] [901,1162,1539,2689,3458] e) [7,73733,w2,w4,w5,w3,w0,w1] [900] (n (s [7,73796,w2,w4,w5,w3,w0,w1] [900]) [7,73796,w2,w4,w5,1985195,w0,w1] [898,1160] e)))) [7,73796,w2,w4,w5,w0,w1,6403412] [898] (n (n (n (n (s [7,73796,w2,w4,w3,1985195,w0,w1] [902,1158,1538]) [7,73796,w2,w4,w3,w0,w1,6403412] [902,1154,1538,3458] e) [7,73797,73797,w2,w5,w3,w0,w1] [] (n (s [7,73797,73797,w2,w5,w0,w1,6551005] []) [7,73797,147593,w2,w4,w3,w0,w1] [1160,1544,2056] e)) [7,73797,147593,w2,w4,w0,w1,6551005] [1160,1544,3464] (n (n (s [7,73797,147593,w2,w3,w0,w1] [8,129,1176,1320,1560,1704]) [7,73797,147593,w2,w3,w0,w1,6551005] [1544] e) [7,73797,147593,w2,w0,w1,6551005] [8,97,1176,1320] (n (s [7,73797,229648,w2,w5,w3,w0,w1] []) [7,73797,229648,w2,w5,w0,w1,6551005] [] e))) [7,73797,w2,239959,w5,w3,w0,w1] [] (n (n (n (s [7,73797,w2,239959,w5,w0,w1,6551005] []) [7,73797,w2,w4,w5,w3,w0,4190271] [900] e) [7,73797,w2,w4,w5,w3,w0,w1] [900] (n (s [7,73797,w2,w4,w5,1911399,w0,w1] [898]) [7,73797,w2,w4,w5,1985195,w0,w1] [898,1160] e)) [7,73797,w2,w4,w5,w0,4190271,6551005] [898] (n (n (s [7,73797,w2,w4,w5,w0,w1,6551005] [898]) [7,73797,w2,w4,w5,w0,w1,7077341] [898] e) [7,73797,w2,w4,w5,w0,w1,7601629] [898,1160,3464] (n (s [7,73797,w2,w4,1296795,w3,w0,w1] [1154]) [7,73797,w2,w4,1296795,w0,w1,6551005] [] e))))))
def N_83 : BT := n T_81 [7,67585,w2,w5,1296795,1911399,w0,w1] [2697,3464] T_82
def N_84 : BT := n N_80 [7,67584,w2,w4,w5,1985195,w0,w1] [904,1160,2056,2697,3464] N_83
def T_85 : BT := (n (n (n (n (n (n (s [7,73797,w2,w4,w3,w0,w1,7190390] [902,1154,1538]) [7,73797,w2,w4,1985195,w0,w1,6551005] [898] (s [7,73797,w2,w4,w0,w1,6551005,7190390] [898])) [7,73797,w2,764247,w5,w3,w0,w1] [1162] (n (s [7,73797,w2,764247,w5,w0,w1,6551005] [1160,3464]) [7,73797,w2,w5,1272013,w3,w0,w1] [1224] e)) [7,73797,w2,w5,1272013,w0,w1,6551005] [1224] (n (n (s [7,73797,w2,w5,1296795,w3,w0,w1] []) [7,73797,w2,w5,1296795,w0,w1,6551005] [] e) [7,73797,w2,w5,1796301,w3,w0,w1] [] (n (s [7,73797,w2,w5,1796301,w0,w1,6551005] []) [7,73797,w2,w5,w3,w3,w0,w1] [1550] e))) [7,73797,w2,w5,w3,1911399,w0,w1] [908,2062] (n (n (n (s [7,73797,w2,w5,w3,1985195,w0,w1] []) [7,73797,w2,w5,w3,2067250,w0,w1] [910,1730,2058] e) [7,73797,w2,w5,w3,2098204,w0,w1] [] (n (s [7,73797,w2,w5,w3,w0,2174077,w1] [910,1544]) [7,73797,w2,w5,w3,w0,2329918,w1] [910] e)) [7,73797,w2,w5,w3,w0,2698365,w1] [910,1544] (n (n (s [7,73797,w2,w5,w3,w0,3296445,w1] []) [7,73797,w2,w5,w3,w0,3935806,w1] [1546] e) [7,73797,w2,w5,w3,w0,4190271] [14,1566] (n (s [7,73797,w2,w5,w3,w0,4190271,w1] []) [7,73797,w2,w5,w3,w0,4190271,6551005] [1544] e)))) [7,73797,w2,w5,w3,w0,w1] [14,129,1566] (n (n (n (n (s [7,73797,w2,w5,w3,w0,w1,6295548] []) [7,73797,w2,w5,w3,w0,w1,6551005] [1544] e) [7,73797,w2,w5,w3,w0,w1,6553055] [] (n (s [7,73797,w2,w5,w3,w0,w1,6553085] [1544]) [7,73797,w2,w5,w3,w0,w1,7077341] [1544] e)) [7,73797,w2,w5,w3,w0,w1,7190390] [3910] (n (n (s [7,73797,w2,w5,w3,w0,w1,7601629] []) [7,73797,w2,w5,w3,w0,w1,7788474] [910,1546] e) [7,73797,w2,w5,w3,w0,w1,7862271] [4161] (n (s [7,73797,w2,w5,w3,w0,w1,8156909] [910]) [7,73797,w2,w5,w3,w0,w1,8314810] [910,1546] e))) [7,73797,w2,w5,w3,w0,w1,8388607] [] (n (n (n (s [7,73797,w2,w5,1911399,w0,w1] [10,129,2072,2713]) [7,73797,w2,w5,1911399,w0,w1,6551005] [906,1544,3464] e) [7,73797,w2,w5,1985195,w0,w1] [10,129,1384,2961] (n (s [7,73797,w2,w5,1985195,w0,w1,6551005] [3784]) [7,73797,w2,w5,2067250,w0,w1,6551005] [906,1546] e)) [7,73797,w2,w5,2098204,w0,w1,6551005] [] (n (n (s [7,73797,w2,w5,w0,2174077,w1,6551005] [906]) [7,73797,w2,w5,w0,2329918,w1,6551005] [906] e) [7,73797,w2,w5,w0,2698365,w1,6551005] [906] (n (s [7,73797,w2,w5,w0,3296445,w1,6551005] []) [7,73797,w2,w5,w0,3935806,w1,6551005] [] e))))) [7,73797,w2,w5,w0,4190271,w1,6551005] [] (n (n (n (n (n (s [7,73797,w2,w5,w0,4190271,6551005] [8]) [7,73797,w2,w5,w0,w1,6295548,6551005] [] (s [7,73797,w2,w5,w0,w1,6551005] [8,97])) [7,73797,w2,w5,w0,w1,6551005,6551005] [] (n (s [7,73797,w2,w5,w0,w1,6551005,6553055] []) [7,73797,w2,w5,w0,w1,6551005,6553085] [] e)) [7,73797,w2,w5,w0,w1,6551005,7077341] [] (n (n (s [7,73797,w2,w5,w0,w1,6551005,7190390] []) [7,73797,w2,w5,w0,w1,6551005,7601629] [3016] e) [7,73797,w2,w5,w0,w1,6551005,7788474] [906,2696] (n (s [7,73797,w2,w5,w0,w1,6551005,8156909] [906]) [7,73797,w2,w5,w0,w1,6551005,8314810] [906,2696] e))) [7,73797,w2,w5,w0,w1,6551005,8388607] [] (n (n (n (s [7,73797,w2,w5,w0,w1,7077341] [8,97]) [7,73797,w2,w5,w0,w1,7601629] [8,97,166] e) [7,73797,w2,1296795,w3,w0,w1] [8,129,1556,2833] (n (s [7,73797,w2,1296795,w3,w0,w1,6551005] [1544]) [7,73797,w2,1296795,w0,w1,6551005] [8,97,2193] e)) [7,73797,w2,w3,1985195,w0,w1] [12,129,1172,1378,2961] (n (n (s [7,73797,w2,w3,1985195,w0,w1,6551005] []) [7,73797,w2,w3,w0,w1,6551005,7190390] [] e) [7,73797,w2,w3,w0,w1,7190390] [4,97,1172,2898,3030] (n (s [7,73797,w2,1985195,w0,w1,6551005] [8,97,3048,3233]) [7,73797,w2,w0,w1,6551005,7190390] [65] e)))) [7,73797,239959,w4,w5,w3,w0,w1] [900,1156,2050] (n (n (n (n (s [7,73797,239959,w4,w5,w0,w1,6551005] [898,1154,3458]) [7,73797,239959,w5,w3,w0,w1] [14,129,1244,1564,2078,2719] e) [7,73797,239959,w5,w3,w0,w1,6551005] [1546] (n (s [7,73797,239959,w5,w0,w1,6551005] [10,97,1562,2075]) [7,73797,w4,764247,w5,w3,w0,w1] [900,1156,2050] e)) [7,73797,w4,764247,w5,w0,w1,6551005] [898,1154,3458] (n (n (s [7,73797,w4,w5,1296795,w3,w0,w1] [908,1548,2054]) [7,73797,w4,w5,1296795,w0,w1,6551005] [906,1546,3466] e) [7,73797,w4,w5,w3,w0,w1,8156909] [900,1542,3460] (n (s [7,73797,w4,w5,w0,w1,6551005,8156909] [898,2690,3458]) [7,73797,w5,1296795,w3,w0,w1] [14,129,1564,2833] e))) [7,73797,w5,1296795,w3,w0,w1,6551005] [1546] (n (n (n (s [7,73797,w5,1296795,w0,w1,6551005] [10,97,2193]) [7,73797,w5,w3,w0,w1,6551005,8156909] [1166] e) [7,73797,w5,w3,w0,w1,8156909] [12,97,1180,2772,2908] (n (s [7,73797,w5,w0,w1,6551005,8156909] [14,65]) [7,75845,w2,w4,w5,w3,w0,w1] [900] e)) [7,75845,w2,w4,w5,w0,w1,6551005] [898] (n (n (s [7,75845,w2,w4,w5,w0,w1,7601629] [898,1160,3464]) [7,75845,w2,w5,w3,w0,w1] [14,129,1566] e) [7,75845,w2,w5,w3,w0,w1,6551005] [1544,3784] (n (s [7,75845,w2,w5,w3,w0,w1,6553055] []) [7,75845,w2,w5,w3,w0,w1,6553085] [1544] e))))))
def T_86 : BT := (n (n (n (n (n (n (s [7,75845,w2,w5,w0,w1,6551005] [8,97,3032]) [7,75845,w2,w5,w0,w1,6551005,6553055] [] (s [7,75845,w2,w5,w0,w1,6551005,6553085] [])) [7,75845,w2,w5,w0,w1,6551005,7601629] [3016] (n (s [7,75845,w2,w5,w0,w1,7601629] [8,97,166]) [7,198656,w2,w4,w5,w3,w0,4190271] [1162,1538] e)) [7,198656,w2,w4,w5,w3,w0,w1] [1162,1538,2689] (n (n (s [7,198656,w2,w4,w5,w3,w0,4394944] [1162,1538]) [7,198656,w2,w4,w5,1911399,w0,w1] [1160,2689] e) [7,198656,w2,w4,w5,2034210,w0,w1] [1160,2689] (n (s [7,198656,w2,w4,w5,2058991,w0,w1] [1160,2689]) [7,198656,w2,w4,w5,w0,w1,6551005] [1160,2049] e))) [7,198656,w2,w4,1263753,w3,w0,w1] [898,1538,2691,3458] (n (n (n (s [7,198656,w2,w4,1296795,w3,w0,w1] [898,1538]) [7,198656,w2,w4,w3,1985195,w0,w1] [902,2054,2695,3462] e) [7,198656,w2,w4,w3,w0,w1,7190390] [898,1538,2051,2690,3458] (n (s [7,198656,w4,764247,w5,w3,w0,w1] [1156,2050]) [7,198656,w4,w5,1829343,w3,w0,w1] [1540,2054] e)) [7,198656,w4,w5,w3,w0,w1,8156909] [908,1156,1542,2053,2692,3460] (n (n (s [7,198656,w4,1296795,1796301,w3,w0,w1] [2054]) [7,198658,w2,w4,w5,w3,w0,w1] [1162,1288,1538,2689] e) [7,198658,w2,w4,w5,1911399,w0,w1] [2689] (n (s [7,198658,w2,w4,w5,2058991,w0,w1] [2689]) [7,198658,w2,w4,w3,1985195,w0,w1] [902,2054,2695,3462] e)))) [7,198668,w2,w4,w5,w3,w0,w1] [900,1162,1538,2689] (n (n (n (n (s [7,198672,w2,w4,w5,w3,w0,w1] [1162,1538,2689]) [7,221389,w2,w4,w5,w3,w0,w1] [900,1608,2312] e) [7,221389,w2,w4,w5,w0,w1,6551005] [898,1608] (n (s [7,229378,w2,w4,w5,w3,w0,w1] [1162,1288,1538]) [7,229392,w2,w4,w5,w3,w0,w1] [1162,1538] e)) [7,229394,w2,w4,w5,w3,w0,4190271] [1162,1288,1538] (n (n (s [7,229394,w2,w4,w5,w3,w0,4192575] [1162,1538]) [7,229394,w2,w4,w5,w3,w0,w1] [1162,1288,1538] e) [7,229394,w2,w4,w5,w3,w0,4427730] [1162,1288,1538] (n (s [7,229394,w2,w4,w5,w3,4190271,6288323] [1162,1288,1538]) [7,229394,w2,w4,w5,w3,w1,6288323] [897,1162,1288,1538] e))) [7,229394,w2,w4,w5,1911399,w0,4190271] [] (n (n (n (s [7,229394,w2,w4,w5,1911399,w0,w1] []) [7,229394,w2,w4,w5,w0,4190271,6551005] [1160,1288] e) [7,229394,w2,w4,w5,w0,w1,6551005] [1160,1288] (n (s [7,229394,w2,w4,1296539,w3,w0,4190271] [898,1288,1538,3458]) [7,229394,w2,w4,1296539,w3,w0,w1] [898,1288,1538,3458] e)) [7,229394,w2,w4,1296795,w3,w0,4190271] [898,1538,3458] (n (n (s [7,229394,w2,w4,1296795,w3,w0,w1] [898,1538]) [7,229394,w2,w4,w3,1985195,w0,4190271] [902,2054,3462] e) [7,229394,w2,w4,w3,1985195,w0,w1] [902,2054] (n (s [7,229394,w2,w4,w3,w0,4190271,7190390] [898,2690,3458]) [7,229394,w2,w4,w3,w0,w1,7190390] [898,3458] e))))) [7,229394,w4,764247,w5,w3,w0,4190271] [1156,1288,3460] (n (n (n (n (n (s [7,229394,w4,764247,w5,w3,w0,w1] [1156,1288]) [7,229394,w4,w5,w3,2067250,w0,4190271] [1602,2184] (s [7,229394,w4,w5,w3,2067250,w0,w1] [1602,2184])) [7,229394,w4,w5,w3,w0,2329918,4190271] [908,1156] (n (s [7,229394,w4,w5,w3,w0,2329918,w1] [908,1156]) [7,229394,w4,w5,w3,w0,4190271,4192575] [] e)) [7,229394,w4,w5,w3,w0,4190271,8156909] [908,1156,2692] (n (n (s [7,229394,w4,w5,w3,w0,4192575,w1] []) [7,229394,w4,w5,w3,w0,w1,8156909] [908,1156] e) [7,229394,w4,w5,w3,w0,w1,8386303] [] (n (s [7,229394,w4,1296795,w3,w0,4190271] [4,40,1688,2070]) [7,229394,w4,1296795,w3,w0,4190271,w1] [3462] e))) [7,229394,w4,1296795,w3,w0,w1] [5,40,1688,2070,2711] (n (n (n (s [7,229648,w2,w4,w5,w3,w0,4190271] [1162,1538]) [7,229648,w2,w4,w5,w3,w0,w1] [1162,1538] e) [7,229648,w2,w4,w5,1911399,w0,w1] [1160] (n (s [7,229648,w2,w4,w5,2067250,w0,w1] [1160]) [7,229648,w2,w4,w5,w0,4190271,6551005] [1160] e)) [7,229648,w2,w4,w5,w0,w1,6551005] [1160] (n (n (s [7,229648,w2,w4,w5,w0,w1,6553055] [1160]) [7,229648,w2,w4,w5,w0,w1,7077341] [1160,1288] e) [7,229648,w2,w4,1296793,w3,w0,w1] [898,1538] (n (s [7,229648,w2,w4,1296793,w0,w1,6551005] []) [7,229648,w2,w4,1296795,w3,w0,w1] [898,1538] e)))) [7,229648,w2,w4,1296795,w0,w1,6551005] [] (n (n (n (n (s [7,229648,w2,w4,w3,1985195,w0,w1] [902,2050]) [7,229648,w2,w4,w3,w0,w1,7190390] [898,3458] e) [7,229648,w2,w4,1985195,w0,w1,6551005] [1538] (n (s [7,229648,w2,w4,w0,w1,6551005,7190390] []) [7,229648,w4,764247,w5,w3,w0,w1] [1156] e)) [7,229648,w4,764247,w5,w0,w1,6551005] [1154,3458,3592] (n (n (s [7,229648,w4,w5,w3,w0,2329918,w1] [908,1156]) [7,229648,w4,w5,w3,w0,w1,6553055] [] e) [7,229648,w4,w5,w3,w0,w1,8156909] [908,1156] (n (s [7,229648,w4,w5,w3,w0,w1,8386557] [1538]) [7,229648,w4,w5,w0,2329918,w1,6551005] [906,1154] e))) [7,229648,w4,w5,w0,w1,6551005,6553055] [] (n (n (n (s [7,229648,w4,w5,w0,w1,6551005,8156909] [906,1154,2690]) [7,229650,w2,w4,w5,w3,w0,w1] [1162,1288,1538] e) [7,229650,w4,w5,w3,w0,w1] [4,40,129,916,936,1180,1688,1832] (n (s [7,229650,w4,w5,w3,w0,w1,7337983] [3784,3910,4161]) [7,229650,w4,w5,w3,w0,w1,8385535] [3784] e)) [7,229650,w4,w5,w3,w0,w1,8386047] [3784] (n (n (s [7,229650,w4,w5,w3,w0,w1,8386431] []) [7,229650,w4,w5,w3,w0,w1,8386558] [4161] e) [7,231442,w2,w4,w5,w3,w0,4190271] [1162,1288,1538] (n (s [7,231442,w2,w4,w5,w3,w0,w1] [1162,1288,1538]) [7,231696,w2,w4,w5,w3,w0,w1] [1162,1538] e))))))
def N_87 : BT := n T_85 [7,75845,w2,w5,w3,w0,w1,7601629] [] T_86
def T_88 : BT := (n (n (n (n (n (n (s [7,231696,w2,w4,w5,w0,w1,7077341] [1160,1288]) [7,w2,w2,w4,w5,w3,w0,4190271] [1162,1538] (s [7,w2,w2,w4,w5,w3,w0,w1] [1162,1538])) [7,w2,w2,w4,w5,w3,w0,4198338] [770,834,1162,1538] (n (s [7,w2,w2,w4,w5,w3,w0,4198352] [770,834,1162,1538,2691]) [7,w2,w2,w4,w5,w3,w0,4263872] [1538] e)) [7,w2,w2,w4,w5,1837618,w0,w1] [1162,1538] (n (n (s [7,w2,w2,w4,w5,1903138,w0,w1] [1538]) [7,w2,w2,w4,w5,1911399,w0,w1] [] e) [7,w2,w2,w4,w5,w0,w1,6551005] [1160] (n (s [7,w2,w2,w4,1198219,w3,w0,w1] [770,834,1160,1538]) [7,w2,w2,w4,1198233,w3,w0,w1] [770,834,1160,1538] e))) [7,w2,w2,w4,1263753,w3,w0,w1] [770,834,1160,1538] (n (n (n (s [7,w2,w2,w4,1296795,w3,w0,4190271] [770,834,1538]) [7,w2,w2,w4,1296795,w3,w0,w1] [770,834,1538] e) [7,w2,w2,w4,1296795,1911399,w0,w1] [] (n (s [7,w2,w2,w4,1296795,w0,w1,6551005] []) [7,w2,w2,w4,w3,1985195,w0,w1] [774,838,2050] e)) [7,w2,w2,w4,w3,2083771,w0,w1] [770,834,2050] (n (n (s [7,w2,w2,w4,w3,w0,w1,7091812] [774,838,3458]) [7,w2,w2,w4,w3,w0,w1,7190390] [770,834,3458] e) [7,w2,w2,w4,w3,w0,w1,7323510] [770,834,3458] (n (s [7,w2,w2,764247,1296795,w3,w0,w1] []) [7,w2,w2,764247,w3,1985195,w0,w1] [] e)))) [7,w2,w2,764247,w3,w0,w1,7190390] [] (n (n (n (n (s [7,w2,231699,w4,w5,w3,w0,4190271] [900,1290,1666]) [7,w2,231699,w4,w5,w3,w0,w1] [900,1290,1666] e) [7,w2,231699,w4,w5,w3,w0,w1,6295548] [] (n (s [7,w2,231699,w4,w5,w3,w0,4198337] [900,1166,1290,1542,1666]) [7,w2,231699,w4,w5,1837603,w0,w1] [898,1162,1290,1538,1666] e)) [7,w2,231699,w4,w5,1911399,w0,w1] [898] (n (n (s [7,w2,231699,w4,w5,w0,w1,6551005] [898,1288]) [7,w2,231699,w4,1296795,w3,w0,w1] [962,1666] e) [7,w2,231699,w4,1796301,w3,w0,w1] [] (n (s [7,w2,231699,w4,w3,1985195,w0,w1] [902,966,1602,2178]) [7,w2,231699,w4,w3,w0,w1,7190390] [902,962,3462] e))) [7,w2,231699,764247,1296795,w3,w0,w1] [] (n (n (n (s [7,w2,231699,1796301,w3,w0,w1] [4,36,129,1556,2068,2709,2833]) [7,w2,231702,w4,w5,w3,w0,4190271] [900,1166,1290,1542,1666] e) [7,w2,231702,w4,w5,w3,w0,w1] [900,1166,1290,1542,1666] (n (s [7,w2,231702,w4,w5,w3,w0,4198340] [900,1166,1290,1542,1666]) [7,w2,231702,w4,w5,w3,2698365,w1] [1542,1666] e)) [7,w2,231702,w4,w5,w3,w1,6288323] [900,961,1166,1291,1542,1666] (n (n (s [7,w2,231702,w4,w5,1837606,w0,w1] [898,1162,1290,1538,1666]) [7,w2,231702,w4,w5,1911399,w0,w1] [898,1538,1666] e) [7,w2,231702,w4,w5,1985195,w0,w1] [898,968,1162,1288] (n (s [7,w2,231702,w4,w5,w0,w1,6551005] [898,1162,1288,1538]) [7,w2,231702,w4,1198221,w3,w0,w1] [900,962,1164,1288,1542,1666] e))))) [7,w2,231702,w4,1296795,w3,w0,w1] [902,962,1156,1542,1666] (n (n (n (n (n (s [7,w2,231702,w4,1296799,w3,w0,w1] [902,962,1156,1542,1666]) [7,w2,231702,w4,w3,1985195,w0,w1] [902,966,1164,2054,2178] (s [7,w2,231702,w4,w3,w0,w1,7190390] [902,962,1156,3462,3586])) [7,w2,231702,764247,w5,w3,w0,w1] [910,970,1166,1290,1540] (n (s [7,w2,231702,w5,w3,1911399,w0,w1] [910,974,1156,1284,2062,2186]) [7,w2,231702,w5,w3,w0,2698365,w1] [910,1156,1288,2702] e)) [7,w2,231702,w5,w3,w0,w1,7788474] [910,970,1156,1288,3470] (n (n (s [7,w2,231703,w4,w5,w3,w0,w1] [900,1290,1666]) [7,w2,231710,w4,w5,w3,w0,w1] [900,1166,1290,1542,1666] e) [7,w2,231730,w4,w5,w3,w0,4190271] [900,1166,1290,1542,1666] (n (s [7,w2,231730,w4,w5,w3,w0,w1] [900,1166,1290,1542,1666]) [7,w2,231730,w4,w5,w3,w0,4198368] [900,966,1166,1290,1542,1666] e))) [7,w2,231730,w4,w5,w3,3935806,w1] [900,1166,1542,2050] (n (n (n (s [7,w2,231730,w4,w5,w3,w1,6288323] [900,961,1166,1290,1542,1666]) [7,w2,231730,w4,w5,1911399,w0,w1] [898,1538,1666] e) [7,w2,231730,w4,w5,w0,3935806,w1] [898,1162,1288,1538,2050] (n (s [7,w2,231730,w4,w5,w0,w1,6551005] [898,1162,1288,1538]) [7,w2,231730,w4,1198249,w3,w0,w1] [902,966,1164,1292,1542,1666] e)) [7,w2,231730,w4,1296795,w3,w0,w1] [902,962,1156,1288,1542,1666] (n (n (s [7,w2,231730,w4,1296827,w3,w0,w1] [902,962,1156,1542,1666]) [7,w2,231730,w4,w3,1985195,w0,w1] [902,966,1164,1292,2054,2178] e) [7,w2,231730,w4,w3,w0,w1,7190390] [902,962,1156,3462,3586] (n (s [7,w2,231734,w4,w5,w3,w0,w1] [900,1166,1290,1542,1666]) [7,w2,231734,w4,w5,1911399,w0,w1] [898,1538,1666] e)))) [7,w2,231734,w5,w3,1911399,w0,w1] [910,974,1156,1284,2062,2186] (n (n (n (n (s [7,w2,231766,w4,w5,w3,w0,w1] [900,1166,1290,1542,1666]) [7,w2,231766,w4,w5,w3,w0,w1,6295548] [] e) [7,w2,232242,w4,w5,w3,w0,w1] [900,1166,1290,1542,1666,2114,2246] (n (s [7,w2,232722,w4,w5,w3,w0,4190271] [900,1166,1290,1542,1666]) [7,w2,232722,w4,w5,w3,w0,w1] [900,1166,1290,1542,1666] e)) [7,w2,232722,w4,w5,w3,w0,6295548] [900,1166,1290,1542,1666,2692,2754,2882] (n (n (s [7,w2,232722,w4,w5,w3,6295548] [4,36,72,900,916,1166,1172,1192,1234,1290,1320,1542,1564,1626,1666,1688,2068,2134,2194,2328,2472,2708,2770,2898]) [7,w2,232722,w4,w5,1838626,w0,w1] [898,1162,1290,1538,1666] e) [7,w2,232722,w4,w5,1911399,w0,w1] [898,1538,1666] (n (s [7,w2,232722,w4,w5,w0,w1,6551005] [898,1162,1288,1538]) [7,w2,232722,w4,1199241,w3,w0,w1] [900,962,1164,1288,1542,1666] e))) [7,w2,232722,w4,1296795,w3,w0,w1] [902,962,1156,1288,1542,1666] (n (n (n (s [7,w2,232722,w4,1297819,w3,w0,w1] [902,962,1156,1542,1666]) [7,w2,232722,w4,w3,1985195,w0,w1] [902,966,1164,1292,2054,2178] e) [7,w2,232722,w4,w3,w0,w1,7190390] [902,962,1156,3462,3586] (n (s [7,w2,232726,w4,w5,w3,w0,w1] [900,1166,1290,1542,1666]) [7,w2,232754,w4,w5,w3,w0,w1] [900,1166,1290,1542,1666] e)) [7,w2,237909,w4,w5,w3,w0,w1] [900,1290] (n (n (s [7,w2,237909,w4,w5,w0,w1,6551005] [898,1288]) [7,w2,237909,764247,w5,w3,w0,w1] [1290] e) [7,w2,237909,764247,w5,w0,w1,6551005] [1288,3592] (n (s [7,w2,237909,w5,w3,w0,w1] [14,46,129,1690,2078,2719]) [7,w2,237909,w5,w3,w0,w1,6551005] [1674,3784] e))))))
def T_89 : BT := (n (n (n (n (n (n (s [7,w2,239959,w4,w5,w3,w0,w1] [900,1290]) [7,w2,239959,w4,w5,w0,w1,6551005] [898,1288] (s [7,w2,239959,w5,w3,w0,w1] [14,46,129,1242,1566,1690,2078,2719])) [7,w2,239959,w5,w3,w0,w1,6551005] [1546,1674,3784] (n (s [7,w2,239959,w5,w0,w1,6551005] [10,40,97,1242,1562,2075,3032]) [7,w2,258049,w4,w5,w3,w0,w1] [900,2312] e)) [7,w2,w4,657408,w5,w3,w0,w1] [908,1156,1290,1798,2312,2945] (n (n (s [7,w2,w4,657411,w5,w3,w0,w1] [1156,1290,1540,1798,2050,2184,2312,2945]) [7,w2,w4,657411,w5,1985195,w0,w1] [1154,1288,1864,2062,2184,2312,2953,3720] e) [7,w2,w4,731205,w5,w3,w0,4190271] [1156,1290,2184] (n (s [7,w2,w4,731205,w5,w3,w0,w1] [1156,1290,2184]) [7,w2,w4,731205,w5,w3,w0,4329408] [908,1156,1290,1352,2184] e))) [7,w2,w4,731205,w5,1911399,w0,w1] [906,1154,1288,2184] (n (n (n (s [7,w2,w4,731205,w5,1968674,w0,w1] [910,1166,1288,1352,2184]) [7,w2,w4,731205,w5,1985195,w0,w1] [1154,1288,1352,1864,2184] e) [7,w2,w4,731205,w5,2042471,w0,w1] [1154,1288,2184] (n (s [7,w2,w4,731205,w5,w0,w1,6551005] [1154,1288,3592]) [7,w2,w4,731205,1296795,w3,w0,w1] [1346] e)) [7,w2,w4,731205,w3,1985195,w0,w1] [1156,1350,1734] (n (n (s [7,w2,w4,731205,w3,w0,w1,7190390] [1158,1346,1794]) [7,w2,w4,731207,w5,w3,w0,w1] [1156,1290,2050] e) [7,w2,w4,731207,w5,1985195,w0,w1] [1154,1288,1352,1864,2050] (n (s [7,w2,w4,731207,w3,1985195,w0,w1] [1156,1350,1862]) [7,w2,w4,731213,w5,w3,w0,w1] [1156,1290,2184] e)))) [7,w2,w4,731221,w5,w3,w0,w1] [1156,1290,2184] (n (n (n (n (s [7,w2,w4,747725,w5,w3,w0,w1] [1156,1864,2184]) [7,w2,w4,747725,w5,w0,w1,6551005] [1154,1864] e) [7,w2,w4,761879,w5,w3,w0,4190271] [1156,1290] (n (s [7,w2,w4,761879,w5,w3,w0,w1] [1156,1290]) [7,w2,w4,763991,w5,w3,w0,4190271] [1156,1290] e)) [7,w2,w4,763991,w5,w3,w0,w1] [1156,1290] (n (n (s [7,w2,w4,764245,w5,w3,w0,w1] [1156,1290,2184]) [7,w2,w4,764245,w5,w0,w1,6551005] [1154,1288,3592] e) [7,w2,w4,764247,w5,w3,1985195,w0,w1] [1540,2184] (n (s [7,w2,w4,764247,w5,w3,2058991,w0,w1] []) [7,w2,w4,764247,w5,w3,2092031,w0,w1] [] e))) [7,w2,w4,764247,w5,w3,w0,4190271] [1156,1290] (n (n (n (s [7,w2,w4,764247,w5,w3,w0,w1] [1156,1290]) [7,w2,w4,764247,w5,w3,w0,w1,6295548] [] e) [7,w2,w4,764247,w5,w3,w0,4198337] [1156,1290,1542,1794] (n (s [7,w2,w4,764247,w5,w3,w0,4198340] [1156,1290]) [7,w2,w4,764247,w5,w3,w0,4198344] [1156,1224,1290,1352] e)) [7,w2,w4,764247,w5,w3,w0,4198356] [1156,1290,2693,2827,2945] (n (n (s [7,w2,w4,764247,w5,w3,w0,4263872] [1542,2184]) [7,w2,w4,764247,w5,w3,w0,4329408] [1156,1224,1290,1352] e) [7,w2,w4,764247,w5,w3,w0,4329409] [1156,1224,1290,1352] (n (s [7,w2,w4,764247,w5,w3,w0,5246912] [1156,1228,1290,1356]) [7,w2,w4,764247,w5,w3,4190271,6288323] [1156,1290] e))))) [7,w2,w4,764247,w5,1837603,w0,w1] [1158,1290,1542] (n (n (n (n (n (s [7,w2,w4,764247,w5,1837606,w0,w1] [1158,1290]) [7,w2,w4,764247,w5,1837610,w0,w1] [1166,1224,1290,1352] (s [7,w2,w4,764247,w5,1837618,w0,w1] [1158,1290])) [7,w2,w4,764247,w5,1837622,w0,w1] [1158,1290,2694] (n (s [7,w2,w4,764247,w5,1838626,w0,w1] [1158,1290]) [7,w2,w4,764247,w5,1903138,w0,w1] [1158,1542] e)) [7,w2,w4,764247,w5,1911399,1985195,w0,w1] [1288,1538,2184] (n (n (s [7,w2,w4,764247,w5,1911399,w0,4190271] [1154]) [7,w2,w4,764247,w5,1911399,w0,w1] [1154] e) [7,w2,w4,764247,w5,1968674,w0,w1] [1166,1224,1290,1352] (n (s [7,w2,w4,764247,w5,1968675,w0,w1] [1166,1224,1290,1352]) [7,w2,w4,764247,w5,1985195,w0,3935806,w1] [1538,2691] e))) [7,w2,w4,764247,w5,1985195,w0,4190271] [1154,1224,1288,1352,1864] (n (n (n (s [7,w2,w4,764247,w5,1985195,w0,w1] [1154,1224,1288,1352,1864]) [7,w2,w4,764247,w5,2058991,w0,w1] [1154,1864] e) [7,w2,w4,764247,w5,w0,4190271,6551005] [1154,1288,3592] (n (s [7,w2,w4,764247,w5,w0,w1,6403412] [1154,1288,1864,3592]) [7,w2,w4,764247,w5,w0,w1,6477208] [1154,1224,1352,3592] e)) [7,w2,w4,764247,w5,w0,w1,6551005] [1154,1288,3592] (n (n (s [7,w2,w4,764247,w5,w0,w1,7077341] [1154,1288,3592]) [7,w2,w4,764247,w5,w0,w1,7601629] [1154,1224,1288,1352,3592] e) [7,w2,w4,764247,1296795,1911399,w0,w1] [] (n (s [7,w2,w4,764247,1296795,w0,w1,6551005] []) [7,w2,w4,764247,1985195,w0,3296445,w1] [1154,2051,2177,2305,3016] e)))) [7,w2,w4,764247,1985195,w0,w1,6551005] [1154] (n (n (n (n (s [7,w2,w4,764247,w0,w1,6551005,7190390] [1154,3458]) [7,w2,w4,764255,w5,w3,w0,w1] [1156,1290] e) [7,w2,w4,765271,w5,w3,w0,w1] [1156,1290] (n (s [7,w2,w4,1116163,1296795,1911399,w0,w1] [1218,2945]) [7,w2,w4,w5,1648709,1911399,w0,w1] [910,1542] e)) [7,w2,w4,w5,1648709,1985195,w0,w1] [910,1550,1736] (n (n (s [7,w2,w4,w5,1648709,w0,w1,6551005] [910,1538,1672,3592]) [7,w2,w4,w5,1771520,w3,w0,w1] [908,1156,1540,1674,1794,2184,3073] e) [7,w2,w4,w5,1779781,w3,w0,w1] [1540,1674] (n (s [7,w2,w4,w5,1794061,w3,w0,4190271] [1540]) [7,w2,w4,w5,1794061,w3,w0,w1] [1540] e))) [7,w2,w4,w5,1796173,w3,w0,4190271] [1540] (n (n (n (s [7,w2,w4,w5,1796173,w3,w0,w1] [1540]) [7,w2,w4,w5,1796301,w3,2067250,w0,w1] [] e) [7,w2,w4,w5,1796301,w3,2075511,w0,w1] [] (n (s [7,w2,w4,w5,1796301,w3,2092031,w0,w1] []) [7,w2,w4,w5,1796301,w3,w0,4190271] [1540] e)) [7,w2,w4,w5,1796301,w3,w0,w1] [1540] (n (n (s [7,w2,w4,w5,1796301,w3,w0,w1,6592306] [1540]) [7,w2,w4,w5,1796301,w3,w0,w1,6594366] [1540,2827,2947] e) [7,w2,w4,w5,1796301,w3,w0,4198337] [908,1156,1540,1674,1794,2184] (n (s [7,w2,w4,w5,1796301,w3,w0,4198338] [1540,1730,1858,2050]) [7,w2,w4,w5,1796301,w3,w0,4198340] [1540,2827] e))))))
def N_90 : BT := n T_88 [7,w2,237909,w5,w0,w1,6551005] [10,40,97,1562,2075,3032] T_89
def N_91 : BT := n N_87 [7,231696,w2,w4,w5,w0,w1,6551005] [1160] N_90
def N_92 : BT := n N_84 [7,73797,w2,w4,w3,1985195,w0,w1] [902,1158] N_91
def N_93 : BT := n N_77 [7,2068,w2,764247,w5,w3,w0,4190271] [910,1162,1544,2058,2698,3466] N_92
def T_94 : BT := (n (n (n (n (n (n (s [7,w2,w4,w5,1796301,w3,w0,4198352] [1540,1730,1858]) [7,w2,w4,w5,1796301,w3,w0,4263872] [1156] (s [7,w2,w4,w5,1796301,w3,w0,4394944] [])) [7,w2,w4,w5,1796301,w3,w0,4427730,6033378] [1540,2050] (n (s [7,w2,w4,w5,1796301,w3,w0,4427730,6295548] [1540,2692]) [7,w2,w4,w5,1796301,w3,4190271,6288323] [1540] e)) [7,w2,w4,w5,1796301,1837603,w0,w1] [910,1158,1542] (n (n (s [7,w2,w4,w5,1796301,1837606,w0,w1] [1542]) [7,w2,w4,w5,1796301,1837614,w0,w1] [1542] e) [7,w2,w4,w5,1796301,1837618,w0,w1] [1542] (n (s [7,w2,w4,w5,1796301,1838626,w0,w1] [1542]) [7,w2,w4,w5,1796301,1903138,w0,w1] [1158,1542] e))) [7,w2,w4,w5,1796301,1911399,w0,4190271] [906,1542] (n (n (n (s [7,w2,w4,w5,1796301,1911399,w0,w1] [906,1542]) [7,w2,w4,w5,1796301,1911399,w0,w1,6592306] [906,1542] e) [7,w2,w4,w5,1796301,2034210,w0,w1] [910,1158,1542] (n (s [7,w2,w4,w5,1796301,2058991,w0,4190271] [1538]) [7,w2,w4,w5,1796301,2058991,w0,w1] [1538] e)) [7,w2,w4,w5,1796301,2058991,w0,w1,6592306] [1538] (n (n (s [7,w2,w4,w5,1796301,2067250,w0,3935806,w1] [2691]) [7,w2,w4,w5,1796301,w0,3935806,w1,6033378] [] e) [7,w2,w4,w5,1796301,w0,4190271,6551005] [1538] (n (s [7,w2,w4,w5,1796301,w0,w1,6329616] [1538,3592]) [7,w2,w4,w5,1796301,w0,w1,6403412] [1154,1538,3592] e)))) [7,w2,w4,w5,1796301,w0,w1,6551005] [1538] (n (n (n (n (s [7,w2,w4,w5,1796301,w0,w1,7077341] [1538]) [7,w2,w4,w5,1796301,w0,w1,8125917] [1538] (s [7,w2,w4,w5,1796303,w3,w0,w1] [1540,2050])) [7,w2,w4,w5,1796317,w3,w0,w1] [1540] (n (s [7,w2,w4,w5,1797325,w3,w0,w1] [1540]) [7,w2,w4,w5,1812823,w3,w0,w1] [1540,1674] e)) [7,w2,w4,w5,1829343,w3,2058991,w0,w1] [] (n (n (s [7,w2,w4,w5,1829343,w3,2075511,w0,w1] []) [7,w2,w4,w5,1829343,w3,2092031,w0,w1] [] e) [7,w2,w4,w5,1829343,w3,w0,3935806,w1] [2693] (n (s [7,w2,w4,w5,1829343,w3,w0,4190271] [1540]) [7,w2,w4,w5,1829343,w3,w0,w1] [1540] e))) [7,w2,w4,w5,1829343,w3,w0,w1,6295548] [2693,3460] (n (n (n (s [7,w2,w4,w5,1829343,w3,w0,w1,6559264] []) [7,w2,w4,w5,1829343,w3,w0,w1,6592306] [1540,4934] e) [7,w2,w4,w5,1829343,1911399,w0,w1] [1542] (n (s [7,w2,w4,w5,1829343,2058991,w0,w1] [1538]) [7,w2,w4,w5,1829343,w0,w1,6551005] [1538] e)) [7,w2,w4,w5,w3,2092031,w0,w1] [1602,2708,2842,2962,3477,3611,3731,3857] (n (n (s [7,w2,w4,w5,w3,2093059,w0,4190271] []) [7,w2,w4,w5,w3,2093059,w0,w1] [] e) [7,w2,w4,w5,w3,2093059,w0,4427730] [910,1158,2692,4162] (n (s [7,w2,w4,w5,w3,2093059,w0,6291395] []) [7,w2,w4,w5,w3,2093059,4190271,6288323] [] e))))) [7,w2,w4,w5,w3,2095175,w0,w1] [] (n (n (n (n (n (s [7,w2,w4,w5,w3,2097180,w0,w1] []) [7,w2,w4,w5,w3,2097212,w0,4190271] [] (s [7,w2,w4,w5,w3,2097212,w0,4193343] [])) [7,w2,w4,w5,w3,2097212,w0,w1] [] (n (s [7,w2,w4,w5,w3,2097212,w0,6295548] []) [7,w2,w4,w5,w3,2097212,2329918,4190271] [910,1158] e)) [7,w2,w4,w5,w3,2097212,2329918,w1] [910,1158] (n (n (s [7,w2,w4,w5,w3,2097212,4190271,4193343] []) [7,w2,w4,w5,w3,2097212,4190271,6288323] [] e) [7,w2,w4,w5,w3,2097212,4193343,w1] [] (n (s [7,w2,w4,w5,w3,2097212,w1,6288323] []) [7,w2,w4,w5,w3,2097212,w1,8385535] [] e))) [7,w2,w4,w5,w3,2098188,w0,w1] [] (n (n (n (s [7,w2,w4,w5,w3,2098196,w0,w1] []) [7,w2,w4,w5,w3,2098204,w0,4190271] [] e) [7,w2,w4,w5,w3,2098204,w0,w1] [] (n (s [7,w2,w4,w5,w3,2098204,2329918,w1] [908,1156]) [7,w2,w4,w5,w3,2098204,2698365,w1] [908] e)) [7,w2,w4,w5,w3,2098204,w1,6288323] [] (n (n (s [7,w2,w4,w5,w3,2098204,w1,6295548] []) [7,w2,w4,w5,w3,2098204,w1,6553085] [] e) [7,w2,w4,w5,w3,2098204,w1,8386527] [] (n (s [7,w2,w4,w5,w3,2098236,w0,w1] []) [7,w2,w4,w5,w3,2098236,w1] [4,42,66,129,916,938,1180,1186,1694,1814,1832] e)))) [7,w2,w4,w5,w3,2098236,w1,7337983] [3650,3784,3910] (n (n (n (n (s [7,w2,w4,w5,w3,2098236,w1,8386047] [3650,3786]) [7,w2,w4,w5,w3,2098236,w1,8386557] [1538,3650,3786] e) [7,w2,w4,w5,w3,2099260,w0,4190271] [] (n (s [7,w2,w4,w5,w3,2099260,w0,w1] []) [7,w2,w4,w5,w3,2100252,w0,w1] [] e)) [7,w2,w4,w5,w3,w0,w0,4190271] [] (n (n (s [7,w2,w4,w5,w3,w0,w0,w1] []) [7,w2,w4,w5,w3,w0,w0,4198340] [2186] e) [7,w2,w4,w5,w3,w0,2100285,4190271] [] (n (s [7,w2,w4,w5,w3,w0,2100285,w1] [3201]) [7,w2,w4,w5,w3,w0,2100285,w1,4427730] [908,1156,2053] e))) [7,w2,w4,w5,w3,w0,2100285,4198337] [] (n (n (n (s [7,w2,w4,w5,w3,w0,2100348,4190271] []) [7,w2,w4,w5,w3,w0,2100348,w1] [3201] e) [7,w2,w4,w5,w3,w0,2100348,4796357] [2186] (n (s [7,w2,w4,w5,w3,w0,2100349,w1] [3201]) [7,w2,w4,w5,w3,w0,2100476,w1] [3201] e)) [7,w2,w4,w5,w3,w0,2100604,w1] [3201] (n (n (s [7,w2,w4,w5,w3,w0,2125837,w1] []) [7,w2,w4,w5,w3,w0,2165820,4190271] [] e) [7,w2,w4,w5,w3,w0,2165820,w1] [3201] (n (s [7,w2,w4,w5,w3,w0,2165820,4263872] []) [7,w2,w4,w5,w3,w0,2165821,w1] [1672,3201] e))))))
def T_95 : BT := (n (n (n (n (n (n (s [7,w2,w4,w5,w3,w0,2171997,w1] [1672]) [7,w2,w4,w5,w3,w0,2174077,w1] [1672] (s [7,w2,w4,w5,w3,w0,2207764,w1] [])) [7,w2,w4,w5,w3,w0,2296892,w1] [3201] (n (s [7,w2,w4,w5,w3,w0,2326590,4190271] [910,1158]) [7,w2,w4,w5,w3,w0,2326590,w1] [910,1158] e)) [7,w2,w4,w5,w3,w0,2327836,w1] [] (n (n (s [7,w2,w4,w5,w3,w0,2328894,4190271] [910,1158]) [7,w2,w4,w5,w3,w0,2328894,w1] [910,1158] e) [7,w2,w4,w5,w3,w0,2329662,4190271] [910,1158] (n (s [7,w2,w4,w5,w3,w0,2329662,w1] [910,1158]) [7,w2,w4,w5,w3,w0,2329886,w1] [910,1158] e))) [7,w2,w4,w5,w3,w0,2329910,w1] [910,1158] (n (n (n (s [7,w2,w4,w5,w3,w0,2329916,w1] []) [7,w2,w4,w5,w3,w0,2329918,4190271] [910,1158] e) [7,w2,w4,w5,w3,w0,2329918,w1] [910,1158] (n (s [7,w2,w4,w5,w3,w0,2329918,4198337] [910,1158,3476,3985]) [7,w2,w4,w5,w3,w0,2329918,4198338] [910,1158,1538,2754,3266] e)) [7,w2,w4,w5,w3,w0,2329918,4198340] [910,1158,2826] (n (n (s [7,w2,w4,w5,w3,w0,2329918,4198352] [910,1158,2692,2754,3203,3266]) [7,w2,w4,w5,w3,w0,2329918,4198368] [910,1158,2433,2758,3270] e) [7,w2,w4,w5,w3,w0,2329918,4198370] [910,1158,1538,2433,2758,3270] (n (s [7,w2,w4,w5,w3,w0,2329918,4263872] [1158]) [7,w2,w4,w5,w3,w0,2329918,4263876] [1158,2187] e)))) [7,w2,w4,w5,w3,w0,2329918,4722624] [910,1158,2756,3268] (n (n (n (n (s [7,w2,w4,w5,w3,w0,2329919,w1] []) [7,w2,w4,w5,w3,w0,2329982,w1] [910,1158] e) [7,w2,w4,w5,w3,w0,2330430,w1] [910,1158,3142] (n (s [7,w2,w4,w5,w3,w0,2355229,4190271] [1672]) [7,w2,w4,w5,w3,w0,2355229,w1] [1672] e)) [7,w2,w4,w5,w3,w0,2355229,4427730] [910,1158,1538,1672] (n (n (s [7,w2,w4,w5,w3,w0,2355229,4796357] [910]) [7,w2,w4,w5,w3,w0,2355229,6033378,6295548] [1672] e) [7,w2,w4,w5,w3,w0,2355229,6295548] [1672] (n (s [7,w2,w4,w5,w3,w0,2355229,6553565] [1672]) [7,w2,w4,w5,w3,w0,2357535,w1] [] e))) [7,w2,w4,w5,w3,w0,2358333,w1] [1672] (n (n (n (s [7,w2,w4,w5,w3,w0,2829437,w1] [1672]) [7,w2,w4,w5,w3,w0,2862463,4190271] [] e) [7,w2,w4,w5,w3,w0,2862463,w1] [] (n (s [7,w2,w4,w5,w3,w0,2881629,w1] [1672]) [7,w2,w4,w5,w3,w0,3141695] [4,42,66,172,916,938,1180,1186,1694] e)) [7,w2,w4,w5,w3,w0,3141695,w1] [] (n (n (s [7,w2,w4,w5,w3,w0,3141695,5246912] []) [7,w2,w4,w5,w3,w0,3894525,4190271] [] e) [7,w2,w4,w5,w3,w0,3894525,w1] [] (n (s [7,w2,w4,w5,w3,w0,3927551,w1] []) [7,w2,w4,w5,w3,w0,4190239] [4,42,66,166,916,938,1180,1186,1694,1814,1832,2468] e))))) [7,w2,w4,w5,w3,w0,4190239,w1] [] (n (n (n (n (n (s [7,w2,w4,w5,w3,w0,4190239,4198368] []) [7,w2,w4,w5,w3,w0,4190269] [4,42,66,162,916,938,1180,1186,1538,1556,1694,1814,1832] (s [7,w2,w4,w5,w3,w0,4190269,w1] [1538])) [7,w2,w4,w5,w3,w0,4190269,4198338] [1538] (n (s [7,w2,w4,w5,w3,w0,4190271] [4,42,66,916,938,1180,1186,1694,1814,1832]) [7,w2,w4,w5,w3,w0,4190271,4190271] [] e)) [7,w2,w4,w5,w3,w0,4190271,4192319] [] (n (n (s [7,w2,w4,w5,w3,w0,4190271,4192383] []) [7,w2,w4,w5,w3,w0,4190271,4192511] [] e) [7,w2,w4,w5,w3,w0,4190271,4192639] [] (n (s [7,w2,w4,w5,w3,w0,4190271,4193343] []) [7,w2,w4,w5,w3,w0,4190271,4193407] [] e))) [7,w2,w4,w5,w3,w0,4190271,w1] [] (n (n (n (s [7,w2,w4,w5,w3,w0,4190271,4198337] []) [7,w2,w4,w5,w3,w0,4190271,4198340] [] e) [7,w2,w4,w5,w3,w0,4190271,4263872] [] (n (s [7,w2,w4,w5,w3,w0,4190271,4427730] [910,1158]) [7,w2,w4,w5,w3,w0,4190271,4452801] [1672] e)) [7,w2,w4,w5,w3,w0,4190271,4960215] [] (n (n (s [7,w2,w4,w5,w3,w0,4190271,5992397] []) [7,w2,w4,w5,w3,w0,4190271,6288323] [] e) [7,w2,w4,w5,w3,w0,4190271,6290375] [] (n (s [7,w2,w4,w5,w3,w0,4190271,6291395] []) [7,w2,w4,w5,w3,w0,4190271,6295548] [] e)))) [7,w2,w4,w5,w3,w0,4190271,6321357] [1602,3784] (n (n (n (n (s [7,w2,w4,w5,w3,w0,4190271,6403412] []) [7,w2,w4,w5,w3,w0,4190271,6524926] [910,1158,3910] e) [7,w2,w4,w5,w3,w0,4190271,6551005] [1672,3784] (n (s [7,w2,w4,w5,w3,w0,4190271,6553055] [3784]) [7,w2,w4,w5,w3,w0,4190271,6553085] [1672,3784] e)) [7,w2,w4,w5,w3,w0,4190271,6553565] [1672,3784] (n (n (s [7,w2,w4,w5,w3,w0,4190271,7077341] [1672,3784]) [7,w2,w4,w5,w3,w0,4190271,7337983] [3650,3784,3910] e) [7,w2,w4,w5,w3,w0,4190271,8385535] [3650,3786,3908] (n (s [7,w2,w4,w5,w3,w0,4190271,8386047] [3650,3786]) [7,w2,w4,w5,w3,w0,4190271,8386527] [3650,3786] e))) [7,w2,w4,w5,w3,w0,4190271,8386557] [1538,3650,3786] (n (n (n (s [7,w2,w4,w5,w3,w0,4190271,8388607] []) [7,w2,w4,w5,w3,w0,4192319] [4,42,66,129,161,916,938,1180,1186,1694,1814,1832] e) [7,w2,w4,w5,w3,w0,4192319,w1] [] (n (s [7,w2,w4,w5,w3,w0,4192383,4192447] []) [7,w2,w4,w5,w3,w0,4192383,4192575] [] e)) [7,w2,w4,w5,w3,w0,4192383,4193343] [] (n (n (s [7,w2,w4,w5,w3,w0,4192383,w1] []) [7,w2,w4,w5,w3,w0,4192383,4427730] [1156] e) [7,w2,w4,w5,w3,w0,4192383,5394377] [1156] (n (s [7,w2,w4,w5,w3,w0,4192383,6295548] []) [7,w2,w4,w5,w3,w0,4192511,w1] [] e))))))
def N_96 : BT := n T_94 [7,w2,w4,w5,w3,w0,2165884,w1] [3201] T_95
def T_97 : BT := (n (n (n (n (n (n (s [7,w2,w4,w5,w3,w0,4193343,w1] []) [7,w2,w4,w5,w3,w0,4193343,4427730] [910,1158] (s [7,w2,w4,w5,w3,w0,4193407,w1] [])) [7,w2,w4,w5,w3,w0,w1] [4,42,66,129,916,938,1180,1186,1694,1814,1832] (n (s [7,w2,w4,w5,w3,w0,w1,6292956] []) [7,w2,w4,w5,w3,w0,w1,6295036] [] e)) [7,w2,w4,w5,w3,w0,w1,6295548] [] (n (n (s [7,w2,w4,w5,w3,w0,w1,6295548,6553055] []) [7,w2,w4,w5,w3,w0,w1,6295549] [938,1186,1694,1814,2081,2469,3108,3784] e) [7,w2,w4,w5,w3,w0,w1,6304836] [1602] (n (s [7,w2,w4,w5,w3,w0,w1,6321357] [1602,3784]) [7,w2,w4,w5,w3,w0,w1,6323453] [3784] e))) [7,w2,w4,w5,w3,w0,w1,6361084] [] (n (n (n (s [7,w2,w4,w5,w3,w0,w1,6403412] []) [7,w2,w4,w5,w3,w0,w1,6405500] [] e) [7,w2,w4,w5,w3,w0,w1,6419933] [1672,3784] (n (s [7,w2,w4,w5,w3,w0,w1,6524926] [910,1158,3910]) [7,w2,w4,w5,w3,w0,w1,6536534] [910,1158] e)) [7,w2,w4,w5,w3,w0,w1,6549981] [1672,3784] (n (n (s [7,w2,w4,w5,w3,w0,w1,6550749] [1672,3784]) [7,w2,w4,w5,w3,w0,w1,6550877] [1672] e) [7,w2,w4,w5,w3,w0,w1,6551004] [] (n (s [7,w2,w4,w5,w3,w0,w1,6551005] [1672,3784]) [7,w2,w4,w5,w3,w0,w1,6553053] [1672,3784] e)))) [7,w2,w4,w5,w3,w0,w1,6553055] [3784] (n (n (n (n (s [7,w2,w4,w5,w3,w0,w1,6553085] [1672,3784]) [7,w2,w4,w5,w3,w0,w1,6553087] [3784] e) [7,w2,w4,w5,w3,w0,w1,6553597] [1672,3784] (n (s [7,w2,w4,w5,w3,w0,w1,6790962] [910,1158,3910]) [7,w2,w4,w5,w3,w0,w1,6813695] [3784,3910,4161] e)) [7,w2,w4,w5,w3,w0,w1,7057407] [3784,3910] (n (n (s [7,w2,w4,w5,w3,w0,w1,7077341] [1672,3784]) [7,w2,w4,w5,w3,w0,w1,7077343] [3784] e) [7,w2,w4,w5,w3,w0,w1,7077373] [1672,3784] (n (s [7,w2,w4,w5,w3,w0,w1,7337471] [3650,3784]) [7,w2,w4,w5,w3,w0,w1,7337981] [1538,1672,3650,3784,4161] e))) [7,w2,w4,w5,w3,w0,w1,7337983] [3650,3784,3910,4161] (n (n (n (s [7,w2,w4,w5,w3,w0,w1,7340031] [3784,3910]) [7,w2,w4,w5,w3,w0,w1,8089597] [] e) [7,w2,w4,w5,w3,w0,w1,8125917] [] (n (s [7,w2,w4,w5,w3,w0,w1,8385023] [3650,3786]) [7,w2,w4,w5,w3,w0,w1,8385535] [3650,3786,3908] e)) [7,w2,w4,w5,w3,w0,w1,8385791] [3650,3786] (n (n (s [7,w2,w4,w5,w3,w0,w1,8385919] [3650]) [7,w2,w4,w5,w3,w0,w1,8386015] [3650,3786] e) [7,w2,w4,w5,w3,w0,w1,8386045] [1538,3650,3786] (n (s [7,w2,w4,w5,w3,w0,w1,8386047] [3650,3786]) [7,w2,w4,w5,w3,w0,w1,8386557] [1538,3650,3786,4161] e))))) [7,w2,w4,w5,w3,w0,w1,8386559] [3650,3786,3908,4161] (n (n (n (n (n (s [7,w2,w4,w5,w3,w0,w1,8387583] []) [7,w2,w4,w5,w3,w0,w1,8388095] [] (s [7,w2,w4,w5,w3,w0,w1,8388605] [1538])) [7,w2,w4,w5,w3,w0,w1,8388607] [] (n (s [7,w2,w4,w5,w3,w0,4198337] [4,42,66,129,162,916,938,1180,1186,1306,1314,1694,1814,1832]) [7,w2,w4,w5,w3,w0,4198337,4198337] [] e)) [7,w2,w4,w5,w3,w0,4198337,4427730] [908,1156,2068] (n (n (s [7,w2,w4,w5,w3,w0,4198337,4427731] [908,1156,2068]) [7,w2,w4,w5,w3,w0,4198337,4796357] [908,1672] e) [7,w2,w4,w5,w3,w0,4198337,6288323] [] (n (s [7,w2,w4,w5,w3,w0,4198337,6295548] [938,1186,1694,1814,2081,2469,3784]) [7,w2,w4,w5,w3,w0,4198337,6295549] [938,1186,1694,1814,2081,2469,3108,3784] e))) [7,w2,w4,w5,w3,w0,4198337,6551005] [1672,3784] (n (n (n (s [7,w2,w4,w5,w3,w0,4198337,7190390] [1156,3522,3650,3910]) [7,w2,w4,w5,w3,w0,4198337,8386558] [3650,3786,3908,4161] e) [7,w2,w4,w5,w3,w0,4198340] [4,42,66,129,170,916,938,1180,1186,1694,1814,1832,2202,2209] (n (s [7,w2,w4,w5,w3,w0,4198340,4198340] []) [7,w2,w4,w5,w3,w0,4198340,4427730] [908,1156] e)) [7,w2,w4,w5,w3,w0,4198340,4427734] [908,1156] (n (n (s [7,w2,w4,w5,w3,w0,4198340,4796357] [908,1672,2187]) [7,w2,w4,w5,w3,w0,4198340,5394377] [1156,3649] e) [7,w2,w4,w5,w3,w0,4198340,5394381] [1156] (n (s [7,w2,w4,w5,w3,w0,4198340,6288323] [2187,3651]) [7,w2,w4,w5,w3,w0,4198340,6295548] [2187] e)))) [7,w2,w4,w5,w3,w0,4198340,6551005] [1672,3784] (n (n (n (n (s [7,w2,w4,w5,w3,w0,4198340,7190390] [1156,3522,3910]) [7,w2,w4,w5,w3,w0,4198340,7788474] [908,1672,2187,3530,3918,4042] e) [7,w2,w4,w5,w3,w0,4198340,8386555] [3651,3786,3908,4042,4161] (n (s [7,w2,w4,w5,w3,w0,4198341] [4,42,66,129,170,916,938,1180,1186,1306,1314,1694,1814,1832,2202,2209]) [7,w2,w4,w5,w3,w0,4198348] [4,42,66,129,162,916,938,1180,1186,1694,1814,1832,2202,2209,2322,2345] e)) [7,w2,w4,w5,w3,w0,4198356] [4,42,66,129,172,916,938,1180,1186,1694,1814,1832,2068,2081,2202,2211] (n (n (s [7,w2,w4,w5,w3,w0,4263872] [4,42,66,129,172,1180,1186,1694,1814,1832]) [7,w2,w4,w5,w3,w0,4263872,4263872] [] e) [7,w2,w4,w5,w3,w0,4263872,4427730] [1158] (n (s [7,w2,w4,w5,w3,w0,4263872,5394377] [1158]) [7,w2,w4,w5,w3,w0,4263872,5459913] [1158] e))) [7,w2,w4,w5,w3,w0,4263872,6288323] [] (n (n (n (s [7,w2,w4,w5,w3,w0,4263872,6295548] []) [7,w2,w4,w5,w3,w0,4263872,6361084] [] e) [7,w2,w4,w5,w3,w0,4263872,6551005] [1672,3784] (n (s [7,w2,w4,w5,w3,w0,4263872,7788474] [1672,3918]) [7,w2,w4,w5,w3,w0,4263872,8321023] [3786,3908,4161] e)) [7,w2,w4,w5,w3,w0,4263873] [4,42,66,129,174,1180,1186,1306,1314,1672,1694,1814,1832] (n (n (s [7,w2,w4,w5,w3,w0,4263876] [4,42,66,129,174,1180,1186,1694,1814,1832,2202,2209]) [7,w2,w4,w5,w3,w0,4394944] [4,42,66,129,164,1694,1814,1832] e) [7,w2,w4,w5,w3,w0,4427730,4796357] [1158,1672] (n (s [7,w2,w4,w5,w3,w0,4427730,4796357,6295548] [908]) [7,w2,w4,w5,w3,w0,4427730,5992397] [3521] e))))))
def T_98 : BT := (n (n (n (n (n (n (s [7,w2,w4,w5,w3,w0,4427730,6107111] [1158,1538,4162]) [7,w2,w4,w5,w3,w0,4427730,6295548] [910,1158,2052,3266,4162] (s [7,w2,w4,w5,w3,w0,4427730,6295548,6893565] [910,2052,4680])) [7,w2,w4,w5,w3,w0,4427730,6295548,8156909] [910,1158,2052] (n (s [7,w2,w4,w5,w3,w0,4427730,6893565] [1158,1672,2052,4162]) [7,w2,w4,w5,w3,w0,4427730,8130558] [910,1158,1538,1672,2052,4162] e)) [7,w2,w4,w5,w3,w0,4427730,8159213] [910,1158] (n (n (s [7,w2,w4,w5,w3,w0,4427730,8386303] []) [7,w2,w4,w5,w3,w0,4960215,6295548] [2052,2186] e) [7,w2,w4,w5,w3,w0,5992397,6295548] [2186,2306] (n (s [7,w2,w4,w5,w3,w0,6291395,6295548] []) [7,w2,w4,w5,w3,w0,6295548,8385535] [] e))) [7,w2,w4,w5,w3,2100285,4190271] [4,42,66,131,161,916,938,1180,1186,1306,1314,1694,1814,1832] (n (n (n (s [7,w2,w4,w5,w3,2100285,4198337] [4,42,66,129,916,938,1180,1186,1306,1314,1694,1814,1832]) [7,w2,w4,w5,w3,2100348,4190271] [4,42,66,139,161,916,938,1180,1186,1694,1814,1832,2898] e) [7,w2,w4,w5,w3,2100348,4796357] [4,42,66,131,916,1180,1186,1306,1814,1832,2202] (n (s [7,w2,w4,w5,w3,2165820,4190271] [4,42,66,141,161,1180,1186,1694,1814,1832]) [7,w2,w4,w5,w3,2165820,4263872] [4,42,66,129,916,938,1180,1186,1694,1814,1832] e)) [7,w2,w4,w5,w3,2329918,2698365,4190271] [1158,1672] (n (n (s [7,w2,w4,w5,w3,2329918,3935806,4190271] [908,1156,1538,1672,3266]) [7,w2,w4,w5,w3,2329918,4190271,6288323] [910,1158] e) [7,w2,w4,w5,w3,2329918,4190271,6295548] [910,1158,4034] (n (s [7,w2,w4,w5,w3,2329918,4427730,6295548] [4,910,1158,2052,2692,4034,4163]) [7,w2,w4,w5,w3,2329918,4796357,6295548] [909,1159,1672,2187,2692,3265] e)))) [7,w2,w4,w5,w3,2329918,6033378,6295548] [909,1157,1538,1672,2433,2692,3266] (n (n (n (n (s [7,w2,w4,w5,w3,4190271,4190271,6288323] []) [7,w2,w4,w5,w3,4190271,4192383,6288323] [] e) [7,w2,w4,w5,w3,4190271,4193343,6288323] [] (n (s [7,w2,w4,w5,w3,4190271,4193343,6295548] []) [7,w2,w4,w5,w3,4190271,6288323] [4,42,66,129,916,938,1180,1186,1694,1814,1832] e)) [7,w2,w4,w5,w3,4190271,6288323,6295548] [] (n (n (s [7,w2,w4,w5,w3,4190271,6288323,6551005] [1672,3784]) [7,w2,w4,w5,w3,4190271,6288323,8385535] [3650,3786,3908] e) [7,w2,w4,w5,w3,4190271,6288323,8388607] [] (n (s [7,w2,w4,w5,w3,6295548,8385535] [4,42,66,916,938,1180,1186,1694,1814,1832,2898,3034,3156]) [7,w2,w4,w5,1837603,1837603,w0,w1] [] e))) [7,w2,w4,w5,1837603,1911399,w0,w1] [] (n (n (n (s [7,w2,w4,w5,1837603,2067250,w0,w1] [1602]) [7,w2,w4,w5,1837603,2067251,w0,w1] [1602] e) [7,w2,w4,w5,1837603,w0,2100285,w1] [3201] (n (s [7,w2,w4,w5,1837603,w0,2329918,w1] [910,1158,3478,3985]) [7,w2,w4,w5,1837603,w0,2698365,w1] [910,1672] e)) [7,w2,w4,w5,1837603,w0,3935806,w1] [1674,1794] (n (n (s [7,w2,w4,w5,1837603,w0,3935807,w1] []) [7,w2,w4,w5,1837603,w0,4190271] [6,42,66,918,938,1182,1186,1832] e) [7,w2,w4,w5,1837603,w0,4190271,w1] [] (n (s [7,w2,w4,w5,1837603,w0,w1] [6,42,66,129,918,938,1182,1186,1832]) [7,w2,w4,w5,1837603,w0,w1,6295548] [938,1186,2081] e))))) [7,w2,w4,w5,1837603,w0,w1,6551004] [] (n (n (n (n (n (s [7,w2,w4,w5,1837603,w0,w1,6551005] [1672,3784]) [7,w2,w4,w5,1837603,w0,w1,7190390] [1158,1794,3522,3910] (s [7,w2,w4,w5,1837603,w0,w1,8156909] [910,1158,3652,3788])) [7,w2,w4,w5,1837603,w0,w1,8386558] [3908,4161] (n (s [7,w2,w4,w5,1837603,w0,4198337] [6,42,66,129,918,938,1182,1186,1306,1314,1690,1810,1832]) [7,w2,w4,w5,1837606,1837606,w0,w1] [1674,1794] e)) [7,w2,w4,w5,1837606,1911399,w0,w1] [2186] (n (n (s [7,w2,w4,w5,1837606,1985195,w0,w1] [2306,2440]) [7,w2,w4,w5,1837606,1985199,w0,w1] [2306,2440] e) [7,w2,w4,w5,1837606,2067250,w0,w1] [1602,2186,2306] (n (s [7,w2,w4,w5,1837606,2067254,w0,w1] [1602,2186,2306]) [7,w2,w4,w5,1837606,w0,w0,w1] [2186] e))) [7,w2,w4,w5,1837606,w0,2329918,w1] [910,1158,2826] (n (n (n (s [7,w2,w4,w5,1837606,w0,2698365,w1] [910,1672,2826]) [7,w2,w4,w5,1837606,w0,3296445,w1] [1158,2186] e) [7,w2,w4,w5,1837606,w0,3935806,w1] [1674,2826] (n (s [7,w2,w4,w5,1837606,w0,4190271] [6,42,66,104,918,938,1174,1186,1690,1810,1832,2202]) [7,w2,w4,w5,1837606,w0,4190271,w1] [] e)) [7,w2,w4,w5,1837606,w0,w1] [6,42,66,105,918,938,1174,1186,1690,1810,1832,2202] (n (n (s [7,w2,w4,w5,1837606,w0,w1,4198340] []) [7,w2,w4,w5,1837606,w0,w1,4427730] [910,1158] e) [7,w2,w4,w5,1837606,w0,w1,4796357] [910,1673] (n (s [7,w2,w4,w5,1837606,w0,w1,5394377] [1158,3649]) [7,w2,w4,w5,1837606,w0,w1,6033378] [1675] e)))) [7,w2,w4,w5,1837606,w0,w1,6033382] [1675] (n (n (n (n (s [7,w2,w4,w5,1837606,w0,w1,6288323] [2186,3651]) [7,w2,w4,w5,1837606,w0,w1,6295548] [2186] e) [7,w2,w4,w5,1837606,w0,w1,6551001] [1673,3649,3784] (n (s [7,w2,w4,w5,1837606,w0,w1,6551005] [1672,3784]) [7,w2,w4,w5,1837606,w0,w1,7190390] [1158,3522,3910] e)) [7,w2,w4,w5,1837606,w0,w1,7788474] [910,1674,3530,3918] (n (n (s [7,w2,w4,w5,1837606,w0,w1,8156909] [910,1158,3652,3788]) [7,w2,w4,w5,1837606,w0,w1,8386555] [3651,3786,3908] e) [7,w2,w4,w5,1837606,w0,4198340] [6,42,66,918,938,1174,1186,1690,1810,1832,2202] (n (s [7,w2,w4,w5,1837606,w1,6288323] [6,42,66,105,918,938,1174,1186,1690,1697,1810,1832,2899]) [7,w2,w4,w5,1837607,w0,3296445,w1] [1158,2186] e))) [7,w2,w4,w5,1837607,w0,w1] [6,42,66,105,918,938,1174,1186,1832,2202] (n (n (n (s [7,w2,w4,w5,1837614,w0,w1] [6,42,66,97,918,938,1182,1186,1690,1810,1832,2202,2322]) [7,w2,w4,w5,1837618,1837618,w0,w1] [1674,1794] e) [7,w2,w4,w5,1837618,1911399,w0,w1] [2186] (n (s [7,w2,w4,w5,1837618,1911415,w0,w1] [2186]) [7,w2,w4,w5,1837618,2067250,w0,w1] [1602,2186,2306,2694] e)) [7,w2,w4,w5,1837618,w0,w0,w1] [2054] (n (n (s [7,w2,w4,w5,1837618,w0,2329918,w1] [910,1158,2694]) [7,w2,w4,w5,1837618,w0,2698365,w1] [910,1674,2694] e) [7,w2,w4,w5,1837618,w0,3935806,w1] [1674,1794,2054] (n (s [7,w2,w4,w5,1837618,w0,4190271] [6,42,66,918,938,1182,1186,1690,1810,1832,2070]) [7,w2,w4,w5,1837618,w0,4190271,w1] [] e))))))
def N_99 : BT := n T_97 [7,w2,w4,w5,w3,w0,4427730,6033378] [908,1156,1538,1672,4162] T_98
def N_100 : BT := n N_96 [7,w2,w4,w5,w3,w0,4192639,w1] [] N_99
def T_101 : BT := (n (n (n (n (n (n (s [7,w2,w4,w5,1837618,w0,w1,4198352] []) [7,w2,w4,w5,1837618,w0,w1,4427730] [910,1158,2054] (s [7,w2,w4,w5,1837618,w0,w1,4796357] [910,1674])) [7,w2,w4,w5,1837618,w0,w1,6033378] [1674,1794,3523] (n (s [7,w2,w4,w5,1837618,w0,w1,6033394] [1674,1794,3522]) [7,w2,w4,w5,1837618,w0,w1,6288323] [2054,3521] e)) [7,w2,w4,w5,1837618,w0,w1,6295548] [2054] (n (n (s [7,w2,w4,w5,1837618,w0,w1,6550989] [1674,1794,3784]) [7,w2,w4,w5,1837618,w0,w1,6551005] [1674,1794,3784] e) [7,w2,w4,w5,1837618,w0,w1,7190390] [1158,1794,3522,3910] (n (s [7,w2,w4,w5,1837618,w0,w1,8156909] [910,1158,2054,3652,3788]) [7,w2,w4,w5,1837618,w0,w1,8386543] [3521,3650,3786,3908] e))) [7,w2,w4,w5,1837618,w0,4198352] [6,42,66,918,938,1182,1186,1690,1810,1832,2070] (n (n (n (s [7,w2,w4,w5,1837618,2329918,w1] [6,42,66,97,938,1186,1558,1690,1810,1832,2710]) [7,w2,w4,w5,1837618,w1,6288323] [6,42,66,97,918,938,1182,1186,1690,1810,1832,2769] e) [7,w2,w4,w5,1837622,w0,w1] [6,42,66,105,918,938,1174,1186,1690,1810,1832,2070,2202] (n (s [7,w2,w4,w5,1837670,w0,w1] [6,42,66,104,129,918,938,1174,1186,1368,1690,1810,1832,2202,2843]) [7,w2,w4,w5,1837670,w0,w1,6295548] [2187,2826,3594] e)) [7,w2,w4,w5,1837874,w0,w1] [6,42,66,129,918,938,1182,1186,1618,1690,1810,1832,2070,2081,2711] (n (n (s [7,w2,w4,w5,1837874,w0,w1,6295548] [2055,2694,3462]) [7,w2,w4,w5,1838626,1838626,w0,w1] [1674,1794] e) [7,w2,w4,w5,1838626,1911399,w0,w1] [2186] (n (s [7,w2,w4,w5,1838626,1912423,w0,w1] [2186]) [7,w2,w4,w5,1838626,2067250,w0,w1] [1602,2186,2306] e)))) [7,w2,w4,w5,1838626,2068274,w0,w1] [1602,2186,2306] (n (n (n (n (s [7,w2,w4,w5,1838626,w0,w0,w1] []) [7,w2,w4,w5,1838626,w0,2329918,w1] [910,1158] e) [7,w2,w4,w5,1838626,w0,2698365,w1] [910,1672] (n (s [7,w2,w4,w5,1838626,w0,3935806,w1] [1674,1794]) [7,w2,w4,w5,1838626,w0,4190271] [6,42,66,918,938,1182,1186,1690,1810,1832] e)) [7,w2,w4,w5,1838626,w0,4190271,w1] [] (n (n (s [7,w2,w4,w5,1838626,w0,w1] [6,42,66,129,918,938,1182,1186,1690,1810,1832,3217]) [7,w2,w4,w5,1838626,w0,w1,6295548] [3969] e) [7,w2,w4,w5,1838626,w0,w1,6549981] [1672,3784] (n (s [7,w2,w4,w5,1838626,w0,w1,6551005] [1672,3784]) [7,w2,w4,w5,1838626,w0,w1,7190390] [1158,1794,3522,3910] e))) [7,w2,w4,w5,1838626,w0,w1,8156909] [910,1158,3652,3788] (n (n (n (s [7,w2,w4,w5,1838626,w0,w1,8385535] [3650,3786,3908,4161]) [7,w2,w4,w5,1838626,w0,6295548] [6,42,66,129,918,938,1182,1186,1690,1810,1832,2146,2344,2408,2534] e) [7,w2,w4,w5,1838626,6295548] [6,42,56,66,918,938,1182,1186,1208,1272,1650,1690,1782,1810,1832,1848,1918,2162,2360,2424,2550] (n (s [7,w2,w4,w5,1838630,w0,w1] [6,42,66,105,918,938,1174,1186,1690,1810,1832,2202]) [7,w2,w4,w5,1838630,w0,w1,4796357] [910,1673] e)) [7,w2,w4,w5,1838642,w0,w1] [6,42,66,97,918,938,1182,1186,1690,1810,1832,2070] (n (n (s [7,w2,w4,w5,1838642,w0,w1,4427730] [910,1158,2054]) [7,w2,w4,w5,1843813,1911399,w0,w1] [1158] e) [7,w2,w4,w5,1845863,w0,w1] [6,42,66,104,129,918,936,1174,1186,1368,1748,1832,2202,2843] (n (s [7,w2,w4,w5,1845863,w0,w1,8156909] [910,1158,3652,3788]) [7,w2,w4,w5,1903138,1903138,w0,w1] [1794] e))))) [7,w2,w4,w5,1903138,1911399,w0,w1] [] (n (n (n (n (n (s [7,w2,w4,w5,1903138,1985195,w0,w1] [2306,2440]) [7,w2,w4,w5,1903138,2050731,w0,w1] [2306,2440] (s [7,w2,w4,w5,1903138,2067250,w0,w1] [1602,2306])) [7,w2,w4,w5,1903138,w0,2165820,w1] [3201] (n (s [7,w2,w4,w5,1903138,w0,2329918,w1] [1158]) [7,w2,w4,w5,1903138,w0,2698365,w1] [910,1672] e)) [7,w2,w4,w5,1903138,w0,3296445,w1] [1158] (n (n (s [7,w2,w4,w5,1903138,w0,3935806,w1] [1674,1794]) [7,w2,w4,w5,1903138,w0,4001342,w1] [1794] e) [7,w2,w4,w5,1903138,w0,4190271] [6,42,66,104,918,1174,1186,1810,1832] (n (s [7,w2,w4,w5,1903138,w0,4190271,w1] []) [7,w2,w4,w5,1903138,w0,w1] [6,42,66,104,129,918,1174,1186,1810,1832] e))) [7,w2,w4,w5,1903138,w0,w1,6295548] [] (n (n (n (s [7,w2,w4,w5,1903138,w0,w1,6485469] [3784]) [7,w2,w4,w5,1903138,w0,w1,6551005] [1672,3784] e) [7,w2,w4,w5,1903138,w0,w1,7190390] [1158,1794,3522,3910] (n (s [7,w2,w4,w5,1903138,w0,w1,7788474] [910,1674,3530,3918]) [7,w2,w4,w5,1903138,w0,w1,8156909] [1158,3788] e)) [7,w2,w4,w5,1903138,w0,w1,8321023] [3530,3786,3908,4161] (n (n (s [7,w2,w4,w5,1903138,w0,4263872] [6,42,66,129,918,936,1174,1186,1690,1810,1832]) [7,w2,w4,w5,1903139,w0,w1] [6,42,66,104,129,918,1174,1186,1832] e) [7,w2,w4,w5,1903142,w0,2329918,w1] [1158,2186] (n (s [7,w2,w4,w5,1903142,w0,w1] [6,42,66,105,918,1174,1186,1810,1832,2202]) [7,w2,w4,w5,1903154,w0,2698365,w1] [910,1674,2054,2694] e)))) [7,w2,w4,w5,1903154,w0,w1] [6,42,66,105,918,1174,1186,1810,1832,2070] (n (n (n (n (s [7,w2,w4,w5,1908775,1911399,w0,4190271] [1730]) [7,w2,w4,w5,1908775,1911399,w0,w1] [1730,3592] e) [7,w2,w4,w5,1911335,w0,4190271] [6,42,66,104,918,1174,1186,1832,2202] (n (s [7,w2,w4,w5,1911335,w0,4190271,w1] []) [7,w2,w4,w5,1911335,w0,w1] [6,42,66,105,918,1174,1186,1832,2202] e)) [7,w2,w4,w5,1911398,w0,w1] [6,42,66,104,129,918,1174,1186,1314,1810,2202,2843] (n (n (s [7,w2,w4,w5,1911398,w0,w1,7190390] [1158,3522,3910]) [7,w2,w4,w5,1911399,1911399,w0,4190271] [] e) [7,w2,w4,w5,1911399,1911399,w0,w1] [] (n (s [7,w2,w4,w5,1911399,1911407,w0,w1] []) [7,w2,w4,w5,1911399,1911415,w0,w1] [] e))) [7,w2,w4,w5,1911399,1912423,w0,w1] [] (n (n (n (s [7,w2,w4,w5,1911399,1985195,2067250,w0,w1] []) [7,w2,w4,w5,1911399,1985195,2075511,w0,w1] [] e) [7,w2,w4,w5,1911399,1985195,w0,2329918,w1] [910,1158] (n (s [7,w2,w4,w5,1911399,1985195,w0,4190271] [1736]) [7,w2,w4,w5,1911399,1985195,w0,w1] [936,1736] e)) [7,w2,w4,w5,1911399,1985195,w0,w1,6295548] [] (n (n (s [7,w2,w4,w5,1911399,2042471,w0,w1] []) [7,w2,w4,w5,1911399,2058991,w0,4190271] [] e) [7,w2,w4,w5,1911399,2058991,w0,w1] [] (n (s [7,w2,w4,w5,1911399,2067250,w0,4190271] [1602]) [7,w2,w4,w5,1911399,2067250,w0,w1] [1602] e))))))
def T_102 : BT := (n (n (n (n (n (n (s [7,w2,w4,w5,1911399,2075511,w0,w1] [1602]) [7,w2,w4,w5,1911399,2083771,w0,w1] [1602,2242] (s [7,w2,w4,w5,1911399,2092031,w0,w1] [1602])) [7,w2,w4,w5,1911399,2093059,w0,w1] [2242,2825,3592] (n (s [7,w2,w4,w5,1911399,2097212,w0,4190271] [2184,2824]) [7,w2,w4,w5,1911399,2097212,w0,w1] [2184,2824] e)) [7,w2,w4,w5,1911399,2098200,w0,w1] [2184] (n (n (s [7,w2,w4,w5,1911399,2098204,w0,w1] [2184]) [7,w2,w4,w5,1911399,2098220,w0,w1] [2184,2824] e) [7,w2,w4,w5,1911399,2098228,w0,w1] [2184,2826] (n (s [7,w2,w4,w5,1911399,2098232,w0,w1] [2184]) [7,w2,w4,w5,1911399,w0,w0,w1] [2184] e))) [7,w2,w4,w5,1911399,w0,2100285,w1] [2185,2824,3201] (n (n (n (s [7,w2,w4,w5,1911399,w0,2100286,w1] [906,1538,2187,3201,3610,3985]) [7,w2,w4,w5,1911399,w0,2100348,w1] [2185,2824,3201] e) [7,w2,w4,w5,1911399,w0,2100412,w1] [2185,2824,3201] (n (s [7,w2,w4,w5,1911399,w0,2100540,w1] [2187,2824,3201]) [7,w2,w4,w5,1911399,w0,2100796,w1] [2187,2824,3201] e)) [7,w2,w4,w5,1911399,w0,2100860,w1] [2185,2824,3201,3592] (n (n (s [7,w2,w4,w5,1911399,w0,2165820,w1] [2185,2824,3201]) [7,w2,w4,w5,1911399,w0,2165822,w1] [1158,1538,2185,3201] e) [7,w2,w4,w5,1911399,w0,2231356,w1] [2185,2824,3201] (n (s [7,w2,w4,w5,1911399,w0,2281496,w1] [2824]) [7,w2,w4,w5,1911399,w0,2329918,4190271] [1158,2184] e)))) [7,w2,w4,w5,1911399,w0,2329918,w1] [1158,2185] (n (n (n (n (s [7,w2,w4,w5,1911399,w0,2355229,w1] [1672,2824]) [7,w2,w4,w5,1911399,w0,2624572,w1] [2824] e) [7,w2,w4,w5,1911399,w0,2698365,4190271] [906,1672,2824] (n (s [7,w2,w4,w5,1911399,w0,2698365,w1] [906,1672,2824]) [7,w2,w4,w5,1911399,w0,2862463,w1] [] e)) [7,w2,w4,w5,1911399,w0,2994230,w1] [1158,3592] (n (n (s [7,w2,w4,w5,1911399,w0,3148860,w1] [2187,3201]) [7,w2,w4,w5,1911399,w0,3148861,w1] [1158,2187,3201] e) [7,w2,w4,w5,1911399,w0,3296445,4190271] [1158,2186] (n (s [7,w2,w4,w5,1911399,w0,3296445,w1] [1158,2187]) [7,w2,w4,w5,1911399,w0,3395007,w1] [2185] e))) [7,w2,w4,w5,1911399,w0,3592250,w1] [906,1674] (n (n (n (s [7,w2,w4,w5,1911399,w0,3894525,w1] [906]) [7,w2,w4,w5,1911399,w0,3935806,4190271] [1674] e) [7,w2,w4,w5,1911399,w0,3935806,w1] [1674] (n (s [7,w2,w4,w5,1911399,w0,3935806,w1,6295548] [2185]) [7,w2,w4,w5,1911399,w0,3960877,w1] [1158,3594] e)) [7,w2,w4,w5,1911399,w0,4009599,4190271] [] (n (n (s [7,w2,w4,w5,1911399,w0,4009599,w1] []) [7,w2,w4,w5,1911399,w0,4083391,w1] [] e) [7,w2,w4,w5,1911399,w0,4157183,w1] [] (n (s [7,w2,w4,w5,1911399,w0,4165438,w1] []) [7,w2,w4,w5,1911399,w0,4173695,w1] [] e))))) [7,w2,w4,w5,1911399,w0,4190271] [6,42,66,104,914,1174,2200,2898] (n (n (n (n (n (s [7,w2,w4,w5,1911399,w0,4190271,4190271] [2882]) [7,w2,w4,w5,1911399,w0,4190271,4192383] [] (s [7,w2,w4,w5,1911399,w0,4190271,4192447] [3650])) [7,w2,w4,w5,1911399,w0,4190271,4192575] [3650] (n (s [7,w2,w4,w5,1911399,w0,4190271,4192831] [3650]) [7,w2,w4,w5,1911399,w0,4190271,4192895] [] e)) [7,w2,w4,w5,1911399,w0,4190271,4193343] [3650] (n (n (s [7,w2,w4,w5,1911399,w0,4190271,w1] [2882,3592]) [7,w2,w4,w5,1911399,w0,4190271,4427730] [1158] e) [7,w2,w4,w5,1911399,w0,4190271,4796357] [906,1672,2882,3592] (n (s [7,w2,w4,w5,1911399,w0,4190271,5394377] [1158]) [7,w2,w4,w5,1911399,w0,4190271,6033378] [1674,3905] e))) [7,w2,w4,w5,1911399,w0,4190271,6107111] [] (n (n (n (s [7,w2,w4,w5,1911399,w0,4190271,6288323] [2184,3651]) [7,w2,w4,w5,1911399,w0,4190271,6295548] [2184,3592] e) [7,w2,w4,w5,1911399,w0,4190271,6477208] [1736,3592] (n (s [7,w2,w4,w5,1911399,w0,4190271,6551005] [1672,3592,3784]) [7,w2,w4,w5,1911399,w0,4190271,7190390] [1158,3522,3910] e)) [7,w2,w4,w5,1911399,w0,4190271,7788474] [906,1674,3530,3918] (n (n (s [7,w2,w4,w5,1911399,w0,4190271,8156909] [1158,3788]) [7,w2,w4,w5,1911399,w0,4190271,8388607] [] e) [7,w2,w4,w5,1911399,w0,4192383,w1] [] (n (s [7,w2,w4,w5,1911399,w0,4192447,w1] [2882,3592]) [7,w2,w4,w5,1911399,w0,4192575,w1] [2882,3594] e)))) [7,w2,w4,w5,1911399,w0,4192831,w1] [2882] (n (n (n (n (s [7,w2,w4,w5,1911399,w0,4192895,w1] []) [7,w2,w4,w5,1911399,w0,4193343,w1] [2882,3592] e) [7,w2,w4,w5,1911399,w0,w1] [6,42,66,104,129,914,1174,2200,2841] (n (s [7,w2,w4,w5,1911399,w0,w1,6295548] [2185,2824,3592]) [7,w2,w4,w5,1911399,w0,w1,6295548,7788474] [906,2185,2824] e)) [7,w2,w4,w5,1911399,w0,w1,6295548,8130558] [2185,2824,4418] (n (n (s [7,w2,w4,w5,1911399,w0,w1,6313096] [1602,3592]) [7,w2,w4,w5,1911399,w0,w1,6321357] [1602,3592,3784] e) [7,w2,w4,w5,1911399,w0,w1,6329616] [3592] (n (s [7,w2,w4,w5,1911399,w0,w1,6403412] [3592]) [7,w2,w4,w5,1911399,w0,w1,6477208] [1736,3592] e))) [7,w2,w4,w5,1911399,w0,w1,6479292] [2185,3592] (n (n (n (s [7,w2,w4,w5,1911399,w0,w1,6524926] [1158,2185,2824,3906]) [7,w2,w4,w5,1911399,w0,w1,6544794] [1158] e) [7,w2,w4,w5,1911399,w0,w1,6551005] [1672,3592,3784] (n (s [7,w2,w4,w5,1911399,w0,w1,6553055] [3784]) [7,w2,w4,w5,1911399,w0,w1,6553085] [1672,3592,3784] e)) [7,w2,w4,w5,1911399,w0,w1,6592306] [906,1174,3522,3910] (n (n (s [7,w2,w4,w5,1911399,w0,w1,6893565] [906,1672,3592,3784]) [7,w2,w4,w5,1911399,w0,w1,7077341] [906,1672,3592,3784] e) [7,w2,w4,w5,1911399,w0,w1,7091812] [3592] (n (s [7,w2,w4,w5,1911399,w0,w1,7190390] [1158,3522,3910]) [7,w2,w4,w5,1911399,w0,w1,7192439] [3522,3910] e))))))
def N_103 : BT := n T_101 [7,w2,w4,w5,1911399,2075511,w0,4190271] [1602] T_102
def T_104 : BT := (n (n (n (n (n (n (s [7,w2,w4,w5,1911399,w0,w1,7323510] [1158,3910]) [7,w2,w4,w5,1911399,w0,w1,7337982] [1158,3910,4161] (s [7,w2,w4,w5,1911399,w0,w1,7337983] [3650,3784,3910,4161])) [7,w2,w4,w5,1911399,w0,w1,7491581] [1158,2185,2824] (n (s [7,w2,w4,w5,1911399,w0,w1,7527833] [1158,1736]) [7,w2,w4,w5,1911399,w0,w1,7601629] [1736] e)) [7,w2,w4,w5,1911399,w0,w1,7624360] [] (n (n (s [7,w2,w4,w5,1911399,w0,w1,7788474] [906,1674,3530,3918]) [7,w2,w4,w5,1911399,w0,w1,7790523] [906,3530,3918] e) [7,w2,w4,w5,1911399,w0,w1,7790526] [906,1674,2185,3530,3918] (n (s [7,w2,w4,w5,1911399,w0,w1,7856058] [3914]) [7,w2,w4,w5,1911399,w0,w1,7862271] [3786,3912,4161] e))) [7,w2,w4,w5,1911399,w0,w1,8130558] [1674,3522] (n (n (n (s [7,w2,w4,w5,1911399,w0,w1,8156909] [1158,3788]) [7,w2,w4,w5,1911399,w0,w1,8158959] [3788] e) [7,w2,w4,w5,1911399,w0,w1,8158973] [1158,3788] (n (s [7,w2,w4,w5,1911399,w0,w1,8204287] [3522,3788]) [7,w2,w4,w5,1911399,w0,w1,8224493] [910,3788] e)) [7,w2,w4,w5,1911399,w0,w1,8224495] [3788] (n (n (s [7,w2,w4,w5,1911399,w0,w1,8241014] [3522]) [7,w2,w4,w5,1911399,w0,w1,8241015] [3522] e) [7,w2,w4,w5,1911399,w0,w1,8255487] [3522,3650,3788,4161] (n (s [7,w2,w4,w5,1911399,w0,w1,8290029] [1158]) [7,w2,w4,w5,1911399,w0,w1,8314810] [1674,3530] e)))) [7,w2,w4,w5,1911399,w0,w1,8321021] [1158,1542,3786,4161] (n (n (n (n (s [7,w2,w4,w5,1911399,w0,w1,8321023] [3530,3786,4161]) [7,w2,w4,w5,1911399,w0,w1,8385535] [3650,3786] e) [7,w2,w4,w5,1911399,w0,w1,8385983] [2824,3650,3786] (n (s [7,w2,w4,w5,1911399,w0,w1,8386047] [3650,3786]) [7,w2,w4,w5,1911399,w0,w1,8386303] [3650,3786] e)) [7,w2,w4,w5,1911399,w0,w1,8386431] [3650] (n (n (s [7,w2,w4,w5,1911399,w0,w1,8386495] [3650,3786]) [7,w2,w4,w5,1911399,w0,w1,8386557] [906,1538,3650,3786,4161] e) [7,w2,w4,w5,1911399,w0,w1,8386558] [4161] (n (s [7,w2,w4,w5,1911399,w0,w1,8388607] []) [7,w2,w4,w5,1911399,w0,4198337] [6,40,66,104,129,914,1174,1304,1314,1810,2200,2840] e))) [7,w2,w4,w5,1911399,w0,4198338] [6,42,66,104,129,906,914,936,1174,1186,1368,1538,1558,2200,2842] (n (n (n (s [7,w2,w4,w5,1911399,w0,4198340] [6,40,66,129,914,1174,2200,2209,2840]) [7,w2,w4,w5,1911399,w0,4198344] [6,40,66,104,129,914,1178,1832,2200,2322,2337,2840] e) [7,w2,w4,w5,1911399,w0,4198352] [6,42,66,104,129,914,1178,1186,2070,2081,2200,2842] (n (s [7,w2,w4,w5,1911399,w0,4198368] [6,42,66,104,129,918,1174,1186,2200,2842]) [7,w2,w4,w5,1911399,w0,4198372] [6,42,66,129,918,1174,1186,2185,2200,2209,2465,2840] e)) [7,w2,w4,w5,1911399,w0,4263872] [6,40,66,129,936,1174,1368,2200,2840] (n (n (s [7,w2,w4,w5,1911399,w0,4263874] [6,40,66,129,1158,1174,1186,2200]) [7,w2,w4,w5,1911399,w0,4329408] [6,42,66,104,129,914,1832,2200,2840] e) [7,w2,w4,w5,1911399,w0,4427730,4796357] [1158,1672,3592] (n (s [7,w2,w4,w5,1911399,w0,4427730,5394377] []) [7,w2,w4,w5,1911399,w0,4427730,6033378] [906,1158,1174,1538,1672] e))))) [7,w2,w4,w5,1911399,w0,4427730,6107111] [1158] (n (n (n (n (n (s [7,w2,w4,w5,1911399,w0,4427730,6295548] [1158,2054,2185,3266,3592]) [7,w2,w4,w5,1911399,w0,4796357,5394377] [906,1158,1674,2826] (s [7,w2,w4,w5,1911399,w0,4796357,6295548] [40,906,1672,2184,2824])) [7,w2,w4,w5,1911399,w0,5246912] [6,42,66,104,129,918,1178,1304,2200,2842] (n (s [7,w2,w4,w5,1911399,w0,5246913] [6,42,66,104,129,918,1158,1178,1314,2200]) [7,w2,w4,w5,1911399,w0,5394377,6033378] [1158,1674,3149] e)) [7,w2,w4,w5,1911399,w0,5394377,6107111] [1158,3149] (n (n (s [7,w2,w4,w5,1911399,w0,5394377,6295548] [1158,2187,2306,3272,3594]) [7,w2,w4,w5,1911399,w0,6033378,6295548] [1368,1674,2184,2433,3270,3610,3926] e) [7,w2,w4,w5,1911399,w0,6107111,6295548] [2184,3270] (n (s [7,w2,w4,w5,1911399,4190271,6288323] [6,42,66,104,129,914,1174,2258,2899]) [7,w2,w4,w5,1911407,w0,w1] [6,40,66,105,914,1178,2200,2322,2840] e))) [7,w2,w4,w5,1911415,w0,w1] [6,42,66,105,914,1178,2070,2202,2842] (n (n (n (s [7,w2,w4,w5,1912423,w0,w1] [6,42,66,104,129,914,1178,2200,2841,3217]) [7,w2,w4,w5,2034210,w0,w1] [6,42,66,129,914,1178,1832] e) [7,w2,w4,w5,2042471,w0,w1] [6,42,66,104,129,914,1178,2200,2841] (n (s [7,w2,w4,w5,2058991,2058991,w0,w1] []) [7,w2,w4,w5,2058991,2067250,w0,w1] [] e)) [7,w2,w4,w5,2058991,2075511,w0,w1] [2378] (n (n (s [7,w2,w4,w5,2058991,2092031,w0,w1] []) [7,w2,w4,w5,2058991,w0,2329918,w1] [2185,2305] e) [7,w2,w4,w5,2058991,w0,2698365,w1] [906,1672,2305,2824] (n (s [7,w2,w4,w5,2058991,w0,3894525,w1] []) [7,w2,w4,w5,2058991,w0,3935806,w1] [2081,2500,3985] e)))) [7,w2,w4,w5,2058991,w0,4009599,w1] [2500] (n (n (n (n (s [7,w2,w4,w5,2058991,w0,4157183,w1] [2500]) [7,w2,w4,w5,2058991,w0,4190271] [6,40,914,1178,2200,2898,3034] e) [7,w2,w4,w5,2058991,w0,4190271,w1] [2882,3018,3592] (n (s [7,w2,w4,w5,2058991,w0,w1] [6,40,129,914,1178,2200,2841,2961]) [7,w2,w4,w5,2058991,w0,w1,6295548] [2185,2305,2824,3592] e)) [7,w2,w4,w5,2058991,w0,w1,6329616] [3592] (n (n (s [7,w2,w4,w5,2058991,w0,w1,6403412] [3592]) [7,w2,w4,w5,2058991,w0,w1,6551005] [3784] e) [7,w2,w4,w5,2058991,w0,w1,6592306] [914,1178,2200,2841,2961,3522,3538,3910,4129] (n (s [7,w2,w4,w5,2058991,w0,w1,7190390] [1154,3522,3910]) [7,w2,w4,w5,2058991,w0,w1,8156909] [] e))) [7,w2,w4,w5,2067250,w0,2100286,w1] [906,1154,1538,2051,2114,2754,3201] (n (n (n (s [7,w2,w4,w5,2067250,w0,2355229,w1] [1674,1794,3458]) [7,w2,w4,w5,2067250,w0,3935806,4190271] [1674,1794,2050,2754] e) [7,w2,w4,w5,2067250,w0,3935806,w1] [1674,1794,2051,2754] (n (s [7,w2,w4,w5,2067250,w0,3935806,w1,6321357] [1674,1794,2051,4865]) [7,w2,w4,w5,2067250,w0,4009599,w1] [2051,2754] e)) [7,w2,w4,w5,2067250,w0,4190271,6033378] [1674,1794,3523,3905] (n (n (s [7,w2,w4,w5,2067250,w0,4190271,6551005] [1674,1794]) [7,w2,w4,w5,2067250,w0,w1,6403412] [] e) [7,w2,w4,w5,2067250,w0,w1,6551005] [1674,1794] (n (s [7,w2,w4,w5,2067250,w0,w1,6553085] [1674,1794]) [7,w2,w4,w5,2067250,w0,w1,7077341] [906,1674] e))))))
def T_105 : BT := (n (n (n (n (n (n (s [7,w2,w4,w5,2067250,w0,w1,8158959] [3522]) [7,w2,w4,w5,2067250,w0,w1,8386557] [906,1154,1538] (s [7,w2,w4,w5,2067250,w0,4198338] [6,42,66,129,906,914,936,978,1154,1178,1242,1538,1554,1690,1810,1832,2066,2130,2706,2771])) [7,w2,w4,w5,2067250,w0,4427730,6033378] [906,1154,1538,1674,1794,2690,3905] (n (s [7,w2,w4,w5,2067250,w0,4796357,6033378] [1794,2694]) [7,w2,w4,w5,2067250,w0,6033378,6295548] [1674,1794,2050,2433,3462] e)) [7,w2,w4,w5,2075511,w0,3935806,w1] [1674,2051,2754] (n (n (s [7,w2,w4,w5,2075511,w0,4009599,w1] [2754]) [7,w2,w4,w5,2075511,w0,w1,6477208] [1608,1736,3594] e) [7,w2,w4,w5,2075511,w0,w1,6551005] [1674,3594] (n (s [7,w2,w4,w5,2093059,w0,w1,6551005] []) [7,w2,w4,w5,2097212,w0,4190271,6551005] [] e))) [7,w2,w4,w5,2097212,w0,w1,6551005] [] (n (n (n (s [7,w2,w4,w5,2098196,w0,w1,6403412] []) [7,w2,w4,w5,2098204,w0,3935806,w1] [] e) [7,w2,w4,w5,2098204,w0,4190271,6551005] [] (n (s [7,w2,w4,w5,2098204,w0,w1,6551005] []) [7,w2,w4,w5,2098204,w0,w1,6553085] [] e)) [7,w2,w4,w5,2098204,w0,w1,7077341] [] (n (n (s [7,w2,w4,w5,2098204,2329918,w1,6551005] [906,1154]) [7,w2,w4,w5,2098204,2698365,w1,6551005] [906] e) [7,w2,w4,w5,2098204,w1,6288323,6551005] [3841] (n (s [7,w2,w4,w5,2098204,w1,6295548,6551005] []) [7,w2,w4,w5,2098204,w1,6551005,6553085] [] e)))) [7,w2,w4,w5,2098220,w0,w1,6551005] [] (n (n (n (n (s [7,w2,w4,w5,2098228,w0,w1,6551005] []) [7,w2,w4,w5,2100252,w0,w1,6551005] [] e) [7,w2,w4,w5,2100252,w0,w1,7077341] [] (n (s [7,w2,w4,w5,w0,w0,w1,6551005] []) [7,w2,w4,w5,w0,2100285,w1,6551005] [2433] e)) [7,w2,w4,w5,w0,2100286,w1,6551005] [2433] (n (n (s [7,w2,w4,w5,w0,2100348,w1,6551005] [2433]) [7,w2,w4,w5,w0,2100540,w1,6551005] [2433] e) [7,w2,w4,w5,w0,2100796,w1,6033378] [2433] (n (s [7,w2,w4,w5,w0,2100796,w1,6551005] [2433]) [7,w2,w4,w5,w0,2165820,w1,6551005] [2433] e))) [7,w2,w4,w5,w0,2171997,w1,6551005] [] (n (n (n (s [7,w2,w4,w5,w0,2174077,w1,6551005] []) [7,w2,w4,w5,w0,2327836,w1,6551005] [] e) [7,w2,w4,w5,w0,2329886,w1,6551005] [906,1154] (n (s [7,w2,w4,w5,w0,2329916,w1,6551005] []) [7,w2,w4,w5,w0,2329918,4190271,6551005] [906,1154] e)) [7,w2,w4,w5,w0,2329918,w1,6403412] [906,1793] (n (n (s [7,w2,w4,w5,w0,2329918,w1,6551005] [906,1154]) [7,w2,w4,w5,w0,2329918,w1,7077341] [906,1154] e) [7,w2,w4,w5,w0,2355229,3935806,w1] [] (n (s [7,w2,w4,w5,w0,2355229,3935806,w1,6033378] []) [7,w2,w4,w5,w0,2355229,4190271,6551005] [] e))))) [7,w2,w4,w5,w0,2355229,4192831,w1] [] (n (n (n (n (n (s [7,w2,w4,w5,w0,2355229,w1,6551005] []) [7,w2,w4,w5,w0,2624572,w1,6551005] [2433] (s [7,w2,w4,w5,w0,2698333,w1,6551005] [906])) [7,w2,w4,w5,w0,2698365,4190271,6551005] [906] (n (s [7,w2,w4,w5,w0,2698365,w1,6403412] [906,1795]) [7,w2,w4,w5,w0,2698365,w1,6477208] [906,2184,2248,2504] e)) [7,w2,w4,w5,w0,2698365,w1,6551005] [906] (n (n (s [7,w2,w4,w5,w0,2698365,w1,7077341] [906]) [7,w2,w4,w5,w0,2698365,w1,7601629] [906,2248,2504] e) [7,w2,w4,w5,w0,2862463,w1,6551005] [] (n (s [7,w2,w4,w5,w0,2994230,w1,6551005] [1154]) [7,w2,w4,w5,w0,3894525,w1,6551005] [] e))) [7,w2,w4,w5,w0,3935806,4190271,6033378] [] (n (n (n (s [7,w2,w4,w5,w0,3935806,4190271,6551005] []) [7,w2,w4,w5,w0,3935806,w1,6033378] [] e) [7,w2,w4,w5,w0,3935806,w1,6033378,6551005] [] (n (s [7,w2,w4,w5,w0,3935806,w1,6107111] []) [7,w2,w4,w5,w0,3935806,w1,6262770] [1539] e)) [7,w2,w4,w5,w0,3935806,w1,6290403] [] (n (n (s [7,w2,w4,w5,w0,3935806,w1,6321357] [1539,2114]) [7,w2,w4,w5,w0,3935806,w1,6403412] [] e) [7,w2,w4,w5,w0,3935806,w1,6551005] [] (n (s [7,w2,w4,w5,w0,3935806,w1,6553055] []) [7,w2,w4,w5,w0,3935806,w1,6553565] [] e)))) [7,w2,w4,w5,w0,3935806,w1,7077341] [] (n (n (n (n (s [7,w2,w4,w5,w0,3935806,w1,8386527] []) [7,w2,w4,w5,w0,3935806,4198368] [6,42,66,97,914,936,1178,1569,2344,3089] e) [7,w2,w4,w5,w0,3935806,4427730,6033378] [906,1154,1538,2050] (n (s [7,w2,w4,w5,w0,3935806,4796357,6033378] [906]) [7,w2,w4,w5,w0,3935806,6033378,6295548] [] e)) [7,w2,w4,w5,w0,3960877,w1,6551005] [906,1154] (n (n (s [7,w2,w4,w5,w0,4009599,w1,6107111] []) [7,w2,w4,w5,w0,4009599,w1,6477208] [2248,2504] e) [7,w2,w4,w5,w0,4009599,w1,6551005] [] (n (s [7,w2,w4,w5,w0,4165438,w1,6551005] []) [7,w2,w4,w5,w0,4190271,4190271,6551005] [] e))) [7,w2,w4,w5,w0,4190271,4192383,6551005] [] (n (n (n (s [7,w2,w4,w5,w0,4190271,4192575,6551005] []) [7,w2,w4,w5,w0,4190271,4192831,6033378] [] e) [7,w2,w4,w5,w0,4190271,4192831,6551005] [] (n (s [7,w2,w4,w5,w0,4190271,4193343,6551005] []) [7,w2,w4,w5,w0,4190271,w1,6403412] [2378] e)) [7,w2,w4,w5,w0,4190271,w1,6551005] [] (n (n (s [7,w2,w4,w5,w0,4190271,w1,7077341] []) [7,w2,w4,w5,w0,4190271,4427730,6551005] [906,1154] e) [7,w2,w4,w5,w0,4190271,4796357,6551005] [906] (n (s [7,w2,w4,w5,w0,4190271,6033378,6551005] []) [7,w2,w4,w5,w0,4190271,6288323,6551005] [] e))))))
def N_106 : BT := n T_104 [7,w2,w4,w5,2067250,w0,w1,8130558] [1674,1794,2051,2690,3522] T_105
def N_107 : BT := n N_103 [7,w2,w4,w5,1911399,w0,w1,7192446] [1158,3522,3910] N_106
def N_108 : BT := n N_100 [7,w2,w4,w5,1837618,w0,w1] [6,42,66,97,918,938,1182,1186,1690,1810,1832,2070] N_107
def T_109 : BT := (n (n (n (n (n (n (s [7,w2,w4,w5,w0,4190271,6403412] [2,40,66,168,914,936,1178,2394,2984]) [7,w2,w4,w5,w0,4190271,6551005] [2,40,914,936,1178,2984,3032] (s [7,w2,w4,w5,w0,4190271,6551005,6551005] [3016])) [7,w2,w4,w5,w0,4190271,6551005,6553055] [3784] (n (s [7,w2,w4,w5,w0,4190271,6551005,6553085] [3784]) [7,w2,w4,w5,w0,4190271,6551005,6553565] [3784] e)) [7,w2,w4,w5,w0,4190271,6551005,7077341] [3016,3784] (n (n (s [7,w2,w4,w5,w0,4190271,6551005,7190390] [1154,2946,3522]) [7,w2,w4,w5,w0,4190271,6551005,8156909] [906,1154,3652,3788] e) [7,w2,w4,w5,w0,4190271,6551005,8386047] [3650,3786] (n (s [7,w2,w4,w5,w0,4190271,6551005,8388607] []) [7,w2,w4,w5,w0,4190271,7077341] [6,42,66,174,914,936,1178,3032] e))) [7,w2,w4,w5,w0,4192383,w1,6551005] [] (n (n (n (s [7,w2,w4,w5,w0,4192575,w1,6551005] []) [7,w2,w4,w5,w0,4192831,w1,6551005] [] e) [7,w2,w4,w5,w0,4193343,w1,6551005] [] (n (s [7,w2,w4,w5,w0,w1,6292956,6551005] []) [7,w2,w4,w5,w0,w1,6295036,6551005] [] e)) [7,w2,w4,w5,w0,w1,6295548,6403412] [1793] (n (n (s [7,w2,w4,w5,w0,w1,6295548,6551005] []) [7,w2,w4,w5,w0,w1,6295548,7077341] [] e) [7,w2,w4,w5,w0,w1,6321357,6551005] [3016] (n (s [7,w2,w4,w5,w0,w1,6321357,8158959] [3522]) [7,w2,w4,w5,w0,w1,6329616] [2,42,66,97,914,1178,1688,2201,2321,2842,2962,2984] e)))) [7,w2,w4,w5,w0,w1,6403412] [2,40,66,97,168,914,936,1178,2321,2984] (n (n (n (n (s [7,w2,w4,w5,w0,w1,6403412,6403412] []) [7,w2,w4,w5,w0,w1,6403412,6405500] [1793] (s [7,w2,w4,w5,w0,w1,6403412,6536534] [906])) [7,w2,w4,w5,w0,w1,6403412,6551005] [3784] (n (s [7,w2,w4,w5,w0,w1,6403412,6929749] [906]) [7,w2,w4,w5,w0,w1,6403412,7190390] [1154,2946,3522] e)) [7,w2,w4,w5,w0,w1,6403412,7601629] [1154,4104] (n (n (s [7,w2,w4,w5,w0,w1,6403412,7788474] [906,2826,3530]) [7,w2,w4,w5,w0,w1,6403412,8156909] [906,3652] e) [7,w2,w4,w5,w0,w1,6403412,8241014] [3522] (n (s [7,w2,w4,w5,w0,w1,6403412,8388607] []) [7,w2,w4,w5,w0,w1,6419933] [2,40,97,168,914,936,1178,2984] e))) [7,w2,w4,w5,w0,w1,6524926,6551005] [906,1154] (n (n (n (s [7,w2,w4,w5,w0,w1,6549981] [2,40,97,914,936,1178,2449,2984,3032]) [7,w2,w4,w5,w0,w1,6550749] [2,40,97,161,914,936,1178,2067,2984,3032] e) [7,w2,w4,w5,w0,w1,6550877] [2,40,97,169,914,936,1178,2321,2984,3032] (n (s [7,w2,w4,w5,w0,w1,6551004] [2,40,97,914,936,1178,2984]) [7,w2,w4,w5,w0,w1,6551005] [2,40,97,914,936,1178,2984,3032] e)) [7,w2,w4,w5,w0,w1,6551005,6551005] [3016] (n (n (s [7,w2,w4,w5,w0,w1,6551005,6553053] [3016,3784]) [7,w2,w4,w5,w0,w1,6551005,6553055] [3784] e) [7,w2,w4,w5,w0,w1,6551005,6553085] [3784] (n (s [7,w2,w4,w5,w0,w1,6551005,6553087] [3784]) [7,w2,w4,w5,w0,w1,6551005,6553597] [3784] e))))) [7,w2,w4,w5,w0,w1,6551005,6592306] [3522] (n (n (n (n (n (s [7,w2,w4,w5,w0,w1,6551005,6893565] [906,3784]) [7,w2,w4,w5,w0,w1,6551005,7077341] [3016,3784] (s [7,w2,w4,w5,w0,w1,6551005,7077343] [3784])) [7,w2,w4,w5,w0,w1,6551005,7077373] [3784] (n (s [7,w2,w4,w5,w0,w1,6551005,7091812] [2946]) [7,w2,w4,w5,w0,w1,6551005,7190390] [1154,2946,3522] e)) [7,w2,w4,w5,w0,w1,6551005,7192439] [3522] (n (n (s [7,w2,w4,w5,w0,w1,6551005,7192446] [1154,3522]) [7,w2,w4,w5,w0,w1,6551005,7323510] [1154,2946] e) [7,w2,w4,w5,w0,w1,6551005,7337983] [3650,3784,4033] (n (s [7,w2,w4,w5,w0,w1,6551005,8125917] [3016]) [7,w2,w4,w5,w0,w1,6551005,8130558] [3522] e))) [7,w2,w4,w5,w0,w1,6551005,8156909] [906,1154,3652,3788] (n (n (n (s [7,w2,w4,w5,w0,w1,6551005,8158959] [3652,3788]) [7,w2,w4,w5,w0,w1,6551005,8158973] [906,1154,3652,3788] e) [7,w2,w4,w5,w0,w1,6551005,8224493] [906,3788] (n (s [7,w2,w4,w5,w0,w1,6551005,8241014] [3522]) [7,w2,w4,w5,w0,w1,6551005,8255487] [3522,3650,3788,4033] e)) [7,w2,w4,w5,w0,w1,6551005,8385535] [3650,3786] (n (n (s [7,w2,w4,w5,w0,w1,6551005,8386047] [3650,3786]) [7,w2,w4,w5,w0,w1,6551005,8386303] [3650,3786] e) [7,w2,w4,w5,w0,w1,6551005,8386431] [3650] (n (s [7,w2,w4,w5,w0,w1,6551005,8386557] [3650,3786,4033]) [7,w2,w4,w5,w0,w1,6551005,8386558] [4033] e)))) [7,w2,w4,w5,w0,w1,6551005,8388607] [] (n (n (n (n (s [7,w2,w4,w5,w0,w1,6553053] [6,42,66,97,164,914,936,1178,2984,3032]) [7,w2,w4,w5,w0,w1,6553055,6553085] [] e) [7,w2,w4,w5,w0,w1,6553055,7077341] [3016] (n (s [7,w2,w4,w5,w0,w1,6553085,6553565] []) [7,w2,w4,w5,w0,w1,6553085,7077341] [3016] e)) [7,w2,w4,w5,w0,w1,6929749] [2,42,66,97,174,906,914,936,1178,1304,2321] (n (n (s [7,w2,w4,w5,w0,w1,7077341] [6,42,66,97,174,914,936,1178,3032]) [7,w2,w4,w5,w0,w1,7077341,7077341] [3016] e) [7,w2,w4,w5,w0,w1,7077341,7077343] [3784] (n (s [7,w2,w4,w5,w0,w1,7077341,7077373] [3784]) [7,w2,w4,w5,w0,w1,7077341,7190390] [1154,2946,3522] e))) [7,w2,w4,w5,w0,w1,7077341,7601629] [2888,3016] (n (n (n (s [7,w2,w4,w5,w0,w1,7077341,7788474] [906,2826,3530,4168]) [7,w2,w4,w5,w0,w1,7077341,8125917] [3016] e) [7,w2,w4,w5,w0,w1,7077341,8156909] [906,1154,3652,3788] (n (s [7,w2,w4,w5,w0,w1,7077341,8388607] []) [7,w2,w4,w5,w0,w1,8125917] [6,42,66,97,166,914,936,1178] e)) [7,w2,w4,w5,w0,4198337,6551005] [2,40,97,914,936,1178,1304,2984,3032] (n (n (s [7,w2,w4,w5,w0,4198338,6551005] [2,42,66,97,162,914,936,1178,2984,3032]) [7,w2,w4,w5,w0,4198340,6551005] [2,40,97,136,914,936,1178,1688,1697,3032] e) [7,w2,w4,w5,w0,4198352,6551005] [2,42,66,97,162,914,936,1178,1554,1569,2984,3032] (n (s [7,w2,w4,w5,w0,4198368,6551005] [6,42,66,97,166,914,936,1178,2984,3032]) [7,w2,w4,w5,w0,4263872,6551005] [2,40,97,136,1178,3032] e))))))
def T_110 : BT := (n (n (n (n (n (n (s [7,w2,w4,w5,w0,4427730,6033378,6551005] [906,1154]) [7,w2,w4,w5,w0,4427730,6295548,6551005] [906,1154,1538,2498] (s [7,w2,w4,w5,w0,4722624,6551005] [6,40,66,97,136,164,914,936,1178,3032])) [7,w2,w4,w5,w0,4796357,5394377,6551005] [906,1154] (n (s [7,w2,w4,w5,w0,4796357,6033378,6551005] [906]) [7,w2,w4,w5,w0,4796357,6295548,6551005] [906,1672] e)) [7,w2,w4,w5,w0,6033378,6295548,6551005] [2502] (n (n (s [7,w2,w4,w5,w0,6033378,6551005,6553565] []) [7,w2,w4,w5,3935806,6033378,6295548] [6,42,66,97,113,914,936,1178,1569,1697,1833,2344,2513,2984,3000,3281,3297] e) [7,w2,w4,w5,4190271,6288323,6551005] [2,40,97,914,936,1178,2984,3032] (n (s [7,w2,w4,1198219,1911399,w0,w1] [6,40,66,129,906,914,936,1368,2200,2841]) [7,w2,w4,1198219,w0,w1,6551005] [2,40,66,97,162,914,936,3032] e))) [7,w2,w4,1198221,1837606,w0,w1] [6,40,66,918,936,1174,1186,1688,1810,2200] (n (n (n (s [7,w2,w4,1198221,1911399,w0,w1] [6,40,67,914,1174,1186,2200,2840]) [7,w2,w4,1198221,1985195,w0,w1] [6,40,67,914,936,1174,1880,2200,2961] e) [7,w2,w4,1198221,1985199,w0,w1] [6,40,914,936,1170,2200] (n (s [7,w2,w4,1198221,w0,w1,6551005] [2,40,67,162,914,936,1170,1688,3032]) [7,w2,w4,1198233,1911399,w0,w1] [6,40,67,914,1174,2070,2200,2840] e)) [7,w2,w4,1198233,1985195,w0,w1] [2,40,67,914,936,1170,1880,2066,2961] (n (n (s [7,w2,w4,1198233,1985211,w0,w1] [2,40,66,914,936,1170,2066,2322,2962]) [7,w2,w4,1198233,w0,w1,6551005] [2,40,67,162,914,936,1170,1554,3032] e) [7,w2,w4,1198249,1911399,w0,w1] [6,40,67,918,1174,1186,2200,2840] (n (s [7,w2,w4,1198249,1985195,w0,3296445,w1] [1158,2382]) [7,w2,w4,1198249,1985195,w0,w1] [6,40,67,914,936,1174,2961] e)))) [7,w2,w4,1198249,w0,3935806,w1] [6,40,66,914,936,1174] (n (n (n (n (s [7,w2,w4,1198249,w0,w1,6551005] [6,40,67,166,914,936,1174,3032]) [7,w2,w4,1198253,1911399,w0,w1] [6,40,67,918,1174,1186,2184,2200,2840] e) [7,w2,w4,1199241,1838626,w0,w1] [6,40,66,129,918,936,1174,1186,1688,1810,3217] (n (s [7,w2,w4,1199241,1911399,w0,w1] [6,40,66,129,914,1174,1186,2200,2841,3217]) [7,w2,w4,1199241,1985195,w0,w1] [6,40,66,129,914,936,1174,1880,2961,3217] e)) [7,w2,w4,1199241,1986219,w0,w1] [6,40,66,129,914,936,1170,2961,3217] (n (n (s [7,w2,w4,1199241,w0,w1,6551005] [2,40,66,97,162,914,936,1170,2449,3032]) [7,w2,w4,1263753,1903138,w0,w1] [6,40,66,129,918,936,1174,1186,1688,1810] e) [7,w2,w4,1263753,1911399,w0,w1] [6,40,66,129,936,2200,2841] (n (s [7,w2,w4,1263753,1985195,w0,w1] [2,40,66,129,914,936,1170,1880,2961]) [7,w2,w4,1263753,2050731,w0,w1] [2,40,66,129,936,2961] e))) [7,w2,w4,1263753,w0,w1,6551005] [2,40,66,97,162,936,3032] (n (n (n (s [7,w2,w4,1263755,1911399,w0,w1] [6,40,66,129,2200,2841]) [7,w2,w4,1296793,w0,w1,6551005] [2,40,66,97,162,936,1554,2067,3032] e) [7,w2,w4,1296795,1296795,1911399,w0,w1] [] (n (s [7,w2,w4,1296795,1296795,w0,w1,6551005] []) [7,w2,w4,1296795,1796301,1911399,w0,w1] [] e)) [7,w2,w4,1296795,1796301,1985195,w0,w1] [1154] (n (n (s [7,w2,w4,1296795,1796301,2058991,w0,w1] []) [7,w2,w4,1296795,1796301,w0,w1,6551005] [] e) [7,w2,w4,1296795,1829343,1911399,w0,w1] [] (n (s [7,w2,w4,1296795,1829343,w0,w1,6551005] []) [7,w2,w4,1296795,1911399,1985195,w0,w1] [914,1602,2498,2710,2840,3479,3609] e))))) [7,w2,w4,1296795,1911399,2058991,w0,w1] [1602] (n (n (n (n (n (s [7,w2,w4,1296795,1911399,2092031,w0,w1] [1602]) [7,w2,w4,1296795,1911399,w0,2329918,w1] [1158,2185,2694] (s [7,w2,w4,1296795,1911399,w0,3296445,w1] [1158,2185])) [7,w2,w4,1296795,1911399,w0,3395007,w1] [2185] (n (s [7,w2,w4,1296795,1911399,w0,4190271] [6,40,66,1618,2070,2200,2898]) [7,w2,w4,1296795,1911399,w0,4190271,w1] [2882,3462,3592] e)) [7,w2,w4,1296795,1911399,w0,w1] [6,40,66,129,1618,2070,2200,2711,2841] (n (n (s [7,w2,w4,1296795,1911399,w0,w1,6295548] [2055,2185,2694,2824,3462,3592]) [7,w2,w4,1296795,1911399,w0,w1,6477208] [1602,3462,3592] e) [7,w2,w4,1296795,1911399,w0,w1,6551005] [1602,1672,3592,3784] (n (s [7,w2,w4,1296795,1911399,w0,w1,7788474] [1672,3918]) [7,w2,w4,1296795,1985195,w0,3296445,w1] [1154] e))) [7,w2,w4,1296795,1985195,w0,3935806,w1] [914,1218,1794,2051,2754,3138] (n (n (n (s [7,w2,w4,1296795,1985195,w0,w1,6551005] [1794,3784]) [7,w2,w4,1296795,1985195,w0,w1,7190390] [1154,1218,3522,3910] e) [7,w2,w4,1296795,2067250,w0,3935806,w1] [1672,1794,2051,2754,3138] (n (s [7,w2,w4,1296795,2067250,w0,w1,6551005] [1672,1794,3784]) [7,w2,w4,1296795,2083771,w0,3935806,w1] [1218,1794,2051,3138] e)) [7,w2,w4,1296795,2083771,w0,w1,6551005] [1218,1794,3784] (n (n (s [7,w2,w4,1296795,2098204,w0,w1,6551005] [1538,2050]) [7,w2,w4,1296795,w0,2329918,w1,6551005] [1154,2050] e) [7,w2,w4,1296795,w0,2698365,w1,6551005] [1539] (n (s [7,w2,w4,1296795,w0,3296445,w1,6551005] [1154]) [7,w2,w4,1296795,w0,3395007,w1,6551005] [] e)))) [7,w2,w4,1296795,w0,3935806,w1,6033378] [1539,2690,4034] (n (n (n (n (s [7,w2,w4,1296795,w0,3935806,w1,6551005] [1539]) [7,w2,w4,1296795,w0,4190271,w1,6551005] [2690] e) [7,w2,w4,1296795,w0,4190271,6551005] [2,40,66,162,1554,3032] (n (s [7,w2,w4,1296795,w0,w1,6295548,6551005] [1539,2050,2690]) [7,w2,w4,1296795,w0,w1,6477208] [2,40,97,1554,1688,2067,2201,2706,2840] e)) [7,w2,w4,1296795,w0,w1,6551005] [2,40,66,97,162,1554,2067,3032] (n (n (s [7,w2,w4,1296795,w0,w1,6551005,6551005] [3016]) [7,w2,w4,1296795,w0,w1,6551005,6553055] [3016,3784] e) [7,w2,w4,1296795,w0,w1,6551005,6553085] [3784] (n (s [7,w2,w4,1296795,w0,w1,6551005,7077341] [3016,3784]) [7,w2,w4,1296795,w0,w1,6551005,7091812] [1218,3458] e))) [7,w2,w4,1296795,w0,w1,6551005,7190390] [1154,3458,3522] (n (n (n (s [7,w2,w4,1296795,w0,w1,6551005,7601629] [3016]) [7,w2,w4,1296795,w0,w1,6551005,7601631] [3016] e) [7,w2,w4,1296795,w0,w1,6551005,7788474] [2824] (n (s [7,w2,w4,1296795,w0,w1,6551005,8156909] [1154,3652,3788]) [7,w2,w4,1296795,w0,w1,6551005,8388607] [] e)) [7,w2,w4,1296795,w0,w1,7077341] [2,40,66,97,174,1554,2067,3032] (n (n (s [7,w2,w4,1296795,w0,w1,7601629] [2,40,66,97,166,936,978,1554,2067]) [7,w2,w4,1722505,w0,w1,6551005] [6,40,66,97,166,914,1174,3032] e) [7,w2,w4,1796301,1985195,2067250,w0,w1] [] (n (s [7,w2,w4,1796301,1985195,w0,3296445,w1] [1158,2185]) [7,w2,w4,1796301,1985195,w0,3935806,w1] [1346] e))))))
def N_111 : BT := n T_109 [7,w2,w4,w5,w0,4427730,4796357,6551005] [1154] T_110
def T_112 : BT := (n (n (n (n (n (n (s [7,w2,w4,1796301,1985195,w0,w1,7190390] [1158,1346]) [7,w2,w4,1796301,2058991,w0,3296445,w1] [1154,2177] (s [7,w2,w4,1796301,2058991,w0,w1,7190390] [1154,3910])) [7,w2,w4,1796301,w0,3296445,w1,6551005] [1154,1665] (n (s [7,w2,w4,1796301,w0,w1,6551005,7190390] [1154,2946]) [7,w2,w4,1985195,1985195,w0,3296445,w1] [2382] e)) [7,w2,w4,1985195,1985195,w0,w1,6551005] [3784] (n (n (s [7,w2,w4,1985195,2058991,w0,3296445,w1] [2185,2380,2500]) [7,w2,w4,1985195,2058991,w0,3935806,w1] [1348,1730,1858,2500,3138] e) [7,w2,w4,1985195,2058991,w0,w1,6551005] [1348,3784] (n (s [7,w2,w4,1985195,2058991,w0,w1,7190390] [1730,1858,3910]) [7,w2,w4,1985195,2098204,w0,w1,6551005] [] e))) [7,w2,w4,1985195,w0,w0,3296445,w1] [] (n (n (n (s [7,w2,w4,1985195,w0,2329918,3296445,w1] [2433,3073]) [7,w2,w4,1985195,w0,2329918,3935806,w1] [1154,1602,2114,2433,2498,3073] e) [7,w2,w4,1985195,w0,2329918,w1,5394377] [2113,2497,2694,3841] (n (s [7,w2,w4,1985195,w0,2329918,w1,6033378] [1154,2115,2499,2694,3202,3841]) [7,w2,w4,1985195,w0,2329918,w1,6551005] [1154] e)) [7,w2,w4,1985195,w0,2329918,w1,7190390] [2114,2498] (n (n (s [7,w2,w4,1985195,w0,2355229,w1] [6,40,97,131,914,1186,2408,3055,3217]) [7,w2,w4,1985195,w0,2355229,w1,6033378] [3202] e) [7,w2,w4,1985195,w0,3296445,3296445,w1] [] (n (s [7,w2,w4,1985195,w0,3296445,3395007,w1] []) [7,w2,w4,1985195,w0,3296445,3894525,w1] [] e)))) [7,w2,w4,1985195,w0,3296445,3935806,w1] [1868,2498,3010,3857] (n (n (n (n (s [7,w2,w4,1985195,w0,3296445,4083391,w1] []) [7,w2,w4,1985195,w0,3296445,4190271] [6,40,130,914,1698,1902] e) [7,w2,w4,1985195,w0,3296445,4190271,w1] [] (n (s [7,w2,w4,1985195,w0,3296445,w1] [6,40,97,131,914,1569,1699,1902,3089]) [7,w2,w4,1985195,w0,3296445,w1,5394377] [2497] e)) [7,w2,w4,1985195,w0,3296445,w1,6033378] [2499] (n (n (s [7,w2,w4,1985195,w0,3296445,w1,6180843] [3918]) [7,w2,w4,1985195,w0,3296445,w1,6288323] [2433,4043] e) [7,w2,w4,1985195,w0,3296445,w1,6295548] [2433,3841] (n (s [7,w2,w4,1985195,w0,3296445,w1,6403412] [1870,3841]) [7,w2,w4,1985195,w0,3296445,w1,6551005] [] e))) [7,w2,w4,1985195,w0,3296445,w1,7190390] [2498,3089,3522,3841] (n (n (n (s [7,w2,w4,1985195,w0,3296445,w1,7491581] []) [7,w2,w4,1985195,w0,3296445,w1,7788474] [910,1288,1673,3530,3906] e) [7,w2,w4,1985195,w0,3296445,w1,8156909] [910,1543,3652] (n (s [7,w2,w4,1985195,w0,4083391,w1,6551005] []) [7,w2,w4,1985195,w0,4190271,w1,6551005] [] e)) [7,w2,w4,1985195,w0,4190271,5394377] [6,40,97,129,162,914,2082,3041,3290,3306] (n (n (s [7,w2,w4,1985195,w0,4190271,6551005] [6,40,166,914,1186,3032,3048]) [7,w2,w4,1985195,w0,w1,6295548,6551005] [] e) [7,w2,w4,1985195,w0,w1,6295548,7491581] [] (n (s [7,w2,w4,1985195,w0,w1,6403412,6551005] [3784]) [7,w2,w4,1985195,w0,w1,6403412,7601629] [] e))))) [7,w2,w4,1985195,w0,w1,6551005] [6,40,97,166,914,1186,3032,3048,3233] (n (n (n (n (n (s [7,w2,w4,1985195,w0,w1,6551005,6551005] [3016]) [7,w2,w4,1985195,w0,w1,6551005,6553055] [3784] (s [7,w2,w4,1985195,w0,w1,6551005,6553085] [3784])) [7,w2,w4,1985195,w0,w1,6551005,7077341] [3016] (n (s [7,w2,w4,1985195,w0,w1,6551005,7190390] [3522]) [7,w2,w4,1985195,w0,w1,6551005,7601629] [3016] e)) [7,w2,w4,1985195,w0,w1,6551005,7788474] [3530] (n (n (s [7,w2,w4,1985195,w0,w1,6551005,8156909] [1154,3652,3778]) [7,w2,w4,1985195,w0,w1,6551005,8388607] [] e) [7,w2,w4,1985195,w0,w1,6553085] [6,40,97,165,914,1186,3032,3048] (n (s [7,w2,w4,1985195,w0,w1,7491581] [6,40,97,162,914,1569,1699,2210]) [7,w2,w4,1985195,w0,w1,7601629] [6,40,97,166,914,1186,3032,3048,3233] e))) [7,w2,w4,1985195,w0,4427730,5394377] [6,40,97,130,162,914,1558,2411,2779] (n (n (n (s [7,w2,w4,1985195,w0,4427730,6033378] [6,40,97,130,914,1154,1174,1186,1558,2210,2411,2466,2771,3282]) [7,w2,w4,1985195,w0,5394377,6295548] [6,40,97,130,146,914,1698,1825,2520,3054] e) [7,w2,w4,2058991,w0,3296445,w1] [6,40,97,129,914,1569,1665,1697,1892,2833,3089] (n (s [7,w2,w4,2058991,w0,w1,7190390] [6,66,97,914,2193,2770,3030,3046,3233]) [7,w2,w4,2098204,w0,w1,6551005,7190390] [] e)) [7,w2,w4,w0,2329918,w1,6551005,7190390] [] (n (n (s [7,w2,w4,w0,3296445,w1,5394377,6551005] []) [7,w2,w4,w0,3296445,w1,6403412] [2,40,65,99,914,1185,1315,2321,2961] e) [7,w2,w4,w0,3296445,w1,6551005,7190390] [] (n (s [7,w2,w4,w0,4190271,w1,6551005,7190390] []) [7,w2,w4,w0,4190271,6551005,7190390] [2,130,914,2210,2770,3282] e)))) [7,w2,w4,w0,w1,6295548,6551005,7190390] [] (n (n (n (n (s [7,w2,w4,w0,w1,6403412,6551005] [2,65,162,914,3105]) [7,w2,w4,w0,w1,6403412,6551005,7190390] [3266,3522] e) [7,w2,w4,w0,w1,6403412,7601629] [2,65,166,914,3105] (n (s [7,w2,w4,w0,w1,6477208,7190390] [2,40,65,130,168,914,1681,2200,2210,2770,3282]) [7,w2,w4,w0,w1,6551005,6551005,7190390] [] e)) [7,w2,w4,w0,w1,6551005,6553055,7190390] [4162] (n (n (s [7,w2,w4,w0,w1,6551005,6553085,7190390] [4162]) [7,w2,w4,w0,w1,6551005,7077341,7190390] [3202,4162] e) [7,w2,w4,w0,w1,6551005,7190390] [2,65,130,914,2210,2770,3282] (n (s [7,w2,w4,w0,w1,6551005,7190390,7337983] [3650,3905]) [7,w2,w4,w0,w1,6551005,7190390,7601629] [3970] e))) [7,w2,w4,w0,w1,6551005,7190390,7788474] [3530] (n (n (n (s [7,w2,w4,w0,w1,6551005,7190390,8388607] []) [7,w2,w4,w0,w1,6551005,7323510] [2,40,65,130,172,914] e) [7,w2,w4,w0,w1,6551005,8241014] [6,40,65,134,168,914,2770,3282] (n (s [7,w2,600135,1198219,w3,w0,w1] [4,40,129,916,936,1180,1538,1556,1692,1812,1832]) [7,w2,600135,1296795,w3,w0,w1] [4,40,68,129,978,1556,1684,2068,2709] e)) [7,w2,600135,w3,w0,w1,7190390] [4,40,97,170,1300,2770,2980,3030] (n (n (s [7,w2,600141,1296795,w3,w0,w1] [4,41,68,936,1688,2068,2708]) [7,w2,600141,w3,w0,3296445,w1] [4,40,916,1300,2340] e) [7,w2,600141,w3,w0,w1,7190390] [4,41,170,916,1300,2770,2980,3030] (n (s [7,w2,600149,1198233,w3,w0,w1] [4,40,916,936,1180,1688,1832,2068]) [7,w2,600149,1296795,w3,w0,w1] [4,41,1688,2068,2708] e))))))
def T_113 : BT := (n (n (n (n (n (n (s [7,w2,600149,w3,w0,w1,7190390] [4,45,170,916,1300,1556,2770,3030]) [7,w2,600157,1296795,w3,w0,w1] [4,41,936,1688,2068,2708] (s [7,w2,601157,1199241,w3,w0,w1] [4,40,129,916,936,1180,1692,1812,1832,3217])) [7,w2,601157,1296795,w3,w0,w1] [4,40,68,129,936,1688,2068,2709,3217] (n (s [7,w2,601157,w3,w0,w1,7190390] [4,40,97,170,916,1300,2449,2770,2980,3030]) [7,w2,631126,764247,w3,w0,w1,7190390] [] e)) [7,w2,633175,w3,w0,w1,7190390] [4,44,97,170,978,1234,1300,1556,2069,2770,3030] (n (n (s [7,w2,657411,764247,w3,1985195,w0,w1] [970,1734,2817]) [7,w2,731205,1296795,w3,w0,w1] [4,40,129,1688,2068,2709] e) [7,w2,731205,w3,1985195,w0,w1] [12,44,129,1308,1382,2961] (n (s [7,w2,731205,w3,w0,w1,7190390] [4,44,97,170,1300,3030]) [7,w2,731207,w3,1985195,w0,w1] [12,44,129,1308,1382,2961] e))) [7,w2,764247,764247,1296795,w3,w0,w1] [] (n (n (n (s [7,w2,764247,764247,w3,1985195,w0,w1] [1734]) [7,w2,764247,764247,w3,w0,w1,7190390] [] e) [7,w2,764247,1296795,1796301,w3,w0,w1] [1864] (n (s [7,w2,764247,1296795,1829343,w3,w0,w1] []) [7,w2,764247,1296795,w3,1911399,w0,w1] [964,2184] e)) [7,w2,764247,1296795,w3,2067250,w0,w1] [900,1156,1602,2052,2184] (n (n (s [7,w2,764247,1296795,w3,2075511,w0,w1] [968,2184]) [7,w2,764247,1296795,w3,w0,2329918,w1] [900,1156,2114,2692] e) [7,w2,764247,1296795,w3,w0,2698365,w1] [] (n (s [7,w2,764247,1296795,w3,w0,2862463,w1] []) [7,w2,764247,1296795,w3,w0,3935806,w1] [1672,2053,2692] e)))) [7,w2,764247,1296795,w3,w0,4190271] [4,40,1556,1688,2068] (n (n (n (n (s [7,w2,764247,1296795,w3,w0,4190271,w1] [3460]) [7,w2,764247,1296795,w3,w0,w1] [4,40,129,1556,1688,2068,2709] e) [7,w2,764247,1296795,w3,w0,w1,6295548] [4,2053,2692,3460] (n (s [7,w2,764247,1296795,w3,w0,w1,6551005] [1672,3784]) [7,w2,764247,1296795,w3,w0,w1,7091812] [3460] e)) [7,w2,764247,1296795,w3,w0,w1,7190390] [3460,3910] (n (n (s [7,w2,764247,1296795,w3,w0,w1,8156909] [900,1156,3652,3788]) [7,w2,764247,1296795,w0,w1,6551005] [40,97,2065,3032] e) [7,w2,764247,1796301,w3,1985195,w0,w1] [2380] (n (s [7,w2,764247,1796301,w3,w0,3296445,w1] [2185,2888,3016]) [7,w2,764247,1796301,w3,w0,w1,7190390] [3460] e))) [7,w2,764247,1829343,w3,1985195,w0,w1] [1868,2380] (n (n (n (s [7,w2,764247,1829343,w3,w0,3296445,w1] [2888,3016]) [7,w2,764247,1829343,w3,w0,w1,7190390] [] e) [7,w2,764247,w3,1911399,w0,w1,7190390] [964,1218] (n (s [7,w2,764247,w3,1985195,2067250,w0,w1] [1218,2188]) [7,w2,764247,w3,1985195,2075511,w0,w1] [972,2188] e)) [7,w2,764247,w3,1985195,2092031,w0,w1] [] (n (n (s [7,w2,764247,w3,1985195,w0,2329918,w1] [908,1540,2305,2700]) [7,w2,764247,w3,1985195,w0,2698365,w1] [908,2305] e) [7,w2,764247,w3,1985195,w0,2862463,w1] [2305,3014] (n (s [7,w2,764247,w3,1985195,w0,4190271] [12,44,1308,1382,1626,2076,3036]) [7,w2,764247,w3,1985195,w0,4190271,w1] [3020,3468] e))))) [7,w2,764247,w3,1985195,w0,w1] [12,44,129,1308,1382,1626,2076,2717,2961] (n (n (n (n (n (s [7,w2,764247,w3,1985195,w0,w1,6295548] [2061,2305,2700,3468]) [7,w2,764247,w3,1985195,w0,w1,6403412] [1610,3468] (s [7,w2,764247,w3,1985195,w0,w1,6551005] [1288,3912])) [7,w2,764247,w3,1985195,w0,w1,7190390] [1610,3782] (n (s [7,w2,764247,w3,2067250,2083771,w0,w1] [1218]) [7,w2,764247,w3,2067250,w0,w1,7190390] [1218] e)) [7,w2,764247,w3,2075511,w0,w1,7190390] [] (n (n (s [7,w2,764247,w3,2083771,w0,w1] [4,44,129,1382,2068,2709,2961]) [7,w2,764247,w3,2098228,w0,w1,7190390] [1540,2052] e) [7,w2,764247,w3,w0,2329918,w1,7190390] [900,2052,3460] (n (s [7,w2,764247,w3,w0,2698365,w1,7190390] [900,3460]) [7,w2,764247,w3,w0,2862463,w1,7190390] [] e))) [7,w2,764247,w3,w0,3296445,w1,5394377] [1541,2692,4040] (n (n (n (s [7,w2,764247,w3,w0,3296445,w1,7190390] [1541]) [7,w2,764247,w3,w0,3935806,w1,7190390] [1541] e) [7,w2,764247,w3,w0,4190271,w1,7190390] [2692] (n (s [7,w2,764247,w3,w0,4190271,7190390] [4,44,170,1556,3030]) [7,w2,764247,w3,w0,w1,6295548,7190390] [1541,2052,2692] e)) [7,w2,764247,w3,w0,w1,6403412] [4,97,1382,1556,2069,2321,2692,2708] (n (n (s [7,w2,764247,w3,w0,w1,6551005,7190390] []) [7,w2,764247,w3,w0,w1,7091812] [4,36,97,1172,1300,1556,2069,2708] e) [7,w2,764247,w3,w0,w1,7190390] [4,44,97,170,1556,2069,3030] (n (s [7,w2,764247,w3,w0,w1,7190390,7190390] [3014]) [7,w2,764247,w3,w0,w1,7190390,7192439] [3782] e)))) [7,w2,764247,w3,w0,w1,7190390,7192446] [3782] (n (n (n (n (s [7,w2,764247,w3,w0,w1,7190390,7323510] [2754,3014,3782]) [7,w2,764247,w3,w0,w1,7190390,7323511] [3782] e) [7,w2,764247,w3,w0,w1,7190390,7624360] [972,3460] (n (s [7,w2,764247,w3,w0,w1,7190390,7788474] [900,2692,3460,3530,3790]) [7,w2,764247,w3,w0,w1,7190390,8156909] [900,2692,3652] e)) [7,w2,764247,w3,w0,w1,7190390,8241014] [3014] (n (n (s [7,w2,764247,w3,w0,w1,7190390,8388607] []) [7,w2,764247,w3,w0,w1,7323510] [4,44,97,172,1238,1556,2069,3030] e) [7,w2,764247,w3,w0,w1,8241014] [4,44,97,168,1300,1556,2069] (n (s [7,w2,764247,1985195,w0,3296445,w1] [14,40,97,129,1242,1537,1569,1697,1902,2280,2408,2705,3089]) [7,w2,764247,1985195,w0,3935806,w1] [12,40,97,129,1242,1537,1569,1697,1902,2278,2705,3089] e))) [7,w2,764247,1985195,w0,w1,6551005] [40,97,1242,2065,3032,3048,3233] (n (n (n (s [7,w2,764247,1985195,w0,w1,7190390] [2,40,97,168,1242,2065,3030,3046,3233]) [7,w2,764247,w0,w1,6551005,7190390] [2,40,65,168,1553] e) [7,w2,1796301,w3,w0,2100285,w1] [4,97,129,916,1300,1569,1634,1697,1829,1894,2340,2433,2449,2996,3089,3153] (n (s [7,w2,1796301,w3,w0,2698365,3296445,w1] [900,2433,2888,3073]) [7,w2,1796301,w3,w0,2698365,w1,5394377] [900,3208,3841] e)) [7,w2,1796301,w3,w0,2698365,w1,7190390] [900] (n (n (s [7,w2,1796301,w3,w0,w1,7190390,7192439] [3650]) [7,w2,1796301,w3,w0,w1,7190390,7788474] [900] e) [7,w2,1796301,w3,w0,w1,8386558] [4,97,916,1300,3028,3281] (n (s [7,w2,1796301,w3,w0,4198337] [4,20,97,916,1266,1300,1332,1396,1650,1844,1910,2163,2289,2356,2423]) [7,w2,1796301,w3,w0,4796357,5394377] [4,97,136,900,916,1300,2088,2257,2273,2348,2472,2905,2921,2980,3288] e))))))
def N_114 : BT := n T_112 [7,w2,600149,w3,1985195,w0,w1] [4,45,916,1308,2068] T_113
def N_115 : BT := n N_111 [7,w2,w4,1796301,1985195,w0,w1,6551005] [1732] N_114
def T_116 : BT := (n (n (n (n (n (n (s [7,w2,w3,2067250,2075511,w0,w1,7190390] [962]) [7,w2,w3,2067250,w0,w1,7190390,7788474] [962,2952] (s [7,w2,w3,2075511,2083771,w0,w1] [4,72,129,2068,2709,2833])) [7,w2,w3,2075511,w0,w1,7190390] [4,72,97,170,1556,2069,2193,2852] (n (s [7,w2,w3,2098228,w0,w1,7190390,7788474] []) [7,w2,w3,w0,2329918,w1,7190390,7788474] [] e)) [7,w2,w3,w0,2698365,w1,4796357,7190390] [] (n (n (s [7,w2,w3,w0,2698365,w1,7190390,7788474] []) [7,w2,w3,w0,4190271,w1,7190390,7788474] [] e) [7,w2,w3,w0,4190271,7190390,7788474] [4,138,162,2088,2130,2220,2262,2778,2852,2910] (n (s [7,w2,w3,w0,w1,6295548,7190390,7788474] []) [7,w2,w3,w0,w1,6403412,7788474] [4,65,140,162,1681,2220,2778] e))) [7,w2,w3,w0,w1,6551005,7190390,7788474] [2824,4040] (n (n (n (s [7,w2,w3,w0,w1,6592306,7190390,7788474] [2114,2246]) [7,w2,w3,w0,w1,7190390,7190390,7788474] [2114,2246] e) [7,w2,w3,w0,w1,7190390,7192439,7788474] [2754,2886] (n (s [7,w2,w3,w0,w1,7190390,7192446,7788474] [2754,2886]) [7,w2,w3,w0,w1,7190390,7323510,7788474] [2114,2246,2886,3208] e)) [7,w2,w3,w0,w1,7190390,7788474] [4,65,138,162,2088,2130,2220,2262,2778,2852,2910] (n (n (s [7,w2,w3,w0,w1,7190390,7788474,8386558] [3652,3905]) [7,w2,w3,w0,w1,7190390,7788474,8388607] [] e) [7,w2,w3,w0,w1,7190390,7856058] [4,65,138,164,2130,2212,2262,2910] (n (s [7,w2,1911399,1985195,2067250,w0,w1] [4,40,129,978,1242,1896,2068,2709,3089]) [7,w2,1911399,1985195,w0,3935806,w1] [4,40,97,129,936,1569,1766,1902,2408,3089] e)))) [7,w2,1911399,1985195,w0,w1,6551005] [4,40,97,164,936,3032,3048,3233] (n (n (n (n (s [7,w2,1911399,w0,2698365,w1,7190390] [6,65,97,168,1185,1382,2321,2770]) [7,w2,1911399,w0,3935806,w1,7190390] [4,40,65,97,170,1185,1382,2321,2770] e) [7,w2,1911399,w0,w1,6551005,7190390] [6,40,65,132,168,2465,2770] (n (s [7,w2,1911399,w0,w1,7190390,7788474] [4,40,65,138,162,2130,2778,2910,2926,3105]) [7,w2,w0,w1,6551005,7190390,7788474] [33,136,2088,2130,2778,3160,3176] e)) [8,0,w2,w4,w5,w3,w0,4190271] [36,74,98,1170,1300,1322,1562,1692,1698,2068,2334,2454,2472] (n (n (s [8,0,w2,w4,w5,w3,w0,4190271,w1] []) [8,0,w2,w4,w5,w3,w0,w1] [36,74,98,161,1170,1300,1322,1562,1692,1698,2068,2334,2454,2472,3473] e) [8,0,w2,w4,w5,w3,w0,w1,6551005] [2312,4808] (n (s [8,0,w2,w4,w5,w0,w1,6551005] [34,72,129,1170,1298,1320,1562,1690,2705,3880,3928]) [8,2048,2049,w2,w4,w5,w3,w0,w1] [1284,3585] e))) [8,2048,2052,w2,w4,w5,w3,w0,w1] [1284,2178] (n (n (n (s [8,2048,3072,w2,w4,w5,w3,w0,w1] [1284,1674,2178]) [8,2048,67584,w2,w4,w5,w3,w0,w1] [2178,3585] e) [8,2048,w2,w4,w5,w3,w0,w1] [36,74,98,161,1170,1300,1322,1562,1692,1698,2068,2334,2454,2472,3473] (n (s [8,2049,2049,w2,w4,w5,w3,w0,w1] [1156,3457]) [8,2049,2050,w2,w4,w5,w3,w0,w1] [1158,1538,1672,1804,2050,2308,2690,2946,3080,3459,3585,4354] e)) [8,2049,2052,w2,w4,w5,w3,w0,w1] [1156,1284] (n (n (s [8,2049,2064,w2,w4,w5,w3,w0,w1] [898,1154,1538,1672,2050,2690,3458,4354]) [8,2049,3072,w2,w4,w5,w3,w0,w1] [1156,1284,1672,3457] e) [8,2049,67584,w2,w4,w5,w3,w0,w1] [1154,3457,3585] (n (s [8,2049,w2,231699,w4,w5,w3,w0,w1] [900,964,1284,1676,1800,2180,3457]) [8,2049,w2,w4,w4,w5,w3,w0,w1] [902,1154,1284,2050,2690,3459,4354] e))))) [8,2049,w2,w4,764247,w5,w3,w0,w1] [900,964,1224,1668,1800,2180,3457] (n (n (n (n (n (s [8,2049,w2,w4,w5,1796301,w3,w0,w1] [900,1224,1292,1668,2180,2312,2952,3457]) [8,2049,w2,w4,w5,w3,2067250,w0,w1] [900,1154,1538,2242,2690,2952,3459,4354] (s [8,2049,w2,w4,w5,w3,w0,2100285,w1] [900,2689,2753,4097])) [8,2049,w2,w4,w5,w3,w0,2329918,w1] [900,1292,1668,2689,4369,4500,5009] (n (s [8,2049,w2,w4,w5,w3,w0,2698365,w1] [900,1154,1292,1538,2312,2689,3458,4354]) [8,2049,w2,w4,w5,w3,w0,4190271] [2,36,72,900,932,1170,1300,1320,1562,1692,1816,2068,2332,2452,2472] e)) [8,2049,w2,w4,w5,w3,w0,4190271,w1] [900,2689] (n (n (s [8,2049,w2,w4,w5,w3,w0,w1] [2,36,72,161,900,932,1170,1300,1320,1562,1692,1816,2068,2332,2452,2472,2689,2721,3473]) [8,2049,w2,w4,w5,w3,w0,w1,6295548] [900,1320,2068,2332,2452,2689,2849,3237,4004,4808] e) [8,2049,w2,w4,w5,w3,w0,w1,6551005] [900,2312,2689,4808] (n (s [8,2049,w2,w4,w5,w3,w0,w1,7190390] [900,1154,1538,1668,2689,4354,4932]) [8,2049,w2,w4,w5,w3,w0,w1,8386558] [900,1154,1538,2689,4808,4932,5185] e))) [8,2049,w2,w4,w5,w3,w0,4198337] [36,72,161,900,932,1170,1300,1320,1562,1692,1816,2068,2332,2452,2472] (n (n (n (s [8,2049,w2,w4,w5,1837603,w0,w1] [36,72,161,898,1170,1300,1320,1562,1692,1816,2328,2472,2689,2721,3473]) [8,2049,w2,w4,w5,1911399,w0,w1] [36,72,136,161,898,1170,1562,1684,1816,2689,2721,2968,3473,3737] e) [8,2049,w2,w4,w5,w0,w1,6551005] [72,129,898,1170,1320,1562,1688,1816,2049,2081,2705,3880,3928] (n (s [8,2049,w2,w4,1296795,w3,w0,w1] [2,36,72,100,161,932,978,1154,1170,1284,1300,1538,1554,1816,2050,2068,2130,2260,2324,2691,2706,2721,2770,2836,3458,3475,3538,3605]) [8,2049,w2,w4,1796301,w3,w0,w1] [2,36,72,161,932,1284,1300,1684,2068,2324,2388,2452,2691,2706,2721,3458,3475,3729,3793] e)) [8,2049,w2,w4,w3,w0,w1,7190390] [2,36,129,902,932,978,1154,1170,1300,1538,1556,1618,1812,2051,2066,2081,2130,2690,2707,2770,3474,3538,3876,3924] (n (n (s [8,2049,w2,1796301,w3,w0,w1] [36,52,129,145,932,1300,1556,1588,1812,1844,1908,2049,2081,2484,2548,2705,2737,2865,2929,2993,3057,3125,3189]) [8,2052,2052,w2,w4,w5,w3,w0,w1] [1156] e) [8,2052,2056,w2,w4,w5,w3,w0,w1] [1164,1284,1544,2056,2696,3464,4360] (n (s [8,2052,2064,w2,w4,w5,w3,w0,w1] [1154,1538,2050,2690,3458,4354]) [8,2052,2112,w2,w4,w5,w3,w0,w1] [1157,1284,1537,2049,2689,3457,4353] e)))) [8,2052,2176,w2,w4,w5,w3,w0,w1] [897,1165,1284,1545,2057,2697,3465,4361] (n (n (n (n (s [8,2052,2304,w2,w4,w5,w3,w0,w1] [897,1155,1539,2051,2691,3459,4355]) [8,2052,3072,w2,w4,w5,w3,w0,w1] [1156,1284,2050] e) [8,2052,67584,w2,w4,w5,w3,w0,w1] [1154,2050] (n (s [8,2052,133120,w2,w4,w5,w3,w0,w1] [904,1162,1544,2056,2696,3464,4360]) [8,2052,w2,231702,w4,w5,w3,w0,w1] [900,964,1284,1668,2180] e)) [8,2052,w2,w4,w4,w5,w3,w0,w1] [902,1154,1284,2050,2690,3458,4354] (n (n (s [8,2052,w2,w4,764247,w5,w3,w0,w1] [900,964,1668,2050]) [8,2052,w2,w4,w5,1198221,w3,w0,w1] [910,1162,1538,1602,1668,2058,2180,2698,3466,4362] e) [8,2052,w2,w4,w5,1296795,w3,w0,w1] [900,972,1160,1538,1602,2056,2180,2696,3464,4360] (n (s [8,2052,w2,w4,w5,1796301,w3,w0,w1] [900,1538,2180]) [8,2052,w2,w4,w5,w3,2067250,w0,w1] [900,1154,1538,2242,2690,3458,4354] e))) [8,2052,w2,w4,w5,w3,w0,w0,w1] [900,1538] (n (n (n (s [8,2052,w2,w4,w5,w3,w0,2329918,w1] [900,1284,1538,1668]) [8,2052,w2,w4,w5,w3,w0,2698365,w1] [900,1154,1284,1538,2690,3458,4354] e) [8,2052,w2,w4,w5,w3,w0,3296445,w1] [900,1162,1538,1668,2698,3466,4362] (n (s [8,2052,w2,w4,w5,w3,w0,4190271] [10,36,900,932,1170,1300,1538,1562,1684,2068,2324,2452]) [8,2052,w2,w4,w5,w3,w0,4190271,w1] [900,1538] e)) [8,2052,w2,w4,w5,w3,w0,w1] [11,36,900,932,1170,1300,1538,1562,1684,2068,2324,2452,3473] (n (n (s [8,2052,w2,w4,w5,w3,w0,w1,4198340] [900,1153,1538,2689,4353]) [8,2052,w2,w4,w5,w3,w0,w1,4427730] [900,1153,1284,1538,1668,2689,4353] e) [8,2052,w2,w4,w5,w3,w0,w1,4796357] [900,1155,1284,1538,2691,4355] (n (s [8,2052,w2,w4,w5,w3,w0,w1,5394377] [900,1163,1538,1668,2699,4363]) [8,2052,w2,w4,w5,w3,w0,w1,6288323] [900,1153,1538,2689,4353] e))))))
def T_117 : BT := (n (n (n (n (n (n (s [8,2052,w2,w4,w5,w3,w0,w1,6551005] [900,1538]) [8,2052,w2,w4,w5,w3,w0,w1,7190390] [900,1154,1538,1602,1668,2690,4354,4932] (s [8,2052,w2,w4,w5,w3,w0,w1,7788474] [900,1162,1284,1538,2698,4362,4932])) [8,2052,w2,w4,w5,w3,w0,w1,8386555] [900,1163,1538,2699,4932] (n (s [8,2052,w2,w4,w5,w3,w0,4198340] [36,900,932,1170,1300,1538,1562,1684,2068,2324,2452]) [8,2052,w2,w4,w5,w3,2698365,w1] [3,36,932,1300,1538,1562,1684,2068,2452,3457,3473] e)) [8,2052,w2,w4,w5,w3,w1,6288323] [11,36,900,932,977,1153,1171,1300,1538,1562,1617,1684,2068,2129,2324,2452,2689,2705,2769,3473,3537] (n (n (s [8,2052,w2,w4,w5,1837606,w0,w1] [36,898,1170,1300,1562,1684]) [8,2052,w2,w4,w5,1911399,w0,w1] [1,36,898,1170,1562,1684,3473] e) [8,2052,w2,w4,w5,1985195,w0,w1] [9,36,898,984,1160,1170,1562,1624,2056,2072,2136,2696,2712,3464,3481,3544] (n (s [8,2052,w2,w4,w5,w0,w1,6551005] [9,898,1170,1562,2705]) [8,2052,w2,w4,1198221,w3,w0,w1] [2,36,900,932,978,1154,1170,1300,1538,1554,1684,2068,2130,2324,2452,2690,2706,3458,3474,3538] e))) [8,2052,w2,w4,1296795,w3,w0,w1] [3,36,100,902,932,978,1154,1170,1538,1554,1618,2050,2068,2130,2324,2690,2706,2836,3458,3475,3538,3604] (n (n (n (s [8,2052,w2,w4,w3,w0,w1,7190390] [3,36,902,932,978,1154,1170,1300,1538,1556,1618,1812,2050,2066,2690,2707,2770,3458,3474,3876,3924]) [8,2052,w2,764247,w5,w3,w0,w1] [11,36,68,910,932,986,1162,1178,1544,1562,1626,2058,2068,2138,2698,2714,2836,3466,3483,3546,3604] e) [8,2052,w2,w5,w3,w0,2698365,w1] [10,36,910,932,1160,1178,1300,1546,1556,1812,3108,3466,3483] (n (s [8,2052,w2,w5,w3,w0,w1,7788474] [11,36,910,932,986,1160,1178,1242,1300,1546,1556,1626,1812,2058,2074,2698,2715,2778,3482,3546,3876,3924]) [8,2053,w2,w4,w5,w3,w0,3296445,w1] [900,1162,1538,1668,2697,3466,4362] e)) [8,2053,w2,w4,w5,w3,w0,w1] [11,36,900,932,1170,1300,1538,1562,1684,2068,2324,2452,2689,3473,3793] (n (n (s [8,2060,w2,w4,w5,1796301,w3,w0,w1] [900,1162,1538,2180,3720]) [8,2060,w2,w4,w5,w3,w0,w1] [3,36,72,900,932,1162,1170,1192,1300,1320,1538,1562,1624,1692,2068,2332,2452,2472,2968,3112,3473] e) [8,2068,w2,w4,764247,w5,w3,w0,w1] [900,962,1162,1666,2050,3586] (n (s [8,2068,w2,w4,w5,w3,w0,w1] [13,34,98,900,930,978,1162,1170,1298,1538,1562,1570,1682,1698,2068,2450,2834,2978,3473]) [8,2068,w2,764247,w5,w3,w0,w1] [11,34,910,986,1162,1178,1544,1562,1626,2058,2068,2138,2698,2714,3466,3483,3546] e)))) [8,2116,w2,w4,w5,w3,w0,w1] [10,36,161,900,932,1170,1300,1538,1562,1684,2068,2324,2452,2689,2721,2977,3473,3537,3729] (n (n (n (n (s [8,2116,w2,w4,w5,w3,w0,w1,6295548] [900,1538,2068,2689,2945]) [8,3072,3072,w2,w4,w5,w3,w0,w1] [1156,1546,2050] e) [8,3072,67584,w2,w4,w5,w3,w0,w1] [1154,2050,2178,3585] (n (s [8,3072,w2,232722,w4,w5,w3,w0,w1] [900,964,1284,1544,1678,1802,2182,2306]) [8,3072,w2,w4,764247,w5,w3,w0,w1] [900,964,1162,1226,1668,1802,2050] e)) [8,3072,w2,w4,w5,1796301,w3,w0,w1] [900,1162,1538,2180] (n (n (s [8,3072,w2,w4,w5,w3,w0,w0,w1] [900,1162,1538]) [8,3072,w2,w4,w5,w3,w0,2329918,w1] [900,1162,1294,1538,1670] e) [8,3072,w2,w4,w5,w3,w0,4190271] [36,74,98,900,932,1162,1170,1194,1300,1322,1538,1562,1570,1692,1698,2068,2334,2454,2472] (n (s [8,3072,w2,w4,w5,w3,w0,4190271,w1] [900,1162,1538]) [8,3072,w2,w4,w5,w3,w0,w1] [36,74,98,161,900,932,1162,1170,1194,1300,1322,1538,1562,1570,1692,1698,2068,2334,2454,2472,3473,4113] e))) [8,3072,w2,w4,w5,w3,w0,w1,6295548] [900,1162,1538,2753,4993] (n (n (n (s [8,3072,w2,w4,w5,w3,w0,w1,6551005] [900,1162,1538,2312,4808]) [8,3072,w2,w4,w5,w3,w0,w1,8385535] [900,1162,1538,4674,4810,4932,5185] e) [8,3072,w2,w4,w5,w3,w0,6295548] [36,74,98,161,900,932,1162,1170,1194,1300,1322,1538,1562,1570,1692,1698,2068,2334,2454,2472,2914,2978,3114,3176,3236,3302] (n (s [8,3072,w2,w4,w5,w3,6295548] [36,52,74,90,98,114,900,932,1162,1170,1194,1202,1300,1322,1538,1562,1570,1594,1692,1698,1720,1784,2068,2100,2226,2290,2334,2356,2420,2454,2472,2492,2556,2930,2994,3130,3192,3252,3318]) [8,3072,w2,w4,w5,1838626,w0,w1] [38,74,98,161,898,930,1160,1170,1192,1302,1322,1562,1694,1698,2330,2450,2472,3473,4113] e)) [8,3072,w2,w4,w5,1911399,w0,w1] [38,74,98,136,161,898,930,1160,1170,1192,1298,1562,1686,2968,3473,3737,4113] (n (n (s [8,3072,w2,w4,w5,w0,w1,6551005] [34,72,129,898,930,1160,1170,1192,1298,1320,1562,1690,2705,3217,3880,3928]) [8,3076,w2,w4,w5,w3,w0,w1] [11,36,900,932,1162,1170,1300,1538,1562,1684,2068,2324,2452,3473] e) [8,3076,w2,w4,w5,w3,w0,w1,4796357] [900,1163,1284,1538,2691,4355] (n (s [8,67584,67584,w2,w4,w5,w3,w0,w1] [2050,3457]) [8,67584,133120,w2,w4,w5,w3,w0,w1] [1160,1544,2056,2696,3465,3585,4360] e))))) [8,67584,w2,w2,w4,w5,w3,w0,w1] [2178,3457] (n (n (n (n (n (s [8,67584,w2,w4,764247,w5,w3,w0,w1] [962,1666,2050,2178,3457]) [8,67584,w2,w4,1050624,w5,w3,w0,w1] [908,1164,1540,1666,2060,2178,2702,3469,3841,4364] (s [8,67584,w2,w4,w5,1263753,w3,w0,w1] [904,1160,1538,1602,1666,2056,2178,2434,2696,3465,4360])) [8,67584,w2,w4,w5,1296795,w3,w0,w1] [904,962,1160,1538,1602,2056,2178,2434,2696,3465,4360] (n (s [8,67584,w2,w4,w5,1796301,w3,w0,w1] [1538,1666,2178,3457]) [8,67584,w2,w4,w5,w3,1985195,w0,w1] [908,1164,1538,1606,2120,2700,3074,3469,4364] e)) [8,67584,w2,w4,w5,w3,w0,2165820,w1] [1538,2689,2753,4097] (n (n (s [8,67584,w2,w4,w5,w3,w0,2329918,w1] [1538,1666,2689]) [8,67584,w2,w4,w5,w3,w0,3296445,w1] [906,1162,1538,1666,2689,3464,4362] e) [8,67584,w2,w4,w5,w3,w0,4190271] [12,34,98,1170,1298,1538,1560,1570,1682,1698,2070,2450] (n (s [8,67584,w2,w4,w5,w3,w0,4190271,w1] [1538,2689]) [8,67584,w2,w4,w5,w3,w0,w1] [12,34,98,161,1170,1298,1538,1560,1570,1682,1698,2070,2450,2689,2721,3473] e))) [8,67584,w2,w4,w5,w3,w0,w1,6295548] [1538,2689] (n (n (n (s [8,67584,w2,w4,w5,w3,w0,w1,6551005] [1538,2689]) [8,67584,w2,w4,w5,w3,w0,w1,7788474] [906,1162,1538,2689,4362,4930] e) [8,67584,w2,w4,w5,w3,w0,w1,8321023] [908,1164,1538,2689,4674,4930,5185] (n (s [8,67584,w2,w4,w5,w3,w0,4263872] [34,98,161,1170,1298,1538,1560,1570,1682,1698,2070,2450]) [8,67584,w2,w4,w5,1903138,w0,w1] [34,98,161,1170,1298,1560,1682,1698,2450,2689,2721,3473] e)) [8,67584,w2,w4,w5,1911399,w0,w1] [34,98,161,1170,1298,1560,1682,2689,2721,3473,3729] (n (n (s [8,67584,w2,w4,w5,1985195,w0,w1] [8,34,98,161,904,920,1160,1170,1298,1560,1624,1682,2056,2072,2136,2697,2712,2721,2776,3464,3481,3544,3857]) [8,67584,w2,w4,w5,w0,w1,6551005] [8,34,129,1170,1298,1560,1682,2049,2081,2705] e) [8,67584,w2,764247,w5,w3,w0,w1] [10,34,161,906,920,1162,1178,1544,1560,1626,2078,2138,2714,2721,2778,3483,3546,3601] (n (s [8,67584,w2,w5,w3,1911399,w0,w1] [14,34,161,910,920,1160,1176,1246,1566,1630,2062,2078,2703,2718,2721,2782,3470,3487,3550,3857]) [8,67584,w2,w5,w3,w0,w1,7788474] [14,129,906,920,1160,1176,1242,1546,1566,1626,2059,2074,2081,2138,2698,2715,2778,3466,3482,3546] e)))) [8,67585,w2,w4,w5,1296795,w3,w0,w1] [908,962,1160,1538,2056,2696,3465,4360] (n (n (n (n (s [8,67585,w2,w4,w5,w3,w0,w1] [14,161,900,1170,1538,1560,2070,2689,2721,3473]) [8,67585,w2,w4,1296795,w3,w0,w1] [2,161,978,1154,1170,1538,1554,2050,2070,2130,2691,2706,2721,2770,3458,3475,3538,3601] e) [8,67585,w4,w5,1296795,w3,w0,w1] [12,161,908,918,1180,1244,1548,1564,2054,2070,2140,2701,2716,2721,2780,3468,3485,3548,3729] (n (s [8,67588,w2,w4,w5,w3,w0,2329918,w1] [900,1538,2689]) [8,67588,w2,w4,w5,w3,w0,w1] [15,900,1170,1538,1560,2070,2689,3473] e)) [8,73797,w2,w4,w5,w3,w0,w1] [14,161,900,1170,1560,2068,2390,3473,3537,3729,3793] (n (n (s [8,73797,w2,w4,w5,w3,w0,w1,6551005] [900,2374]) [8,73797,w2,w4,w5,w0,w1,6551005] [8,129,898,1170,1560,2705,2769,2961,3025] e) [8,73797,w2,w5,w3,w0,w1] [14,129,145,1400,1566,1778,1916,2290,2424,2550,2737,2801,2865,2931,2993,3065,3121,3191] (n (s [8,73797,w2,w5,w3,w0,w1,6551005] [14,129,1544,1566,1762,1902,2518,3089,3159,3816,4129,4193]) [8,73797,w2,w5,w0,w1,6551005] [8,97,113,1400,1778,1912,2097,2161,2225,2291,2353,2425,3064,3249,3313] e))) [8,198656,w2,w4,w5,1796301,w3,w0,w1] [1162,1288,1538,3457] (n (n (n (s [8,198656,w2,w4,w5,w3,w0,w1] [4,72,161,1162,1192,1320,1538,1560,1624,1688,2070,2328,2472,2689,2721,3473]) [8,229394,w2,w4,w5,w3,w0,4190271] [4,72,1162,1192,1288,1320,1538,1560,1624,1688,2070,2130,2328,2472,2770] e) [8,229394,w2,w4,w5,w3,w0,4190271,w1] [1162,1288,1538,4547] (n (s [8,229394,w2,w4,w5,w3,w0,w1] [5,72,1162,1192,1288,1320,1538,1560,1624,1688,2070,2130,2328,2472,2770,3473,3667]) [8,229648,w2,w4,w5,w3,w0,w1] [4,72,161,1162,1192,1320,1538,1560,1624,1688,2066,2258,2328,2472,2770,3473,3539,3601] e)) [8,229648,w2,w4,w5,w3,w0,w1,6551005] [1162,1538,2242,2312,4808] (n (n (s [8,229648,w2,w4,w5,w0,w1,6551005] [72,129,1160,1192,1320,1560,1624,1688,2130,2705,2771,2833,3880,3928]) [8,w2,w2,w4,764247,w5,w3,w0,w1] [1162,1800,2050] e) [8,w2,w2,w4,w5,w3,2067250,w0,w1] [770,834,1162,1538,2114,2690,2952] (n (s [8,w2,w2,w4,w5,w3,w0,2329918,w1] [1162,1538,2754]) [8,w2,w2,w4,w5,w3,w0,w1] [4,72,161,1162,1192,1538,1560,1624,2066,2130,2328,2472,2770,3473,3539] e))))))
def N_118 : BT := n T_116 [8,2052,w2,w4,w5,w3,w0,w1,6295548] [900,1538] T_117
def T_119 : BT := (n (n (n (n (n (n (s [8,w2,w2,w4,1296795,w3,w0,w1] [2,72,161,770,834,1170,1234,1538,1554,2066,2130,2328,2706,2770,3475,3539]) [8,w2,231699,w4,w5,w3,w0,w1] [4,36,72,161,900,916,1172,1192,1234,1290,1320,1564,1626,1666,1688,1752,1816,2068,2134,2194,2258,2328,2472,2708,2770,2898,3477,3539,3601,3667] (s [8,w2,231702,w4,w5,w3,w0,w1] [4,45,900,916,1166,1172,1234,1290,1542,1556,1626,1666,1688,1752,2068,2134,2194,2258,2708,2770,3476,3539,3601,3667])) [8,w2,231730,w4,w5,w3,w0,w1] [4,37,72,900,916,1166,1172,1192,1234,1290,1298,1320,1542,1564,1626,1666,1690,1752,2068,2134,2194,2262,2328,2472,2708,2770,2898,3476,3539,3601,3667] (n (s [8,w2,232722,w4,w5,w3,w0,w1] [4,36,72,161,900,916,1166,1172,1192,1234,1290,1320,1542,1564,1626,1666,1688,1752,2068,2134,2194,2258,2328,2472,2708,2770,2898,3477,3539,3601,3667,4113]) [8,w2,w4,731205,w5,w3,w0,w1] [4,42,78,161,916,938,1156,1172,1290,1306,1378,1556,1690,1752,1880,2184,2202,2260,2324,2388,2842,3611,3665,3729,3793] e)) [8,w2,w4,764247,764247,w5,w3,w0,w1] [1156,1290] (n (n (s [8,w2,w4,764247,w5,1296795,w3,w0,w1] [1156,1224,1290,1352,1794,1864,2052,2186,2434,2708,2842,2970,3090,3218]) [8,w2,w4,764247,w5,1796301,w3,w0,w1] [1156,1290,1864,2052,2186,2824,2842] e) [8,w2,w4,764247,w5,1829343,w3,w0,w1] [1156,1290,1864,2052,2186,2842] (n (s [8,w2,w4,764247,w5,w3,1985195,w0,w1] [1164,1228,1294,1356,1540,1564,1570,1608,1798,1820,1864,2050,2114,2184,2206,2244,2312,2334,2374,2692,2722,2762,2826,2884,2972,3074,3484,3614,3858,4381,4511,4755,4881]) [8,w2,w4,764247,w5,w3,w0,2329918,w1] [910,1156,1290,1542,3460,3594] e))) [8,w2,w4,764247,w5,w3,w0,2862463,w1] [1156,1290,3460,3594] (n (n (n (s [8,w2,w4,764247,w5,w3,w0,3296445,w1] [1156,1226,1290,1354,1542,1794,2202,2322,2450,2693,2827,2955,3460,3530,3594,3784]) [8,w2,w4,764247,w5,w3,w0,4190271] [4,42,76,98,916,938,978,1156,1172,1290,1306,1378,1556,1570,1626,1690,1752,1880,2068,2134,2202,2260,2322,2390,2450,2708,2770,2842,3476,3610,3666] e) [8,w2,w4,764247,w5,w3,w0,4190271,w1] [1156,1290,3460,3594,3650,4356,4419,4490,4545,4673] (n (s [8,w2,w4,764247,w5,w3,w0,w1] [4,42,76,98,161,916,938,978,1156,1172,1290,1306,1378,1556,1570,1626,1690,1752,1880,2068,2134,2202,2260,2322,2390,2450,2708,2770,2842,3477,3539,3611,3665,3729,3793]) [8,w2,w4,764247,w5,w3,w0,w1,6295548] [1156,1290,1556,1752,2134,2202,2322,2693,2708,2827,2842,2945,3460,3477,3594,3611,4356,4372,4418,4490,4506] e)) [8,w2,w4,764247,w5,w3,w0,w1,6551005] [1156,1290,2050,2114,2184,2246,2374,4356,4490,4808] (n (n (s [8,w2,w4,764247,w5,w3,w0,w1,7624360] [1156,1228,1290,1356,4356,4420,4490,4554]) [8,w2,w4,764247,w5,w3,w0,w1,7788474] [910,1156,1226,1290,1354,2184,4356,4426,4490,4554,4682,4942] e) [8,w2,w4,764247,w5,1911399,w0,w1] [6,40,98,161,914,978,1154,1170,1378,1554,1626,1688,1880,2066,2130,2386,2706,2770,2840,3475,3539,3609,3729,3793] (n (s [8,w2,w4,764247,w5,1985195,w0,w1] [14,42,72,98,161,914,936,978,1154,1170,1224,1256,1288,1304,1352,1378,1562,1626,1688,1752,1816,1864,1880,1896,2078,2138,2200,2260,2328,2706,2770,2840,2968,3475,3539,3609,3665,3737,3793,3857]) [8,w2,w4,764247,w5,w0,w1,6551005] [2,40,72,129,914,936,978,1154,1170,1288,1304,1378,1554,1626,1688,1752,1880,2066,2130,2200,2707,2771,2841,2897,2961,3025,3474,3592,3608,3928] e)))) [8,w2,w4,w5,1796301,1796301,w3,w0,w1] [1540] (n (n (n (n (s [8,w2,w4,w5,1796301,1829343,w3,w0,w1] [1540,2052]) [8,w2,w4,w5,1796301,w3,2067250,w0,w1] [908,1156,1540,1570,1730,1858,2114,2184,2454,2826,2946,2984,3090,3476,3610,3730,4373,4507,4627,4881] e) [8,w2,w4,w5,1796301,w3,w0,2329918,w1] [908,1156,1540,2068,2452,2827,2947,3073,3233,3594,3714,4372,5009] (n (s [8,w2,w4,w5,1796301,w3,w0,2698365,w1] [908,1540,1674,1730,1858,2184,2947,3594,3784,3906]) [8,w2,w4,w5,1796301,w3,w0,3894525,w1] [1540] e)) [8,w2,w4,w5,1796301,w3,w0,4190271] [4,42,66,98,916,938,1180,1186,1368,1540,1556,1762,1898,2206,2326,2344,2452,2516,2842,2962,3666,3802] (n (n (s [8,w2,w4,w5,1796301,w3,w0,4190271,w1] [1540,3650,3786,4490,4610,4801]) [8,w2,w4,w5,1796301,w3,w0,w1] [4,42,66,98,161,916,938,1180,1186,1368,1540,1556,1762,1898,2206,2326,2344,2452,2516,2842,2962,3611,3731,3857,3921] e) [8,w2,w4,w5,1796301,w3,w0,w1,6295548] [1540,2452,2721,2827,2947,3073,3237,3594,3714,4004,4490,4610] (n (s [8,w2,w4,w5,1796301,w3,w0,w1,6551005] [1540,2184,2500,4680]) [8,w2,w4,w5,1796301,w3,w0,w1,6592306] [916,1180,1540,1556,1730,1858,2344,2452,2842,2962,3611,3731,4418,4434,4490,4610,4934,4950,5153] e))) [8,w2,w4,w5,1796301,w3,w0,w1,7190390] [1156,1540,1730,1794,1858,4418,4490,4802,4934] (n (n (n (s [8,w2,w4,w5,1796301,1911399,w0,w1] [6,40,66,136,161,906,914,936,1174,1368,1542,1558,1762,1898,2396,2840,2962,3609,3731,3857,3921]) [8,w2,w4,w5,1796301,2058991,w0,w1] [6,40,161,914,936,1178,1368,1538,1554,1762,1898,2840,3609,3729,3857,3921] e) [8,w2,w4,w5,1796301,w0,w1,6551005] [2,40,129,914,936,1178,1368,1538,1554,1762,1898,2200,2841,2961,3089,3153,3752,3800] (n (s [8,w2,w4,w5,1829343,w3,w0,w1] [4,42,66,102,161,916,938,978,1180,1186,1242,1368,1540,1556,1762,1898,2068,2098,2134,2206,2228,2326,2344,2364,2516,2708,2770,2842,2962,3477,3539,3611,3731,3857,3921,4017]) [8,w2,w4,w5,w3,2093059,w0,w1] [4,42,66,161,916,938,1180,1186,1694,1814,1832,2082,2274,2344,2410,2470,2532,2721,2851,2987,3109,3233,3618,3754,3876,3985,4177] e)) [8,w2,w4,w5,w3,2093059,w0,w1,6295548] [3201] (n (n (s [8,w2,w4,w5,w3,2097212,w0,4190271] [4,42,66,916,938,1180,1186,1694,1814,1832,2146,2210,2346,2408,2468,2534,2850,2986,3108]) [8,w2,w4,w5,w3,2097212,w0,4190271,w1] [] e) [8,w2,w4,w5,w3,2097212,w0,w1] [4,42,66,129,916,938,1180,1186,1694,1814,1832,2146,2210,2346,2408,2468,2534,2850,2986,3108] (n (s [8,w2,w4,w5,w3,2098204,w0,w1] [4,42,66,135,916,938,1180,1186,1694,1814,1832,2146,2210,2346,2408,2468,2984,3174,3985]) [8,w2,w4,w5,w3,2098204,w0,w1,6551005] [1672,3142,4680] e))))) [8,w2,w4,w5,w3,w0,w0,2329918,w1] [910,1158,2114] (n (n (n (n (n (s [8,w2,w4,w5,w3,w0,w0,w1] [4,42,66,129,916,938,1180,1186,1694,1814,1832,2146,2210,2346,2408,2468,2534]) [8,w2,w4,w5,w3,w0,w0,w1,6288323] [2561,2625] (s [8,w2,w4,w5,w3,w0,w0,w1,6295548] [])) [8,w2,w4,w5,w3,w0,2100285,w1] [4,42,66,129,163,916,938,1180,1186,1306,1314,1694,1814,1832,2081,2146,2209,2345,2408,2469,2534,2786,2850,2986,3048,3108,3174,3201,3217,3892,3985,4049] (n (s [8,w2,w4,w5,w3,w0,2100348,w1] [4,42,66,129,171,916,938,1180,1186,1694,1814,1832,2081,2146,2209,2337,2408,2469,2534,2786,2850,2986,3048,3108,3174,3201,3217,3610,3985,4049,4177]) [8,w2,w4,w5,w3,w0,2165820,w1] [4,42,66,129,173,916,938,1180,1186,1694,1814,1832,2081,2146,2211,2337,2408,2467,2534,2786,2850,2984,3048,3110,3174,3201,3217,3985,4049] e)) [8,w2,w4,w5,w3,w0,2329918,2329918,w1] [910,1158] (n (n (s [8,w2,w4,w5,w3,w0,2329918,2698365,w1] [908,1158,1672,2754,3201,3266,3522,3969,4881]) [8,w2,w4,w5,w3,w0,2329918,2862463,w1] [910,1158] e) [8,w2,w4,w5,w3,w0,2329918,3935806,w1] [908,1156,1538,1672,2114,2502,2756,3142,3201,3268,3522,3969,4098,4162] (n (s [8,w2,w4,w5,w3,w0,2329918,4165438,w1] [910,1158,2754,3142,3266,4098]) [8,w2,w4,w5,w3,w0,2329918,4190271] [4,42,66,164,910,916,938,1158,1180,1186,1556,1694,1814,1832,2130,2146,2344,2984,3048,3106,3174,4114] e))) [8,w2,w4,w5,w3,w0,2329918,4190271,w1] [910,1158,4098,4356,5059] (n (n (n (s [8,w2,w4,w5,w3,w0,2329918,w1] [4,42,66,129,165,910,916,938,1158,1180,1186,1556,1694,1814,1832,2130,2146,2209,2345,2465,2984,3048,3106,3174,3476,3985,4179]) [8,w2,w4,w5,w3,w0,2329918,w1,4427730] [4,910,1158,2114,2692,2753,3265,3523,4163,4356,4930] e) [8,w2,w4,w5,w3,w0,2329918,w1,4796357] [909,1159,1672,2187,2755,2827,3267,3460,4098,4356,4865,5057] (n (s [8,w2,w4,w5,w3,w0,2329918,w1,6033378] [909,1157,1538,1672,2433,2757,3073,3269,3460,4100,4356,4865,4994,5058]) [8,w2,w4,w5,w3,w0,2329918,w1,6058689] [909,1157,2757,3269,3477,3989,4356,4865] e)) [8,w2,w4,w5,w3,w0,2329918,w1,6288323] [910,1158,2114,2753,3201,3265,4356,5057] (n (n (s [8,w2,w4,w5,w3,w0,2329918,w1,6295548] [910,916,1158,1180,2114,2209,2345,3201,3460,4163,4418,4865,5058]) [8,w2,w4,w5,w3,w0,2329918,w1,6524926] [910,1158,4163,4806] e) [8,w2,w4,w5,w3,w0,2329918,w1,6551005] [910,1158,1538,1672,2433,3142,4680] (n (s [8,w2,w4,w5,w3,w0,2329918,w1,7190390] [910,1158,2307,2754,2946,3016,3266,4418,4806,4930,4994,5058]) [8,w2,w4,w5,w3,w0,2329918,w1,8156909] [910,1158,2114,2692,2756,3268,3476,3985,4548,4684,4865,5060] e)))) [8,w2,w4,w5,w3,w0,2355229,w1] [4,42,66,129,165,916,938,1180,1186,1672,1694,1814,1832,2984,3048,3110,3752,3927,3943,4113] (n (n (n (n (s [8,w2,w4,w5,w3,w0,2862463,w1] [4,42,66,129,173,916,938,1180,1186,1306,1556,1694,1814,1832,2130,2347,2469,2914,3048,3106,3174,3477,3611,3985,4177]) [8,w2,w4,w5,w3,w0,3894525,w1] [4,42,66,129,163,916,938,1180,1186,1694,1814,1832,2081,2469,2914,3050,3108,3172,3611,3731,3985,4177] e) [8,w2,w4,w5,w3,w0,4190271] [4,20,42,58,66,82,916,938,1180,1186,1208,1272,1586,1650,1694,1716,1780,1814,1832,1852,1916,2162,2226,2362,2424,2484,2550,2738,2930,3000,3066,3126,3188] (n (s [8,w2,w4,w5,w3,w0,4190271,4190271] [4,42,66,916,938,1180,1186,1694,1814,1832,2722,2914,2984,3050,3110,3172]) [8,w2,w4,w5,w3,w0,4190271,4190271,w1] [] e)) [8,w2,w4,w5,w3,w0,4190271,4192383] [4,42,66,203,916,938,1180,1186,1694,1814,1832,2898,2914,3108,3682,3818,3876,3940] (n (n (s [8,w2,w4,w5,w3,w0,4190271,4192383,w1] [2882,4490,5185]) [8,w2,w4,w5,w3,w0,4190271,4193343] [4,42,66,193,916,938,1180,1186,1694,1814,1832,2722,2984,3110,3490,3682,3752,3818,3878,3940] e) [8,w2,w4,w5,w3,w0,4190271,4193343,w1] [] (n (s [8,w2,w4,w5,w3,w0,4190271,w1] [4,42,66,129,161,916,938,1180,1186,1694,1814,1832,2722,2914,2984,3050,3110,3172,3555,3618,3681,3754,3817,3876,3943]) [8,w2,w4,w5,w3,w0,4190271,w1,6288323] [3201,5185] e))) [8,w2,w4,w5,w3,w0,4190271,w1,6295548] [3201] (n (n (n (s [8,w2,w4,w5,w3,w0,4190271,w1,6551005] [1672,3140,3911,4680,5185]) [8,w2,w4,w5,w3,w0,4190271,w1,8388607] [] e) [8,w2,w4,w5,w3,w0,4190271,4427730] [4,42,66,129,161,196,910,916,938,1158,1180,1186,1556,1694,1814,1832,2068,2708,2984,3110,3681,3752,3817,3874,3943,4066] (n (s [8,w2,w4,w5,w3,w0,4190271,6288323] [4,42,66,129,161,916,938,1180,1186,1694,1814,1832,2146,2210,2346,2408,2468,2534,3490,3553,3683,3752,3819,3878,3941]) [8,w2,w4,w5,w3,w0,4190271,6295548] [4,42,66,916,938,1180,1186,1694,1814,1832,2210,2346,2468,2722,2984,3110,3554,3618,3754,3816,3876,3942] e)) [8,w2,w4,w5,w3,w0,4190271,6551005] [4,42,66,196,916,938,1180,1186,1634,1672,1694,1766,1814,1832,1902,2518,3156,3752,3784,3800,3816] (n (n (s [8,w2,w4,w5,w3,w0,4190271,8388607] [4,42,66,916,938,1180,1186,1694,1814,1832,3682,3818,3940]) [8,w2,w4,w5,w3,w0,4192383,w1] [4,42,66,129,171,916,938,1180,1186,1694,1814,1832,2914,3050,3108,3172,3611,3681,3876,4177,4193] e) [8,w2,w4,w5,w3,w0,4193343,w1] [4,42,66,129,161,916,938,1180,1186,1694,1814,1832,2722,2914,2984,3050,3110,3172,3618,3754,3876,3985] (n (s [8,w2,w4,w5,w3,w0,w1] [4,20,42,58,66,82,129,145,916,938,1180,1186,1208,1272,1586,1650,1694,1716,1780,1814,1832,1852,1916,2162,2226,2362,2424,2484,2550,2737,2803,2867,2929,3003,3065,3125,3191]) [8,w2,w4,w5,w3,w0,w1,6295548] [4,42,66,129,916,938,1180,1186,1208,1694,1716,1814,1832,1852,2081,2211,2347,2469,2850,2986,3108,3281,3554,3618,3754,3816,3876,3942,4193] e))))))
def T_120 : BT := (n (n (n (n (n (n (s [8,w2,w4,w5,w3,w0,w1,6295548,6524926] [910,916,1158,1180,2211,2347,2850,2986,3522,4806]) [8,w2,w4,w5,w3,w0,w1,6295548,6551005] [1672,1694,1814,2433,2469,3108,3910,4680,5057] (s [8,w2,w4,w5,w3,w0,w1,6321357] [4,42,66,129,194,210,916,938,1180,1186,1586,1602,1622,1634,1694,1814,1832,2068,2709,3089,3476,3618,3754,3784,3800,3816,3876,4129,4193])) [8,w2,w4,w5,w3,w0,w1,6403412] [4,42,66,129,204,916,938,1180,1186,1256,1314,1634,1694,1766,1814,1832,1884,1902,2322,2392,2518,2963,3033,3089,3159,3554,3618,3730,3752,3794,3878,4129,4193] (n (s [8,w2,w4,w5,w3,w0,w1,6524926] [4,42,66,129,196,910,916,938,1158,1180,1186,1556,1694,1814,1832,2211,2347,2469,2850,2986,3108,3752,3816,3874,3910,3926,3942,4193]) [8,w2,w4,w5,w3,w0,w1,6551005] [4,42,66,129,196,916,938,1180,1186,1634,1672,1694,1766,1814,1832,1902,2518,3089,3159,3752,3784,3800,3816,4129,4193] e)) [8,w2,w4,w5,w3,w0,w1,6551005,6551005] [1672,3784] (n (n (s [8,w2,w4,w5,w3,w0,w1,6551005,6553055] [1538,1672,3784,4680,4802]) [8,w2,w4,w5,w3,w0,w1,6551005,6553085] [1672,2433,3784,4680,4806] e) [8,w2,w4,w5,w3,w0,w1,6551005,7077341] [1672,3784,4680,4806] (n (s [8,w2,w4,w5,w3,w0,w1,6551005,7190390] [1158,1672,1868,3714,3784,4418,4806]) [8,w2,w4,w5,w3,w0,w1,6551005,8156909] [908,1156,1538,1602,1672,3460,3784,4548,4684,4804] e))) [8,w2,w4,w5,w3,w0,w1,6551005,8388607] [1672,3784] (n (n (n (s [8,w2,w4,w5,w3,w0,w1,6553055] [4,42,66,129,196,916,938,1180,1186,1556,1634,1694,1814,1832,3089,3752,3784,3800,3816,3922,3938,4129,4193]) [8,w2,w4,w5,w3,w0,w1,6553085] [4,42,66,129,197,916,938,1180,1186,1672,1694,1814,1832,2469,2518,3089,3752,3784,3800,3816,3926,3942,4193] e) [8,w2,w4,w5,w3,w0,w1,7077341] [4,42,66,129,206,916,938,1180,1186,1634,1672,1694,1766,1814,1832,1902,2518,3089,3159,3682,3784,3800,3816,3926,3940,4129,4193] (n (s [8,w2,w4,w5,w3,w0,w1,7337983] [4,42,66,129,204,916,938,1180,1186,1694,1814,1832,3650,3666,3682,3784,3800,3816,3910,3926,3942,4161,4177,4193]) [8,w2,w4,w5,w3,w0,w1,8385535] [4,42,66,129,916,938,1180,1186,1694,1814,1832,3217,3650,3666,3682,3786,3802,3818,3908,3924,3940,4177,4193] e)) [8,w2,w4,w5,w3,w0,w1,8386047] [4,42,66,129,199,916,938,1180,1186,1694,1814,1832,3089,3108,3650,3666,3682,3786,3802,3818,3924,3940,4177,4193] (n (n (s [8,w2,w4,w5,w3,w0,w1,8386557] [4,42,66,129,194,916,938,1180,1186,1538,1556,1694,1814,1832,3650,3666,3682,3786,3802,3818,3924,3940,4161,4177,4193]) [8,w2,w4,w5,w3,w0,w1,8388607] [4,42,66,129,916,938,1180,1186,1694,1814,1832,3682,3818,3940,4193] e) [8,w2,w4,w5,w3,w0,4198337] [4,20,42,56,66,129,162,178,916,938,1180,1186,1208,1272,1306,1314,1586,1650,1694,1716,1780,1814,1832,1852,1916,2162,2226,2362,2424,2484,2550,2803,2929,3000,3065,3124,3191] (n (s [8,w2,w4,w5,w3,w0,4198340] [4,20,42,66,129,170,186,916,938,1180,1186,1208,1272,1586,1650,1694,1716,1780,1814,1832,1852,1916,2162,2202,2209,2226,2362,2424,2484,2550,2803,3065,3124,3191]) [8,w2,w4,w5,w3,w0,4263872] [4,18,42,66,82,129,172,188,1180,1186,1208,1272,1586,1650,1694,1718,1782,1814,1832,1852,1916,2162,2226,2362,2424,2484,2550,2803,2866,2929,3065,3122,3191] e)))) [8,w2,w4,w5,w3,w0,4427730,4796357] [4,42,66,129,164,202,1158,1180,1186,1306,1556,1672,1694,1814,1832,2068,2202,2897,2913,2978,3106,3234,3539,3555,4178] (n (n (n (n (s [8,w2,w4,w5,w3,w0,4427730,6033378] [4,42,66,129,164,908,916,938,1156,1180,1186,1538,1556,1672,1694,1814,1832,2068,2852,2988,3159,3175,3236,3539,3555,3752,4162,4182,4194]) [8,w2,w4,w5,w3,w0,4427730,6295548] [4,42,66,129,164,180,910,916,938,1158,1180,1186,1556,1694,1814,1832,2052,2068,2209,2345,2465,2984,3106,3266,3282,3298,3538,3554,3752,3768,4162,4178,4194] e) [8,w2,w4,w5,w3,4190271,6288323] [4,20,42,58,66,82,129,145,916,938,1180,1186,1208,1272,1586,1650,1694,1716,1780,1814,1832,1852,1916,2098,2290,2360,2426,2486,2548,2739,2801,2865,2931,3001,3067,3127,3189] (n (s [8,w2,w4,w5,1837603,w0,w1] [6,42,56,66,129,145,918,938,1182,1186,1208,1272,1650,1780,1832,1848,1916,2162,2360,2424,2550,2737,2803,2865,2929,3001,3065,3121,3191]) [8,w2,w4,w5,1837606,w0,w1] [6,42,66,105,918,938,1174,1186,1208,1272,1650,1690,1780,1810,1832,1918,2162,2202,2424,2550,2803,2929,3065,3191] e)) [8,w2,w4,w5,1837618,w0,w1] [6,42,56,66,97,918,938,1182,1186,1208,1272,1650,1690,1782,1810,1832,1848,1918,2070,2162,2360,2424,2546,2803,2929,3000,3065,3191] (n (n (s [8,w2,w4,w5,1838626,w0,w1] [6,42,56,66,129,145,918,938,1182,1186,1208,1272,1650,1690,1782,1810,1832,1848,1918,2162,2360,2424,2550,2737,2803,2865,2929,3001,3065,3121,3191,3217]) [8,w2,w4,w5,1903138,w0,w1] [6,42,66,104,129,145,918,1174,1186,1208,1272,1650,1778,1810,1832,1918,2162,2424,2550,2737,2803,2865,2929,2993,3065,3121,3191] e) [8,w2,w4,w5,1911399,1911399,w0,w1] [6,42,66,161,918,1174,1186,1634,1762,1900,2840,3158,3609,3857,3927] (n (s [8,w2,w4,w5,1911399,1985195,w0,w1] [6,42,66,104,161,918,936,1182,1208,1368,1576,1634,1736,1762,1832,1884,1900,2104,2154,2260,2276,2410,2456,2520,2842,2962,3096,3158,3294,3505,3611,3731,3865,3927,3985,4063]) [8,w2,w4,w5,1911399,2058991,w0,w1] [6,40,66,104,161,918,1174,1634,1762,1884,1900,2274,2410,2840,2962,3158,3284,3609,3731,3857,3927,3985,4053] e))) [8,w2,w4,w5,1911399,2067250,w0,w1] [6,42,66,104,161,914,1174,1186,1304,1602,1618,1634,2258,2274,2322,2410,2710,2842,3282,3479,3611,3857,3985,4051] (n (n (n (s [8,w2,w4,w5,1911399,2075511,w0,w1] [6,42,66,161,914,1174,1186,1602,1618,1634,2274,2410,2710,2842,3282,3479,3611,3857,3985,4051]) [8,w2,w4,w5,1911399,w0,2329918,w1] [6,40,66,104,129,161,914,1158,1178,1558,2130,2146,2185,2200,2209,2337,2465,3048,3170,3478,3608,3985,4179] e) [8,w2,w4,w5,1911399,w0,2698365,w1] [6,40,66,129,161,906,914,936,1174,1186,1304,1368,1672,1688,2081,2200,2337,2534,2786,2824,2840,2914,3048,3174,3608,3665,3985,4177] (n (s [8,w2,w4,w5,1911399,w0,3296445,w1] [6,42,66,104,129,161,914,1158,1178,1314,1810,1832,2081,2187,2202,2209,2392,2408,2465,2794,3050,3180,3610,3730,3985,4185]) [8,w2,w4,w5,1911399,w0,3935806,w1] [6,42,66,104,129,161,918,936,1174,1186,1208,1304,1368,1674,1690,2081,2200,2337,2518,2534,2786,2842,2900,2916,3052,3609,3665,3985,4183] e)) [8,w2,w4,w5,1911399,w0,4009599,w1] [6,42,66,129,161,918,1174,1186,2081,2200,2337,2518,2534,2786,2914,3052,3609,3985,4183] (n (n (s [8,w2,w4,w5,1911399,w0,4190271] [6,42,66,104,914,1174,1208,1272,1650,1778,1916,2162,2200,2424,2550,2898,2930,3066]) [8,w2,w4,w5,1911399,w0,4190271,w1] [6,42,66,104,129,161,914,1174,2200,2882,2898,2914,3050,3555,3592,3609,3681,3817,3943] e) [8,w2,w4,w5,1911399,w0,w1] [6,42,66,104,129,145,914,1174,1208,1272,1650,1778,1916,2162,2200,2424,2550,2737,2803,2841,2865,2929,2993,3065,3121,3191] (n (s [8,w2,w4,w5,1911399,w0,w1,6295548] [6,42,66,104,129,914,1174,2081,2185,2200,2209,2337,2465,2824,2841,3281,3554,3592,3608,3816,3942,4193]) [8,w2,w4,w5,1911399,w0,w1,6477208] [6,42,66,104,129,914,1178,1634,1736,1762,1832,1900,2200,2518,2841,3089,3159,3562,3592,3608,3816,3864,3928,4129,4193] e))))) [8,w2,w4,w5,1911399,w0,w1,6551005] [6,40,66,104,129,196,914,936,1178,1304,1368,1634,1672,1688,1762,1900,2200,2518,2841,2897,3089,3159,3592,3608,3784,3800,3816,4129,4193] (n (n (n (n (n (s [8,w2,w4,w5,1911399,w0,w1,7190390] [6,42,66,104,129,202,914,1158,1174,1186,1256,1314,1810,1884,2200,2322,2392,2841,2963,3033,3522,3538,3554,3682,3730,3794,3910,3926,3942,4129,4193]) [8,w2,w4,w5,1911399,w0,w1,7788474] [6,42,66,104,129,194,906,914,936,1178,1304,1368,1674,1690,1832,2200,2841,2897,3530,3546,3562,3610,3674,3818,3918,3934,3950,4129,4193] (s [8,w2,w4,w5,1911399,w0,w1,8156909] [6,42,66,104,129,918,978,1158,1174,1186,1242,1558,1618,2070,2130,2200,2711,2771,2841,3478,3542,3684,3788,3804,3820,4129,4193])) [8,w2,w4,w5,2058991,w0,w1] [6,40,56,129,145,914,1178,1208,1272,1778,1914,2162,2200,2360,2424,2548,2737,2803,2841,2865,2929,2961,3001,3065,3121,3189] (n (s [8,w2,w4,w5,2067250,w0,3935806,w1] [6,42,66,129,161,914,936,1178,1674,1690,1794,1810,1832,2051,2066,2081,2209,2345,2514,2530,2754,2770,2786,2984,3475,3985]) [8,w2,w4,w5,2067250,w0,w1,6551005] [2,42,66,129,194,914,936,1178,1674,1690,1762,1794,1810,1832,1898,2066,2514,2707,3089,3155,3474,3752,3800,4129] e)) [8,w2,w4,w5,2098204,w0,w1,6551005] [2,40,97,914,936,1178,1634,1832,1896,2344,3089,3752,3800] (n (n (s [8,w2,w4,w5,w0,2329918,w1,6551005] [2,40,97,129,906,914,936,1154,1178,1618,1634,1697,1833,2344,2408,2706,3089,3283,3752,3800]) [8,w2,w4,w5,w0,2698365,w1,6551005] [2,40,66,97,137,194,906,914,936,1178,1304,1569,1825,2146,2274,2408,2840,3089,3281,3800] e) [8,w2,w4,w5,w0,3935806,w1,6033378] [6,42,66,97,129,145,914,936,1178,1569,1697,1833,2081,2209,2345,2984,3089,3287,3303,3752,3926,3942,4049] (n (s [8,w2,w4,w5,w0,3935806,w1,6551005] [6,42,66,97,129,196,914,936,1178,1569,1697,1833,2146,2276,2344,2412,3089,3287,3752,3800,3857]) [8,w2,w4,w5,w0,4190271,w1,6551005] [2,40,97,129,914,936,1178,2274,2344,2410,2787,2913,2984,3049,3752,3800,4177] e))) [8,w2,w4,w5,w0,4190271,6551005] [2,40,56,914,936,1178,1208,1272,1650,1848,1912,2290,2360,2426,2984,3000,3032,3064] (n (n (n (s [8,w2,w4,w5,w0,w1,6295548,6551005] [2,40,97,914,936,1178,1569,1697,1833,2344,2513,2786,2984,3048,3297,3752,3800,4049]) [8,w2,w4,w5,w0,w1,6403412] [2,40,66,97,113,168,184,914,936,1178,1208,1272,1650,1848,1912,2097,2163,2225,2289,2321,2361,2425,2802,2984,3249,3313] e) [8,w2,w4,w5,w0,w1,6551005] [2,40,56,97,113,914,936,1178,1208,1272,1650,1848,1912,2097,2163,2225,2289,2361,2425,2984,3000,3032,3064,3249,3313] (n (s [8,w2,w4,w5,w0,w1,6551005,6551005] [2,40,97,914,936,1178,2984,3016,3032,3048,3233,3297]) [8,w2,w4,w5,w0,w1,6551005,6553055] [2,40,97,196,914,936,1178,2984,3032,3233,3752,3784,3800,3816,4001,4065] e)) [8,w2,w4,w5,w0,w1,6551005,6553085] [2,40,97,197,914,936,1178,2984,3032,3752,3784,3800,3816,4065] (n (n (s [8,w2,w4,w5,w0,w1,6551005,7077341] [2,40,97,206,914,936,1178,3016,3032,3048,3233,3297,3682,3784,3800,3816,4001,4065]) [8,w2,w4,w5,w0,w1,6551005,7190390] [2,40,66,97,162,202,914,936,1154,1178,1256,1880,2321,2393,2946,2984,3032,3522,3538,3554,3682,4001,4065] e) [8,w2,w4,w5,w0,w1,6551005,8156909] [6,42,66,97,164,906,914,936,978,1154,1178,1242,1554,1618,2067,2131,2706,2984,3032,3474,3538,3652,3668,3684,3752,3788,3804,3820,4001,4065] (n (s [8,w2,w4,w5,w0,w1,6551005,8388607] [2,40,97,914,936,1178,2984,3032,3682,3818,4065]) [8,w2,w4,w5,w0,w1,7077341] [6,42,66,97,113,174,190,914,936,1178,1208,1272,1650,1848,1912,2097,2163,2225,2289,2361,2425,2930,3032,3064,3249,3313] e)))) [8,w2,w4,1296795,1911399,w0,w1] [6,18,40,66,82,129,145,1586,1618,1650,1714,1778,2070,2162,2200,2226,2424,2482,2550,2711,2737,2803,2841,2867,2929,2993,3065,3123,3191] (n (n (n (n (s [8,w2,w4,1296795,w0,w1,6551005] [2,40,66,97,113,162,178,1554,1650,1912,2067,2097,2163,2225,2289,2353,2425,3032,3064,3249,3313]) [8,w2,w4,1985195,w0,3296445,w1] [6,40,97,131,147,914,1202,1274,1396,1569,1650,1699,1714,1902,1918,2170,2737,2803,2867,2929,3071,3089,3321] e) [8,w2,w4,1985195,w0,w1,6551005] [6,40,97,113,166,182,914,1186,1202,1274,1396,1650,1714,1918,2097,2163,2227,2289,2353,2431,3032,3048,3064,3233,3249,3313] (n (s [8,w2,w4,w0,w1,6551005,7190390] [2,18,65,81,130,146,914,1266,1330,1585,1651,1715,1777,2210,2481,2545,2738,2770,2802,2866,2930,2994,3058,3123,3187,3282]) [8,w2,764247,1296795,w3,w0,w1] [4,40,56,129,145,1208,1556,1650,1688,1782,1848,1918,2068,2162,2360,2424,2550,2709,2737,2803,2865,2929,3001,3065,3121,3191] e)) [8,w2,764247,w3,1985195,w0,w1] [12,28,44,60,129,145,1266,1308,1382,1398,1596,1626,1658,1852,1916,2076,2162,2364,2430,2492,2556,2717,2737,2803,2865,2929,2961,3005,3071,3133,3197] (n (n (s [8,w2,764247,w3,w0,w1,7190390] [4,44,97,113,170,186,1266,1398,1556,1650,1910,2069,2097,2163,2225,2289,2353,2423,2802,3030,3062,3249,3313]) [8,w2,w3,w0,w1,7190390,7788474] [4,20,65,81,138,154,162,178,1010,1266,1332,1398,1585,1651,1717,1783,2088,2130,2162,2220,2228,2262,2294,2481,2545,2744,2778,2810,2852,2876,2910,2942,3000,3064,3129,3193] e) [9,2049,w2,w4,w5,w3,w0,w1] [2,36,52,72,88,161,177,900,932,1170,1300,1320,1562,1592,1692,1720,1784,1816,2068,2100,2332,2356,2420,2452,2472,2492,2556,2689,2721,3128,3192,3252,3316,3473,3505,3633,3697,3761,3825,3897,3961,4021,4085] (n (s [9,2052,w2,w4,w5,w3,w0,w1] [11,36,52,900,932,1170,1300,1538,1562,1684,2068,2100,2290,2324,2356,2420,2452,2484,2548,3252,3316,3473,4020,4084]) [9,3072,w2,w4,w5,w3,w0,w1] [36,52,74,90,98,114,161,177,900,932,1162,1170,1194,1202,1300,1322,1538,1562,1570,1594,1692,1698,1720,1784,2068,2100,2226,2290,2334,2356,2420,2454,2472,2492,2556,2930,2994,3130,3192,3252,3318,3473,3505,3633,3699,3763,3825,3899,3961,4021,4087,4113] e))) [9,67584,w2,w4,w5,w3,w0,w1] [12,34,50,98,114,161,177,1170,1202,1298,1538,1560,1570,1682,1698,2070,2098,2226,2290,2354,2418,2450,2689,2721,2930,2994,3192,3250,3318,3473,3505,3633,3699,3763,3825,3889,3961,4019,4087] (n (n (n (s [9,w2,w4,764247,w5,w3,w0,w1] [4,18,42,76,98,114,161,177,916,938,978,1156,1172,1290,1306,1378,1394,1556,1570,1626,1656,1690,1752,1880,1912,2068,2098,2134,2162,2202,2226,2260,2294,2322,2354,2390,2422,2450,2556,2708,2770,2802,2842,2866,3192,3250,3318,3477,3505,3539,3571,3611,3635,3665,3697,3729,3761,3793,3825,3889,3961,4019,4087]) [9,w2,w4,w5,1796301,w3,w0,w1] [4,20,42,56,66,98,161,177,916,938,1180,1186,1208,1272,1368,1540,1556,1762,1778,1898,1914,2162,2206,2228,2292,2326,2344,2364,2428,2452,2484,2516,2548,2802,2842,2962,3000,3064,3252,3318,3505,3571,3611,3633,3697,3731,3769,3833,3857,3889,3921,3953,4021,4087] e) [9,w2,w4,w5,w3,w0,2329918,w1] [4,42,56,66,129,165,910,916,938,1158,1180,1186,1208,1272,1556,1586,1650,1694,1718,1782,1814,1832,1854,1918,2130,2146,2162,2209,2345,2360,2424,2465,2550,2984,3000,3048,3064,3106,3174,3190,3476,3571,3697,3768,3833,3959,3985,4179,4211] (n (s [9,w2,w4,w5,w3,w0,4190271] [4,20,42,58,66,82,916,938,1180,1186,1208,1272,1586,1650,1694,1716,1780,1814,1832,1852,1916,2162,2226,2362,2424,2484,2550,2738,2930,3000,3066,3126,3188]) [9,w2,w4,w5,w3,w0,4190271,w1] [4,20,42,58,66,82,129,161,177,916,938,1180,1186,1208,1272,1586,1650,1694,1716,1780,1814,1832,1852,1916,2162,2226,2362,2424,2484,2550,2722,2738,2914,2930,2984,3000,3050,3066,3110,3126,3172,3188,3505,3555,3571,3618,3635,3681,3697,3754,3771,3817,3833,3876,3893,3943,3959] e)) [9,w2,w4,w5,w3,w0,w1] [4,20,42,58,66,82,129,145,916,938,1180,1186,1208,1272,1586,1650,1694,1716,1780,1814,1832,1852,1916,2162,2226,2362,2424,2484,2550,2737,2803,2867,2929,3003,3065,3125,3191] (n (n (s [9,w2,w4,w5,w3,w0,w1,6295548] [4,20,42,58,66,82,129,145,916,938,1180,1186,1208,1272,1586,1650,1694,1716,1780,1814,1832,1852,1916,2081,2162,2211,2226,2347,2362,2424,2469,2484,2550,2737,2803,2850,2867,2929,2986,3003,3065,3108,3125,3191,3281,3554,3570,3618,3634,3754,3770,3816,3832,3876,3892,3942,3958,4193,4209]) [9,w2,w4,w5,w3,w0,w1,6551005] [4,42,56,66,129,145,196,212,916,938,1180,1186,1208,1272,1586,1634,1650,1672,1694,1718,1766,1782,1814,1832,1854,1902,1918,2162,2226,2362,2424,2484,2518,2550,2737,2803,2867,2929,3003,3065,3089,3125,3159,3191,3752,3768,3784,3800,3816,3832,4129,4145,4193,4209] e) [9,w2,w4,w5,1911399,w0,w1] [6,42,66,104,129,145,914,1174,1208,1272,1650,1778,1916,2162,2200,2424,2550,2737,2803,2841,2865,2929,2993,3065,3121,3191] (n (s [9,w2,w4,w5,w0,w1,6551005] [2,40,56,97,113,914,936,1178,1208,1272,1650,1848,1912,2097,2163,2225,2289,2361,2425,2984,3000,3032,3064,3249,3313]) [10,w2,w4,w5,w3,w0,w1] [4,20,42,58,66,82,129,145,916,938,1180,1186,1208,1272,1586,1650,1694,1716,1780,1814,1832,1852,1916,2162,2226,2362,2424,2484,2550,2737,2803,2867,2929,3003,3065,3125,3191] e))))))
def N_121 : BT := n T_119 [8,w2,w4,w5,w3,w0,w1,6295548,6295548] [] T_120
def N_122 : BT := n N_118 [8,w2,w2,w4,w5,w3,w0,w1,8156909] [772,836,1162,1538,4676,4812] N_121
def N_123 : BT := n N_115 [7,w2,w3,2067250,2075511,2083771,w0,w1] [962] N_122
def N_124 : BT := n N_108 [7,w2,w4,w5,w0,4190271,6295548,6551005] [] N_123
def N_125 : BT := n N_93 [7,w2,w4,w5,1796301,w3,w0,4198348] [1540,2827,2947,3073] N_124
def N_126 : BT := n N_62 [6,w2,764247,w3,3296445,5394377,6295548] [2504,2692] N_125
def T_cert : BT := N_126
def chk := stepOK M_ Y_ PD_ PM_ V6_ G_ T_cert
set_option maxHeartbeats 0 in
theorem p_T_0 : T_0.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_1 : T_1.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_3 : T_3.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_4 : T_4.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_7 : T_7.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_8 : T_8.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_10 : T_10.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_11 : T_11.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_15 : T_15.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_16 : T_16.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_18 : T_18.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_19 : T_19.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_22 : T_22.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_23 : T_23.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_25 : T_25.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_26 : T_26.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_31 : T_31.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_32 : T_32.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_34 : T_34.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_35 : T_35.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_38 : T_38.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_39 : T_39.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_41 : T_41.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_42 : T_42.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_46 : T_46.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_47 : T_47.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_49 : T_49.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_50 : T_50.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_53 : T_53.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_54 : T_54.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_56 : T_56.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_57 : T_57.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_63 : T_63.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_64 : T_64.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_66 : T_66.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_67 : T_67.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_70 : T_70.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_71 : T_71.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_73 : T_73.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_74 : T_74.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_78 : T_78.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_79 : T_79.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_81 : T_81.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_82 : T_82.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_85 : T_85.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_86 : T_86.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_88 : T_88.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_89 : T_89.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_94 : T_94.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_95 : T_95.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_97 : T_97.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_98 : T_98.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_101 : T_101.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_102 : T_102.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_104 : T_104.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_105 : T_105.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_109 : T_109.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_110 : T_110.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_112 : T_112.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_113 : T_113.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_116 : T_116.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_117 : T_117.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_119 : T_119.allOK chk = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem p_T_120 : T_120.allOK chk = true := by decide +kernel
theorem p_N_2 : N_2.allOK chk = true := BT.allOK_n p_T_0 (by decide +kernel) p_T_1
theorem p_N_5 : N_5.allOK chk = true := BT.allOK_n p_T_3 (by decide +kernel) p_T_4
theorem p_N_6 : N_6.allOK chk = true := BT.allOK_n p_N_2 (by decide +kernel) p_N_5
theorem p_N_9 : N_9.allOK chk = true := BT.allOK_n p_T_7 (by decide +kernel) p_T_8
theorem p_N_12 : N_12.allOK chk = true := BT.allOK_n p_T_10 (by decide +kernel) p_T_11
theorem p_N_13 : N_13.allOK chk = true := BT.allOK_n p_N_9 (by decide +kernel) p_N_12
theorem p_N_14 : N_14.allOK chk = true := BT.allOK_n p_N_6 (by decide +kernel) p_N_13
theorem p_N_17 : N_17.allOK chk = true := BT.allOK_n p_T_15 (by decide +kernel) p_T_16
theorem p_N_20 : N_20.allOK chk = true := BT.allOK_n p_T_18 (by decide +kernel) p_T_19
theorem p_N_21 : N_21.allOK chk = true := BT.allOK_n p_N_17 (by decide +kernel) p_N_20
theorem p_N_24 : N_24.allOK chk = true := BT.allOK_n p_T_22 (by decide +kernel) p_T_23
theorem p_N_27 : N_27.allOK chk = true := BT.allOK_n p_T_25 (by decide +kernel) p_T_26
theorem p_N_28 : N_28.allOK chk = true := BT.allOK_n p_N_24 (by decide +kernel) p_N_27
theorem p_N_29 : N_29.allOK chk = true := BT.allOK_n p_N_21 (by decide +kernel) p_N_28
theorem p_N_30 : N_30.allOK chk = true := BT.allOK_n p_N_14 (by decide +kernel) p_N_29
theorem p_N_33 : N_33.allOK chk = true := BT.allOK_n p_T_31 (by decide +kernel) p_T_32
theorem p_N_36 : N_36.allOK chk = true := BT.allOK_n p_T_34 (by decide +kernel) p_T_35
theorem p_N_37 : N_37.allOK chk = true := BT.allOK_n p_N_33 (by decide +kernel) p_N_36
theorem p_N_40 : N_40.allOK chk = true := BT.allOK_n p_T_38 (by decide +kernel) p_T_39
theorem p_N_43 : N_43.allOK chk = true := BT.allOK_n p_T_41 (by decide +kernel) p_T_42
theorem p_N_44 : N_44.allOK chk = true := BT.allOK_n p_N_40 (by decide +kernel) p_N_43
theorem p_N_45 : N_45.allOK chk = true := BT.allOK_n p_N_37 (by decide +kernel) p_N_44
theorem p_N_48 : N_48.allOK chk = true := BT.allOK_n p_T_46 (by decide +kernel) p_T_47
theorem p_N_51 : N_51.allOK chk = true := BT.allOK_n p_T_49 (by decide +kernel) p_T_50
theorem p_N_52 : N_52.allOK chk = true := BT.allOK_n p_N_48 (by decide +kernel) p_N_51
theorem p_N_55 : N_55.allOK chk = true := BT.allOK_n p_T_53 (by decide +kernel) p_T_54
theorem p_N_58 : N_58.allOK chk = true := BT.allOK_n p_T_56 (by decide +kernel) p_T_57
theorem p_N_59 : N_59.allOK chk = true := BT.allOK_n p_N_55 (by decide +kernel) p_N_58
theorem p_N_60 : N_60.allOK chk = true := BT.allOK_n p_N_52 (by decide +kernel) p_N_59
theorem p_N_61 : N_61.allOK chk = true := BT.allOK_n p_N_45 (by decide +kernel) p_N_60
theorem p_N_62 : N_62.allOK chk = true := BT.allOK_n p_N_30 (by decide +kernel) p_N_61
theorem p_N_65 : N_65.allOK chk = true := BT.allOK_n p_T_63 (by decide +kernel) p_T_64
theorem p_N_68 : N_68.allOK chk = true := BT.allOK_n p_T_66 (by decide +kernel) p_T_67
theorem p_N_69 : N_69.allOK chk = true := BT.allOK_n p_N_65 (by decide +kernel) p_N_68
theorem p_N_72 : N_72.allOK chk = true := BT.allOK_n p_T_70 (by decide +kernel) p_T_71
theorem p_N_75 : N_75.allOK chk = true := BT.allOK_n p_T_73 (by decide +kernel) p_T_74
theorem p_N_76 : N_76.allOK chk = true := BT.allOK_n p_N_72 (by decide +kernel) p_N_75
theorem p_N_77 : N_77.allOK chk = true := BT.allOK_n p_N_69 (by decide +kernel) p_N_76
theorem p_N_80 : N_80.allOK chk = true := BT.allOK_n p_T_78 (by decide +kernel) p_T_79
theorem p_N_83 : N_83.allOK chk = true := BT.allOK_n p_T_81 (by decide +kernel) p_T_82
theorem p_N_84 : N_84.allOK chk = true := BT.allOK_n p_N_80 (by decide +kernel) p_N_83
theorem p_N_87 : N_87.allOK chk = true := BT.allOK_n p_T_85 (by decide +kernel) p_T_86
theorem p_N_90 : N_90.allOK chk = true := BT.allOK_n p_T_88 (by decide +kernel) p_T_89
theorem p_N_91 : N_91.allOK chk = true := BT.allOK_n p_N_87 (by decide +kernel) p_N_90
theorem p_N_92 : N_92.allOK chk = true := BT.allOK_n p_N_84 (by decide +kernel) p_N_91
theorem p_N_93 : N_93.allOK chk = true := BT.allOK_n p_N_77 (by decide +kernel) p_N_92
theorem p_N_96 : N_96.allOK chk = true := BT.allOK_n p_T_94 (by decide +kernel) p_T_95
theorem p_N_99 : N_99.allOK chk = true := BT.allOK_n p_T_97 (by decide +kernel) p_T_98
theorem p_N_100 : N_100.allOK chk = true := BT.allOK_n p_N_96 (by decide +kernel) p_N_99
theorem p_N_103 : N_103.allOK chk = true := BT.allOK_n p_T_101 (by decide +kernel) p_T_102
theorem p_N_106 : N_106.allOK chk = true := BT.allOK_n p_T_104 (by decide +kernel) p_T_105
theorem p_N_107 : N_107.allOK chk = true := BT.allOK_n p_N_103 (by decide +kernel) p_N_106
theorem p_N_108 : N_108.allOK chk = true := BT.allOK_n p_N_100 (by decide +kernel) p_N_107
theorem p_N_111 : N_111.allOK chk = true := BT.allOK_n p_T_109 (by decide +kernel) p_T_110
theorem p_N_114 : N_114.allOK chk = true := BT.allOK_n p_T_112 (by decide +kernel) p_T_113
theorem p_N_115 : N_115.allOK chk = true := BT.allOK_n p_N_111 (by decide +kernel) p_N_114
theorem p_N_118 : N_118.allOK chk = true := BT.allOK_n p_T_116 (by decide +kernel) p_T_117
theorem p_N_121 : N_121.allOK chk = true := BT.allOK_n p_T_119 (by decide +kernel) p_T_120
theorem p_N_122 : N_122.allOK chk = true := BT.allOK_n p_N_118 (by decide +kernel) p_N_121
theorem p_N_123 : N_123.allOK chk = true := BT.allOK_n p_N_115 (by decide +kernel) p_N_122
theorem p_N_124 : N_124.allOK chk = true := BT.allOK_n p_N_108 (by decide +kernel) p_N_123
theorem p_N_125 : N_125.allOK chk = true := BT.allOK_n p_N_93 (by decide +kernel) p_N_124
theorem p_N_126 : N_126.allOK chk = true := BT.allOK_n p_N_62 (by decide +kernel) p_N_125
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, chk x h = true := BT.mem_allOK T_cert chk p_N_126

def seven : BFn 7 := fun x => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

def sixG : BFn 6 := fun x =>
  (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5) ||
  (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 3 && x 4) ||
  (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5)

def perm7 (i : Fin 7) : Fin 7 :=
  match i.val with
  | 0 => 0
  | 1 => 2
  | 2 => 6
  | 3 => 1
  | 4 => 3
  | 5 => 4
  | _ => 5

def rearranged : BFn 7 := fun x => seven (x ∘ perm7)

theorem sixG_eq : (fun y : Fin 6 → Bool => rearranged (Fin.snoc y false)) = sixG := by
  funext y
  revert y
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem lb6 : ∀ s : ℕ, HasCircuitSize 6 sixG s → 11 ≤ s :=
  lb_cert sixG L_ M_ Y_ XS_ PD_ PM_ V6_ G_ T_cert 10 11 rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨fun _ => false, fun _ => true, by decide +kernel⟩
    (by decide +kernel) (by decide +kernel) hT_cert (by decide +kernel)

theorem lb7 (t : ℕ) (h : HasCircuitSize 7 seven t) : 12 ≤ t := by
  have hrel : HasCircuitSize 7 rearranged t := Restrict.relabel_size perm7 seven t h
  have hdep : ∃ x : Fin 7 → Bool,
      rearranged (Function.update x (Fin.last 6) (!x (Fin.last 6))) ≠ rearranged x :=
    ⟨fun i => decide (i = 3), by decide +kernel⟩
  have hnc : ∃ y y' : Fin 6 → Bool,
      rearranged (Fin.snoc y false) ≠ rearranged (Fin.snoc y' false) :=
    ⟨fun _ => false, fun _ => true, by decide +kernel⟩
  obtain ⟨s', hs', h6⟩ := Restrict.gate_elim_one 6 rearranged false t hdep hnc hrel
  rw [sixG_eq] at h6
  have h11 := lb6 s' h6
  omega

def W_ : List Gate :=
  [⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [0, 8]⟩,
   ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [9, 11]⟩, ⟨GateOp.or, [0, 12]⟩,
   ⟨GateOp.and, [3, 14]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.or, [13, 17]⟩]

theorem W_ok : ∀ g ∈ W_, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [W_, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem step_or (gs : List Gate) (a b : ℕ) (w w' : List Bool) (v : Bool)
    (hv : (w.getD a false || w.getD b false) = v) (hw : w ++ [v] = w') :
    (⟨GateOp.or, [a, b]⟩ :: gs).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w =
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w' := by
  subst hw; subst hv; simp [List.foldl, GateOp.eval]

theorem step_and (gs : List Gate) (a b : ℕ) (w w' : List Bool) (v : Bool)
    (hv : (w.getD a false && w.getD b false) = v) (hw : w ++ [v] = w') :
    (⟨GateOp.and, [a, b]⟩ :: gs).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w =
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w' := by
  subst hw; subst hv; simp [List.foldl, GateOp.eval]

def evalFast (x0 x1 x2 x3 x4 x5 x6 : Bool) : Bool :=
  let g0 := x1 || x5
  let g1 := x1 || x4
  let g2 := x2 || g0
  let g3 := x0 || g1
  let g4 := x4 || x6
  let g5 := x5 || x6
  let g6 := g2 && g4
  let g7 := x0 || g5
  let g8 := x3 && g7
  let g9 := g3 && g5
  let g10 := g8 || g9
  g6 || g10

theorem eval_W (x0 x1 x2 x3 x4 x5 x6 : Bool) :
    Circuit.eval ⟨W_, 18⟩ [x0, x1, x2, x3, x4, x5, x6] = evalFast x0 x1 x2 x3 x4 x5 x6 := by
  unfold Circuit.eval Circuit.wires W_ evalFast
  dsimp only
  generalize hg0 : (x1 || x5) = g0
  generalize hg1 : (x1 || x4) = g1
  generalize hg2 : (x2 || g0) = g2
  generalize hg3 : (x0 || g1) = g3
  generalize hg4 : (x4 || x6) = g4
  generalize hg5 : (x5 || x6) = g5
  generalize hg6 : (g2 && g4) = g6
  generalize hg7 : (x0 || g5) = g7
  generalize hg8 : (x3 && g7) = g8
  generalize hg9 : (g3 && g5) = g9
  generalize hg10 : (g8 || g9) = g10
  generalize hg11 : (g6 || g10) = g11
  rw [step_or _ _ _ _ [x0,x1,x2,x3,x4,x5,x6,g0] g0 (by exact hg0) rfl]
  rw [step_or _ _ _ _ [x0,x1,x2,x3,x4,x5,x6,g0,g1] g1 (by exact hg1) rfl]
  rw [step_or _ _ _ _ [x0,x1,x2,x3,x4,x5,x6,g0,g1,g2] g2 (by exact hg2) rfl]
  rw [step_or _ _ _ _ [x0,x1,x2,x3,x4,x5,x6,g0,g1,g2,g3] g3 (by exact hg3) rfl]
  rw [step_or _ _ _ _ [x0,x1,x2,x3,x4,x5,x6,g0,g1,g2,g3,g4] g4 (by exact hg4) rfl]
  rw [step_or _ _ _ _ [x0,x1,x2,x3,x4,x5,x6,g0,g1,g2,g3,g4,g5] g5 (by exact hg5) rfl]
  rw [step_and _ _ _ _ [x0,x1,x2,x3,x4,x5,x6,g0,g1,g2,g3,g4,g5,g6] g6 (by exact hg6) rfl]
  rw [step_or _ _ _ _ [x0,x1,x2,x3,x4,x5,x6,g0,g1,g2,g3,g4,g5,g6,g7] g7 (by exact hg7) rfl]
  rw [step_and _ _ _ _ [x0,x1,x2,x3,x4,x5,x6,g0,g1,g2,g3,g4,g5,g6,g7,g8] g8 (by exact hg8) rfl]
  rw [step_and _ _ _ _ [x0,x1,x2,x3,x4,x5,x6,g0,g1,g2,g3,g4,g5,g6,g7,g8,g9] g9 (by exact hg9) rfl]
  rw [step_or _ _ _ _ [x0,x1,x2,x3,x4,x5,x6,g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,g10] g10 (by exact hg10) rfl]
  rw [step_or _ _ _ _ [x0,x1,x2,x3,x4,x5,x6,g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11] g11 (by exact hg11) rfl]
  rfl

theorem W_val : ∀ x : Fin 7 → Bool, Circuit.eval ⟨W_, 18⟩ (List.ofFn x) = seven x := by
  intro x
  have h1 : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by simp [List.ofFn_succ]
  rw [h1, eval_W]
  revert x
  decide +kernel

end PEqualNP.Outside.L_meta_10638

theorem PEqualNP.Outside.L_meta_10638 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hops _ hf
  have h : PEqualNP.MetaComplexity.HasCircuitSize 7 PEqualNP.Outside.L_meta_10638.seven gates.length := by
    refine ⟨⟨gates, o⟩, ?_, le_rfl, hf⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hops g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  exact ⟨PEqualNP.Outside.L_meta_10638.W_, 18,
    PEqualNP.Outside.L_meta_10638.W_ok,
    PEqualNP.Outside.L_meta_10638.lb7 gates.length h,
    PEqualNP.Outside.L_meta_10638.W_val⟩
