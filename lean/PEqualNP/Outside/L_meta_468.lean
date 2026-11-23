import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_468_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w = wiresFrom gs (step w g) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) :=
  List.foldl_append

private lemma length_wiresFrom (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresFrom]
  | cons g gs ih =>
    intro w
    rw [wiresFrom_cons, ih]
    simp [step]
    omega

private lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, htl⟩ := ih (step w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, by simp [htl]⟩
    rw [wiresFrom_cons, ht, step, List.append_assoc]

private lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

private lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) :
    (L ++ [S]).getD L.length d = S := by
  simp

private lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

private lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (i : ℕ) (hi : i ≠ L.length) :
    (L ++ [S]).getD i d = L.getD i d := by
  by_cases hlt : i < L.length
  · exact List.getD_append _ _ _ _ hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

private def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private lemma normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
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

private lemma wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
    simp only [step, normGate_eval]
    exact ih _

private abbrev Stat := Bool ⊕ ℕ

private def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
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

private lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
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

private lemma simplify_kill_and (m : ℕ) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hc : Sum.inl false ∈ ins) :
    simplify GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at hc
  · cases a <;> simp_all [simplify, simpAnd]
  · rcases a with ca | ja <;> rcases b with cb | jb <;>
      (try cases ca) <;> (try cases cb) <;> simp_all [simplify, simpAnd]
  · simp at hlen

private lemma simplify_kill_or (m : ℕ) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hc : Sum.inl true ∈ ins) :
    simplify GateOp.or m ins = (none, Sum.inl true) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at hc
  · cases a <;> simp_all [simplify, simpOr]
  · rcases a with ca | ja <;> rcases b with cb | jb <;>
      (try cases ca) <;> (try cases cb) <;> simp_all [simplify, simpOr]
  · simp at hlen

private lemma simplify_kill_not (m : ℕ) (ins : List Stat) (hlen : ins.length ≤ 1)
    (c : Bool) (hc : Sum.inl c ∈ ins) :
    simplify GateOp.not m ins = (none, Sum.inl (!c)) := by
  rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

private lemma simplify_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length)
      (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom, step]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom, step]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom, step]

private def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

private def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

private lemma elim_nil (n : ℕ) (acc : List Stat × List Gate) : elim n [] acc = acc := rfl

private lemma elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

private lemma elim_append (n : ℕ) (gs₁ gs₂ : List Gate) (acc : List Stat × List Gate) :
    elim n (gs₁ ++ gs₂) acc = elim n gs₂ (elim n gs₁ acc) :=
  List.foldl_append

private lemma elim_len1 (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp [elimStep]
    omega

private lemma elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

private lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

private lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

private lemma elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

private lemma statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat,
    statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

private lemma statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

private def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

private lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    rw [wiresFrom_cons, elim_cons]
    apply ih (step w g) (elimStep n acc g)
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
    refine ⟨by simp [elimStep, step, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) =
        (step w g).getD i false
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, step, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, step, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

private def initStatsAt (m : ℕ) (u : Fin m) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin m => if i = u then Sum.inl b else Sum.inr i.val)

private lemma initStatsAt_getD_self (m : ℕ) (u : Fin m) (b : Bool) :
    (initStatsAt m u b).getD u.val (Sum.inl false) = Sum.inl b := by
  unfold initStatsAt
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private lemma inv_initAt (m : ℕ) (u : Fin m) (b : Bool) (x : Fin m → Bool) :
    Inv m (List.ofFn x) (List.ofFn (Function.update x u b)) (initStatsAt m u b, []) := by
  refine ⟨by simp [initStatsAt], ?_⟩
  intro i
  by_cases hlt : i < m
  · unfold initStatsAt
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [List.getElem_ofFn, List.length_nil, Nat.add_zero]
    by_cases heq : (⟨i, hlt⟩ : Fin m) = u
    · simp [heq, statValid, statVal]
    · simp only [heq, ↓reduceIte, statValid, statVal, wiresFrom, List.foldl_nil,
        Function.update_of_ne heq]
      refine ⟨hlt, ?_⟩
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp
  · rw [List.getD_eq_default _ _ (by simp [initStatsAt]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

private lemma wiresFrom_indep2 (m₁ m₂ : ℕ) (gs : List Gate) :
    (∀ g ∈ gs, m₁ ∉ g.inputs ∧ m₂ ∉ g.inputs) →
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i : ℕ, i ≠ m₁ → i ≠ m₂ → w₁.getD i false = w₂.getD i false) →
      (wiresFrom gs w₁).length = (wiresFrom gs w₂).length ∧
      (∀ i : ℕ, i ≠ m₁ → i ≠ m₂ → (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false) := by
  induction gs with
  | nil => intro _ w₁ w₂ hlen hag; exact ⟨hlen, hag⟩
  | cons g gs ih =>
    intro hno w₁ w₂ hlen hag
    have hg : g.op.eval (g.inputs.map fun i => w₁.getD i false) =
        g.op.eval (g.inputs.map fun i => w₂.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      have h0 := hno g List.mem_cons_self
      exact hag i (fun e => h0.1 (e ▸ hi)) (fun e => h0.2 (e ▸ hi))
    rw [wiresFrom_cons, wiresFrom_cons]
    apply ih (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hlen]
    · intro i hi1 hi2
      simp only [step, hg]
      by_cases hil : i = w₁.length
      · subst hil; rw [getD_snoc_eq, hlen, getD_snoc_eq]
      · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]; exact hag i hi1 hi2

private lemma split_first_reading (k : ℕ) (gs : List Gate) (hex : ∃ g ∈ gs, k ∈ g.inputs) :
    ∃ (gs1 : List Gate) (g1 : Gate) (gs2 : List Gate),
      gs = gs1 ++ [g1] ++ gs2 ∧ (∀ g ∈ gs1, k ∉ g.inputs) ∧ k ∈ g1.inputs := by
  induction gs with
  | nil => obtain ⟨g, hg, _⟩ := hex; simp at hg
  | cons g gs ih =>
    by_cases hkg : k ∈ g.inputs
    · exact ⟨[], g, gs, rfl, by simp, hkg⟩
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      obtain ⟨gs1, g1, gs2, hgs, hno, hmem⟩ := ih hex'
      refine ⟨g :: gs1, g1, gs2, ?_, ?_, hmem⟩
      · simp [hgs]
      · intro g' hg'
        rcases List.mem_cons.1 hg' with rfl | h
        · exact hkg
        · exact hno g' h

private lemma gate_elim_one (m : ℕ) (f : (Fin m → Bool) → Bool) (u : Fin m) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin m → Bool, f (Function.update x u false) ≠ f (Function.update x u true))
    (hnc : ∃ x x' : Fin m → Bool, f (Function.update x u b) ≠ f (Function.update x' u b))
    (h : HasCircuitSize m f s) :
    1 ≤ s ∧ HasCircuitSize m (fun x : Fin m → Bool => f (Function.update x u b)) (s - 1) := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin m → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x; rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim m gs (initStatsAt m u b, []) with hacc
  have hinv : ∀ x : Fin m → Bool,
      Inv m (List.ofFn x) (wiresFrom gs (List.ofFn (Function.update x u b))) acc := by
    intro x
    exact inv_elim m _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_initAt m u b x)
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false))
        = f (Function.update x u b) := by
    intro x; rw [((hinv x).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨x, x', hne⟩ := hnc
    apply hne
    rw [← hval x, ← hval x', hst]; rfl
  | inr j =>
    have hread : ∃ g ∈ gs, u.val ∈ g.inputs := by
      by_contra hno
      push Not at hno
      have hout : C.output ≠ u.val := by
        intro e
        rw [e, hacc, elim_getD m u.val _ gs _ (by simp [initStatsAt])] at hst
        have hb := initStatsAt_getD_self m u b
        rw [show ((initStatsAt m u b, ([] : List Gate))).1 = initStatsAt m u b from rfl, hb] at hst
        cases hst
      obtain ⟨x, hx⟩ := hdep
      apply hx
      rw [← hevg, ← hevg]
      have hag := (wiresFrom_indep2 u.val u.val gs (fun g hg => ⟨hno g hg, hno g hg⟩)
        (List.ofFn (Function.update x u false)) (List.ofFn (Function.update x u true))
        (by simp) (by
          intro i hi _
          by_cases hlt : i < m
          · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
            simp only [List.getElem_ofFn]
            have hne : (⟨i, hlt⟩ : Fin m) ≠ u := fun e => hi (congrArg Fin.val e)
            rw [Function.update_of_ne hne, Function.update_of_ne hne]
          · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])).2
      exact hag C.output hout hout
    have hlt := elim_len_lt m u.val gs (initStatsAt m u b, []) hnok (by simp [initStatsAt])
      ⟨b, initStatsAt_getD_self m u b⟩ hread
    rw [← hacc] at hlt
    have hl : gs.length = C.gates.length := by simp [hgs]
    simp only [List.length_nil, zero_add] at hlt
    refine ⟨by omega, ⟨acc.2, j⟩, elim_ok m gs _ (by simp), by show acc.2.length ≤ s - 1; omega, ?_⟩
    intro x
    have := hval x
    rw [hst] at this
    exact this

private lemma gate_elim_two (m : ℕ) (f : (Fin m → Bool) → Bool) (u : Fin m) (s : ℕ)
    (hdep : ∃ x : Fin m → Bool, f (Function.update x u false) ≠ f (Function.update x u true))
    (hnc0 : ∃ x x' : Fin m → Bool, f (Function.update x u false) ≠ f (Function.update x' u false))
    (hnc1 : ∃ x x' : Fin m → Bool, f (Function.update x u true) ≠ f (Function.update x' u true))
    (h : HasCircuitSize m f s) :
    (2 ≤ s ∧ HasCircuitSize m (fun x => f (Function.update x u false)) (s - 2)) ∨
    (2 ≤ s ∧ HasCircuitSize m (fun x => f (Function.update x u true)) (s - 2)) := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin m → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x; rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hread : ∃ g ∈ gs, u.val ∈ g.inputs := by
    by_contra hno
    push Not at hno
    by_cases hout : C.output = u.val
    · obtain ⟨x, x', hne⟩ := hnc0
      apply hne
      rw [← hevg, ← hevg, hout]
      rw [getD_wiresFrom _ _ _ (by simp), getD_wiresFrom _ _ _ (by simp)]
      rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
      simp
    · obtain ⟨x, hx⟩ := hdep
      apply hx
      rw [← hevg, ← hevg]
      have hag := (wiresFrom_indep2 u.val u.val gs (fun g hg => ⟨hno g hg, hno g hg⟩)
        (List.ofFn (Function.update x u false)) (List.ofFn (Function.update x u true))
        (by simp) (by
          intro i hi _
          by_cases hlt : i < m
          · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
            simp only [List.getElem_ofFn]
            have hne : (⟨i, hlt⟩ : Fin m) ≠ u := fun e => hi (congrArg Fin.val e)
            rw [Function.update_of_ne hne, Function.update_of_ne hne]
          · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])).2
      exact hag C.output hout hout
  obtain ⟨gs1, g1, gs2, hsplit, hno1, hmem1⟩ := split_first_reading u.val gs hread
  have hlen_split : gs.length = gs1.length + 1 + gs2.length := by
    rw [hsplit]; simp; omega
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok1 : NOk g1 := hnok g1 (by rw [hsplit]; simp)
  have hnok2 : ∀ g ∈ gs2, NOk g := fun g hg => hnok g (by rw [hsplit]; simp [hg])
  have mk_res : ∀ (b : Bool),
      (∃ x x' : Fin m → Bool, f (Function.update x u b) ≠ f (Function.update x' u b)) →
      (elim m gs (initStatsAt m u b, [])).2.length + 2 ≤ gs.length →
      2 ≤ s ∧ HasCircuitSize m (fun x => f (Function.update x u b)) (s - 2) := by
    intro b hncb hle2
    set acc := elim m gs (initStatsAt m u b, []) with hacc
    have hinv : ∀ x : Fin m → Bool,
        Inv m (List.ofFn x) (wiresFrom gs (List.ofFn (Function.update x u b))) acc := by
      intro x
      exact inv_elim m _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_initAt m u b x)
    have hval : ∀ x : Fin m → Bool,
        statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false))
          = f (Function.update x u b) := by
      intro x; rw [((hinv x).2 C.output).2, hevg]
    cases hst : acc.1.getD C.output (Sum.inl false) with
    | inl c =>
      exfalso
      obtain ⟨x, x', hne⟩ := hncb
      apply hne
      rw [← hval x, ← hval x', hst]; rfl
    | inr j =>
      refine ⟨by omega, ⟨acc.2, j⟩, elim_ok m gs _ (by simp), by show acc.2.length ≤ s - 2; omega, ?_⟩
      intro x
      have := hval x
      rw [hst] at this
      exact this
  by_cases hread2 : ∃ g ∈ gs2, u.val ∈ g.inputs
  · right
    apply mk_res true hnc1
    rw [hsplit, elim_append, elim_append, elim_cons, elim_nil]
    set acc1 := elim m gs1 (initStatsAt m u true, [])
    have h1len : acc1.2.length ≤ gs1.length := by
      have := elim_len m gs1 (initStatsAt m u true, [])
      simpa using this
    have hu1 : acc1.1.getD u.val (Sum.inl false) = Sum.inl true := by
      rw [elim_getD m u.val _ gs1 _ (by simp [initStatsAt])]
      exact initStatsAt_getD_self m u true
    have hnone1 : (simplify g1.op (m + acc1.2.length)
        (g1.inputs.map fun i => acc1.1.getD i (Sum.inl false))).1 = none := by
      apply simplify_count
      · exact hnok1.1.1
      · simpa using hnok1.1.2
      · intro h; simpa using hnok1.2 h
      · exact ⟨true, List.mem_map.2 ⟨u.val, hmem1, hu1⟩⟩
    have hstep_len : (elimStep m acc1 g1).2.length = acc1.2.length := by
      show (acc1.2 ++ (simplify g1.op (m + acc1.2.length)
        (g1.inputs.map fun i => acc1.1.getD i (Sum.inl false))).1.toList).length = _
      rw [hnone1]; simp
    have hl1 : acc1.1.length = m + gs1.length := by rw [elim_len1]; simp [initStatsAt]
    have hu2 : (elimStep m acc1 g1).1.getD u.val (Sum.inl false) = Sum.inl true := by
      simp only [elimStep]
      rw [getD_snoc_ne _ _ _ _ (by omega), hu1]
    have h2len := elim_len_lt m u.val gs2 (elimStep m acc1 g1) hnok2
      (by simp [elimStep, hl1]; omega) ⟨true, hu2⟩ hread2
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · push Not at hread2
    have hread_w1 : ∃ g ∈ gs2, (m + gs1.length) ∈ g.inputs := by
      by_contra hnow1
      push Not at hnow1
      have hnot_out_u : C.output ≠ u.val := by
        intro e
        obtain ⟨x, x', hne⟩ := hnc0
        apply hne
        rw [← hevg, ← hevg, e, getD_wiresFrom _ _ _ (by simp), getD_wiresFrom _ _ _ (by simp),
          List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
        simp
      have hnot_out_w1 : C.output ≠ m + gs1.length := by
        intro e
        have hconst : ∀ (b : Bool) (c : Bool),
            (∀ (acc1 : List Stat × List Gate), acc1 = elim m gs1 (initStatsAt m u b, []) →
              (simplify g1.op (m + acc1.2.length)
                (g1.inputs.map fun i => acc1.1.getD i (Sum.inl false))).2 = Sum.inl c) →
            ∀ x : Fin m → Bool, f (Function.update x u b) = c := by
          intro b c hsimp x
          have hinv := inv_elim m (List.ofFn x) (by simp) gs
            (List.ofFn (Function.update x u b)) (initStatsAt m u b, [])
            (fun g hg => (hnok g hg).1) (inv_initAt m u b x)
          rw [← hevg, ← (hinv.2 C.output).2, e, hsplit, elim_append, elim_append, elim_cons, elim_nil]
          set acc1 := elim m gs1 (initStatsAt m u b, []) with hacc1
          have hl1 : acc1.1.length = m + gs1.length := by rw [hacc1, elim_len1]; simp [initStatsAt]
          rw [elim_getD m (m + gs1.length) _ gs2 _ (by simp [elimStep, hl1])]
          simp only [elimStep]
          rw [getD_snoc_len _ _ _ _ hl1, hsimp acc1 hacc1]
          rfl
        rcases hnok1.1.1 with hop | hop | hop
        · have hce : ∀ x, f (Function.update x u false) = false := by
            apply hconst false false
            intro acc1 hacc1
            have hu1 : acc1.1.getD u.val (Sum.inl false) = Sum.inl false := by
              rw [hacc1, elim_getD m u.val _ gs1 _ (by simp [initStatsAt])]
              exact initStatsAt_getD_self m u false
            have h := simplify_kill_and (m + acc1.2.length)
              (g1.inputs.map fun i => acc1.1.getD i (Sum.inl false))
              (by simpa using hnok1.1.2) (List.mem_map.2 ⟨u.val, hmem1, hu1⟩)
            rw [hop, h]
          obtain ⟨x, x', hne⟩ := hnc0
          exact hne ((hce x).trans (hce x').symm)
        · have hce : ∀ x, f (Function.update x u true) = true := by
            apply hconst true true
            intro acc1 hacc1
            have hu1 : acc1.1.getD u.val (Sum.inl false) = Sum.inl true := by
              rw [hacc1, elim_getD m u.val _ gs1 _ (by simp [initStatsAt])]
              exact initStatsAt_getD_self m u true
            have h := simplify_kill_or (m + acc1.2.length)
              (g1.inputs.map fun i => acc1.1.getD i (Sum.inl false))
              (by simpa using hnok1.1.2) (List.mem_map.2 ⟨u.val, hmem1, hu1⟩)
            rw [hop, h]
          obtain ⟨x, x', hne⟩ := hnc1
          exact hne ((hce x).trans (hce x').symm)
        · have hce : ∀ x, f (Function.update x u true) = false := by
            apply hconst true false
            intro acc1 hacc1
            have hu1 : acc1.1.getD u.val (Sum.inl false) = Sum.inl true := by
              rw [hacc1, elim_getD m u.val _ gs1 _ (by simp [initStatsAt])]
              exact initStatsAt_getD_self m u true
            have h := simplify_kill_not (m + acc1.2.length)
              (g1.inputs.map fun i => acc1.1.getD i (Sum.inl false))
              (by simpa using hnok1.2 hop) true (List.mem_map.2 ⟨u.val, hmem1, hu1⟩)
            rw [hop, h]; rfl
          obtain ⟨x, x', hne⟩ := hnc1
          exact hne ((hce x).trans (hce x').symm)
      obtain ⟨x, hx⟩ := hdep
      apply hx
      rw [← hevg, ← hevg, hsplit, wiresFrom_append, wiresFrom_append, wiresFrom_append,
        wiresFrom_append, wiresFrom_cons, wiresFrom_nil, wiresFrom_cons, wiresFrom_nil]
      set W0 := wiresFrom gs1 (List.ofFn (Function.update x u false))
      set W1 := wiresFrom gs1 (List.ofFn (Function.update x u true))
      have hlen0 : W0.length = m + gs1.length := by rw [length_wiresFrom]; simp
      have hlen1 : W1.length = m + gs1.length := by rw [length_wiresFrom]; simp
      have hag1 := wiresFrom_indep2 u.val u.val gs1 (fun g hg => ⟨hno1 g hg, hno1 g hg⟩)
        (List.ofFn (Function.update x u false)) (List.ofFn (Function.update x u true))
        (by simp) (by
          intro i hi _
          by_cases hlt : i < m
          · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
            simp only [List.getElem_ofFn]
            have hne : (⟨i, hlt⟩ : Fin m) ≠ u := fun e => hi (congrArg Fin.val e)
            rw [Function.update_of_ne hne, Function.update_of_ne hne]
          · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
      have hag2 := wiresFrom_indep2 u.val (m + gs1.length) gs2
        (fun g hg => ⟨hread2 g hg, hnow1 g hg⟩) (step W0 g1) (step W1 g1)
        (by simp [step, hlen0, hlen1]) (by
          intro i hi1 hi2
          simp only [step]
          rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
          exact hag1.2 i hi1 hi1)
      exact hag2.2 C.output hnot_out_u hnot_out_w1
    rcases hnok1.1.1 with hop | hop | hop
    · left
      apply mk_res false hnc0
      rw [hsplit, elim_append, elim_append, elim_cons, elim_nil]
      set acc1 := elim m gs1 (initStatsAt m u false, [])
      have h1len : acc1.2.length ≤ gs1.length := by
        have := elim_len m gs1 (initStatsAt m u false, [])
        simpa using this
      have hl1 : acc1.1.length = m + gs1.length := by rw [elim_len1]; simp [initStatsAt]
      have hu1 : acc1.1.getD u.val (Sum.inl false) = Sum.inl false := by
        rw [elim_getD m u.val _ gs1 _ (by simp [initStatsAt])]
        exact initStatsAt_getD_self m u false
      have hkill := simplify_kill_and (m + acc1.2.length)
        (g1.inputs.map fun i => acc1.1.getD i (Sum.inl false))
        (by simpa using hnok1.1.2) (List.mem_map.2 ⟨u.val, hmem1, hu1⟩)
      have hstep_len : (elimStep m acc1 g1).2.length = acc1.2.length := by
        show (acc1.2 ++ (simplify g1.op (m + acc1.2.length)
          (g1.inputs.map fun i => acc1.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hop, hkill]; simp
      have hw1 : (elimStep m acc1 g1).1.getD (m + gs1.length) (Sum.inl false) = Sum.inl false := by
        simp only [elimStep]
        rw [getD_snoc_len _ _ _ _ hl1, hop, hkill]
      have h2len := elim_len_lt m (m + gs1.length) gs2 (elimStep m acc1 g1) hnok2
        (by simp [elimStep, hl1]) ⟨false, hw1⟩ hread_w1
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · right
      apply mk_res true hnc1
      rw [hsplit, elim_append, elim_append, elim_cons, elim_nil]
      set acc1 := elim m gs1 (initStatsAt m u true, [])
      have h1len : acc1.2.length ≤ gs1.length := by
        have := elim_len m gs1 (initStatsAt m u true, [])
        simpa using this
      have hl1 : acc1.1.length = m + gs1.length := by rw [elim_len1]; simp [initStatsAt]
      have hu1 : acc1.1.getD u.val (Sum.inl false) = Sum.inl true := by
        rw [elim_getD m u.val _ gs1 _ (by simp [initStatsAt])]
        exact initStatsAt_getD_self m u true
      have hkill := simplify_kill_or (m + acc1.2.length)
        (g1.inputs.map fun i => acc1.1.getD i (Sum.inl false))
        (by simpa using hnok1.1.2) (List.mem_map.2 ⟨u.val, hmem1, hu1⟩)
      have hstep_len : (elimStep m acc1 g1).2.length = acc1.2.length := by
        show (acc1.2 ++ (simplify g1.op (m + acc1.2.length)
          (g1.inputs.map fun i => acc1.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hop, hkill]; simp
      have hw1 : (elimStep m acc1 g1).1.getD (m + gs1.length) (Sum.inl false) = Sum.inl true := by
        simp only [elimStep]
        rw [getD_snoc_len _ _ _ _ hl1, hop, hkill]
      have h2len := elim_len_lt m (m + gs1.length) gs2 (elimStep m acc1 g1) hnok2
        (by simp [elimStep, hl1]) ⟨true, hw1⟩ hread_w1
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · right
      apply mk_res true hnc1
      rw [hsplit, elim_append, elim_append, elim_cons, elim_nil]
      set acc1 := elim m gs1 (initStatsAt m u true, [])
      have h1len : acc1.2.length ≤ gs1.length := by
        have := elim_len m gs1 (initStatsAt m u true, [])
        simpa using this
      have hl1 : acc1.1.length = m + gs1.length := by rw [elim_len1]; simp [initStatsAt]
      have hu1 : acc1.1.getD u.val (Sum.inl false) = Sum.inl true := by
        rw [elim_getD m u.val _ gs1 _ (by simp [initStatsAt])]
        exact initStatsAt_getD_self m u true
      have hkill := simplify_kill_not (m + acc1.2.length)
        (g1.inputs.map fun i => acc1.1.getD i (Sum.inl false))
        (by simpa using hnok1.2 hop) true (List.mem_map.2 ⟨u.val, hmem1, hu1⟩)
      have hstep_len : (elimStep m acc1 g1).2.length = acc1.2.length := by
        show (acc1.2 ++ (simplify g1.op (m + acc1.2.length)
          (g1.inputs.map fun i => acc1.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hop, hkill]; simp
      have hw1 : (elimStep m acc1 g1).1.getD (m + gs1.length) (Sum.inl false) = Sum.inl false := by
        simp only [elimStep]
        rw [getD_snoc_len _ _ _ _ hl1, hop, hkill]; rfl
      have h2len := elim_len_lt m (m + gs1.length) gs2 (elimStep m acc1 g1) hnok2
        (by simp [elimStep, hl1]) ⟨false, hw1⟩ hread_w1
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

private lemma drop_prefix_size (n k s : ℕ) (g : (Fin k → Bool) → Bool)
    (hnc : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (h : HasCircuitSize (n + k) (fun x : Fin (n + k) → Bool => g (fun j : Fin k => x (Fin.natAdd n j))) s) :
    HasCircuitSize k g s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  let init : List Stat :=
    List.ofFn (fun i : Fin (n + k) => if i.val < n then Sum.inl false else Sum.inr (i.val - n))
  set acc := elim k C.gates (init, []) with hacc
  have hinv : ∀ y : Fin k → Bool,
      Inv k (List.ofFn y)
        (wiresFrom C.gates (List.ofFn (fun i : Fin (n + k) =>
          if hi : i.val < n then false else y ⟨i.val - n, by omega⟩))) acc := by
    intro y
    apply inv_elim k (List.ofFn y) (by simp) C.gates _ (init, []) ok
    refine ⟨by simp [init], ?_⟩
    intro i
    by_cases hlt : i < n + k
    · rw [List.getD_eq_getElem _ _ (by simp [init]; omega),
        List.getD_eq_getElem _ _ (by simp; omega)]
      simp only [init, List.getElem_ofFn, List.length_nil, Nat.add_zero]
      by_cases hn : i < n
      · simp [hn, statValid, statVal]
      · simp only [hn, ↓reduceIte, ↓reduceDIte, statValid, statVal, wiresFrom, List.foldl_nil]
        refine ⟨by omega, ?_⟩
        rw [List.getD_eq_getElem _ _ (by simp; omega)]
        simp
    · rw [List.getD_eq_default _ _ (by simp [init]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hval : ∀ y : Fin k → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false)) = g y := by
    intro y
    rw [((hinv y).2 C.output).2]
    have h1 := hev (fun i : Fin (n + k) =>
      if hi : i.val < n then false else y ⟨i.val - n, by omega⟩)
    change (wiresFrom C.gates _).getD C.output false = _
    rw [show (wiresFrom C.gates _).getD C.output false =
      C.eval (List.ofFn fun i : Fin (n + k) =>
        if hi : i.val < n then false else y ⟨i.val - n, by omega⟩) from rfl, h1]
    dsimp only
    congr 1
    funext j
    simp
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length ≤ s := by
      have h1 := elim_len k C.gates (init, [])
      have hsz' : C.gates.length ≤ s := hsz
      rw [← hacc] at h1
      simp only [List.length_nil, zero_add] at h1
      omega
    refine ⟨⟨acc.2, j⟩, elim_ok k C.gates _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

private def shiftAddGate (n : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun w => w + n)⟩

private def AddRel (n : ℕ) (W W' : List Bool) : Prop :=
  W'.length = W.length + n ∧ ∀ w : ℕ, W'.getD (w + n) false = W.getD w false

private lemma addRel_step (n : ℕ) (W W' : List Bool) (g : Gate) (h : AddRel n W W') :
    AddRel n (step W g) (step W' (shiftAddGate n g)) := by
  obtain ⟨h1, h2⟩ := h
  have hv : (shiftAddGate n g).op.eval ((shiftAddGate n g).inputs.map fun i => W'.getD i false) =
      g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [shiftAddGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h2 a
  refine ⟨by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hw]
    exact h2 w
  · rw [hw, ← h1, getD_snoc_eq, getD_snoc_eq]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma addRel_fold (n : ℕ) (gs : List Gate) :
    ∀ W W' : List Bool, AddRel n W W' →
      AddRel n (wiresFrom gs W) (wiresFrom (gs.map (shiftAddGate n)) W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
    exact ih _ _ (addRel_step n W W' g h)

private def buildOrRest (cur : ℕ) (ws : List ℕ) (m : ℕ) : List Gate × ℕ :=
  match ws with
  | [] => ([], cur)
  | w :: rest =>
    let res := buildOrRest m rest (m + 1)
    (⟨GateOp.or, [cur, w]⟩ :: res.1, res.2)

private lemma buildOrRest_spec (ws : List ℕ) : ∀ (cur m : ℕ), cur < m → (∀ w ∈ ws, w < m) →
    (buildOrRest cur ws m).1.length = ws.length ∧
    (buildOrRest cur ws m).2 < m + ws.length ∧
    (∀ g ∈ (buildOrRest cur ws m).1, Ok g) ∧
    ∀ W : List Bool, W.length = m →
      (wiresFrom (buildOrRest cur ws m).1 W).getD (buildOrRest cur ws m).2 false =
        (W.getD cur false || ws.any (fun w => W.getD w false)) := by
  induction ws with
  | nil =>
    intro cur m hcm _
    refine ⟨rfl, by simp [buildOrRest]; omega, by simp [buildOrRest], ?_⟩
    intro W _
    simp [buildOrRest, wiresFrom]
  | cons w rest ih =>
    intro cur m hcm hws
    have hw : w < m := hws w List.mem_cons_self
    have hrest : ∀ z ∈ rest, z < m + 1 := fun z hz => by
      have := hws z (List.mem_cons_of_mem _ hz); omega
    obtain ⟨hlen, hout, hok, hev⟩ := ih m (m + 1) (by omega) hrest
    refine ⟨by simp [buildOrRest, hlen], by simp [buildOrRest]; omega, ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.1 hg with rfl | hg'
      · simp [Ok]
      · exact hok g hg'
    · intro W hW
      simp only [buildOrRest, wiresFrom_cons]
      have hW1 : (step W ⟨GateOp.or, [cur, w]⟩).length = m + 1 := by simp [step, hW]
      rw [hev (step W ⟨GateOp.or, [cur, w]⟩) hW1]
      have hm_val : (step W ⟨GateOp.or, [cur, w]⟩).getD m false = (W.getD cur false || W.getD w false) := by
        simp only [step, getD_snoc_len _ _ _ _ hW, GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, id_eq, Bool.or_false]
      have hrest_any : rest.any (fun z => (step W ⟨GateOp.or, [cur, w]⟩).getD z false) =
          rest.any (fun z => W.getD z false) := by
        apply Bool.eq_iff_iff.2
        simp only [List.any_eq_true]
        refine exists_congr fun z => and_congr_right fun hz => ?_
        have hzm : z < W.length := by have := hws z (List.mem_cons_of_mem _ hz); omega
        simp only [step, List.getD_append _ _ _ _ hzm]
      rw [hm_val, hrest_any, List.any_cons, Bool.or_assoc]

private def buildCoverBlocks (pairs : List (ℕ × List ℕ)) (cur m : ℕ) : List Gate × ℕ :=
  match pairs with
  | [] => ([], cur)
  | (u, ws) :: rest =>
    match ws with
    | [] => buildCoverBlocks rest cur m
    | w0 :: ws' =>
      let bOr := buildOrRest w0 ws' m
      let m1 := m + ws'.length
      let gAnd : Gate := ⟨GateOp.and, [u, bOr.2]⟩
      let gOr : Gate := ⟨GateOp.or, [cur, m1]⟩
      let tail := buildCoverBlocks rest (m1 + 1) (m1 + 2)
      (bOr.1 ++ [gAnd, gOr] ++ tail.1, tail.2)

private lemma buildCoverBlocks_spec (pairs : List (ℕ × List ℕ)) :
    ∀ (cur m : ℕ), cur < m →
      (∀ p ∈ pairs, p.1 < m ∧ 1 ≤ p.2.length ∧ ∀ w ∈ p.2, w < m) →
      (buildCoverBlocks pairs cur m).1.length = (pairs.map (fun p => p.2.length + 1)).sum ∧
      (buildCoverBlocks pairs cur m).2 < m + (pairs.map (fun p => p.2.length + 1)).sum ∧
      (∀ g ∈ (buildCoverBlocks pairs cur m).1, Ok g) ∧
      ∀ W : List Bool, W.length = m →
        (wiresFrom (buildCoverBlocks pairs cur m).1 W).getD (buildCoverBlocks pairs cur m).2 false =
          (W.getD cur false || pairs.any (fun p => W.getD p.1 false && p.2.any (fun w => W.getD w false))) := by
  induction pairs with
  | nil =>
    intro cur m hcm _
    refine ⟨rfl, by simp [buildCoverBlocks]; omega, by simp [buildCoverBlocks], ?_⟩
    intro W _; simp [buildCoverBlocks, wiresFrom]
  | cons p rest ih =>
    intro cur m hcm hpairs
    obtain ⟨u, ws⟩ := p
    have hp := hpairs (u, ws) List.mem_cons_self
    cases ws with
    | nil => simp at hp
    | cons w0 ws' =>
      have hw0 : w0 < m := hp.2.2 w0 List.mem_cons_self
      have hws' : ∀ w ∈ ws', w < m := fun w hw => hp.2.2 w (List.mem_cons_of_mem _ hw)
      obtain ⟨hblen, hbout, hbok, hbev⟩ := buildOrRest_spec ws' w0 m hw0 hws'
      set m1 := m + ws'.length with hm1
      have hrest_ok : ∀ q ∈ rest, q.1 < m1 + 2 ∧ 1 ≤ q.2.length ∧ ∀ w ∈ q.2, w < m1 + 2 := by
        intro q hq
        have hq0 := hpairs q (List.mem_cons_of_mem _ hq)
        exact ⟨by omega, hq0.2.1, fun w hw => by have := hq0.2.2 w hw; omega⟩
      obtain ⟨htlen, htout, htok, htev⟩ := ih (m1 + 1) (m1 + 2) (by omega) hrest_ok
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [buildCoverBlocks, List.length_append, List.length_cons, List.length_nil,
          hblen, ← hm1, htlen, List.map_cons, List.sum_cons]
      · simp only [buildCoverBlocks, ← hm1, List.map_cons, List.sum_cons, List.length_cons]
        omega
      · intro g hg
        simp only [buildCoverBlocks, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with (hg | rfl | rfl) | hg
        · exact hbok g hg
        · simp [Ok]
        · simp [Ok]
        · exact htok g hg
      · intro W hW
        simp only [buildCoverBlocks, ← hm1]
        rw [wiresFrom_append, wiresFrom_append]
        set W1 := wiresFrom (buildOrRest w0 ws' m).1 W with hW1
        have hlW1 : W1.length = m1 := by rw [hW1, length_wiresFrom, hW, hblen]
        set W2 := wiresFrom [⟨GateOp.and, [u, (buildOrRest w0 ws' m).2]⟩, ⟨GateOp.or, [cur, m1]⟩] W1
          with hW2
        have hlW2 : W2.length = m1 + 2 := by rw [hW2, length_wiresFrom, hlW1]; simp
        rw [htev W2 hlW2]
        have hW1_old : ∀ z : ℕ, z < m → W1.getD z false = W.getD z false := fun z hz =>
          getD_wiresFrom _ _ _ (by omega)
        have hW2_old : ∀ z : ℕ, z < m → W2.getD z false = W.getD z false := by
          intro z hz
          rw [hW2, getD_wiresFrom _ _ _ (by omega), hW1_old z hz]
        have hW1_or : W1.getD (buildOrRest w0 ws' m).2 false =
            (W.getD w0 false || ws'.any (fun w => W.getD w false)) := hbev W hW
        have hW2_m11 : W2.getD (m1 + 1) false =
            (W.getD cur false || (W.getD u false && (W.getD w0 false || ws'.any (fun w => W.getD w false)))) := by
          rw [hW2, wiresFrom_cons, wiresFrom_cons, wiresFrom_nil]
          set W1' := step W1 ⟨GateOp.and, [u, (buildOrRest w0 ws' m).2]⟩ with hW1'
          have hlW1' : W1'.length = m1 + 1 := by simp [hW1', step, hlW1]
          have hW1'_m1 : W1'.getD m1 false = (W1.getD u false && W1.getD (buildOrRest w0 ws' m).2 false) := by
            simp only [hW1', step, getD_snoc_len _ _ _ _ hlW1, GateOp.eval, List.map_cons,
              List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          have hW1'_cur : W1'.getD cur false = W.getD cur false := by
            rw [hW1', step, List.getD_append _ _ _ _ (by omega), hW1_old cur hcm]
          simp only [step, getD_snoc_len _ _ _ _ hlW1', GateOp.eval, List.map_cons, List.map_nil,
            List.any_cons, List.any_nil, id_eq, Bool.or_false, hW1'_cur, hW1'_m1,
            hW1_old u hp.1, hW1_or]
        have hrest_any : rest.any (fun q => W2.getD q.1 false && q.2.any (fun w => W2.getD w false)) =
            rest.any (fun q => W.getD q.1 false && q.2.any (fun w => W.getD w false)) := by
          apply Bool.eq_iff_iff.2
          simp only [List.any_eq_true, Bool.and_eq_true]
          refine exists_congr fun q => and_congr_right fun hq => ?_
          have hq0 := hpairs q (List.mem_cons_of_mem _ hq)
          rw [hW2_old q.1 hq0.1]
          refine and_congr_right fun _ => exists_congr fun w => and_congr_right fun hw => ?_
          rw [hW2_old w (hq0.2.2 w hw)]
        rw [hW2_m11, hrest_any, List.any_cons, List.any_cons, Bool.or_assoc]

private lemma adj_symm {n : ℕ} (G : SimpleGraph (Fin n)) {a b : Fin n} (h : G.Adj a b) : G.Adj b a :=
  (SimpleGraph.adj_comm G a b).1 h

private lemma adj_irrefl {n : ℕ} (G : SimpleGraph (Fin n)) (a : Fin n) : ¬ G.Adj a a :=
  G.loopless.irrefl a

private lemma upper_bound (n k c t s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    (hgnonconst : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (hgsize : ∀ r : ℕ, HasCircuitSize k g r ↔ c ≤ r)
    (hcover_ex : ∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = t)
    (hcover_min : ∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card)
    (hs : A.card + G.edgeFinset.card + t + c ≤ s) :
    HasCircuitSize (n + k) (fun x : Fin (n + k) → Bool =>
      decide ((∃ a ∈ A, x (Fin.castAdd k a) = true) ∨
        ∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) ||
      g (fun j : Fin k => x (Fin.natAdd n j))) s := by
  classical
  obtain ⟨Cg, hCg_ok, hCg_sz, hCg_ev⟩ := (hgsize c).2 (le_refl c)
  have hCg_out_lt : Cg.output < k + Cg.gates.length := by
    by_contra hge
    obtain ⟨y, y', hne⟩ := hgnonconst
    apply hne
    rw [← hCg_ev y, ← hCg_ev y']
    show (wiresFrom Cg.gates (List.ofFn y)).getD Cg.output false =
      (wiresFrom Cg.gates (List.ofFn y')).getD Cg.output false
    rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
      List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)]
  obtain ⟨S, hScov, hScard⟩ := hcover_ex
  let nbrs : Fin n → Finset (Fin n) := fun u =>
    Finset.univ.filter (fun w => G.Adj u w ∧ (w ∉ S ∨ u < w))
  have hnbrs_nonempty : ∀ u ∈ S, (nbrs u).Nonempty := by
    intro u hu
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hcov' : ∀ a b : Fin n, G.Adj a b → a ∈ S.erase u ∨ b ∈ S.erase u := by
      intro a b hab
      by_cases hau : a = u
      · subst hau
        have hbn : b ∉ nbrs a := by rw [hemp]; simp
        have hba : ¬ (G.Adj a b ∧ (b ∉ S ∨ a < b)) := by simpa [nbrs] using hbn
        have hbS : b ∈ S := by
          by_contra hbnot
          exact hba ⟨hab, Or.inl hbnot⟩
        exact Or.inr (Finset.mem_erase.2 ⟨(G.ne_of_adj hab).symm, hbS⟩)
      · by_cases hbu : b = u
        · subst hbu
          have han : a ∉ nbrs b := by rw [hemp]; simp
          have hab' : ¬ (G.Adj b a ∧ (a ∉ S ∨ b < a)) := by simpa [nbrs] using han
          have haS : a ∈ S := by
            by_contra hanot
            exact hab' ⟨adj_symm G hab, Or.inl hanot⟩
          exact Or.inl (Finset.mem_erase.2 ⟨G.ne_of_adj hab, haS⟩)
        · rcases hScov a b hab with ha | hb
          · exact Or.inl (Finset.mem_erase.2 ⟨hau, ha⟩)
          · exact Or.inr (Finset.mem_erase.2 ⟨hbu, hb⟩)
    have hmin := hcover_min (S.erase u) hcov'
    have hcard := Finset.card_erase_of_mem hu
    have hpos : 0 < S.card := Finset.card_pos.2 ⟨u, hu⟩
    omega
  have hsum_nbrs : ∑ u ∈ S, (nbrs u).card = G.edgeFinset.card := by
    let P : Finset (Fin n × Fin n) := S.biUnion (fun u => (nbrs u).image (fun w => (u, w)))
    have hPcard : P.card = ∑ u ∈ S, (nbrs u).card := by
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun u _ => ?_
        exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
      · intro u1 _ u2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        obtain ⟨_, _, rfl⟩ := Finset.mem_image.1 hp1
        obtain ⟨_, _, heq⟩ := Finset.mem_image.1 hp2
        exact hne (Prod.mk.inj heq).1.symm
    have hPimg : P.image (fun p => s(p.1, p.2)) = G.edgeFinset := by
      ext e
      simp only [Finset.mem_image, Finset.mem_biUnion, P, nbrs, Finset.mem_filter,
        Finset.mem_univ, true_and, SimpleGraph.mem_edgeFinset]
      induction e using Sym2.ind with
      | _ a b =>
        constructor
        · rintro ⟨⟨u, w⟩, ⟨_, _, ⟨_, ⟨hadj, _⟩, heq⟩⟩, hs2⟩
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [← hs2]
          exact hadj
        · intro hadj
          rcases hScov a b hadj with ha | hb
          · by_cases hbS : b ∈ S
            · rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with hlt | hgt
              · exact ⟨(a, b), ⟨a, ha, ⟨b, ⟨hadj, Or.inr hlt⟩, rfl⟩⟩, rfl⟩
              · exact ⟨(b, a), ⟨b, hbS, ⟨a, ⟨adj_symm G hadj, Or.inr hgt⟩, rfl⟩⟩, Sym2.eq_swap⟩
            · exact ⟨(a, b), ⟨a, ha, ⟨b, ⟨hadj, Or.inl hbS⟩, rfl⟩⟩, rfl⟩
          · by_cases haS : a ∈ S
            · rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with hlt | hgt
              · exact ⟨(a, b), ⟨a, haS, ⟨b, ⟨hadj, Or.inr hlt⟩, rfl⟩⟩, rfl⟩
              · exact ⟨(b, a), ⟨b, hb, ⟨a, ⟨adj_symm G hadj, Or.inr hgt⟩, rfl⟩⟩, Sym2.eq_swap⟩
            · exact ⟨(b, a), ⟨b, hb, ⟨a, ⟨adj_symm G hadj, Or.inl haS⟩, rfl⟩⟩, Sym2.eq_swap⟩
    have hPinj : Set.InjOn (fun p : Fin n × Fin n => s(p.1, p.2)) (P : Set (Fin n × Fin n)) := by
      intro p1 hp1 p2 hp2 heq
      obtain ⟨u1, hu1, hp1'⟩ := Finset.mem_biUnion.1 hp1
      obtain ⟨w1, hw1, rfl⟩ := Finset.mem_image.1 hp1'
      obtain ⟨u2, hu2, hp2'⟩ := Finset.mem_biUnion.1 hp2
      obtain ⟨w2, hw2, rfl⟩ := Finset.mem_image.1 hp2'
      have h1 := (Finset.mem_filter.1 hw1).2.2
      have h2 := (Finset.mem_filter.1 hw2).2.2
      rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exfalso
        rcases h1 with h1 | h1
        · exact h1 hu2
        · rcases h2 with h2 | h2
          · exact h2 hu1
          · exact lt_irrefl _ (lt_trans h1 h2)
    rw [← hPcard, ← hPimg, Finset.card_image_of_injOn hPinj]
  let gs0 : List Gate := Cg.gates.map (shiftAddGate n)
  let m0 : ℕ := n + k + Cg.gates.length
  let out0 : ℕ := Cg.output + n
  let pairs : List (ℕ × List ℕ) :=
    S.toList.map (fun u => (u.val, (nbrs u).toList.map Fin.val))
  have hpairs_ok : ∀ p ∈ pairs, p.1 < m0 ∧ 1 ≤ p.2.length ∧ ∀ w ∈ p.2, w < m0 := by
    intro p hp
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hp
    have huS : u ∈ S := Finset.mem_toList.1 hu
    obtain ⟨w0, hw0⟩ := hnbrs_nonempty u huS
    have hpos : 0 < (nbrs u).card := Finset.card_pos.2 ⟨w0, hw0⟩
    refine ⟨by have := u.isLt; omega, by simp only [List.length_map, Finset.length_toList]; omega, ?_⟩
    intro w hw
    obtain ⟨v, _, rfl⟩ := List.mem_map.1 hw
    have := v.isLt; omega
  have hpairs_sum : (pairs.map (fun p => p.2.length + 1)).sum = G.edgeFinset.card + t := by
    have h1 : pairs.map (fun p => p.2.length + 1) =
        S.toList.map (fun u => (nbrs u).card + 1) := by
      simp [pairs]
    rw [h1]
    have h2 : (S.toList.map (fun u => (nbrs u).card + 1)).sum = ∑ u ∈ S, ((nbrs u).card + 1) := by
      rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]; rfl
    rw [h2, Finset.sum_add_distrib, hsum_nbrs, Finset.sum_const, smul_eq_mul, mul_one, hScard]
  let blk := buildCoverBlocks pairs out0 m0
  obtain ⟨hblk_len, hblk_out, hblk_ok, hblk_ev⟩ := buildCoverBlocks_spec pairs out0 m0 (by omega) hpairs_ok
  let m1 : ℕ := m0 + (pairs.map (fun p => p.2.length + 1)).sum
  let aWires : List ℕ := A.toList.map Fin.val
  have haWires_lt : ∀ w ∈ aWires, w < m1 := by
    intro w hw
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hw
    have := a.isLt; omega
  let finOr := buildOrRest blk.2 aWires m1
  obtain ⟨hfin_len, _, hfin_ok, hfin_ev⟩ := buildOrRest_spec aWires blk.2 m1 hblk_out haWires_lt
  refine ⟨⟨gs0 ++ blk.1 ++ finOr.1, finOr.2⟩, ?_, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 ha
      exact ⟨(hCg_ok a0 ha0).1, by simpa [shiftAddGate] using (hCg_ok a0 ha0).2⟩
    · exact hblk_ok a ha
    · exact hfin_ok a ha
  · have hCg_sz' : Cg.gates.length ≤ c := hCg_sz
    have hblk' : blk.1.length = G.edgeFinset.card + t := hblk_len.trans hpairs_sum
    have hfin' : finOr.1.length = A.card := by
      rw [hfin_len]; simp [aWires]
    show (gs0 ++ blk.1 ++ finOr.1).length ≤ s
    simp only [List.length_append, gs0, List.length_map, hblk', hfin']
    omega
  · intro x
    let y : Fin k → Bool := fun j => x (Fin.natAdd n j)
    have hadd_init : AddRel n (List.ofFn y) (List.ofFn x) := by
      refine ⟨by simp; omega, ?_⟩
      intro w
      by_cases hlt : w < k
      · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
        simp only [List.getElem_ofFn, y]
        have heq : (⟨w + n, by omega⟩ : Fin (n + k)) = Fin.natAdd n ⟨w, hlt⟩ := by
          ext; simp [Nat.add_comm]
        rw [heq]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have hadd_fold := addRel_fold n Cg.gates (List.ofFn y) (List.ofFn x) hadd_init
    set W0 := wiresFrom gs0 (List.ofFn x) with hW0
    have hlW0 : W0.length = m0 := by rw [hW0, length_wiresFrom]; simp [gs0, m0]
    have hW0_g : W0.getD out0 false = g y := by
      rw [hW0, hadd_fold.2 Cg.output]
      exact hCg_ev y
    have hW0_in : ∀ u : Fin n, W0.getD u.val false = x (Fin.castAdd k u) := by
      intro u
      rw [hW0, getD_wiresFrom _ _ _ (by simp; have := u.isLt; omega)]
      rw [List.getD_eq_getElem _ _ (by simp; have := u.isLt; omega)]
      simp only [List.getElem_ofFn]
      rfl
    set W1 := wiresFrom blk.1 W0 with hW1
    have hlW1 : W1.length = m1 := by rw [hW1, length_wiresFrom, hlW0, hblk_len]
    have hW1_in : ∀ u : Fin n, W1.getD u.val false = x (Fin.castAdd k u) := by
      intro u
      rw [hW1, getD_wiresFrom _ _ _ (by rw [hlW0]; have := u.isLt; omega), hW0_in u]
    show (wiresFrom (gs0 ++ blk.1 ++ finOr.1) (List.ofFn x)).getD finOr.2 false = _
    rw [wiresFrom_append, wiresFrom_append, ← hW0, ← hW1, hfin_ev W1 hlW1, hW1, hblk_ev W0 hlW0, hW0_g]
    have hA_eq : aWires.any (fun w => W1.getD w false) = decide (∃ a ∈ A, x (Fin.castAdd k a) = true) := by
      apply Bool.eq_iff_iff.2
      simp only [aWires, List.any_eq_true, List.mem_map, Finset.mem_toList, decide_eq_true_eq]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, hval⟩
        exact ⟨a, ha, by rwa [← hW1_in a]⟩
      · rintro ⟨a, ha, hval⟩
        exact ⟨a.val, ⟨a, ha, rfl⟩, by rwa [hW1_in a]⟩
    have hE_eq : pairs.any (fun p => W0.getD p.1 false && p.2.any (fun w => W0.getD w false)) =
        decide (∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) := by
      apply Bool.eq_iff_iff.2
      simp only [pairs, List.any_eq_true, List.mem_map, Finset.mem_toList, Bool.and_eq_true,
        decide_eq_true_eq]
      constructor
      · rintro ⟨_, ⟨u, hu, rfl⟩, hxu, ⟨_, hwmem, hxw⟩⟩
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hwmem
        rw [Finset.mem_toList] at hw
        rw [hW0_in u] at hxu
        rw [hW0_in w] at hxw
        exact ⟨u, w, (Finset.mem_filter.1 hw).2.1, hxu, hxw⟩
      · rintro ⟨u, v, hadj, hxu, hxv⟩
        have mkPair : ∀ (a b : Fin n), a ∈ S → b ∈ nbrs a →
            x (Fin.castAdd k a) = true → x (Fin.castAdd k b) = true →
            ∃ p : ℕ × List ℕ, (∃ a' ∈ S, (a'.val, (nbrs a').toList.map Fin.val) = p) ∧
              W0.getD p.1 false = true ∧ ∃ w ∈ p.2, W0.getD w false = true := by
          intro a b haS hbn hxa hxb
          refine ⟨(a.val, (nbrs a).toList.map Fin.val), ⟨a, haS, rfl⟩, by rwa [hW0_in a],
            b.val, List.mem_map.2 ⟨b, Finset.mem_toList.2 hbn, rfl⟩, by rwa [hW0_in b]⟩
        rcases hScov u v hadj with hu | hv
        · by_cases hvS : v ∈ S
          · rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with hlt | hgt
            · exact mkPair u v hu (Finset.mem_filter.2 ⟨Finset.mem_univ _, hadj, Or.inr hlt⟩) hxu hxv
            · exact mkPair v u hvS (Finset.mem_filter.2 ⟨Finset.mem_univ _, adj_symm G hadj, Or.inr hgt⟩) hxv hxu
          · exact mkPair u v hu (Finset.mem_filter.2 ⟨Finset.mem_univ _, hadj, Or.inl hvS⟩) hxu hxv
        · by_cases huS : u ∈ S
          · rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with hlt | hgt
            · exact mkPair u v huS (Finset.mem_filter.2 ⟨Finset.mem_univ _, hadj, Or.inr hlt⟩) hxu hxv
            · exact mkPair v u hv (Finset.mem_filter.2 ⟨Finset.mem_univ _, adj_symm G hadj, Or.inr hgt⟩) hxv hxu
          · exact mkPair v u hv (Finset.mem_filter.2 ⟨Finset.mem_univ _, adj_symm G hadj, Or.inl huS⟩) hxv hxu
    dsimp only
    rw [hA_eq, hE_eq, Bool.decide_or]
    cases g y <;> cases decide (∃ a ∈ A, x (Fin.castAdd k a) = true) <;>
      cases decide (∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) <;>
      rfl

private lemma isPath_length_lt {n : ℕ} {G : SimpleGraph (Fin n)} {a b : Fin n}
    (p : G.Walk a b) (hp : p.IsPath) : p.length < n := by
  have h1 := hp.support_nodup.length_le_card
  rw [SimpleGraph.Walk.length_support, Fintype.card_fin] at h1
  omega

private lemma cycle_of_path_adj {n : ℕ} {G : SimpleGraph (Fin n)} (hacyc : G.IsAcyclic)
    {u v w : Fin n} (huv : G.Adj u v) (huw : G.Adj u w) (hne : w ≠ v)
    (r : G.Walk v w) (hr : r.IsPath) (hu : u ∉ r.support) : False := by
  cases r with
  | nil => exact hne rfl
  | @cons _ z _ hvz r2 =>
    have hwalk : (SimpleGraph.Walk.cons huv (SimpleGraph.Walk.cons hvz r2)).IsPath :=
      (SimpleGraph.Walk.cons_isPath_iff huv _).2 ⟨hr, hu⟩
    have hcyc : (SimpleGraph.Walk.cons (adj_symm G huw)
        (SimpleGraph.Walk.cons huv (SimpleGraph.Walk.cons hvz r2))).IsCycle := by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      refine ⟨hwalk, ?_⟩
      intro he
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with he1 | hmem_e
      · rw [Sym2.eq_iff] at he1
        rcases he1 with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact absurd h1 (G.ne_of_adj huw).symm
        · exact hne h1
      · exact hu (SimpleGraph.Walk.snd_mem_support_of_mem_edges _ hmem_e)
    exact hacyc _ hcyc

private lemma max_path_start_leaf {n : ℕ} {G : SimpleGraph (Fin n)} (hacyc : G.IsAcyclic)
    {u v b : Fin n} (huv : G.Adj u v) (q' : G.Walk v b)
    (hp : (SimpleGraph.Walk.cons huv q').IsPath)
    (hmax : ∀ (a c : Fin n) (r : G.Walk a c), r.IsPath → r.length ≤ (SimpleGraph.Walk.cons huv q').length) :
    ∀ w : Fin n, G.Adj u w → w = v := by
  intro w huw
  by_cases hmem : w ∈ (SimpleGraph.Walk.cons huv q').support
  · rcases List.mem_cons.1 hmem with rfl | hmem'
    · exact absurd huw (adj_irrefl G _)
    · by_contra hne
      have hr1_path : (q'.takeUntil w hmem').IsPath :=
        (SimpleGraph.Walk.IsPath.of_cons hp).takeUntil hmem'
      have hu_not_q' : u ∉ q'.support := (SimpleGraph.Walk.cons_isPath_iff huv q').1 hp |>.2
      have hu_not_r1 : u ∉ (q'.takeUntil w hmem').support := fun h =>
        hu_not_q' (SimpleGraph.Walk.support_takeUntil_subset q' hmem' h)
      exact cycle_of_path_adj hacyc huv huw hne (q'.takeUntil w hmem') hr1_path hu_not_r1
  · have hlonger : (SimpleGraph.Walk.cons (adj_symm G huw) (SimpleGraph.Walk.cons huv q')).IsPath :=
      (SimpleGraph.Walk.cons_isPath_iff _ _).2 ⟨hp, hmem⟩
    have hle := hmax w b _ hlonger
    simp only [SimpleGraph.Walk.length_cons] at hle
    omega

private lemma exists_penultimate {n : ℕ} (G : SimpleGraph (Fin n)) (hacyc : G.IsAcyclic)
    (hedge : ∃ u v : Fin n, G.Adj u v) :
    ∃ u v : Fin n, G.Adj u v ∧ (∀ w : Fin n, G.Adj u w → w = v) ∧
      ((∃ u2 : Fin n, u2 ≠ u ∧ G.Adj v u2 ∧ ∀ w : Fin n, G.Adj u2 w → w = v) ∨
       (∀ w₁ w₂ : Fin n, G.Adj v w₁ → G.Adj v w₂ → w₁ ≠ u → w₂ ≠ u → w₁ = w₂)) := by
  classical
  let P : ℕ → Prop := fun L => ∃ (a b : Fin n) (p : G.Walk a b), p.IsPath ∧ p.length = L
  have hP1 : P 1 := by
    obtain ⟨u, v, huv⟩ := hedge
    exact ⟨u, v, SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil,
      SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [G.ne_of_adj huv]), rfl⟩
  let S : Finset ℕ := (Finset.range (n + 1)).filter P
  have hSne : S.Nonempty := ⟨1, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by
    obtain ⟨u, v, huv⟩ := hedge
    have := u.isLt; omega), hP1⟩⟩
  let L := S.max' hSne
  have hPL : P L := (Finset.mem_filter.1 (Finset.max'_mem S hSne)).2
  have hLge1 : 1 ≤ L := Finset.le_max' S 1 (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by
    obtain ⟨u, v, huv⟩ := hedge
    have := u.isLt; omega), hP1⟩)
  have hmax : ∀ (a b : Fin n) (r : G.Walk a b), r.IsPath → r.length ≤ L := by
    intro a b r hr
    have hlt := isPath_length_lt r hr
    exact Finset.le_max' S r.length (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega),
      ⟨a, b, r, hr, rfl⟩⟩)
  obtain ⟨u, b, q, hq, hqlen⟩ := hPL
  cases q with
  | nil => simp at hqlen; omega
  | @cons _ v _ huv q' =>
    have huleaf : ∀ w : Fin n, G.Adj u w → w = v :=
      max_path_start_leaf hacyc huv q' hq (fun a c r hr => hqlen ▸ hmax a c r hr)
    refine ⟨u, v, huv, huleaf, ?_⟩
    cases q' with
    | nil =>
      right
      intro w1 _ hvw1 _ hne1 _
      exfalso
      have hnot : w1 ∉ (SimpleGraph.Walk.cons (adj_symm G huv) SimpleGraph.Walk.nil).support := by
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false, not_or]
        exact ⟨(G.ne_of_adj hvw1).symm, hne1⟩
      have hp2 : (SimpleGraph.Walk.cons (adj_symm G hvw1)
          (SimpleGraph.Walk.cons (adj_symm G huv) SimpleGraph.Walk.nil)).IsPath :=
        (SimpleGraph.Walk.cons_isPath_iff _ _).2
          ⟨SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [(G.ne_of_adj huv).symm]), hnot⟩
      have hle := hmax w1 u _ hp2
      simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hle hqlen
      omega
    | @cons _ p _ hvp q'' =>
      by_cases hex : ∃ w : Fin n, G.Adj v w ∧ w ≠ u ∧ w ≠ p
      · left
        obtain ⟨w, hvw, hwu, hwp⟩ := hex
        refine ⟨w, hwu, hvw, ?_⟩
        have hq'path : (SimpleGraph.Walk.cons hvp q'').IsPath := SimpleGraph.Walk.IsPath.of_cons hq
        have hw_not_q' : w ∉ (SimpleGraph.Walk.cons hvp q'').support := by
          intro hmem
          rcases List.mem_cons.1 hmem with rfl | hmem''
          · exact adj_irrefl G _ hvw
          · have hr1_path : (q''.takeUntil w hmem'').IsPath :=
              (SimpleGraph.Walk.IsPath.of_cons hq'path).takeUntil hmem''
            have hv_not_q'' : v ∉ q''.support :=
              (SimpleGraph.Walk.cons_isPath_iff hvp q'').1 hq'path |>.2
            have hv_not_r1 : v ∉ (q''.takeUntil w hmem'').support := fun h =>
              hv_not_q'' (SimpleGraph.Walk.support_takeUntil_subset q'' hmem'' h)
            exact cycle_of_path_adj hacyc hvp hvw hwp (q''.takeUntil w hmem'') hr1_path hv_not_r1
        have hqw_path : (SimpleGraph.Walk.cons (adj_symm G hvw) (SimpleGraph.Walk.cons hvp q'')).IsPath :=
          (SimpleGraph.Walk.cons_isPath_iff _ _).2 ⟨hq'path, hw_not_q'⟩
        exact max_path_start_leaf hacyc (adj_symm G hvw) (SimpleGraph.Walk.cons hvp q'') hqw_path
          (fun a c r hr => by
            have := hmax a c r hr
            simp only [SimpleGraph.Walk.length_cons] at hqlen ⊢
            omega)
      · right
        push Not at hex
        intro w1 w2 hvw1 hvw2 hne1 hne2
        exact (hex w1 hvw1 hne1).trans (hex w2 hvw2 hne2).symm

private lemma isAcyclic_mono {n : ℕ} {G G' : SimpleGraph (Fin n)} (hacyc : G.IsAcyclic)
    (hle : ∀ a b : Fin n, G'.Adj a b → G.Adj a b) : G'.IsAcyclic := by
  intro v c hc
  exact hacyc (SimpleGraph.Walk.mapLe hle c) (SimpleGraph.Walk.IsCycle.mapLe hle hc)

private def delEdge {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) : SimpleGraph (Fin n) where
  Adj x y := G.Adj x y ∧ ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
  symm := ⟨fun _ _ ⟨h1, h2⟩ => ⟨adj_symm G h1, fun h => h2 (by tauto)⟩⟩
  loopless := ⟨fun x ⟨h1, _⟩ => adj_irrefl G x h1⟩

private def delVert {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : SimpleGraph (Fin n) where
  Adj x y := G.Adj x y ∧ x ≠ v ∧ y ≠ v
  symm := ⟨fun _ _ ⟨h1, h2, h3⟩ => ⟨adj_symm G h1, h3, h2⟩⟩
  loopless := ⟨fun x ⟨h1, _⟩ => adj_irrefl G x h1⟩

private lemma card_edgeFinset_delEdge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (huv : G.Adj u v) [DecidableRel (delEdge G u v).Adj] :
    (delEdge G u v).edgeFinset.card + 1 = G.edgeFinset.card := by
  have heq : (delEdge G u v).edgeFinset = G.edgeFinset.erase s(u, v) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, Finset.mem_erase, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
      simp only [delEdge, ne_eq, Sym2.eq_iff]
      tauto
  have hmem : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.2 (G.mem_edgeSet.2 huv)
  rw [heq, Finset.card_erase_of_mem hmem]
  have hpos : 0 < G.edgeFinset.card := Finset.card_pos.2 ⟨s(u, v), hmem⟩
  omega

private lemma card_edgeFinset_delVert_deg1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (huv : G.Adj u v) (huniq : ∀ w : Fin n, G.Adj v w → w = u)
    [DecidableRel (delVert G v).Adj] :
    (delVert G v).edgeFinset.card + 1 = G.edgeFinset.card := by
  have heq : (delVert G v).edgeFinset = G.edgeFinset.erase s(u, v) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, Finset.mem_erase, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
      simp only [delVert, ne_eq, Sym2.eq_iff]
      constructor
      · rintro ⟨hadj, hav, hbv⟩
        refine ⟨?_, hadj⟩
        rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hbv rfl
        · exact hav rfl
      · rintro ⟨hne, hadj⟩
        refine ⟨hadj, ?_, ?_⟩
        · rintro rfl; exact hne (Or.inr ⟨rfl, huniq b hadj⟩)
        · rintro rfl; exact hne (Or.inl ⟨huniq a (adj_symm G hadj), rfl⟩)
  have hmem : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.2 (G.mem_edgeSet.2 huv)
  rw [heq, Finset.card_erase_of_mem hmem]
  have hpos : 0 < G.edgeFinset.card := Finset.card_pos.2 ⟨s(u, v), hmem⟩
  omega

private lemma card_edgeFinset_delVert_deg2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v p : Fin n) (huv : G.Adj u v) (hvp : G.Adj v p) (hup : p ≠ u)
    (huniq : ∀ w : Fin n, G.Adj v w → w = u ∨ w = p)
    [DecidableRel (delVert G v).Adj] :
    (delVert G v).edgeFinset.card + 2 = G.edgeFinset.card := by
  have heq : (delVert G v).edgeFinset = (G.edgeFinset.erase s(u, v)).erase s(v, p) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, Finset.mem_erase, Finset.mem_erase, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
      simp only [delVert, ne_eq, Sym2.eq_iff]
      constructor
      · rintro ⟨hadj, hav, hbv⟩
        refine ⟨?_, ?_, hadj⟩
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact hav rfl
          · exact hbv rfl
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact hbv rfl
          · exact hav rfl
      · rintro ⟨hne1, hne2, hadj⟩
        refine ⟨hadj, ?_, ?_⟩
        · rintro rfl
          rcases huniq b hadj with rfl | rfl
          · exact hne2 (Or.inr ⟨rfl, rfl⟩)
          · exact hne1 (Or.inl ⟨rfl, rfl⟩)
        · rintro rfl
          rcases huniq a (adj_symm G hadj) with rfl | rfl
          · exact hne2 (Or.inl ⟨rfl, rfl⟩)
          · exact hne1 (Or.inr ⟨rfl, rfl⟩)
  have hmem1 : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.2 (G.mem_edgeSet.2 huv)
  have hne_e : s(v, p) ≠ s(u, v) := by
    intro h
    rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact (G.ne_of_adj huv) h1.symm
    · exact hup h2
  have hmem2 : s(v, p) ∈ G.edgeFinset.erase s(u, v) :=
    Finset.mem_erase.2 ⟨hne_e, SimpleGraph.mem_edgeFinset.2 (G.mem_edgeSet.2 hvp)⟩
  have hc2 := Finset.card_erase_of_mem hmem2
  have hc1 := Finset.card_erase_of_mem hmem1
  have hpos1 : 0 < (G.edgeFinset.erase s(u, v)).card := Finset.card_pos.2 ⟨s(v, p), hmem2⟩
  have hpos0 : 0 < G.edgeFinset.card := Finset.card_pos.2 ⟨s(u, v), hmem1⟩
  rw [heq, hc2, hc1]
  omega

private lemma exists_min_cover {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ t : ℕ, (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = t) ∧
      (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card) := by
  classical
  let covs : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun S => ∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S)
  have hne : covs.Nonempty := ⟨Finset.univ, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun u _ _ => Or.inl (Finset.mem_univ u)⟩⟩
  obtain ⟨S0, hS0, hmin⟩ := Finset.exists_min_image covs Finset.card hne
  refine ⟨S0.card, ⟨S0, (Finset.mem_filter.1 hS0).2, rfl⟩, ?_⟩
  intro S hS
  exact hmin S (Finset.mem_filter.2 ⟨Finset.mem_univ _, hS⟩)

private def targetFun (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool) (x : Fin (n + k) → Bool) : Bool :=
  decide ((∃ a ∈ A, x (Fin.castAdd k a) = true) ∨
    ∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) ||
  g (fun j : Fin k => x (Fin.natAdd n j))

private lemma targetFun_nonconst (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    (hgnonconst : ∃ y y' : Fin k → Bool, g y ≠ g y') :
    ∃ x x' : Fin (n + k) → Bool, targetFun n k G A g x ≠ targetFun n k G A g x' := by
  obtain ⟨y, y', hne⟩ := hgnonconst
  let mk : (Fin k → Bool) → (Fin (n + k) → Bool) := fun z i =>
    if h : i.val < n then false else z ⟨i.val - n, by omega⟩
  have hmk : ∀ z, targetFun n k G A g (mk z) = g z := by
    intro z
    have h1 : ∀ a : Fin n, mk z (Fin.castAdd k a) = false := by
      intro a; simp [mk, a.isLt]
    have h2 : (fun j : Fin k => mk z (Fin.natAdd n j)) = z := by
      funext j
      have hge : ¬ (Fin.natAdd n j).val < n := by simp
      simp [mk, hge]
    unfold targetFun
    simp [h1, h2]
  exact ⟨mk y, mk y', by rw [hmk, hmk]; exact hne⟩

private lemma exists_g_false {k : ℕ} (g : (Fin k → Bool) → Bool)
    (hgnonconst : ∃ y y' : Fin k → Bool, g y ≠ g y') :
    ∃ y0 : Fin k → Bool, g y0 = false := by
  obtain ⟨y, y', hne⟩ := hgnonconst
  cases hy : g y
  · exact ⟨y, hy⟩
  · cases hy' : g y'
    · exact ⟨y', hy'⟩
    · exact absurd (hy.trans hy'.symm) hne

private lemma lower_bound_ind (n k c : ℕ) (g : (Fin k → Bool) → Bool)
    (hgnonconst : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (hgsize : ∀ r : ℕ, HasCircuitSize k g r ↔ c ≤ r) :
    ∀ M : ℕ, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (t s : ℕ),
      A.card + 2 * G.edgeFinset.card ≤ M →
      G.IsAcyclic →
      (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) →
      (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = t) →
      (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card) →
      HasCircuitSize (n + k) (targetFun n k G A g) s →
      A.card + G.edgeFinset.card + t + c ≤ s := by
  intro M
  induction M with
  | zero =>
    intro G _ A t s hM _ _ hcov_ex hcov_min hcs
    have hA0 : A = ∅ := Finset.card_eq_zero.1 (by omega)
    have hE0 : G.edgeFinset = ∅ := Finset.card_eq_zero.1 (by omega)
    have hGno : ∀ u v : Fin n, ¬ G.Adj u v := by
      intro u v hadj
      have := SimpleGraph.mem_edgeFinset.2 (G.mem_edgeSet.2 hadj)
      rw [hE0] at this; simp at this
    have ht0 : t = 0 := by
      have := hcov_min ∅ (fun u v hadj => absurd hadj (hGno u v))
      simp at this; omega
    have hfun : targetFun n k G A g = fun x => g (fun j => x (Fin.natAdd n j)) := by
      funext x
      unfold targetFun
      simp [hA0, hGno]
    rw [hfun] at hcs
    have hcg := drop_prefix_size n k s g hgnonconst hcs
    have hcs_ge := (hgsize s).1 hcg
    rw [hA0, hE0, ht0]; simp; omega
  | succ M ih =>
    intro G hdecG A t s hM hacyc hisol hcov_ex hcov_min hcs
    classical
    by_cases hAne : A.Nonempty
    · obtain ⟨a, ha⟩ := hAne
      let A' := A.erase a
      have hupd : (fun x => targetFun n k G A g (Function.update x (Fin.castAdd k a) false)) =
          targetFun n k G A' g := by
        funext x
        unfold targetFun
        have hnat : ∀ j : Fin k, Function.update x (Fin.castAdd k a) false (Fin.natAdd n j) =
            x (Fin.natAdd n j) := by
          intro j
          apply Function.update_of_ne
          intro e
          have hv := congrArg Fin.val e
          simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
          have := a.isLt; omega
        have hcast : ∀ w : Fin n, Function.update x (Fin.castAdd k a) false (Fin.castAdd k w) =
            if w = a then false else x (Fin.castAdd k w) := by
          intro w
          by_cases hw : w = a
          · subst hw; simp
          · have hne : Fin.castAdd k w ≠ Fin.castAdd k a := fun e => hw (Fin.castAdd_injective n k e)
            simp [hw, Function.update_of_ne hne]
        simp only [hnat]
        congr 1
        apply Bool.eq_iff_iff.2
        simp only [decide_eq_true_eq, hcast, A', Finset.mem_erase]
        constructor
        · rintro (⟨w, hwA, hxw⟩ | ⟨u, v, huv, hxu, hxv⟩)
          · by_cases hwa : w = a
            · simp [hwa] at hxw
            · left; exact ⟨w, ⟨hwa, hwA⟩, by simpa [hwa] using hxw⟩
          · have hua : u ≠ a := fun e => hisol a ha v (e ▸ huv)
            have hva : v ≠ a := fun e => hisol a ha u (adj_symm G (e ▸ huv))
            right; exact ⟨u, v, huv, by simpa [hua] using hxu, by simpa [hva] using hxv⟩
        · rintro (⟨w, ⟨hwa, hwA⟩, hxw⟩ | ⟨u, v, huv, hxu, hxv⟩)
          · left; exact ⟨w, hwA, by simpa [hwa] using hxw⟩
          · have hua : u ≠ a := fun e => hisol a ha v (e ▸ huv)
            have hva : v ≠ a := fun e => hisol a ha u (adj_symm G (e ▸ huv))
            right; exact ⟨u, v, huv, by simpa [hua] using hxu, by simpa [hva] using hxv⟩
      have hdep : ∃ x : Fin (n + k) → Bool,
          targetFun n k G A g (Function.update x (Fin.castAdd k a) false) ≠
          targetFun n k G A g (Function.update x (Fin.castAdd k a) true) := by
        obtain ⟨y0, hy0⟩ := exists_g_false g hgnonconst
        let x : Fin (n + k) → Bool := fun i =>
          if h : i.val < n then false else y0 ⟨i.val - n, by omega⟩
        refine ⟨x, ?_⟩
        have h0 : targetFun n k G A g (Function.update x (Fin.castAdd k a) false) = false := by
          unfold targetFun
          have h1 : ∀ w : Fin n, Function.update x (Fin.castAdd k a) false (Fin.castAdd k w) = false := by
            intro w
            by_cases hw : w = a
            · subst hw; simp
            · rw [Function.update_of_ne (fun e => hw (Fin.castAdd_injective n k e))]
              simp [x, w.isLt]
          have h2 : (fun j : Fin k => Function.update x (Fin.castAdd k a) false (Fin.natAdd n j)) = y0 := by
            funext j
            rw [Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; have := a.isLt; omega)]
            simp [x]
          simp [h1, h2, hy0]
        have h1 : targetFun n k G A g (Function.update x (Fin.castAdd k a) true) = true := by
          unfold targetFun
          have htrue : (∃ w ∈ A, Function.update x (Fin.castAdd k a) true (Fin.castAdd k w) = true) :=
            ⟨a, ha, by simp⟩
          simp [htrue]
        rw [h0, h1]; decide
      have hnc : ∃ x x',
          targetFun n k G A g (Function.update x (Fin.castAdd k a) false) ≠
          targetFun n k G A g (Function.update x' (Fin.castAdd k a) false) := by
        obtain ⟨x, x', hne⟩ := targetFun_nonconst n k G A' g hgnonconst
        exact ⟨x, x', by rw [congrFun hupd x, congrFun hupd x']; exact hne⟩
      obtain ⟨hs1, hcs'⟩ := gate_elim_one (n + k) (targetFun n k G A g) (Fin.castAdd k a) false s hdep hnc hcs
      rw [hupd] at hcs'
      have hA'card : A'.card + 1 = A.card := by
        have h1 := Finset.card_erase_of_mem ha
        have hpos : 0 < A.card := Finset.card_pos.2 ⟨a, ha⟩
        change (A.erase a).card + 1 = A.card
        omega
      have hih := @ih G hdecG A' t (s - 1) (by omega) hacyc
        (fun b hb => hisol b (Finset.mem_of_mem_erase hb)) hcov_ex hcov_min hcs'
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hAne
      subst hAne
      by_cases hedge : ∃ u v : Fin n, G.Adj u v
      · obtain ⟨u, v, huv, huleaf, hbranch⟩ := exists_penultimate G hacyc hedge
        have hdep_u : ∃ x : Fin (n + k) → Bool,
            targetFun n k G ∅ g (Function.update x (Fin.castAdd k u) false) ≠
            targetFun n k G ∅ g (Function.update x (Fin.castAdd k u) true) := by
          obtain ⟨y0, hy0⟩ := exists_g_false g hgnonconst
          let x : Fin (n + k) → Bool := fun i =>
            if h : i.val < n then decide (i.val = v.val) else y0 ⟨i.val - n, by omega⟩
          refine ⟨x, ?_⟩
          have h0 : targetFun n k G ∅ g (Function.update x (Fin.castAdd k u) false) = false := by
            unfold targetFun
            have h2 : (fun j : Fin k => Function.update x (Fin.castAdd k u) false (Fin.natAdd n j)) = y0 := by
              funext j
              rw [Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; have := u.isLt; omega)]
              simp [x]
            have hno : ¬ ∃ a b : Fin n, G.Adj a b ∧
                Function.update x (Fin.castAdd k u) false (Fin.castAdd k a) = true ∧
                Function.update x (Fin.castAdd k u) false (Fin.castAdd k b) = true := by
              rintro ⟨a, b, hab, hxa, hxb⟩
              have hav : a = v := by
                by_cases hau : a = u
                · subst hau; simp at hxa
                · rw [Function.update_of_ne (fun e => hau (Fin.castAdd_injective n k e))] at hxa
                  simp [x, a.isLt] at hxa
                  exact Fin.ext hxa
              have hbv : b = v := by
                by_cases hbu : b = u
                · subst hbu; simp at hxb
                · rw [Function.update_of_ne (fun e => hbu (Fin.castAdd_injective n k e))] at hxb
                  simp [x, b.isLt] at hxb
                  exact Fin.ext hxb
              subst hav; subst hbv
              exact adj_irrefl G _ hab
            simp [h2, hy0, hno]
          have h1 : targetFun n k G ∅ g (Function.update x (Fin.castAdd k u) true) = true := by
            unfold targetFun
            have hxv : Function.update x (Fin.castAdd k u) true (Fin.castAdd k v) = true := by
              rw [Function.update_of_ne (fun e => (G.ne_of_adj huv).symm (Fin.castAdd_injective n k e))]
              simp [x, v.isLt]
            have hex : ∃ a b : Fin n, G.Adj a b ∧
                Function.update x (Fin.castAdd k u) true (Fin.castAdd k a) = true ∧
                Function.update x (Fin.castAdd k u) true (Fin.castAdd k b) = true :=
              ⟨u, v, huv, by simp, hxv⟩
            simp [hex]
          rw [h0, h1]; decide
        let GdelE := delEdge G u v
        have hupd_false : (fun x => targetFun n k G ∅ g (Function.update x (Fin.castAdd k u) false)) =
            targetFun n k GdelE ∅ g := by
          funext x
          unfold targetFun
          have hnat : ∀ j : Fin k, Function.update x (Fin.castAdd k u) false (Fin.natAdd n j) =
              x (Fin.natAdd n j) := by
            intro j; apply Function.update_of_ne
            intro e; have := congrArg Fin.val e; simp at this; have := u.isLt; omega
          simp only [hnat]
          congr 1
          apply Bool.eq_iff_iff.2
          simp only [decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false, false_or]
          constructor
          · rintro ⟨a, b, hab, hxa, hxb⟩
            have hau : a ≠ u := by rintro rfl; simp at hxa
            have hbu : b ≠ u := by rintro rfl; simp at hxb
            rw [Function.update_of_ne (fun e => hau (Fin.castAdd_injective n k e))] at hxa
            rw [Function.update_of_ne (fun e => hbu (Fin.castAdd_injective n k e))] at hxb
            refine ⟨a, b, ⟨hab, ?_⟩, hxa, hxb⟩
            rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
            · exact hau rfl
            · exact hbu rfl
          · rintro ⟨a, b, ⟨hab, hne⟩, hxa, hxb⟩
            have hau : a ≠ u := by
              rintro rfl
              exact hne (Or.inl ⟨rfl, huleaf b hab⟩)
            have hbu : b ≠ u := by
              rintro rfl
              exact hne (Or.inr ⟨huleaf a (adj_symm G hab), rfl⟩)
            refine ⟨a, b, hab, ?_, ?_⟩
            · rw [Function.update_of_ne (fun e => hau (Fin.castAdd_injective n k e))]; exact hxa
            · rw [Function.update_of_ne (fun e => hbu (Fin.castAdd_injective n k e))]; exact hxb
        let GdelV := delVert G v
        have hupd_true : (fun x => targetFun n k G ∅ g (Function.update x (Fin.castAdd k u) true)) =
            targetFun n k GdelV {v} g := by
          funext x
          unfold targetFun
          have hnat : ∀ j : Fin k, Function.update x (Fin.castAdd k u) true (Fin.natAdd n j) =
              x (Fin.natAdd n j) := by
            intro j; apply Function.update_of_ne
            intro e; have := congrArg Fin.val e; simp at this; have := u.isLt; omega
          simp only [hnat]
          congr 1
          apply Bool.eq_iff_iff.2
          simp only [decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false, false_or,
            Finset.mem_singleton, exists_eq_left]
          constructor
          · rintro ⟨a, b, hab, hxa, hxb⟩
            by_cases hav : a = v
            · subst hav
              left
              rw [Function.update_of_ne (fun e => (G.ne_of_adj huv).symm (Fin.castAdd_injective n k e))] at hxa
              exact hxa
            · by_cases hbv : b = v
              · subst hbv
                left
                rw [Function.update_of_ne (fun e => (G.ne_of_adj huv).symm (Fin.castAdd_injective n k e))] at hxb
                exact hxb
              · have hau : a ≠ u := fun e => hbv (huleaf b (e ▸ hab))
                have hbu : b ≠ u := fun e => hav (huleaf a (adj_symm G (e ▸ hab)))
                rw [Function.update_of_ne (fun e => hau (Fin.castAdd_injective n k e))] at hxa
                rw [Function.update_of_ne (fun e => hbu (Fin.castAdd_injective n k e))] at hxb
                right; exact ⟨a, b, ⟨hab, hav, hbv⟩, hxa, hxb⟩
          · rintro (hxv | ⟨a, b, ⟨hab, hav, hbv⟩, hxa, hxb⟩)
            · refine ⟨u, v, huv, by simp, ?_⟩
              rw [Function.update_of_ne (fun e => (G.ne_of_adj huv).symm (Fin.castAdd_injective n k e))]
              exact hxv
            · have hau : a ≠ u := fun e => hbv (huleaf b (e ▸ hab))
              have hbu : b ≠ u := fun e => hav (huleaf a (adj_symm G (e ▸ hab)))
              refine ⟨a, b, hab, ?_, ?_⟩
              · rw [Function.update_of_ne (fun e => hau (Fin.castAdd_injective n k e))]; exact hxa
              · rw [Function.update_of_ne (fun e => hbu (Fin.castAdd_injective n k e))]; exact hxb
        have hdelV_cov : ∃ tV : ℕ, tV + 1 = t ∧
            (∃ S : Finset (Fin n), (∀ a b : Fin n, GdelV.Adj a b → a ∈ S ∨ b ∈ S) ∧ S.card = tV) ∧
            (∀ S : Finset (Fin n), (∀ a b : Fin n, GdelV.Adj a b → a ∈ S ∨ b ∈ S) → tV ≤ S.card) := by
          obtain ⟨tV, hVex, hVmin⟩ := exists_min_cover GdelV
          have hle1 : t ≤ tV + 1 := by
            obtain ⟨S', hS'cov, hS'card⟩ := hVex
            have hcovG : ∀ a b : Fin n, G.Adj a b → a ∈ insert v S' ∨ b ∈ insert v S' := by
              intro a b hab
              by_cases hav : a = v
              · subst hav; exact Or.inl (Finset.mem_insert_self _ _)
              · by_cases hbv : b = v
                · subst hbv; exact Or.inr (Finset.mem_insert_self _ _)
                · rcases hS'cov a b ⟨hab, hav, hbv⟩ with ha | hb
                  · exact Or.inl (Finset.mem_insert_of_mem ha)
                  · exact Or.inr (Finset.mem_insert_of_mem hb)
            have := hcov_min (insert v S') hcovG
            have hc := Finset.card_insert_le v S'
            omega
          have hge1 : tV + 1 ≤ t := by
            obtain ⟨S, hScov, hScard⟩ := hcov_ex
            rcases hScov u v huv with huS | hvS
            · have hcov' : ∀ a b : Fin n, GdelV.Adj a b → a ∈ S.erase u ∨ b ∈ S.erase u := by
                intro a b ⟨hab, hav, hbv⟩
                have hau : a ≠ u := fun e => hbv (huleaf b (e ▸ hab))
                have hbu : b ≠ u := fun e => hav (huleaf a (adj_symm G (e ▸ hab)))
                rcases hScov a b hab with ha | hb
                · exact Or.inl (Finset.mem_erase.2 ⟨hau, ha⟩)
                · exact Or.inr (Finset.mem_erase.2 ⟨hbu, hb⟩)
              have h1 := hVmin (S.erase u) hcov'
              have h2 := Finset.card_erase_of_mem huS
              have hpos : 0 < S.card := Finset.card_pos.2 ⟨u, huS⟩
              omega
            · have hcov' : ∀ a b : Fin n, GdelV.Adj a b → a ∈ S.erase v ∨ b ∈ S.erase v := by
                intro a b ⟨hab, hav, hbv⟩
                rcases hScov a b hab with ha | hb
                · exact Or.inl (Finset.mem_erase.2 ⟨hav, ha⟩)
                · exact Or.inr (Finset.mem_erase.2 ⟨hbv, hb⟩)
              have h1 := hVmin (S.erase v) hcov'
              have h2 := Finset.card_erase_of_mem hvS
              have hpos : 0 < S.card := Finset.card_pos.2 ⟨v, hvS⟩
              omega
          exact ⟨tV, by omega, hVex, hVmin⟩
        have hEcard_delE : GdelE.edgeFinset.card + 1 = (@SimpleGraph.edgeFinset _ G (SimpleGraph.fintypeEdgeSet G)).card := by
          convert @card_edgeFinset_delEdge n G hdecG u v huv _
        rcases hbranch with ⟨u2, hu2ne, hvu2, hu2leaf⟩ | hdegle2
        · have hnc0 : ∃ x x',
              targetFun n k G ∅ g (Function.update x (Fin.castAdd k u) false) ≠
              targetFun n k G ∅ g (Function.update x' (Fin.castAdd k u) false) := by
            obtain ⟨x, x', hne⟩ := targetFun_nonconst n k GdelE ∅ g hgnonconst
            exact ⟨x, x', by rw [congrFun hupd_false x, congrFun hupd_false x']; exact hne⟩
          obtain ⟨hs1, hcs'⟩ := gate_elim_one (n + k) (targetFun n k G ∅ g) (Fin.castAdd k u) false s hdep_u hnc0 hcs
          rw [hupd_false] at hcs'
          have hcovE_min : ∀ S : Finset (Fin n), (∀ a b : Fin n, GdelE.Adj a b → a ∈ S ∨ b ∈ S) → t ≤ S.card := by
            intro S hScov
            have hu2adj : GdelE.Adj v u2 := by
              refine ⟨hvu2, ?_⟩
              rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
              · exact (G.ne_of_adj huv) h1.symm
              · exact hu2ne h2
            rcases hScov v u2 hu2adj with hvS | hu2S
            · exact hcov_min S (fun a b hab => by
                by_cases h1 : (a = u ∧ b = v) ∨ (a = v ∧ b = u)
                · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact Or.inr hvS
                  · exact Or.inl hvS
                · exact hScov a b ⟨hab, h1⟩)
            · have hcovG : ∀ a b : Fin n, G.Adj a b → a ∈ insert v (S.erase u2) ∨ b ∈ insert v (S.erase u2) := by
                intro a b hab
                by_cases hav : a = v
                · subst hav; exact Or.inl (Finset.mem_insert_self _ _)
                · by_cases hbv : b = v
                  · subst hbv; exact Or.inr (Finset.mem_insert_self _ _)
                  · have hau2 : a ≠ u2 := fun e => hbv (hu2leaf b (e ▸ hab))
                    have hbu2 : b ≠ u2 := fun e => hav (hu2leaf a (adj_symm G (e ▸ hab)))
                    have hnotuv : ¬ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) := by
                      rintro (⟨_, rfl⟩ | ⟨rfl, _⟩) <;> contradiction
                    rcases hScov a b ⟨hab, hnotuv⟩ with ha | hb
                    · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hau2, ha⟩))
                    · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hbu2, hb⟩))
              have h1 := hcov_min (insert v (S.erase u2)) hcovG
              have h2 := Finset.card_insert_le v (S.erase u2)
              have h3 := Finset.card_erase_of_mem hu2S
              have hpos : 0 < S.card := Finset.card_pos.2 ⟨u2, hu2S⟩
              omega
          have hcovE_ex : ∃ S : Finset (Fin n), (∀ a b : Fin n, GdelE.Adj a b → a ∈ S ∨ b ∈ S) ∧ S.card = t := by
            obtain ⟨S, hScov, hScard⟩ := hcov_ex
            exact ⟨S, fun a b ⟨hab, _⟩ => hScov a b hab, hScard⟩
          have hEeq : GdelE.edgeFinset.card + 1 = G.edgeFinset.card := by
            convert hEcard_delE
          have hih := ih GdelE ∅ t (s - 1) (by simp only [Finset.card_empty, zero_add] at hM ⊢; omega)
            (isAcyclic_mono hacyc (fun _ _ h => h.1)) (by simp) hcovE_ex hcovE_min hcs'
          simp only [Finset.card_empty, zero_add] at hih ⊢
          omega
        · by_cases hexp : ∃ p : Fin n, G.Adj v p ∧ p ≠ u
          · obtain ⟨p, hvp, hpu⟩ := hexp
            have huniq : ∀ w : Fin n, G.Adj v w → w = u ∨ w = p := by
              intro w hvw
              by_cases hwu : w = u
              · exact Or.inl hwu
              · exact Or.inr (hdegle2 w p hvw hvp hwu hpu)
            have hnc0 : ∃ x x',
                targetFun n k G ∅ g (Function.update x (Fin.castAdd k u) false) ≠
                targetFun n k G ∅ g (Function.update x' (Fin.castAdd k u) false) := by
              obtain ⟨x, x', hne⟩ := targetFun_nonconst n k GdelE ∅ g hgnonconst
              exact ⟨x, x', by rw [congrFun hupd_false x, congrFun hupd_false x']; exact hne⟩
            have hnc1 : ∃ x x',
                targetFun n k G ∅ g (Function.update x (Fin.castAdd k u) true) ≠
                targetFun n k G ∅ g (Function.update x' (Fin.castAdd k u) true) := by
              obtain ⟨x, x', hne⟩ := targetFun_nonconst n k GdelV {v} g hgnonconst
              exact ⟨x, x', by rw [congrFun hupd_true x, congrFun hupd_true x']; exact hne⟩
            rcases gate_elim_two (n + k) (targetFun n k G ∅ g) (Fin.castAdd k u) s hdep_u hnc0 hnc1 hcs with
              ⟨hs2, hcs0⟩ | ⟨hs2, hcs1⟩
            · rw [hupd_false] at hcs0
              have hEeq : GdelE.edgeFinset.card + 1 = G.edgeFinset.card := by
                convert hEcard_delE
              obtain ⟨tE, hEex, hEmin⟩ := exists_min_cover GdelE
              have htE_ge : t ≤ tE + 1 := by
                obtain ⟨S', hS'cov, hS'card⟩ := hEex
                have hcovG : ∀ a b : Fin n, G.Adj a b → a ∈ insert u S' ∨ b ∈ insert u S' := by
                  intro a b hab
                  by_cases h1 : (a = u ∧ b = v) ∨ (a = v ∧ b = u)
                  · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · exact Or.inl (Finset.mem_insert_self _ _)
                    · exact Or.inr (Finset.mem_insert_self _ _)
                  · rcases hS'cov a b ⟨hab, h1⟩ with ha | hb
                    · exact Or.inl (Finset.mem_insert_of_mem ha)
                    · exact Or.inr (Finset.mem_insert_of_mem hb)
                have h1 := hcov_min (insert u S') hcovG
                have h2 := Finset.card_insert_le u S'
                omega
              have hih := ih GdelE ∅ tE (s - 2) (by simp only [Finset.card_empty, zero_add] at hM ⊢; omega)
                (isAcyclic_mono hacyc (fun _ _ h => h.1)) (by simp) hEex hEmin hcs0
              simp only [Finset.card_empty, zero_add] at hih ⊢
              omega
            · rw [hupd_true] at hcs1
              have hEeq : GdelV.edgeFinset.card + 2 = G.edgeFinset.card := by
                convert @card_edgeFinset_delVert_deg2 n G hdecG u v p huv hvp hpu huniq _
              obtain ⟨tV, htV, hVex, hVmin⟩ := hdelV_cov
              have hih := ih GdelV {v} tV (s - 2) (by simp only [Finset.card_empty, Finset.card_singleton, zero_add] at hM ⊢; omega)
                (isAcyclic_mono hacyc (fun _ _ h => h.1))
                (by intro a ha w; rw [Finset.mem_singleton] at ha; subst ha; simp [GdelV, delVert])
                hVex hVmin hcs1
              simp only [Finset.card_empty, Finset.card_singleton, zero_add] at hih ⊢
              omega
          · push Not at hexp
            have hnc1 : ∃ x x',
                targetFun n k G ∅ g (Function.update x (Fin.castAdd k u) true) ≠
                targetFun n k G ∅ g (Function.update x' (Fin.castAdd k u) true) := by
              obtain ⟨x, x', hne⟩ := targetFun_nonconst n k GdelV {v} g hgnonconst
              exact ⟨x, x', by rw [congrFun hupd_true x, congrFun hupd_true x']; exact hne⟩
            obtain ⟨hs1, hcs1⟩ := gate_elim_one (n + k) (targetFun n k G ∅ g) (Fin.castAdd k u) true s hdep_u hnc1 hcs
            rw [hupd_true] at hcs1
            have hEeq : GdelV.edgeFinset.card + 1 = G.edgeFinset.card := by
              convert @card_edgeFinset_delVert_deg1 n G hdecG u v huv hexp _
            obtain ⟨tV, htV, hVex, hVmin⟩ := hdelV_cov
            have hih := ih GdelV {v} tV (s - 1) (by simp only [Finset.card_empty, Finset.card_singleton, zero_add] at hM ⊢; omega)
              (isAcyclic_mono hacyc (fun _ _ h => h.1))
              (by intro a ha w; rw [Finset.mem_singleton] at ha; subst ha; simp [GdelV, delVert])
              hVex hVmin hcs1
            simp only [Finset.card_empty, Finset.card_singleton, zero_add] at hih ⊢
            omega
      · push Not at hedge
        have hE0 : G.edgeFinset = ∅ := by
          ext e
          induction e using Sym2.ind with
          | _ a b => simp [SimpleGraph.mem_edgeFinset, hedge a b]
        have ht0 : t = 0 := by
          have := hcov_min ∅ (fun u v hadj => absurd hadj (hedge u v))
          simp at this; omega
        have hfun : targetFun n k G ∅ g = fun x => g (fun j => x (Fin.natAdd n j)) := by
          funext x
          unfold targetFun
          simp [hedge]
        rw [hfun] at hcs
        have hcg := drop_prefix_size n k s g hgnonconst hcs
        have hcs_ge := (hgsize s).1 hcg
        rw [hE0, ht0]; simp; omega

theorem main_thm :
    ∀ (n k c t s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
      (g : (Fin k → Bool) → Bool),
      G.IsAcyclic →
      (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) →
      (A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) →
      (∃ y y' : Fin k → Bool, g y ≠ g y') →
      (∀ r : ℕ, HasCircuitSize k g r ↔ c ≤ r) →
      (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = t) →
      (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card) →
      (HasCircuitSize (n + k) (fun x : Fin (n + k) → Bool =>
        decide ((∃ a ∈ A, x (Fin.castAdd k a) = true) ∨
          ∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) ||
        g (fun j : Fin k => x (Fin.natAdd n j))) s ↔
      A.card + G.edgeFinset.card + t + c ≤ s) := by
  intro n k c t s G _ A g hacyc hisol _ hgnonconst hgsize hcov_ex hcov_min
  constructor
  · intro hcs
    exact lower_bound_ind n k c g hgnonconst hgsize (A.card + 2 * G.edgeFinset.card) G A t s
      (le_refl _) hacyc hisol hcov_ex hcov_min hcs
  · exact upper_bound n k c t s G A g hgnonconst hgsize hcov_ex hcov_min

end PEqualNP.Outside.L_meta_468_aux

theorem PEqualNP.Outside.L_meta_468 : ∀ (n k c t s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool), G.IsAcyclic → (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) → (A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) → (∃ y y' : Fin k → Bool, g y ≠ g y') → (∀ r : ℕ, PEqualNP.MetaComplexity.HasCircuitSize k g r ↔ c ≤ r) → (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = t) → (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card) → (PEqualNP.MetaComplexity.HasCircuitSize (n + k) (fun x : Fin (n + k) → Bool => decide ((∃ a ∈ A, x (Fin.castAdd k a) = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) || g (fun j : Fin k => x (Fin.natAdd n j))) s ↔ A.card + G.edgeFinset.card + t + c ≤ s) :=
  PEqualNP.Outside.L_meta_468_aux.main_thm
