import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4455_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

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
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate]

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

-- Each old wire is either constant or represented by a wire in the smaller circuit.
abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
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

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    all_goals (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    all_goals (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    all_goals (subst hg; simp [Ok])
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
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

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
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
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

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

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
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj

private theorem graphFun_erase {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (haA : a ∈ A) (x : Fin n → Bool) :
    graphFun K A x = (x a || graphFun K (A.erase a) x) := by
  unfold graphFun
  by_cases hxa : x a = true
  · simp [hxa, show ∃ b ∈ A, x b = true from ⟨a, haA, hxa⟩]
  · have hxaf : x a = false := Bool.eq_false_iff.2 hxa
    have hiff : (∃ b ∈ A, x b = true) ↔ (∃ b ∈ A.erase a, x b = true) := by
      constructor
      · rintro ⟨b, hbA, hxb⟩
        have hba : b ≠ a := fun h => hxa (h ▸ hxb)
        exact ⟨b, Finset.mem_erase.2 ⟨hba, hbA⟩, hxb⟩
      · rintro ⟨b, hbe, hxb⟩
        exact ⟨b, (Finset.mem_erase.1 hbe).2, hxb⟩
    simp [hxaf, hiff]

private theorem graphFun_erase_update {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (hAdisj : ∀ b ∈ A, ∀ v : Fin n, ¬ K.Adj b v)
    (haA : a ∈ A) (x : Fin n → Bool) (val : Bool) :
    graphFun K (A.erase a) (Function.update x a val) = graphFun K (A.erase a) x := by
  unfold graphFun
  have h1 : (∃ b ∈ A.erase a, Function.update x a val b = true) ↔
      (∃ b ∈ A.erase a, x b = true) := by
    constructor <;> rintro ⟨b, hb, hxb⟩ <;> refine ⟨b, hb, ?_⟩
    · rwa [Function.update_of_ne (Finset.mem_erase.1 hb).1] at hxb
    · rwa [Function.update_of_ne (Finset.mem_erase.1 hb).1]
  have h2 : (∃ u v, K.Adj u v ∧ Function.update x a val u = true ∧ Function.update x a val v = true) ↔
      (∃ u v, K.Adj u v ∧ x u = true ∧ x v = true) := by
    constructor <;> rintro ⟨u, v, huv, hu, hv⟩
    · have hua : u ≠ a := fun h => hAdisj a haA v (h ▸ huv)
      have hva : v ≠ a := fun h => hAdisj a haA u (h ▸ huv.symm)
      rw [Function.update_of_ne hua] at hu
      rw [Function.update_of_ne hva] at hv
      exact ⟨u, v, huv, hu, hv⟩
    · have hua : u ≠ a := fun h => hAdisj a haA v (h ▸ huv)
      have hva : v ≠ a := fun h => hAdisj a haA u (h ▸ huv.symm)
      exact ⟨u, v, huv, by rwa [Function.update_of_ne hua], by rwa [Function.update_of_ne hva]⟩
  simp only [h1, h2]

private theorem graphFun_update_false {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (hAdisj : ∀ b ∈ A, ∀ v : Fin n, ¬ K.Adj b v)
    (haA : a ∈ A) (x : Fin n → Bool) :
    graphFun K A (Function.update x a false) = graphFun K (A.erase a) x := by
  rw [graphFun_erase K A a haA, Function.update_self, Bool.false_or,
    graphFun_erase_update K A a hAdisj haA]

def initial {n : ℕ} (a : Fin n) : List Stat :=
  List.ofFn fun j : Fin n => if j = a then Sum.inl false else Sum.inr j.val

theorem initial_sound {n : ℕ} (a : Fin n) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn (Function.update x a false)) (initial a, []) := by
  refine ⟨by simp [initial], ?_⟩
  intro i
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    by_cases eq : j = a
    · subst a
      simp [initial, hi, j, Stat.Valid, Stat.val]
    · simp [initial, hi, j, eq, Function.update_of_ne, Stat.Valid, Stat.val, wiresFrom] at *
  · change ((initial a).getD i (Sum.inl false)).Valid (n + 0) ∧
        ((initial a).getD i (Sum.inl false)).val (List.ofFn x) =
          (List.ofFn (Function.update x a false)).getD i false
    rw [List.getD_eq_default _ _ (by simp [initial]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

-- Setting an isolated input to false removes a gate that reads it and preserves the edge term.
theorem removeOne {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (a : Fin n) (ha : a ∈ A)
    (isolated : ∀ b ∈ A, ∀ v, ¬ G.Adj b v) (edge : ∃ u v, G.Adj u v)
    (s : ℕ) (has : HasCircuitSize n (graphFun G A) s) :
    ∃ t, t + 1 ≤ s ∧ HasCircuitSize n (graphFun G (A.erase a)) t := by
  obtain ⟨C, fan, budget, computes⟩ := has
  let gs := C.gates.map normGate
  have normOK : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, h0, rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g0 (fan _ h0)
  have value (x : Fin n → Bool) :
      (wiresFrom gs (List.ofFn x)).getD C.output false = graphFun G A x := by
    rw [show gs = C.gates.map normGate from rfl, wiresFrom_norm]
    exact computes x
  obtain ⟨u, v, uv⟩ := edge
  have on : graphFun G (A.erase a) (fun _ => true) = true := by
    simp [graphFun, show ∃ i j, G.Adj i j from ⟨u, v, uv⟩]
  have off : graphFun G (A.erase a) (fun _ => false) = false := by simp [graphFun]
  have diff : C.output ≠ a.val := by
    intro same
    have h := value (Function.update (fun _ => true) a false)
    rw [graphFun_update_false G A a isolated ha, on, same,
      getD_wiresFrom _ _ _ (by simp [a.isLt])] at h
    simp [a.isLt] at h
  have reads : ∃ g ∈ gs, a.val ∈ g.inputs := by
    by_contra none
    let x : Fin n → Bool := fun _ => false
    let y := Function.update x a true
    have agree := agree_except a.val gs (List.ofFn x) (List.ofFn y)
      (fun g hg hi => none ⟨g, hg, hi⟩) (by simp) (by
        intro i ne
        by_cases hi : i < n
        · have distinct : (⟨i, hi⟩ : Fin n) ≠ a := fun h => ne (congrArg Fin.val h)
          simp [y, hi, Function.update_of_ne distinct]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
      C.output diff
    rw [value, value, graphFun_erase G A a ha y] at agree
    simp [x, y, graphFun] at agree
  let acc := elim n gs (initial a, [])
  have simulation (x : Fin n → Bool) :
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) =
        graphFun G (A.erase a) x := by
    have h := inv_elim n (List.ofFn x) (by simp) gs _ _
      (fun g hg => (normOK g hg).1) (initial_sound a x)
    exact ((h.2 C.output).2.trans (value _)).trans (graphFun_update_false G A a isolated ha x)
  have lengthBound : acc.2.length + 1 ≤ s := by
    have h := elim_len_lt n a.val gs (initial a, []) normOK (by simp [initial, a.isLt])
      ⟨false, by simp [initial, a.isLt]⟩ reads
    have h' : acc.2.length + 1 ≤ C.size := by simpa [acc, gs, Circuit.size] using h
    exact h'.trans budget
  cases hz : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    have e₀ := simulation (fun _ => false)
    have e₁ := simulation (fun _ => true)
    rw [hz, off] at e₀
    rw [hz, on] at e₁
    exact Bool.false_ne_true (e₀.symm.trans e₁) |>.elim
  | inr out =>
    refine ⟨acc.2.length, lengthBound, ⟨acc.2, out⟩, elim_ok n gs _ (by simp), le_rfl, ?_⟩
    intro x
    have h := simulation x
    rw [hz] at h
    exact h

theorem strip {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (edge : ∃ u v, G.Adj u v) (A : Finset (Fin n)) :
    (∀ a ∈ A, ∀ b, ¬ G.Adj a b) → ∀ s, HasCircuitSize n (graphFun G A) s →
      ∃ t, t + A.card ≤ s ∧ HasCircuitSize n (graphFun G ∅) t := by
  induction A using Finset.induction_on with
  | empty =>
    intro _ s hs
    exact ⟨s, by simp, hs⟩
  | @insert a A ha ih =>
    intro isolated s hs
    obtain ⟨t, saved, smaller⟩ :=
      removeOne G (insert a A) a (Finset.mem_insert_self a A) isolated edge s hs
    rw [Finset.erase_insert ha] at smaller
    obtain ⟨k, bound, h⟩ := ih (fun b hb => isolated b (Finset.mem_insert_of_mem hb)) t smaller
    exact ⟨k, by rw [Finset.card_insert_of_notMem ha]; omega, h⟩

end PEqualNP.Outside.L_meta_4455_aux

theorem PEqualNP.Outside.L_meta_4455 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ (x5 x6 : Fin x1), x2.Adj x5 x6 → x5 ∉ x4) → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → ∀ (x7 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4) x7 → ∃ (x9 : ℕ), x9 + x4.card ≤ x7 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x9 := by
  intro n G inst A isolated edge
  apply PEqualNP.Outside.L_meta_4455_aux.strip G edge A
  exact fun a ha b hab => isolated a b hab ha
