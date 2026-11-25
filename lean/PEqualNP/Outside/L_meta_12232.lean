import PEqualNP.Defs

-- The engine (sections 1 and 2) is that of L-meta-9148 by stasana666, after L-meta-927, Apache-2.0; only the
-- lookup depth of idxGen is raised from 12 to 14. The bank of states below was computed by our own search.
namespace PEqualNP.Outside.L_meta_12232

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

/-! ## Section 1: Self-contained circuit simplification, relabeling, and gate elimination -/

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

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
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
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      statVal (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y))
        ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
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

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨s', hs, h'⟩ := gate_elim_one n _ b s hdep' hnc' hg
  refine ⟨s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

/-! ## Section 2: Self-contained Run, Reach, NatRun, and barrier checker -/

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem split_at {α : Type} (gs : List α) (p : ℕ) (g : α) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hget : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp; omega⟩
  have h1 : gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
  have h2 : gs.drop p = gs[p] :: gs.drop (p + 1) := List.drop_eq_getElem_cons hlt
  exact h1.trans (by rw [h2, hget])

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

def initId (n : ℕ) : List Stat := List.ofFn fun i : Fin n => Sum.inr (i : ℕ)

theorem inv_initId (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initId n, []) := by
  refine ⟨by simp [initId], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [initId, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initId]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem exists_clean (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) :
    ∃ gs o, CleanL n gs ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set acc := elim n C.gates (initId n, []) with hacc
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ ok (inv_initId n y)
  have hcl : CleanL n acc.2 := by
    apply elim_clean n C.gates (initId n, []) ok
    · intro i
      by_cases hlt : i < n
      · simp [initId, hlt, statValid]
      · rw [List.getD_eq_default _ _ (by simp [initId]; omega)]; trivial
    · intro p g hp; simp at hp
  have hlen : acc.2.length ≤ s := by
    have := elim_len n C.gates (initId n, [])
    rw [← hacc] at this
    simp only [List.length_nil, zero_add] at this
    omega
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 C.output).2
    have e2 := ((hinv y').2 C.output).2
    rw [hst] at e1 e2
    have h1 : (wiresFrom C.gates (List.ofFn y)).getD C.output false = f y := hev y
    have h2 : (wiresFrom C.gates (List.ofFn y')).getD C.output false = f y' := hev y'
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr j =>
    have hj : j < n + acc.2.length := by
      obtain ⟨y, _, _⟩ := hnc
      have := ((hinv y).2 C.output).1
      rw [hst] at this
      exact this
    refine ⟨acc.2, j, hcl, hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (neg save : Bool), P s ((if neg then inv a else a) :: kept save a r) →
      P (s+1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s+1) (a :: b :: r)) → P t ws

theorem Run.done {α inv meet join y} : @Run α inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {α inv meet join y s xs zs} (p : List.Perm xs zs)
    (h : @Run α inv meet join y s xs) : Run inv meet join y s zs :=
  fun P d q u b => q p (h P d q u b)

theorem Run.one {α inv meet join y s a r} (neg save : Bool)
    (h : @Run α inv meet join y s ((if neg then inv a else a) :: kept save a r)) :
    Run inv meet join y (s+1) (a :: r) := fun P d q u b => u neg save (h P d q u b)

theorem Run.two {α inv meet join y s a b r} (c ka kb : Bool)
    (h : @Run α inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s+1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {α inv meet join y} {P : ∀ t ws, @Run α inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (neg save : Bool)
      (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a r)),
      P _ _ h → P _ _ (Run.one neg save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun n k ⟨h', ih⟩ => ⟨Run.one n k h', one n k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

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
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

def Reach (n : ℕ) (gs : List Gate) (o a : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P o →
    (∀ q g, gs[q]? = some g → P (n + q) → ∀ u ∈ g.inputs, P u) → P a

theorem reach_self (n : ℕ) (gs : List Gate) (o : ℕ) : Reach n gs o o :=
  fun _ ho _ => ho

theorem reach_step {n : ℕ} {gs : List Gate} {o q u : ℕ} {g : Gate}
    (hq : gs[q]? = some g) (hr : Reach n gs o (n + q)) (hu : u ∈ g.inputs) :
    Reach n gs o u :=
  fun P ho hs => hs q g hq (hr P ho hs) u hu

theorem reach_cases {n : ℕ} {gs : List Gate} {o a : ℕ} (h : Reach n gs o a) :
    a = o ∨ ∃ q g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q) := by
  apply h (fun x => x = o ∨ ∃ q g, gs[q]? = some g ∧ x ∈ g.inputs ∧ Reach n gs o (n + q))
  · exact Or.inl rfl
  · intro q g hq hP u hu
    refine Or.inr ⟨q, g, hq, hu, ?_⟩
    rcases hP with rfl | ⟨q', g', hq', hin', hr'⟩
    · exact reach_self n gs (n + q)
    · exact reach_step hq' hr' hin'

def Live (n : ℕ) (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q)

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live n gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live n gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ_reach (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (hr : Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live n gs o (p + 1) a)) := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases reach_cases hr with h | ⟨q, g', hg', hin, hrq⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin, hrq⟩
        have := cleanG_lt (hcl q g' hg') _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

theorem live_succ_dead (n : ℕ) (gs : List Gate) (o : ℕ)
    (p : ℕ) (hnr : ¬ Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔ a ∈ liveList gs n o p := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    have hne : a ≠ n + p := by
      rintro rfl
      rcases hl with rfl | ⟨q, _, g', hg', hin, hrq⟩
      · exact hnr (reach_self n gs _)
      · exact hnr (reach_step hg' hrq hin)
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro ⟨hlt, hl⟩
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · by_cases hqp : q = p
      · subst hqp; exact absurd hrq hnr
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run (invF (n := n)) meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
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
      · rintro ⟨_, h | ⟨q, hq, g', hg', _, _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1; omega
    exact ⟨0, le_rfl, Run.perm (hperm.map (val gs n)) Run.done⟩
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    obtain ⟨d', hd', IH⟩ := ih (p + 1) (by omega)
    by_cases hr : Reach n gs o (n + p)
    · have hstep := live_succ_reach n gs o hcl p g hg hr
      have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
        (mem_liveList _ _ _ _ _).2 ⟨cleanG_lt (hcl p g hg) a ha, Or.inr ⟨p, le_rfl, g, hg, ha, hr⟩⟩
      have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
        Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
      have hvg := val_gate n gs p g hg (cleanG_lt (hcl p g hg))
      have hnd0 := nodup_liveList gs n o p
      have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
          val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
          Run (invF (n := n)) meetF joinF (val gs n o) (d' + 1)
            ((liveList gs n o p).map (val gs n)) := by
        intro j neg hmem hval
        have hj := hin j ((hmem j).2 rfl)
        have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
          List.perm_cons_erase hj
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
            rw [mem_kept]
            rintro (⟨_, h⟩ | h)
            · exact hnew j hj h.symm
            · exact hnew _ (List.mem_of_mem_erase h) rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
            simp only [decide_eq_true_eq]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
                · exact Or.inr (Or.inr ⟨haj, h1⟩)
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hj, fun _ => h1⟩
              · exact Or.inr ⟨h2, fun h => absurd h h1⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        rw [List.map_cons, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
      refine ⟨d' + 1, by omega, ?_⟩
      rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
      · apply single j true
        · intro a; simp [hinp]
        · funext x; rw [hvg x, hop, hinp]; simp [GateOp.eval]
      · by_cases hjk : j = k
        · subst hjk
          apply single j false
          · intro a; simp [hinp]
          · funext x; rw [hvg x, hinp]; rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
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
            intro a; rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
          have hp2 : (liveList gs n o (p + 1)).Perm
              ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j
                (kept (decide (Live n gs o (p + 1) k)) k
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
            funext x; rw [hvg x, hinp]
            rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
          rw [List.map_cons, kept_map, kept_map, hval] at IH'
          exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
    · have hp : (liveList gs n o (p + 1)).Perm (liveList gs n o p) :=
        (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) (nodup_liveList _ _ _ _)).2
          (live_succ_dead n gs o p hr)
      exact ⟨d', by omega, Run.perm (hp.map (val gs n)) IH⟩

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hlen, ho, hev⟩ := exists_clean n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live n gs o hcl ho gs.length 0 (by omega)
  refine ⟨d', by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
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
    exact hrun

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha, hm]; exact hw _ (by simp [hr]))
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
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k+k by omega, show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  apply List.any_eq_true.2 ⟨neg, by cases neg <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht, hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
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
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
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
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
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

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
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
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih => simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers, he, required_up h he]
  · simp [covers, he, required h]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | (grw [← Nat.add_assoc, ← hand]; exact ih')
            | (grw [← Nat.add_assoc, ← hor]; exact ih')

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
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

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl, Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (T w h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if fld T w ((lo + hi) / 2) ≤ h then bsr T w h f ((lo + hi) / 2) hi
       else bsr T w h f lo ((lo + hi) / 2))
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
    !(next (mask k) (s + 2 - ws.length) ws fun _ zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs)))

theorem bar_sound {k S N idx ori pool} {s i : Nat} (hb : bar k S N idx ori pool s i = true)
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (_ : Nat) (zs : List Nat) :=
      covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
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

def mv (m c : Nat) (ws : List Nat) : List Nat :=
  let a := ws.getD (c % 16) 0
  let b := ws.getD (c / 16 % 16) 0
  let op := c / 256 % 4
  let r := if op < 2 then ws.erase a else (ws.erase a).erase b
  (if op = 0 then a else if op = 1 then a ^^^ m else if op = 2 then a &&& b else a ||| b) ::
    kept (decide (c / 1024 % 2 = 1)) a (kept (decide (2 ≤ op ∧ c / 2048 % 2 = 1)) b r)

def StGen (k : Nat) (xs : List Nat) (PT : Nat → Nat) : Nat → Nat → Nat → List Nat
  | 0, _, _ => xs
  | d + 1, s, j =>
    let e := fld (PT s) 18 j
    mv (mask k) (e % 4096) (StGen k xs PT d (s + 1) (e / 4096))

def Sgen (k cap : Nat) (xs : List Nat) (PT : Nat → Nat) (s j : Nat) : List Nat :=
  StGen k xs PT (cap - s) s j

def idxGen (NN HT : Nat → Nat) (s : Nat) (zs : List Nat) : Nat :=
  bsr (HT s) 32 (hk zs) 14 0 (NN s)

theorem prove_base (n k cap : ℕ) (f : BFn n) (rows xs pool : List ℕ)
    (NN HT : ℕ → ℕ) (S : ℕ → ℕ → List ℕ) (hroot : S cap 0 = xs)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (hlen : rows.length = k + k)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun a => encL a rows) = xs)
    (hgoal : encL f rows = goal k)
    (hprop : ∀ zs ∈ xs.sublists, zs ≠ xs → (cov k zs &&& lo k) ≠ lo k)
    (hNcap : 0 < NN cap)
    (hchk : ∀ s ≤ cap, ∀ i < NN s,
      bar k S NN (idxGen NN HT) id pool s i = true) :
    ∀ s : ℕ, HasCircuitSize n f s → cap + 1 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run f hnc s h
  have hmask : mask k = 2 ^ rows.length - 1 := by rw [hlen]; rfl
  have hr : NatRun (mask k) (encL f rows) s' (ws.map fun a => encL a rows) :=
    Run.map (fun a : BFn n => encL a rows)
      (fun a => by rw [hmask]; exact encL_inv a rows)
      (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) hrun
  rw [hgoal] at hr
  have hsub' : (ws.map fun a => encL a rows).Sublist xs := by
    rw [← hxs]; exact hsub.map _
  by_cases he : (ws.map fun a => encL a rows) = xs
  · rw [he] at hr
    cases hxs_nil : xs with
    | nil =>
      rw [hxs_nil] at hr
      have hc := required hr
      have hne : cov k [] = 0 := rfl
      rw [hne] at hc
      have hlo : lo k ≠ 0 := by
        cases k with
        | zero =>
          simp [goal, lo] at hgoal
          obtain ⟨y, y', hne'⟩ := hnc
          have h0 : rows.length = 0 := hlen
          have hnil : rows = [] := List.eq_nil_of_length_eq_zero h0
          rw [hnil] at hxs
          have hxs0 : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun _ => 0) = [] := by
            simpa [encL, hxs_nil] using hxs
          have hn0 : n = 0 := by simpa using congrArg List.length hxs0
          subst hn0
          exact absurd (Subsingleton.elim y y') (fun e => hne' (e ▸ rfl))
        | succ k' =>
          simp only [lo]
          have : 1 ≤ 2 ^ k' := Nat.one_le_two_pow
          rw [pow_succ]; omega
      simp at hc
      exact hlo hc.symm
    | cons a r =>
      rw [hxs_nil] at hr
      have hcap : NatRun (mask k) (goal k) cap (a :: r) := extend_run hr (by omega)
      rw [← hxs_nil] at hcap
      rw [← hroot] at hcap
      exact bar_all (fun h => h) hchk cap le_rfl 0 hNcap hcap
  · exact hprop _ (List.mem_sublists.2 hsub') he (required hr)



def fT : BFn 6 := fun x => Nat.testBit (4261412864 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def sampleRows : List Nat := [11, 13, 14, 15, 19, 21, 22, 23, 25, 25, 25, 26, 26, 26, 28, 28, 28, 41, 42, 43, 44, 45, 46, 47, 49, 50, 51, 52, 53, 54, 55, 56, 56, 56, 27, 29, 30, 31, 27, 29, 30, 31, 27, 29, 57, 27, 30, 58, 29, 30, 60, 57, 58, 59, 60, 61, 62, 63, 57, 58, 59, 60, 61, 62, 63, 57, 58, 60]
def inputWords : List Nat := [0x356a93eec55aa07bb, 0x59b32e77466cc38dd, 0x9e3c74bb878f1c0ee, 0xfffffffff80ffff0f, 0xfffffffffff01fff0, 0xffffc9003fffe0000]

def bankWordChunk (i : Nat) : Nat := (if i < 46 then (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0xaa000b0000000000054000400000000000320002000000000000e0001000000000000000ff000000000000000f00000000000000000f00000000000000000 else 0x1932002200000000019000020000000000070e00110000000000700001000000000000fe000f00000000000fe000000000000000f0000e00000000000cc000d) else (if i < 3 then 0x78f000ee000000000780000e000000000066cc00dd000000000660000d000000000055aa00bb000000000550000b00000000002a5400440000000002a000040 else (if i < 4 then 0x241100001f844000012eec000007bb0000108880001c72200000244400003f110000000007ffe00ff0000000007ffe00000000000007f0000f00000000007f000000 else 0x36ffc7f01ffff000036ffc00ffffff000036ffc0001ffff000036ffc0001fff0000036ffc0001ff0f000036ffc0001ff00000034bb80001c0ee000026774000038dd))) else (if i < 8 then (if i < 6 then 0x14280000050a00000112202664448800991122026644400009011220266400880009112202664000000001122000004488000010200022040800088000036ffc7fffffff else (if i < 7 then 0x18302433000c0000c1830243300000000018300000060c00000152a12eec54a800bb142810aa850a000aa142810aa8500000a0142810aa800a0000a142810aa800000000 else 0x24489188811220722214293eec050a07bb214283444050a0711204081003810207001c3834bb870e000ee19322677464c800dd18302433060c000cc183024330600000c0)) else (if i < 9 then 0x356a91aa855aa00aa356a8366455aa0099356a8100055aa0000356a8100055000000356a8100000aa0000356a8100000000000254a93ccc152a0733244893eec112207bb else (if i < 10 then 0x356a93eec00fe070f356a93eec00aa07bb356a93eec00aa070b356a93eec00aa0700356a93eec00a0070a356a93eec00880709356a93eec000007bb356a93eec00000700 else 0x356a93eec44880700356a93eec44000790356a93eec40aa078b356a93eec40800788356a93eec11aa072b356a93eec11220722356a93eec05aa071b356a93eec050a0711)))) else (if i < 17 then (if i < 14 then (if i < 12 then 0x356a93eec50aa07ab356a93eec50aa070b356a93eec50a007aa356a93eec50a00700356a93eec500007a0356a93eec44aa079b356a93eec44aa070b356a93eec44880799 else (if i < 13 then 0x356a93eec558007b8356a93eec552207b2356a93eec550a07b1356a93eec550007bb356a93eec550007b0356a93eec55000700356a93eec54aa07bb356a93eec54a807bb else 0x356a93eec55aa070b356a93eec55aa0700356a93eec55aa00bb356a93eec55a807bb356a93eec55a007ba356a93eec55a007b0356a93eec558807b9356a93eec558807b0)) else (if i < 15 then 0x356a93eec55aa07bb356a93eec55aa07ba356a93eec55aa07b9356a93eec55aa07b0356a93eec55aa07ab356a93eec55aa07aa356a93eec55aa079b356a93eec55aa0799 else (if i < 16 then 0x356a93eec55fe07bb356a93eec55fa07bf356a93eec55ee07bf356a93eec55ba07bb356a93eec55ae07bb356a93eec55aa07ff356a93eec55aa07fb356a93eec55aa07bf else 0x356a93eec7daa07fb356a93eec77ee07ff356a93eec77aa07fb356a93eec5dba07bb356a93eec5daa07bb356a93eec57ae07bb356a93eec57aa07bb356a93eec55fe07bf))) else (if i < 20 then (if i < 18 then 0x3d7a93eec75ea07bb356ab7ffc55abffff356a93eec7ffe07ff356a93eec7ffe07bb356a93eec7faa07fb356a93eec7faa07bb356a93eec7f0007f0356a93eec7dfa07ff else (if i < 19 then 0x3d7ab7ffc75aa07fb3d7ab7ffc750007f03d7ab7ffc60ea07cf3d7ab7ffc60c007cc3d7ab7ffc55ea07bf3d7ab7ffc55aa07bb3d7ab7ffc00ea070f3d7ab7ffc00000700 else 0x49932e554264c385548912e774224438dd48912c1102244384441832e774060c38dd41830a444060c3811408108003820438003d7ab7ffc75ea07ff3d7ab7ffc75c007fc)) else (if i < 21 then 0x59b32e774000038dd59b32e7740000380059b32c33066cc00cc59b30a66466cc009959b30800066cc000059b3080006600000059b30800000cc000059b30800000000000 else (if i < 22 then 0x59b32e77406cc381d59b32e774060c381159b32e77400fe380f59b32e77400cc38dd59b32e77400cc380d59b32e77400cc380059b32e77400c0380c59b32e77400883809 else 0x59b32e77444cc380d59b32e7744488389959b32e7744488380059b32e7744400389059b32e77440cc388d59b32e7744080388859b32e77422cc384d59b32e77422443844))))) else (if i < 34 then (if i < 28 then (if i < 25 then (if i < 24 then 0x59b32e77464cc38dd59b32e77464c838dd59b32e77460cc38cd59b32e77460cc380d59b32e77460c038cc59b32e77460c0380059b32e774600038c059b32e77444cc389d else 0x59b32e774668838d959b32e774668838d059b32e774668038d859b32e774664438d459b32e774660c38d159b32e774660038dd59b32e774660038d059b32e77466003800) else (if i < 26 then 0x59b32e77466cc389d59b32e77466cc389959b32e77466cc380d59b32e77466cc380059b32e77466cc00dd59b32e77466c838dd59b32e77466c038dc59b32e77466c038d0 else (if i < 27 then 0x59b32e77466cc38fd59b32e77466cc38df59b32e77466cc38dd59b32e77466cc38dc59b32e77466cc38d959b32e77466cc38d059b32e77466cc38cd59b32e77466cc38cc else 0x59b32e77467cc38dd59b32e77466fe38df59b32e77466fe38dd59b32e77466fc38df59b32e77466ee38df59b32e77466dc38dd59b32e77466ce38dd59b32e77466cc38ff))) else (if i < 31 then (if i < 29 then 0x59b32e7747f0038f059b32e7747efc38ff59b32e7747ecc38fd59b32e77477ee38ff59b32e77477cc38fd59b32e7746edc38dd59b32e7746ecc38dd59b32e77467ce38dd else (if i < 30 then 0x5dbb3effc00ec380f5dbb3effc000038005dbb2e77476ec38dd59b33effc66cdffff59b32e7747ffe38ff59b32e7747ffe38dd59b32e7747fcc38fd59b32e7747fcc38dd else 0x5dbb3effc76ec38ff5dbb3effc76cc38fd5dbb3effc76a038fa5dbb3effc760038f05dbb3effc66ec38df5dbb3effc66cc38dd5dbb3effc50ec38af5dbb3effc50a038aa)) else (if i < 32 then 0x61c38b447fffe3fff61c38b447ff0e3ff161c38b44787fe3f1f61c38b447870e3f1161c38b44787003f1061c38b447800e3f0161c38b44780003f0061c389003870e0000 else (if i < 33 then 0x7dfb9beec55ee07bb7dfb9beec55aa07bb7dfb9beec00ee070b7dfb9beec000007007dfb8900077ee000079f3af777e7ce3fdd75eb9beefd7ae3fbb61c3bffff870fffff else 0x7dfbaf77400ee380d7dfbaf774000038007dfb9beec77ee07bb7dfb9beec77cc07b07dfb9beec77aa07bb7dfb9beec770007b07dfb9beec66ee070b7dfb9beec66cc0700)))) else (if i < 40 then (if i < 37 then (if i < 35 then 0x7dfbaf77477ee38dd7dfbaf77477cc38dd7dfbaf77477aa38d07dfbaf774770038d07dfbaf77466ee38dd7dfbaf77466cc38dd7dfbaf77455ee380d7dfbaf77455aa3800 else (if i < 36 then 0x7dfbbfffc77aa3ffb7dfbbfffc77003ff07dfbbfffc66ee3fdf7dfbbfffc66cc3fdd7dfbbfffc55ee3fbf7dfbbfffc55aa3fbb7dfbbfffc00ee3f0f7dfbbfffc00003f00 else 0x8a14641102851c044860c74bb81831c0ee860c508881831c0228204400038811c0007dfbbfffc77ee3fff7dfbbfffc77ee38ff7dfbbfffc77ee07ff7dfbbfffc77cc3ffd)) else (if i < 38 then 0x9e3c6433078f000cc9e3c50aa878f000aa9e3c4000078f000009e3c40000780000009e3c4000000f000009e3c40000000000008e1c749983871c0668a1474bb82851c0ee else (if i < 39 then 0x9e3c74bb800ffc00f9e3c74bb800f1c0ee9e3c74bb800f1c00e9e3c74bb800f1c0009e3c74bb800c1c00c9e3c74bb800a1c00a9e3c74bb80001c0ee9e3c74bb80001c000 else 0x9e3c74bb850a1c0009e3c74bb85001c0a09e3c74bb840f1c08e9e3c74bb84081c0889e3c74bb828f1c04e9e3c74bb82851c0449e3c74bb818f1c02e9e3c74bb81831c022))) else (if i < 43 then (if i < 41 then 0x9e3c74bb860f1c0ce9e3c74bb860f1c00e9e3c74bb860c1c0cc9e3c74bb860c1c0009e3c74bb86001c0c09e3c74bb850f1c0ae9e3c74bb850f1c00e9e3c74bb850a1c0aa else (if i < 42 then 0x9e3c74bb87881c0e89e3c74bb87851c0e49e3c74bb87831c0e29e3c74bb87801c0ee9e3c74bb87801c0e09e3c74bb87801c0009e3c74bb870f1c0ee9e3c74bb870e1c0ee else 0x9e3c74bb878f1c00e9e3c74bb878f1c0009e3c74bb878f000ee9e3c74bb878e1c0ee9e3c74bb878c1c0ec9e3c74bb878c1c0e09e3c74bb878a1c0ea9e3c74bb878a1c0e0)) else (if i < 44 then 0x9e3c74bb878f1c0ee9e3c74bb878f1c0ec9e3c74bb878f1c0ea9e3c74bb878f1c0e09e3c74bb878f1c0ce9e3c74bb878f1c0cc9e3c74bb878f1c0ae9e3c74bb878f1c0aa else (if i < 45 then 0x9e3c74bb878ffc0ee9e3c74bb878fdc0ef9e3c74bb878fbc0ef9e3c74bb878f5c0ee9e3c74bb878f3c0ee9e3c74bb878f1c0ff9e3c74bb878f1c0fe9e3c74bb878f1c0ef else 0x9e3c74bb87ef1c0fe9e3c74bb87dfbc0ff9e3c74bb87df1c0fe9e3c74bb87af5c0ee9e3c74bb87af1c0ee9e3c74bb879f3c0ee9e3c74bb879f1c0ee9e3c74bb878ffc0ef)))))) else (if i < 69 then (if i < 57 then (if i < 51 then (if i < 48 then (if i < 47 then 0x9f3e74bb87cf9c0ee9e3c76ffc78f1ffff9e3c74bb87fffc0ff9e3c74bb87fffc0ee9e3c74bb87ff1c0fe9e3c74bb87ff1c0ee9e3c74bb87f01c0f09e3c74bb87efdc0ff else 0x9f3e76ffc7c89c0f99f3e76ffc7c01c0f09f3e76ffc78f9c0ef9f3e76ffc78f1c0ee9f3e76ffc44f9c09f9f3e76ffc4489c0999f3e76ffc00f9c00f9f3e76ffc0001c000) else (if i < 49 then 0xa64cd188b99ffc72fa64cd188b9933c722a64cd188b9901c720a64cd188b8033c702a64cd188b8001c700a64cc1003993200009f3e76ffc7cf9c0ff9f3e76ffc7cf1c0fe else (if i < 50 then 0xbf7ed3eec00fa070bbf7ed3eec00000700bf7ec10007dfa0000be7cf5bbbf9f3c7eeb76ed3eefddbbc7bba64cf7fff9933ffffa64cd188bffffc7ffa64cd188bff33c7f2 else 0xbf7ed3eec7dfa07bbbf7ed3eec7df007b0bf7ed3eec7daa07bbbf7ed3eec7d0007b0bf7ed3eec78fa070bbf7ed3eec78f00700bf7ed3eec55fa07bbbf7ed3eec55aa07bb))) else (if i < 54 then (if i < 52 then 0xbf7ef5bb87dabc0e0bf7ef5bb87d01c0e0bf7ef5bb878fbc0eebf7ef5bb878f1c0eebf7ef5bb855fbc00ebf7ef5bb855abc000bf7ef5bb800fbc00ebf7ef5bb80001c000 else (if i < 53 then 0xbf7ef7ffc78fbc7efbf7ef7ffc78f1c7eebf7ef7ffc55fbc7bfbf7ef7ffc55abc7bbbf7ef7ffc00fbc70fbf7ef7ffc0001c700bf7ef5bb87dfbc0eebf7ef5bb87df1c0ee else 0xca956c1138001f800ca9548003aa540000bf7ef7ffc7dfbc7ffbf7ef7ffc7dfbc0ffbf7ef7ffc7dfa07ffbf7ef7ffc7df1c7febf7ef7ffc7dabc7fbbf7ef7ffc7d01c7f0)) else (if i < 55 then 0xdbb76e777eeddf8ddca957efffaa55ffffca956c113fffff8ffca956c113ff55f8f4ca956c113aafff84fca956c113aa55f844ca956c113aa01f840ca956c1138055f804 else (if i < 56 then 0xdfbf6e77478fc380ddfbf6e77478f03800dfbf6e77466fc38dddfbf6e77466cc38dddfbf6e77400fc380ddfbf6e77400003800dfbf480007efc0000debd7cbbbfaf5f8ee else 0xdfbf7cbb866fdc00edfbf7cbb866cdc000dfbf7cbb800fdc00edfbf7cbb80001c000dfbf6e7747efc38dddfbf6e7747ef038d0dfbf6e7747ecc38dddfbf6e7747e0038d0)))) else (if i < 63 then (if i < 60 then (if i < 58 then 0xdfbf7effc00fdf80fdfbf7effc0001f800dfbf7cbb87efdc0eedfbf7cbb87ef1c0eedfbf7cbb87ecdc0e0dfbf7cbb87e01c0e0dfbf7cbb878fdc0eedfbf7cbb878f1c0ee else (if i < 59 then 0xdfbf7effc7efc38ffdfbf7effc7ef1f8fedfbf7effc7ecdf8fddfbf7effc7e01f8f0dfbf7effc78fdf8efdfbf7effc78f1f8eedfbf7effc66fdf8dfdfbf7effc66cdf8dd else 0xeeddfd99bbb77ff66eeddc9003bb760000ebd7ef557af5fff55ebd7c9003af5e0000e7cfdbccf9f3fff33e7cfc90039f3e0000dfbf7effc7efdf8ffdfbf7effc7efdc0ff)) else (if i < 61 then 0xffffc9003870e0000ffffc900380fe000fffffc900380fe0000ffffc900380f00000ffffc900380cc0000ffffc900380aa0000ffffc900380000000ffffc90007ffe0000 else (if i < 62 then 0xffffc9003d0a00000ffffc9003c4fe0000ffffc9003c4880000ffffc9003aafe0000ffffc9003aa540000ffffc900399fe0000ffffc900399320000ffffc900387fe0000 else 0xffffc9003e6cc0000ffffc9003e6000000ffffc9003e0fe0000ffffc9003e0c00000ffffc9003d5fe0000ffffc9003d5aa0000ffffc9003d5000000ffffc9003d0fe0000))) else (if i < 66 then (if i < 64 then 0xffffc9003fdfe0000ffffc9003fdfa0000ffffc9003f8fe0000ffffc9003f8f00000ffffc9003f8000000ffffc9003f7fe0000ffffc9003f7ee0000ffffc9003e6fe0000 else (if i < 65 then 0xffffc9003ff880000ffffc9003ff540000ffffc9003ff320000ffffc9003ff0e0000ffffc9003ff0000f0ffffc9003ff000000ffffc9003fefe0000ffffc9003fefc0000 else 0xffffc9003fffc0000ffffc9003fffa0000ffffc9003fff00000ffffc9003ffee0000ffffc9003ffcc0000ffffc9003ffc00000ffffc9003ffaa0000ffffc9003ffa00000)) else (if i < 67 then 0xffffc9003fffe000fffffc9003fffe000effffc9003fffe000dffffc9003fffe000bffffc9003fffe0004ffffc9003fffe0002ffffc9003fffe0001ffffc9003fffe0000 else (if i < 68 then 0xffffc9003fffe00bbffffc9003fffe00b0ffffc9003fffe0044ffffc9003fffe0040ffffc9003fffe0022ffffc9003fffe0020ffffc9003fffe0011ffffc9003fffe0010 else 0xffffcb447fffe3f11ffffc9223fffe0088ffffc9003fffe00ffffffc9003fffe00f0ffffc9003fffe00eeffffc9003fffe00e0ffffc9003fffe00ddffffc9003fffe00d0))))) else (if i < 81 then (if i < 75 then (if i < 72 then (if i < 70 then 0xffffcb667fffe0009ffffcb667fffe0000ffffcb667ff880099ffffcb667ff000090ffffcb667c4fe0099ffffcb667c4880099ffffcb66780fe0009ffffcb66780000000 else (if i < 71 then 0xffffd9aabff0000a0ffffd9aabd0fe00aaffffd9aabd0a000aaffffd9aab80fe000affffd9aab80000000ffffd988bffffc722ffffcb667fffe0099ffffcb667fffe0090 else 0xffffdbeef80fe070bffffdbeef80000700ffffdbeec7ffe07bbffffd9aabfffe00aaffffd9aabfffe00a0ffffd9aabfffe000affffd9aabfffe0000ffffd9aabffa000aa)) else (if i < 73 then 0xffffdbeeffffe07b0ffffdbeeffffe070bffffdbeeffffe0700ffffdbeeffffe00bbffffdbeefffaa07bbffffdbeefff0007b0ffffdbeefd5fe07bbffffdbeefd5aa07bb else (if i < 74 then 0xffffed333ffc000ccffffed333ff0000c0ffffed333e0fe00ccffffed333e0c000ccffffed33380fe000cffffed33380000000ffffed113fffff844ffffdbeeffffe07bb else 0xffffef777e6cc38ddffffef77780fe380dffffef77780003800ffffef7747ffe38ddffffed333fffe00ccffffed333fffe00c0ffffed333fffe000cffffed333fffe0000))) else (if i < 78 then (if i < 76 then 0xffffef777fffe38ddffffef777fffe38d0ffffef777fffe380dffffef777fffe3800ffffef777fffe00ddffffef777ffcc38ddffffef777ff0038d0ffffef777e6fe38dd else (if i < 77 then 0xfffffdbbbfffe00eefffffdbbbfff1c0eefffffdbbbff01c0e0fffffdbbbf8ffc0eefffffdbbbf8f1c0eefffffdbbb80ffc00efffffdbbb8001c000fffffdbb87fffc0ee else 0xffffffffc7fffffffffffffffc7f01fff0ffffffffc00ffff0fffffffffc0001ff00fffffdbbbffffc0eefffffdbbbffffc0e0fffffdbbbffffc00efffffdbbbffffc000)) else (if i < 79 then 0xfffffffff800fff01fffffffff8001fffffffffffff8001fff0fffffffff8001ff0ffffffffff8001ff00fffffffff8001f800fffffffff8001c700fffffffff80003f00 else (if i < 80 then 0xfffffffff80cdff00fffffffff80c1ff0cfffffffff80abff0bfffffffff80abff00fffffffff80a1ff0afffffffff8089ff09fffffffff8055ff04fffffffff8033ff02 else 0xfffffffff80ffc70ffffffffff80fe3f0ffffffffff80fdff0ffffffffff80fbff0ffffffffff80f1ff0efffffffff80f1ff00fffffffff80efff0ffffffffff80cdff0d)))) else (if i < 87 then (if i < 84 then (if i < 82 then 0xfffffffff8701ff10fffffffff80fffffffffffffff80ffff0ffffffffff80ffff0efffffffff80ffff0dfffffffff80ffff0bfffffffff80ffff00fffffffff80fff80f else (if i < 83 then 0xfffffffffaaffff4ffffffffffaa55ff44fffffffffaa01ff40fffffffff99ffff2ffffffffff9933ff22fffffffff9901ff20fffffffff87ffff1ffffffffff870fff11 else 0xfffffffffd501ffb0fffffffffd501ff00fffffffffd0ffffaffffffffffd0a1ffaafffffffffd001ffa0fffffffffc4ffff9ffffffffffc489ff99fffffffffc401ff90)) else (if i < 85 then 0xfffffffffe601ff00fffffffffe0ffffcffffffffffe0c1ffccfffffffffe001ffc0fffffffffd5ffffbffffffffffd5ffff0ffffffffffd5abffbbfffffffffd5abff00 else (if i < 86 then 0xffffffffff7ffffffffffffffff7efffffffffffffff701fff0fffffffffe6ffffdffffffffffe6ffff0ffffffffffe6cdffddfffffffffe6cdff00fffffffffe601ffd0 else 0xffffffffffdfbffffffffffffffd01fff0ffffffffff8ffffefffffffffff8ffff0fffffffffff8f1ffeeffffffffff8f1ff00ffffffffff801ffe0ffffffffff801ff00))) else (if i < 90 then (if i < 88 then 0xfffffffffff01ff00fffffffffff01f8f0fffffffffff01c7f0fffffffffff003ff0ffffffffffeffffffffffffffffefdffffffffffffffe01fff0ffffffffffdffffff else (if i < 89 then 0xfffffffffff55fff4fffffffffff33fff2fffffffffff0ffff1fffffffffff01fffffffffffffff01fff0fffffffffff01ffe0fffffffffff01ffd0fffffffffff01ffb0 else 0xfffffffffffeffffffffffffffffcdfffdfffffffffffcdfff0fffffffffffc1fffcfffffffffffabfffbfffffffffffabfff0fffffffffffa1fffafffffffffff89fff9)) else (if i < 91 then 0xfffffffffffffff00ffffffffffffff8fffffffffffffffc7ffffffffffffffe3fffffffffffffffdffffffffffffffffbffffffffffffffff1fffeffffffffffff1fff0 else (if i < 92 then 0xffffffffffffffff0fffffffffffffffeffffffffffffffffeefffffffffffffffdffffffffffffffffddfffffffffffffffbffffffffffffffffbbfffffffffffffff0f else 0xfffffffffffffffffffffffffffffffffeffffffffffffffffdffffffffffffffffb)))))))
def bankWord (i : Nat) := fld (bankWordChunk (i / 8)) 68 (i % 8)

def decodeState : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, x => bankWord (x &&& 1023) :: decodeState n (x >>> 10)

def level2Chunk (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x8417a460e10688ee3931ce1dce61648d539858e354e5f71048384178460e3e684a63929d9120e3e668d53955c41dcde15e1233 else 0x955c61dce3e4c1173785ad3b8e10688f038f998354e3e57d0e395530434e6b638a6394dce120e5557d083929ce1dcde1688f73) else (if i < 3 then 0x985ba1dce3c688a63785ce264e284c123392198298e5f4c1043955cd120e484c10e39555f410e2a57d183841ce250e616f8773 else 0x8f95f440e2857d1838c530460de1764903841ce240e33688d5378581460e6b6e84838cdad298e6165ca63985c3120e35688d53))
def level2 (i : Nat) := fld (level2Chunk (i / 12)) 34 (i % 12)

def level3Chunk (i : Nat) : Nat := (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0xa36106a0f44a365957d0c4a362d57d1e49ce4557d1749ce5a7307749ce4357d1749ce48664d549ce3a6b4d5484130298584a366570c6349ce484c1174785a2354334 else 0x9ce106a0f749ce68640d549ce6b70c7749ce107449949ce6370c77478556354484785452987749ce48684c149ce6b700774785562987749ce69644d549ce356b4d54) else (if i < 3 then 0x9ce3157d2049ce4257d174841452985849ce3157d1c49ce486b0d549ce6b65cd54b0e3f66cd549ce6365cd549ce107409947855f298484a3642678d548f95f298454 else (if i < 4 then 0x9ce106a8f649ce6265cd549ce6b7047749ce4657d1349ce549215f49ce5a57d0b49ce2e57d2349ce107649049ce3f57d1749ce6270c7749ce5d7247749ce10748924 else 0x9ce106b4f54a36025f92349ce6170c7749ce4857d2249ce5f7607749ce6b8f4d54a364e7646349ce3157d1f4a364252d1749ce2c57d234b0e346b4ab49ce2f57d1d4))) else (if i < 8 then (if i < 6 then 0xb0e626ec774841302ec4849ce5c7347749ce336b4d549ce5f57d0949ce366b4d549ce5957d0d49ce107589949ce5f52d0d49ce6165cd549ce2e57d1a49ce3b6a8d54 else (if i < 7 then 0x9ce5b7647749ce376b4d549ce106b4f74785302984849ce105e12349ce105f51d49ce1074c9349ce4866cd549ce6b63cd549ce3c69cd549ce6b6e8774a362c52d234 else 0x9ce517447749ce106b5224795303044849ce5857d074b0e5657d054b0de56b4ef49ce4867cd549ce1073c9949ce106051d49ce105f12349cde56b4f74a365952d0d4)) else (if i < 9 then 0xb0e564d50d49ce6b65ca649ce105f11a49ce6b70c4849ce686f07749ce3c694d54a3665658d549ce5f71c774a36376b4c14a36026051e49ce106a4f64b0e5f4d5054 else (if i < 10 then 0xa3665708774b0e626fc7749ce105fd2347dd302987747954b2984849ce6670c7749ce3c6a8d54a366b700634b0e5f7144d49ce537547749ce3b6a4d549ce5e730774 else 0x9ce105e9234b0de56051949ce2b57d2349ce3c6b4c149ce4857d1447855f2985847f1303544849ce6665cd549ce537647747f130298774b0e5373c4d4b0e4b73c774)))) else (if i < 17 then (if i < 14 then (if i < 12 then 0x7855f3b87747dd452987749ce5857d0d49ce5f7350d49ce5a57d0d4a36026b4f449ce6a654d54841402984849ce5e57d0b49ce667047749ce2e57d1c49ce676b4d54 else (if i < 13 then 0x785302ec7749ce10690f24809302984d49ce6870c7749ce026b4f747dd5f298484b0e1073c9549ce10698f249ce59734774a364852d144a36027509949ce5f7344d4 else 0xa36657007747854b2ac4849ce3c698d549ce3157d1849ce3c68cd547c940354484b0e6270c4d49ce6865cd549ce106b4f1484130410d549ce4657d1749ce60920d54)) else (if i < 15 then 0x9ce105f11c4841ba57c484b0e294d5234b0e3f684ab4785353044849ce10765ab49ce6b650d549ce5f7307749ce3c6a4d547855f3306e49ce3c690d5479530298634 else (if i < 16 then 0xa366b650c149ce48680d54785783547749ce1069cf349ce10688f749ce3152d2349ce4c7647749ce48678d549ce64644d549ce537487749ce6b6ec774841304602e4 else 0xa3648678c14b0e105e51949ce446b4d549ce3a69cd549ce537644849ce2f57d1b49ce5f57d0b4a364257d1549ce4a7647749ce10754994b0e2957d19478530330774))) else (if i < 20 then (if i < 18 then 0x9ce696f47749ce105f9234b0e1073c9149ce346b4d54785563307749ce106b4ef4785302ac6349ce107649949ce4d7647749ce4852d1749ce3e684d549ce1075dad4 else (if i < 19 then 0x7855f330484b0de55e52349ce10694f34b0e3668cd549ce39690d549ce48684ab49ce47680d549ce386b4d549ce527587749ce537507749ce39698d549cde5764994 else 0x785403544849ce105f51b49ce507407749ce5b57d2349ce5757d0649ce587347749ce5a7347749ce5f7107749ce5f7346349ce5374c7749ce2f57d2349ce48674d54)) else (if i < 21 then 0x9ce6b6acd54b0de568cf749ce40684d549ce5e57d0d4b0e105ed1949ce106051b49ce6b654d549ce106b4ee49ce6b644d549ce3a694d549ce6b6fc7749ce53764994 else (if i < 22 then 0x9ce3157d1d49ce107589747dd5f298584a360276496478535298634785302984d49ce10761234a36597346349ce2a57d2349ce5757d0d49cde16b4f749ce43680d54 else 0xb0e314d51949ce41674d54841302d84849ce106051e49ce105f52349ce5f57d0549ce2d57d234785303044849ce5f57d0749ce10605194841302985d49ce57720774))))) else (if i < 34 then (if i < 28 then (if i < 25 then (if i < 24 then 0x9ce5f4d50d49ce10748994a36106a0f54a36107509649ce4857d1649ce4857d1049ce5657d0d49ce106012349ce677647749ce106052349ce48684d54b0e484d50f4 else 0x9ce027649949ce537387749ce6b65cc14a364f7507747854b2984847f1302ec7749ce517647749ce10744934841304387749ce6b70c4d49cde56052349ce1069cf74) else (if i < 26 then 0xb0e6264cd549553028c7749ce5f72c7749ce48685174a36376a0d549ce47684d549ce5f57d0649ce107409249ce6097c7749ce106051a49ce6b9507749ce106b4f04 else (if i < 27 then 0x9ce5f57d0d4b0e6b6ec4d49ce10694f749ce10764944a362c57d1e49ce6970c7749ce106b4f447855f4602e49ce106b4f649ce6b638d549ce4757d1649ce41684d54 else 0xa365972c7749ce3b6b4d54a364e7507749ce5f720774b0e3f57d114841982987749ce6965cd547855f3549047c95f2d84849ce107509949ce6b648d549ce5d57d074))) else (if i < 31 then (if i < 29 then 0x9ce48668d549ce4357d1649ce587247749ce3c6a0d549ce106a8f74b0e1068cf14a3665650d549ce3057d234a36537506349ce45684d549ce1074c9949ce43684d54 else (if i < 30 then 0xb0e48664ab49ce2957d234a36107509849ce5557d0d49ce577347749ce66654d549ce5f57d0849ce3c6b4ab49ce5e734774785302986349555f28c484b0e56714774 else 0x9ce5f4c10d4b0de57649149ce105e5234785303545d49ce3f684d549ce40670d549ce5f57d2149ce02605234a363c6a0c149ce48684a649ce42684d549ce4857d134)) else (if i < 32 then 0x9ce48670d54809302ac4849ce106051c4a3642684c149ce106b4f249ce4857d1549ce106b12349ce6b70c6349ce567347749ce5d57d0d49ce527547749ce4857d114 else (if i < 33 then 0x9ce4057d124b0e6265cab49ce3c6b4d549ce4157d1349ce106a4f749ce10690f749ce527647749ce106012049ce10698f749ce1068cf74a36026a0f749ce10605204 else 0x9ce6b70d9749295f3544847855f2d84848cd5f298774b0e3468cd54b0e3f4d5174b0e3f57d0f49ce537644d4b0e1068cef49ce4b7647749ce10738994a36105fd1e4)))) else (if i < 40 then (if i < 37 then (if i < 35 then 0x9ce5f7347749ce4857d1249ce6b640d549ce63640d549ce107549749ce106011f49ce5174c7749ce107652149ce105ed2349ce106051f49ce646f47749cde1764994 else (if i < 36 then 0x841ce120394841302984849852d2987749ce107649548418e57ca64b0e6b63cab49ce3e57d1749ce107649749ce314d5234809352984849ce5f728774b0e5657d094 else 0x9ce3057d2049ce6b75c7749ce50764774841302ec5d49ce6565cd54795302984849ce6b64cd54841a22983349ce107649649ce3157d1b49852d3544849ce6570c774)) else (if i < 38 then 0x9ce396b4d549ce3157d1e49ce6a70c7749ce4f7647749ce557347749ce484d51749ce4857d0f49ce5f7187749ce6b6f87749ce3157d1949ce45670d54a3659728774 else (if i < 39 then 0x9ce4057d174b0e5671c7749ce537447749ce3157d234a366565cc14a36386a0d54841452984849ce6a65cd54a364267cd54785303044d47c9303544849ce46674d54 else 0x9ce3c6b4a649ce316052349ce4557d1249ce5d734774a363152d1e49ce6a704774785303546e49ce537407749ce5f8f55f49ce6b6f47749cde16052349ce3057d1f4))) else (if i < 43 then (if i < 41 then 0x9ce53764634b0e4d73c774b0e6263cd547c95f2984849ce48660d549ce3157d1a49ce4857d1747854b2984d49ce4857d0e49ce4e764774841c43544849ce6b658d54 else (if i < 42 then 0x9ce6470c7749ce107649147855f2986e49ce10764934a364257d1449ce5f57d0449ce46684d54785563546e4b0de573c994b0e3f664d549ce5c57d064785302ac484 else 0x9ce5f57d0a49ce507487749ce5c57d0d49ce6465cd549ce5f7344849ce537587749ce107649249ce6b7087749ce6b6f07747f1303545d4a36105f91e49ce636f0774)) else (if i < 44 then 0x9ce3c688d54b0e2b57d1949ce3c6b4f749ce5f7247749ce2857d2349ce4757d1749ce314c1234809302984849ce5c7207748a130354774b0e567344d49ce10764984 else (if i < 45 then 0xa365957d0a4785302987749ce10605184a365f52d0a4785352984849ce4457d234b0e3c68cab49ce5f57d0c4841402d84849ce5f7147749ce4157d1749ce6b65cab4 else 0x785303544848f930354454a365f728634b0e4b7644d49ce5373c7749ce106b4f34785ce1dc394))))))
def level3 (i : Nat) := fld (level3Chunk (i / 12)) 44 (i % 12)

def level4Chunk (i : Nat) : Nat := (if i < 93 then (if i < 46 then (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0x9ce10684d5135673809813547759ce1052cd518d6738415f36c775a02104d4c11dd6c37955f2ac4d59ce10734d51356739315f354775b0de14d4d51216828095f354775b5de157cd5121673841302ac485 else 0xb0e8d9195f45d68d9ce6b65cd559cde157cd52356738414b3d87759ce1052cc11216c3a3660920d559b21057cd51dd673841812987759ce1057cc118d6738415f48c2d5a35e157ca61216738915f298775) else (if i < 3 then 0x9ce105e4d51dd673841813544859ce1057cf51dd6738415f354705b0e8d841ad3c5673841ad2983359ce2457cd5121673809ad3543359ce1052cb91dd673841cd304775a0e0252cd51dd673841563546e5 else (if i < 4 then 0xb0de54d4d513567397d5f28c4859ce6b4b4d51dd6898095f3547759cde14d4ab1dd6737954b3546359ce104d4bd1dd673841303a477578530354a61dd673841a13047759ce1054cd51dd67398d2d354775 else 0x9ce1057ca61b967394d5f2987759ce3657cd51dd673841ad3543b59cdf257cd51dd6739295f3547759cde157cb61dd6738095f3546e59ce1057cd52196737955f304635b0e8d8f1a33556737855f3545d5))) else (if i < 8 then (if i < 6 then 0xb0e8d8f1a935567394d5f3544859ce1057cd51a16738415f354795a7e1057cb41356738413d3547759cdf057cd51dd673795533547759ce1051cab1dd673835303547759ce104c8d51dd6738cd5f354775 else (if i < 7 then 0x9ce106b0d51dd6738415f48ca45b0e738c55f48d655841303547759cde15d4d51dd6738c61057d235b0e5657ca313568d8094b3044d59ce104d4c71dd673841c357c4d59ce10680d518d67397dcd57c775 else 0x2739adc31dd27384173298775b0e8d9ad9435567378d5f2ac775b0e8d97dcc1dd6738095f45c7759ce1070d4b1dd6738415f3544a59ce025ccd51dd68d8095c3547459ce1057cd51696738ed4b354775)) else (if i < 9 then 0x9ce106a8d50c96739892d3547759cdf557cd51dd6737859c3547759c21057cd51dd6738415f3549959ce4d57cd51dd673841303546959ce1057ccc18d6737995f354775b0e8d841d96ad6738415f3545c5 else (if i < 10 then 0x9ce0657cd51dd6a1841303544859ce1057cf71dd6738413c3547759ce0957cc71dd6738419752cd55b0e10508b81356737955f3545a5001e157ca61212738415f45c4859ce105ccd512168d8414b304635 else 0x9cdfd4c0d51dd6737955f3549959ce548415f1dd61057d302984859ce10580d51dd6738095f2ac4859ce1057cd522d673841cc3547759ce3757cd51dd6738419757cc15002739ad973552738415f3244d5)))) else (if i < 17 then (if i < 14 then (if i < 12 then 0xb0e8d9219e3556737955f3548b59ce024d4a61dd6738415f3546c5b0e8d991913556737955f3dc7759ce1957cd51dd6737cd5f2e07759ce10500d518d6c3a366b6ec7759ce1052cc91dd68d7954b304635 else (if i < 13 then 0x9ce024c0d51dd673841352984859ce1055ca61dd6106895f2987759ce024d4d5121673809573547759ce0257ce91dd6739adc33547759ce105a0a61dd6808415f3047759ce104c0eb1dd67380968354775 else 0x9ce106395f3556737a55f3547759ce10738770e569f8415f2e04d5b0e024d4ab135673841683544859ce104c0a61dd6739221057d1759ce6b4b8d51dd673841c152c7759cde157cd52016c3a363152d235)) else (if i < 15 then 0x9ce0d57ca61dd6738415f488775b0e8d921a03556807955f3047759ce614b4d51dd6737dd5f354635b0e8d841a73cd6c37955f3bc7759ce1055cd51216738415f3a44857855f354a61216c39ce4857d175 else (if i < 16 then 0x9ce1057d1d0b16738955f3548d5841303e4d51dd673841ad3dc3359cdfc57cd518d6738414b3545f59ce1057cdd1dd6737855f2ac7759ce2457cd522d6b1841352f47759ce104c0d51216738415f2f4775 else 0x9ce106b4f71dd67385d5f378775b0e106ed5f1356c3a36107549959ce10688d50cd673785d91dc3959ce5357cd52656738417b3547759ce0d57cd5121673795302987759ce1057cc117d6c3841302ac4d5))) else (if i < 20 then (if i < 18 then 0xb0e8d97d5f42d673785353547759ce0257cd51a56738415f31c7759561057cd51216738555f354775a363757cc11dd6738419257cd559cde54c0d51216737955f2f47759ce1057cb51dd6738415f334635 else (if i < 19 then 0x9ce5157cab1dd6a18095f354485aaa1057ca61356c3a36446b4d559cdfa57cd51dd6c3a363a69cd559cde157d121dd6c3795352ac6359c61057cd51dd6c3841a32ac3359ce1057ca61a56c3a362f57d1b5 else 0x9cde557cc71dd6c3a361075dad5a861057ca61216738c55f2ac7759ce1051cd51dd673921a13544559f61057cd51216739ad2f354775a81e157cd51dd6738415f2ac585a3673841ad3dd67384130304635)) else (if i < 21 then 0x9f61057ca818d6738414b3546b59cdfd57ca61dd6738099557cd55aa21057cab18d6c3795353347759ce02544d51dd673895753547759ce104d4b81dd6738415f348635aaa1052ca61dd68d82551354635 else (if i < 22 then 0x9ce1057cc11ad67380956354775b0e8d841d92656c3a364d7647759ce105ccd522d6c3a364852d1759ce10568d51dd6738415f3786359ce10754770e16738415f42cd55a36024c0c11dd67384151298775 else 0x9ce10544d5121673841353545859ce10570a61dd673945353547759cde357cd51dd6737f55f3544859ce10508d518d6737c9303547759cde551cd51dd673841562987759ce02570d51dd6738415f2cc775))))) else (if i < 34 then (if i < 28 then (if i < 25 then (if i < 24 then 0x9ce1057cd51cd67d8414b3546359ce10558d51216c3a36346b4d559ce10514a61dd68d841303044859ce1066cd51dd67380945354775a360257cd52596738c5353547759ce0257ceb1dd6c3a36106b4ef5 else 0x9ce1057cab1d16c3a36537507759ce10514d51216738415f3ac4859ce0257ca61dd67d8415f3046359ce1057cb41dd6c3a35e5764995b0e8d9a5bd1dd6738415f3987759ce10570d51216c3a36105f9235) else (if i < 26 then 0x9ce1057d072ad6737b95f3547759fa1057cc11dd6737895f3547759ce1054cd51a56c3a3647680d559ce0257cd51216738415f3547c5b0e8d8e1ad3556c3a36527587759ce104c0d516967e8414b354775 else (if i < 27 then 0xb0e8d841a53cd67384130354995b0dfd4d4d513567397d5f2847759ce10764770e167385d5f354635a3610750630e56738414c354775a360257cc11a56c3a3648684ab59ce1057ca61216738415f35c775 else 0xb0e8d94dd31dd6737955f298485a85f257cd512167384135354745b0e8d8bd5f48d6738415f3a48b59ce104c0f71dd673841a935432500273841ad3dd2738f15f3544d5ace104c0d51756c3a3648674d55))) else (if i < 31 then (if i < 29 then 0x9ce0252cd518d68d8414b3046b59cde757cd51dd6c3a3658734775b0e8d969cd1dd673841263547759ce1067cd51dd6738415f2ec5d59ce3c52cd51dd6738415f3546659ce104c0d522d6c3a365f734635 else (if i < 30 then 0xb0e104d4a61356738095f304635b0e8d8417d46d6c3785302987759ce1052ca618d6738415f44c4d5b0e8d96d5f48d6739ad2c354775afde157cd51dd6738415f310775841e14c0a61dd6738f15f304775 else 0xb0de14c0d51216737855f3547759ce104d5230b96c3a366b6fc775841e14c0d51216738415f354815b0e8d94dd926567382d5f2ac7759ce6757cd51dd6738955f2ac775a3602570c11dd6898095c354775)) else (if i < 32 then 0x9ce10684d518d6c3841352ac5f5b0e8d9ad91355673841c43547759cde157cd51bd673841532987759ce1057cf618d68d8094b2987759ce10734d518d673809533547759ce10534d51dd6c3a363a694d55 else (if i < 33 then 0xa360257cc112168d8414b2984859ce0b4d4d51dd673841ad3dcd559ce1057cb81dd6737c95f2987759ce254d4d51dd69b84135354775b0e8d9ad9535567384153354485a360252cd51216739ad2d298775 else 0xa360257cf41dd6c3a365e57d0d59ce1057d1b0b96738414b3548d59cde14c0ab1dd6c3a36106051b59cde152cd51356c37e15f2ac5a59ce104c0bd1dd68d841533046959ce6b4b4d51216c3795573544d5)))) else (if i < 40 then (if i < 37 then (if i < 35 then 0x9ce2157cd51dd6739455f3547759ce1057cb61356738415f458635b0e8d9adab3556738415f3048d5b0de557ccd1bd6737855f3044d59cdf257cd51216738395f3547759ce104d4ab1356c3795303544d5 else (if i < 36 then 0xb0e8d841d848d673841d91dc3759ce1052cd51756737d15f3547759cde557cb81dd6738095f3545a59ce3157cd51dd6737854b3047759ce1057ce21dd6aa7dd5f298775b0e8d90da03556738415f354585 else 0x9ce3b57cd518d6738413031c775b0de568cd50cd673785813547759ce0157cd51dd6738415f3045d59ce1052cb61dd6739695f2887759ce10765ad48d6738415f32c775a021057cc11a56738415f2985a5)) else (if i < 38 then 0xaa61057ca61dd673785ad354335b0e8d8c55f4756737955f3545859ce1057ca62656c3a36107589759ce105d4d51356739715f28c775a367394dd91dd68d8094b3046359ce1070d5f18d6738095f354995 else (if i < 39 then 0xb0e8d97d5f4156c3a362d57d2359ce664b4d51dd6738095f3548b5a25e157cd51dd673809cc3547759ce104e8d51dd6c3a365f57d0759ce1057d200b56738415f4642e59ce0257cf71dd6c3a3610605195 else 0x9ce1057cf71216739ae1070c7759ce1057d1e0b96b3841302ac7759cde157cd51b96c3a36106051e5a9e1057cab1dd6738415f2988b5a360254cc11dd6c3a36105f52359ce104d8d51dd67384175304775))) else (if i < 43 then (if i < 41 then 0x841e157ca61216738415f3547859ce1b57cd51dd6738c5813547759ce1057cc918d6737f55f2f47759ce1057cf11dd6738415f3547459cdf357cd51356c39ce6b70c775b0e8d9059d3556738795f354775 else (if i < 42 then 0x9ce1057cd51016737e15f2ac7759ce6b841973556737cd5f3047759ce1057d053555e157cd51dc225b0de157ca61216738414a354775a020257cc11dd6c3a3648684d559ce1057d073556737cd4b354775 else 0xb0e8d99dd91dd6738415f3549459ce1057d230b96c3a36106052359ce104a0d51dd673809302987759cde557cd51d16737855f45c7759cdef57cd51dd67378573354775afde5528d51dd6c39ce6b65cd55)) else (if i < 44 then 0x9ce104c0a61215e157d30298775b0e8d9215f45969f8414b3544d59ce10544c71dd6c3a365657d0d59ce104d4bb1dd673809303544859ce0257cbd1dd6c3a36106012359ce1057d141dd6737955f41cd55 else (if i < 45 then 0x9ce2557cd51dd6737a15f354775b0e8d7958148d6c3a361069cf75b0e8d97d354354009ce537647749ce1057d0d2ad67381d5f3547759cdf84d4d51dd6b084135354775a7e1057cc11356c37955f2984d5 else 0xb0e8d9adc3135673841433547759ce1052cd52016737855f2ac4859ce5d57ca11dd6739a12a3547759ce1070d9757d6738415f47c2d59ce0b57cd51dd6738415f2f44857855f4c0d51216737955f48c2e5)))))) else (if i < 69 then (if i < 57 then (if i < 51 then (if i < 48 then (if i < 47 then 0x9cde14d4a61dd673841a73543359ce0257cc71dd6c37e1472ac775a361052d1e0b96738415f3546459ce1057cc11596738415f304805a360957cc718d6738415f2ac4d59ce10500b61dd67384149354775 else 0x9ce1057cc71216c3a3651764775b0e8d841d124d6c38fd5f2ac455a361052cc918d67384135434d559cde15a0d51dd6738415f2707759ce107644d0e56c3795cf1dc3959ce1057ce41dd6738414b2ac775) else (if i < 49 then 0x9ce1057cca1dd673841472987759ce1057cd51d96737955f2ac4d59ce10605230b96739215f3544659cde14d4d5121680841533047759ce0251cd51dd67378557354775785a257cd51dd6737855f3a4775 else (if i < 50 then 0x9ce106415f3556738095f42cd55b0e8d9ad973056737954b2ac7759ce1058cd51dd67384166354775b0de54d4d517d6c3841352f44d59ce104d4d513568d8095c3487759ce10764770d967378530354775 else 0xb0e3f4d4d511568d809303546359ce1057cce1dd68d8414b450775b0e8d9ae541dd6737f15f3545d5aaa1057ca618d67394dd93547759ce1057ce31dd6c3a36027649959ce10574d51dd67384147354485))) else (if i < 54 then (if i < 52 then 0x9ce0957cd51356739a12d3547759ce2f57cd51356c3a3647684d559cde54d4d51356c3a366097c7759ce104c0b81dd68d84130298635b0e1051cab1356c3795573347759ce1057d1a0b967384135304775 else (if i < 53 then 0x9ce2857cd51dd67398210354775b0e8d905a13556738254b3547759cde157cd51a56738c530354775b0e1063d5f2ad67379535304775b0e8d97dcb1dd67384130354585b0e8d921a145d6808415f3044a5 else 0x9ce1057cb11dd6b3841303547759ce1057cd5215673841bd4d47759ce6b70d5f1dd6738615f3547759ce0257ca61216738413e3546359ce1057d063556c3a364757d1659ce0957cc11dd6738416f354775)) else (if i < 55 then 0x9ce6b65d5f355673841673547759cde1544d51dd673841cb3547759ce1057cbb1dd6c3a366970c775b0e8d841ad3d1673841543547759ce10764770ed6c3a36106b4f65a85e157cd51216c39892d3544d5 else (if i < 56 then 0x9cde1570d51dd6c3a365d57d075b0e8d97d5f4356737e15f3547759cde1558d51dd6739218d57cd55acde54c0d51dd68d78530304775b0e8d841a53dd6738419357cd55a9de557cd51dd6737d95f354775 else 0x9cde557cbb1dd673785453547759ce1357cd51dd6c3a366965cd559cde157ceb1dd68d809513546359ce0f57cd51dd6c3a36107509959ce10500ab1dd6c37cd5f2e04d59ce104d4cc1dd6739115f354775)))) else (if i < 63 then (if i < 60 then (if i < 58 then 0x9ce1057d0d3556c39ce106b4f759ce1051cd51696737855f298775b0de557cd52456b07955f354775a3602570d518d673841a53543359ce1157cd51dd673841303547459ce1075d5f1dd6738f15f354635 else (if i < 59 then 0xa360257ca618d6738413048c2e5b0e8d841d32656c3a3643684d559cde157cd51216738415f3bc7759ce106f95f1dd6738f95f3544559ce1057ca81dd6c3a363b6b4d55b0e104c0a613567384134354775 else 0x9cde557d0d3556bf7955f3544d59ce10514d5161673841c8354775b0e8d8c15f48d6c37855f2ac4d59cdf757cab1dd6b1841353544d59ce1057cd51356738d15f3547759ce0257cb81dd6738415f3246b5)) else (if i < 61 then 0xb0e8d8f1a83556738e15f3547759ce1f57cd51dd6738415f2e04859ce4857cd510d6c3a36106a8f759cddc57cd51dd6738695f3547759cde54d0d51dd6737cd423547759ce1052cd51dd6737f15f2ac775 else (if i < 62 then 0x9ce106b4d50c56c3a364357d1659ce0b4c0d51dd6738414b3546f5afde552cd51dd67c8415f3546359ce254c0d51dd6b1841353047759ce0257cd51616c3a36587247759ce1057cc11dd6738417d3544d5 else 0x9ce104d4ab18d6c3785353544d59ce664b0d51dd6d77855f3544d59cdf74d4d51dd673841302ac4d59cde152cd518d6738415f3046f5afde557cc11dd6738c55f2987759cde557cd51356738415f298585))) else (if i < 66 then (if i < 64 then 0x9ce1057cb618d6d77854b3547759ce105c8d51dd6737955f3047759cdfc4d4d51dd69f841423544d59ce3157cd51216739215f2ac4559ce106a8d50cd6738419e3547759cde157cc118d6737954b354775 else (if i < 65 then 0x9ce10570d51d16738915f3544d5a35e152ca61dd6c3a365e7347759ce106f55f1dd6738415f3788059ce5f57d0d28d67378553354775b5de157cc11dd6a88415f2ac5659ce104ccab1dd6738414b3044d5 else 0x9ce2452cd51dd673841a03547759ce5f57ca3135673841d92647759ce5257cd51dd6828414b3547759ce1057caf1dd6c3a363c6b4ab59ce10604d513567384135334775b0e104d4b8135673841d91dc3a5)) else (if i < 67 then 0xa35e157cc11216738915f304775a361052cc91ad6b2841303547759ce0b57cd51a5673841904c0d55a01e357cc11dd67392135354455a0e1052cd51356c3a3666654d559ce105d4d518d68d7854b354485 else (if i < 68 then 0x9ce10600c11dd6738415f3a8775b0e8d8a55f48d6b17ed353547759ce1057ca61d16739655f28c7759ce10508ab1dd6737ed5f3547759cde56f55f1dd67397d4b28c7759ce10604c11dd6738095f354745 else 0x9ce104d4d21dd6738415f3b8775b0e8d909a13556738415f3307759ce5357cd513568d9ce107649959ce10744770e5673841ad304335a0e1052cc11dd6c3a364857d1359ce02528d51dd67392d5f354775))))) else (if i < 81 then (if i < 75 then (if i < 72 then (if i < 70 then 0x9ce0257d230b967385d5f3548059ce104d4de1dd6c3a365f57d215b0e8d8098148d6738414b3546e5a7e1057cd512167394d4b3547759cdf357cd518d6738415f420d55aa2104d4ab1dd6737855f3545a5 else (if i < 71 then 0x9ce2557ceb1dd6c37f5353545f59cde557ccc1dd6a97855f3547759ce1057cd52296c3a363f684d559ce106595f3556737855f3549959ce10748770d96738415f3046e59ce5357cc11dd673841d01dc395 else 0x9cdf157cd518d6738415f45c4d59cde157cf71dd673841733544d59ce4057cd51156d77855f3307759ce10500d51dd68d8419e3047759ce1757cab1dd6c3a36105e52359ce1057cd61dd6737815f354775)) else (if i < 73 then 0x9ce0257cab1356738b95f3547759ce104c0bb1dd6738414b45c7759ce106b55f3dd673841463547759ce0b57ca61dd6738415f484d559ce2557ca61dd6738415f3cc4d59cde157cd522d6739795f288775 else (if i < 74 then 0x9ce0252cab1dd67385d35354775a360252cd51d16739055f3544359cdf84c0d51dd67382d5f3544859ce1057d1b0b1673795403547759ce2557cd5121673841d31dc3759ce1056cd51dd67384173304775 else 0x9cdf757cd51dd6c3a36106b1235b0e8d9adc318d67394e10764775b0e8d959cd1dd6c3a365d57d0d5b0e8d949d51dd68d8095f304745a260257cd51d168d9654b28c775b0e8d9215f44568d82d5f304695))) else (if i < 78 then (if i < 76 then 0x9ce104d4a61354009ce107649949ce10734ab1dd673785302987759cdfc57cd51dd673809353544d59ce1052cab1216738414b3545b5b0e7394dd91dd6738415f2ac6359ce1057cd51f96c3a364857d155 else (if i < 77 then 0x9ce1057d1c0b9673785303544859cde157cbd1dd673841683544d59ce10684ab1dd673841a63543059ce1057ccc1b9673841d918c3959ce104c10d3556738e95f3544d59ce2c57cd51dd67384144354775 else 0x9ce105d0d51dd6738419d3547759ce107095f1dd67b8414b354775b0e8d84181481673841bc57c7759cde557cab18d673809353047759ce1057ccd1dd673841573544d59ce1057ce913567379135354775)) else (if i < 79 then 0xb0e8d841804816739215f3544559ce105a0c11dd6738415f3346f59ce1052ce91dd6bf7955f3347759ce104d4d518d6c3a361068cf759ce10690d50c16738415f4802e59ce104c0d51356738415f354975 else (if i < 80 then 0xb0de557cb8135673841303047759ce104ccd51dd6c3a36527647759ce0b54cd51dd673841353044859ce0d57cd5135673841573047759ce1057cd52556c3795352ac775a3610544c718d68d8097e354775 else 0x9ce1057cd21dd673795353546359ce1068cd50cd6c3a363c6b4d55b0e8d9055f44d673795303544d5b0e8d841a93dd6737959d3547759cde157cc71dd6738354b354775a36026a0d50cd6737955f334775)))) else (if i < 87 then (if i < 84 then (if i < 82 then 0xace104c0a61dd6c3a36537644d59ce10764d52656738415f418a65b0e8d92dd91dd6a88415f2ac775ace024c0d51dd6738415f3549659ce6b97dd91dd673841a63543359ce0d57cc11dd6738415f2a8775 else (if i < 83 then 0x9ce0257cbb1dd673841d61dc3959ce106a4d50cd673841423547759ce10690d50cd67395d5f2807759cde54c0c11dd68d8095f31c6359cde151cd51dd683841303547759ce1057cde1dd6738255f354635 else 0xaa1e557cab1dd6738415f30c7759ce1057ce51dd6737f95f3547759ce694acd51dd6739415f3547759cde557caa1dd6737955f3487759cdff57cd51dd6b3841303544859ce105c4d51dd6738415f48c2c5)) else (if i < 85 then 0x9cde5508d51dd673841c34d47759ce1057cc11a56738415f2ec4859ce0457cd51dd6737e15f298775a35e14c0d518d6737955f3787759ce1065d5f2ad6738414b354695a362c52cd51dd6c3a366b70d975 else (if i < 86 then 0x9ce1057cd51a9673921a13547759cdf857cd5121673841513544d59ce1057d1f0b96737f55f3544d5b0e8d8417b48d6c3a36106051f5a861052cd51216c3a36646f47759ce1057cba1dd6c39593528c775 else 0x9ce105e0d51dd67385d5f3547759ce4f57cd51dd6737695f3547759ce3057cc11dd6737f54b3547759ce10558d51356c3a36106011f59ce1057ca71dd6c3a365174c775b0e8d841d94856a18415f304485))) else (if i < 90 then (if i < 88 then 0x9ce10544c11dd6738418148c7759ce1065d353556737f55f3047759ce0257d0d3556738415f3c0775b0e8d841d525d6738419552cd559ce1057d230d16c37e15f2ac4d59ce10570d513567384130330775 else (if i < 89 then 0x9ce10570c11dd6738414b3ac775a360d52cc11dd673841563047759cde157ca612168d9ce48684d559ce1057cbf1dd6738415f3507759ce10514d51356738415f434a659ce1057ceb13568d82d53304775 else 0x9ce0252cd51dd68d9ce106052359ce104a4d51dd67391d5f3544559ce10514c11dd68d8254b3546359ce1057ca6135673841523547759ce104d4c91dd6c3a365f7347759ce1057cab24d6738095f3544d5)) else (if i < 91 then 0x9ce1057cab17d6739215f45c4559ce5f57ca51dd67394dd957c7759ce0257cc11dd6737915f3547759ce1052ca61dd68d8255f3046359ce105f0d51dd68082d5f304775a7a1057cd5135673841c8298775 else (if i < 92 then 0x9ce1057cc11216c3a3610764975b0e8d8c53548d673841cd3547759ce4157cd51156c38413543c7759ce104d4d524d6737955f2984d59ce1052cd51216b1841353546359ce1057cd518d6c3a365f728775 else 0xb0e8d841d92556c37955f2ac6f59ce104e0d51dd6b1841352e47759ce1057cf41dd673841a13547759cde552ca61dd6738415f2e47759ce1073c770e56bf7955f3546359ce1057cf61dd68d8414b304695))))))) else (if i < 140 then (if i < 116 then (if i < 104 then (if i < 98 then (if i < 95 then (if i < 94 then 0xb5de157cd518d673841302ac6359cde5734d51dd6c3785303544d5b0e8d995c31dd673841ca354775b0e104d4bd17d673841353545f59cdf74c0d51dd6737954b3544859ce1057cd52316737955f354635 else 0x9ce1057d101dd67384156330775b0e8d841d92596c3a363157d1b59ce02680d51dd673795a13547759cdfc4c0d51dd67384169354775b0de552cab1356738415f370775a360257cd21d16737955f304485) else (if i < 96 then 0xb0de54d4d51bd673841573347759cdf857cd51696738414b3046359ce1057cbc1dd6c3a366b64cd559ce107015f1dd6737855f2e0775a26024d0d51dd68d7855f2986359ce1057d230ad6738415f458775 else (if i < 97 then 0x9ce2457cd518d6898095f3544d59ce1057cd50f967384130334775b0e8d995973556988415f3544d5a7e104f8d513563e8413035477500273921a1355273841533544d59ce5f57ca21dd6a184140354485 else 0x9ce484c0d511567397d5f28c6359cde157cd51616737c95f3544d59ce3b57cd51dd6c3a366b75c7759ce0257ccc1dd6837914b3547759ce10604d518d6739ad2d3544d59ce106f1301dd6738415f2ac6b5))) else (if i < 101 then (if i < 99 then 0x9ce5a57ca31dd6739395f3547759ce104c8d51356838414b3546359ce1054cc11dd67384180354635002738418148d2c3a363057d205a360252cc11dd6898094b3547759ce1057cc01dd673841c357c775 else (if i < 100 then 0x9ce4357cd51156aa841352987759f61057cab18d6738415f330485afde557cc01dd6737c94b354775b0de54d4c11356739ad2d304775841ce57cd51216739615f28c775a260257cc11dd67397dcd28c775 else 0x9ce105d4d52356738419757cd559ce4557cd511567394d5f354635b0e8d9215f43d673841303487759ce104d4d51ad6738995f3547759ce105a0de1dd6c3a363157d195a361052cc11216737c95f304775)) else (if i < 102 then 0x9ce10504d51dd6738415f3247759ce1052cd51696618415f298775b0e8d8c55f479673841402987759ce104c0de1dd6c3a366a70c775b0e8d93dd91dd67380940354775b0e8d9213545d673795c357c775 else (if i < 103 then 0x9cde157cd51d16c3a366a65cd559ce10718d51dd67397d5f4347759cde565d5f355673941303547759ce2e57ca61dd6618415f3544859ce1057cc116967384140354485b0e8d9199d35567d84135354635 else 0x9ce1057cc12656738415f4682b59ce10560d51dd6737dd453547759ce2e57cd51216738418148cd559ce106b4d50c96738415f45c6359ce105ccd518d6c37f5352ac7759ce1057cf71356738414b354995)))) else (if i < 110 then (if i < 107 then (if i < 105 then 0xb0e8d94dd11dd68d9ce5f57d0d59ce10685171dd6c3a363157d2359ce1057cd52456738415f3549359ce175a0d51dd6738415f3546759ce3c57cab1dd6738414b3dc7759cde557cc91dd6738417f354775 else (if i < 106 then 0x9ce1057cc122d67d8255f3546359ce10730c11dd6c3a363057d1f5a365957ca318d6c37855f2984d59ce1057cd51496737dd5f2987759ce5f57ca01dd6738414b3548b59ce0257cab18d673841c157c775 else 0x9ca1057cd51dd6738415f3545f5a021057cc11356738415f3544e59cdf757cd51216c3a365f8f55f5b0e8d9adbd1dd6737855f48c2e59ce1057cd52496737f15f2987759ce0a57cd51dd67385d30354775)) else (if i < 108 then 0xb0e8d9a9c11dd6738ad5f354775a021052cc11dd673841d92947759ce024c0d513563e8415f2987759ce3c4d4d51dd6738415f3549859cdfc57cd51216739a52d3547759ce0257ccd1dd6b1841353545f5 else (if i < 109 then 0x9ce4257cd51156738415c348775a0e1052cc91dd6739215f3544759ce105e8d51dd67384135298635b0df3508d51356737a95f3547759ce104c0a61356c3841352ac4859ce024d4d518d6738815f354775 else 0x9ce1057cd51c5673809303047759cde557cd517d6738415f2f44d59ce3d8415f355673841683546359ce1057cd515167b8415f354635b0e8d975cd1dd6738415f3344859ce4857ca61156738415f2b0775))) else (if i < 113 then (if i < 111 then 0x9ce1052cbd1dd673841303546359ce5f6e55f1dd6738415f3687759ce1057cab2356738415f3a0775b0e73841d92656737e1473547759ce1055cd518d6738415f3a46359cde157cab1356737c940354775 else (if i < 112 then 0x9ce0d57cd518d6738415f2ac5d59ce104c0c11216738415f278775b0de54c0ab1dd6a88095f2ac7759ce3f57cd51156738c55f48c2e59cde152cab1dd6c3a36316052359ce0257cd21dd6c3795572ac775 else 0x9ce1057cc713568d8094b2ac6359ce1657cd51dd673809423547759ce1057cd21216c3a364e764775aaa1057ca61dd6104c1183547759ce4857d033556c3a366b658d559ce10724ab1dd6738095f378775)) else (if i < 114 then 0x9ce1052cc71dd6739415f298775ac9e157cd51dd6737859057cd559ce1057cde1214009ce5f57d0d4b0e8d9215f45d673841353548d59ce10508a61dd6738415f3546b59cde54c0d518d673785353544d5 else (if i < 115 then 0x9cde557cd51ad673841352d87759f61057cd518d6738415f3544c59ce104d4d51756aa7955f2987759ce105d4ab1dd673785353047759ce1051cd513567384142354485b0e8d94dd918d69f7cd5f3544d5 else 0x9ce1063d5f35569f7c55f3544d5a3602750770e568d9094b3544559ce10668d51dd68d809353046359ce1051cc11dd6738413e354775b0e4b57cd5135673841ba57c7759ce1057cf21dd6c3841422ac4d5))))) else (if i < 128 then (if i < 122 then (if i < 119 then (if i < 117 then 0x9ce1057d0b30567d7955f3546359cdf357cab1dd6737795f3547759cde557cd51316738c15f3546359fe0257cd51dd6738414f354775b0e8d919a135568d9095f3044559ce1070d301dd67385d5f298775 else (if i < 118 then 0xa921057cab1dd6c3a3610764935a36104c0c118d6c3841352ac5a5acde14c0d51dd673841623547759ce1057cd51f567385d5f354485a360252cd21dd673841513546359cde157d063556737f55f354635 else 0xa0e1052cd51ad673841974c0d559ce10570d518d6738155f354775a360d52cd518d67397d5f434d559ce10558d518d6c3a366470c7759ce0257ca61356898095f2a8775b0e8d841d92456898095f348775)) else (if i < 120 then 0xa7e1057cab1356738f15f3547759cde257cd51356738415f380775b0e8d94dd61dd6738417c2987759ce10514d518d6738415f3544159ce0252ca61dd6737855f2ec7759ce1057ceb18d6c3a366b708775 else (if i < 121 then 0x9ce02734d51dd6c3a36107649859ce1057ca618d6c3a365f57d0a59ce105f0d51216c3a366465cd559ce0252cd5121673841303247759ce0257cd518d67397d5f2907759ce1057d043556737cd35354775 else 0x9ce10684a61dd6739015f3544259ce1057d131dd6c3841992ac7759ce1057cab201673809a13547759ce0d57cc91dd6738415f3547559ce10734a61dd6738095f304485a92104d4d51dd6738414b298485))) else (if i < 125 then (if i < 123 then 0x9ce10684d51216738415f48c3a5b0e8d91d5f45d673841ad3544759cde557ca618d673841ad4b8d55a7e104d4d51356c37955f2ac4859ce10734d51216738415f2c87759cdf957cd51dd6a88415f2ac5a5 else (if i < 124 then 0x9cde157cd513567384135354805b0de54d4a61dd6738095f4587759ce104c0d52496c3a363c6b4f759cde557d131dd673841d957c9959cdeb57cd51dd6c3a365f7247759ce1057d0a3556737855f434d55 else 0x9ce104d4ab1dd6738415f3547b59cde152cd51dd6c379535354485b0e8d97dc51dd673785c8354775b0e8d9055f45d6c38a535354775a3610544c118d673841303545f5b0e8d9ad972ad6738415f3548d5)) else (if i < 126 then 0x9ce1057cb81356c3a365f57d0c59ce10724d51dd6738095f3007759ce0270d5f1dd6a88415f298775b0de555cd51bd680841333047759ce1057cd51756737855f3047759ce3c6b4d50cd6a584130354775 else (if i < 127 then 0xb0e8d841ad3cd68d8095f304635a260257cd518d6738414b2e0775a361052ca618d6738f1ad3547759ce1054cd518d68d8094b354635b0de557ccd1356737955f3548d5b0e8d9115f48d6738415f2d8775 else 0x9cdf257cd518d6738099757cd559cde557cd517567392210684d55b0e8d94dcf1dd68d8354b3247759cde54d4ab1dd673841c53547759ce1070d5f1216739ad2d3546359ce1057d111dd6738415f4602e5)))) else (if i < 134 then (if i < 131 then (if i < 129 then 0x9ce1057cd31dd6738255f2ac7759ce4857cd51096737955f2d87759ce105d4d51dd6738419757ca659ce0c57cd51dd6738c55f3544d59ce1057d151dd6738bd5f2ac775b0e73921a1355673795c9354775 else (if i < 130 then 0x9ce1057cc11616738095f3247759ce1057cd52416738415f37c7759ce3152cd51dd67a8415f3047759ce1057cc61dd6aa841302987759ce1052cd516168d9ce3c6b4d559ce1057d0c3556738415f3548f5 else 0xa021057ca61dd6738415f3244859ce1057d1c0ad6738355f3546b5b0e624b4ab1dd68d841ca3546359cde55d4d51dd6738419c3547759ce3157cc11dd68d8414b428d559ce104c0d51ad6c39ce10605235)) else (if i < 132 then 0x9ce104c0f21dd6738415f354625785ce57cd51dd6c3a365a730775b0e8d90d5f45d6c3a3648664d559ce094d4d51dd6c3a363a6b4d55b0de557cab1696737f55f3545f5b0de5508d51356737cd5f354775 else (if i < 133 then 0x9ce104dcd51dd6738415f3dc6359ce105dcd51dd6738415f3546059ce0857cd51dd6bf7955f354625a35e152cc11dd6998415f2987759ce027055f1dd67384165354775a36107015f18d6737855f330775 else 0xa364e57cd518d6c3a3669644d55aa21051cab1dd6738095f3545f5a361054cc118d6738414b3547459ce10754770e569f8415f3544d59ce1057ca62496737c55f354775a661057cd51216739adc34b4775))) else (if i < 137 then (if i < 135 then 0x9ce1057cd52016a58415f298775b0e8d921a1305673841a73543159ce6b65d2d3556739795f28c7759ce104fcd51dd6c3a366b7007759ce1057cd5195673785403547759ce1057cc11d16738415f2985f5 else (if i < 136 then 0xb0e8d9adc31dd67395d5f28c7759ce1052d230b96738f1303547759ce10520d51dd6c3a3610744995002738f1ad35528d9ce5f734775a021057cc118d68d8094b324775a7de557cd51356738415f354565 else 0x9ce2557cd513569b8415f3544d5b0e8d841a83dd68d8354b3546b59ce104c0a618d6737b55f354775ac6104d4ab1dd6c3841302ac4859ce024c0d518d6738415f2ac7759ce0057cd51dd6739195f354435)) else (if i < 138 then 0xaaa0257ca61dd6738715f3547759ce2552cd51dd6738417d2ac7759ce1057cbd18d673841d91dc3959ce1057cab1bd6bf7955f2ac7759ce0b57cd51356aa841452987759cde557cd52016c3841cf134395 else (if i < 139 then 0xa36024c0a61dd6737955f2ac775b0e8d921ac3556738955f304775b0e8d9ad9735567382d4b3547759cde157cab18d6738495f3547759ce3957cd51dd6104c0a61dc4859f610544d518d6738417e354775 else 0xb0de14d4ab1dd6d77855f2ac775b0e8d9095f45d673841433047759ce104d4d51dd6738414b2ac4d59ce1057ca61ad673841a83543359ce1057cad1dd67382d5f3047759ce10540d51dd6738095f3546b5)))))) else (if i < 163 then (if i < 151 then (if i < 145 then (if i < 142 then (if i < 141 then 0x9ce1057ce71dd673785bc57c775a36104c0a61216737855f3347759ce104d4d51bd6bf795353547759ce1057cd51556738415f4487759cde5764770e568d80930354485aaa1057ca61216c3a363157d205 else 0x9ce486855f3556738415f354495b0de55e4d51dd6c3a366270c7759cde14d4d518d673841303548d59ce1057cc718d67d8095f354635ace104c0bb1dd6c3a365d7247759cde14c0d51356738415f354835) else (if i < 143 then 0x9cde14c0c11dd6d7785353547759ce104c4d51dd6738bd5f3547759cdf757cd51616c3a365a57d0b59ce10604ab1dd6738415e3547759ce2457cab1dd6c3795352f4775b0e8d8fd5f45d67379535354775 else (if i < 144 then 0x9ce106b4ab0cd6c3a366b704775a0e1052cab1dd6738418157d235b0e8d9195f44d673841353044d59ce1051cd518d6738415f3c84859ce0957cd51dd67397e1057d0d5b0e8d9524857d673841303545d5 else 0xb0e8d8bd5f4756c3a36106a8f659ce5b57cd51dd673841352a47750027397dcd1dd2737855f348775b0de551cab1dd6c3a366265cd559ce105b8d51dd673841302d8775a72104c0d51dd6c39ce5f57d0d5))) else (if i < 148 then (if i < 146 then 0xb0e8d8b15f48d67397d3528c775a360257cd218d673785423547759ce644acd51dd673841643547759ce1057cab1b967394d5f2ac7759ce244d4d51dd6737855f3787759ce654b4d51dd6739595f28c775 else (if i < 147 then 0xa36106a0c10cd6739ad8d3547759ce1057cb418d6c3a363157d1f59ce105c0d51dd6738f15f298775ace104c0d5135673841a53543159ce10584d51dd67394dd91dc395a360b52cc11dd68d8094b3546b5 else 0x9ce1057cb01dd673841593547759ce1057cbb135673841353546e59ce4557cd510967394d353547759ce3c57cd5121673841422e0775b0e8d9215f4896c3a365f760775b0e8d9ae3d3556738095f298635)) else (if i < 149 then 0xa861057cb61216737e15f3544d59ce1052cbb1dd6738c55f48c7759cdec57cd51dd6898095f3544c59cdf34c0d51dd40084130298484a361052cc718d6b3841303047759ce1057cd5225673841732ac775 else (if i < 150 then 0x9f6104c8d518d6c3841352984859ce2a57cd51dd6739615f2847759ce1057cd91dd673841353544b59ce10744770dd6738415f2f8775b0e8d8edaa3556738415f3545e5b0e8d841ad3d567397dcd354775 else 0x9cdf857cc11dd6739ae486b4d55a360257ca61216738755f354775b0e8d9655f4356c3a36107589959ce1057ce11dd6c3a365f52d0d59cdf657cc11dd6738415f3ac8d59cdf852cd51dd673841d8354775)))) else (if i < 157 then (if i < 154 then (if i < 152 then 0x9ce1057cd51dd6738415f2988d59cde157ca61356738095f3548d59f20257cd51dd6c3a365f57d0959ce104d5171dd68d9ce3157d2359ce6b6e4d51dd6c3a36366b4d559ce1057d0f1dd6739a92d354775 else (if i < 153 then 0x9ce0257cd51756738415f3546f5afde557cd51dd673809352ac7759cde152ca61dd6738415f2a04d5a36654b4c11dd6738419457cd559ce1057cd515d67384168354805ac6104d4d51dd673841353cc775 else 0x9ce105a0ab1dd6737855f3546359ce0257cb61dd6738417d354775b0e8d8f1a73556738415f2985d59ce1052d0d3556738415f2f45f59ce2d57cd51dd673841303548059ce1057cd21d16c379530298775)) else (if i < 155 then 0x9cde1734d51dd673841572ac775ac5e54d4d51dd6c3795303544859ce1057d093556737955f3547759ce1057cd11dd6104c0d52984859ce1057d0d3056737854b3544859ce4657cd51156bf7955f3546f5 else (if i < 156 then 0x9cde557cd51bd673841d61dc3859cde1684d51dd6739215f354445b5de157cd51dd673841302ac7759ce105d4eb1dd6738414b3544d59cde157cc11216c3a366b63cd559ce106b4d50c1673841352ac485 else 0x9ce1057cb71dd6738355f2ac7759ce1057cb818d673809753547759ce106ed5f1dd6c3a36105f51d5b0e8d841d324d6c3a364866cd559ce1057cc11355e157d183547759ce1057cb612169c8415f354485))) else (if i < 160 then (if i < 158 then 0x9ce4857d171dd6738415f3548459ce105b4d51dd6c3a36376b4d559ce394c0d51dd6738413b3547759ce1052cc11dd6738415f2a47759ce3a4d4d51dd673841752987759ce1057cd52216c3a36106b4f75 else (if i < 159 then 0x9ce3157cd518d67397d5f28c7759cde557cc113567a8415f354635b0e8d96dd91dd673841753544859ce10604d51dd673795302ac7759ce104d4e91dd6738915f3547759ce1057cd514d6737954b3544d5 else 0x9ce5f57d031dd6c3a36106051d59ce0257cd51894009ce3157d234a36739215f45d6737cd5f2987759ce0d4d4d51dd6737954b304775b0e8d795ad3dd673841ad354335a0e1052cd51dd67384180354775)) else (if i < 161 then 0x9cdf357cd512167394d5f3547759ce3c57cf71dd68d8419457cc159cde170d5f1dd6738415f4742e59cde5604d51dd6c3a361073c9959ce10670d51216738415f2ac6959ce1057cc21dd6a8841432ac775 else (if i < 162 then 0xa35e157cc118d6738415f354615b0df357cab13567382530354775b0e8d9219f3556739494b354775a35e152cd518d6a18415f2ac4859cde56b4d50cd673841d21dc395a0de552cd51dd6738415f3546e5 else 0x9cde165d5f355673841512ac7759ce1057cd51656737c95f2d87759cdfb52cd51dd6c3a36106b52259ce1057ccc1356737f55f2ac775b0e8d9615f41d6738416a354775a7e0257cd51356739495f304775))))) else (if i < 175 then (if i < 169 then (if i < 166 then (if i < 164 then 0x9ce10570ab1dd6738414b3307759ce10558ab1dd6b37f130354775a0e1052ca91dd6738415f4387759cde557cd51b96738415f3547f5b0e8d945d11dd67384135354695b0e104d5190b96738415f3544b5 else (if i < 165 then 0xa360257d1e0b9673841452ac7759f61057cc718d6738415f2988059cde157cc91dd67384198354775a86104d4d51216738415f45c775b0e8d841a93d96d77855f3546e59ce105ccd51dd6738095f354805 else 0x9ce0257cab1dd6c3a365f71c7759ce10500d51356c37f5352f47759cdfd4d4d51dd673841ad354345b0de557ca61216738c55f48cd559cdfc57cbb1dd6c37cd353544d59ce10645353556738415f3cc775)) else (if i < 167 then 0x9ce1057cd516d673809d91dc395b0df84d4ab1dd6c384135414d559cde557d171dd673795733547759ce6b4acd51dd67391d5f3544459ce105b0d51dd673841d01dc3659ce1057ccf1dd6c3a363c694d55 else (if i < 168 then 0x9ce10764480e5673841c73547759ce3c841ad3556738415f3545059ce1057c9f1dd6739715f280775002739215f45d273841353ac775ac6104d4d516d673841403047759ce1057cd51c96738415f2ac485 else 0x9ce245ccd51dd6c3a363b6a4d559ce3a57cd51dd6c3a365e7307759ce09544d51dd6738e55f3544859ce104d4a61dd67382d5f3546359ce644b4d51dd6c39ce3c6b4d559ce2557cd518d67380935354775))) else (if i < 172 then (if i < 170 then 0x9ce104d4d5121673841573547759ce1057ce91dd6738415f3207759ce5557ca31dd6737dd5f3544d59cde557cab1216c3a36537547759ce105a0d51dd6738415f48c465a0e1052cd512d6737855f3545f5 else (if i < 171 then 0x9cdf757cc11dd6c3841352ac4d59ce1057cd513d673841573546f5afde555cd51dd6c3785302ac7759ce1057d121216738414b2ac635aa1f657cab1dd673841303547759cdf752cd51dd6737f15f3544d5 else 0xb0e8d999c31dd6738415f3344d5b0e8d8f1aa35567d7895f3546359cde55a0d51dd6738355f3547759ce104c0d51bd6738895f3547759cdfc52cd51dd6a08415f3544859cde54d4a61dd6a87e15f2ac775)) else (if i < 173 then 0x9cde54c0d51dd6c3a36105fd2359ce1054cab1dd6738415f3548259cde14c0d518d673795353544859cde555cd51dd6737955f3a47759ce10674d51356738255f2987759ce3557cd51dd6737f15f304775 else (if i < 174 then 0x78530354771216d778530354775b0de54d4ab1356739ad2d2ac7759ce0957cd51216738414b354975a260257cab1dd6c3841c53544d5a621057cab1dd6738415f3546d59ce4857d173556738414b334775 else 0xa35e14c0a61dd6739215f3044559ce10750770e56738515f3547759ce104d4c118d6c3a366665cd559cdf257cab1dd6c3a3653764775aa9e157ca61dd6739214b3544559ce104c0c11356738415f304975)))) else (if i < 181 then (if i < 178 then (if i < 176 then 0x9ce1052cd21dd6738415f3784d59ce106fd5f1dd68d785303544859ce244c0d51dd6a88415f2ac4d59ce5f9215f48d6738915f3a47759ce1057cd51a567390d5f3544459ce1057cd21356737855f3546b5 else (if i < 177 then 0x9ce10554d51dd673841423544d5b0e8d8ad5f48d6a88414b2ac775b0e7397dcd1dd68d82d5f304635b0e8d8f1ad3056a18415f3544859ce104e4d51dd689809353547759ce5f841cd1dd6c3a364857d145 else 0x9cdfd57cd51dd6739a92c3547759cde557cd51a56c37955f4642e5b0e8d99dad3556738c15f3547759ce1057cab1296738414b3787759cdf24d4d51dd6738419157cd559ce1057cab16967397d3028c775)) else (if i < 179 then 0x9ce107652f1dd673841423047759ce1057cab2656838354b354775aaa1057ca61616738419557cd55ace104c0d518d67384151354775ac5fd4d4d51dd673841d31dc3959ce5d57ca31dd67388d5f354775 else (if i < 180 then 0x9ce106ad5f355673841d92643959ce1057ceb1dd6738415f2ec6359cde56455f3556106bd5f3544859ce104c0d51b96738415c3547759ce534c0d51dd6c3a3666704775a85e557cd512167384156354775 else 0x9ce1057cd81dd6738095f3547759ce1757cd51356737e15f3546359ce0357cd51dd6738416b354775b0e8d9795f42d6738415f2ac8b59cde5544d51dd673841453547759ce1057cc51dd673841353545a5))) else (if i < 184 then (if i < 182 then 0xb0e8d9615f43567384135354995b0e8d97dcd4356737955c354775b0e8d9695f4356c3841302984859ce634a8d51dd6738415f2987759ce1057cd514567379556354775b0e8d9a9953556b180935354775 else (if i < 183 then 0x9ce104c1171dd67379545354775a36654b4d518d6738415f2986f59ce1057cd521d6737955f3ac7759ce6b4a8d51dd6d7785563547759ce0257cd51bd67385d4b354775b0e1051cab169673841733a4775 else 0x9ce3c6b55f355673841353548b59ce1057ced1dd6b1841303547759cde157ca618d67f8415f304775b0e8d97dcd13540078530298774b0de157cab121673841353dc7759ce1057cd512167385d5f304775)) else (if i < 185 then 0x8418357ca61dd69e7955f3547759ce0257cc11356738414b2984d5b0e8d965cd1dd400785303544849ce024c0ab1dd673841993547759ce0252cd51356737955f298775b0e3457cab1dd6738415f2b8775 else (if i < 186 then 0x9ce10538d51dd6c3a36026b4f759ce6b65cd51dd68d9ce6b70c7759cde557cd51216738415f3407759ce2957cd51dd6c3785352987757855f298771216d77855f2987759ce107350d3556738415f3547a5 else 0x2738094b304775))))))))
def level4 (i : Nat) := fld (level4Chunk (i / 12)) 54 (i % 12)

def level5Chunk (i : Nat) : Nat := (if i < 122 then (if i < 61 then (if i < 30 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0xb0e8d8419357cd56b0e8d7d95f354776b0e8d9ad9757cd56002c37955f2ac4d5a36738415f3549969ce1057cd518c2d6b0e738415f3546f6b0e8d841673547769ce1057cd51202b6b0ebf7955f354776b8e737955f3547769ce1057cd522c776 else (if i < 2 then 0xb2a8d8095f3547769ce1057d35354776b0e8d9115f354776002738415f3046359ce1057cd52987769ce107955f354776b0e737855f354636b0e8d7e15f3547769ce0257cd5354776b0e8d9218d57cd56002738414b3546359ce107855f354636 else 0xa36738415f3548b6b0e738414b3544d600273794fc354775b0e8d84d5f354776b5e107855f354776a76738415f354776b0e8d83d5f354776a96738415f3547769ce1057d2d3544d6b0e737955f354776ab27384135354776a36738415f3dc776)) else (if i < 5 then (if i < 4 then 0x273841533547759ce106a15f3547769ce478415f3547769ce1069d5f3544d69ce1057cd5354486b1e738415f354776b62738415f354776b0e8d8455f354776b5ec37855f354776b0e73841302ac776b0e8d841d757c776b0e8d8f15f354636 else 0x2c3795353544d5002739ad2d3547759ce2557cd51dc1b6002898095f3547750021057cd52341b59ce1057d02354776a36598415f354636b0ea38415f2e04d69cde157cd51dc426b0e8d841a53543369ce1052d2d354776b0e738415f3044d6) else (if i < 6 then 0x2738418457c775b0e738414b3047769cde557d35354776b0e8d841473545a69cde557cd52987769cde57955f354776b0e8d7855f298776b62738415f3546f6b62bf7955f3547769ce1057d2d304776b0eac841472ac7769ce688415f354776 else 0xb0e8d7855f354486b0e738915f354776b0e8d8415f3bc776b0e8d8415f2a0776b0e8078d5f354776b36738415f354776b0e8d84134354776aaa73841453547769ce248415f354776002737c95f354775b0e828415f354776b0e8d8415f434d56))) else (if i < 11 then (if i < 9 then (if i < 8 then 0xb0e8c8415f354776b0e8d8415f3246b6b5e73841303547769ce5f8415f28c776aaa738095f3547769ce1057cd518c256a36808415f304776b0e7384181354776b7e8d8095f2ac7769ce418415f354776b0e838415f3544d6b62737955f354776 else 0x9ce1074535354776b0de557cd52ac4d6b0e838414b354776a3673809303547769ce106c95f3544d6b0e7397d5f28c776aaa738415f298776b0e8d8415f3544d6b0e8d8d15f354776b0e8d8095f2e07760027357cd51dc2459ce104c0d51dc486) else (if i < 10 then 0xaaa738415f354486b0e8d7715f354776b0e8d8695f3547769ce106c94b3547769ce106b55f2ac776b0e8d7cd42354776b0e8d8414b354776b0e838415f304776b0e8d7955f434d56a367384130298776b0e628415f3544d6b0e73841ad354336 else 0x9ce538415f3547769ce106c95f3047769ce417955f354776b0e8d8415f304776b0e898415f354776b0e8d8417d3544d69ce106d55f354776b0e8d8e15f354776b0e7d8415f2ac776b0e8d9215f354436002738415f3545a59ce1057cd5304636)) else (if i < 13 then (if i < 12 then 0xb0ea27955f354776b0e738415f3546e6b0e8d7955f3544d6b7e8d80935354776b0e7394d5f354776b0e8d841ad354316a36737855f2ac776002105d4d51dc1b59ce1057cd526c776b0e8d8414b3546f6a367384130354486a36738415f2f4776 else 0x9ce1057cd518c396b0e888415f354776b0e8d7954b354776b0e8d841352ac636b0e8d9992c3547760028d8414b3046359ce1057ca61dc366002738415f354995b7e738415f348776b0e8d8415f3046f6a5a738415f354776a8e7384142354776) else (if i < 14 then 0xb0e7d841353547769ce106b5353547769ce1057cd51dc066002738415f3dc775b0e8d84172354776b0e8d7955f304776b0e897955f3547769ce106115f3547769ce1057cde1dc0b6b0e8d9215f2ac456b0e8d841aa354336b0e8d8419e354776 else 0xb0e8d8415c354746b0e8d8915f3544d69ce4884130354776b0e8d841bd57c776a367378535354776b0e8d8415f378806a36106a15f304776a36738415f31c776b0e8d97d5f434a36b0e788415f354776002738415f3548b5b0e8d8414b3044d6)))) else (if i < 22 then (if i < 18 then (if i < 16 then 0xb0e8d97d5f28c4d6b0e8d841d9264776b0e8d9495f354776a7e8d7cd5f354776abe738415f3547769ce1057cd51342e6b0e8d8415f2bc776b0e738415f45c776b0e8d841813544d6b0e7384173354776b0e8d84135334776b0e8d841d91dc3a6 else (if i < 17 then 0xb0e8d8095f354746b0e8d8915f304776b3a737855f3547769ce1052cd51dc2e6b0e8d82d5f354696b368d8415f304776a3673841473547769ce108095f2ac7769ce438415f354776b0e8d92135354456b0e8d8914b354776b0e8d841a0354776 else 0x9ce6a8414b354776b0e8d841422ac776b0e8d7ed5f3547769ce1057cc11dc2e6b0e8d795bd57c776002808415f3047759ce458415f354776b0e8d97d4b28c776aea738415f354776b46737855f354776b0e8d84181304776b0e738095f2ac776)) else (if i < 20 then (if i < 19 then 0xab2738415f3547769ce1057d5f354776b0e8d841d11dc3960027380930354775b0e8d841ad304336b0e8d92d5f354776b0e8d84180304776b5e73841563547769ce1057d0d354a369ce6b97d5f354776b0e7d8255f354776b0e8d9655f28c776 else 0x9ce1057cd528c4d6a7e8d7c55f3547760027384130298775ad6737855f354776b0e738415f2ac486b0e8d84135348776b0de557cd51dc236a361052cd5304636ac61057d353547769ce1757cd51dc0b6b0e8d8415f330776b0e8d94d5f3544d6) else (if i < 21 then 0x27384130354485b5e738095f354776002738415f2f4775b0e8d8095f48c2e6b0e8d85d5f3548069ce1057cd518c456b0e8d841353787769ce1080935354776b0e8d94d4b354776a86738415f2d87769ce1057cf7354776b0e8d7cd5f354636 else 0xb8e7384130354776b0e8d8419657cd56b0e73841352987769ce1057ca61dc486b5e738415f2987769ce1052cd528c776002737855f2ac775b0e8d94d5f304776b0e7380935354776b7a738415f3547769ce0257cd51dc486b0eb584135354636))) else (if i < 26 then (if i < 24 then (if i < 23 then 0x9ce1057d4b3544d6b0e8d7815f3547769ce10684d51dc456b0e7384168354776a36738095f298776b0e7b8415f3547769ce1057cc128c776ab2737955f354776a8e738415f354636b2e8d8415f31c6369cde557d5f354776b0e8d8415f3548a6 else 0xb0e73841353544869ce1057cd5120486b0e8d841733544d6b0e7384157354776b0e738415f3a4776b5e738415f35448600273841b252cd559ce1057d302ac776b0e8d841403547760021057cab1dc1b5b0e8d85d5f2ac776b0e8d8415f358776) else (if i < 25 then 0xb0e8d8415f3cc4d69ce107655f48c7769ce1052d4b354776b0e7384130354776a36738095f354486b0e8d9795f2887769ce637855f35477600273841b257cc1500273841b557cd559ce1084130354776b0e8d8415f45c4d6002738418657c635 else 0x9ce1057cd518c0b69ce107455f3547769ce6b7855f354776b0e8d8414b45c776b0e8d841ad57cf76b7e738415f3546369ce668095f354776b0e8d84146354776a36738415f298486b62c37855f354776a7e8d8415f2ac776b0e8d8415f484d56)) else (if i < 28 then (if i < 27 then 0xb0e818415f354776b0e8d841d31dc376b0e8d8415b354776b0e738355f354776b0e8d84173304776b0e8d8095f2ac4d6ace738415f2ec7760027378535354775002738415f31c7759ce108355f3547769ce1057d4b304776a021057cd5304776 else 0x9ce104d5303547769ce1057cd51341b6002104d4d51dc1b5b0e8d8094b2ac776b0e8d85d353547769ce104c0d52987769ce1079530354776b0e8d9055f3544369ce106055f3547769cde157cd51dc336b76738415f354776b0e8d8415f46c2c6) else (if i < 29 then 0x9cde157cd51dc7769ce1057d1d3547769ce1057cd518c6369ce106b55f354336a0e1057d4b354776b627384157354776b7e8d8095f35477600273841473547759ce107415f354776b0e7379530354776ac68d8415f2f47760027357cab1dc255 else 0xb0e8d8415f2ac6369ce428415f354776b0e8d8415f3547e69cde157cd52ac776a7e8d84135354776b0e8d7dd5f354776a72738415f3547769ce1052cd51dc1b6b6273841303547769ce1057cd52f47769ce488095f354776b0e8d94e10764776))))) else (if i < 45 then (if i < 37 then (if i < 33 then (if i < 31 then 0xb0e8d8b15f354776b0e7d8415f3547769ce106b55f354776002c3a3610764995b0e8d841cd2ac776b0e8d7f15f3547769ce6884130354776b0e8d809353544d6a52738415f3547769ce1057cc11dc1b6b4e738415f3547769ce488415f298776 else (if i < 32 then 0xa36737855f354776002734d4d51dc255b0e8d841683544d69ce106195f3546369ce1057cd51dc356b0e8d841a12ac776b0e8d841d918c396b2e738415f3544d69ce488415f3544869ce1057d27354776b0e738415f354696b0e8d8e95f3544d6 else 0xb0e8d8419d354776b0e8d841c257c776b0ea18415f354486b2e738414b354776b0e8d7955f2ac6369ce3f8415f354776b0e104d519354776b0e8d80935304776b0e8d8415f334776ad2738415f354776b0e8d841573544d6b0e8d8415f3a44d6)) else (if i < 35 then (if i < 34 then 0x9ce1057cd518c326b0e8d84168304776b0e8d8415f3346f6b0e8d8414b3a47769cde56b55f354776ace738415f3544d6b2e738415f304776b0e8d841353546369ce1057cd531c776b0e8d8415f4802e6b0e8d841303544d6b0e8d8415f354976 else 0xb0e8d8355f3544d69ce1057cd51dc586b0e8d84157304776b0e8d8415f3549569ce5a8095f354776b5a738415f354776b0e737f55f354776b0e7d7955f3547769ce106cd5f354636b0e8d9215f354456002738095f2987759ce107f55f354776) else (if i < 36 then 0x2738095f354485b0e8d7955f334776b0e8d841303047769ce105cd5f354776b268d8415f354636b0e8d84133354776a360257d1e3547769ce1057cd5134196ace738414b354776a36738415f2e0776b0e8d82d53354776b0e7384151354776 else 0xb0e8d8415f348776a86738415f2ac776b0e8d795353546369ce1052cd51dc196b8e738095f354776b0e8d841a3354336b0e738415c354776002738415f298485b0e8d7959d354776b0e8d8354b354776ace738415f304776b0e7384156354776))) else (if i < 41 then (if i < 39 then (if i < 38 then 0xb3a7382d5f3547769ce107655f354636b0e73841453547769ce1057d23354636b0e8d8415f3549669ce1057cc11dc196b0e738415f3ac776b8e738415f298776b0e8d9ae5f764776b0e8d8355f3047760027357cd51dc225b0e8d8415f2a8776 else 0xb8e738415f3544869ce108415f298776b0e738095f354776a6a738415f354776b0e8d8415f378776b0e8d8255f354636a36738c55f3547769ce108095f354776b0e8082d5f354776b0e8d841d93549969ce1062d5f354776a36738415f354586) else (if i < 40 then 0xb0e8d7fd5f354776aa28d8415f354636b0e8d84171354776b0e8d8415f48c2c6a36428414b35477600273808fc354775b0e8d841d61dc396b0e738415f298776b0e8d841a9354336b0e8d841423547760027357cd51dc2359ce1057cfd354776 else 0x9ce6b841d9354776b0e8d8414b354696b0e738415f354486a867384135354776b0e8d8415f30c776b0e8d8415f3947769ce108415f3544869ce1052d2c354776a36428415f304776b0e8d9a52b354776b0e8d7955f34877600273840fc298775)) else (if i < 43 then (if i < 42 then 0x9ce1057ca62987769ce1057cd51dc7469ce107955f298776b0e8d8415f304696b0e8d8115f3547769ce0257d3535477600273840fc3544859ce328415f3547769ce0257cd5298776b0e8d7955f378776b0e8d8419757cab69ce027955f354776 else 0xb22738415f354776b0e8d841513544d6b0e8d8415f47c2e6b62738095f3547769ce105a15f354776b0e8d7f55f3544d6002737855f354775b0e737955f298776b0e8d79542354776b0eb5841353545f69ce1057d35298776b0e8d841c34d4776) else (if i < 44 then 0xb0e8d8c15f304776b0e8d7f54b35477600273840f9354775b0e737955f3544869ce1057d353544869ce1057d573547769ce1057cd52984869ce1057cfc2ac776b62738415f298776b0e8d8415f3546a69ce107955f354486b0e8d921a1354776 else 0xb0e107955f2ac4d6a36738415f354746b0e8d8419552cd56b0e8d8415f48c346b0e8d8415c3544d6ab273841303547769ce1057d303547760021057cd51dc1b5afe8d8414a354776b0e8d85d5f354776b0e8d93d5f354776b0e8d7695f354776)))) else (if i < 53 then (if i < 49 then (if i < 47 then (if i < 46 then 0x9ce1057d231dc2e69ce107595f354776b0e8d84151304776b0e8d8418148c7769ce1057d2d354636b0ea38414b3544d6b0e1057d352ac4d6b0e8d841974d4d56b62738415f354486b0e8d7f55f304776b0e8d8095f434d569ce738415f2ac776 else 0xb0e8d8415c304776b0e898415c3547769ce1057cd5268776b0e738415f3046369ce104d4d51dc316b0ea38415f3044d6a7e8d8415f35477600273841b26195f5b0e8d8415f2fc776b0e8d8415f350776b0e738414b354636002738415f2e0775) else (if i < 48 then 0xb0e837915f354776b0e8d91d5f3544569ce105d95f3547769cde557d30354776001e557cd51dc1b5b0e8d8415f2984d69ce104d4fc354776b0e8d84152354776b0e8d841353247769ce5e8415f354776b0e8d8415f2ac936b0e8d8095f3544d6 else 0x2738c55f3547759ce7384135354776b0e10795353544d69ce6b8412d354776a26108095f354776a36738415f48c2e6b0e73841533547760027357cd51dc255002738415f354585b0e8d8094b354776b0e8d84129354776b3a8d82d5f304776)) else (if i < 51 then (if i < 50 then 0xb0e8d97d5f2947769ce1057cd51dc1a69ce107c95f354776b0e838415f3546369ce578415f354776b0e739ad2d354776b0e8d94dd957c776b0e8d8095f304776b0e898095f354776a7e8d7955f354776b0e8d7915f354776b0e8d8414b298776 else 0xb0e8d9055f354456b0e8d84135354936a82738415f354776b0e8d8414b3544869ce106c95f3546369ce1061d5f304776b0e737c95f354776b0e8d8415f3546369ce1057cab1dc4d69cde157cd5354776b0e8d8415f2ac5f6b0e8d9215f45c456) else (if i < 52 then 0xb0e8d841a1354776b0e8d8415f2e4776a367382d5f354776b0e8d841cf1dc396a36738955f354776b0e8d8415f3d8776a6e8d8415f3547769ce1057cd51dc166b0e8d8415f3044869ce1057cd51dc2469ce106d55f354486b0e8d841cd354776 else 0xb0e8d841353545f69ce1070d5f4b47769ce1057cd5294776b228d8415f304776b0e8d7955f354636b72738415f3547769ce1057cd52e0776a36738415f2ac4d69ce10741303547769ce106e15f354776b0de557d19354776b0e8d8415f3d0776))) else (if i < 57 then (if i < 55 then (if i < 54 then 0x9ce106b530354776b0e8d795a1354776b0e8d841693547769ce1057d24354776b0e8d8415f370776a36738414b2ac7769ce1057cd51dc1169ce1057d51354776b0e8d795cd354776b0e8d841ca3547769ce104d4d51dc4d6b0e738415f3545a6 else 0x9ce106a54b354776b0e738415f354996b0e8d841c057c776b0eac7e15f2ac7769ce1057d5c3547769ce438095f354776aaa737855f354776b0e8d8415f458776ace737f15f354776002738415f3547459ce1057d56354776b0e8d809a0354776) else (if i < 56 then 0xa3673841353544d600273840fb3547759ce1057d45354776002c3a3648684d559ce1065d5f4b4d56b0e8d841533544d6a367378530354776b0e8d97d5f288776b0e8d84157334776b0e8d7e15f3545a6b0e8d8414b304636b0e8d8415f2f0776 else 0x9ce1057cd518c2e6b0e8d841813546369ce1073d5f354776b0e8d9ad2d3544d6b0e738415f3dc776b0e8d8415f2ac6b69ce1057d1f304776a86738415f354776b0e8d8915f354636af28d8415f354776b0e8d8415f3543e6b0e8a8415f354776)) else (if i < 59 then (if i < 58 then 0x2c3a3610605235b0e8d8415f300776ab2738415f2987769ce1057d5f298776b0e8d841c357c776b0e8d97d5f28c636b0e738415f3548b6b0e8d8ed5f3547769ce5f8415f2ac776ab2738095f3547769ce1057cd51dc1069ce0257d5f354776 else 0xb0e808415f3544d6b0e8d9ad2d304776b0e8d9615f28c776b0e8d97dcd28c776b0e8d9695f28c776b3a738415f3544d6b0e8d9395f354776a367384135304776002738415f48c2e59ce458415f354486b0e8d84153304776b0e8d84180354636) else (if i < 60 then 0x9ce106bd5f3547769ce1057cd51dc206b3a738414b3547769ce568415f354776b0e8d90d5f354456a86737955f3547769ce1057cd5288776ab2738415f3544869ce1057d5f354486b6e738415f3547769ce1057cd51dc0a6b46738415f3544d6 else 0x9ce1057cd51dc466b0e8d795c357c776b0eac8415f2ac4d6b0e8d8419757cd56b3a738415f304776b0e8d94d5f354636b0e8d841353546b6aaa738415f354586b46738414b354776b0e8d8995f354776b0e808414b354776b0e8d84168378776)))))) else (if i < 91 then (if i < 76 then (if i < 68 then (if i < 64 then (if i < 62 then 0xb0eac8414b2ac776b0e838415f3247769ce1057cd51dc3169ce10809303547769ce1057cd528c6360027382d5f3547759ce5f84135354776002738955f354775002738418357c775b46738415f304776b0e808415f304776ad6738415f3544d6 else (if i < 63 then 0xad6738415f3047769ce69841353547769ce1057cfc354776b0e8d8415f324776a9e8d8415f354776b0e7384130298776002738415f2ac4d5b0e8d8414b3545a6afe738415f3547769ce10734d528c776ad6738414b354776b0e7380930354776 else 0xb0e7384130354486b0e738415f2f47769ce738415f3547769ce1057d4b354636002738414b2ac7759ce107855f2ac776b0e8d97d5f434776b0e8d7959757cd56b0e8d8415f3045a6b7e8d8095c354776b0e8d84141354776ace8d84130354776)) else (if i < 66 then (if i < 65 then 0x9ce1057d233542e6b0e8d8415f304996b0e9d8415f3544d6b0e8d8418148cd56a36738415f2ec776b0e8d841ad354326b0e8d8415f45c636b0e8d84173354636b0e8d8415f3dc4d6b0e8d8414b354996b0e737855f2ac776b0e7d84151354776 else 0xb0e8d8415f354936b0e8d85d683547769ce6b8415f3544d60027378530354775b0e8d8415f354676b0e8d8f15f2ac776b0e8d8414b3dc7769cde557cfc354776b068d8415f354776b0e8d7955f3247769ce407855f354776b0e8d8417f354776) else (if i < 67 then 0x9ce6b57d2d3547769ce1057cd51343369ce737955f354776b0e8d8414b3548b6b0e8d8095f2ac636b0e8d841c157c7769ce1057d53354776b0e8d841a145c776b0e8d8415f35491600273841353544d5a36737e15f354776ac28d8415f354776 else 0xb0e7d8095f3547769ce106c15f3547769ce104c1303547769ce1078535354776002104c0d51dc1b5b0e8d8295f3547769ce026b55f354776b0e8d8415f3048b6b0de557d353544d69ce6b8414b354776b0e8d841cc3047769ce1057d0d354776))) else (if i < 72 then (if i < 70 then (if i < 69 then 0x27384135304775b3a8d8415f3044d6b0e8d8415f3544e6b0e73785353547769ce6b8415f3047769cde157cd51dc4869ce106b55f298776b468d8414b3544d69ce1057cd518c1b6b5e737855f354776b0e738415f31c7769ce1060d5f354776 else 0x9ce1057cc11dc336a36737855f298776b0e8d9a52d354776b0e8d8095f3347769ce1057cab1dc2569ce106a95f3546369ce1057cd51dc4d6b0e8d8415f3545f69ce1057cd52747769ce1052cd51dc336b62c37955f3544d69ce5f9215f354776) else (if i < 71 then 0xb468d8414b304776b0e8d8ad5f354776a36738415f434d56afe8d8415f3544d6b0e8d841d9294776b62c37954b354776af68d8415f354776b3a8d8414b304776b0e8d8f1353547769ce106b55f354486b0e8d8415f3549869ce1057cd52ac4d6 else 0xa36737855f3544869ce1052cd52ac776b0eab8415f2ac776b62c37955f3047769ce1057cd51342c6b0e8d7a95f3547769ce1057cd52807769ce1052cd51dc776b0e8d809353546369ce1052cd51dc386b0e8d8815f354776b0e7384147354776)) else (if i < 74 then (if i < 73 then 0x9ce1057cc12ac776b0e8d841683546369ce106355f354776afe8d8414b354776b2e738415f354636002734c0d51dc255b0e8d8415f2b07769ce1057cc11dc776b0e8d9095f354456b0e8d8415c3487769ce1057cc11dc386b0e8d9215f354476 else 0xb0e8d84157354636b0e8d8415f3a4636afe8d8415f304776b0e8d8415f354716a8a738415f3547769cde557cd51dc4d6b0e8d7955f3545f6b0e8d8415f2f44d6ab2738415f3545a6a36738415f3544d6b0e8d8f61057cd56b4a738415f354776) else (if i < 75 then 0xb0e8d8414b2f4776a36738414b354776002b384130354775b0e8d84130354636b0e8d97db957c77600273841af57cd559ce104d4d51dc2569ce106295f354776b0e8d8415f368776b0ea3841423544d6b0e8d8415f3a0776b0e8d7e147354776 else 0xb0e8d8355f3546369cde157cd51dc2869ce1057cab1dc396b0e8d8415f278776b7e8d7855f354776a36738415f304776a26738415f354776b0e8d8fd5f354456a361057d4b304636b0e8d8c55f48c2e6ace738415f354636b0e8d8095f348776)))) else (if i < 83 then (if i < 79 then (if i < 77 then 0x9ce104d4d5304776b0eb384135354776b0e838415f3546b69ce108095f298776002738415f2ec775b0e8d9215f40cd569ce1057cd518c1969ce487855f354776b0e8d841c92ac776a36737955f3544d6b0e8d8095f3787769ce028095f354776 else (if i < 78 then 0x9ce108095f354486002c3a365f57d0d5002737e15f3547759ce48841ad57cd56a36737954b354776b0e8d8415f3546b6b2e8d8415f354486b0e8d8415f31c4d6b0e8d8595f354776b0e738095f298776b0e8d80942354776a8e737cd5f354776 else 0xa366e8415f3547769ce1057cd51dc1869ce104d4d51dc396b0e8d841473544d69ce1057cd51dc226b0e738415f298486b0e738095f354486b0e8d8414b31c776a36737955f304776a26737955f3547769ce5f8415f3547769ce106e55f354776)) else (if i < 81 then (if i < 80 then 0xa867384130354776b0ea38415f354486a7e738415f354636002737855f298775b0e7d841323547769ce1057cd51dc4369ce104d52b3547760021057ceb1dc1b5a8e9f8415f3544d6b0e8d7955f3546b69ce698415f354776b0e8d8415f3544c6 else 0xb0e8d8418f57cd5600273841b057cd559ce0257d303547760020257cd51dc1b5b2e8d8414b354636002738415f434d559ce1057cd5238776b0e8d84147304776b0e8d8413e354776ac6738415f3547769ce1057cd51dc2369ce5f7955f354776) else (if i < 82 then 0x9ce1057cd52ec776b2a738415f354776b8e737855f354776b0e8d7cd5f2ac776b0e8d7795f354776b0e8d8c15f354636b2e8d8415f304636a4a8d8415f354776b0e8d8414f3547769ce1057d302987760021057ca61dc1b5002737855f354485 else 0xb0e8d8415f3547d6a36738415f3307760021057cd51201b5b0eb5841352ac776b0e8d841513546369cde557cd51dc4369ce1057cab1dc456b0e8d7f55f354636b0e8d8415f42cc16002738415f3544d5a7e8d8095f3547769ce5d8415f2ac776))) else (if i < 87 then (if i < 85 then (if i < 84 then 0xb0e8084133354776b0e8d8415c354636b0e737855f354776b0e8d8155f3547769ce106315f354776a8e738415f2ac776b0e8d97d5f434d56002738414b3547759ce107855f3547769ce106d95f3547769ce1057cd51dc2d69ce1057d30354486 else 0xb0e8d97d5f2907769ce104d4d51dc4569ce1057d1b2ac776b0e8d7cd35354776b0e8d8f15f354776002737955f3544d5b0e8d8415f3544160027357ca61dc2559ce1057d2035463600273784fc354775002738415f3047759ce1057cd52000b6) else (if i < 86 then 0xb0e8d8415f2986369cde157cd5298776a3673841403547760027357cd5120255002737954b3547759cde57855f354776a36027515f3547769ce1057cab1dc0b6b7e738415f2ac7769ce104c0fc354776002103f0d51dc1b5b0e8d8095f354636 else 0xac68d8415f3544d6b468d84130354776b0e8d8355f324776b0e8d8415f3547569ce7384130354776a8e7384135354776002737955f304775b0e8d809cd354776b0e738415f2e07769ce1057cd51dc3d69ce106895f3547769cde157d35354776)) else (if i < 89 then (if i < 88 then 0xb0e1068d5f2ac7769ce1057cd53544d6b0e7a8415f3547769ce1057cd51dc256ab273841473547769ce1057d4735477600273841864d4775b0e8d8415f44c776b62737855f354776b0e8d8415f2ac806b52738415f354776b0e8d809a1354776 else 0xac68d8415f304776002733f0d51dc255b7e7384135354776b0e8d8415f48c3a69ce1057cd5290776b0e8d841ad354476b0e738c55f354776b0e738415f354586b0e8d841ad4b8d56ac68d8414b3547769ce1057cab1dc6369ce318415f354776) else (if i < 90 then 0xb62c37955f334776002738418957c775b0e8d8095f4587769ce558415f3547769ce1057cd5304776b0e8d7955f44c776b0e8d841d957c9969ce468415f3547769ce1052cd5354776b228d8415f354636b0e8d8415f428d569ce104d4d51dc0b6 else 0x9ce104d4d51dc636afe8d8415f334776002738415f330775a36737f15f3547769ce104c0d51dc4d6b0e8d8415f3548d6a36738415f2ac6369ce106195f2ac776b0e8d7855f3544d69cde557cd51dc256b0e8d84135354806a36737dd5f354776))))) else (if i < 106 then (if i < 98 then (if i < 94 then (if i < 92 then 0xb0e8d8415f3545d69ce1057cd51dc396b0e8d7855f304776b0e8d8f1ad354336b0e8d841352ac776a86738415f298776b0e8d8415f3547b69ce4857cd51dc4569f6738415f354776b0eab7955f354776b0e8d7854b354776a86738095f354776 else (if i < 93 then 0xb0e8d84153354636a3673841303544d69ce106215f2ac7769ce1057d2b354776a86738415f354486b0e8d8415f2d8776a36738415f334776b0e8d8415f2e04d6aaa738415f3544d6b0e8d841c9354776b0e8d809c357c7769cde557cd5304776 else 0xb0e8d841c5354776b0e8d9ad2d354636b0e8d8415f444776a36739215f354456b0e738415f354746b0e8d8414b2e07769ce0257cd5288776aaa738414b354776a367384135354636b0e8d8f1ad354776a46738415f3547769ce1061935354776)) else (if i < 96 then (if i < 95 then 0xac68d7ed5f3547769ce107655f2ac7769ce1057d232ac776b0e8d795c9354776b0e7d8415f31c776b0e8d8099757cd569cde557cd51dc396b428d8095f354776b0e8d92210684d56b0e8d795352ac7760027384140354775aaa738415f304776 else 0xb3a738415f354636b0e8d8415f34c776b0e8d8255f2ac7769cde557d2b354776b0e9a8415f3544d6b0e8d84175354776b0e8d8315f354776b0e8d8c55f3544d6b0e8d8415f454776aa28d8415f354566a367384130304776b0e8d8bd5f2ac776) else (if i < 97 then 0xb0e8d8095f324776b0e8d8415f37c776b0e8d8c54b354776a36738415f348776afe738095f3547769ce278415f354776b0e8d8415f318776b46738415f354636b0e808415f3546369ce106255f354776b0e8d8415f430d56b0e8d8415f3548f6 else 0xad6738415f3546369ce5f84130354776b0eac8415f2ac636a36738415f3787769ce1057cd53307769ce1057cd51dc2a69ce1057cfc2987769ce106dd5f354776b0e8d8c55f304776b0e738415f48c2e6aa28d8415f2ac7769ce0257cfc354776))) else (if i < 102 then (if i < 100 then (if i < 99 then 0xb0e8d7f55f3545f69ce5d8415f354776b0e8d7cd5f3547769ce1057cfc3544869ce10765353547769ce104d5233547769ce738415f298776b3a8d8415f298776a367384142354776b0e8d8355f3546b6b2e7d8415f3546369ce738095f354776 else 0xab2737855f3547769cde157d5f354776b0e738955f354776002738415f2ac6359ce1082d5f354776b0eb584135354776002738418557c775b0e8d8415f3546269ce258415f354776002737dd5f3547759ce1057cd51dc456b0e8d82535354776) else (if i < 101 then 0xb0e738415f2ac4d6b0e8d841773547769ce1057cf9354776b0e8d8215f354776aa28d84135354776a8e738415f354776b3e738415f354776b0e8d809c157c776002737f15f354775b0e8d84165354776b0e7382d5f3547769ce738415f354486 else 0x2738415f334775b0e8d7c55f3547769da738415f3547769ce5357cd51dc3969cde557cd51dc4569ce1057d2d2ac776002738418657c775b0e8d9adc34b4776b0e8d84137354776b0e8d8415f3dc636a86737c95f354776a868d8415f354636)) else (if i < 104 then (if i < 103 then 0x9ce1057cd51dc0b6b7e738415f3547769ce1057cd51dc0d69ce6b8415f3546369ce0257cd51dc4d600273841303544d5b0e8d8095f3545f6b0e738414b2ac776b0e8d8414b354746b0e8d841d51dc3969ce1057d1b354776b0eb579535354776 else 0x2c3795352ac7759ce1078530354776b0e7d7895f354776b0e8d8415f35465600273840ff354775002739215f3544559ce1057ca61dc4d6a8e737955f354776b0e8d8415f304746b0e898415f354746a367385d5f3547760027384135354635) else (if i < 105 then 0x273841303047759ce1057cd5134486b0e8d8415f354566b5e738415f3544d69ce1057ca6280776b0e8d8415f354806b0e7378530354776002737958657c775b0e8d841a7354316b0e8d9ad974b4d56b0e8d9795f28c7769ce1057cd518c336 else 0x9ce1057cd51dc636b7e737955f354776b0e838415f2ac776002c3a363c6b4d559ce104d52d3547769ce106d15f354776a36738095f3544d6b62c37955f354636b3a8d8415f304636002738418857c775b0e73841353544d6b468d8414b354636)))) else (if i < 114 then (if i < 110 then (if i < 108 then (if i < 107 then 0xa36738094b354776002a88415f2ac775b0e8d8415f2ac776b0e8d9195f3544369ce1057cd52ac6369ce106155f3547769ce1052cd51dc486002738415f348775b5e738414b354776a36738415f2984d6b0e8d8414b48c2e69cde557cd51dc0b6 else 0x9ce1057d19354776a36738095f304776b0e8d7955f3548069ce1057cd52341b6a36738414b298776b0e628415f2ac776002738415f378775b0e73841353047769ce106c95f2ac7769ce1057cc11dc486afe8d8415f354636b5e738415f304776) else (if i < 109 then 0xb0e8d8417d2ac776b0e8d8415f2f4636b0de568d5f354776a36738415f354636b46738415f32477600273840fe3547759ce106195f3547760027384142354775b0e8d841d91dc3969ce107555f354776b0e8d8415f2ac6f6b0e8d82d5f3544d6 else 0xa3673841cd3547769ce1057d1e3547769ce104c0d51dc256b0e8d82d4b354776b0e8d8495f3547769ce1057cd53347769ce1057cd51dc146a36738414b354486b0e848415f3547769cde557cd51dc636b0e8d8417e354776b0e8d8715f354776)) else (if i < 112 then (if i < 111 then 0xa3673841a1354776b0e8d84135354776b0e8d8414b2ac4d6b0e8d841a8354336b0e8d8415f2b47769cde16b55f354776b0e8d82d5f304776b0e8d84150354776a36738415f304486b0e8d8095f3546b6b0e8d7955f2ac776b0e8384135354776 else 0xa36737955f3546369ce488415f3544d6b0e8d8415f3545569cde56195f354776aaa737dd5f354776b0e8d795d91dc3969ce5f8415f298776b0de54d4d52ac7769ce106cd5f3547769ce1057cd51dc3269ce106c9353547769ce5f8095f354776) else (if i < 113 then 0x9ce488414b3547769ce1057d2a354776aa2738415f3047769ce5f8415f354486b0e8d8415f31c636b0e8d8415f3548369ce1057cd51dc136b0e8d8415f39c7769ce106215f3547769ce104c0d5304776b0eb384130354776b0e8d841353546f6 else 0xb0e8d841812ac776b0e8d8415e354776b0e738415f2ec776b0e8d8915f2ac776b0e8d795353547760027385d5f354775b0e1073d5f3544d69ce1057cfb3547769ce105d4d51dc1b69ce1057cd5348776b0e8d921a157cd56b0ea18415f3544d6))) else (if i < 118 then (if i < 116 then (if i < 115 then 0xb0e8d97e1057d0d69ce104c0d51dc3969ce107e15f354776aa6738415f3547769ce1057cde354776b0e8d8bd5f3547769ce107655f3547769ce1057cab1dc2e69ce1057d233547769ce1057d171dc4569ce488415f304776aa21057cd52ac776 else 0xa7e8d8415f2d0776002c3a365f734775002738095f3544d5b5e738415f330776b0e8d841ad2ac336ace738415f3545d6afe8d8415f300776b0e8d8418157d236b0e737e15f354776b0e8d841353044d6b0e8d84147354636b0e8d8255f354776) else (if i < 117 then 0xb0e8d9952d354776b0e8d9595f28c776ad6738415f3545f69ce1065d5f354776a3673841c357c7769ce1057cd51dc3f6b0e104d4fa354776b0e8d96d5f354776a36106155f304776b0e568415f3544d6002738415f2984d5aa28d8415f354776 else 0xb468d8414b324776002738095f3047759ce104d4d51dc2e6b0e8d84164354776002738414b2987759ce107855f298776b0e8d94d5f2ac776b0e8d89135354776002738094b3547759cde57655f3547769cde557d233547769ce027855f354776)) else (if i < 120 then (if i < 119 then 0x27357cd51dc265b0e738415f434d56002738415f354635a361052d1e354776b8e738415f3544d69ce1057cec35477600273841b457cd55b0e8d97d3528c7769ce1057cab28c7769ce1057cd518c446b0e737855f298776b0e8d9912b354776 else 0x273841b257cab5002738415f304485b7e8d8095f35474600273841cd354775b0e737855f354486a36738419757cd56b0e8d841a5354316b0e8d84161354776002738414b354485b0e8d94dd91dc3969ce107855f354486aa28d7955f354776) else (if i < 121 then 0x9ce1057d2d354776b0e8d8415935477600273840fc3544d5b0e8d94d353547769ce1057d4b2ac776b0e8d841422e0776b8e738415f304776b0e738415f3544d600273841a1354775b0e8d9ad8d3547769ce108415f3544d6b8e738414b354776 else 0xa361052cfb354776b0e8d7b15f3547769ce108415f3047769ce104d4d528c776b46738415f3546b6b0e738414b3547769ce1069535354776002737955f354635a36738415f324776b0e8d8415f354896b0e8d841732ac7769ce108414b354776))))))) else (if i < 183 then (if i < 152 then (if i < 137 then (if i < 129 then (if i < 125 then (if i < 123 then 0xb0e8d8415f3545e69cde157d303547769ce107955f3544d6001e157cd51dc1b59ce1057ca61dc256b0e8d97dcd354776b0e8d7e15f3544d6b0e738415f3047769ce1069d5f354776b0e8d8c55f48c7769ce0257cd51dc2569ce104c0d51dc456 else (if i < 124 then 0xb0e8d841d8354776b0e8d9615f28477600273841b357cd55b0e8d8415f364776b0e8d841d11dc376a8e738413035477600273841b24d4d55b0e737955f3544d69ce1057cd51dc1f600273840fc3047759ce1057d353544d69ce1057cd52984d6 else 0x9ce1052d35354776b62738415f3544d6ac68d8415f3546369ce1052cd52987769ce1057cd5120256b0e106c15f3544d6b0e8d8415f3847769ce107954b3547769cde557d2d3547769ce10765ad3547769ce1057d1a354776b0e8d7e14b354776)) else (if i < 127 then (if i < 126 then 0xb0e8d9adb93547769ce1057cd51dc5f69ce107955f304776b0e8d8415f43c776b0e8d9a92d3547769ce1057cab1dc1b6b0e8d7e15f304776b0e737954b35477600273841864c0775b0e8d9ae486b4d569ce105a0d51dc0b69ce0257cd5304776 else 0xb7e7384130354776b0e8d841353cc776ac68d8415f2e4776b0e8d8415f354776b62738414b3547769ce1057cd5354636b0e737955f3047769ce1057d353047769ce1057cd51dc056b0e8d8413545c776b0e838415f3547769ce1057cc1298776) else (if i < 128 then 0xb0e8d809352ac7760028d8094b30477500273841c357c7759ce1057cd5304486b62738415f3047769ce1076d5f354776b0e8d8419457cd56b2a8d8415f354636b0e8d841683548069ce106c95f3547769ce104c0d51dc0b69ce658415f354776 else 0xb0e837955f354776b0e8d8417d3547769ce1057ca61dc396b0e8d8414b434d56b0e8d8415f2f45f6b0e8d8b55f354776a36738415f3545f6b0e8d8415f3487469ce577855f3547769ce0257cd51dc396b0e8d8415f3546f6a7e8d8415f2e0776))) else (if i < 133 then (if i < 131 then (if i < 130 then 0xb0e8d8415f424d56b0e8d7955f354776b0e8984134354776b0e8d8415f344776b0e8d8415f434c16b0e8d9195f3544569ce104d4d51dc1b6b0ea28415f3544d6b0e8d841682ac776b0e8d7855f3546360015f354770941b5b2e738415f2ac776 else 0xace1057d30354776b0e8d9215f354446b0e8d841302ac776b0e8d8414b3544d6002738419757cd559ce1057cd5120396b6a738415f3547769cde56c95f354776b0e8d841572ac776b12738415f3547769ce104c0d51dc636b0eaa8415f2ac776) else (if i < 132 then 0xb82738415f354776b0e738415f330776b0e8d8415f2e0636aaa738415f354636b468d8414b3546b6b0e8d841bb57c776b0e838415f2a4776b0e8d8415f3044d6ace738415f2ac776b0e898415f3544d6b0e8d7955f3546f6b0e8d841d61dc386 else 0xa367384130354636b0ea37cd5f3544d69ce1057cab1dc196b0e8d8414b304776b0e898414b354776b0e8d8415f2a4776002738415f324775b0e8d8e9353547769ce1061930354776b0eb57f535354776b0e8d8415f2dc776b0e8d8355f2ac776)) else (if i < 135 then (if i < 134 then 0xb0e8d84181354776b0e8d841353a4776b0e8d8915f354776b0e8d8415f354536b0e8d7954b3544d6b0e898415f304776b0e8d9215f45c776b0e8d8416d3547769ce106255f2987769ce1057cd51dc6b6b0e8d8413b354776b2e7384135354776 else 0xb0e8d841803547769ce6a8415f354776ace7384135354776b0e8d8c55f354636b0e8d97d5f28c776aaa8d8415f29877600273840fa354775a360252cd53047769ce1070d5f354776ab2737e15f3547769ce1057cd51dc2e6b0e8d7955f3044d6) else (if i < 136 then 0x9ce1057cd51dc476002c3a363157d2359ce0257cd51dc456a86737855f354776b0e8d83535354776b0e73841403547769ce1057d2e3547769f61057cd51dc636b16738415f354776a36738415f3546b6b0e8d7954b304776b0e8d841ad354336 else 0x9cde557cd51dc2e6b2e738255f354776a36658415f3047769ce104c12a354776b0e8d8415f4742e6b0e8d79581354776b0e8d8415f2ac696b0e8d8415f308776b0e8d97d5f40c7769ce1057ca61dc456b0eb5809353547769ce104d4d51dc196)))) else (if i < 144 then (if i < 140 then (if i < 138 then 0xb0e8d9494b3547769ce106955f354776b0e8d795ad3543369ce10765303547769ce1057cd51204569ce104c123354776a8e738415f298776b7e738415c354776b0e8d8415f3546e6b0e8d94d5f354776b0e8d8f15f3dc776a8e738095f354776 else (if i < 139 then 0xab2738415f3544d69ce1057d5f3544d69ce1057cd5324776a8e738415f354486b0e838415f3544b6b0e8d9495f304776b0eb584130354776b0e8d8415f354616002738415f3545f59ce1057cd528c776002738098657c775a367d8415f354636 else 0xb7e738415f2987769ce107dd5f354776b0e8d841353546969ce3c57cd51dc3369ce1057d03354776b0e8d8415f3544b6b0e8d841512ac77600273841b257cd55b0e8d8415f3545969ce0257cd51dc0b6b7e738095f354776b0e8d7f55f2ac776)) else (if i < 142 then (if i < 141 then 0xb0e8d8415c2ac7769cde557cd528c7769ce1057cd51dc3c6b0e738415f2ac6369ce10604d51dc2e6ab2738414b3547769ce1057d4b354776b0e737dd5f354776b0ea38415f2ac4d6002738418657c4859ce1057ca61dc0b6b0e8d8415f3547f6 else 0x9cde157cfc3547760027357cd51dc2750022557cd51dc1b59ce1057cd51200b6b0e737f15f354776b7e738415f354486ab2738415f3047769ce1057d5f304776b0e8d8415f45c776b0e8d84173354776b0e8d8095f3548069ce107f15f354776) else (if i < 143 then 0xb0e8d7f535354776b0e8d841ad3543469ce737855f3547769ce1057ca61dc636ade738415f3547769ce1057d2f354776b0e8d8c55f48cd5600273795b257cd559ce0257cd51dc6360027384130354635b0e8d841914d4d56b0e8d8415f3cc776 else 0xb0e73841303544d6b0e8d79573354776ac68d8415f3545f6b0ea3841353544d6b0e8d9ad2b354776b0e8d91d5f35444600273841863f07759cde557d4b354776b0e8d8415f33c776b0e738415f3347769ce107495f354776b0e8d8095f2ac776))) else (if i < 148 then (if i < 146 then (if i < 145 then 0x9ce104c12d354776b0e8d809d91dc3969ce1057cd51dc1b6b0e73841353546369ce1057cd518c486a36738f15f354776002aa8415f298775b5e738415f3546369ce488415f354456b0e778415f3547769ce1057cd5264396b0e8d7955f45c776 else 0x2c3a364857d175a36738415f2986369ce106a95f3547769ce106195f298776002738415f3546b5b0e8d8415f2ac486b0e8d8415f3545b6a36738095f3546369ce1074d5f2ac7769ce026195f354776b0e10795352ac776b0e739215f354456) else (if i < 147 then 0xb0e8d84135298776b0e8d82d5f354636b0e8d9912d354776b7e8d8095f3544d69ce106195f354486b0e8d80935354776b0e8d841c7354776b5e8d8095f354776b0e8d8f2106b4d569ce1057cd51dc0f6b0e7384130304776b0e8d8415f27c776 else 0x27d8415f354635b0e8d8415f48c4669cde157cd51dc4d6b2e738415f3547769ce1057d1d3544d6b0e8d89173354776b0e8d8e95f354776b0e738415f3487769ce1057d013547769cde557cd51dc1b6b0e8d82551354776b62738415f334776)) else (if i < 150 then (if i < 149 then 0xb7e898095f354776aae738415f354776b0e8d84135354486b0e8d84157354776b0e8d8415f3a4776b0e738415f378776b0e8d8415f320776b7e8d8094b354776b0e7d8415f2a07769ce1057cd5234776b0ea88415f2ac776b0e8d84168354776 else 0x9ce1057cd51dc5d6ace738415f354776b0e8d841573546f6b0ea68415f2ac776b0e8d8414b2ac6369ce106c930354776b0e7d8415f3544d6b0e7384142354776b0e8d841303547769ce106b55f3544d69cde157cd5280776b7e8d8095f304776) else (if i < 151 then 0x9ce107655f298776b0e8d8355f354776a36738415f3548d69ce1057d23298776b2e737955f3547769ce106b54b354776a36737855f3544d6b0e8d8895f3547769ce027655f3547769ce0257d23354776b0e8d8415f3544f6b0e838355f354776 else 0xb0e748415f354776b0e8d79557354776b0e8d7955f3a4776b0e8d8419d3544d69ce106b55f304776a360252cd51dc6369ce1057cd51dc196aaa1057cd52987769ce488415f354636b0e8d8415f3344d6b0e7d8414b354776b0e8d79568354776))))) else (if i < 167 then (if i < 159 then (if i < 155 then (if i < 153 then 0x9ce104d4fe354776a3673841352ac776b0e8d9215f45cd56b0e8d8414b3347769ce107655f354486b0e8d795303547769ce1057d23354486aa28d8095f354776b0e8d841532ac776a360257cc11dc636a36737854b354776b0e7d8415f304776 else (if i < 154 then 0xb0e8d9214b354456ada8d8415f354776b0e8d8415f304976b0ea6841353547769ce1057d40354776a36738415f2d8776b0e8d9ad2d2ac776b0e8d8414b354976ace737955f354776a36738415f3545d6a36737855f304776b0e8d8415f3546d6 else 0xb0e8d8415f3484d6002738095f354635b3a738415f2ac7769ce1057d2c354776b0e8d9215f304456b0e7385d5f354776b0e8d841d41dc396002738f15f354775b0e8d8515f3547769cde557cd51dc196b0e8d841353046369ce178415f354776)) else (if i < 157 then (if i < 156 then 0x9ce1057cd51dc2f6a7e738415f3547769ce5c8415f354776002738415f2986359ce5f7855f354776b0e8d97e4857d236b0e8d8915f3a4776b0e8d8415f354696b0e8d90d5f354446b0e7f8415f354776b46738415f2ac776b0e808415f2ac776 else 0xad6738415f2ac776b0e738095f3544d6b0e8d841393547769ce104c0d51dc2e6002738418757c775b0e8d97e10734776b0e8d8414b348776a367384175354776b0e8d8415f3784d69ce648415f3547769ce108095f3544d6b0e8d841bf57c776) else (if i < 158 then 0xb0e8d8414b3787769ce108094b354776b0e8d8419157cd569ce0257d2d3547769ce1057cd51dc126b0e8d8415f2ac5a6b0e8d84155354776b0e738415f2984d6b0e898415f2a8776b0e8d841423544d6ae68d8415f354776b0e898415f348776 else 0xb0e8d9755f28c776b3a7384135354776b0e8d7f55f3547769ce108095f304776b0e8d9a92c354776b0e8d7955f3546969ce1052cfd3547769ce1057d2d298776b0e738094b3547769ce2457cd51dc196b8e738415f354636b0e8d8c15f354776))) else (if i < 163 then (if i < 161 then (if i < 160 then 0xb0e8d8415f2ac9969ce647955f3547769ce488415f48cd56ace8d8414b354776afe8d8415f354626b0e8d8419557cd56b0e738095f304776b467384135354776b0e8084135354776b0e8d84151354776b0e738414b298776b0e8d841d31dc396 else 0x9ce1057d1c3547769ce106b95f354776b0e738415f3546369ce106c55f354776b0e8d841563547769ce1057d2d354486a42738415f3547769ce1057cd51dc266b0e8d841d94bc776b0e8d841423047769ce108415f354636b0ea38415f3544d6) else (if i < 162 then 0xa7e1057cd51dc4d6b0eb5841352f4776ad67384135354776b0eac841352ac776b0e73841cd354776002737855f3544d500273840fc354635b0e8d7959157cd56b0e738414b354486b0e8d8415c3547769ce107515f354776a36737cd5f354776 else 0xa928d8415f354776b0e8d84145354776b0e8d8415f314776b0e8d841353545a6b0e8d841ab57cd569ce104c0d528c776b0e8d841d9264396b0e738415f3044869ce1057d203547769ce1057d1a298776002738415f3548d5b0e8d8415f3ac776)) else (if i < 165 then (if i < 164 then 0x21057cd51341b5b0e8d85d5f3544d69ce1057cd51dc426b0e8d7e15f354636b0e8d80d5f354776b0e8d8416b354776002737854b3547759cde17855f354776b0e73841a1354776b0e8d8415f2ac8b6b0e8d79551354776b0e838095f354776 else 0xb0e8d8415f354516002737855f3047759ce1057d353546369ce026c95f35477600273841352ac77500273841b24c0d559ce1057cd52986369ce107955f354636b0e8d8095f354776b0ea37955f3544d69ce6b8415f2ac7769ce1057d303544d6) else (if i < 166 then 0xb0e8d8095f3546f6b0e8d85d4b3547769ce1061d5f354776b0e8d841733a47769ce1057cd52007769ce1057cff3547769ce106c95f298776b0e8d84135354996b0e8d7955c354776b0e737955f354636b0e8d8415f298776002738415f3545d5 else 0xb468d8414b2ac7769ce1074d5f3547769ce478415f3546360028d8094b354635b0e8d8415f354876b62738415f354636a7e8d8415f3544d6b0de557d352ac7769ce1052d30354776002738415f2d87750021052cd51dc1b59ce1057cab1dc336)))) else (if i < 175 then (if i < 171 then (if i < 169 then (if i < 168 then 0x9ce107595f304776a7e8d8414b354776b0e9d841353547760028d8095f304635b62c37955f2ac7769ce106c95f354486b5ec37955f354776b0e8d841353dc7769ce1057d30304776b0e8d8415f3544860021057cc11dc1b5b0e8d85d5f304776 else 0xa36738415f3548069ce6b841353547769ce105ccd51dc1960027357cd5134255b0e8d8094b3544d6a7e8d8415f304776b0e8d7955f2987769ce1057cab2ac776b0e8d8f1ad57cd569ce1057cab1dc776b0e8d841353548b6b0e8d8415f3b4776) else (if i < 170 then 0x9ce1068d5f3547769ce5e8415f304776b0e8d8a55f3547769ce1057cab1dc2c6aa28d8415f3545a6b0e8d841cd434d56b0e8d8095f3044d6a36026a15f3547760027384175354775ab2a88415f2ac776afe8d8415f2ac776b0e8d84199354776 else 0xb0e73841c357c7769ce1057d42354776b0e8d9ad973547769ce106995f3547769ce104c0d51dc1b6b8a738415f354776a36108094b304776aca738415f3547760027352cd51dc255b0e8d7955f3544869cde157cd51dc2569ce104d4d51dc336)) else (if i < 173 then (if i < 172 then 0x9ce104d4d51dc776b0e8d8414b354636b0e8d8415f36c776b368d8095f354776b62c379535354776b0e8d841cd3544d6b3a8d841353047769ce1057cfe354776a36738415f2ac7760027357cc11dc255b0e8d8094b304776b0e8d8414e354776 else 0xafe8d84135354776b0e8d8415f304636b0e898415f354636b0e8d8415f48c2d6a3673841d91dc3969ce106a55f3547769cde157cd53047769ce0257cd51dc2e69ce106915f3547769ce104d4d52ac776b0e8d841a13544d6b0e8d80981354776) else (if i < 174 then 0xa0e7384135354776b2e7384130354776b0e738419757cd56b0e8d809ad354336b0e106115f2ac776b42738415f354776b0e8d841cd3047769ce1057cd52d8776b0e8d8414b3d87769ce1057ca61dc2e69ce1057d1f354776002737cd5f354775 else 0xb0e8d9ad2d354776b0e8d7954b354636b0e8d841352f4776a367384135354776a360257cd53046369ce1057cd51202e6b0e8d841a1304776b0e8d84153354776b0e8d84179354776b0e8d8415f3d4776b66738415f354776a36737955f2ac776))) else (if i < 179 then (if i < 177 then (if i < 176 then 0xb7e8d8095f348776b0e8d8d95f354776b0e8d841ad3543b6a36658415f354636b0e8d7c95f3547769ce6b9215f354776ace7384130354776b0e738415f324776b0e8d7955f30463600273841b157cd559cde157cd51dc396aee738415f354776 else 0x9ce1057ca628c7769ce104c0d51dc196b0e808415f354776b0e8d79553354776a86738415f3544d6b0e8d841472ac776b3a738415f3547769ce107755f3547769ce0257cd528c776b0e8d841323547760029f8415f3544d59ce1057ce91dc196) else (if i < 178 then 0xb0e8d8413531c776b0e8d841c357c4d6b0e8d841a0354636b0e8d97dcd57c77600273809b257cd55b2e8d8415f2ac636b0e8d8415f354686b0e8d8415f354796b0e8d8413d354776b0e8d7c15f354776a367379535354776b46738415f354776 else 0xb0e8d841ac354776a86738415f304776b0e8d8415f48ca469ce0257d4b354776ad6738415f354776b0eac8415f2ac776002738415f354805a36738255f3547769ce1057cd528c48600273841b257ca65b0e8d8c61057d236a86738414b354776)) else (if i < 181 then (if i < 180 then 0xb46737955f354776b0e807955f354776b0e8d8095f45c776b3a737955f3547769ce1057d4b298776b0e8d841c352c776b0e8d8415f3544a6b0e8d809733547769ce1057cab1dc376b0e8d8415f3545a6b0e8d8ed4b354776ad6b184135354776 else 0xb0e8d7d55f354776b0e8d8415f354996b0e8d9355f3547769ce1057d4b3544869ce1057cd51dc216ab2738415f3546369ce1057d5f354636b0e8d7995f354776002738415f2ac7759ce1077d5f354776002c3a366b70c7759ce1057cd51dc306) else (if i < 182 then 0xb428d8414b354776b0e8d7955f3545a69ce1057cd51343169ce1057cc1288776ad6737955f354776b0eac7955f2ac7769ce107355f354776b2e8d84135354636b0e738415f3545f69ce1057ceb1dc1b6b0e8d841aa354326b0e8d9892d354776 else 0x2c3a366b65cd55b0e8d8415f3244d69ce0257cd51dc1b6b2e73841513547769cde157cd51dc456b0e8d8195f354776b0e8d8415f3dc7769ce106855f354776b0e8d8255f31c776b0e8d8419752cd569ce107495f29877600273841d91dc395)))))) else (if i < 213 then (if i < 198 then (if i < 190 then (if i < 186 then (if i < 184 then 0xa8e737855f354776b0e8d84160354776002737955f2ac7759ce1057ca61dc1b6b0e8d8415f3548b600273841b23f0d55b0e8d841cc354776b0e8d8dd5f3547769ce638415f3547769ce104d4d51dc3769ce1057cfc3544d6b0e8d8419757cc16 else (if i < 185 then 0xa3e8d8415f354776b32738415f3547769ce1052cfc354776b0e8d8414b3247769ce738415f3544d600273841353547759ce1057cd51dc276b0e798415f354776b0e8d7955f3549969ce6b8415f354776b0e8d9521057c776a5e738415f354776 else 0xaa28d84147354776b2e8d8255f3546369ce738414b354776b0e8d8415f3546c6b0e7384130354636b0e8d7955f3dc7769ce1057cd51dc3369ce1057cfc304776b46838414b354776002737858657c775b0e8d7cd5f2e07769ce1057cd51201b6)) else (if i < 188 then (if i < 187 then 0x2106195f1dc1b5b62c37955f3547769cde157cd51dc0b6b7e737855f3547769ce738415f304776b3a8d8415f304776b0e8d80968354776a36758415f354776ac68d8415f2ac776b0e8d7955f3548b6b2e738095f354776b468d8414b354776 else 0xb0eaa8415f2987769ce1057cd52ac77600273795353547759cde557cd51dc276b0e8d80957354776b0e8d8095f3a47769ce1057cd51dc776b0e8d9adc33547769ce6b7955f3547769ce1057cd51dc386b2e738415f298776a8e738415f2e0776) else (if i < 189 then 0xace738095f354776b0e8d9221057d176b0e8d9ad2e3547769ce1057cd51dc6f6b2e738415f3544869ce1057cab2847769cde557cd51dc336b0e8d841c152c776afe8d8415f354776b0e8d80930354776b62c37955f3546f69ce1057cd51dc086 else 0x9ce1057cd51344d69ce10764d51dc396a0e738415f354776b468d7954b354776ace738415f298776a360257d4b3047769ce104c0ff354776b7e8d8095f3546369ce1057cd51dc2c6002738255f354775b0e738415f3546b6b0e8d84130298776))) else (if i < 194 then (if i < 192 then (if i < 191 then 0xac68d841353547769cde557cd51dc776b0e8d84130354486b0e868415f354776b0e8d8415f2f4776a36738415f354776b0e8d8415f488776ae2738415f3547769ce0257cd51dc1969cde157cd51dc636b3a8d7955f304776afe8d8415f3546f6 else 0xb0e8d841ad3dc336b0e3f8415f2ac7769ce1052cd51dc4d6b0e8d8414b3545f6b0e8d8415f3747769ce628415f354776ace738415f3544869cde557cd52ac776002736195f1dc2559ce1057ca61dc196b0e8d7855f2ac776b0e8d8915f3548b6) else (if i < 193 then 0xb0e8d94d5f354996b0e8d8417b3547769ce1057cc11dc4d6b0e8d8415f3045f6a867384140354776b0e7d8415f354636b0e8d8415f4742c69ce104d4d53547760027357cd51dc285a36738415f3546f6afe8d7955f3547769ce106b55f354636 else 0xa36738414b3544d69ce0257d2c354776b0e7e8415f354776aaa738415f2ac776b0e8d7955f2f4776a36737955f354776b0e8d8415f334636b0e8d841ad3dc776b0e8d85d5f378776a36737855f3546369cde16195f3547769ce1057cd5120196)) else (if i < 196 then (if i < 195 then 0x9ce107395f354776b0eb484135354776a36738415f3044d69ce6b841ad354776b0e8d78535354776b328d8414b354776b0e8d8095f354696b5e8d7855f354776b0e8d8415f31c776a3673841302ac776b0e8d8555f3547769ce1057cd51dc346 else 0xb0e8d9ad2f3547769ce1057cd51dc296a36738414b3047769ce106b4d51dc336b0e8d9455f2ac776b0e8d7e95f354776aba738415f3547769ce1069130354776a7e8d841423547769ce5c8415f298776b328d8415f304776b0e3f84135354776) else (if i < 197 then 0xa367384181354776b0e8d841352e0776b0e8d8415f348636b0e8d7955f31c776a36738915f354776aaa73841353547769cde157d2a354776b0e9a8415f2ac776b0e8d8c55f2ac776b0e8d84147354776b0e8d921a13544569ce1057cfa354776 else 0xb0ea38095f3544d6b0e8d8415f42cd56a367397d5f28c776b0e738f15f354776b0e8d8414b3546b69cde17655f3547769cde157d23354776b0e8d8099557cd56b0e8d809513547769ce3c8415f354776b2e8d8415f3546369ce5f8415f3544d6)))) else (if i < 205 then (if i < 201 then (if i < 199 then 0x9ce5f8414b354776b0e738095f354636b0e8d8415f2cc776b0e8d8415f3046b6a3673841ad354336a36838414b354776b0e8d841733548b69ce0257cd51dc266b0e8d8415f378636b0e8d841d51dc3869ce1057cd51dc6e69ce108095f354636 else (if i < 200 then 0x9ce5f8415f304776b0e8d94535354776b0e8d78d5f354776b0e738415f2986369ce106b55f48cd569ce618415f354776b0e8d84142354636b0e8d795473547769ce1057cd51dc3769ce598415f354776b0e8d8095c354776b7e738415f354746 else 0x9ce1057d1c354486a367394d5f354776b0e8d8415f354736002b184135354775b467384130354776b2e8d7955f354636002738415f354775b0e8d8419b354776b3a7384130354776b0e8d8c5353547769ce1057cd51344369ce1057cd51dc446)) else (if i < 203 then (if i < 202 then 0x9ce1057cd51dc0169ce1057cd51dc006b46738355f354776ac6738414b354776ab68d8415f354776b0e8d8095f298776002738415f3546f5b0e8d8415f2d0776002bf7955f354775b0e898415f3544c69ce1057cd51dc1c6a36738415f3546e6 else 0xb0e8d8415f41cab69ce104c0d51dc306b0e8d7b95f354776b0e8d7895f354776b0e8d84153354696b0e8d8095f354486002737955f354775b0e8d8415f3547c69ce1057cd5120426002737855f354635b0e8d8415f2ac746ad67384130354776) else (if i < 204 then 0xb0e8d841d91dc3869ce1057d303546360021057cd518c1b5002d77855f354775b0e8d85d5f354636b0e8d8414c35477600273841302ac775002738414b3544d59ce107855f3544d69ce1057cd51dc076b0e8d8415f298486b0e8d8415f35c776 else 0xa7e8d8415f3546369ce1057cc11dc2d69ce107854b3547769cde157d2d354776a36738415f45c776a367384173354776002738415f3044d5b0e738415f3548d6b0e7c8415f354776b0e737855f3544d69ce1057cd51dc2b6b0e8d97d5f284776))) else (if i < 209 then (if i < 207 then (if i < 206 then 0xb5e738415f2ac776b0e8d8415f3a48b69ce1057cd51dc046ac68d8415f354776002738414b304775b3a738415f354696a4e738415f3547769ce107855f304776b0e8d841a9354326002c3a36106b4f75b0e8d8f15f3544d6b0e737854b354776 else 0x9ce1057cd5354776b0e8d8f14b3547769ce3e8415f354776002738915f354775b0e8d8415f354666a36738095f2ac776b0e738415f3545d6b0e737855f304776b0e808415f354696b0e73841352ac776b0e8d841353547469ce1057cab1dc486) else (if i < 208 then 0xb0e8d8415f3107760027357cd518c2559ce1057cd5284776b0e8d8f15f304776b0e8d8094b3546369ce6b84130354776b0a8d8415f354776b0e8d84126354776b0e8d8419f354776a36108094b354636b0e738415f2d87760027384181354775 else 0x9ce104c0d51dc3369ce1057cd522c19600273841ad354335b0e8d8095f304636002838414b3547759ce106995f354486b0e8d8415f44c4d6b0e8d9ad2c3547760027397d5f28c775b0e858415f354776a36108095f304636a36598414b354776)) else (if i < 211 then (if i < 210 then 0xb5e7384135354776a36107515f3546369ce1057cd51dc026b0e8d8413548c2e6a36106c55f354636b62c379557354776b0e8d8415f3548169ce1057cd5134256b0e8d82d5f2ac776a36738415f2ac486ac68d7955f354776b0e8d99d5f354776 else 0x9ce1057cd51dc0369ce104c0d51dc7769ce1052cd51dc256b0e8d841cd354636b0e8d80953354776b0e8d8414d354776b0e73841753547769cde16c95f3547769cde557cd53547769ce104d4d51dc4869ce1057cd51dc0c6b0e8d7855f354776) else (if i < 212 then 0x9ce1057cc11dc256b0e104d4ab1dc4d6a367384135298776002738415f3546e59ce104c0d52ac776b468d8354b3547760027394d5f354775afe8d841573547769ce468415f3544d69cde557cd5284776b0e8d8415f3d8636a367380935354776 else 0xb0e8d841ad3dcd56a367384135354486b0e8d8415f2e0776a367384157354776a36738415f3a4776aaa738415f354776a367384168354776a3a738415f354776b0e6d8415f3547769ce1057cd53044d6ad6737f55f354776b0e8d841a1354636))))) else (if i < 228 then (if i < 220 then (if i < 216 then (if i < 214 then 0x9f6738415f3544d6b3a738415f298776a367384130354776b46738095f3547769ce107cd5f354776b0e808095f354776b0eb47955f354776a360257cd51dc2469ce488415f2ac776b3a738095f3547769ce1052cd5304776b0e8d82d35354776 else (if i < 215 then 0xb0e8d9455f354776b3a738415f3544860027384173354775b0e8d8415f458636a36738355f3547769ce1057cd5134396b0e8d8395f354776b0e8d841352ac4d6b46738415f298776b0e737cd5f354776b0e8d8415f46c2e69ce1057cc1304776 else 0xb0e8d7955f2e0776b0e8d8095f3545a6b0e8d8c55f354776b2e738415f31c776aaa737955f354776b028d8415f354776b46738415f354486ad6738095f354776b0eac8095f2ac776b0e8d8415f3545869ce5f57cd528c776002738415f45c775)) else (if i < 218 then (if i < 217 then 0x9ce1057cd51dc6969ce1057cc11dc396a86738415f354636b0e8d9695f2887769ce1057cd51dc366a367379530354776b0e8d841d96b5236b0e8d8415f32c776b0e8d841d91dc376b3a8d8415f304696ad6738415f2987769ce1052cd51dc396 else 0xb0e8d841c357c636b0e8d8095f3549969ce1057d25354776b0e9f8415f3544d69ce1057cd51dc156b0e8d8ed5f354636ad6738415f3544869cde157cd51dc2e6002738095f2ac7759ce106095f3547769ce4884135354776b0e8d8055f354776) else (if i < 219 then 0xb0e8d8095f3548b6b0e8d809cc354776b0e8d8415f4802d6a36738415f354696aa28d84143354776b0e8d8415f4642e6a02738415f2ac776002738415f2ac485b0e8d8095f3dc7769ce1057cd512030600273840fd354775a861057cd51dc486 else 0xb0e8d8795f3547769ce6b8415f298776b0e8d9ae1070c7769ce1057cd51dc0e6b0e8d8415f4782e6a868d8415f35448600273809353547759ce6b8095f354776b0e8d84136354776b8e738415f2ac776b0e738415f354806b0e8d9992d354776))) else (if i < 224 then (if i < 222 then (if i < 221 then 0x9ce1057cd51344569ce1057d173547760027384168354775b0e738415f2ac776b0e8d8415f3547469ce0257cd51dc336a568d8415f354776b0e8d7cd5f3544d69cde157cd528c7769ce108415f2ac776b0e56841353547760027384135298775 else 0xb0e8d8415f32463600273840fc2ac7759ce6b8415f354486b0e8084153354776b0e8d7f55f2f4776b468d8094b354776a36737f55f354776aaa8d8415f304776b0eb5841353544d6b0e8d8415f3c47769ce1057ca61dc336b3a7384153354776) else (if i < 223 then 0x273785b257cd559ce408415f354776b0e8d7cd4b3547769ce3157cd51dc2e6b3a8d8095f3047760027384135354485b0e8d8415f3547860027384157354775002738415f3a47759ce1057cfc354636a367384151354776b0e8d8c581354776 else 0xa367384156354776b0e8d7cd5f304776b0e8d8415f414d56b8e7384135354776b0e73841d91dc3969ce0257cd51dc77600273841303547759ce1052cd51dc456a8e738415f3544d6b0e8d8414a354776b0e8b8415f354776b0e8d8415f41cd56)) else (if i < 226 then (if i < 225 then 0x9ce107955f2ac776b0e8d8415f3544069ce1057cc11dc456002c3841352ac4d5b0e8d7e15f2ac776a36738415c3547769cde157d4b3547769ce1057ca61dc7769ce0257cd52ac7769ce738415f354636b0e8d9ae1065cd569ce1057cd5120336 else 0xa36738415f3ac776b0e737955f2ac776b0e8d7955f354746ac68d8415f3545b6a8e738414b3547769ce1057d352ac776002106c95f3541b5002738418657c4d5afe8d8095f354776b0eb5841353047769ce1057cab2987769ce1057cd51dc3b6) else (if i < 227 then 0xb56738415f354776b0e73841353547769ce1057cd51dc486b5e738415f354776a8e738415f304776b0e8d8415f48c2e6a3673841453547769ce10841353547769ce5f841d957c776b0e8d841283547769ce5f8415f48c776002738355f354775 else 0x27379530354775b0e8d8095f2f4776a36738095f354776a360257d4b354636b0e8d8415f4507769ce1057cd51340b69ce1057cd52ac486b0e8d7955f41cd56b7e738415f3544d6b62738415f2ac776002738418652c7759ce1057d18354776)))) else (if i < 236 then (if i < 232 then (if i < 230 then (if i < 229 then 0x2c3a3653764775b0e8d8415f434ab6b0e8d81d5f354776b0e8d7e135354776a7a8d8415f3547769ce1057cf83547769ce1052cd51dc0b6b7e738414b354776b26738415f3547769ce1057cd51dc176a36738415f298776b0e8d8415131c776 else 0x9ce104d535354776b0e8d7955f48c2e6a36738415f354486002736c95f354255b0e8d8955f354776b0e8d7a15f3547769ce104d4d52987769ce1057cc11dc0b6b7e738415f3047769cde157cd51dc1b69ce1079535354776b0e808415f3544a6) else (if i < 231 then 0x9ce668415f354776b0e8d8414b3548069ce1057cd518c4d6b0e8d9755f2847769ce105d55f354776b0e73795353547769ce106d15f3544d6b0e8d841c365d5f69cde557cd51dc486b0e8d8415f47c2d6b0e8d82d5f354776b5e737955f354776 else 0xb0e738255f354776b0de557cab1dc4d6a36737955f298776b0e8d8415f304806b0eac8415f2ac5a6b0e8d8415f2ac4d6b6273841353547769ce1057ce9354776b0e8d84149354776002738415f3546959ce108255f354776b0e8d84143354776)) else (if i < 234 then (if i < 233 then 0xb0e8d8414b2ac776b0e104d4d52ac4d69ce1057cc11dc636002a18415f354485b0e8d841a73543369ce6f8415f3547769ce104c0d53547769ce1052cd51dc636b0e8d8095f31c776b0e8d8415f354646b2e8d84151354636b86738415f354776 else 0x9ce498415f354776b3a8d841533047769ce1057cd51dc286b0e898415f2ac7769ce1057cd51dc096b0e8d84135434d56b0e8d8415f2707769ce106195f3544d6b2e737855f354776b0e8d841d9134396a36737955f354486aa2738415f354776) else (if i < 235 then 0xb0e8d8415f3547669ce106194b354776aa28d7d95f3547760027384151354775b0e8d7955f2ac4d6002737f55f354775b0e8d8418148c2e6b0e8d9215f3544669ce1057d003547769ce107554b3547769ce488415f354776b0e8d80947354776 else 0xa36738415f3046369ce106195f304776ace737855f354776b0de54d4d51dc4d6b2e8d8095f354636aa28d7e15f354776b0e8d841353544d6a9a738415f354776b0e8d78530354776afa8d8415f354776a36738414b354636b0e8d8415f328776))) else (if i < 240 then (if i < 238 then (if i < 237 then 0xb3a808415f304776002738415f3ac7759cde157cd51dc196b0e8d94dd9354776b0e8d8415f38c776b0e8d8415d354776b0e8d8095f42cd56002738415c354775b0e8d7954b2ac776b0e8d84163354776b0e8d841663547760027384156354775 else 0xb1a738415f3547769ce0257cd51dc446a628d8415f354776a7e8d8413e354776aaa7384130354776b0e8d84135304776b0e8984135354776a3673841533547769ce487955f3547760027384145354775b0eac8415f2987769ce1052cd51dc326) else (if i < 239 then 0xb0e8d8bd5f3544d69ce107655f3544d69ce1057d233544d6b0de573d5f354776002738415f2987759ce5f8415f354636b268d8414b354776002738095f354775b5e738415f3546e6b0e8d795353544d6a36739ad2d354776a36898095f354776 else 0xa02738415f354776002738415f3544859ce107654b3547769ce1052d23354776ac68d7f55f3547769ce1057cd51dc5a69ce1057cd51dc1e6b0e8d8255f3544d69ce588415f3547769ce5a8415f354776b0e878415f354776a36737c95f354776)) else (if i < 242 then (if i < 241 then 0x9ce1057cd51dc1d6b0e8d8416f354776b0e8d982103547769ce104c0d51dc3669ce1057cf71dc336b8e738415f3547769ce107655f3047769ce1057d23304776aa28d8415f3544d6b0e8d8254b3547769ce1057cd51dc3a6b0e8d79535304776 else 0xab2738415f2ac776b0e8d8415f2c47769ce1057d5f2ac776a66738415f354776a361052cc11dc636b0e8d8415f3548569ce1057cd5264776b0e8d841bd4d4776b0e8d9adc357c776b0e8d8615f354776002737955f298775b0e8d8255f304776) else (if i < 243 then 0xb0e8d84154354776b0eb184135354776b0e8d841d91dc3b6002737955f354485b0e738415f354776aa28d8415f3047769ce1057ca61dc2b6a36738415f3545a69ce108415f3547769ce587955f354776ad6738415f2f4776aa28d8414b354776 else 0xac68d8095f354776b0e8d841cb354776b0e8d8415f2ec7769ce107655f1dc39600273840fc354775afe107955f3547769ce1057ceb354776))))))))
def level5 (i : Nat) := fld (level5Chunk (i / 12)) 64 (i % 12)

def level6Chunk (i : Nat) : Nat := (if i < 47 then (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0xb0e8d8415f35477061ec3a36104d4d51dc397002c39cde557cd51dd8009ce1057d35354776b0e8d97e1057cd51ddc009ce1057cd5298776b0e8d841b957cd51ddc009ce107955f354776002c3a35f857cd51ddac3a3648841ad57cd57b0ea3a35f357cd51ddec3a36104d4d5304777 else 0xb0e738415f354d51ddc00b0e8d841b057cd56002c3a361057d0d355ac3a361057cd5238777b0eb1a361057cd51ddec3a361057cd51dc237b0e8d97de557cd51ddec3a361057cd51dc437b0e8d841354acd51dded1a361057d4b354777b0e8d9a61057cd51ddc00b62738415f354776) else (if i < 3 then 0xb0ea3a361057cab1ddc00b0e8d8414b354776b0e8d841e157cd51ddec3a36106d95f354777b0e8d8415f354770b5eaca36738415f354777a36738415f57cd51ddec3a35e557cd51dc437b0e8d8415f2ac77115c00b0e8d8415f3544d6b0e8d9761057cab1ddecab0e8d8415f354777 else (if i < 4 then 0xb0e8d795e157cd51ddec3a361057cab1dc0b7b7ec3a361057cab1ddec3a36104d4d51dc457b0e8d8415f46cab1ddc00b0e1057cd518c196002c3a35e557cd5135ac3a361057d20354637002c3a361057cc11ddac3a361057cd52000b7002c3a261057cd51ddac3a36106315f354777 else 0xb0e8d8415f35477095ec3ab28d84147354777b0e8d8415f51cd51ddc00b0e8d841864d4776b52c3a361057cd51ddec3a367384130354777b0ea3a36104d4d51ddc00b0e8d7955f304776b0e8d8415f354770f5ec3aaa738415f354777002c3a35e552cd51dd800a36105a0d51dc0b6))) else (if i < 8 then (if i < 6 then 0xb0e8d8418657cab1ddec3a35e557cd51dc257b0e8d8415f354c11ddec3a36468415f354777b0e8d8414b354d51ddec3a36104d4d51dc0b7002c3a34fc35477095adfb0e8d84135354777b0e8d8415f354a41ddec3a361057cab1dc637b0e8d8c61057cd51ddec3a361057cd53544d7 else (if i < 7 then 0xb0e91a361057cd51ddec3a361061935354777b0e8d8418857cab1ddec3a361057d2b354777b0e8d7955f354c11ddec3a361057cd51dc397b0e8d9215f35477115ec3a367d8415f354777b0e8d841353547718de8d9ce106b55f354777002ac9ce1057cd51dd8009ce1057d5f354776 else 0xb0e8d841b757cd51dded7b0e738415f354777b0e8d8095f3f0d51ddec3a36278415f354777b46c3a361057cd518deceb0e8d8415f354637b0e8d7955f4acd51ddc00b0e7384130354776b0e8d841d957cab1ddec3a361057d232ac777b0e8d7955f354770e5ec3a360257cd5288777)) else (if i < 9 then 0xb0e8d8415f35477115ec3a365d8415f354777b0e8d841d94d4d51ddec3a36104d523354777b0e8d9ce1057ca61ddc00a360257cd51dc0b6002dfa360257cd51ddac3a36738095f354777b0eb5a361057cd518de8d9ce108095f354777b0e8d8415f354770a9ec39ce1057cd51dc487 else (if i < 10 then 0xb0e8d7955f35477115ec3a361057d2d2ac7770028d9cde157cd51dd800b0e8d8418657c776002c39f61057cd51ddac3a8e8d8415f354777b3ec3a361057cd51ddc009ce106b55f354776b0e8d9ce1057cd5121c00b0e8d8415f2ac636b0e8d8420b57cd51ddc00b0e8d8418557c776 else 0xb0ea3a35e557cd51dde8d9ce1057d303547770028d8415f3547706d800b0e8d84135354636b0e8d8415f3547702dedfb0e8d8415f354777002c3841b257cd5065ac3a366b8415f354637b0e8d8095f35477135ec3a361057d1b354777002c3a361057ccd1ddac3a365357cd51dc397)))) else (if i < 17 then (if i < 14 then (if i < 12 then 0xb0e8d7955f3547702dec3a361057cd51dc637b7ec3a35e557cd51ddec3a36104d52d354777b0e8d841b457cd51ddc00b0e8d8418857c776b0e8d8415f3544d121c00b0e8d7958657c776b0e8d8415f354630cdec39ce488415f3547770028d840fc3547702d800b0e8d9215f354456 else (if i < 13 then 0x2c39ce1057ca61dd800b0e8d84142354776b0e8d841d557cd51ddc00b0e738095f354776b0e8d8415f464d51ddc00b0e8d8415f378776002738420257cd51ddac3a36106c95f2ac7770028d9cd5f35477095ac3a361057cd52ac637b0e8d8418557cd51ddc00b0e8d8415f348776 else 0xb0e8d8415f354770c9ec3a36106c935354777b0e8d97e0257cd51ddc00b0e738415f354486b0e8d8415f478d51ddec3a361057cd5334777b0e8d8415f35477051ec3a35e557cd51dc637b0e8da361057cd518ded1b0e8d8415f324777002c3a36103f8d51ddac3a36106195f354777)) else (if i < 15 then 0x2c3a361757cd51ddac3a361057cfb354777b0e8d8415f354d21ddec3a36488414b354777b0ec39ce1057cd51ddec39ce108415f354777b0e8d8418857cd51ddc00002737855f354775b0e8d9221057cd5135ec3a35e56195f354777b0e8d841b357cd51ddee3b0e738415f354777 else (if i < 16 then 0xb0e73841e557cd51ddc00a7e8d8415f354776b0e8d841f857cd51ddec3a361057cde354777b0e8d841d957cd51ddec3a361057cab1dc2e7b0e8d8415f48cd51ddec3a361057d171dc457b0e8d9221057cc11ddc00b0e73840fc354776002738415f4c0d51dd8000021057cd51dc1b5 else 0x2c3a360252cd51ddac3a35e57655f354777b0e8d7955f48cd51ddec3a36027855f354777b0eb5a361057cd517ded8b0e738415f354777b0e8d8419757cd51ddec3a361057cd51dc3f7002c3a360257cd5135ac39ce1057d35354777a868d9ce1057cd51ddec39ce1057cd5298777))) else (if i < 20 then (if i < 18 then 0x2c3a36106c95f2ad800b0e8d841cd354776002c3a355f35477099800b0e8d8415f354636b8ec3a361057cd5135ec3a361057cec354777002c3a36106d15f355ac3a361057cab28c777b0e8d8415f35463111c00b0e8d8095f304776b0e8d84135354770b9c000027357cd51dc255 else (if i < 19 then 0xb0e8d841a54d4d51ddc00b0e8d7955f354636a36738415f3f0d51ddec3a36108414b354777b0e8d8415f4b4d51ddc00b0e8d840fc3544d6b0e8d8415f52cab1ddee3b0e8d8415f304777b0ec3a361057cd5135c00b0e8d841a1354776b0e8d8421057cd5135ee3b0e8d8414b354777 else 0xb0e8d8415f3547707dc00b0e8d840fc304776b0e8d8415f4d4d5135e8d9ce738415f354777b0e8d841e557cd5135ec3b0e8d8415f304777b0e8d841a757cd51ddec3a360257cd51dc257b0e8d8421057cc11ddec3a36104d4d528c777b46c3a361057cd51adec3b0e8d8414b354777)) else (if i < 21 then 0xb0e8d8415f304a61ddec3a361057cd51dc5f7b0e8d841e557cc11ddec3a36105a0d51dc0b7b0e8d8095f354c11ddec3a361052d35354777b62c3a361057cd5135ec3a36107954b354777b0e8d7955f4b4d51ddec3a3610765ad354777002c3a36106cd5f355800b0e8d841b24d4d56 else (if i < 22 then 0xa36738415f35477135ec3a360257cd51dc397002c3a361070d5f1ddad8b0e8d8415f304777b0e8d841db57cd51ddec3a36106c95f354777b0e8d9961057cd51dded8b0e8d8414b354777b0e8d8415f354d518dc00a86738415f354776b0e8d8415f4d4c11ddec3a361057cd51dc057 else 0xb2ec3a36104d4d51ddc009ce1057cfc354776b0e8d8415f2ac77065c00b0e8d8415f324776b82c3a361057cd51ddec3ab2738415f354777b0e738415f57cd51ddc00b0e8d8419757cd56b6ac3a361057cd51ddec3a35e56c95f354777b12c3a361057cd51ddecbb0e8d8415f2ac777))))) else (if i < 35 then (if i < 29 then (if i < 26 then (if i < 24 then 0xb0e8d8413535477065ec3a361057cd51dc477b0e8d8095f35477115ec3a361057d2e354777b16c3a361057cd51ddec3a366a8415f354777002c3a36103e8d51ddac3a361070d5f354777b0eaca35f857cd51ddec3a361057cd51dc2e7002739ce1057cd51ddac3a361057cd51dc6b7 else (if i < 25 then 0xb0e8d8415f354c91ddedfa36108095f354777002738415f35477135800b0e8d8415f3545f6b0e8d8415f354a31ddc00b0e8d8098657c776b0e8d841a557cd51ddedfb0e8d8415c354777b0ea3a360257cd51ddec3a35e557cd51dc2e7b2ec3a360957cd51dde8d9ce5f8415f354777 else 0xb0e8d7955f354a31ddec3a361057cd51dc3c7b0e8d84181354770b9ec3ab28d8414b354777b0e8d8415f52cd51ddec3a363c57cd51dc337b0e8d8415f40cd51ddc00b0e8d841b257cd56b0e8d8095f3547702dedfb0e8d8095f354777b0eaca361057cd5135ec3a361057d5f3544d7)) else (if i < 27 then 0xb0e8d9cde157cd51ddec3a361057d2f3547770028d9ce1052cd51dd800b0e8d795b257cd56a3673841e157cd51ddec3a360257cd51dc637002c38415f2ac77065ac39ce106b55f354777002c3a355f3547709dac3ab28d8415f304777b0e8d8415f57cc11ddc00a36738415f3544d6 else (if i < 28 then 0x2c38413535477065ac3a36106a95f354777002c3a361057cd51adac3a361074d5f2ac777b0e8d8098657cd51ddec3a361057cd51dc1b7b0e8d8415f35463121ec3a36488415f354457b0e8d8415f354990e5c00b0e8d841863f0776b0e8d7955f52cd51ddc00a36738415f304776 else 0xa36738415f354c11ddec3ace8d8415f354777b0e8d841ad57cd5135ec3aae8d8415f3547770028d57cd51dc2502dac39ce108095f354777b2ec3a361057cd51ddec3a361057d1d3544d7a36738415f35477095ec3a361057d01354777b62c3a361057ccd1ddc009ce5f8415f354776))) else (if i < 32 then (if i < 30 then 0xa36738415f354770e5ec3a36104d4fe354777000009ce1052cd51dd4009ce107855f354776b0e8d841ad57cc11ddec3a361057cd51dc197b0e8d9221057cd518dc00002738415f3544d5b2ec3a35e557cd51ddec3a36106b54b354777b0e8d809d957cd51ddec3a360257d23354777 else (if i < 31 then 0xb0e9fa361057cd51dded1b0e8d8415f2ac777002c3a360257cd518daceb0e8d8415f2ac777b0e8d8415f4b0d51ddec39ce1057d30354777002c38415f3547706d800b0e8d8f15f354776b0e8d7955f35477065ec3a36178415f354777000009ce1057cc11dd400b0e737855f354776 else 0x2c39cd5f35477095ac3a362457cd51dc197b8ec3a361057cd518dc009ce1057cd51dc256b0e8d8420252cd51ddec3a360257d2d354777b0e8d8415f35477049ec3ad68d8415f2ac777002c3a361061d5f1ddac3a36648415f354777b0e8d8420257cd5135ec3a361057cd51dc2f7)) else (if i < 33 then 0x2738415f354c11ddac3a36106b95f354777b0ec3a361057cd518dec3a36106c55f354777b0e8d8415f35477099ec3a36108415f354637b0e8d991e557cd51ddec3a36488415f48cd57b46c3a36104d4d51ddeceb0e8d84135354777b0e8d8420257cc11ddec3a361052cfd354777 else (if i < 34 then 0xb0e8d8415f4d4d518dec3a36026c95f354777002c3a36104d4ab1ddac3a36107955f354637b0e8d9ae1057cab1ddea3a36738415f354777002c38415f35477065ac3a361057d20354777b0eb5a36104d4d51ddc00b0e8d840fc354636a36738415f35477115ec3a36107515f354777 else 0xa36738415f3547702dedfa36738415f354777002c37955f35477065ac3a361074d5f354777b0e8d91e1057cd518ded8b0e8d8415f354637b0e8d8414b4c0d51ddec3a361057cab1dc337b0e8d8418757cd51ddec3a361057cd52007770028d9ce106195f1dd8009ce1057cd51dc396)))) else (if i < 41 then (if i < 38 then (if i < 36 then 0x2c3a354b35477095ac3a36104d4d51dc337b0e8d841a357cd51ddec3a365e8415f304777b0e8d8415f2ac770b1ec3a86738415f354777b0e8d9ae104d4d51ddec3a36105ccd51dc197002c3a355f3544d095ac3a361057cab2ac777b0e8d8415f2ac771ddec3a36107595f304777 else (if i < 37 then 0xa36738418657cd51ddec3a36106a55f354777b0e8d8095f354770b9ec3a36104d4d52ac777b0e8d84135354771ddec3a361057cfe354777b0e8da361057cab1ddc00b0e8d57cc11dc256002c38915f35477065ac3a361057d42354777b8ac3a361057cd51dde8d9ce1057cd51dc637 else 0xb0e8d9ae4857cd51ddc00002738418657c775b0e738415f3f0d51ddc00b0e8d841b157cd56b0ebba361057cd51ddc00a8e738415f354776b0e8da36104d4d51ddc00b0eb584135354776b42c3a361057cd51ddc009ce1057cd51dc456b0e8d8415f47cd51ddc00b0e8d7cd5f354776)) else (if i < 39 then 0xa3673841d957cd51ddc00b0e8d809b257cd56a36738415f48cd51ddc009ce1057cd51dc0b6b46c3a361057cd51ddc00b7e738415f354776b0e739ce1057cd51ddeceb0e8d8415f354777b0e8d841dd57cd51ddec3a360257cd528c777b46c3a0e1057cd51ddec3a361057ce91dc197 else (if i < 40 then 0xb0eaca361057cd518dec3a361057d5f354637002c3a361057cab1ddac3a361077d5f354777b46c3a35e557cd51ddc009ce1057cd51dc636b3ac3a35e557cd51ddec3a361057cab1dc377b0e8d8095f52cd51ddec3ad68d8415f354777002c3a361057cd5201800b0e105ccd51dc196 else 0xb0e8d8415f3f0d5135ecbb0e8d841513547770028d9ce1057cd518dac3a36106855f354777002738418657cd51dd800b0e8d841d91dc396b0e8d8415f3544d0c5ec3a361057cc1288777b0eb5a35e557cd51ddec39ce1057cd51dc4d7b0e8d841cd57cd51ddec3a361057cd51dc217))) else (if i < 44 then (if i < 42 then 0xa36738415f4b4d51ddeccb0e8d8415f3547770028d8415f3544d02dac3a361052cfc354777b0e8d9ce1057cd5135c00b0e8d84135354776b0e8d8415f3547709dec3a366b8415f354777b0e97a361057cd51ddc00b0e8d7955f2ac776002c3a36106c8fc355ac3a36104d4d51dc377 else (if i < 43 then 0xb0e8d8415f354771ddec3a366b7955f354777b0e8d8415f354770e1c00a361057cc11dc0b6b0ea3a361057cb81ddec3a36738415f304777b2ec3a360257cd51ddc00b0e1057ce91dc1960028d8414b3547702dac3a36738414b354777b0e8d8415f354770cdec3a361057cfc304777 else 0xb0e8da0e1057cd51ddec3a361057cd51dc2c7002c3a360957cd51ddac3a361057cd51dc6f7b0e8d8415f2aca11ddec3a35e557cd51dc33700273841d957cd51dd8009ce1057d23354776b0e8d8415f35477021ec3a361057cd52ac777002c3a35e54d4d51ddac3a35e557cd51dc277)) else (if i < 45 then 0xb0e8d98a1057cd51ddec3a35e557cd52ac777002c3a358657c77095a8d9ce106c95f354777b0e8d7955f354771ddc00aa28d8415f354776b0e8da361057cd51ddec3ae28d8415f354777b0e8d8095f35477065ec39ce5f8415f354777b0e8d8415f3544d135ec3a3610764d51dc397 else (if i < 46 then 0xb0e8d841ad354770cdc009ce1057d2d354776002c39ce1057cd5135ac3a366b841ad354777b0e8d8415f354770d1ec3a360257d2c354777b0e8da35e557cd51ddc00002738415f354635b0e8d8415f30477135ec3a36104d4d5354777b0e8d841ad57cd518dec3a361052cd51dc4d7 else 0xb7ec3a361057cd51d1ec3a365f8414b354777b0e8d8095f35477099ec3a36108095f354637b0e8d8f21057cd51dde8d9ce1057cd51dc2e7b0e8d97e1057cd5135c00b0e738415f304776b0e8d8415f3e8d51ddc00b0e738414b354776b0e73841e157cd51ddec3a361057cd51dc297)))))) else (if i < 71 then (if i < 59 then (if i < 53 then (if i < 50 then (if i < 48 then 0xb0e738415f35477095ec3a361057cd51dc1c700273841b257cd51dd800b0e8d8415f354776002c38095f35477065ac3a361057cd5134437b0e8d8415f35477111ec3a365f8415f304777002c3a0e1057cd51ddac3a36106b55f48cd57b0e8d8415f354770ddec3a36598415f354777 else (if i < 49 then 0x2c3a361057cc1135a8d9ce1057d4b354777002c3a361052cd5135ac3a361057cd51dc077b0e738415f354c11ddc00a3673841b257cd56002c3a35e557cd51ddac3a361057cd51dc017b0e8d8415f35477001ed1b0e8d8355f354777a36738415f354a31ddc00b0e8d8415f3546f6 else 0xb0e8d8415f354a11ddc009ce1057cd51dc2e6002c3a3610604d51ddac3a361057cd53547770028d8418657c7702d800b0e8d8915f354776b0e738415f354770e5ec3a361057cd51dc047002c3a361052cc11ddaceb0e8d8415f354697002c3840fc35477065ac3a361057cc11dc2d7)) else (if i < 51 then 0xb0e8d91a1057cd5135ec3a35e557cd5284777b0e8d8414b35477095ec3a35e557cd5354777b0e8d8415f35477031ec3a361057cd51dc027b0e8d8415f3544d095ec3a361057cd522c197002c3a36106b4d50cda8d9ce1057cd51dc1b7002c3a365f57ca31dd800b0e8d57cd518c256 else (if i < 52 then 0xb0e8d9221057cab1ddeceb0e8d8095f3547770028d8415f3787702dac3a361052cd5304777b0eaaa361057cd51ddc009ce1057cd528c776b0e8ea361057cd51ddecba36738415f354777b0e8d8415f354c1135ec3ad68d7f55f354777b0e8d8415f30477095c00b0e8d94d5f354776 else 0xa36738415f35477065ec3a365f57cd528c777002c3a361057d171dd800b0e8d84173354776002738415f52cd51ddac3a361057cd5134397b0e738415f35477115eb3a36738415f354777b0e8d8415f304c11ddc0000273841b257cd55b46c3a360257cd51ddec3a36107cd5f354777))) else (if i < 56 then (if i < 54 then 0x2c3a36103f4d51ddac3a361057d25354777002c3a360257cab1dd800b0e738418657c776b0e8d8418257cd51ddec3a364884135354777b0e8d8415f354771a5ec3a361057cc11dc397b0e8d8414b354770e5ec3a8e738415f354777b2ec3a361057cc71ddec3ad68d8095f354777 else (if i < 55 then 0xb0e8d8421057cab1ddec39ce1057cd51dc637b0e8d8415f35477039c00b0e8d80935354776b0ea38415f35477135ec3a366b8095f354777b8ec3a361057cab1ddc00b0e1057cd522c1960028d85d5f3547702d8009ce1057cd51dc1b6b0e738415f3547702dedfb0e738415f354777 else 0xb0e8d8c55f354770b9c00b0e8d84157354776002c3a361057ce91ddac3a361057cfc354637002c3a36103f0ab1ddaceb0e8d84153354777b0e8d8415f3544d115ec3a361057d17354777002c3a36105a0d51ddac3b0e8d8415f2ac777002cb9ce1057cd51ddac3a360257cd51dc337)) else (if i < 57 then 0xb0e8d841e557cab1ddc00a361057cd518c0b6b0e8d8415f30477115c00ace738415f354776b0e8d8095f354ab1ddec3a36738415f354637b0e738418657cd51ddee3b0e8d84135354777b0e8d8095f354771ddc00b0e8d84130354776b0e8d8414b35477115ec3a8e8d8415f3544d7 else (if i < 58 then 0xb0ea3a361057cc11ddc009ce1057cd51dc196b3ac3a021057cd51ddec3a361084135354777b0e8d97e107655f1ddec3a365f8415f48c777002c3a360d57cd51ddac3a8e8d8414b354777b0e8d8415f4d4ab1ddc00b0e8d8418657c4d6b0e8d8415f2aca61ddec3a361057cd51dc3b7 else 0xb0e8d8414b3547702dedfb0e8d8414b354777b26c3a361057cd51ddec3a368d8095f354777b0e8d8415f3544d02dedfb0e8d8415f3544d7b62c3a361057cab1ddc00b0e8d8418652c776b56c3a361057cd51ddec3b0e8d84135354777b0e8d8415f35477121ed7b0e8d8415f354777)))) else (if i < 65 then (if i < 62 then (if i < 60 then 0xb0e73841d957cd51ddec39ce1057d23354777b0e8d99a1057cd51ddec3a361057cd518c4d7b0e8d841b457cd5135ec3a36104d535354777002c3a35b257cd5095ac3a361057cc11dc0b7b7ec3a361057cc11ddedfb0e898415f354777b0e8d841e54d4d51ddec3a361057cf8354777 else (if i < 61 then 0xb0e8d9261057cd51ddec3a361057cd51dc097b0e8d8418657cd5135ec3aa28d8415f354777b0e8d8415f3047718dec3a366f8415f354777b0e8d8414b3547718dee1b0e8d8415f354777b62c3a36104d4d51ddec3a361057ce9354777002c3a361057cd51a5ac3a36108255f354777 else 0x2c3a3610570d51dd800b0e738415f354636b0e8d8418657cc11ddc00b0ea38415f3544d6b0ea6a361057cd51ddec3ad61057d35354777b0e8d8418652cd51ddc00b0e8d84151354776002c3a35fd57cd51ddac3a361057d00354777b0e8d841d552cd51ddec3a36488415f354777)) else (if i < 63 then 0xb0e8d9621057cd51ddec3a365a8415f354777b0e8d841d957cd5135ec3a361057d233544d7002c3a361057ca61ddac3a365f8415f354637b0e738415f4b4d51ddc00b0e8d8095f354776b1ac3a361057cd51ddec3a360257cd51dc447b0e8d921e557cd51ddec3a361052cd51dc327 else (if i < 64 then 0xb8ec3a361057cd51ddec3a36107655f304777b0e8d8415f48cc11ddec3a361057cd51dc3a7b468d9ce1057cd51ddec3a36808415f354777002c3a361057cd5121ac3a36107654b354777b0e8d8414b48cd51ddecea36738415f354777b0e8d8415f35477169ec3a361057cd51dc1e7 else 0x2c3a36103f0d51ddac39ce106c95f354777b0ec3a361057cd51ddec3a36108415f354777b0e8d961e557cd51ddec3ad68d8415f2f4777ad68d9ce1057cd51ddec3ab28d8415f2ac777b0e8d8415f57cab1ddec3a361057cd5264777b0e8d8415f35477075ec3a361057cf71dc337))) else (if i < 68 then (if i < 66 then 0xb0eaca36104d4d51ddec3a361057d35354777002c3a361057cc118dac3a361057cd5298777b0e8d841e557cd51ddec3a360257cd5354777002c3a361052cd518dac3a361057cd518c2d7b8ec3a35e557cd51ddc00a36738415f2ac776b0e8d8415f3548b1ddec3a36107655f1dc397 else (if i < 67 then 0xa36739ae1057cd51ddc00b0e8d84153354776b0e8d841a857cd51ddec3a36478415f354777b0e8d841a757cd5135ec7b0e8d8415f354777b62c3a361057cd51ddc00b0e8d794fc3547760028d841b257cd502dac3a768d8415f354777b0e8d8415f4b4d5135ec3b0e8d7955f354777 else 0xb36c3a361057cd51ddec3a36248415f354777002c3a36106115f1ddac3a35e557d35354777a36738415f354770cdec3a35e57955f354777b62c3a361057cd51bdec3a361057d2d304777002c3a366b4b4d51ddac3a361057d023547770028d9ce104d4d51ddac3a361052d2d354777)) else (if i < 69 then 0xb0e8d841b257cd5135e8d9ce1057cd52ac777002c3a355f35477091ac3a365f8415f28c777a36738415f354771ddc00b46738415f354776b0e738415f354770b9c00b0e808415f354776b0e8d8415f35463095ec3a36418415f354777b62c3a35e557cd51ddc00b3a738415f354776 else (if i < 70 then 0xb0e8d94e1057cd51ddec3a36106c95f304777b0e8d905e557cd51ddc00b0e8d8415f3545a6b0e8d8415f354c118dec3a36106c94b354777002b59ce1057cd51ddac3a36106b55f2ac777002c3ab21057cab1dd800b0d5f35477094196ab2a8a361057cd51ddec3a361074535354777 else 0xb0e8d8415f35477019c00b0e8d8415f3dc776b0e8d8418457cd51ddec3a361057cde1dc0b7b0e8d8415f354630e5ec39ce1057cd528c777002c3a361057cd5265adfb0e8d8415f348777000009ce1057cab1dd6c3a8e8d84142354777b0e8d8415f3549b1dde8da36738415f354777))))) else (if i < 83 then (if i < 77 then (if i < 74 then (if i < 72 then 0xb0eac8415f354ab1ddc009ce1057cd51dc336b0eafa361057cd51ddec3a361057cd51342e7ad6b1a361057cd51ddc000027384135354775b2e8d8415f3547718dc009ce6b8415f354776b0e738415f52cd51ddc00b0e8d8415f3548b6002c39ce106c95f355ac3a36106b535354777 else (if i < 73 then 0xb0e8d8415f434d528dec3a366b97d5f354777002738415f354771ddaa3a7e8d8415f354777b0e8d9aa1052cd51ddec3a361057cc11dc2e7002d8b0de557cd51dd800b3a8d8415f304776002d1a361052cd51ddac3a361052cd51dc2e7b0e8d8420257cab1ddec3a36438415f354777 else 0x2c3a361057cbd1dd800a36738415f354776b0e8d8415f35463115ec3a361080935354777b0e8d8415f3dcd51ddec3a361057cd528c4d7b0e8d85d5f3547702dc00afe8d8415f354776b0eaca361057cd51ddec3a361057d5f354777b0e738415f3547706dc009ce1057cd52ac776)) else (if i < 75 then 0x2c3a36106c95f305800b0e8d8418657c636002c3a36106c94b355ac3a361057d4b3544d7b0e8d841a135477115ec3a361057cc128c777b2ec39ce1057cd51ddec3ab28d7955f354777b0ea3a361057cd518dec3a35e557d5f354777b0e8d8414b354a31ddedeb0e8d8415f354777 else (if i < 76 then 0x2c3a361057cc71ddac3a36108355f354777b0e8d8415f52cc11ddec3a361057cd518c0b7b0e8d841d157cd51ddedfb0e8d8415f354637b0e8d99a0257cd51ddecea361057cd5304777b0eb39ce1057cd51ddec3a36107655f48c777b0e8d8414b52cd51ddc00a36737955f354776 else 0xb0e8d9220257cd51dde8d9ce1057cd5354777b0e8d8415f474d51ddec3a361057cd518c637b0e8d841ad57cd50cded8b0e8d84157354777002c3a361051cd51dd800b0e8d57cab1dc256b0e8d841354c0d51ddc008415f354770640b6b0e8d8418157cd51ddec39ce1057cd51dc197))) else (if i < 80 then (if i < 78 then 0xb0eb4a361057cd51ddc00b0e8d4d4d51dc256b0e8d8418657cd518dec3a361057cd51dc357b2ec3a361057cd5135ec3a361057d27354777b0e8d841ad57cd51ddec3a528d8415f354777b4ec3a361057cd51ddec3a36428415f354777002cba361057cd518dac3a361057cd52f4777 else (if i < 79 then 0xaaa8d9ce1057cd51ddec3a365a8095f354777b5ac3a361057cd51ddec3a36106cd5f354637b0e8d841fd57cd51ddec3a361057cd518c327b0e8d795ad57cd51ddecbb0e8d8415f304777b0e8d8415f354c71ddecbb0e8d8414b354777b0e8d8fe1057cd51ddc00002738415f354775 else 0xb0e9aa361057cd51ddec3a36108095f354777b0e8d8418b57cd51ddeceb0e8d82d5f354777b0e8d841d957cd518dec3a361057d23354637b0e8d8415f30477065ec3a361052cd51dc197b8ec3a360257cd51ddc00002737955f354775b0e8d8417357cd51ddec3a361057cd5134197)) else (if i < 81 then 0xb0e8d8415f354771d1ec3a360257d35354777b0e8d8ca1057cd51ddec3a36027955f354777b0e8d9ae10764d51ddec3a361052d2c354777002738415f354d51dd800b0e8d808fc354776002c3a355f3547708dac3a361057cfd354777b0ec3a360257cd51ddc00ac68d8415f354776 else (if i < 82 then 0xb0e8d841d657cd51ddec3a361057d2d3546370028d8415f2ac7702dac3a36738415f2ac777b0e8d8415f4c0d51ddec3a361057d57354777b0e8d8415f3f0ab1ddec8b0e8d8415f3547770028d8415f3548002dad8b0e8d8095f354777b0e8d8416857cd51ddc00b0e8d7855f354776 else 0xb0e8d8417657cd51ddec3a36104d4fc354777002c38414b35477065ac3a365e8415f354777b0e8d8415f3549a1ddc00a367384130354776b0e8d84135354770c5c00b0e8d841b26195f6002c38415f3544d065800b0e8d8415f2e0776b0e8d8415f48c770b9c00aaa738415f354776)))) else (if i < 89 then (if i < 86 then (if i < 84 then 0xb3ac39ce1057cd51ddec3a36106c95f354637b0e8d8418757cc11ddec3a361057cab1dc4d70028d841353547702d800b0e8d8c55f354776b0e8d9ce104d4d51ddec3a366b8412d354777a36738415f35477121ed7a36738415f354777002c3a355f35477095800b0e1057cc11dc196 else (if i < 85 then 0xb0e8d8415f544d51ddec3a36104d4d51dc4d7b2ec39f61057cd51ddec3a361070d5f4b4777b0eb59ce1057cd51ddec3a361057cd5294777b72c3a361057cd51ddec3a361057cd52e0777b0e8d841b857cd51dded1b0e738415f354777b0e8d8415f35477059ec3a361057cd51dc247 else 0xb0e8d8415f47cc11ddec3a868d8415f354777000009ce104c0d51dd400b0e8d840fb354776b0e8d8419757d2d355ec3a36106a54b354777a36739221057cd51ddec3a361057d5c354777b0e8d90e0257cd51ddc00b0e738415f2ac776002c3a361057cd51d1ac3a361057d24354777)) else (if i < 87 then 0x2c39ce104d4d51ddaceb0e8d8415f3544d7002738415f35477121800b5e738415f354776002c3a361057d230b9ac39ce6b8415f354777b0e8d97e1057cab1ddec3ab28d8095f354777b0e8d8415f35477041ec3a360257d5f354777b0e8d8415f354630b9ec3a361073d5f354777 else (if i < 88 then 0xb3ac3a361057cc11dded8b0e107955f354777b46c3a361052cd51ddec3a361057cd51dc207b3ac3a361052cd51ddec3a36568415f3547770028d9ce1057ca61ddac39ce1057cd51dc337b0e8d8415f354a21ddc00a36738095f354776b0e8d8415f35477029ed1b0e8d8415f3544d7 else 0xb0eb5a361052cd51ddee3a36738415f354777b0e738415f354ab1ddec3a361057cd51dc317b0e8d8415f354a318dc00b0e8d82d5f354776b0e738415f354771ddc00a36738415f354486b0e8d97e104d4d51dded1b0e8d8415f304777b0eb5a361057cd5135ec3a361057cd51dc467))) else (if i < 92 then (if i < 90 then 0x28d9ce103f0d51dd800a361057cd51dc0b6b0e8d9ce1057cd51ddec3a361057d4b354637002c3a361052cab1dda8d9ce108415f354777b0eb5a361057cc11ddec3a366984135354777b0e8d8415f3f0d51ddc00b0e8d8415f2ac4d6b0ebfa361057cd51ddec3a3610734d528c777 else (if i < 91 then 0xb0e8d8415f3544d0cdec3a36737955f354777a36738415f4d4d51dde8d9ce1057cd5298777b0e8d8415f54cd51dde8d9ce107955f354777b62bfa361057cd51ddc00b0e8d841353544d6b0e8d9ae1057cd5135ec3a35e557cfc354777002739221057cd51ddac3a361057d233542e7 else 0xb0e8d8414b354770cdec3a365f9215f354777002c3a36104d4c11ddac3a366b8415f304777b628d9ce1057cd51ddec3a36106c15f354777002c38418657c77065ac3a36026b55f3547770028d7955f3547702dac3a366b8414b354777b0e8d8415f434d51ddec3a366b57d2d354777)) else (if i < 93 then 0xb0e8d8414b354ab1ddec3a361057cd51342c7b0e8d8414b354771ddec3a361052cd51dc387000009ce1057ca61dd6c3a361057cd52ac4d7b0e8d8415f304770cdc00002738095f354775b0e8d8415f2ac77095ec3a36106a95f354637b0e8d8415f35477135ec3a361057cd5274777 else (if i < 94 then 0x2e39ce1057cd51ddac3a8a8d8415f354777b0e8d7955f35477135ec3ab28d8415f3545a7b0e8da361057cd5135ed2b0e8d8415f354777b0e8d8415f304ab1ddec3a36106355f354777b2ec3a361057cd518dc00002738415f354485b0e8d8415f304771ddec3a361057cc11dc387 else 0x2c3a361057cd518c197000009ce103f0d51dd6c3a36028095f354777b0e8d8415f2ac770e5c00b0e738415f354776b0e8da361057cc11ddec3a36898415f354777002738421057cd51ddac3a368d8414b354777b0e8d8413535477095ec3a36106295f354777)))))))
def level6 (i : Nat) := fld (level6Chunk (i / 12)) 74 (i % 12)

def level7Chunk (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xb0e8d8415f3547702dedfb0e8d8415f354777002c3a36106195f1ddac3a8e8d8415f354777b0e8d8415f35477115ec3a361057cd51dc397b0e8d8415f354c11ddec3a361057cd51dc257002c3a361057cc11dd800b0e8d8414b354776002c3a361057cd5135ac3a365f8415f354777 else 0xb2ec3a361057cd51ddec3a361057d4b354777002c3a36106c95f355ac3a361057cd528c777b0e8d8415f354770b9ec3a36106c95f354777b0e8d8415f4b4d51ddc00b0e8d8415f354636b0e8d841d957cd51ddec3a361057d23354777b0e8d8418657cd51ddec3a361057cd51dc637) else (if i < 3 then 0xb0e8da361057cd51ddec3a361057cd52ac777b0e8d8415f354771ddec3a361057cd51dc337002c3a36104d4d51ddac3a366b8415f354777002c3a361057cab1ddac3ad68d8415f354777b46c3a361057cd51ddeceb0e8d8415f354777002c38415f35477065ac3a361057cd51dc197 else (if i < 4 then 0xb62c3a361057cd51ddec3a361057d35354777b0e8d841e557cd51ddc00b0e8d840fc354776b0ec3a361057cd51ddec3a36108415f354777b8ec3a361057cd51ddc00b0e8d8095f354776b0e8d9221057cd51ddec3a361057cd5354777002c3a35e557cd51dd800b0e8d8415f354776 else 0x2c39ce1057cd51ddac3a361057cd51dc4d70028d8415f3547702dac3a36738415f354777b0e8d8415f3f0d51ddc00b0e8d57cd51dc256b0e8d8420257cd51ddc00002738415f354775b0e8d841ad57cd51ddc00a36738415f354776b0eaca361057cd51ddec3a361057d5f354777)))
def level7 (i : Nat) := fld (level7Chunk (i / 12)) 74 (i % 12)

def level8Chunk (i : Nat) : Nat := 0x842c3a355f354776
def level8 (i : Nat) := fld (level8Chunk (i / 12)) 64 (i % 12)

def number : Nat → Nat
  | 2 => 48
  | 3 => 547
  | 4 => 2233
  | 5 => 2923
  | 6 => 1139
  | 7 => 60
  | 8 => 1
  | _ => 0

def hashes : Nat → Nat
  | 2 => 0xff8778dcfdf21f54fd0eb083fb42915df7db57d4ec46408ce574067ddcd48323d8620efcd70251aad5995234d427bab0c3d2505bb20307a3a74479a9a1beba0ea1718390989a1a45924dce4d91a802538ecea705846ebed57fe6a6727861666877a3ca5a777dfb2d619c47645f39eab25ec4786f5d727d47553f2457508d1d464c43b0204ab05bf44a4e2a474a1fcff048f43eda45dab529452e1b423dba2d45392e01042f4408792c5ebeff234a5f231fb2b68b1aaf6768155df89e0e48a399
  | 3 => 0xfe176700fdbf2f37fdab9a33fda45b2afd617a2efcb71684fcacab98fc8881e5fc74507afc619167fc554f73fbbcbbd6fb6e8209fb18af16fafff6c1fa46f1c6f9157ff6f8e1b0faf8b88941f8965658f83f0f2ef73adc63f6df90b4f6c98ed8f5f4f86af5e62007f5478462f51cd0b2f50a9aa1f4f70704f29da5c4f287a516f26f22f4f24f9b04f24b09eaf1241657f0f70e5ef0e8f147f074f4ebf04486caf00bbc93ef792f61ef4f37b2ef3ef3eeef2d9e4def28f7b5eee6c78deecf3483eda4ef0fecceca31ebd5ab6ceba0f0f6eb1f3d92ea4687bce947c5dae8f65645e8737467e8728572e819c70ce804d245e7cf33f4e7c948dee7590261e6b2d71de6a4f3cee677555be60c128be4b224c8e475d76ce4114ffbe24c4935e1e06534e10d96ebe0b171a0df922928ded7a196dea31decde4b7601ddc97dcfddb5f9dddd6a1cdddd2361b2dcf113e2dcbb0af2dc367773db1b188fdab1d367dab16519d9b810e1d9a240f7d98c2faad964a055d812bad7d7a5bd6bd77415a6d73e067cd6f7179fd6a541abd67a1264d653d15fd62091add56454a0d51811d1d3f08d75d35f16cbd33a8b5cd2483cf8d216cc00d197b7d1d10e180ad0c3da32d07b80dfd06507a2cfbbe2a8cf0ab604cea9fe53ce71a335ce18cc22cdaa7c38cd1b14c7cc9824b1cc88cff7cc25f987cc1ee2a3cb8046fecb173502caa44dc0c8146d97c808c356c7de6858c6e91940c5b67dd7c4b4bf75c48df322c44d5065c39ea2d1c36bd0a6c365fd6fc1993e1cc191f953c0a9c6f3c0961541bf9afecbbf893e28bf64ceb7bf12f8c3bebbba3cbe62253fbe5626d9be320493bdf8d74dbdf57455bdde8ec4bd45928ebd2fade7bcf4239bbcbeab77bbb7219dbadbcf1bbac2844aba440ed6b99d0178b992e04cb95bc7fbb90b5102b890bf05b71c796cb680dd33b63bbde6b5ea9cfbb5e99ee2b5a8d2b3b5583bdab547a5edb4d50737b4156c61b06ef8d1b0557f3eafad3fbfaf7097efaf4878faae1113ebae0f0129adcd8001ac8ab8f9ac783a7aac1745cbabfd2b3cab8740bbab27f7afaa49f921aa14749ba9c78aada986a3fea875f168a7fa975ba7e1daf1a5cad480a4c52afaa3efc13ea3d0b14ea34b4bc8a329410fa2e212c0a2ddb676a2b09a55a196cd25a180a830a126b364a06210c6a019d8f09f88ed4c9f79f3129f2f45b99ded95ea9d42be4f9ca0a47e9c3ea1669c39a1ca9c20ef389bea5f439bac983c9b4027159b20603c9b0a6d399a5ed3a99a3b6ae59a0d51d699328b6a9915b753990c3fb4986ea92d97206bfb9700aea996368edb96341d8d95b037e59588107d95165386937e40a49349d64b93174cf492f24ea192df7e079217400e920338ad91e907d7915cc9449133e84f91058e9f8ffe67918f35bcb88f138e578eb2ca738e815d718cd723418baf02d98a5f34988a5de00d8a4e2efd89bb7faf895185748905d2ca88d4ff1d88c7d2b788b4c55888820ecb88123e1c87391ffc851e26bf83ee56548369a65682f3f4548278cb61825ac6f181f0a20a81c3fa8981a20fb38194cb3881084b7780689dc780077bf47fed9cee7fcf31f17f943c177f706f9a7e783ccb7e1a9d8d7da73ee87d840b827d82d4dd7d462e597d2067407cceed157c9496617c0542007b85695a7b0ad7be7b068a007ae966847aad13bc79a13f8a7889d24e783569b27748629476b947ee7606874d75e58d6a756495ca7543e8b6751b7037751753f8748028ab7454f130743440a87381f80e7363f48272db0d4c71db8c3871d893e17196d9c271595322714490a57066b4c1704e85996fc493bc6f2bee386f25642d6eec42ff6e6a8d946dacfcb36d5994eb6d30adb26d2192956ce6807a6ce231126bbf67916ba5a7916a86e8176a7f80246a70188169ddadd868b41e82688e2c6167a042f1678172d267476ef866987493664f010c6642fcb764bcac6064a2eeba64176c6762d2046e61bdf746619f5cf46198e4306194842c61585f86610d5ada5f97e3855f82dfb55de9ed6f5cf849355cbd636b5bbc38e85aeef5d45ab06a3c59627aa958d0556458bc3cb157cd8dd4579c291956fb1e02568e14e5547d1f1e54729e815447a6fa53f59988535d1f3a52f98958524b7fcd5219855251cd0a595170676150d5085c5051bc09503af8c84fcd672c4f79ec554ee3aa004eb511834d82f19f4d6aca104d45a60d4c92783d4bba58834b9e70804b86ca724aee6fac4a1bf06b49e71b2f49475c0548d5373348493142478c1b504767ddb54760e3d54712733f46cae88a463fc99f4629267b440a391343c41e3441d05eba41cbae5e41a9f84b40f44b8040c2f6c6404e460e404504313e75e3d93dae758f3d88cbd33cd2cd533cafae843c4a1b213c2a71433bdf4d713bb0559e3b9fbbe83b497b4f3aa25f933a6b0e433a3c08183863b44c3719502336b17fa236743ea935fdda0134f4bca63436eb45338bbd30330e186c31e7cf2c31c18ee331ba71de3117f65b305782dd2fa635bd2f0d0f322e4d60572dab4b7e2da889cf2d74068b2d73a58d2d00c2152c3076a42a5f96772a173e0b2958cb3328e2abac27c80cae277040622673b76925bc97102583f93f25362e8324cec01924c1f0412470b613234c7ff421e6db9021c4bb5721927a8420e23e6b20b2643e1f43a8641ef55db61ef4a2c11ea1d2f71dfa62511df52aa71dc72fdf1d95a0641d4a9f3d1c9f6ec71c46fc391b2d699e1a898a6819b51a5f199c9f33197cf6fc193959041923c49118f106fb17c4d0271632253c15b92b5b159424e21492ea0713e3edf013c7e94213620f4512838050126c7f2b12301c4c121bba131186d40b11176c57101d88e40f4ad4370f235c9e0ed12fab0e48b2f00e075ca50d882a6c0cde6d2b0c92db540c9045710c8eed1a0c6adbe90c36b5510ba045910aa7f9fa0a7c14700a217dfb0986c558093ba0d1091dc5d9089b8af707a7a2e707988a4b06ebe0b106d6d7da062040930500d39503ea916703d1d58802ce987e02c4fb1402b1867f02a625fb0227ba51019f1b3a00be550800699e02
  | 4 => 0xfffa5208ffeb3c4effd479ceffb365f3ffa2d019ff35fa61ff2fed55fed3214efec839edfeba28a1fea5bb13fe9b2a97fe9ae320fe944f95fe8ef1d9fe8670d3fe468d4bfe30713dfe176700fdfb8931fde0a768fdafdc3efd92e3dbfd6b1506fd61a60efd25aa10fd168705fd08fdd8fcf68c84fcecafbbfcd60472fc895d96fc74507afc6de08cfc23559bfc0fe5c5fbfb0307fbed75f1fbc4d320fbc1aba9fbbe593dfb9d968dfb76ae1efb70614afb526ecafb27a830fb246e72fb211e22faee8c94face1ce1faabc740faa9df46faa4d3d3faa2e566fa8cca0cfa7b1232fa6ccf3ffa585038fa3f9792fa0cea1bfa05304df9e205bef9d61e32f9b08d3df9a1857cf99ca0a2f99c5c39f96b280cf919171ef9170c3ef89ebe84f89df0c4f898cac6f8933981f86cd580f8509982f81b1abaf7e975cff7c5d492f79efc8af77ebf37f774e860f74c3aa4f7277f07f71982f6f6c0a8ddf6b58a97f6ae5759f66e56b3f6667806f62f370bf62219a4f5f0f7a2f5e36636f5ca42b5f5c94f68f5c6b33bf5b4541bf57d1551f57566eef542317df512604bf4e2adb8f4d99703f4d30af3f4cb3bc2f4c36133f49b5adff4867feff485c1d8f46b14cdf4364d11f431e0d8f42f946ef424f336f404f857f4016a6bf3d5e341f3a4f17cf39cfe50f390479ff3888cf1f35f29bef3473f6ff33e22aef335c8cdf2bdffa3f2723331f25d3923f24f5252f24798bff214abbcf19caa5ef19b0c28f187e120f1529132f11d7237f118fa70f0f07720f0cdcbdbf0cacd64f0b30e34f0b14c8bf0a59bcbf09a6e27f042a28cf02e34feefd2b38defcf03b9efcd7b2aefc3d992efa78195ef97012eef4b0aa8ef4af10def35c12def241db6ef1b5dc6eef2572feeef38dfeea83016ee7529a6ee63c922ee4ea0cdee42ce1cee3d9b8fee2a64a4ee0fc7a4edee7416ede46124edb03c81edad0fd4eda8baf9ed80f822ed804965ed46d328ed25fc93ed17df81ed158000ecc0b29cecbecf3aecbb62abecac9ef1ecaaed8cec7a162fec68741dec5343f1ec478d04ec44f5f4ec057f86ebf5492aebe4ce16eba3fe4ceb3db486eb288c31eb1cb980ead71f5ceabb0cafea70ece1ea66593bea5b51b4ea5ae386ea33dd8eea24ed23ea184abcea128fbce9f38133e9df15c5e9b6403ae9ae8d07e9ad38e4e99a9e00e980b444e9618462e960b965e938e43be903ecf3e8fec2c6e8edbec0e8ce2347e8929964e7df2b13e7d71edae7c948dee77e6843e7612dcde740d3c7e740cf11e740449fe7321bb2e6c4fb33e6ad6e88e6405c14e61e7e68e5f824b5e57bb8cae577961ae55f30b4e55ddea6e55b207ae529d0bde5067d0ce4fc736fe4f65dfde4ed54d6e4e222dce4d1918fe4bdd283e45d8c31e41e6321e3f9f7e0e3f12ff4e3f00653e3efbc0fe3cf1d5ee3ac27d3e364c30fe363cc81e333f333e32f392ce2f869cce2e8374ee2e2dc39e2d21019e2ce1202e2af1e11e25d45a9e249e1d0e225620be1fe123ae1e1f80be1d00501e1aec9ebe18f61e8e17d2113e149eba2e136dfd5e12877f2e121567ce11bdfe7e1112767e109aa83e0ed4d0fe0e96474e0e4b2f5e0b6081ce067a187e03c5c75e02b963de0245c73e00c7e6edffc87f9dfb2de8fdf727835df5501a8df4dc7dedf31c945df2c79b9df23b19edf145eefdea9f065de8d9d8ede7fdc3bde73cc32de2d5475de1c61f6ddaf773dddab152bdda19808dd9a91a9dd7fb12cdd6f79dddd6c12addd646e38dd593f9cdd0db2f9dcf113e2dcf0048cdcea8708dcae1826dc4a8577dc24ad3ddc06651ddbee4a53dbcdef5edbaa7eecdb9173cadad6a442dacd3894dab241f3daa3c817da85008fda4bbca0da4a8841da40bca8da33de90da000fadd9f4846ad9e51d16d9c44808d9b5b8fad9929c49d9691766d92470dbd91004ecd90ce486d900b191d8ff3a78d8fe98a1d8fca317d8b0a83fd88f9062d86a0084d84a3069d810c1aad803f1d2d7b2b7a4d7b08fa6d786f6ced783a02bd78395f4d777db9fd774c3fdd75f9db2d74be68ed73928d9d725a804d6e47bd4d6d9fb11d69fa002d68e8185d676b86ed66e1360d65a1083d658eb0bd65563bcd6464c6ed627efa3d62651a1d6007f52d5de1b84d5d11156d5c90b6dd5bb205fd591aeefd58b4260d5801d81d549d898d53c829dd528dd21d51250bed4fa7cc1d4f5e0c9d4edf046d4ed3cfad4e21ab1d4a335e8d47b9fb1d451c703d44024f1d4344bcdd425f4e7d3f27bc0d3d1856ad3891583d35af429d352d756d32f4f20d31dd514d3003d05d30029f0d2b213b2d26978e3d2419d09d236a452d226388dd217cf90d1fc1cd7d1e3d488d1d46299d1c84ddfd1b15f3dd19e188ed17933ebd1612c13d13c63e2d1372c38d11cf228d1093170d0f80f89d0e3f433d0dacaa8d0cfec15d0cc69edd0c58ca8d0920eecd077ee6ad0714b73d064ae96d0591c4fd0152ecfcfe17058cfbd9c2ccf88fdcacf80e5e6cf7524d1cf66e973cf545fe6cf1c4f6ececad3a3ceab1b86ce7300f3ce71a335ce5035fdce31f365ce09f58dce026ef3cdf08e3bcde21be1cde07eb1cdd7bf26cdc586ffcdadaafccd8e2b1dcd59ef4accf71bf0ccdea0c4ccbef88dccb03ae3cc8e5290cc7c329fcc6f61cdcc65c622cbf423d1cbeb1497cbe77d9bcbca128acbaa1daacb6eb93ccb5e3862cb2ddfe3cb06d1b8cabf428bca4c03b1ca4a7c69ca3e984dc9dc27cec9da4f3fc9b03b15c96e8b69c93e915ac92d4678c925d8e6c8fb2cecc8d62673c86750cac83dd3adc8146d97c7f41358c7dc73bec7d4eb98c7c77c0bc7690390c768f959c73b8713c736c3f7c725ef81c71ea92dc719377ec709ead3c6de5e67c6d844d7c6c975c2c6bdd26ac6a8f0f5c6a410d6c69acaa9c6850367c666f79ac638b63bc626eddfc603be4fc5c581e1c5b55f69c5a13ca6c5711b82c55f525cc55dbba4c5542062c4fe3e41c4eaad74c4e2ba55c4c8d59cc4adec42c488a3dbc4828ba0c46d44dcc461e270c4596de8c43a8d9dc40fbc87c3f01957c3e4d455c3985ee3c38fa41dc37f95c4c36df3b2c350025fc337e444c3152ea2c301add6c2b060efc28cd5c8c28c068dc26987b3c2655e2fc25ea2b0c22e0bc6c20a59ebc1f6e693c1ea139ec1b50af7c1908e05c17ae709c1603586c15e9750c156b07bc1495e36c148bdfcc0ca2bfdc0b9f970c0b07c5bc0ac28a4c09d9024c09cdec1c0881e4cc07c8e45c076995cc07441acc0722967c06ce177c05db38ebfef1a06bf8225ddbf7083cbbf46183bbf3f39aebf1e4571bf15fcb7befe4832beeb9043bee24722bed80b16becf65dbbe7937a9be5fadfabe5096acbe38b4cebe309bdfbe2f37d8bddcd831bdbe1601bd917acebd7828d1bd738e82bd695df6bd637f8cbd45928ebd3b2945bcfb1f86bcf50206bc8c8fe4bc23f424bbf830d5bbec4992bbdd8c88bbc91eeebbb489c7bb779d8ebb15b8cbbae9a478badff335bad5c599ba7dfe9bba7286f1ba30696cba2de242b9f58e95b9dbd5e4b9d0a36eb9a76a06b97f9e56b9667b48b94c93eeb938f403b8f98813b8a873cbb87b5173b8631151b832b49fb8256577b80f79f6b777b9b8b75da19fb756718db747c69eb71c5127b6c9ff99b6c8cc10b6aed927b637d1ccb6134e00b6109a0fb606fca5b5f38810b5eba12bb5e8278cb5dcb563b5ba0bcdb5ac6f51b57df4ceb57cc316b5611f3cb55e14b3b50a60b9b4f5093cb4dee71ab4ba33f3b48ae8e9b3ba58adb3889c5ab37f607eb35446d3b3436114b32757a9b3272cb4b2eb94e8b2e3c418b2dd1255b2a0df60b295c454b26ccc7fb26c4e3cb23343a8b221f7b6b1f1d119b1ee3144b1bcfa5ab19a0c07b1941f57b182b427b1742157b16fe2e3b16aded4b1574cb9b1394d96b138f237b10af778b0ec031ab0cbd320b0a6b778b0a37bc4b09f2d39b0847f3cb048ccddb019b4b1b00c2f56b0042825aff9ca9eaff9181aafe7e79bafe4ad32afc8d58eafa80413af70ce1aaf2c647caf115306aef19705aeb9ac52aeb0839fae73f76bae54f459ae41f857ae12dd9badf2e9cbaddfed1eadc7449aadbb70b3adbb0ac2ada5be84ad8ff742ad84aa75ad74c37dad5e6aa0ad06a2beacb962adac7f0f0aac57818cac3338d6ac23b290ac1c35f7ac02c10babfb00dcabfa8ad7ab9397b6ab458178ab25ff96aadbf884aada0138aad50dd9aa7cddf9aa6c7b55aa66ff99aa602d5baa21924aa9baf1fda9660328a95cf06da93cdd50a936fa00a9296846a9006e52a8975ee6a8944a09a8819f23a857633ea8535850a805902aa7f5d03aa7b9d9e7a7a9ab59a74666b9a72c4c2aa7288fafa72328daa6d182dca6ce67c7a6b44cb8a6632b2aa627235aa62347a2a61d9baba5dfa75aa5da59b6a5c9a6aca5b45486a58d0b80a58c9695a54682a1a543a8a9a538b1a3a4d83bf6a4abc38fa496da22a47e825da44482bda43fbfeca4390ff4a4113e00a40c48fba40473cea3e9800fa3bfe64da3be23f9a3b6f681a37861a7a30b2e12a2ec49aea2cf308ea2bb7e39a28cd88ba2870d6da280f584a2759edaa272e92ba26f9fe3a258a309a229b373a228c923a2071293a1e46f88a1c6e537a1beac89a19cb7c9a18d4794a18548dda15e8219a15cefe0a121de92a0f3add1a0bd784ba0ae53a8a0adf46fa05a4a6ca050382fa02e816ca0276db9a010cbc7a008cf9a9fff18169fea310e9fda77759f9f32469f4f4d1e9f323b059f1ee22c9f15b65c9ee81e989ee0a2639e9b6b979e52b2d89db9cd029db6b98f9db068f59da1c62c9d9763af9d3435d09cd38d459cc6cccb9cc47e319cbdc6039c9da8ce9c47cf249c3857db9be433119bbbd0cc9b9e2e039b8fd9c79b7eb5e39b3be4159b20603c9b0b4a749ac166779aa4b89e9a8a54599a88e83d9a7350399a47ef979a41b1e09a2a49229a0e079199f1661399e6f56499a0b82f9969acee99689a31994e142199433c7599021c8298edd3dc98d61d5e9882562298760418986702889860f267985cee1d980e10a397e9c18797b7d90297b79e80979a458f9796f8ba9762d3a19756c77696f5178796c3f69096a67fdf96a20eee969e7865969616a8968a43f79675e05296609f90964d800196488e8f962c095396231785960aee7d95c86dfd95bb96dc95b71e4a958e4acb958cf6d895770f27956ce05d956490a895603f85953f83ca9533372795178ef1950828779504127e94c209759494c9d2948959489471776a945bfdf3944f988194402c13943464b2942cbf8a93fe18c593b120c093ac511e9394b6319380b8a393551bde93532f45933506d293301a9f9305f4b792c0837d92534124924da7389219a32c91e51f8291e3af3891e001b491dda21d917b47689172aaf991661c7c9154f914913ec5ff910b7f6590ffdb1090cd599a90ae513590aa90b290a7e412908f87e7907407839071e5719065634890471bea90457474903315789024aeba8fddd7fa8fd845558fbb854a8faee1378f9c567d8f778b188efc36318efb5cb78ee495bc8edeed5e8edc7ff78ec8087e8ea5984b8e8bd2818e65f4438e3f9a908e2dc79e8e2875488e24c8228e12f06d8df3d4fd8dad5f4b8d4b9bc88d3c36898d26a7ee8d24f1f88cf82b888ce8603d8cd318548cce31408cc532708ca1cdcf8c51767c8c11cba88b5515028b54bc6d8b3001ce8b21477a8ae7bf018ab6173c8a9950c18a3919358a30208d8a277a088a1621ed8a13099289ed66b289e7434189d6c97889b8231a899578f58986e1d689629343895af45a891ad13989062f1e88ce86f088c7c28988c61ecb885cf08a88443ca4881fb8eb881c09178810a0bb87fd2ede87f486f387d8f14387d1f763879c043b876831b1875bd4ca873c3e3d873b79d587391ffc87328f0b87212cc7871df25e871d089e870a0bf186ff891286fefe4186d852e686d05b6f86b2e2e186a11861868c5738860f377e85f28b0685d1934d85c78a7585bab33385ae471f85aa1129858f275c85725a3d8558cd96854d9a3c8546e0a685399aab851e26bf84f1c87384d45f4f84c49cfa84c0f04884a59d44849eba0a8491fb52846f573b845019a084359a6884345bf58416cb6184138a7a840675aa8404200b83f6f3a583cfbbfc83bd827583a70938839de64b83735c4983661c088350fe75834bb46f83076bb282ded69d82b35e9982a6b3508293327b826dcf1a8255d385824cb79a824a81e9823ef5728233c37882330a9d81dcca0481c6a33d8193dc1880ec7dce80c38061809d677a80518969804ea722804d47ad8039b37e8022774e7fc7c8667fadaf687fa798fc7f9a60e77f8d49fd7f67fb1d7f60e4397f47ba7e7f22e5097f1d77427f0ba6bb7ec5d2497eb6b5687e9cd9977e6dc77c7e5936987e3653917e02a9b47df083107d68e3557d53826a7d212a307d139ee27ccf9bd37ca4abc67ca081dc7c9bcbab7c8d750b7c7cedd57c5fdbaa7c4c08967c362c797c1c22bc7bf9073e7b9fbdad7b8112777b7f453d7b566f2d7b0e36d47b090ca07afc236f7af769257acb57fa7a96e72e7a8ece097a44e26d7a041b0c79f0d10c79d1acf279c03f5d798387f0797605c4796e5bda79645b887943f0ae7931b85379298e507921f7a678f87f6d78d606ae78bea0cb78b28e3578b1ada578ab823078820f16787d9ed4786b261378606cfa786011f0785b23be784c716477f6c10b77d56f8c77cff4b8778f51fb777ecea3777d31c57749624b7743a3ca7723e610770409dd76e7428976e0a46776add23c76a83a0e76a7ff0576992ce3766eed8f765e3b007637dab275ccb68a75bd390875a8fe5575a08d44759c046575524ff1754680c774f621f574de5b1774d3fae974b125d674afa1847462c89e743ac24474322fc974319bc9742218117407d1ef73e3a34a73c437f273a72cf0738787fc73837175735d5c96733df1ad733826647308798972a7eb167298c1fe727f478c727d106a723c86da722c3b55722b5ce17221216c71fdbbd271f3606671b72c157198286f718b113a718a705f7172914c711d08bf710c525c70fdad9d70fc037570e1bd5370c1aad9708ddce8708794247071af7d704e4c34703625317030c1c270275733702719086fe6cf8a6fa362b46f964edd6f72ad626f2db2b86ef923336ed1c6d26ebb18be6eb337d36ea5f0696ea18ca56e9fc5246e9a20fc6e794a316e1dd0b16e0a7ced6dd847be6dced8166dc389236dbd36046d9b963d6d86106c6d78ccda6d2b19836d2837986d1d09f46d1379666d0aad266d02ec716cf063766cd4e1e26cd27e506cc43af26c81512b6c7d4e186c5b7a9f6c4fa7ee6c4ef8f16c28f83c6c1747f46c027f216b8dd1f46b7da6876b7ca5ad6b60296b6b5ca47d6b48b9486b1204336b10b0ba6ad9677f6acd8c6e6a86e8176a7819586a74316e6a710fe36a36db6169e7144269d8eb5569a3f2aa699e265669801dbc697dbf7c693dfe78692c9e91692ba07869115c8c68ead449689a3d706889a783687aba876877801e6839203c681708cd68067e1167ad4caf67ab6d9567a425f267449cdb6729072f6722d29266fb7bbc66e9843066db02896699af1f666008ac664f745166396b7a65b85fbe65a29c6d659f396f659cae926585f24b657fbc0c654460d26537ec036522f4c164fb0e4e64ba891364a67e7a642b583a6407dce46404fe8763f72dec63ef61df63c36f9463bd4d4f63adfdae639780d463972014636a1035631bb6466303207662dc8aa762c57db862b9311262b29985629a0a1162904e89628918e96227549d61fd407361f8776061a73a60617592a4615a0a1661531581615102bf6150c0086143359f6126abde60eb7f4560b9f0e560b8dffb607d520f600f8c145fc2c21d5fba3c105fb6760b5fb2caa95fada3c55f89afea5f83c9555f6bae8b5f5947615f5706e45f4d37465f4b53965f3aaa1a5ec942515e91ed005e6d2ca25e6b75df5e68853e5e62dae55e572a0e5e38436d5e0264c75dd67b955dc67ac15dbe20e05da9382d5d728fe75d623f1f5d616c035d5dafc25d384bae5d2138c15d098c435d01a9ce5cefe62c5ce78c4b5cc8051e5cc462385cb223a35cae320a5c25e19b5bfb19115bb7f2fe5bb7eefd5bab1cd95b9e09025b91ad7b5b7f1c9a5b73ab165b4ccfa65b3c98f15b3115725b242f255ae4e3e85ad1300f5ab68d115aaec8595a5e11925a575f4959e181e259dff87c59a8ef6e59a3b5d9599edea4599e64a7594c9d3a593adbc7592be0d259190e5d58fd81b958cd214458cbf517588e96215879b779586c1747586bcd39585896725826ed2457cf2b3b57bd892957a986b45759400f57328f1b5727d5f15712b2e4570835f756f896a656e6f49456d9465356c065ee56acb358569bde0e568d4d5e567da13d566f710b566b42a55664de07564f2d5c5631aeb0562c34bf5624145655f3d7ae55f1cdf355c5fa4755b5de2d55a70ca855a16ebd5579c1bf5573135f55647e605520e2d154d8cebb5491263a546e5d5254623d8e54332b73541f704953f7e71d53db8dd053d715a253c6655853a4125c535bda8653223bcf52f8576052e1c8e552ca040652bf8d5752bbf4a852b00fba529fe5ab5253ad2351d7bde751d57965517f25495166093e514eb05750e9059a50a8a1bb501522e24ff5a68d4fed0e514fec0cd44fd3a4e44fb1148e4fa0d9fc4f80a2fc4f62ef8c4f5b3e054f5178684f2c60d94ef3ce6e4eedf20a4ee444cc4eba62a14e9115414e8228ab4e6261d24e33fb0a4e2bd9004ddb09374ddaa3ce4dabde264da0d53f4d9c0f904d80f49f4d7aab564d6841ee4d25e3f04d034dac4cbb5d644cad90484c748d004c57b8e94c54b7484c03755d4bb0aac34b13c0754af798d04adb9bfc4ab48f324aa0e2014a5ee4334a5c2bf24a5314c44a5259314a4e2cda4a4a99db4a42b03f4a3b36a24a1b45f64a156f704a12caee497890714964a20d4961a85c4932009f49261c3748d1849a48ca121348bb09064858551c4836903847f0c0d8476836814759dc4d468bd7e146870ed046217f9d4617121545f6409a45e94d9045e6f7c845af794545ab6ffe45a602c6455f8f8d455b8246454b115945453a4345169162450e42a644f5442244d56cda449ecada448c7fe0447a6325446c5fde444c2acb4447903543fd801e43ee959d43e3fd4e43751dfc436c2c2e4360fa34435cfb714354815143079f3442f528b742d74c9f42cc686d42899ee942561cbd42509d3842500a90424c321442409b92423ae23b4235d929422f0f8a4224a9ee41f4cc0941c35f0741a892df418cab5041817be4416d39904160963d41220874410922ea40e4e33b40d76b8240acf40a40a7ae1f3feae25b3fea1d273fc0aa853fb783b43fa1585c3f75950d3f66fbc43f638a4d3f3729fa3f1f61403ef1046f3ee13e7d3e9f00783e529aa93e440ef93e39f2ec3e1ff0d93e1a61c13e1329d23dffd1dc3df77e873df76dcf3dcb59c93dc76f273da1362e3d9fe1a33d9030933d88cbd33d840bfd3d636be33d61c9cb3d566a7c3ce3df803ce118313c7184293c5468013c1700b33c0d4aeb3c05bbcb3bf6c6ee3bdb5f093bdad31c3bc60a493bc410613b7d66fc3b61acfa3b543fb23b327b523ad159333a7b21923a65b00d3a37bc963a26af043a0abfd639efb2c139e4662339c10da339a351433988f33a396459e43910bb2538fb590638f7477038d966e538aa13f1388125b73863764138602855383b985e3824c47138177dd337ec075037e8cdac37c1b80437bf00f337a440323773e89737009a6836b0e33c36973b473635f5ea3618a20e36052f9f3604a52935f3002835e4ee0c35bc466f359cc887358b3edd35554a833538fa293532a3a0353218793511838f3505fc1f34e4114934c4f00734be997634b39798349742f9344aeeb7344a4d0d344171673400d6fe33cb680c33aa9f5d331fb9ed3318bb273311338732ec117d32ea8abe32d63dad32c70dc532c0ae9732af8781328eb73e327796683253d9b132206d58320a0d5331cf376c31975699313de180312322bc311ac70e3114e2e830fc279830e8477e30dcaa6130d78e4430c60d1830be8670304c8e273049830b30481a8c3040dd37303cf47a3036c6e5302cb7bc2fde79a22fd697f72fc5fce12fbb776c2fa9dae02fa6e5d92f71aa822f4743962f10fbee2f10329a2ec2e5b02ead15c62e9c23e02e91590e2e69921c2e4b630e2e488b962e454cf32e3a67592e37fe0e2def15522dec511b2dea5ecc2de535412db22e492dae4da42d9cd5232d8a05e92d4a22612d40f8932d290f5f2d2205f02d09ff402cf9288a2ce6709b2ce341202cce82ca2cb371542c0b371e2bbad2242b7f683a2b776b482b678d8f2b641d0d2b2b6c442b1523732b105ace2ab544f52a94bb372a8cf9142a8a642a2a328ddc2a12930f29ff27f429fb4984299ff7be2972769c294888e3294388ac29094e8928fbb8a328f8df5b28f5a4f228e8d25628c10ce128a69760288f77562881295928795527285d71cd28536c56282c665f280906f827fce13827fbe69527ea784c27d562ee27d34ace27c22a412796f2c627769397275f9792275311c72725520026fb962c26ddc46e26c3f9a426a5f61826a28ca0269e9a6c262e6929261d0ee2260534c425ea930425c35f1125bc971025b170cb255a10b1251d8dce249b54b8247304a924305732240c335b2406817223eb294b23e6f66823e68ddb23c972762390872f237c7804236f2b87236bf738232038b12312357223119454230def572306955222e5c6f722dec030226defce226765c32260082f223ba0dd2230f942222e449521ae6749216042472142b0712114c7e72101d75b20eefe49209b96812097b707208e67fc2072af482054656a203e335220292bbb20288210200b50c31fa930e11f9fd7011f749fb61f6f4d381f6ac33b1f267ab41f0169271f00a0671ef3cba21eeb51761ed7a9a11ed057b81ec3fce01ea5b0db1e92792b1e90cf011e8615351e54a0691e0e271b1e07b8911def64281dc8e9ad1dc181ba1dba8b5d1db21a171da52b3a1d99c5cc1d9705c21d76499e1d6f694e1d5d89e11d56b4011d3123fc1d20e65a1d05183d1cf89bb11cec775d1cc6d8d41c5f3c1b1c4fd4b11c4f47ca1c4787d21c42f23d1c3b15ca1bf620181b6dfcaa1b6d53541b6aba651b5787951b3981fd1b29c1c91b182d4a1af65bbb1ae352be1ae037d91ada39ba1ad74b9d1ad3a69d1ac374681ac14b9b1a89708e1a4a3a4e1a0d4f9b1a0b65c019d981aa19bbe491199102a21984fe4d194061d0192533841915012e18fb59e118f936a71850e62a183a8fc2182b068b18163db8180f69fd17ead88f17e7d29c17a99d24179864bf17596dfd175728ec1701701016fd97ba16ea8369168ff22a1687f005168358ef1673dc5a1665a60b165eb47a164a265015fbaef715de9a5a15acc45a15aaf1301542f1e9152937ec151f3b371504f1ef14f0291c14ecdba414e43b4d14dae5c614b3a9b014ac1adc14ab88ef149a611c1439b1e4143834f6142c624513fb656913e46fba13ae638113a118f9139a36871388443313828023136a8c4b1361db691351d99c134257341318b514130a86df12d9e51b12cb2a5c12aa46c512951e701290155e121395b811fe6d6311f29ab211e88cbf11c775c5118d95141145a5ac1130c4b8112bef05110ecce510707f32104158f1103a4acb101b9b7b0faaaaf80f9fbdb90f30fa0b0efe3a7e0ef8461f0edeeaad0ea960450ea40d200e9130330e51babc0e4b96a00e1625d10de8b8490dc161cc0daca7380d9386250d882a6c0d8464ea0d094d6c0cf676950cf586df0ce91f790cd296930cbcf1900ca823a00c9110a60c8eed1a0c0812910be1b8de0bb8d6110bb14e360ba9647f0ba6d3500b9d3ef30b8262160b7df8840b7690910b445e7c0b2400820af8b2a80ade2aaf0ad9cbf30a7c14700a3ea2580a3d1f980a00b69209d0167b09ce4afe09b0db9409a9382e09a7f14b097bd886096afc0a0959b28409367d9309201df7090c3abe08e0bd4608a675610879a4a008740d3c08541b350842cfef083cfa5f08358f9507f4851e07bf20b4078f8500076a26ec0768d7a90768159e074f85ad0742b92406e4eea6069b193f0675558f06354348062e4d85061682a405ec6e7a05dac2c605c195fb059d6d060599ff2705864d75057fd19705644ef205114050050f0bef04b8148e04a254b804a11c8f049ea4e4047722c00470c0aa043aabbb041df7dd0411c5aa03e0c8ce03caabe503beda0a03a955cc03a15fd60394a954037fec08037d0010037cfa5e0372f75c0350656d02dc464f02c946f102c51eb602c42b8502c3365b02bbedeb02aee61a02a5edc0024e689f023419a00225ab9601f9211901f192ce01eb2bb401e7b11701b5a8c801ad4ee70180361b015ae1c10114971f0112a89100bb63d500a4e4d1007aa8ec0079f022006b50780054f32a0048d19e003550c9
  | 5 => 0xfffe1d3afffd5ef5ffef91d9ffcf3188ffcad027ffc8b5aaffbd11d1ff96b8d9ff4a75f7ff4576eeff35fa61ff1b63dcfefed241febee877fe91b7b3fe88cdbefe53c8d6fe3f1653fe283dacfe1ffd77fe1d9d8dfe10b361fde9c042fde41198fde2e392fda9340bfda0e5c4fd9e2d83fd951655fd92e3dbfd7d3833fd79fa3efd5d4787fd54cc7ffd409ddefd349ec1fcfa31a5fcd320a1fcc97480fcb45c77fca6a39efc88bde3fc13862bfc1011cbfc0fe5c5fbfc8c0cfbf2dfebfbdc5323fb963791fb572905fb32c269fb2db43afb027cbffac82184fac428affa9bdddefa88aad7fa7efeb6fa6fc54dfa6ccf3ffa2f839df9de9b40f9d61e32f9d06723f9c91061f9c5608df99dde69f9913b93f950e8a9f941677cf93aade6f9291309f8ed718ff8ea3726f8e595b3f8aafcf8f89ebe84f87776bff86b91eef85cf6f1f8509982f8490506f83745b3f8176e6bf7ce8171f78e2c5cf77ebf37f73f81aff730972ef725fedff71982f6f711e75df6d55e1ff6d1ba01f6cd903ff6cd76fbf6b52c0ef6a2fbc5f666808af649a0c5f640fdcbf63b52c8f6372a48f60e69fef5fec98af5fbdc5af5f0f7a2f5cba07af5b4541bf5981e4ef5929ec9f590230af58d105cf584e85cf5829d23f58105def5327ad9f506016ff4ecc73ff4d422d6f4c37d75f4a297cef48ae855f47586a2f4640a05f45cb60ff45a934ff4196d13f4191740f416673bf4016a6bf3e9afb0f37f5cf6f361c179f33fd2a6f32ce3ecf2f98545f2e8506bf2db90eef2d8f941f2d02058f2b99f89f2b7969ef2a6025ff2a58bdef299a4aaf28931cff26162d1f24f5252f2466323f223400ef20138e2f1e10209f1cbf171f186108af17436d9f16f4739f1638804f161f26af16135edf15c6352f1552b63f14cc85ff13bf209f1396f60f136a173f1338565f10d5b5af10970b8f107164ff101e908f0ee0cc8f0ddfaf6f0dcb11bf0d452d7f0cacd64f0c60d8ef0a56d74f0a3cb5cf08f98ebf07860e8f02b5473f0177833f010f0e3efcfb8d0ef938aedef47bd5cef1b5dc6ef080bdaeefcd9e0eef16a88eebf688deeb7733eeeacbceeeea3ae8beea396feee9c34c3ee92513bee7481b8ee68c4c6ee49329dee3b2151ee26b3c3ee20cac7ee135ac4edc57a32edb69c7fedab0040eda7b19eeda1541fed804965ed775530ed71d752ed68b095ed5a1abaed4a3632ed3e8222ed2af7ceed1e7006ed16ad30ed15a31ded09a668ecfa85c5ecdf4134eccaf4cbecb7020eecac9ef1eca65b75eca57ae5ec997a2fec980acbec72f55bec6da86bec52bcb6ec4efdacec403ea4ec3d5a97ec394901ec280066ec0a40ddec0159beebf5492aebe06d79ebd654fdebc32748eb9370efeb7d99efeb71c6dbeb71995beb66c602eb59f136eb49bf06eb3db486eb2e08e1eb288c31eb1cb980eb187220eb17b350eb03b995eb010284eafb2f01eaea967feae9f4b3eae641c3eadd242ceadb0fc9ead845d6eacb2d53eab5ea28eaabe726ea8e3be7ea6c8c44ea64e21bea5ae386ea4bc2b6ea429bf9ea153619e9fe70b5e9f2e4cde9d716b6e9b92c98e99f72ebe99a9e00e95aa39fe9477ff9e946a6bae9403251e93501b9e9282619e903ecf3e8b0ceece8741a0ae82a907fe81357ace806f198e8009b07e7d9448ae78372f8e7760e00e7626f81e742d88fe74070a5e740449fe70d699de6bf50fde62e7187e62ca5f7e5b997f9e595db42e5897456e581a21fe56a60e1e5626ee9e55ed301e52f8fcbe5067d0ce4bd7658e4b2b71de47fe311e47a8ddee4638ea6e45f2d11e456e479e44b91b9e4421974e43e2929e42a490fe4008801e3c2f326e3bbbc7be38cfa11e38a1c1de382dec8e37ef60be377f4c1e35a1b80e34e5154e3494162e3250b6ee311248ce307fe72e2fdec19e2f869cce2ebdc71e2df47a7e2d21019e2b3ac13e2a70513e21918dce1de2571e1d35a9fe1a62adce1991ba5e1874e84e1677dbfe15ca895e13c3121e11c04d8e10f79cfe1068587e10138e0e0eb68b3e0bf34a2e0b54736e0a58014e090e92ae082fa24e06b10f0e0647034e0640781e04f47dfe043752ee03406e4df819f34df7a7431df64df4fdf1d07f5df034157defcd3b5deda4685ded7da7ddec159aedea9f065de922053de874f5fde7fdc3bde691b2fde687a3cde6594d9de572504de2aa8a1de27e8c6de2084b6de03b1f0ddf74686ddd6bcc8ddcefaa5ddaf462edd9d0267dd92c9f0dd68f012dd60ee1add5494a0dd548284dd4d98cbdd4d16fbdd412985dd05ac33dcd57f99dcb4782ddc8fd0bbdc858a3ddc67004ddc4e50a9dc4b501adc346111dc1f2a40dc06651ddc030e72dbee4a53dbe83643dbbb56b8db956de7db9173cadb735031db707854db69a598db4b0889db41dc0bdb3f803ddb3de826db2c79dddacff9e4dace3e04dab89528daa19923da99e3bfda8f1e42da85008fda6cb554da675391da446f75da40bca8da3d97bdda2d38bad9c0e55bd9ab1e19d97a6d00d9799177d9706abad96b802bd957129dd9473655d939314bd9283c0dd92470dbd91eb434d91a0a22d91887fbd90560a2d8fe98a1d8f3725cd8d48984d8c7d2ffd8b0f5ddd841f366d83ef26ad81f257ad7f8cbc7d7b08fa6d7aebe8dd786e2b3d760a84fd752563dd74e34ecd7488303d742eb23d7394e74d73928d9d72d2adcd7288f6cd725a804d6d9fb11d6ce1231d6ccedb6d6be7995d6b12d18d6adf8c9d6a4b462d6623a42d65395e5d64ff0e8d627c888d62651a1d620c1c1d5fbc408d5801d81d572fad3d5443666d52e9fc6d4e64eabd4b9a502d4a830f1d4999f54d484b202d451c703d443d8ecd44024f1d3f06130d3d24315d3d0ac13d3b35816d3a697e9d39666fbd32f4f20d32ea4c7d31daa6ad3003d05d2e1d892d2c4ab0cd2acc4ccd28e4416d27b077cd23f5d5ed219ab32d2125949d1f5808dd1f33800d1e863b7d1e7b26cd1d2d092d1b596d8d19bfb3bd196a1fad17105f3d168c8c9d15ecf80d15028acd149ba22d12d20cbd1150601d0fc8ceed0f2a6f7d0dbc75dd0d90753d0d52bf1d0cc3962d0c77c12d0b84b2fd0b82f78d099a934d073258dd0681273d05e6652d04719ced008da65d0071316cff795cecff4e794cfabbc3dcf91d642cf91495bcf7d175bcf677856cf61d5a5cf10aed5ceea1e67ceaf54e5ceacbbf6ce998926ce8e6056ce6bc35ace684a50ce4b2c89ce31a0a9ce1c3b4bce034d2ccdd355b0cdc9c0d5cd9231e7cd5dc62dcd4a9de0cd206e35cd00d8eaccf322d8ccd74b54cccd397ccc826361cc74094bcc673515cc5fe487cc5702bfcc4c63b2cc3b3838cc0a815ecc00b6bfcbb74504cbaff811cb6465becb583f49cb4d0d4fcb2cda20cb29d42dcaeb9eb5caa6d92fca6a4ff1ca4657c1ca3f994bca2c84fac9dbcb32c9c55a80c9b4d529c9b28a86c9a7a79cc99a8415c97d70b6c97882b1c966e09fc9402abbc93db088c922fe4ec905369dc8eec5ebc8ecf2c1c8e5ad5ac8cf0cbcc8c328cac8bf962cc8a3413bc884f37ac86b397dc8560acec8518d2dc846f380c83a75c9c8322aadc826f8b3c8263cdec80e5885c80c902ec7ab590dc799f275c7925601c7915568c75b9255c7475ba4c72d579bc72bf636c7014449c6f63837c6daeef3c6d3688fc6bdd26ac6a57b30c6a3dcfac6954529c693db2dc68458c5c67d028fc672d95dc66fdf17c6656988c65ab6a5c640cc03c60d2bedc5feba6bc5f8949bc5bbdf06c59d142ec5542062c5504557c5406ef4c5349c43c52b7891c52a8e50c501025bc4fd91dac4cfc2d7c4c52f7ac4b70895c4ad306dc496dadac482fe9ac47d822cc473ddd9c472c649c467288cc4589ae7c450ce76c43911cac40742ffc3ebeb69c3b52b33c3a6ed97c3835a82c37dfa78c35d9d0cc33f54ecc3284be1c327a5f0c2fdd7a2c2e1bf4ac2db4db1c2d7325dc2a65eeec251b74cc23a47b0c2330c62c22e0bc6c22a30bbc1e9cbcec1e60eb1c1daedbfc1d331c4c1c1e959c1b5bc99c18d9831c156b07bc138372bc12ab9dac12a03f8c103635dc0eea8c9c0e59ea7c0e36599c0ddd617c0d587b6c0ca2bfdc0c6667bc0a1861ec053eb3ac04bf3e0c04b4efdc0378870c02d5f2fc0149824bffef321bff6e640bfef1a06bfd81bd9bfd31237bf93b429bf851069bf753eddbf6157fbbf27d200bf25648fbf211b8ebf1c016ebef34fc7beeb6610bee8d4e1bebffa15beb89222be96cceabe961ca2be5d2914be4ddefebe3ab439be309bdfbe1296babdbe1601bdafa83dbd5fad3ebd516c4fbd104c8fbcf5b383bcf3b664bcf2dd25bceb39bfbce9f2dcbce5f5b2bcacfd9bbc9bb415bc7e3c5cbc787f24bc6f06d2bc621f88bc5d0557bc4f2a41bc3b435fbbf830d5bbe48e18bbd46971bbcc0310bbbba631bb98723dbb84d180bb7efbf0bb779126bb3686afbb355203bb27f4a8baac287dbaaad93aba91873eba84bab5ba7adc10ba3998a2ba3152ebba2bbb26ba2b57b3ba26f037ba249108b9dd1ad0b9cf9ee7b99c4416b99aa1deb97744d9b9667b48b9532b7cb94ee4cab91cc457b903978cb8fdf489b8df6e97b8d7085db8b47021b86c9d53b85341e1b8460b76b7f88078b7f6d916b7e0a675b77cad4cb75ff96eb754c774b7545feab72ce286b70cad76b700db9bb6e36167b6c1ed99b689fea9b67d6c29b6752a65b6583cc2b63148c4b61e47e0b61992a5b60a717cb6072047b5e06fbab5906a30b589cc00b57ec0f7b57df4ceb56e9ac4b52d2d45b529f2dcb529b2a8b515d5b4b50a2cd4b4fc6f91b4f31af3b4d4b4b0b4cae2efb4c237acb49ce352b4594752b45698b0b454aa22b3ea9baeb3daff2eb3bcaa7db3a1ac9ab35a110eb357578db351b5ccb33c539eb32d3de4b32532c8b3183de6b2f56789b2d88d83b2c0b116b2c05319b2a9bd80b27d64b1b27b2137b277fbf7b26f3857b26d23adb25a180fb2258722b21522e4b203c769b1ec2d0eb1dd2c2db1c87269b1b30ab1b1941f57b17a72d2b1712addb122a8feb11eec83b108bc80b1088215b1074002b0f1ddd4b0d7acc0b0d4e571b0cd7308b067aba6b05bd76bb058889bb04aff6eb0416331b001182baff2898cafe7e79bafdd8f47af9a5522af680e47af655731af52c4e4af51e75baf492835af3d049daf37a1d9af30e51daf1e225faf115306aedf9823aed96060ae8d36f6ae7fdca6ae7c304fae73f76bae7293a0ae6fb3c6ae69a9c6ae667008ae63fa87ae308e2aae236c61ae012c12adf73e9cadedc8d6ade6d569adaf02efadaed0d5ada5be84ad9a51cead8ff742ad7badbfad608d8fad5e6aa0ad547cfbad46d205ad1c6cd1ad181fc8ad17af81ad0b4c99ad084f1aacfeb26bacf28ed3acec1b48ace38712acdea238acde5dcfacb962adacad79cdac686e84ac5b18b4ac590dd4ac3882b9ac201047abe0c01aabdff25aabdacc5cabd53b17abb9ccd6abaed716aba870d4aba5d09dab96c299ab9397b6ab929b18ab91b6d4ab882afcab7cf902ab691220ab62e155ab458178ab385a9eab2b7765aad1dc3faac0c0cdaab9339aaaa4b07caaa3af56aa8e3197aa88ee53aa714702aa5b848caa3c4525aa265e44aa1cc5caaa02aa73a9f78c2da9f65835a9f19ae5a9f058efa9c3e1dea9a58018a98d0e59a97860caa97138a1a96ea941a9676763a9592674a932f938a92ec5b9a90c444ba90b50fea8fd6da8a8f655b1a8dc1323a8bf16e7a8b76884a8b558aca8992e9fa89814aca8772ea4a867bc1ca824af4ea8150c89a8057e8ea80562c9a8027d92a7def263a7dd5c75a7c7c36ea7bae484a7b82ed5a7ad1663a7acdffda79de8b3a77f891ba7243377a717e4d7a71245eba6f78238a6deffe6a6ca8e87a6badb05a6a12b54a69dcd42a6919d59a6894105a6659ed9a6336dcea5f133f3a5da59b6a5d44f30a5b434c7a59f3ab9a59153e8a5899a55a573c716a569f77ca55bb68da556ad52a543a8a9a4fffdc1a4e163d7a4c9e2b6a498c5aba49492c8a47e825da45f73cda45cc39da45afc06a4062f8da3f34e21a3dec478a3dc6fbda3af9533a3a38716a39ab319a311054fa305db28a2e57898a2cc7a32a2b6b2f0a28cf2a3a287dfcfa285264ea277c2c3a2661f4ca265652ea25d5f5ca25bb90da2574f3ba2313a75a2132327a1e01e5ba1c26447a1ac38e6a190a263a184cfb2a17f9d25a150047ca13c8e92a136af01a10d307ea0f272d3a0f23e17a0ebcfb2a0c2f9b8a0c24ea8a0c24afba0ba5364a0b8a287a0894539a0796fe7a06c3d26a067fe29a02b9d9ba021f17a9fecef229fe2adec9fd0fa109fbf63fc9fbc17c59fb2254c9f86f78a9f7fb8879f77ee7d9f534d3b9f374ac09f058eb29eed86fe9eeac8b49ee78e4b9ee03aa79e7fb61c9e6a8dc79e5ebb169e47622c9e1920f29e14341f9e0450619dbed3429da638119d9ce51c9d9763af9d75df249d70bd049d63309d9d5d1cc59d5491529d21175b9cfce42a9cf86cc69cf1b98d9cf08e9d9ce8e6fc9cdc9f969cc2b5da9ca385f89ca052ea9c67a2ac9c45ee899c2fc0569c236faf9c1024dd9bc89bda9b8dd4399b212ca99b0b4a749b0115649af81bf99ac48c269a8a54599a8246359a741d489a6a64579a6143f79a2ddb199a2855dd9a25a3c49a21a88a9a06fcc999cba4f199b6bd1499a8abc899a53e0b99a0b82f99943e3a99930da69990a6bd9963e5ed99607ffe99435e6f993a264b992df3bf991f69a698bdba6098b997b098b614bf98ad38c6989d2210989874ef988a540698487ea29824247298139325981273fe9805954297b87b3797b7b94a979f8dc797858572976ee4359762d3a19733318a973207e996bd3db396a1a0029696e0c196942d95968c36ba96805155966d02d5965db8bf963a6b62961411af9610139895f9a09c95f11fa795ead54d95c9919795b94d2d95a1fd5095966e409587242a9559254f9521f9bf94fb2a5d94f1170f94f0cb8194dd3acf94c68f3194bf22a994bd9a449497bb1f9478e16b94635812945f70d6945de17d945a6602944689c29426b48b94228d0b941342f593bdeecb93b30f549399445c936d97d3935f7c4e934e80049305f4b792c4c0b192c162ca92be1f5d9297033e9274dce2926e7b4f924ac8939249469b92411c72920ff8ce91ef2ac791ebf1fb91c1ddd191b5cdc8917947c191434e629120c602910dce4a90f364f590f178d390ed16c190c1b2c290b17b7390a66fce90a63015906e201790647dc29062581590331578900f7f089003f8a48ff019bc8fde966b8fd04eb58fc29f3b8fc00d1f8fb110078f8c870d8f4866b38f0ff0f48f0496bf8eed32bd8eec80828ed375608ec773dd8eae48d48e8da5168e7684408e235ca28e1d39c68e18a5d88dc702258d8c89d78d82be3e8d75e0268d4211438d39cc9d8d3686008d06499e8cfc568f8cb58fe58cab18fc8c90ff5e8c898f4f8c6f52ae8c670ddb8c6672718c6338088c5206828c51767c8c4ee61c8c4d06118c4c56008c3ea4ad8bf2a9d58bd233988bd19ce28bd191f88ba1915b8b915a538b8c31ff8b7269738af2913c8aefc2d68aef56d38ab9dd358ab6c5938a94a6b48a8de8248a67a99a8a1bfca78a1621ed89f5d33389e7e84089b0c0fe899aeca18990891b898e0f2d897faba68969f13989685337895c110b894280e8891312ec88fd21f588f973b288d4341388cd43f688c21f17889fd89188938f778888b628887e84338852bcad883c7e578837e25f882ff1dc882cb06588241c4787d4563487bc0ba08793c899877c117387764d6387212cc7870a0bf186f9c24c86e93a2186cb9c5386cb171986acea5c8694d8ec868aac62867990fa86698f588665b4ba865fd6aa864a765686423e9b8612a58c85da3fcb85bedcb0858b8780858486fb85683a238562a18c8556abc6853e1e6d85313043852c46928516642f850a4f7584fc03cb84f360d384e8481b84e08dc284e01a2484df2b5684bffab984b4f2eb849ec4578495c68484801731846c8b128465dde5845ef3be8455b1fd8452b1018448082b842a305f841ccc3e8411edab83b9f00083b8e56983b34d09839b1de5839872b9838d3f97837466e6836875568348345f834111b6830c35fc82ff9dc282e7b6b682e1d0c882de1a0782c9748c82c2e77c82a8eb098298c8148273e946825e51048232c37f822eaa00822e39da820cd539820631f681f28f7281c3aff681c2337f81a2aba38193dc188178322a814bf72381447089812f9d61812c9c6581241d7780fdbe9580efac9280b78304809bf0e0807795dd804e524a804d47ad7fbe34357fbbbc2c7fa101487f8fcfb07f8d49fd7f6dc1df7f47ba7e7f3d62a67f3cdd9b7f0c14207eec1f407eb6b5687eb0bad27eaacc887ea782aa7e9435117e6ed3fa7e6dc77c7e3b619f7e2d20137e151dbd7e055e0f7e0144217df51f8b7de891f37d9a4c207d8099e37d587c767d53826a7d4b08877d1e29647d139ee27d07b6027cf23cab7cb08cff7c7cedd57c7bd10a7c7224e97c7104f57c6f480e7c67da7c7c54e1f37c415d797c30c79f7bdf9c6b7bd774ff7ba952607ba4c1b87ba492987b9fbdad7b816e0e7b5be2de7b566f2d7b090ca07adcecc97a78c58d7a64e57b7a5d979c7a5b39147a4f21e17a205ffd7a1a466d79ffd40079eaf28b79db369879bc8bc379b308a27998b3a47968ef757955bc6e794d98a0794c104d7931caa279024c9478f7898978f760ff78e33e3c78c8b71f78b31d18789621f8787d9ed4787c9f1f78608f7d785f8743784e35a278403fd7783fd6f0782bb7ff77fe58d077d7f78777d1a1eb77c48d367751be1d773af31e77321aed76f8559476df25b176cfb60976c1975a76ba97c676b7d6ca769203f5767e0e887671c85776573038762e8b65760c3d7375e420f575c4c25075b87b237597da587574035b75700d5c754c5b81752c153474f70c8d74e4f64e74d28f9b74bce89f74b405ab74a2371c7498b2117490704d746e762c746db7427451ee7773fbfb0673ee2a3a73e9c66773e70e5a73dd711673c9246673bf17a473be8fdb73b6434273aee30d739fb524739b72937394832a738ad2197379f98c7357f9ec7338266473311b9c72e640be72c42773728819d1727b8e18727a3e1872604707725effa2723a5a907231521c722c3b5571c696d571bb0b3c71b8858971ae567a71a417fb71a3a983718b113a71729d75711ed9c7710a9ea5710082c670e1f0f470e1bd5370cd836670c6795b70ba2a6770aa9971709903087096bd317093006670879424705a6b267030999b702fc84e701abae46fe168506f8bdd456f7c210b6f74cd766f72ad626f6e0fbf6f65f5ba6f59a2316f47c3336f3a326b6f22c60b6f1196396f0b20846ef68b5d6eb99f246eacdf636e9fc5246e902fed6e56575e6e21f4cb6e2114906e0a7ced6dcaf9396dc97b306dc000316dbcc5c86da45a826d9b963d6d8484d56d70a8956d5b36af6d4878366d34482c6d2837986d1dd77a6cf292596ce96b9c6cc19fec6cc0040d6cbe53866c7d4e186c7af5996c74d9d56c65c9a96c5fb2776c5cfb3f6beb819d6bea75616bbd53096ba512e76b8ed29b6b8607d06b7eb1246b74b6356b54fb1a6b517b8c6aaf3ccf6aa366946a9dbdaa6a89c8346a710fe36a5e52bd6a2e50a96a0fc6b96a01f4a769f2aa9169e680a0699e2656699bba8b69983eea69940a776979d3626953ea82693dfe7869399ddb692da2c168fc0d6368f9d4c968bff66468ba906e68838b2f6879df0e686cb03368630be0685ee212684c624f67fa574767d5ff2667bcb4b867b7055067a8cdd66752f7036722ee5a6717bc74671779e867129e0466fc5a4366ec800a66b1cce86680c8db6669593f662d967e6625c5ae6608790165efd27665e2f4f865e2e0f665a723196598e22a658fc4556575453e6563f94c653d295e6533d2af653032da652fc4ec64ecadfb64d620ed64b622ed64b1e47964ace06a64a5252d6499691064994e4f648ad9ed64861b48647c6f27647af3cd6459c438642e04b0640c3f0f64072d6863e8b90e63c680d263c36f9463b16b1c638ace73634e30ec634629bb6331389b631bc13f630ad72462dd8d6362dad68762c251eb62b2cfb062a138e36285c8ad626e6612624ef3466228b46e6209b05062014b5f61b5f90161a409c66196f5ef6166f5526154df316121eeb461102e2860e7c01a60e62a7360d1f8d860c6ac0b60a06c36605e34d96048a4546035b8796029ba2c6021952b5ffb64435fc783cc5fc6d1c95fbddd165fb6760b5f97cb915f5373245ed5994c5ec4e2045e8858c65e87830e5e82f6ee5e68012c5e64ba265e2a41805e234c065e1c02ce5deb92105dea198c5dae7ceb5da9012f5d358bd35d1384f75d08b5be5cfcf3935cb253965ca5a0455c9ee4bb5c9e77565c7edee65c6bfe8a5c6b69dc5c581b515be123b85bd9607c5bcf0bb05bc961e25bc585335ba5bcd15b9fa3c25b7ad4f95b5ce2525b5a1bfd5b4ad1e75b19505e5a88684f5a7e2bf35a6a91455a67057a5a652a705a5b2a7b5a557f865a1384725a10695d59f52a1e59d1355559a3b5d9595f9d41593d2cc75926b8095923641359207952591c5b4c58eb9d9858ea2b4258e3fa5958cd214458c1386458b5ef8658b4e3af58a1076f589ff3d3589657245885aa3f587ab33958676c9c57f062e757edc52557c083f35759400f574675645740e3d357135b1456dd2631567da13d567c78a55658cd66562e4b44562db9e65611322455fbbe5655d3c56e55ceda2155a70ca8559b23c8556fe40b553391aa54e5097154deb95f54dd31b954db6cc254c89dc454a083af54816a495469fcb55463e0285435af6754332b73543029ba542a33a3541a08975418852b540c87af53f0553e53eff605539239c55374fa06536eff9553696f4f5341f2eb5338563c53223bcf531c790b52ec6e0852ab41de52a1a52f529e65715253ad23522d7678522a202e5222a3f95201615351f78c1f51e80dc751e6aec451ce553c51a0f845517f2549517a0652515b55ad51377f11511c207f5109a4d750f26a8b509164be50763766504744335020cb815013f9344fdfaa644fc6f1cf4f979edb4f00edce4efdd2624eca71874ec7371e4ec1f92b4e8a145d4e6e57b04e6261d24e33fb0a4e2c10144df3dcf24dcc55ef4d99b41c4d89f12d4d6c4ab84d5dd7484d5009274d211e5d4d17e84d4d0878a54cecb8e04ccb412a4cad90484caa9bc74ca439784c973e664c853e0b4c7ffbbd4c441e184c34901d4c2fd5724c1857794c16894d4bb805ae4ba9d9594ba45ceb4ba122824b9eefb34b98ed934b5012394b2cee734af9a0164ad8fa504acdc8564ab48f324aa4d5374a98c90c4a8ad13a4a8ab1134a3a4f0f4a37191d4a29844449e8817549e079fb49d8183e49cc458d49be303b498f81974985ffc249847b9b496e0ae94965191b495a5da24959e721494cf013493397e0491a7866490a6f93490a2a2548e79ba648d0bb1448c95dbe48aee1f348a8dcc948a6923e48a2411b487af612487538bd4848f77d4843e3d1482bdf69482a94a5480656fd48040b0b47db30f947d2483447b3790047a4617d479dff894785e13c4784a73747822da9477a68d14773ba71476ec120475400104746dacf471aad7c46ee52b446e2490946d6b7c746d0029c46bcb92446a5e0f746971d74469530db468d412c4665a670465e66ff4647f64d461bdb8745e6248f45e01edb45be13c945ab6ffe45a6cc47459542ba455b88a7455851f7454d775b453f3283453a316d45392f68453909cd4530280545279e4f451ae1414517a99444ca6cd644c8f28944c0d02744bd48fe44a8817644a81e1244826c3a4481bd624480c795447ee8af447ebc664472435a4426329543d1897d43b6091943b3e707439ef18c4387760a4366b0504360fa34435ab6b8434f5769431fd990431a46eb430ddc2d43079f3442fd86e042f0e2cd42de581342d0fc4a42c486c942b98cae4283ef65423e37c7423dd182423d5e4d41f7a93941e799e141d44bf641cdd41741a7f5d941819c26416a76de4166c9b8415e18c04135bab1412018c6410b4ff341001df940f4aea140d76b8240cb82a2408d9d5e407e381f402a61d33febe6b33fe3cf653fdb4ae03fcc8e793fbf337f3faae7ae3f9378123f819bb13f7d02403f638a4d3f53cd3e3f19f1493f0c3e2a3ef5f9e43ee651333ee213023eb3db033e60c5c03e53bb153e324b283e1329d23defc7ec3dcb59c93dbb26003db6fcda3da8bbeb3d8218af3d7fbe263d7222233d6e31cd3d5823833d4d031f3d2f68483cfa24b03cf9c6c03ce068453cd77a8b3cd227563cc8e36c3cb60cc63c7badc83c766e8a3c565e473c4830b43c17b73b3c07ac363bff47623beffd4c3b90a6ee3b88b2013b6c87103b5e46213b5e0aad3b3f30743b1af2d93b13f8f93b028d553ade05d13ad22bac3ad159333a9d1dc63a7e3fd33a7d7b6b3a7b21923a5f0a343a5c30dc3a4ce6c63a4c0d873a40ffd73a03df2039f4e47739f2580539c57fcf39bf779a39b635b9398ac43d39348c9c392e6ace391394e33910adb638fcb4c938fc252f38f1a29f38f048b538dd99a738d128f238b989f43887b5e2388077fb387ed60b386028553842814d3833ca09382e5ae2381660e537e79eda37e0bba037d3fce837b158d137b0fc7737991f5b37779bfe376f0164375ed6be37567bbf37465cee374621a1373036da37009a6836f99a7d36dfe7e136c7ac6e36b55ddf3693000b368cc30436496d4835fe273035fc0fa835d10f2935afd0b0358c837f358c35c0358622e13575c50e35366b513523cff735188f7f34d5ddae349c860b348e7e3f348a45fb345425ed33c3273f33bce89c3390a8b8338f4943336478e43339e5803309c9fc32f2157732e99a9232df5d8832dd6a2632cf4b9332c278bb32b9f1083289bc143264e69f324da8513205b83431f8b6fe31f836d931e15ebf31b893dd31afc912318ec5d9317f0b5e317855273144ab4a313284a63131911b3125fdbf30d02c0330c2002f30b9cbbb30aae4eb309584003092499730805d2930632bc63055a078303cf47a302decba302ae5713027359d2fffb3792ff814e12fda00e12fd451992fc5fce12fbeef6b2f8e0a2c2f86caa62f838eb72f782e0f2f614fda2efb754d2ef1d89e2ee1bf432ed8b66f2ec3140d2ec146d32ea822ef2e50386a2e4b0e362e3e25052e3aea9c2e16e7802e06528b2d8e94812d6eff1d2d5a488d2d4ab56e2d461ca22d32d2a22d2fbdf62d2205f02cfc94bf2cc3fefe2cb05d702ca65d1e2c9a26dc2c986a882c8cb6782c85f2442c7b7eae2c73b9e92c6b8fe62c307cd32c2d758a2c2756162c1808442c00a2612bf3af3b2be4aac72bd560b12bcbc4022bc1b4b52bbfa06a2bad27a92ba26e902ba213862b9d25542b74e3982b51213d2b1dcc0d2b08a3b82ae8f0532adb46882ad868282abf335b2abe8b1f2a8b63e12a74508d2a65e7a62a460b732a41b71b2a3afb0d2a29441f2a12930f29ae0ab729a03c96299df69c297ab5872979dc482945d9cd292bd5f4291b7499290eb82028eaffeb28e4047a28da78ec28d8381528af28c0289451872888825d2884c38c285055a62838238b282b0ca1281f716027f1a31a27a4ca34279876832788337a27833b0e2774315f2749d385273762662725a4e026eef88526e92e8626c9899226aca67926a0b159269f5e2c2687f61b267ff343267a27fa266efb66260e890e2609da6a25f55ffd25f1450e259e79aa256e3ceb256d5e772563b028255eaef0253e4480253561fc2525609324ecb88f24e28bb424c346e524b9e56024b99ac424b492e224b41339246bc05e2466c3e4245f0a55243faf33243e6116243e050b2423bee9242201792403ac6f23dd7ea423d012d723cfde7e2399e613237c78042372c35823691a9e233cc8342334a9d222e5c6f722e5644a22b4aef822b227a022a55619226fb44e226a732e22699d6f2266339f2248c19e2213c868220c1e7e21f5396921f1386d21e7f1ff21e38e3b21d85df121d72d6c21cf7af7216b14b02151ab6c214c7e832142b071213ce4d921324cc7211a49542110d9ac21058ab920f8b4e520f2526a20e094d520dd97d32081797d206d1b19206a392e205f0b8a204caebc2044ee07201c9147200a004020063c881fd759911fc4a2c11fc352c11fbf4fae1faa0e341f9d7c351f91a9841f394ebd1f02205a1ecfd38a1ec584631ec01dbd1ebfa81d1e9ea6131e961f0b1e9491211e780c841e6a792e1e5405c91e52b2501e4500141dd2a0491dc8e9ad1dba1aee1db311791d998b861d78dcf71d6989891d4909291d42ecca1cf17a9b1ce027ec1cdefc1c1cc21f521caf6a381c88174e1c80000e1c73ce281c7274941c60e2131c5ca16b1c5ac98e1c535e221c3dce9b1c2a2e5c1c068d7f1be67ca41bce61da1b94251a1b6d64811b6aba651b5f19c81b3684a21b1828241b04b0731b032f721afe935f1af992c31aef4e451aed6f2b1ace53b81aa3ee841a869e711a6518161a51aaf61a50cdab1a3d7d521a11fe1f19dbb0b519a20a42199b7041199175e7197b6d10196cb73f194061d01915012e1908da231904886218fa0d6318f20f4c18f0525218ed43c918e13b0518deb02818de330c18d71a1418c7f3e118a333b2189971db188aa767188662681864f65718351767182df3cd18107006180c82a517fc8aa917f7f4b117dcd50e177f0cbc177dd9e8176d59d017590c141758db62174aca161747001d1743b30d1737e05c17365c88170640791705bf8b1705712a16fc22dc16efff4416d921aa16ba129816ac11cb1686a88316760a6216696c1f1664baaf164224e91615b33e1610f10b160c59f71606692815fb32a815ef3dcf15dc0ba715b5c4dc15a7b39015934602156b90541542f1e9153f4209151f13cf15160a20151102831505c9611504f1ef14fc94f514f0291c14e93bf614b7943a14a72852149c0bac148c7db11468ad7414655d051461ff2e142d80db13f7af1f1392ff8b1361db691361804b135b6b7b13518daa1338e6a313254e60130f66a71301e6a412f877a112f4cc3f12ef9ea212e0548c12cbb18012cb2a5c12c5caeb128f38dc128d552c123ff9b9121830cf1214192c1202957911ad777511ab666211aa86d411a4dc7b119a9dfe11992ba4118d9514118d7506117a45031154f60d114beeac1144665d1121a3e811187d2b1100227610e1f4f110c4096910a440b510921eb910917613108f0dca10809a92107a4d4410298de1100a06b4100663ce0ff425390ff033a00fd800560f65e91f0f5028340f3d1aa70f1390a80ef9f0930eed36f50eed1e6f0ed3af110ec11e300eb5acac0e79f4860e7317080e671d7e0e6630bb0e5a8dbc0e3bbcdc0e26e57e0e05b36a0de8b8490d9960df0d72ced50d006f0a0cfd4ca30cf586df0ceaf1040ce5b76f0ce27d060ccdede80cb083250c7cdd5d0c6de2680c5b0ff30c53b4ea0c2ea14a0c0f22da0c0df6ad0bbbb90f0bb8d6110bb823f80b7df8840b5228e30b112cd10afcab500adb4ff30ac75a460ac517410a9b41a50a9b33420a9b03170a69d7870a69ad970a5fa6540a5b05590a3a983c0a2bad9d0a16e4ca0a086cf90a08109a09c3651909bfa2d309bc686a09b172a109aa484809a6df9d09755eee096e3655096afc0a0957a4030943afa90935d9440933cf8909317c050902ff2308f7dfc308e90e3e08e005c408bbc355088897170833e1b008218bf9081e211308115d200809712f07f1e60a07bd9ad007ac9aa607a0992307752d09076171df0739e8b30739e80207302d7b07202972071d8f66071bbfed071a04880709e81606ca6cc906b450c206a0276b069dc35b069d507d06958ffa0691ea8a06643d65065be384063a58f606018eed05fb726605eddfc705e1e74105d2886805c94d66059d6d06059a38d40595aeb905617599053f97b7053437e905177afb04ff5c2f04d4f6fb04c126df04bd5fec04abbdda04aa009d04a5c0bf04a47f6104a254b8049ea4e40496c1b5047722c0045f1eb3044691d004306071041363d003fe715203eaa35103d36c0803cbb68203beda0a03b64eca03b097ed03a6d7b4037c5e19037ac858036bd5ee0357247803544fb50340cee0032f0fe7032e0e6a030f73f702f521ed02f0e4c802e2db9202c1b99702a974e8029379fe027f984c025f8ad30241787d021d6d63021c428d02154117020e234d01fc643701eb2bb401d9479301aee25f019b445d0175fca001429686011d0acd0114971f0108ae3f00de112600bcacec00aa438400a4e4d100a4b43200a11c21006ceddf0067e5860061ff02005b4bcd002046460013f3d5
  | 6 => 0xffe63b09ffcad027ff7691aeff588adeff1b63dcfee65e7cfee32413fe88cdbefe0fc9e7fdccb2a4fd7c50a0fcfa31a5fcc80153fcc67d2cfc9c5f33fc9be8b2fc759971fc5c79f7fc4c2bb6fc12bca5fc0fe5c5fbeade5afbbcf7a3fb85e562fb48588efb1449c5fae6630efa6ccf3ffa12042df9febab5f9d61e32f9cf42bdf9a7a801f9a06890f95ddd18f9282620f900155af8ed718ff89a5388f8929197f859ab25f83d397cf7ea8307f7d1742bf7c3bef3f7c0ea40f7c0bdf7f7b444ebf7683426f734def6f700033cf6e0f31df6d59e08f6ac64e7f6a2fbc5f64fddbef612fddbf584e85cf57fd313f4f18bd5f4ab5f8ff4421f8af436b032f4196d13f3af896cf30e900af3013510f2ece93ff2a58bdef25bf2daf24e3fbbf237fb75f220ed53f1b83b05f1a2c751f1744cb9f1552b63f1469f68f136a173f131c97df0f8fe6bf0c41a40f0c1bfb7f08f04b0f035c126f02269d6efbdaf59efb8701bef985fd8ef938aedef5a7bc3ef49adc7eefcd9e0eecab392eeae88a1ee49329dee448ee6ee3b2151ee26b3c3ee135ac4edf61496ed345996ed078160ed01792becf8374aecccc5ceec706c5fec3e26c0ec33a430ebf5492aebc2798ceb8482deeaf2fe08eaaba40aeaa0d84fea987d50ea4bc2b6ea429bf9e9cec495e91310bae8ce3751e8a7f3a7e8786ce2e86a5118e865d188e7de879ce7d07fd0e70528d0e654bf79e61f6bb7e6047a4ce5eac5bee53a386ae5236050e4d0c76ae3d92e50e37ef60be36fee4be369372ee361dcffe34d6f71e316532ae2cf591ce2a3516be21ab800e1f8c487e1ea2480e158e911e11c04d8e0d09612e08cb6ffe084e352e0640781e03e9650e03406e4e006008fdfdc286ddfdbbe69df727e64df176242de4aa549de1d4819ddb6521edda3535fdd83b8acdd7cfc9edd5494a0dc6dd785dc26060bdc1a39a6dbc6c51ddb925737daca350bda6cb554d9e2b2ead9b0fcf7d9508a9fd933469fd9283c0dd8e07b3bd8a0b081d8676224d8248d45d8054876d7fb9c55d7f614cad71f8035d7121468d62651a1d5f42931d5ab9f00d55ac292d51a5f82d5192efdd493acfdd47ee66ad4744e58d43ab676d4229666d3c37b0ed34c01d1d3195b22d3003d05d2ec0fc5d24421ebd20785f4d2021f4ed1d8209cd1ba0e15d114a1dad0ab8b1ad084ee5bd020fdadcff795cecf9ea2fccf9ccb1fcf937102cf6c2fedcf488f10cf287e35ced626abceacbbf6ce46b204ce453103cdbb15ddcda719a7cd51d5d8cc5702bfcc4adbb4cc4689f3cc3410ddcc3253e3cc20349dcc191ba5cbe05628cbda8ad3cb7718f8cb6ff55ecb4d0d4fcb1ed69fca9b0da5ca48420ac9fc1429c9c8aa14c984267ac97e5774c957b4cfc952f29cc9486ab9c8ad91e5c8580bb1c8322aadc826f8b3c7e929e3c7ce7f42c7a400bfc739b0b0c643e835c640cc03c631a033c622561dc5e6cbc8c59d142ec55a3260c5561abdc52b7891c4fd7217c4ed67f3c4dc9f8fc4ad306dc473ddd9c40742ffc4060afac3d10f5bc3c29c23c3a7bbaec33f54ecc2a7eab0c29229c5c2772949c22e0bc6c222d15ac1daedbfc1a24b01c12ab9dac07a97adc042709bc03f4e34c0378870c00fef79bff284b6bf95b67bbedfe788bebffa15be942a74be309bdfbe1d5184bd9d06eabd4db461bd4a6e8abd4a122bbd0566aabcacfd9bbc99a594bc737d96bc4f2a41bc4500b4bc3b435fbc260978bb70cfa6bb6022a4baff9c61bac3cfdcba7be993ba5c0619ba52343fba3998a2ba38609dba2b57b3ba0c6e5ab9df520eb9d3ec1bb9cf9ee7b92fe158b90b4ef7b8a3772ab876397ab866109ab816f88cb7ff617db7ec022eb7e0a675b7889361b754c774b7156d99b701a96db700db9bb6f8505bb6f2997eb6e8d945b6bcc9e9b6add77fb632e659b60a9360b5eb7679b5a18c64b5837a0eb55f6ef4b55024deb52d2d45b51b4924b4f0e3f0b4849817b45698b0b3e31db2b36247d7b357578db355f566b311331eb30cd1bdb2a5d339b25d6572b1cacf54b195ca6cb18117e9b175e5efb161ff0db152b4f7b0eb35a1b0bbfbd4b076a057b03c333bb0152237b00b7616afcabf79af605450af521361af51e75baf3e8da2af34e181aef65a95aed83927ae992a9bae6fb5d0ae447e55adcaac6dadc1004cadaed0d5ad718533ad47c33cad181fc8acd33d29ac92ea3fabecfe8eabad9384aac0c0cdaa88ee53aa175fb5a9f19ae5a9a88220a978566ca940cb20a932f938a8f655b1a8d224a0a8cf11f2a8c6e9f2a8c30774a816246ca7cce9eba79c94e5a75868d1a6c15e8ca681d43ca61d9284a5dba640a5cb3365a59153e8a58864b9a570e345a5673724a5433a78a50df307a4a5899aa47df39fa47586fba443ea9ea4300e5ea42cd3f5a41eb2b1a3ba627ea36d5609a35979c9a352f279a23edb76a1f974d4a1e59894a1de3659a1d452d1a1aac65ca18b3433a17d22e7a168b559a162cc5da136af01a0fab995a0f89e15a0ed01d6a0e355b5a0c24afba08c37c8a08083b8a060719ca04ba7fea03c875ba02142caa018ea069ff903a49fbf63fc9fb4f6f19fafaa019f7320c39f6a01fc9f435b549f374ac09f226f0f9f1856939e9bf2cc9e6a8dc79e5ebb169e5a73b69e3d30979dd03d7d9dae8dda9da6e3b19d9ce51c9d8dc44c9d63309d9d5737af9cfb2e2e9cb429df9c8233e79c45ee899c1cd6719bf2d0829b6c92159a3a70289a28c15e99cba4f1999fabac998bcf6c9970731d98cb75ec98487ea29806a87497ff77ee97f4b8b397bc8f7497a5903c96cefba796be8d6b96b9f65796670d04965d6aaf963fedaf963a6b62961411af9587242a955b1a729554c4b294e61faa94a97f55945f70d694517b659448871d93f748cc93e781aa93d75ddf93d2eac09376087a92c4c0b192bc75c79289ec4b925f098b924542ed921c481b91c1ddd191aa7bd291a7966f9145b38690d4cb8690a2efb0908f18918fd1d2518f612bd68f4866b38ef2609f8ed375608e83dda18e8181d38e1d39c68dc702258daeb6ea8d96a4278d82be3e8d01514a8c7b32e18c6672718c60b5ca8c1c880b8bf2f7738af2913c8aaddfd88a1bfca78a0eef4c8a05406389862c84896853378870a15c8828504187fba69887eb7c5f8793c89987780929871444ab868aac6286423e9b8627d61685d045ac85bd091285815ef48562a18c8535399684f7986e84ddfcd184b3078984aaca5f8434a88d840e3af8834914ac8343f5748336e92a8298c81481d061ec81c2337f81b64a9f81aa4be68173a23f812c9c65804e524a800f3b127f4c82f47ef9469a7e8f0ee57e6dc77c7d1dccc87cdc85ab7c822c517c4738337c27aef07c052a607c0197c27bb168107b938ec37b816e0e7b68fa497b505a1b7b4e91c47add20027ad356fe7a9d93eb7a895d3a7a156a2579ffd40079bf042579b1e0ad79a76b1e7955bc6e794c104d793a963178df15c4789621f8789246ed786d7a27784303f1783f93707828c3c77807311077bf83c2777b1360776e716477522f3276e8ef2d76815682766a4d777653581375e8608475de4dfd7593b8e275750df875700d5c756c3251751cef557503eaef7498b211746c058e7425672f741fd7ad7395ecd07394832a736f60c57357f9ec73311b9c72d5b5bf72c711ff72b7407372798dd67269d39671d81e38719f2aaa718fe09471729d757154985070a1aed4709903087037b5197027f7486f9f06ed6f912bd76f3a326b6f23c7fd6e7c781c6e7753996e72cbfb6d8484d56d7b9a386d70a8956d1b44d06d11a07d6cde45ac6cdca3746c9bfd296c952d126c1909f36beb819d6bc60e856b880d0c6b38daac6aa366946a96c90a69983eea694c731269399ddb68c0c28d68bff664687eb59a684c2e6a68351c89680ce485679b48e8669c12a4669959236693b7626692748c665a3f7c660254af65bfbeb665bd22cd65af2543659c19a5656788b86545c8ff650cc976644abe16644a83ab64494198640f749e639dd901638364c762ab408362976443627809856272e6b3626023f5621b61f661be31e561b1b55c61a5fc1d61656df761123d4b60e62a7360bdaf5560a28f2560a06c36605e6e67604d4e2f5fca22425f51f4e95ee7d2335ebefa985e7a5c345e6059895dfb35305dea198c5dd0332d5dcaefe95db348985d5ec7605d3859cb5d05e3745ce781ae5ca968f95c3f6f3e5c1e14b95bf75a425bef78705bb9303a5ba9bdb25b5ce2525b4780245b447f285b20f3f95ac18ab15a3983ce59dfced859d39eef59a7a06f59756f6458abf9125885aa3f5841ff575823656d57f0878857e6ead957c083f3579ec53357483123567da13d562db9e6560ce62155c9e16555a70ca8559b23c8549206125478b0975434746954332b7353cb46cf53bb717d536d9f315363f3105310d53a530165925247904852223c3d517f74235179d5c750a53233509f1e5b50839e00503a6e5c502ae8924ec1f92b4e7fc3aa4e3a1d8f4dcc55ef4da3458d4d6fdcaf4d0da6874ceaad5e4cd50f3c4ca5e7834bf816554bef3a5c4ba45ceb4b5475944af9bae04acdc8564ac787084ac1df764ab0e5cb4a8253c349edc72049e3a19849af046b499fba554959e721492cd6e3490b932d48e3fee648d86fd648c925c047ff9bda47d9bcb547a1726c479c679847888b5847648ea14755448b46fff06146f5f53a465e66ff4647f64d4606c2474603646045b6de7845312c5d44bb495744854ff84462c79843e8b4d943a67f5843a459ab4351809e4312504b43020eb54246985541f04a6a41b885d641655e38415f3b5c41001df93ff7917b3fd300f43faae7ae3fa90f713f9378123f14352e3f0ac5793efb7b633d5823833d29e9d63cf2c2943cd28ab13bd5910d3b8522ad3afe0d363a4c0d873a2b3bb73a0d9de939ccadf839ab90ee3954a722391c416138f1a29f38cd891638c688913898ad5c387331d9386e482838212cec3801fc4f37f6f48137e0c5ed3797b3933794b297378a09c136fae6ff36cf412d36aa76ec368a35f53683134c3626d9a73623d25e35dac9aa35b5eadc3574c5153548338c353491083505b18c3504351534e4ad3934d5ddae34d1a35c34719ef7346e9dfb343fc02b33f9849a33b99773339053e0338f494332fdbdc232e302de32d1d1463289bc1431d636a731afc912316f21a931571f5331475fa531372121312a938930958400308d0a1d2fd451992fbeef6b2fbdd2a02fb4267f2fb3068b2f96e3892f86fcc52f835f0f2f219e012e4b0e362e294a242e185e4d2df46e6a2dca09362d5a488d2cfe8d592cdab53a2c97be042c8f9a362c8e11e32c73cc382c444e2a2be5f7032bd560b12bcbc4022bbfa06a2ba291132b9037382b6db9952b368ab82aa3f49a2a3a572a2a12930f29f9d86029c0101e2926228b291558812906c3e628fa7cb928d9dbee282b0ca127afb8d8272bc7fd27290ff02701193a26d684c026ccd3af26bbfb222699fb822687f61b267a27fa2628425425f1450e25bd8fae256e3ceb255eaef024fd0cd224fb0d47244ca03b2442845c2423bee923ec9b0723db049e23d8bec7239c6cbc23729b3122cddedb22b01155225397cf21eee0f921a00f382175f2b6214c7e83210b7cc620fc1c5f20f27fb020dd97d320c6866b20b2aa2b20b128ba208a79cc207649c2200205a31fbf4fae1fa7cb3f1fa1b40d1f9efcd51f394ebd1f2d83331e4500141de5682a1ddfbf401dd2a0491d51c84f1ce027ec1cddbc211cd60c0d1c7b9f711c3bd65f1bc58cc51bbbe0a41baeb1c91b8140c11b6d64811b1800bc1afeb64e1a856a9e1a59be0a1a56482d1a549f9a1a41da9f19c2ca711924f68e18e924af187f2af41871c6821810700617c81cde17be70bd174e40a5161f8ef915e33a7915c7ca43156ab604154bb1e614522fbe14282c091377ba0f136bbbc21308d35f12f95bf712ef9ea212e0548c11ca5a5c11c4f884112c1b2210778d691055868d0ff4552c0fe0e6510fe078ec0fae00200f0b63780f0786c90ee1a5580e9ee3e80e9c1d930e8cd37d0e5b51f40da907100d372bb40d1336eb0ce5b76f0c68b99f0c4f2dc00c0f22da0c0606150c0339fa0bf6e5450be309050ba96e320b32647d0abf7f600a9b41a50a555caa09bfa2d309be7a3b09bc686a093dbfec0915c70408e90e3e08dd255e08b1e5a10875934008165a500807103a07c36bdf07abfe4b07752d09076c3539075a86c10687dc30062e6f9e0595aeb9056f780e054362e905398db5052a0f5d049d5743047980a703e75a8603d36654036bd5ee0362cd170355faca0241787d020e234d0203fac101d9479301cc15f301aee25f0175fca0016e11aa00631ff30059e9e3
  | 7 => 0xff1b63dcf9a06890f4ab5f8ff4421f8af2ece93fe316532ad8a0b081d3003d05d114a1dac826f8b3c631a033c622561db6add77fb55024deb4f0e3f0b30cd1bdb25d6572b1cacf54b03c333bad181fc8a8c6e9f28daeb6ea8968533786423e9b7b68fa4978df15c4786d7a277681568275700d5c751cef5571729d756f912bd76d7b9a386d11a07d5f51f4e95478b09750a5323348c925c047a1726c4606c247415f3b5c39ccadf8346e9dfb31afc9122c97be042c8e11e32699fb8223db049e20c6866b20b2aa2b1f2d83331de5682a1c7b9f7114282c09112c1b220e9ee3e809bfa2d308e90e3e07752d090203fac1
  | 8 => 0x86423e9b
  | _ => 0

def stateCode : Nat → Nat → Nat
  | 2, i => level2 i
  | 3, i => level3 i
  | 4, i => level4 i
  | 5, i => level5 i
  | 6, i => level6 i
  | 7, i => level7 i
  | 8, i => level8 i
  | _, _ => 0

def state (d i : Nat) : List Nat :=
  let code := stateCode d i
  decodeState (code % 16) (code / 16)

def test (d : Nat) := bar 34 state number (idxGen number hashes) id [] d

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part2_0 : span (test 2) 48 0 = true := by decide +kernel
theorem all2 : span (test 2) 48 0 = true := part2_0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part3_0 : span (test 3) 100 0 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part3_100 : span (test 3) 100 100 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part3_200 : span (test 3) 100 200 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part3_300 : span (test 3) 100 300 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part3_400 : span (test 3) 100 400 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part3_500 : span (test 3) 47 500 = true := by decide +kernel
theorem all3 : span (test 3) 547 0 = true := (@span_join (test 3) 300 0 247 (@span_join (test 3) 100 0 200 part3_0 (@span_join (test 3) 100 100 100 part3_100 part3_200)) (@span_join (test 3) 100 300 147 part3_300 (@span_join (test 3) 100 400 47 part3_400 part3_500)))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_0 : span (test 4) 100 0 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_100 : span (test 4) 100 100 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_200 : span (test 4) 100 200 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_300 : span (test 4) 100 300 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_400 : span (test 4) 100 400 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_500 : span (test 4) 100 500 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_600 : span (test 4) 100 600 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_700 : span (test 4) 100 700 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_800 : span (test 4) 100 800 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_900 : span (test 4) 100 900 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_1000 : span (test 4) 100 1000 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_1100 : span (test 4) 100 1100 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_1200 : span (test 4) 100 1200 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_1300 : span (test 4) 100 1300 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_1400 : span (test 4) 100 1400 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_1500 : span (test 4) 100 1500 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_1600 : span (test 4) 100 1600 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_1700 : span (test 4) 100 1700 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_1800 : span (test 4) 100 1800 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_1900 : span (test 4) 100 1900 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_2000 : span (test 4) 100 2000 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_2100 : span (test 4) 100 2100 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part4_2200 : span (test 4) 33 2200 = true := by decide +kernel
theorem all4 : span (test 4) 2233 0 = true := (@span_join (test 4) 1100 0 1133 (@span_join (test 4) 500 0 600 (@span_join (test 4) 200 0 300 (@span_join (test 4) 100 0 100 part4_0 part4_100) (@span_join (test 4) 100 200 200 part4_200 (@span_join (test 4) 100 300 100 part4_300 part4_400))) (@span_join (test 4) 300 500 300 (@span_join (test 4) 100 500 200 part4_500 (@span_join (test 4) 100 600 100 part4_600 part4_700)) (@span_join (test 4) 100 800 200 part4_800 (@span_join (test 4) 100 900 100 part4_900 part4_1000)))) (@span_join (test 4) 600 1100 533 (@span_join (test 4) 300 1100 300 (@span_join (test 4) 100 1100 200 part4_1100 (@span_join (test 4) 100 1200 100 part4_1200 part4_1300)) (@span_join (test 4) 100 1400 200 part4_1400 (@span_join (test 4) 100 1500 100 part4_1500 part4_1600))) (@span_join (test 4) 300 1700 233 (@span_join (test 4) 100 1700 200 part4_1700 (@span_join (test 4) 100 1800 100 part4_1800 part4_1900)) (@span_join (test 4) 100 2000 133 part4_2000 (@span_join (test 4) 100 2100 33 part4_2100 part4_2200)))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_0 : span (test 5) 100 0 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_100 : span (test 5) 100 100 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_200 : span (test 5) 100 200 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_300 : span (test 5) 100 300 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_400 : span (test 5) 100 400 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_500 : span (test 5) 100 500 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_600 : span (test 5) 100 600 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_700 : span (test 5) 100 700 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_800 : span (test 5) 100 800 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_900 : span (test 5) 100 900 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1000 : span (test 5) 100 1000 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1100 : span (test 5) 100 1100 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1200 : span (test 5) 100 1200 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1300 : span (test 5) 100 1300 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1400 : span (test 5) 100 1400 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1500 : span (test 5) 100 1500 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1600 : span (test 5) 100 1600 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1700 : span (test 5) 100 1700 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1800 : span (test 5) 100 1800 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_1900 : span (test 5) 100 1900 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_2000 : span (test 5) 100 2000 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_2100 : span (test 5) 100 2100 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_2200 : span (test 5) 100 2200 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_2300 : span (test 5) 100 2300 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_2400 : span (test 5) 100 2400 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_2500 : span (test 5) 100 2500 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_2600 : span (test 5) 100 2600 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_2700 : span (test 5) 100 2700 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_2800 : span (test 5) 100 2800 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part5_2900 : span (test 5) 23 2900 = true := by decide +kernel
theorem all5 : span (test 5) 2923 0 = true := (@span_join (test 5) 1500 0 1423 (@span_join (test 5) 700 0 800 (@span_join (test 5) 300 0 400 (@span_join (test 5) 100 0 200 part5_0 (@span_join (test 5) 100 100 100 part5_100 part5_200)) (@span_join (test 5) 200 300 200 (@span_join (test 5) 100 300 100 part5_300 part5_400) (@span_join (test 5) 100 500 100 part5_500 part5_600))) (@span_join (test 5) 400 700 400 (@span_join (test 5) 200 700 200 (@span_join (test 5) 100 700 100 part5_700 part5_800) (@span_join (test 5) 100 900 100 part5_900 part5_1000)) (@span_join (test 5) 200 1100 200 (@span_join (test 5) 100 1100 100 part5_1100 part5_1200) (@span_join (test 5) 100 1300 100 part5_1300 part5_1400)))) (@span_join (test 5) 700 1500 723 (@span_join (test 5) 300 1500 400 (@span_join (test 5) 100 1500 200 part5_1500 (@span_join (test 5) 100 1600 100 part5_1600 part5_1700)) (@span_join (test 5) 200 1800 200 (@span_join (test 5) 100 1800 100 part5_1800 part5_1900) (@span_join (test 5) 100 2000 100 part5_2000 part5_2100))) (@span_join (test 5) 400 2200 323 (@span_join (test 5) 200 2200 200 (@span_join (test 5) 100 2200 100 part5_2200 part5_2300) (@span_join (test 5) 100 2400 100 part5_2400 part5_2500)) (@span_join (test 5) 200 2600 123 (@span_join (test 5) 100 2600 100 part5_2600 part5_2700) (@span_join (test 5) 100 2800 23 part5_2800 part5_2900)))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_0 : span (test 6) 100 0 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_100 : span (test 6) 100 100 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_200 : span (test 6) 100 200 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_300 : span (test 6) 100 300 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_400 : span (test 6) 100 400 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_500 : span (test 6) 100 500 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_600 : span (test 6) 100 600 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_700 : span (test 6) 100 700 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_800 : span (test 6) 100 800 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_900 : span (test 6) 100 900 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_1000 : span (test 6) 100 1000 = true := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part6_1100 : span (test 6) 39 1100 = true := by decide +kernel
theorem all6 : span (test 6) 1139 0 = true := (@span_join (test 6) 600 0 539 (@span_join (test 6) 300 0 300 (@span_join (test 6) 100 0 200 part6_0 (@span_join (test 6) 100 100 100 part6_100 part6_200)) (@span_join (test 6) 100 300 200 part6_300 (@span_join (test 6) 100 400 100 part6_400 part6_500))) (@span_join (test 6) 300 600 239 (@span_join (test 6) 100 600 200 part6_600 (@span_join (test 6) 100 700 100 part6_700 part6_800)) (@span_join (test 6) 100 900 139 part6_900 (@span_join (test 6) 100 1000 39 part6_1000 part6_1100))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part7_0 : span (test 7) 60 0 = true := by decide +kernel
theorem all7 : span (test 7) 60 0 = true := part7_0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem part8_0 : span (test 8) 1 0 = true := by decide +kernel
theorem all8 : span (test 8) 1 0 = true := part8_0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem lowerFn : ∀ s, HasCircuitSize 6 fT s → 9 ≤ s := by
  refine prove_base 6 34 8 fT sampleRows inputWords [] number hashes state (by decide +kernel)
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) ?_
  intro s hs
  interval_cases s
  · intro i hi; exact False.elim (Nat.not_lt_zero i hi)
  · intro i hi; exact False.elim (Nat.not_lt_zero i hi)
  · exact fun i hi => span_ok all2 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok all3 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok all4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok all5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok all6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok all7 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok all8 i (Nat.zero_le i) hi

def witness : Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [8, 10]⟩, ⟨.and, [12, 13]⟩], 14⟩

theorem good : PEqualNP.MetaComplexity.Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem values : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = fT x := by decide +kernel

theorem wsize : witness.size = 9 := by decide

end PEqualNP.Outside.L_meta_12232

open PEqualNP.Outside.L_meta_12232 in
theorem PEqualNP.Outside.L_meta_12232 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4261412864 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4261412864 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have hl := lowerFn s h
  exact ⟨witness, good, by rw [wsize]; exact hl, values⟩
