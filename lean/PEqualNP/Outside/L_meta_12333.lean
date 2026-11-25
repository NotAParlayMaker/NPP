import PEqualNP.Defs



namespace PEqualNP.Outside.L_meta_12333.Core

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool



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

theorem next_one {m y a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun m y s ((if neg then a ^^^ m else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
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

theorem next_two_sorted {m y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
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

theorem next_two {m y a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
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
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) →
      next (m) (s+2-zs.length) zs f = true := by
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


theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih



theorem simplify_nonot (op : GateOp) (hop : op ≠ GateOp.not) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op ≠ GateOp.not := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp)
  · exact absurd rfl hop
  · simp at hg
  · simp at hg

theorem elim_nonot (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, g.op ≠ GateOp.not) → (∀ g ∈ acc.2, g.op ≠ GateOp.not) →
    ∀ g ∈ (elim n gs acc).2, g.op ≠ GateOp.not := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hg h
    apply ih (elimStep n acc g) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_nonot _ (hg g List.mem_cons_self) _ _ g' (by simpa using h1)

theorem exists_clean_m (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (h : ∃ C : Circuit, FanInTwo C ∧ (∀ g ∈ C.gates, g.op ≠ GateOp.not) ∧ C.size ≤ s ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    ∃ gs o, CleanL n gs ∧ (∀ (p : ℕ) (g : Gate), gs[p]? = some g → g.op ≠ GateOp.not) ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hC, hsz, hev⟩ := h
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
    refine ⟨acc.2, j, hcl, fun p g hp => elim_nonot n C.gates (initId n, []) hC (fun _ h => by simp at h) g (List.mem_of_getElem? hp), hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

open Classical in
theorem run_live_m (n : ℕ) (inv : BFn n → BFn n) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (hm : ∀ (p : ℕ) (g : Gate), gs[p]? = some g → g.op ≠ GateOp.not) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run inv meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
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
          val gs n (n + p) = (if neg then inv (val gs n j) else val gs n j) →
          Run inv meetF joinF (val gs n o) (d' + 1)
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
      · exact absurd hop (hm p g hg)
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

theorem exists_run_m {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : ∃ C : Circuit, FanInTwo C ∧ (∀ g ∈ C.gates, g.op ≠ GateOp.not) ∧ C.size ≤ s ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (fun a => a) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hm, hlen, ho, hev⟩ := exists_clean_m n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live_m n (fun a => a) gs o hcl hm ho gs.length 0 (by omega)
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




theorem run_nil {α inv meet join y t} (h : @Run α inv meet join y t []) : False := by
  have key : ∀ t ws, @Run α inv meet join y t ws → ws ≠ [] := by
    intro t ws h
    induction h using Run.fold with
    | done => simp
    | perm hp _ ih => exact fun he => ih (List.Perm.eq_nil (he ▸ hp))
    | one => simp
    | two => simp
  exact key t [] h rfl

def isort (l : List ℕ) : List ℕ := l.insertionSort (· ≤ ·)

inductive BT where
  | lf : BT
  | nd : BT → List ℕ → BT → BT

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
  | .lf, _ => false
  | .nd l k r, x => leqL x k || (if ltL x k then l.mem x else r.mem x)

def BT.toList : BT → List (List ℕ)
  | .lf => []
  | .nd l k r => l.toList ++ k :: r.toList

theorem BT.mem_toList : ∀ (T : BT) (x : List ℕ), T.mem x = true → x ∈ T.toList
  | .lf, x, h => by simp [BT.mem] at h
  | .nd l k r, x, hm => by
      simp only [BT.mem, Bool.or_eq_true] at hm
      simp only [BT.toList, List.mem_append, List.mem_cons]
      rcases hm with he | hm
      · exact Or.inr (Or.inl (leqL_eq x k he))
      · split at hm
        · exact Or.inl (BT.mem_toList l x hm)
        · exact Or.inr (Or.inr (BT.mem_toList r x hm))

theorem all_app {α : Type} {p : α → Bool} {A B : List α} (ha : A.all p = true) (hb : B.all p = true) :
    (A ++ B).all p = true := by
  rw [List.all_append, ha, hb]; rfl

theorem cover {p : List ℕ → List (ℕ × ℕ) → Bool} (T : BT) (L : List (List ℕ × List (ℕ × ℕ)))
    (hK : T.toList = L.map Prod.fst) (hL : L.all (fun kh => p kh.1 kh.2) = true) :
    ∀ x, T.mem x = true → ∃ h, p x h = true := by
  intro x hx
  have h1 := BT.mem_toList T x hx
  rw [hK, List.mem_map] at h1
  obtain ⟨kh, hkh, rfl⟩ := h1
  exact ⟨kh.2, List.all_eq_true.1 hL kh hkh⟩


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

def distOK (pD : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pD.all fun dr => Nat.beq (Nat.land dr.2 (accD dr.1 ws)) dr.2

def monoOK (pM : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pM.all fun qp => Nat.beq (Nat.land qp.2 (accM qp.1 ws)) qp.2

def via (y : ℕ) (pD pM : List (ℕ × ℕ)) (t : ℕ) (ws : List ℕ) : Bool :=
  Nat.ble ws.length (t + 1) && (t != 0 || leqL ws [y]) && distOK pD ws &&
    (ws.length != t + 1 || monoOK pM ws)


def prsOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) : Bool :=
  pD.all (fun dr => Nat.beq (Nat.land dr.2 (Nat.xor y (Nat.shiftRight y dr.1))) dr.2 &&
    Nat.beq (Nat.land dr.2 (Nat.xor m (Nat.shiftRight m dr.1))) 0) &&
  pM.all (fun qp => Nat.beq (Nat.land qp.2 y) qp.2 && !Nat.testBit y qp.1)

theorem land_zero {R X i : ℕ} (h : Nat.beq (Nat.land R X) 0 = true) (hi : R.testBit i = true) :
    X.testBit i = false := by
  have he : (R &&& X) = 0 := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and, Nat.zero_testBit] at h2
  exact h2

theorem via_sound {m y : ℕ} {pD pM : List (ℕ × ℕ)} (hp : prsOK m y pD pM = true) {t : ℕ}
    {ws : List ℕ} (h : NatRun m y t ws) : via y pD pM t ws = true := by
  simp only [prsOK, Bool.and_eq_true, List.all_eq_true] at hp
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
    have h12 := hp.1 dr hdr
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
      simp only [monoOK, List.all_eq_true]
      intro qp hqp
      have h1 := hp.2 qp hqp
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
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
    · left; simpa using hlen


def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL, Nat.testBit_bit_zero]
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


def hfind (G : List (List ℕ)) (T : BT) (t : ℕ) (h : List (ℕ × ℕ)) (tag : ℕ) (ys : List ℕ) : Bool :=
  match h.lookup tag with
  | some j =>
    match G[j]? with
    | some pi => T.mem (t :: isort (ys.map (actL pi)))
    | none => false
  | none => false

theorem hfind_false {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) (T : BT) (t : ℕ)
    (ih : ∀ ws, NatRun m y t ws → T.mem (t :: isort ws) = false)
    (h : List (ℕ × ℕ)) (tag : ℕ) {ys : List ℕ} (hys : NatRun m y t ys) : hfind G T t h tag ys = false := by
  unfold hfind
  split
  · split
    · rename_i pi hpi
      have hmem : pi ∈ G := List.mem_of_getElem? hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hmem
      exact ih _ (run_act pi hm hy hys)
    · rfl
  · rfl

def stepOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) :
    List ℕ → List (ℕ × ℕ) → Bool
  | [], _ => false
  | 0 :: _, _ => false
  | (t + 1) :: es, h => !(next m (t + 2 - es.length) es
      (fun tag ys => via y pD pM t ys && !T.mem (t :: isort ys) && !hfind G T t h tag ys))

theorem closure_sound {m y : ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} (T : BT)
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true) :
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
        (fun tag ys => via y pD pM t ys && !T.mem (t :: isort ys) && !hfind G T t h tag ys)
        (fun tag ys hys => by simp [via_sound hp hys, ih ys hys, hfind_false hG T t ih h tag hys])
      rw [hn] at hs; cases hs

def rootOK (y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap : ℕ) (zs : List ℕ) : Bool :=
  !via y pD pM cap zs || T.mem (cap :: isort zs) || G.any (fun pi => T.mem (cap :: isort (zs.map (actL pi))))

theorem cert_core {m y : ℕ} {xs : List ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} {T : BT} {cap : ℕ}
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true)
    (hi : xs.sublists.all (rootOK y pD pM G T cap) = true)
    {s' : ℕ} (hs' : s' ≤ cap) {ws : List ℕ} (hsub : ws.Sublist xs) (hr : NatRun m y s' ws) : False := by
  have hmem := List.all_eq_true.1 hi _ (List.mem_sublists.2 hsub)
  revert hr hmem
  cases ws with
  | nil => intro hr _; exact run_nil hr
  | cons a r =>
    intro hr hmem
    have hcap : NatRun m y cap (a :: r) := extend_run hr hs'
    have hd := via_sound hp hcap
    have hc := closure_sound T hp hG hT cap (a :: r) hcap
    have hg : (G.any fun pi => T.mem (cap :: isort ((a :: r).map (actL pi)))) = false := by
      rw [List.any_eq_false]
      intro pi hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hpi
      rw [closure_sound T hp hG hT cap _ (run_act pi hm hy hcap)]
      simp
    unfold rootOK at hmem
    rw [hd, hc, hg] at hmem
    simp at hmem

theorem lb_cert {n : ℕ} (f : BFn n) (l : List ℕ) (m y : ℕ) (xs : List ℕ)
    (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap lb : ℕ)
    (hlb : cap + 1 = lb)
    (hm : m = 2 ^ l.length - 1)
    (hy : encL f l = y)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map
      (fun a => encL a l) = xs)
    (hnc : ∃ a b : Fin n → Bool, f a ≠ f b)
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true)
    (hi : xs.sublists.all (rootOK y pD pM G T cap) = true) :
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



def idx5 (x : Fin 5 → Bool) : ℕ :=
  (if x 0 then 2 ^ 0 else 0) + (if x 1 then 2 ^ 1 else 0) + (if x 2 then 2 ^ 2 else 0) +
    (if x 3 then 2 ^ 3 else 0) + (if x 4 then 2 ^ 4 else 0)

theorem sum_eq (x : Fin 5 → Bool) : (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) = idx5 x := by
  rw [Fin.sum_univ_five]; rfl


theorem one_le {n : ℕ} (f : BFn n) (hf : f (fun _ => false) = true) :
    ∀ s, HasCircuitSize n f s → 1 ≤ s := by
  intro s hs
  obtain ⟨C, _, hle, hC⟩ := hs
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · exfalso
    have hg : C.gates = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hle)
    have h1 := hC (fun _ => false)
    rw [hf] at h1
    have e : C.eval (List.ofFn fun _ : Fin n => false) = false := by
      unfold Circuit.eval Circuit.wires
      rw [hg, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      split <;> rfl
    rw [e] at h1
    exact Bool.false_ne_true h1
  · exact hpos


-- Repeated truth-table words shared by the two certificates.
abbrev w0 : ℕ := 2863311530
abbrev w1 : ℕ := 4042322160
abbrev w2 : ℕ := 4278255360
abbrev w3 : ℕ := 3435973836
abbrev w4 : ℕ := 4294901760
abbrev w5 : ℕ := 3233857728
abbrev w6 : ℕ := 4244438268
abbrev w7 : ℕ := 2863267840
abbrev w8 : ℕ := 4294945450
abbrev w9 : ℕ := 16711935
abbrev wa : ℕ := 2290649224
abbrev wb : ℕ := 1431655765
abbrev wc : ℕ := 3435921408
abbrev wd : ℕ := 4008636142
abbrev we : ℕ := 4294954188
abbrev wf : ℕ := 3368601800
abbrev w10 : ℕ := 4287168392
abbrev w11 : ℕ := 4293984240
abbrev w12 : ℕ := 4244373504
abbrev w13 : ℕ := 4294951104
abbrev w14 : ℕ := 2829625512
abbrev w15 : ℕ := 4294936712
abbrev w16 : ℕ := 4294923605
abbrev w17 : ℕ := 1431633920
abbrev w18 : ℕ := 4289396650
abbrev w19 : ℕ := 4008574976
abbrev w1a : ℕ := 3435956360
abbrev w1b : ℕ := 3941264106
abbrev w1c : ℕ := 4210752250
abbrev w1d : ℕ := 4008627404
abbrev w1e : ℕ := 3435970752
abbrev w1f : ℕ := 2863333375
abbrev w20 : ℕ := 4294963440
abbrev w21 : ℕ := 2863180456
abbrev w22 : ℕ := 3937069738
abbrev w23 : ℕ := 3435972808
abbrev w24 : ℕ := 4294967040
abbrev w25 : ℕ := 2290614272
abbrev w26 : ℕ := 4287168256
abbrev w27 : ℕ := 4291624908
abbrev w28 : ℕ := 3974950124
abbrev w29 : ℕ := 3435187392
abbrev w2a : ℕ := 4177066232
abbrev w2b : ℕ := 4294962926
abbrev w2c : ℕ := 4294967295
abbrev w2d : ℕ := 3772834016
abbrev w2e : ℕ := 3221274624
abbrev w2f : ℕ := 4294770684
abbrev w30 : ℕ := 1145324612
abbrev w31 : ℕ := 2155905152
abbrev w32 : ℕ := 2863302792
abbrev w33 : ℕ := 4294963200
abbrev w34 : ℕ := 4210096880
abbrev w35 : ℕ := 3435711688
abbrev w36 : ℕ := 4205509290
abbrev w37 : ℕ := 3233808384
abbrev w38 : ℕ := 3941253312
abbrev w39 : ℕ := 4286644096
abbrev w3a : ℕ := 1431699455
abbrev w3b : ℕ := 4278124286
abbrev w3c : ℕ := 4026593280
abbrev w3d : ℕ := 4294966524
abbrev w3e : ℕ := 4294934656
abbrev w3f : ℕ := 11141290
abbrev w40 : ℕ := 2868882175
abbrev w41 : ℕ := 13369548
abbrev w42 : ℕ := 16711680
abbrev w43 : ℕ := 4294902015
abbrev w44 : ℕ := 3722304989
abbrev w45 : ℕ := 4008618666
abbrev w46 : ℕ := 4294705152
abbrev w47 : ℕ := 4244416680
abbrev w48 : ℕ := 4278059008
abbrev w49 : ℕ := 4294950912
abbrev w4a : ℕ := 4278190080
abbrev w4b : ℕ := 252645135
abbrev w4c : ℕ := 4293918720
abbrev w4d : ℕ := 3439316223
abbrev w4e : ℕ := 4289265576
abbrev w4f : ℕ := 2863311016
abbrev w50 : ℕ := 4244425932
abbrev w51 : ℕ := 4210688000
abbrev w52 : ℕ := 3435986943
abbrev w53 : ℕ := 983055
abbrev w54 : ℕ := 5570645
abbrev w55 : ℕ := 2852170240
abbrev w56 : ℕ := 268374015
abbrev w57 : ℕ := 1442797055
abbrev w58 : ℕ := 2863300736
abbrev w59 : ℕ := 4241292492
abbrev w5a : ℕ := 4289396480
abbrev w5b : ℕ := 3435973824
abbrev w5c : ℕ := 4290838464
abbrev w5d : ℕ := 3422604288
abbrev w5e : ℕ := 3941247658
abbrev w5f : ℕ := 3364407432
abbrev w60 : ℕ := 1154237644
abbrev w61 : ℕ := 4278102698
abbrev w62 : ℕ := 4288741280
abbrev w63 : ℕ := 4294945280
abbrev w64 : ℕ := 4290838272
abbrev w65 : ℕ := 4291559424
abbrev w66 : ℕ := 16777215
abbrev w67 : ℕ := 3368599744
abbrev w68 : ℕ := 3941203968
abbrev w69 : ℕ := 4289331200
abbrev w6a : ℕ := 4042260480
abbrev w6b : ℕ := 4244435184
abbrev w6c : ℕ := 4042318048
abbrev w6d : ℕ := 4244434156
abbrev w6e : ℕ := 4294953984
abbrev w6f : ℕ := 1442775040
abbrev w70 : ℕ := 4294944936
abbrev w71 : ℕ := 3993038336
abbrev w72 : ℕ := 4210749680
abbrev w73 : ℕ := 4227922944
abbrev w74 : ℕ := 268369920
abbrev w75 : ℕ := 4194368000
abbrev w76 : ℕ := 2868838400
abbrev w77 : ℕ := 4294919236
abbrev w78 : ℕ := 3722248192
abbrev w79 : ℕ := 4294901930
abbrev w7a : ℕ := 4293962400
abbrev w7b : ℕ := 4294942880
abbrev w7c : ℕ := 3925928448
abbrev w7d : ℕ := 2694881440
abbrev w7e : ℕ := 3435970560
abbrev w7f : ℕ := 4205506560
abbrev w80 : ℕ := 3368077504
abbrev w81 : ℕ := 4294954176
abbrev w82 : ℕ := 3431517320
abbrev w83 : ℕ := 4291624704
abbrev w84 : ℕ := 3936938112
abbrev w85 : ℕ := 3974941900
abbrev w86 : ℕ := 2829582336
abbrev w87 : ℕ := 4278583045
abbrev w88 : ℕ := 4177064176
abbrev w89 : ℕ := 3229663360
abbrev w8a : ℕ := 4243389676
abbrev w8b : ℕ := 4042301600
abbrev w8c : ℕ := 3435938884
abbrev w8d : ℕ := 4294901845
abbrev w8e : ℕ := 3722300620
abbrev w8f : ℕ := 4241227776
abbrev w90 : ℕ := 4294901775
abbrev w91 : ℕ := 4294961898
abbrev w92 : ℕ := 4276677288
abbrev w93 : ℕ := 4278254592
abbrev w94 : ℕ := 4204853920
abbrev w95 : ℕ := 4210094320
abbrev w96 : ℕ := 267390960
abbrev w97 : ℕ := 4289265408
abbrev w98 : ℕ := 4261477888
abbrev w99 : ℕ := 3284386755
abbrev w9a : ℕ := 4278254080
abbrev w9b : ℕ := 4243651824
abbrev w9c : ℕ := 4294958557
abbrev w9d : ℕ := 3435972744
abbrev w9e : ℕ := 100599295
abbrev w9f : ℕ := 1145307136
abbrev wa0 : ℕ := 3368550400
abbrev wa1 : ℕ := 4294966010
abbrev wa2 : ℕ := 3435134976
abbrev wa3 : ℕ := 4241280204
abbrev wa4 : ℕ := 4277993212
abbrev wa5 : ℕ := 4294757580
namespace Cert0


def L_ : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def M_ : ℕ := w2c
def Y_ : ℕ := w84
def XS_ : List ℕ := [w0,w3,w1,w2,w4]
def PD_ : List (ℕ × ℕ) := [(1,357831744),(2,268571168),(4,67241480),(8,4325480),(16,552)]
def PM_ : List (ℕ × ℕ) := [(3,w84),(5,w84),(9,w84),(17,w84),(22,w84),(26,w84),(28,w84)]

def G_ : List (List ℕ) := [[0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,16,17,18,19,24,25,26,27,20,21,22,23,28,29,30,31],[0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15,16,17,20,21,18,19,22,23,24,25,28,29,26,27,30,31],[0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15,16,17,20,21,24,25,28,29,18,19,22,23,26,27,30,31],[0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15,16,17,24,25,18,19,26,27,20,21,28,29,22,23,30,31],[0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15,16,17,24,25,20,21,28,29,18,19,26,27,22,23,30,31]]


noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [2,w14,w7c,w13] BT.lf) [2,w14,w38,w2] BT.lf) [2,w58,3907578088,w2] (BT.nd (BT.nd BT.lf [2,w58,w7c,w6] BT.lf) [3,wa,w7d,w38,w2] BT.lf)) [3,wa,w7,3768639648,w2] (BT.nd (BT.nd (BT.nd BT.lf [3,wa,w7,w2d,w71] BT.lf) [3,wa,w7,w2d,w2] BT.lf) [3,w14,w7,w5,w2] (BT.nd (BT.nd BT.lf [3,w14,w7,w67,w2] BT.lf) [3,w14,w7,w38,w2] BT.lf))) [3,w14,w58,w5,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,w14,w0,w38,w2] BT.lf) [3,w14,w5,w7c,w4] BT.lf) [3,w14,w5,w68,w2] (BT.nd (BT.nd BT.lf [3,w14,w5,w38,w2] BT.lf) [3,w14,w3,w38,w2] BT.lf)) [3,w14,w38,w6,w2] (BT.nd (BT.nd (BT.nd BT.lf [3,w14,w38,w2] BT.lf) [3,w14,w38,w2,w4] BT.lf) [3,w14,w1b,w2,w13] (BT.nd (BT.nd BT.lf [3,w14,w1d,w72,w2] BT.lf) [3,2863179944,w5,w2,w4] BT.lf)))) [3,w21,w5,w73,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,w58,w3,w7c,w1] BT.lf) [3,w58,w1b,w6,w2] BT.lf) [3,w32,wc,w2d,w2] (BT.nd (BT.nd BT.lf [3,2863310984,w7e,w1,w2] BT.lf) [3,w4f,w5,w12,w2] BT.lf)) [3,w0,w5,w73,w46] (BT.nd (BT.nd (BT.nd BT.lf [3,w0,w5,w12,w93] BT.lf) [3,w0,w5f,w11,w33] BT.lf) [3,w0,w3,w94,w33] (BT.nd (BT.nd BT.lf [3,w0,w3,w7f,w34] BT.lf) [3,w0,w3,w7f,w11] BT.lf))) [3,w0,w3,w95,w5a] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,w0,w3,4210618608,w5a] BT.lf) [3,w0,w85,w72,4288741120] BT.lf) [3,w3,w22,w11,w33] (BT.nd (BT.nd BT.lf [3,w22,w59,w11,w4] BT.lf) [4,43690,w7,w3,w1,w2] BT.lf)) [4,11184810,w7,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [4,16776960,w0,w3,w1] BT.lf) [4,67043328,w0,w3,w1,w2] BT.lf) [4,178913280,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [4,w96,w0,w3,w3c,w4] BT.lf) [4,w96,w0,w3,w4] BT.lf))))) [4,w74,w0,w3,w3c,w11] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w74,w0,w3,w1,w2] BT.lf) [4,715795114,w3,w1,w2,w4] BT.lf) [4,1073676288,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [4,1154272460,w7,w0,w1,w2] BT.lf) [4,1154272460,w0,w1,w2,w4] BT.lf)) [4,1288457420,w0,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,1431677610,w3,w1,w2] BT.lf) [4,1437226410,w3,w1,w4] BT.lf) [4,1610547200,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [4,w25,w0,w1d,w1,w2] BT.lf) [4,w25,w0,w1d,w1,w26] BT.lf))) [4,wa,w7d,w7,w5,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,wa,2862656160,w3,w3c,w4] BT.lf) [4,wa,w7,w0,w2d,w2] BT.lf) [4,wa,w7,w3,w2d,w2] (BT.nd (BT.nd BT.lf [4,wa,w7,w2d,wd,w2] BT.lf) [4,wa,w7,w2d,w1,w2] BT.lf)) [4,wa,w7,w2d,w2] (BT.nd (BT.nd (BT.nd BT.lf [4,wa,w7,w2d,w2,w4] BT.lf) [4,wa,w7,w1b,w1,w2] BT.lf) [4,wa,w7,w28,w1,w2] (BT.nd (BT.nd BT.lf [4,wa,w7,wd,w1,w2] BT.lf) [4,wa,2863308800,w3,w1,w2] BT.lf)))) [4,wa,w0,3768639648,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,wa,w0,w2d,w71,w4] BT.lf) [4,wa,w0,w2d,w19,w2] BT.lf) [4,wa,w0,w2d,w2,w4] (BT.nd (BT.nd BT.lf [4,wa,w0,w38,w1,w2] BT.lf) [4,wa,w2d,w71,w4] BT.lf)) [4,wa,w2d,w19,w2] (BT.nd (BT.nd (BT.nd BT.lf [4,wa,w22,w1,w2,w4] BT.lf) [4,2290657962,w7,w3,w1,w2] BT.lf) [4,2576980377,w1,w2,w4] (BT.nd (BT.nd BT.lf [4,2827528328,w7,w3,w1,w2] BT.lf) [4,w86,w0,w3,w72,w2] BT.lf))) [4,w14,w7,w0,w5,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w14,w7,w5,w3,w2] BT.lf) [4,w14,w7,w5,w6,w2] BT.lf) [4,w14,w7,w5,w2] (BT.nd (BT.nd BT.lf [4,w14,w7,w5,w2,w4] BT.lf) [4,w14,w7,w3,w1,w2] BT.lf)) [4,w14,w7,w3,w72,w2] (BT.nd (BT.nd (BT.nd BT.lf [4,w14,w0,w5,w2,w4] BT.lf) [4,w14,w0,w5,w2,w13] BT.lf) [4,w14,w5,w1b,w2,w4] (BT.nd BT.lf [4,2863136768,w21,w3,w1,w2] BT.lf)))))) [4,2863136768,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863179944,w3,w1,w2,w4] BT.lf) [4,w21,w7,w3,w1,w2] BT.lf) [4,w21,w5,w6,w2,w4] (BT.nd (BT.nd BT.lf [4,w21,w29,w1,w2,w4] BT.lf) [4,w21,w3,w1,w2,w46] BT.lf)) [4,w21,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,w7,w4f,w3,w1,w2] BT.lf) [4,w7,w0,w5,w28,w2] BT.lf) [4,w7,w0,w5,w6,w2] (BT.nd (BT.nd BT.lf [4,w7,w0,w5f,w1,w2] BT.lf) [4,w7,w0,w67,w6,w2] BT.lf))) [4,w7,w0,wf,w1,w75] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w7,w0,wf,w1,w2] BT.lf) [4,w7,w0,3435711680,w1,w2] BT.lf) [4,w7,w0,w35,w1,w2] (BT.nd (BT.nd BT.lf [4,w7,w0,w23,w1,w2] BT.lf) [4,w7,w0,w5b,w1,w2] BT.lf)) [4,w7,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [4,w7,w0,w3,w1,w87] BT.lf) [4,w7,w0,w3,w1,4286643968] BT.lf) [4,w7,w0,w3,w1,w39] (BT.nd (BT.nd BT.lf [4,w7,w0,w3,w1,w26] BT.lf) [4,w7,w0,w3,w1,w97] BT.lf)))) [4,w7,w0,w3,w88,w26] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w7,w0,w3,w7f,w11] BT.lf) [4,w7,w0,w3,w95,w5a] BT.lf) [4,w7,2863639215,w3,w1,w2] (BT.nd (BT.nd BT.lf [4,w7,w3,w22,w1,w2] BT.lf) [4,2863289685,w0,w3,w1,w2] BT.lf)) [4,2863289685,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [4,2863300608,w0,w3,w1,w2] BT.lf) [4,w58,w0,w5,w6,w2] BT.lf) [4,w58,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [4,w58,w3,w1b,w1,w2] BT.lf) [4,2863302784,w0,w3,w1,w2] BT.lf))) [4,w32,2863308960,w3,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w32,w0,w1e,w1,w2] BT.lf) [4,w32,wc,wd,w1,w2] BT.lf) [4,w32,w3,w2d,w2,w4] (BT.nd (BT.nd BT.lf [4,w32,w28,w1,w2,w4] BT.lf) [4,2863310984,w3,w1,w2,w4] BT.lf)) [4,2863310984,w3,w1,w2,w33] (BT.nd (BT.nd (BT.nd BT.lf [4,w4f,w5,w6,w2,w4] BT.lf) [4,w4f,w1e,w1,w2,w4] BT.lf) [4,w4f,w3,w1,w12,w2] (BT.nd BT.lf [4,w4f,w3,w1,w93,w4] BT.lf))))) [4,w4f,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w4f,w3,w1,w2,w24] BT.lf) [4,2863311528,w3,w1,w2,w4] BT.lf) [4,w0,2863595520,w3,w1,w2] (BT.nd (BT.nd BT.lf [4,w0,2867724288,w3,w1,w2] BT.lf) [4,w0,w76,w3,w1,w2] BT.lf)) [4,w0,2868838485,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,2952724480,w3,w1,w2] BT.lf) [4,w0,w2e,w3,w11,w33] BT.lf) [4,w0,w2e,w59,w11,w4] (BT.nd (BT.nd BT.lf [4,w0,w89,w8a,w2,w4] BT.lf) [4,w0,w89,w6,w2,w4] BT.lf))) [4,w0,w5,3907578088,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w5,w7c,w6,w4] BT.lf) [4,w0,w5,w68,w6,w2] BT.lf) [4,w0,w5,w38,w6,w2] (BT.nd (BT.nd BT.lf [4,w0,w5,w28,w2,w4] BT.lf) [4,w0,w5,w28,w2,w13] BT.lf)) [4,w0,w5,w71,w6,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w5,w19,w6,w2] BT.lf) [4,w0,w5,w73,w2f,w4] BT.lf) [4,w0,w5,4238933160,w2,w4] (BT.nd (BT.nd BT.lf [4,w0,w5,w8a,w2,w4] BT.lf) [4,w0,w5,w12,w2,w3d] BT.lf)))) [4,w0,w5,w47,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w5,w50,w2,w20] BT.lf) [4,w0,w5,w6d,w2,w4] BT.lf) [4,w0,w5,4244438016,w2,w4] (BT.nd (BT.nd BT.lf [4,w0,w5,4244438220,w2,w4] BT.lf) [4,w0,w5,w6,w98,w4] BT.lf)) [4,w0,w5,w6,w48,w2] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w5,w6,w93,w4] BT.lf) [4,w0,w5,w6,w2,w69] BT.lf) [4,w0,w5,w6,w2,w46] (BT.nd (BT.nd BT.lf [4,w0,w5,w6,w2,w4] BT.lf) [4,w0,w5,w6,w2,w16] BT.lf))) [4,w0,w5,w6,w2,w3e] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w5,w6,w2,w49] BT.lf) [4,w0,w5,w6,w2,w13] BT.lf) [4,w0,w5,w6,w2,w6e] (BT.nd (BT.nd BT.lf [4,w0,w5,w6,w2,4294966272] BT.lf) [4,w0,w5,w6,w39,w4] BT.lf)) [4,w0,w5,4261281277,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w5,w2,4294769916,w4] BT.lf) [4,w0,3234647244,w1,w2,w4] BT.lf) [4,w0,w99,w6,w2,w4] (BT.nd BT.lf [4,w0,w99,w2,w4] BT.lf))))))) [4,w0,w5f,4037079200,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w5f,w1,4205445120,w2] BT.lf) [4,w0,w5f,w1,w2,w4] BT.lf) [4,w0,w5f,w1,w2,w33] (BT.nd (BT.nd BT.lf [4,w0,w80,w6,w2,w4] BT.lf) [4,w0,w67,w1d,w1,w2] BT.lf)) [4,w0,w67,w1,w2,we] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w67,w6,w2,w4] BT.lf) [4,w0,3368601736,w1,w2,w4] BT.lf) [4,w0,3368601792,w1,w2,w4] (BT.nd (BT.nd BT.lf [4,w0,wf,w2d,w2,w4] BT.lf) [4,w0,wf,w68,w1,w2] BT.lf))) [4,w0,wf,w71,w1,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,wf,w19,w1,w2] BT.lf) [4,w0,wf,w6a,w2,w20] BT.lf) [4,w0,wf,w8b,w2,w4] (BT.nd (BT.nd BT.lf [4,w0,wf,w1,w75,w51] BT.lf) [4,w0,wf,w1,w75,w4] BT.lf)) [4,w0,wf,w1,w51,w2] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,wf,w1,w98,w4] BT.lf) [4,w0,wf,w1,w48,w2] BT.lf) [4,w0,wf,w1,w9a,w4] (BT.nd (BT.nd BT.lf [4,w0,wf,w1,w2,w69] BT.lf) [4,w0,wf,w1,w2,4294574080] BT.lf)))) [4,w0,wf,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,wf,w1,w2,4294903045] BT.lf) [4,w0,wf,w1,w2,w16] BT.lf) [4,w0,wf,w1,w2,w13] (BT.nd (BT.nd BT.lf [4,w0,wf,w1,w2,4294952960] BT.lf) [4,w0,wf,w1,w2,w6e] BT.lf)) [4,w0,wf,w1,w2,w33] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,wf,w1,w87,w4] BT.lf) [4,w0,wf,4126537205,w2,w4] BT.lf) [4,w0,wf,4176541936,w2,w4] (BT.nd (BT.nd BT.lf [4,w0,wf,w88,w2,w4] BT.lf) [4,w0,wf,w9b,w2,w4] BT.lf))) [4,w0,wf,w6b,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,wf,w2,4293980400,w4] BT.lf) [4,w0,3368602828,w1,w2,w4] BT.lf) [4,w0,3368863948,w1,w2,w4] (BT.nd (BT.nd BT.lf [4,w0,w29,w1,w2,w46] BT.lf) [4,w0,w29,w1,w10,w4] BT.lf)) [4,w0,3435710664,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,3435711680,w1,w2,w4] BT.lf) [4,w0,w35,w1,w51,w2] BT.lf) [4,w0,w35,w1,w2,4294574080] (BT.nd (BT.nd BT.lf [4,w0,w35,w1,w2,w4] BT.lf) [4,w0,wc,w1d,w1,w2] BT.lf))))) [4,w0,3435934515,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w8c,w1,w2,we] BT.lf) [4,w0,w8c,w1,w2,w9c] BT.lf) [4,w0,w7e,w1,w2,we] (BT.nd (BT.nd BT.lf [4,w0,w7e,w1,w2,4294966476] BT.lf) [4,w0,w1e,w1d,w1,w2] BT.lf)) [4,w0,w1e,w1,w93,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w1e,w1,w2,w15] BT.lf) [4,w0,w1e,w1,w2,w6e] BT.lf) [4,w0,w1e,w1,w2,we] (BT.nd (BT.nd BT.lf [4,w0,w1e,w2a,w2,w4] BT.lf) [4,w0,w9d,w1,w2,w4] BT.lf))) [4,w0,w9d,w1,w2,w33] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,3435972800,w1,w2,w4] BT.lf) [4,w0,w23,w1,w51,w2] BT.lf) [4,w0,w23,w1,w9a,w4] (BT.nd (BT.nd BT.lf [4,w0,w23,w1,w2,w4] BT.lf) [4,w0,w23,w1,w2,w13] BT.lf)) [4,w0,w5b,w1,w2,w4c] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w5b,w1,w2,w4] BT.lf) [4,w0,w5b,w1,w2,w13] BT.lf) [4,w0,w5b,w1,w2,w81] (BT.nd (BT.nd BT.lf [4,w0,w5b,w1,w2,we] BT.lf) [4,w0,3435973832,w1,w2,w4] BT.lf)))) [4,w0,w3,3489595392,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,3937009664,w1,w2] BT.lf) [4,w0,w3,3937058816,w1,w2] BT.lf) [4,w0,w3,w68,w1,w2] (BT.nd (BT.nd BT.lf [4,w0,w3,w38,w1,w2] BT.lf) [4,w0,w3,w38,w6,w2] BT.lf)) [4,w0,w3,w85,w72,w2] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,4008312832,w1,w2] BT.lf) [4,w0,w3,4008365248,w1,w2] BT.lf) [4,w0,w3,4008443904,w1,w2] (BT.nd (BT.nd BT.lf [4,w0,w3,w19,w1,w2] BT.lf) [4,w0,w3,w19,w1,4279369489] BT.lf))) [4,w0,w3,4008592452,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,4008624320,w1,w2] BT.lf) [4,w0,w3,w1d,w1,w26] BT.lf) [4,w0,w3,4008632320,w1,w2] (BT.nd (BT.nd BT.lf [4,w0,w3,4009689088,w1,w2] BT.lf) [4,w0,w3,w1,4277010432,w2] BT.lf)) [4,w0,w3,w1,4277071872,w2] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,4277927936,w2] BT.lf) [4,w0,w3,w1,w48,w2] BT.lf) [4,w0,w3,w1,w2,w46] (BT.nd BT.lf [4,w0,w3,w1,w2,4294836224] BT.lf)))))) [4,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w2,4294901763] BT.lf) [4,w0,w3,w1,w2,4294901765] BT.lf) [4,w0,w3,w1,w2,4294901828] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w2,w8d] BT.lf) [4,w0,w3,w1,w2,4294901952] BT.lf)) [4,w0,w3,w1,w2,4294903125] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w2,4294918208] BT.lf) [4,w0,w3,w1,w2,w77] BT.lf) [4,w0,w3,w1,w2,4294923348] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w2,w16] BT.lf) [4,w0,w3,w1,w2,4294934528] BT.lf))) [4,w0,w3,w1,w2,w3e] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w2,4294936704] BT.lf) [4,w0,w3,w1,w2,w49] BT.lf) [4,w0,w3,w1,w2,4294951040] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w2,w13] BT.lf) [4,w0,w3,w1,w2,4294952132] BT.lf)) [4,w0,w3,w1,w2,4294953152] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w2,w81] BT.lf) [4,w0,w3,w1,w2,4294956501] BT.lf) [4,w0,w3,w1,4278255363,w4] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,4278255365,w4] BT.lf) [4,w0,w3,w1,4278320897,w4] BT.lf)))) [4,w0,w3,w1,4278517508,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,4278583040,w4] BT.lf) [4,w0,w3,w1,w87,w4] BT.lf) [4,w0,w3,w1,w87,4294903045] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,4279041792,w4] BT.lf) [4,w0,w3,w1,4279631637,w4] BT.lf)) [4,w0,w3,w1,4286643968,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w39,w4] BT.lf) [4,w0,w3,w1,w39,w3e] BT.lf) [4,w0,w3,w1,w39,w13] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w26,w69] BT.lf) [4,w0,w3,w1,w26,w4] BT.lf))) [4,w0,w3,w1,w26,w15] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w26,we] BT.lf) [4,w0,w3,w1,4287168384,w4] BT.lf) [4,w0,w3,w1,w10,4294936576] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w10,w6e] BT.lf) [4,w0,w3,w1,w97,w4] BT.lf)) [4,w0,w3,w1,w5a,w65] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w5a,4291611852] BT.lf) [4,w0,w3,4059165169,4279369489,w4] BT.lf) [4,w0,w3,4169726088,w11,w4] (BT.nd BT.lf [4,w0,w3,4176541936,w10,w4] BT.lf))))) [4,w0,w3,w88,w26,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w7f,w11] BT.lf) [4,w0,w3,w7f,w11,w4] BT.lf) [4,w0,w3,w36,w11,w33] (BT.nd (BT.nd BT.lf [4,w0,w3,w95,w5a] BT.lf) [4,w0,w3,w95,w5a,w4] BT.lf)) [4,w0,w3,w72,w5a,w11] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311535,w3,w1,w2,w4] BT.lf) [4,w1f,w3,w1,w2,w16] BT.lf) [4,2863377067,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [4,w5,w22,w6,w2,w4] BT.lf) [4,w5f,w22,w1,w2,w4] BT.lf))) [4,wf,w22,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w3,3937009664,w22,w1,w2] BT.lf) [4,w3,3937053354,w1,w2,w4] BT.lf) [4,w3,w22,w1,w2,w4] (BT.nd (BT.nd BT.lf [4,w3,w22,w1,w2,w49] BT.lf) [4,w3,w22,w1,w2,w13] BT.lf)) [4,w3,w22,w1,w5c,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,0,w7,w0,w3,w1,w2] BT.lf) [5,0,w0,w3,w1,w2,w4] BT.lf) [5,0,w0,w3,w1,w2,w16] (BT.nd (BT.nd BT.lf [5,15,w0,w3,w1,w2,w4] BT.lf) [5,85,w0,w3,w1,w2,w4] BT.lf)))) [5,170,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,204,w0,w3,w1,w2,w4] BT.lf) [5,255,w7,w0,w3,w1,w2] BT.lf) [5,255,w0,w3,w1,w4a] (BT.nd (BT.nd BT.lf [5,255,w0,w3,w1,w2,w4] BT.lf) [5,4095,w0,w3,w1,w2] BT.lf)) [5,4095,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,4095,w0,w3,w1,w2,w33] BT.lf) [5,17476,w0,w3,w1,w2,w4] BT.lf) [5,21845,w7,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [5,21845,w7,w3,w1,w2] BT.lf) [5,21845,w0,w3,w1,w2,w4] BT.lf))) [5,21845,w0,w3,w1,w2,w16] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,21845,w1f,w3,w1,w2,w4] BT.lf) [5,22015,w0,w3,w1,w2,w4] BT.lf) [5,34952,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,43690,65535,w7,w3,w1,w2] BT.lf) [5,43690,w9,w0,w3,w1] BT.lf)) [5,43690,wb,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [5,43690,w3a,w7,w3,w1,w2] BT.lf) [5,43690,w3a,w3,w1,w2] BT.lf) [5,43690,w7,w0,w3,w1,w2] (BT.nd BT.lf [5,43690,w7,w3,w1,w2] BT.lf)))))))) [5,43690,w7,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,43690,w0,w3,w1,w2] BT.lf) [5,43690,w0,w3,w1,w2,w4] BT.lf) [5,43690,w0,w3,w1,w2,w16] (BT.nd (BT.nd BT.lf [5,43690,w1f,w3,w1,w2] BT.lf) [5,43690,w1f,w3,w1,w2,w4] BT.lf)) [5,49344,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,52428,w7,w0,w3,w1,w2] BT.lf) [5,52428,w0,wc,w1,w2,w4] BT.lf) [5,52428,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,52428,w0,w52,w1,w2] BT.lf) [5,52428,w0,w52,w1,w2,w4] BT.lf))) [5,61166,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,61166,w0,w3,w1,w2,w4] BT.lf) [5,64764,w0,w3,w1,w2,w4] BT.lf) [5,65535,w9,w4b,w0,w3] (BT.nd (BT.nd BT.lf [5,65535,w9,wb,w3,w1] BT.lf) [5,65535,w9,w0,w3,w1] BT.lf)) [5,65535,wb,w7,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [5,65535,wb,w3,w1,w2] BT.lf) [5,65535,wa,wd,w1,w2] BT.lf) [5,65535,w7,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [5,65535,w7,w3,w1,w2,w8] BT.lf) [5,65535,w0,w5,w6,w2] BT.lf)))) [5,65535,w0,w5,w6,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,65535,w0,wf,w1,w2] BT.lf) [5,65535,w0,wf,w1,w2,w4] BT.lf) [5,65535,w0,wc,w1,w2,we] (BT.nd (BT.nd BT.lf [5,65535,w0,w3,w19,w1,w2] BT.lf) [5,65535,w0,w3,w1,w2] BT.lf)) [5,65535,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,65535,w0,w3,w1,w2,w16] BT.lf) [5,65535,w0,w3,w1,w2,w13] BT.lf) [5,196611,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,327685,w0,w3,w1,w2,w4] BT.lf) [5,655370,w0,w3,w1,w2,w4] BT.lf))) [5,786444,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,983040,w0,w3,w1,w2,w4] BT.lf) [5,w53,w7,w0,w3,w1,w2] BT.lf) [5,w53,w0,w3,w3c,w11,w4] (BT.nd (BT.nd BT.lf [5,w53,w0,w3,w3c,w4] BT.lf) [5,w53,w0,w3,w1,w2,w4] BT.lf)) [5,983295,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,1048575,w0,w3,w1,w2,w4] BT.lf) [5,4128831,w0,w3,w1,w2,w4] BT.lf) [5,4456516,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,5570560,w0,w3,w1,w2,w4] BT.lf) [5,w54,w55,w3,w1,w4] BT.lf))))) [5,w54,w7,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w54,w0,w82,w1,w2,w4] BT.lf) [5,w54,w0,w3,w1,w2,w69] BT.lf) [5,w54,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w54,w0,w3,w1,w2,w8d] BT.lf) [5,w54,w0,w3,4042649845,w2,w4] BT.lf)) [5,5570815,w7,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [5,5570815,w0,w3,w1,w2,w4] BT.lf) [5,5592405,w0,w3,w1,w2,w4] BT.lf) [5,5636095,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [5,5636095,w0,w3,w1,w2,w69] BT.lf) [5,5636095,w0,w3,w1,w2,w4] BT.lf))) [5,6226015,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,8913032,w0,w3,w1,w2,w4] BT.lf) [5,11141120,w7,w0,w3,w1,w2] BT.lf) [5,11141120,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w3f,w55,w3,w1,w2,w4] BT.lf) [5,w3f,w7,w0,w3,w1,w2] BT.lf)) [5,w3f,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w3f,w40,w3,w1,w2,w4] BT.lf) [5,w3f,w40,w3,w1,w4] BT.lf) [5,11184810,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,12583104,w0,w3,w1,w2,w4] BT.lf) [5,13369344,w0,w3,w1,w2,w4] BT.lf)))) [5,w41,w7,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w41,w0,w5d,w1,w2,w4] BT.lf) [5,w41,w0,w3,w1,w2,w4] BT.lf) [5,w41,w0,w4d,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w41,w0,w4d,w1,w4] BT.lf) [5,13421772,w0,w3,w1,w2,w4] BT.lf)) [5,15597806,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,15597806,w0,w3,w1,w4] BT.lf) [5,16515324,w0,w3,w1,w2,w4] BT.lf) [5,w42,w7,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [5,w42,w0,w3,w1,w4a,w2] BT.lf) [5,w42,w0,w3,w1,w2,w4] BT.lf))) [5,w42,w0,w3,w1,w2,w43] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w42,w0,w3,w1,w2,we] BT.lf) [5,w42,w0,w3,w1,w43] BT.lf) [5,16711850,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,16711884,w0,w3,w1,w2,w4] BT.lf) [5,w9,w4b,858993459,w0,w4] BT.lf)) [5,w9,w4b,wb,w3,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w9,w4b,w7,w0,w3] BT.lf) [5,w9,w4b,w0,w3,w4] BT.lf) [5,w9,wb,w7,w3,w1] (BT.nd BT.lf [5,w9,wb,w3,w1,w4] BT.lf)))))) [5,w9,wb,w3,w1,w16] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w9,w3a,w0,w3,w1] BT.lf) [5,w9,wa,wd,w1,w4] BT.lf) [5,w9,w55,w3,w1,w18,w4] (BT.nd (BT.nd BT.lf [5,w9,w7,w0,w3,w1] BT.lf) [5,w9,w7,w0,w3,w1,w2] BT.lf)) [5,w9,w7,w3,w1,w8] (BT.nd (BT.nd (BT.nd BT.lf [5,w9,w0,w76,w3,w1] BT.lf) [5,w9,w0,w76,w3,w1,w2] BT.lf) [5,w9,w0,w5,w6,w2,w4] (BT.nd (BT.nd BT.lf [5,w9,w0,w5,w6,w4] BT.lf) [5,w9,w0,wf,w1,w2,w4] BT.lf))) [5,w9,w0,wf,w1,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w9,w0,w5d,w1,w27,w4] BT.lf) [5,w9,w0,w82,w1,w2,w4] BT.lf) [5,w9,w0,w82,w1,w4] (BT.nd (BT.nd BT.lf [5,w9,w0,wc,w1,we] BT.lf) [5,w9,w0,w3,w71,w1,w4] BT.lf)) [5,w9,w0,w3,w19,w1] (BT.nd (BT.nd (BT.nd BT.lf [5,w9,w0,w3,w19,w1,w2] BT.lf) [5,w9,w0,w3,w1,w2,w69] BT.lf) [5,w9,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w9,w0,w3,w1,w2,w16] BT.lf) [5,w9,w0,w3,w1,w2,w13] BT.lf)))) [5,w9,w0,w3,w1,w2,w6e] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w9,w0,w3,w1,w69] BT.lf) [5,w9,w0,w3,w1,w4] BT.lf) [5,w9,w0,w3,w1,w16] (BT.nd (BT.nd BT.lf [5,w9,w0,w3,w1,w13] BT.lf) [5,w9,w0,w3,w1,w6e] BT.lf)) [5,16715775,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,16733695,w0,w3,w1,w2,w4] BT.lf) [5,w66,w7,w0,w3,w1,w2] BT.lf) [5,w66,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w66,w0,w3,w1,w24] BT.lf) [5,67044351,w0,w3,w1,w2,w4] BT.lf))) [5,89458005,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w9e,w0,w3,w1,w75,w4] BT.lf) [5,w9e,w0,w3,w1,w2,w4] BT.lf) [5,w9e,w0,w3,w1,w4] (BT.nd (BT.nd BT.lf [5,178916010,w0,w3,w1,w2,w4] BT.lf) [5,214699212,w0,w3,w1,w2,w4] BT.lf)) [5,w74,w56,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [5,w74,w0,w3,w3c,w1,w2] BT.lf) [5,w74,w0,w3,w1,w2] BT.lf) [5,w74,w0,w3,w1,w2,w4] (BT.nd BT.lf [5,w56,w7,w0,w3,w1,w2] BT.lf))))) [5,w56,w0,w3,w3c,w11,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w56,w0,w3,w1,w2,w4] BT.lf) [5,w56,w0,w3,w1,w2,w33] BT.lf) [5,w56,w0,w3,w11,w4] (BT.nd (BT.nd BT.lf [5,268435455,w0,w3,w1,w2,w4] BT.lf) [5,1073692671,w0,w3,w1,w2,w4] BT.lf)) [5,1077952576,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w9f,w0,w3,w1,w2,w4] BT.lf) [5,w30,wa,w0,w1,w2,w4] BT.lf) [5,w30,w7,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [5,w30,w0,w3,w1,w2,w4] BT.lf) [5,w30,w0,w3,w1,w2,w77] BT.lf))) [5,w30,w0,w3,w1,w2,w16] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w30,w0,w44,w1,w2,w4] BT.lf) [5,w30,w44,w1,w2,w4] BT.lf) [5,1145359564,w7,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [5,1145359564,w0,w3,w1,w2,w4] BT.lf) [5,w60,w0,w3,w1,w2,w4] BT.lf)) [5,1414812756,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w17,w7,w0,w3,w1,w2] BT.lf) [5,w17,w0,w3,w1,w2,w4] BT.lf) [5,w17,w0,w3,w1,w2,w16] (BT.nd (BT.nd BT.lf [5,w17,w3,w1,w2,w16] BT.lf) [5,1431651396,w0,w3,w1,w2,w4] BT.lf)))) [5,wb,w3a,w3,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,wb,w7,w0,w3,w1,w2] BT.lf) [5,wb,w7,w3,w1,w2] BT.lf) [5,wb,w0,w5,w6,w2,w4] (BT.nd (BT.nd BT.lf [5,wb,w0,wf,w1,w2,w4] BT.lf) [5,wb,w0,w3,w19,w1,w2] BT.lf)) [5,wb,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,wb,w0,w3,w1,w2,w77] BT.lf) [5,wb,w0,w3,w1,w2,w16] BT.lf) [5,wb,w0,w3,w1,w2,w13] (BT.nd (BT.nd BT.lf [5,wb,w1f,w3,w1,w2,w4] BT.lf) [5,wb,w5,w6,w2,w4] BT.lf))) [5,wb,wf,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,wb,wc,w1,w2,we] BT.lf) [5,wb,w3,w19,w1,w2] BT.lf) [5,wb,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,wb,w3,w1,w2,w77] BT.lf) [5,wb,w3,w1,w2,w16] BT.lf)) [5,wb,w3,w1,w2,w13] (BT.nd (BT.nd (BT.nd BT.lf [5,1431655935,w0,w3,w1,w2,w4] BT.lf) [5,w3a,w7,w0,w3,w1,w2] BT.lf) [5,w3a,w0,w3,w1,w2] (BT.nd BT.lf [5,w3a,w0,w3,w1,w2,w4] BT.lf))))))) [5,w3a,w3,w1,w2,w8] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1432311135,w0,w3,w1,w2,w4] BT.lf) [5,w6f,w0,w3,w1,w2,w4] BT.lf) [5,w57,w7,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [5,w57,w0,w3,w1,w2,w4] BT.lf) [5,w57,w3,w1,w18,w4] BT.lf)) [5,1442840575,w7,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [5,1442840575,w0,w3,w1,w2,w4] BT.lf) [5,1610571775,w0,w3,w1,w2,w4] BT.lf) [5,2147516416,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,2155872256,w7,w0,w3,w1,w2] BT.lf) [5,2155872256,w0,w3,w1,w2,w4] BT.lf))) [5,w31,w7,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w31,w0,w5,w6,w2,w4] BT.lf) [5,w31,w0,w3,w1,w2,w4] BT.lf) [5,w31,w0,w3,w1,w2,w3e] (BT.nd (BT.nd BT.lf [5,w31,w0,w3,w1,w2,w13] BT.lf) [5,w31,w0,w3,w1,w39,w4] BT.lf)) [5,w31,w0,w3,w2a,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,2290124928,w0,w3,w1,w2,w4] BT.lf) [5,w25,w7,w0,w3,w1,w2] BT.lf) [5,w25,w7,w0,w3,w1,w26] (BT.nd (BT.nd BT.lf [5,w25,w7,w0,w1d,w1,w2] BT.lf) [5,w25,w0,w3,w1d,w1,w2] BT.lf)))) [5,w25,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w25,w0,w3,w1,w2,w15] BT.lf) [5,w25,w0,w3,w1,w2,we] BT.lf) [5,w25,w0,w3,w1,w26,w4] (BT.nd (BT.nd BT.lf [5,w25,w0,w1d,w1,w2] BT.lf) [5,w25,w0,w1d,w1,w2,w4] BT.lf)) [5,2290647168,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,wa,w7d,w7,w3,w1,w2] BT.lf) [5,wa,w7d,w0,w5,w2,w4] BT.lf) [5,wa,2862656160,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,wa,w7,w0,w5,w1,w2] BT.lf) [5,wa,w7,w0,w3,w1,w2] BT.lf))) [5,wa,w7,w0,w1d,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,wa,w7,w0,wd,w1,w2] BT.lf) [5,wa,w7,w3,wd,w1,w2] BT.lf) [5,wa,w7,wd,w1,w2] (BT.nd (BT.nd BT.lf [5,wa,w7,wd,w1,w2,w4] BT.lf) [5,wa,2863308960,w3,w1,w2,w4] BT.lf)) [5,wa,w0,w2e,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,wa,w0,w5,w1,w2,w4] BT.lf) [5,wa,w0,w5,w1,w2,w13] BT.lf) [5,wa,w0,w5,w2a,w2,w4] (BT.nd (BT.nd BT.lf [5,wa,w0,w5,w6,w2,w4] BT.lf) [5,wa,w0,wf,w1,w2,w4] BT.lf))))) [5,wa,w0,w29,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,wa,w0,w1e,w1,w2,w4] BT.lf) [5,wa,w0,w3,w2d,w2,w4] BT.lf) [5,wa,w0,w3,w19,w1,w2] (BT.nd (BT.nd BT.lf [5,wa,w0,w3,w3c,w11,w4] BT.lf) [5,wa,w0,w3,4037079200,w2,w4] BT.lf)) [5,wa,w0,w3,w1,w51,w2] (BT.nd (BT.nd (BT.nd BT.lf [5,wa,w0,w3,w1,w2,w4] BT.lf) [5,wa,w0,w3,w1,w2,w16] BT.lf) [5,wa,w0,w3,w1,w2,w3e] (BT.nd (BT.nd BT.lf [5,wa,w0,w3,w1,w2,w13] BT.lf) [5,wa,w0,w3,w1,w2,w33] BT.lf))) [5,wa,w0,w3,w1,w39,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,wa,w0,w3,w1,w26,w4] BT.lf) [5,wa,w0,w4d,w1,w2,w4] BT.lf) [5,wa,w0,w2d,wd,w2,w4] (BT.nd (BT.nd BT.lf [5,wa,w0,w2d,w1,w2,w4] BT.lf) [5,wa,w0,w2d,w2,w4] BT.lf)) [5,wa,w0,w1b,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,wa,w0,w28,w1,w2,w4] BT.lf) [5,wa,w0,w19,wd,w1,w2] BT.lf) [5,wa,w0,w1d,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,wa,w0,wd,w1,w2,w4] BT.lf) [5,wa,w2d,wd,w2,w4] BT.lf)))) [5,wa,w1b,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,wa,w19,wd,w1,w2] BT.lf) [5,wa,wd,w1,w2,w4] BT.lf) [5,2290657962,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,2290666700,w0,w3,w1,w2,w4] BT.lf) [5,2290679807,w0,w3,w1,w2,w4] BT.lf)) [5,2292877482,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,2295105740,w0,w3,w1,w2,w4] BT.lf) [5,2298448127,w0,w3,w1,w2,w4] BT.lf) [5,2827528328,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w86,w7,w0,w3,w1,w2] BT.lf) [5,w86,w0,w3,w1,w2,w4] BT.lf))) [5,2829617288,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w14,w7,w0,w3,w1,w2] BT.lf) [5,w14,w7,w3,w1,w6,w2] BT.lf) [5,w14,w7,w3,w1,w2] (BT.nd (BT.nd BT.lf [5,w14,w7,w3,w1,w2,w4] BT.lf) [5,w14,w0,w5,w3,w2,w4] BT.lf)) [5,w14,w0,w5,w6,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w14,w0,w5,w2,w4] BT.lf) [5,w14,w0,w3,w1,w2,w4] BT.lf) [5,w21,w0,w3,w1,w2,w4] (BT.nd BT.lf [5,w21,w3,w1,w6,w2,w4] BT.lf)))))) [5,w21,w3,w1,w2,w2f,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w21,w3,w1,w2,w4] BT.lf) [5,w7,w7,w0,w3,w1,w2] BT.lf) [5,w7,w32,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [5,w7,w0,w0,w3,w1,w2] BT.lf) [5,w7,w0,w1f,w3,w1,w2] BT.lf)) [5,w7,w0,2868838655,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [5,w7,w0,w40,w3,w1,w2] BT.lf) [5,w7,w0,w2e,w3,w1,w2] BT.lf) [5,w7,w0,w37,w3,w1,w2] (BT.nd (BT.nd BT.lf [5,w7,w0,w5,w3,w1,w2] BT.lf) [5,w7,w0,w5,w3,w6,w2] BT.lf))) [5,w7,w0,w5,w6,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w7,w0,w5,w6,w2,w4] BT.lf) [5,w7,w0,w67,w3,w1,w2] BT.lf) [5,w7,w0,wf,w3,w1,w2] (BT.nd (BT.nd BT.lf [5,w7,w0,wf,w1,w1c,w2] BT.lf) [5,w7,w0,wf,w1,w2] BT.lf)) [5,w7,w0,wf,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w7,w0,w29,w3,w1,w2] BT.lf) [5,w7,w0,wc,w3,w1,w2] BT.lf) [5,w7,w0,wc,w1d,w1,w2] (BT.nd (BT.nd BT.lf [5,w7,w0,w1a,w3,w1,w2] BT.lf) [5,w7,w0,w1e,w3,w1,w2] BT.lf)))) [5,w7,w0,w3,w3,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w7,w0,w3,w52,w1,w2] BT.lf) [5,w7,w0,w3,w4d,w1,w2] BT.lf) [5,w7,w0,w3,w44,w1,w2] (BT.nd (BT.nd BT.lf [5,w7,w0,w3,3722313727,w1,w2] BT.lf) [5,w7,w0,w3,w38,w1,w2] BT.lf)) [5,w7,w0,w3,w1b,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [5,w7,w0,w3,w85,w1,w2] BT.lf) [5,w7,w0,w3,w28,w1,w2] BT.lf) [5,w7,w0,w3,w19,w1,w2] (BT.nd (BT.nd BT.lf [5,w7,w0,w3,w45,w1,w2] BT.lf) [5,w7,w0,w3,w1d,w1,w2] BT.lf))) [5,w7,w0,w3,wd,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w7,w0,w3,w1,w59,w2] BT.lf) [5,w7,w0,w3,w1,w12,w2] BT.lf) [5,w7,w0,w3,w1,w50,w2] (BT.nd (BT.nd BT.lf [5,w7,w0,w3,w1,w6,w2] BT.lf) [5,w7,w0,w3,w1,4278123772,w2] BT.lf)) [5,w7,w0,w3,w1,w3b,w2] (BT.nd (BT.nd (BT.nd BT.lf [5,w7,w0,w3,w1,w2] BT.lf) [5,w7,w0,w3,w1,w2,w2f] BT.lf) [5,w7,w0,w3,w1,w2,w4] (BT.nd BT.lf [5,w7,w0,w3,w1,w2,w43] BT.lf))))) [5,w7,w0,w3,w1,w2,w16] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w7,w0,w3,w1,w2,w15] BT.lf) [5,w7,w0,w3,w1,w2,w8] BT.lf) [5,w7,w0,w3,w1,w2,w13] (BT.nd (BT.nd BT.lf [5,w7,w0,w3,w1,w2,we] BT.lf) [5,w7,w0,w3,w1,w2,w2b] BT.lf)) [5,w7,w0,w3,w1,w2,w3d] (BT.nd (BT.nd (BT.nd BT.lf [5,w7,w0,w3,w1,w2,w2c] BT.lf) [5,w7,w0,w3,w1,w26] BT.lf) [5,w7,w0,w3,w1,w26,w4] (BT.nd (BT.nd BT.lf [5,w7,w0,w3,w1,w5a,w27] BT.lf) [5,w7,w3,w45,w1,w2] BT.lf))) [5,w7,w3,w1,w2,w16] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w7,w3,w1,w2,w8] BT.lf) [5,2863268010,w0,w3,w1,w2,w4] BT.lf) [5,w58,w0,w5,w3,w1,w2] (BT.nd (BT.nd BT.lf [5,w58,w0,w3,w1,w2] BT.lf) [5,w58,w0,w3,w1,w2,w4] BT.lf)) [5,w58,w0,w3,w1,w2,w13] (BT.nd (BT.nd (BT.nd BT.lf [5,w32,w0,wc,w3,w1,w2] BT.lf) [5,w32,w0,w3,w1,w2,w4] BT.lf) [5,w32,w0,w3,w1,w2,w20] (BT.nd (BT.nd BT.lf [5,w32,w3,wd,w1,w2,w4] BT.lf) [5,w4f,w0,w3,w1,w2,w4] BT.lf)))) [5,w4f,w3,w1,w6,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w4f,w3,w1,w2,w4] BT.lf) [5,w4f,w3,w1,w2,w4,we] BT.lf) [5,w4f,w3,w1,w2,w4,w3d] (BT.nd (BT.nd BT.lf [5,w0,w0,w5,w6,w2,w4] BT.lf) [5,w0,w0,wf,w1,w2,w4] BT.lf)) [5,w0,w0,w3,w19,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w0,w3,w1,w2,w4] BT.lf) [5,w0,w0,w3,w1,w2,w16] BT.lf) [5,w0,w0,w3,w1,w2,w13] (BT.nd (BT.nd BT.lf [5,w0,2863311615,w3,w1,w2,w4] BT.lf) [5,w0,2863329006,w3,w1,w2,w4] BT.lf))) [5,w0,w1f,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,2863639215,w3,w1,w2,w4] BT.lf) [5,w0,2867768046,w3,w1,w2,w4] BT.lf) [5,w0,w76,w40,w3,w1,w2] (BT.nd (BT.nd BT.lf [5,w0,w76,w3,w1,w2] BT.lf) [5,w0,w76,w3,w1,w2,w4] BT.lf)) [5,w0,2868838655,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,2868882090,w3,w1,w2,w4] BT.lf) [5,w0,w40,w3,w1,w2,w4] BT.lf) [5,w0,2868903935,w3,w1,w2,w4] (BT.nd BT.lf [5,w0,2952769535,w3,w1,w2,w4] BT.lf))))))))) [5,w0,3221225472,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w2e,w5,w6,w2,w4] BT.lf) [5,w0,w2e,w3,w1,w2,w4] BT.lf) [5,w0,w2e,w3,w1,w2,w49] (BT.nd (BT.nd BT.lf [5,w0,w2e,w3,w1,w2,w13] BT.lf) [5,w0,w2e,w3,w1,w5c,w4] BT.lf)) [5,w0,w89,w82,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w89,w3,w1,w2,w4] BT.lf) [5,w0,w37,w5,w6,w2,w4] BT.lf) [5,w0,w37,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w37,w3,w1,w2,w13] BT.lf) [5,w0,3233841280,w3,w1,w2,w4] BT.lf))) [5,w0,3233857536,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w5,w5,w6,w2,w4] BT.lf) [5,w0,w5,wf,w1,w2,w4] BT.lf) [5,w0,w5,w5d,w1,w27,w4] (BT.nd (BT.nd BT.lf [5,w0,w5,w82,w1,w2,w4] BT.lf) [5,w0,w5,wc,w1,w2,we] BT.lf)) [5,w0,w5,wc,w6,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w5,w1a,w1,w2,w4] BT.lf) [5,w0,w5,3435973632,w1,w2,w4] BT.lf) [5,w0,w5,w3,w7c,w1,w4] (BT.nd (BT.nd BT.lf [5,w0,w5,w3,w68,w1,w2] BT.lf) [5,w0,w5,w3,w38,w1,w2] BT.lf)))) [5,w0,w5,w3,w28,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w5,w3,w71,w1,w4] BT.lf) [5,w0,w5,w3,w19,w1,w2] BT.lf) [5,w0,w5,w3,w1,w2,w69] (BT.nd (BT.nd BT.lf [5,w0,w5,w3,w1,w2,w4] BT.lf) [5,w0,w5,w3,w1,w2,w16] BT.lf)) [5,w0,w5,w3,w1,w2,w3e] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w5,w3,w1,w2,w49] BT.lf) [5,w0,w5,w3,w1,w2,w13] BT.lf) [5,w0,w5,w3,w1,w2,w6e] (BT.nd (BT.nd BT.lf [5,w0,w5,w3,w1,w39,w4] BT.lf) [5,w0,w5,w3,4126537205,w2,w4] BT.lf))) [5,w0,w5,w3,w2a,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w5,w3,w9b,w2,w4] BT.lf) [5,w0,w5,w3,w6b,w2,w4] BT.lf) [5,w0,w5,w3,w6,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w5,w3,w6,w2,w13] BT.lf) [5,w0,w5,w3,w2,4293980400,w4] BT.lf)) [5,w0,w5,w1b,w6,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w5,w28,w2,w4] BT.lf) [5,w0,w5,wd,w6,w2,w4] BT.lf) [5,w0,w5,w73,w6,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w5,w12,w6,w2,w4] BT.lf) [5,w0,w5,w6,w6,w2,w4] BT.lf))))) [5,w0,w5,w6,w3b,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w5,w6,w4a,w2,w4] BT.lf) [5,w0,w5,w6,w2,w2,w4] BT.lf) [5,w0,w5,w6,w2,w18,w4] (BT.nd (BT.nd BT.lf [5,w0,w5,w6,w2,w5c,w4] BT.lf) [5,w0,w5,w6,w2,w27,w4] BT.lf)) [5,w0,w5,w6,w2,w2f,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w5,w6,w2,w4] BT.lf) [5,w0,w5,w6,w2,w4,w4] BT.lf) [5,w0,w5,w6,w2,w4,w8] (BT.nd (BT.nd BT.lf [5,w0,w5,w6,w2,w4,w13] BT.lf) [5,w0,w5,w6,w2,w4,we] BT.lf))) [5,w0,w5,w6,w2,w4,w3d] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w5,w6,w2,w4,w24] BT.lf) [5,w0,w5,w6,w2,w13] BT.lf) [5,w0,3233860812,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,3233873919,w3,w1,w2] BT.lf) [5,w0,3233873919,w3,w1,w2,w4] BT.lf)) [5,w0,3234644172,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,3237986559,w3,w1,w2,w4] BT.lf) [5,w0,3301229764,w3,w1,w2,w4] BT.lf) [5,w0,w5f,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w5f,w1,w36,w2,w4] BT.lf) [5,w0,w5f,w1,w2,w4] BT.lf)))) [5,w0,w80,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,wa0,wf,w1,w2,w4] BT.lf) [5,w0,wa0,w3,w1,w51,w2] BT.lf) [5,w0,wa0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,3368585352,w3,w1,w2,w4] BT.lf) [5,w0,w67,w3,w1,w2,w4] BT.lf)) [5,w0,wf,wf,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,wf,wc,w1,w2,w4] BT.lf) [5,w0,wf,w3,w1,w75,w4] BT.lf) [5,w0,wf,w3,w1,w51,w2] (BT.nd (BT.nd BT.lf [5,w0,wf,w3,w1,w2,w4] BT.lf) [5,w0,wf,w1b,w1,w2,w4] BT.lf))) [5,w0,wf,wd,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,wf,w6a,w1,w2,w4] BT.lf) [5,w0,wf,w1,w1,w2,w4] BT.lf) [5,w0,wf,w1,w2a,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,wf,w1,w75,w1c,w4] BT.lf) [5,w0,wf,w1,w75,w4] BT.lf)) [5,w0,wf,w1,w51,w1c,w2] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,wf,w1,w51,w2] BT.lf) [5,w0,wf,w1,w51,w2,w4] BT.lf) [5,w0,wf,w1,w1c,w2,w4] (BT.nd BT.lf [5,w0,wf,w1,w6,w2,w4] BT.lf)))))) [5,w0,wf,w1,w3b,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,wf,w1,w4a,w2,w4] BT.lf) [5,w0,wf,w1,w2,w2,w4] BT.lf) [5,w0,wf,w1,w2,w18,w4] (BT.nd (BT.nd BT.lf [5,w0,wf,w1,w2,4291362760,w4] BT.lf) [5,w0,wf,w1,w2,w27,w4] BT.lf)) [5,w0,wf,w1,w2,w11,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,wf,w1,w2,4294639610,w4] BT.lf) [5,w0,wf,w1,w2,w4] BT.lf) [5,w0,wf,w1,w2,w4,w4] (BT.nd (BT.nd BT.lf [5,w0,wf,w1,w2,w4,w8] BT.lf) [5,w0,wf,w1,w2,w4,4294953160] BT.lf))) [5,w0,wf,w1,w2,w4,we] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,wf,w1,w2,w4,w20] BT.lf) [5,w0,wf,w1,w2,w4,wa1] BT.lf) [5,w0,wf,w1,w2,w4,w24] (BT.nd (BT.nd BT.lf [5,w0,wa2,w3,w1,w2,w4] BT.lf) [5,w0,3435184320,w3,w1,w2,w4] BT.lf)) [5,w0,w29,wc,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w29,w3,w1,w2,w4] BT.lf) [5,w0,w29,w3,w1,w2,w81] BT.lf) [5,w0,w29,w1,w6,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w29,w1,w2,w2f,w4] BT.lf) [5,w0,w35,w3,w1,w2,w4] BT.lf)))) [5,w0,w35,w1,w1c,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w35,w1,w2,w11,w4] BT.lf) [5,w0,w35,w1,w2,4294639610,w4] BT.lf) [5,w0,w35,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,wc,w3,w19,w1,w2] BT.lf) [5,w0,wc,w3,w1d,w1,w2] BT.lf)) [5,w0,wc,w3,w1,w51,w2] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,wc,w3,w1,w2,w4c] BT.lf) [5,w0,wc,w3,w1,w2,w4] BT.lf) [5,w0,wc,w3,w1,w2,w16] (BT.nd (BT.nd BT.lf [5,w0,wc,w3,w1,w2,w15] BT.lf) [5,w0,wc,w3,w1,w2,w13] BT.lf))) [5,w0,wc,w3,w1,w2,we] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,wc,w3,w1,w2,w33] BT.lf) [5,w0,wc,w3,w1,w26,w4] BT.lf) [5,w0,wc,w1d,w1,w2] (BT.nd (BT.nd BT.lf [5,w0,wc,w1d,w1,w2,w4] BT.lf) [5,w0,wc,wd,w1,w2,we] BT.lf)) [5,w0,wc,w1,w2,we] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,3435921612,w3,w1,w2,w4] BT.lf) [5,w0,w8c,w3,w1,w2,w4] BT.lf) [5,w0,w8c,w3,w1,w2,w16] (BT.nd BT.lf [5,w0,3435954304,w3,w1,w2,w4] BT.lf))))) [5,w0,w1a,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w1a,wd,w1,w2,w4] BT.lf) [5,w0,w7e,w3,w1,w2,w4] BT.lf) [5,w0,w7e,w3,w1,w2,w33] (BT.nd (BT.nd BT.lf [5,w0,w1e,w3,w1,w2,w4] BT.lf) [5,w0,w1e,w3,w1,w2,w13] BT.lf)) [5,w0,w1e,w3,w1,w2,we] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w1e,w1,w6,w2,w4] BT.lf) [5,w0,w1e,w1,w2,w4,we] BT.lf) [5,w0,w1e,w1,w2,w4,w3d] (BT.nd (BT.nd BT.lf [5,w0,w1e,w1,w2,we] BT.lf) [5,w0,w1e,w1,w2,we,w20] BT.lf))) [5,w0,w23,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w23,w1,w1c,w2,w4] BT.lf) [5,w0,w23,w1,w2,w4] BT.lf) [5,w0,w23,w1,w2,w4,w8] (BT.nd (BT.nd BT.lf [5,w0,w23,w1,w2,w4,w20] BT.lf) [5,w0,w23,w1,w2,w4,wa1] BT.lf)) [5,w0,w5b,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w5b,w1,w2,w11,w4] BT.lf) [5,w0,w5b,w1,w2,w4] BT.lf) [5,w0,w5b,w1,w2,w4,w20] (BT.nd (BT.nd BT.lf [5,w0,w5b,w1,w2,w4,4294967280] BT.lf) [5,w0,w3,w3,w19,w1,w2] BT.lf)))) [5,w0,w3,w3,w1,w51,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w3,w1,w2,w4] BT.lf) [5,w0,w3,w3,w1,w2,w16] BT.lf) [5,w0,w3,w3,w1,w2,w13] (BT.nd (BT.nd BT.lf [5,w0,w3,w3,w1,w2,w33] BT.lf) [5,w0,w3,3435973887,w1,w2,w4] BT.lf)) [5,w0,w3,3435978205,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,3435982574,w1,w2,w4] BT.lf) [5,w0,w3,3435986172,w1,w2,w4] BT.lf) [5,w0,w3,w52,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,3436170447,w1,w2,w4] BT.lf) [5,w0,w3,3437087965,w1,w2,w4] BT.lf))) [5,w0,w3,3438202094,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,3439119612,w1,w2,w4] BT.lf) [5,w0,w3,3439263744,w1,w2,w4] BT.lf) [5,w0,w3,3439263999,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,3439316172,w1,w2,w4] BT.lf) [5,w0,w3,w4d,w1,w2,w4] BT.lf)) [5,w0,w3,3439329279,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,3489648639,w1,w2,w4] BT.lf) [5,w0,w3,3587560917,w1,w2,w4] BT.lf) [5,w0,w3,3705461980,w1,w2,w4] (BT.nd BT.lf [5,w0,w3,w78,w1,w2,w4] BT.lf))))))) [5,w0,w3,3722270037,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w8e,w1,w2,w4] BT.lf) [5,w0,w3,w44,w1,w2,w4] BT.lf) [5,w0,w3,w44,w1,w2,w16] (BT.nd (BT.nd BT.lf [5,w0,w3,3722313727,w1,w2,w4] BT.lf) [5,w0,w3,3724533247,w1,w2,w4] BT.lf)) [5,w0,w3,w22,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,3938511552,w1,w2,w4] BT.lf) [5,w0,w3,w68,w1b,w1,w2] BT.lf) [5,w0,w3,w68,w1,w2] (BT.nd (BT.nd BT.lf [5,w0,w3,w68,w1,w2,w4] BT.lf) [5,w0,w3,w5e,w1,w2,w4] BT.lf))) [5,w0,w3,w38,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w38,w1,w2,w4] BT.lf) [5,w0,w3,w1b,w1,w2,w4] BT.lf) [5,w0,w3,w1b,w1,w2,w13] (BT.nd (BT.nd BT.lf [5,w0,w3,3972852940,w1,w2,w4] BT.lf) [5,w0,w3,3974889472,w1,w2,w4] BT.lf)) [5,w0,w3,3974930592,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w85,w1,w2,w4] BT.lf) [5,w0,w3,w28,w1,w2,w4] BT.lf) [5,w0,w3,4007718624,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,4008373994,w1,w2,w4] BT.lf) [5,w0,w3,4008505068,w1,w2,w4] BT.lf)))) [5,w0,w3,w19,w19,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w19,w45,w1,w2] BT.lf) [5,w0,w3,w19,w1d,w1,w2] BT.lf) [5,w0,w3,w19,wd,w1,w2] (BT.nd (BT.nd BT.lf [5,w0,w3,w19,w1,w1c,w2] BT.lf) [5,w0,w3,w19,w1,w6,w2] BT.lf)) [5,w0,w3,w19,w1,4278120688,w2] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w19,w1,w3b,w2] BT.lf) [5,w0,w3,w19,w1,w2] BT.lf) [5,w0,w3,w19,w1,w2,w11] (BT.nd (BT.nd BT.lf [5,w0,w3,w19,w1,w2,w4] BT.lf) [5,w0,w3,w19,w1,w2,w8] BT.lf))) [5,w0,w3,w19,w1,w2,we] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w19,w1,w2,w2b] BT.lf) [5,w0,w3,w19,w1,w2,w20] BT.lf) [5,w0,w3,w45,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,w1d,w1,w72,w2] BT.lf) [5,w0,w3,w1d,w1,w2,w4] BT.lf)) [5,w0,w3,w1d,w1,w2,w20] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,4008632544,w1,w2,w4] BT.lf) [5,w0,w3,4008635114,w1,w2,w4] BT.lf) [5,w0,w3,4008635628,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,wd,w1,w48,w2] BT.lf) [5,w0,w3,wd,w1,w2,w4] BT.lf))))) [5,w0,w3,wd,w1,w2,4294906129] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,wd,w1,w2,w16] BT.lf) [5,w0,w3,wd,w1,w2,w13] BT.lf) [5,w0,w3,wd,w1,w2,w33] (BT.nd (BT.nd BT.lf [5,w0,w3,wd,w1,4279369489,w4] BT.lf) [5,w0,w3,4008640511,w1,w2,w4] BT.lf)) [5,w0,w3,4009750271,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w8f,w2,w4] BT.lf) [5,w0,w3,w1,wa3,w2,w4] BT.lf) [5,w0,w3,w1,4241289216,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w59,w2,w4] BT.lf) [5,w0,w3,w1,w59,w2,w33] BT.lf))) [5,w0,w3,w1,w8a,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w12,w2,w4] BT.lf) [5,w0,w3,w1,w12,w2,we] BT.lf) [5,w0,w3,w1,w12,w2,w3d] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w47,w2,w4] BT.lf) [5,w0,w3,w1,w50,w2,w4] BT.lf)) [5,w0,w3,w1,w50,w2,w20] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w6d,w2,w4] BT.lf) [5,w0,w3,w1,4244438016,w2,w4] BT.lf) [5,w0,w3,w1,4244438220,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w6,w48,w2] BT.lf) [5,w0,w3,w1,w6,w2,w46] BT.lf)))) [5,w0,w3,w1,w6,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w6,w2,w16] BT.lf) [5,w0,w3,w1,w6,w2,w13] BT.lf) [5,w0,w3,w1,w6,w2,w6e] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w6,w2,4294966272] BT.lf) [5,w0,w3,w1,4244439039,w2,w4] BT.lf)) [5,w0,w3,w1,4244634879,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,4261281277,w2,w4] BT.lf) [5,w0,w3,w1,4277075694,w2,w4] BT.lf) [5,w0,w3,w1,wa4,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w48,w3b,w2] BT.lf) [5,w0,w3,w1,w48,w2] BT.lf))) [5,w0,w3,w1,w48,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w61,w2,w4] BT.lf) [5,w0,w3,w1,4278111436,w2,w4] BT.lf) [5,w0,w3,w1,4278120174,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,4278123772,w2,w4] BT.lf) [5,w0,w3,w1,w3b,w2,w4] BT.lf)) [5,w0,w3,w1,w2,w46] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w46,w2f] BT.lf) [5,w0,w3,w1,w2,w46,w4] BT.lf) [5,w0,w3,w1,w2,wa5,w4] (BT.nd BT.lf [5,w0,w3,w1,w2,4294769916,w4] BT.lf)))))) [5,w0,w3,w1,w2,w2f,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,4294901758,w4] BT.lf) [5,w0,w3,w1,w2,w4] BT.lf) [5,w0,w3,w1,w2,w4,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,w90] BT.lf) [5,w0,w3,w1,w2,w4,w8d] BT.lf)) [5,w0,w3,w1,w2,w4,w79] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,4294901964] BT.lf) [5,w0,w3,w1,w2,w4,w43] BT.lf) [5,w0,w3,w1,w2,w4,4294905855] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,w77] BT.lf) [5,w0,w3,w1,w2,w4,w16] BT.lf))) [5,w0,w3,w1,w2,w4,4294923775] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,w3e] BT.lf) [5,w0,w3,w1,w2,w4,w15] BT.lf) [5,w0,w3,w1,w2,w4,w70] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,w8] BT.lf) [5,w0,w3,w1,w2,w4,4294945535] BT.lf)) [5,w0,w3,w1,w2,w4,w49] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,w13] BT.lf) [5,w0,w3,w1,w2,w4,4294953160] BT.lf) [5,w0,w3,w1,w2,w4,w81] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,we] BT.lf) [5,w0,w3,w1,w2,w4,4294954239] BT.lf)))) [5,w0,w3,w1,w2,w4,w9c] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,w91] BT.lf) [5,w0,w3,w1,w2,w4,4294962412] BT.lf) [5,w0,w3,w1,w2,w4,w2b] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,4294966476] BT.lf) [5,w0,w3,w1,w2,w4,w3d] BT.lf)) [5,w0,w3,w1,w2,w4,4294967038] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,4294967292] BT.lf) [5,w0,w3,w1,w2,w4,w2c] BT.lf) [5,w0,w3,w1,w2,w8d] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w43,w24] BT.lf) [5,w0,w3,w1,w2,w77] BT.lf))) [5,w0,w3,w1,w2,w16] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w16,w16] BT.lf) [5,w0,w3,w1,w2,w16,w8] BT.lf) [5,w0,w3,w1,w2,w16,we] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w16,w9c] BT.lf) [5,w0,w3,w1,w2,w16,w2c] BT.lf)) [5,w0,w3,w1,w2,w3e] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w15,w20] BT.lf) [5,w0,w3,w1,w2,w8,w13] BT.lf) [5,w0,w3,w1,w2,w49] (BT.nd BT.lf [5,w0,w3,w1,w2,w13] BT.lf))))) [5,w0,w3,w1,w2,w13,w13] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w13,we] BT.lf) [5,w0,w3,w1,w2,w13,w91] BT.lf) [5,w0,w3,w1,w2,w13,w24] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w13,4294967232] BT.lf) [5,w0,w3,w1,w2,w81] BT.lf)) [5,w0,w3,w1,w2,we,w20] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,we,4294967280] BT.lf) [5,w0,w3,w1,4278255615,w4,w24] BT.lf) [5,w0,w3,w1,w87,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,4279238415,w11,w4] BT.lf) [5,w0,w3,w1,4283826005,w18,w4] BT.lf))) [5,w0,w3,w1,w39,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w26,w4] BT.lf) [5,w0,w3,w1,w10,w11,w4] BT.lf) [5,w0,w3,w1,w10,w4,w24] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w5a,w27,w4] BT.lf) [5,w0,w3,w1,w18,w5c,w4] BT.lf)) [5,w0,w3,w1,w18,w83,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w1f,w3,w1,w2,w4,w8] BT.lf) [5,w40,w3,w1,w2,w18,w4] BT.lf) [5,w2e,w3,w22,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w5,w3,w22,w1,w2,w4] BT.lf) [5,w3,w22,w1,w2,w4] BT.lf)))) [5,w3,w1b,w1,w2,w18,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,0,65535,w0,w3,w1,w2] BT.lf) [6,0,65535,w0,w3,w1,w2,w4] BT.lf) [6,0,w9,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,0,w9,w0,w3,w1,w4] BT.lf) [6,0,wb,w0,w3,w1,w2,w4] BT.lf)) [6,0,wb,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,0,w0,w3,w1,w2,w4] BT.lf) [6,255,w0,w3,w1,w2,w4] BT.lf) [6,255,w0,w3,w1,w2,w4,w24] (BT.nd (BT.nd BT.lf [6,21845,w0,w3,w1,w2,w4] BT.lf) [6,21845,w0,w3,w1,w2,w4,w8] BT.lf))) [6,43690,65535,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,43690,65535,w0,w3,w1,w2,w4] BT.lf) [6,43690,w0,w3,w1,w2] BT.lf) [6,43690,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,52428,65535,w0,w3,w1,w2] BT.lf) [6,52428,65535,w0,w3,w1,w2,w4] BT.lf)) [6,52428,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,65535,w0,w3,w1,w2] BT.lf) [6,65535,65535,w0,w3,w1,w2,w4] BT.lf) [6,65535,w9,w0,w3,w1] (BT.nd BT.lf [6,65535,w9,w0,w3,w1,w2] BT.lf)))))))) [6,65535,w9,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,w9,w0,w3,w1,w4] BT.lf) [6,65535,wb,w0,w3,w1,w2] BT.lf) [6,65535,wb,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,65535,wb,w3,w1,w2] BT.lf) [6,65535,wb,w3,w1,w2,w4] BT.lf)) [6,65535,wa,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,wa,w0,w3,w1,w2,w4] BT.lf) [6,65535,w7,w0,w3,w1,w2] BT.lf) [6,65535,w7,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,65535,w0,w0,w3,w1,w2] BT.lf) [6,65535,w0,w0,w3,w1,w2,w4] BT.lf))) [6,65535,w0,w1f,w3,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,w0,w1f,w3,w1,w2,w4] BT.lf) [6,65535,w0,w5,w3,w1,w2] BT.lf) [6,65535,w0,w5,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,65535,w0,wc,w3,w1,w2] BT.lf) [6,65535,w0,wc,w3,w1,w2,w4] BT.lf)) [6,65535,w0,w3,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,w0,w3,w3,w1,w2,w4] BT.lf) [6,65535,w0,w3,w52,w1,w2] BT.lf) [6,65535,w0,w3,w52,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,65535,w0,w3,wd,w1,w2] BT.lf) [6,65535,w0,w3,wd,w1,w2,w4] BT.lf)))) [6,65535,w0,w3,w1,w6,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,w0,w3,w1,w6,w2,w4] BT.lf) [6,65535,w0,w3,w1,w2] BT.lf) [6,65535,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,65535,w0,w3,w1,w2,w4,w4] BT.lf) [6,65535,w0,w3,w1,w2,w4,w8] BT.lf)) [6,65535,w0,w3,w1,w2,w4,we] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,w0,w3,w1,w2,w4,w2c] BT.lf) [6,65535,w0,w3,w1,w2,w8] BT.lf) [6,65535,w0,w3,w1,w2,we] (BT.nd (BT.nd BT.lf [6,65535,w0,w3,w1,w2,w2c] BT.lf) [6,w53,w0,w3,w1,w2,w11,w4] BT.lf))) [6,w53,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w54,w0,w3,w1,w2,w18,w4] BT.lf) [6,w54,w0,w3,w1,w2,w4] BT.lf) [6,w3f,w9,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w3f,w9,w0,w3,w1,w4] BT.lf) [6,w3f,w0,w3,w1,w2,w4] BT.lf)) [6,w41,w9,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w41,w9,w0,w3,w1,w4] BT.lf) [6,w41,w0,w3,w1,w2,w4] BT.lf) [6,w42,w9,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w42,w9,w0,w3,w1,w4] BT.lf) [6,w42,w0,w3,w1,w2,w4] BT.lf))))) [6,w9,w9,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w9,w9,w0,w3,w1,w4] BT.lf) [6,w9,w4b,w0,w3,w1,w2,w4] BT.lf) [6,w9,w4b,w0,w3,w1,w4] (BT.nd (BT.nd BT.lf [6,w9,w4b,w0,w3,w4] BT.lf) [6,w9,wb,w0,w3,w1,w2,w4] BT.lf)) [6,w9,wb,w0,w3,w1,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w9,wb,w3,w1,w2,w4] BT.lf) [6,w9,wb,w3,w1,w4] BT.lf) [6,w9,wa,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w9,wa,w0,w3,w1,w4] BT.lf) [6,w9,w55,w0,w3,w1,w2,w4] BT.lf))) [6,w9,w55,w0,w3,w1,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w9,w7,w0,w3,w1] BT.lf) [6,w9,w7,w0,w3,w1,w2] BT.lf) [6,w9,w7,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w9,w7,w0,w3,w1,w4] BT.lf) [6,w9,w0,w0,w3,w1,w2,w4] BT.lf)) [6,w9,w0,w0,w3,w1,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w9,w0,w40,w3,w1,w2,w4] BT.lf) [6,w9,w0,w40,w3,w1,w4] BT.lf) [6,w9,w0,w5,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w9,w0,w5,w3,w1,w4] BT.lf) [6,w9,w0,w5d,w3,w1,w2,w4] BT.lf)))) [6,w9,w0,w5d,w3,w1,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w9,w0,wc,w3,w1,w2,w4] BT.lf) [6,w9,w0,wc,w3,w1,w4] BT.lf) [6,w9,w0,w3,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w9,w0,w3,w3,w1,w4] BT.lf) [6,w9,w0,w3,w4d,w1,w2,w4] BT.lf)) [6,w9,w0,w3,w4d,w1,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w9,w0,w3,wd,w1,w2,w4] BT.lf) [6,w9,w0,w3,wd,w1,w4] BT.lf) [6,w9,w0,w3,w1,w6,w2,w4] (BT.nd (BT.nd BT.lf [6,w9,w0,w3,w1,w6,w4] BT.lf) [6,w9,w0,w3,w1,w4a,w2,w4] BT.lf))) [6,w9,w0,w3,w1,w4a,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w9,w0,w3,w1,w2,w2,w4] BT.lf) [6,w9,w0,w3,w1,w2,w18,w4] BT.lf) [6,w9,w0,w3,w1,w2,w27,w4] (BT.nd (BT.nd BT.lf [6,w9,w0,w3,w1,w2,w4] BT.lf) [6,w9,w0,w3,w1,w2,w4,w4] BT.lf)) [6,w9,w0,w3,w1,w2,w4,w43] (BT.nd (BT.nd (BT.nd BT.lf [6,w9,w0,w3,w1,w2,w4,w8] BT.lf) [6,w9,w0,w3,w1,w2,w4,we] BT.lf) [6,w9,w0,w3,w1,w2,w4,w24] (BT.nd BT.lf [6,w9,w0,w3,w1,w2,w4,w2c] BT.lf)))))) [6,w9,w0,w3,w1,w18,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w9,w0,w3,w1,w27,w4] BT.lf) [6,w9,w0,w3,w1,w4] BT.lf) [6,w9,w0,w3,w1,w4,w4] (BT.nd (BT.nd BT.lf [6,w9,w0,w3,w1,w4,w43] BT.lf) [6,w9,w0,w3,w1,w4,w8] BT.lf)) [6,w9,w0,w3,w1,w4,we] (BT.nd (BT.nd (BT.nd BT.lf [6,w9,w0,w3,w1,w4,w24] BT.lf) [6,w9,w0,w3,w1,w4,w2c] BT.lf) [6,w66,w0,w3,w1,w4a,w2,w4] (BT.nd (BT.nd BT.lf [6,w66,w0,w3,w1,w2,w4] BT.lf) [6,w56,w0,w3,w3c,w1,w2,w4] BT.lf))) [6,w56,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w30,wb,w0,w3,w1,w2,w4] BT.lf) [6,w30,wb,w3,w1,w2,w4] BT.lf) [6,w30,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w17,wb,w0,w3,w1,w2,w4] BT.lf) [6,w17,wb,w3,w1,w2,w4] BT.lf)) [6,w17,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,wb,wb,w0,w3,w1,w2,w4] BT.lf) [6,wb,wb,w3,w1,w2,w4] BT.lf) [6,wb,wa,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,wb,wa,w3,w1,w2,w4] BT.lf) [6,wb,w7,w0,w3,w1,w2] BT.lf)))) [6,wb,w7,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,wb,w7,w3,w1,w2] BT.lf) [6,wb,w7,w3,w1,w2,w4] BT.lf) [6,wb,w0,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,wb,w0,w5,w3,w1,w2,w4] BT.lf) [6,wb,w0,wc,w3,w1,w2,w4] BT.lf)) [6,wb,w0,w3,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,wb,w0,w3,w44,w1,w2,w4] BT.lf) [6,wb,w0,w3,wd,w1,w2,w4] BT.lf) [6,wb,w0,w3,w1,w6,w2,w4] (BT.nd (BT.nd BT.lf [6,wb,w0,w3,w1,w2,w4] BT.lf) [6,wb,w0,w3,w1,w2,w4,w4] BT.lf))) [6,wb,w0,w3,w1,w2,w4,w16] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,wb,w0,w3,w1,w2,w4,w8] BT.lf) [6,wb,w0,w3,w1,w2,w4,we] BT.lf) [6,wb,w0,w3,w1,w2,w4,w2c] (BT.nd (BT.nd BT.lf [6,wb,w0,w3,w1,w2,w16] BT.lf) [6,wb,w5,w3,w1,w2,w4] BT.lf)) [6,wb,wc,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,wb,w3,w3,w1,w2,w4] BT.lf) [6,wb,w3,w44,w1,w2,w4] BT.lf) [6,wb,w3,wd,w1,w2,w4] (BT.nd BT.lf [6,wb,w3,w1,w6,w2,w4] BT.lf))))) [6,wb,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,wb,w3,w1,w2,w4,w4] BT.lf) [6,wb,w3,w1,w2,w4,w16] BT.lf) [6,wb,w3,w1,w2,w4,w8] (BT.nd (BT.nd BT.lf [6,wb,w3,w1,w2,w4,we] BT.lf) [6,wb,w3,w1,w2,w4,w2c] BT.lf)) [6,wb,w3,w1,w2,w16] (BT.nd (BT.nd (BT.nd BT.lf [6,w3a,w7,w0,w3,w1,w2] BT.lf) [6,w3a,w7,w0,w3,w1,w2,w4] BT.lf) [6,w3a,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [6,w3a,w0,w3,w1,w2,w4] BT.lf) [6,w57,w55,w0,w3,w1,w2,w4] BT.lf))) [6,w57,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w31,wa,w0,w3,w1,w2,w4] BT.lf) [6,w31,w0,w5,w3,w1,w2,w4] BT.lf) [6,w31,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w25,wa,w0,w3,w1,w2,w4] BT.lf) [6,w25,w7,w0,w3,w1,w2] BT.lf)) [6,w25,w7,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w25,w0,wc,w3,w1,w2,w4] BT.lf) [6,w25,w0,w3,w1,w2,w4] BT.lf) [6,wa,wa,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,wa,w7d,w0,w3,w1,w2,w4] BT.lf) [6,wa,w7,w0,w3,w1,w2] BT.lf)))) [6,wa,w7,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,wa,w0,w0,w3,w1,w2,w4] BT.lf) [6,wa,w0,w5,w3,w1,w2,w4] BT.lf) [6,wa,w0,w5,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,wa,w0,wc,w3,w1,w2,w4] BT.lf) [6,wa,w0,w3,w3,w1,w2,w4] BT.lf)) [6,wa,w0,w3,wd,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,wa,w0,w3,w3c,w1,w2,w4] BT.lf) [6,wa,w0,w3,w6a,w1,w2,w4] BT.lf) [6,wa,w0,w3,w1,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,wa,w0,w3,w1,w2a,w2,w4] BT.lf) [6,wa,w0,w3,w1,w1c,w2,w4] BT.lf))) [6,wa,w0,w3,w1,w6,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,wa,w0,w3,w1,w2,w11,w4] BT.lf) [6,wa,w0,w3,w1,w2,w4] BT.lf) [6,wa,w0,w3,w1,w2,w4,w4] (BT.nd (BT.nd BT.lf [6,wa,w0,w3,w1,w2,w4,w15] BT.lf) [6,wa,w0,w3,w1,w2,w4,w8] BT.lf)) [6,wa,w0,w3,w1,w2,w4,we] (BT.nd (BT.nd (BT.nd BT.lf [6,wa,w0,w3,w1,w2,w4,w20] BT.lf) [6,wa,w0,wd,w1,w2,w4] BT.lf) [6,wa,w3,wd,w1,w2,w4] (BT.nd BT.lf [6,wa,wd,w1,w2,w4] BT.lf))))))) [6,w14,w0,w3,w1,w6,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w14,w0,w3,w1,w2,w4] BT.lf) [6,w7,w7,w0,w3,w1,w2] BT.lf) [6,w7,w7,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w7,w0,w0,w3,w1,w2] BT.lf) [6,w7,w0,w0,w3,w1,w2,w4] BT.lf)) [6,w7,w0,w5,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [6,w7,w0,w5,w3,w1,w2,w4] BT.lf) [6,w7,w0,wc,w3,w1,w2] BT.lf) [6,w7,w0,wc,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w7,w0,w3,w3,w1,w2] BT.lf) [6,w7,w0,w3,w3,w1,w2,w4] BT.lf))) [6,w7,w0,w3,w1d,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w7,w0,w3,w1d,w1,w2,w4] BT.lf) [6,w7,w0,w3,wd,w1,w2] BT.lf) [6,w7,w0,w3,wd,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w7,w0,w3,w1,w6,w2] BT.lf) [6,w7,w0,w3,w1,w6,w2,w4] BT.lf)) [6,w7,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [6,w7,w0,w3,w1,w2,w4] BT.lf) [6,w7,w0,w3,w1,w2,w4,w4] BT.lf) [6,w7,w0,w3,w1,w2,w4,w8] (BT.nd (BT.nd BT.lf [6,w7,w0,w3,w1,w2,w4,we] BT.lf) [6,w7,w0,w3,w1,w2,w8] BT.lf)))) [6,w7,w0,w3,w1,w2,we] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w7,w3,w1,w2,w4,w8] BT.lf) [6,w7,w3,w1,w2,w8] BT.lf) [6,w32,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w32,w0,w3,w1,w2,w4,we] BT.lf) [6,w0,w0,w0,w3,w1,w2,w4] BT.lf)) [6,w0,w0,w5,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w0,wc,w3,w1,w2,w4] BT.lf) [6,w0,w0,w3,w3,w1,w2,w4] BT.lf) [6,w0,w0,w3,wd,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,w0,w3,w1,w6,w2,w4] BT.lf) [6,w0,w0,w3,w1,w2,w4] BT.lf))) [6,w0,w0,w3,w1,w2,w4,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w0,w3,w1,w2,w4,w8] BT.lf) [6,w0,w0,w3,w1,w2,w4,we] BT.lf) [6,w0,w1f,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,w40,w3,w1,w2,w4] BT.lf) [6,w0,w2e,w5,w3,w1,w2,w4] BT.lf)) [6,w0,w2e,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w37,w5,w3,w1,w2,w4] BT.lf) [6,w0,w37,wc,w3,w1,w2,w4] BT.lf) [6,w0,w37,w3,w1,w2,w4] (BT.nd BT.lf [6,w0,w5,w5,w3,w1,w2,w4] BT.lf))))) [6,w0,w5,w5d,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w5,wc,w3,w1,w2,w4] BT.lf) [6,w0,w5,w3,w3,w1,w2,w4] BT.lf) [6,w0,w5,w3,w1b,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,w5,w3,wd,w1,w2,w4] BT.lf) [6,w0,w5,w3,w1,w6,w2,w4] BT.lf)) [6,w0,w5,w3,w1,w4a,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w5,w3,w1,w2,w2,w4] BT.lf) [6,w0,w5,w3,w1,w2,w18,w4] BT.lf) [6,w0,w5,w3,w1,w2,w5c,w4] (BT.nd (BT.nd BT.lf [6,w0,w5,w3,w1,w2,w27,w4] BT.lf) [6,w0,w5,w3,w1,w2,w4] BT.lf))) [6,w0,w5,w3,w1,w2,w4,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w5,w3,w1,w2,w4,w8] BT.lf) [6,w0,w5,w3,w1,w2,w4,w13] BT.lf) [6,w0,w5,w3,w1,w2,w4,we] (BT.nd (BT.nd BT.lf [6,w0,w5,w3,w1,w2,w4,w24] BT.lf) [6,w0,w5,w3,w1,w2,w13] BT.lf)) [6,w0,w5,w3,w6,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w5,w6,w2,w4] BT.lf) [6,w0,wf,w3,w1,w1c,w2,w4] BT.lf) [6,w0,wf,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,wf,w1,w1c,w2,w4] BT.lf) [6,w0,wf,w1,w2,w4] BT.lf)))) [6,w0,w29,w3,w1,w2,w11,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w29,w3,w1,w2,w4] BT.lf) [6,w0,wc,wc,w3,w1,w2,w4] BT.lf) [6,w0,wc,w3,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,wc,w3,w45,w1,w2,w4] BT.lf) [6,w0,wc,w3,wd,w1,w2,w4] BT.lf)) [6,w0,wc,w3,w6a,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,wc,w3,w1,w1,w2,w4] BT.lf) [6,w0,wc,w3,w1,w1c,w2,w4] BT.lf) [6,w0,wc,w3,w1,w6b,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,wc,w3,w1,w6,w2,w4] BT.lf) [6,w0,wc,w3,w1,w2,w11,w4] BT.lf))) [6,w0,wc,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,wc,w3,w1,w2,w4,w4] BT.lf) [6,w0,wc,w3,w1,w2,w4,w8] BT.lf) [6,w0,wc,w3,w1,w2,w4,we] (BT.nd (BT.nd BT.lf [6,w0,wc,w3,w1,w2,w4,w20] BT.lf) [6,w0,wc,w3,w1,w2,we] BT.lf)) [6,w0,wc,w1,w2,w4,we] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,wc,w1,w2,we] BT.lf) [6,w0,w1a,w3,w1,w2,w4] BT.lf) [6,w0,w1a,w3,w1,w2,w4,w8] (BT.nd BT.lf [6,w0,w1e,w3,w1,w2,w4] BT.lf)))))) [6,w0,w1e,w3,w1,w2,w4,w20] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w3,w3,w1,w2,w4] BT.lf) [6,w0,w3,w3,wd,w1,w2,w4] BT.lf) [6,w0,w3,w3,w1,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,w3,w3,w1,w1c,w2,w4] BT.lf) [6,w0,w3,w3,w1,w6,w2,w4] BT.lf)) [6,w0,w3,w3,w1,w2,w11,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w3,w1,w2,w4] BT.lf) [6,w0,w3,w3,w1,w2,w4,w4] BT.lf) [6,w0,w3,w3,w1,w2,w4,w8] (BT.nd (BT.nd BT.lf [6,w0,w3,w3,w1,w2,w4,we] BT.lf) [6,w0,w3,w3,w1,w2,w4,w20] BT.lf))) [6,w0,w3,w52,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w4d,w1,w2,w4] BT.lf) [6,w0,w3,w44,w1,w2,w4] BT.lf) [6,w0,w3,w1b,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,w3,w28,w1,w2,w4] BT.lf) [6,w0,w3,w19,wd,w1,w2] BT.lf)) [6,w0,w3,w19,wd,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w19,w1,w2] BT.lf) [6,w0,w3,w19,w1,w2,w4] BT.lf) [6,w0,w3,w45,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,w3,w1d,w1,w2,w4] BT.lf) [6,w0,w3,wd,wd,w1,w2,w4] BT.lf)))) [6,w0,w3,wd,w1,w1c,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,wd,w1,w6,w2,w4] BT.lf) [6,w0,w3,wd,w1,w3b,w2,w4] BT.lf) [6,w0,w3,wd,w1,w2,w11,w4] (BT.nd (BT.nd BT.lf [6,w0,w3,wd,w1,w2,w4] BT.lf) [6,w0,w3,wd,w1,w2,w4,w4] BT.lf)) [6,w0,w3,wd,w1,w2,w4,w8] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,wd,w1,w2,w4,we] BT.lf) [6,w0,w3,wd,w1,w2,w4,w2b] BT.lf) [6,w0,w3,wd,w1,w2,w4,w20] (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w59,w2,w4] BT.lf) [6,w0,w3,w1,w12,w6,w2,w4] BT.lf))) [6,w0,w3,w1,w12,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w50,w2,w4] BT.lf) [6,w0,w3,w1,w6,w6,w2,w4] BT.lf) [6,w0,w3,w1,w6,w3b,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w6,w2,w27,w4] BT.lf) [6,w0,w3,w1,w6,w2,w2f,w4] BT.lf)) [6,w0,w3,w1,w6,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w6,w2,w4,w4] BT.lf) [6,w0,w3,w1,w6,w2,w4,w8] BT.lf) [6,w0,w3,w1,w6,w2,w4,we] (BT.nd BT.lf [6,w0,w3,w1,w6,w2,w4,w3d] BT.lf))))) [6,w0,w3,w1,w6,w2,w4,w24] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w3b,w2,w4] BT.lf) [6,w0,w3,w1,w2,w2f,w4] BT.lf) [6,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w2,w4,w4] BT.lf) [6,w0,w3,w1,w2,w4,w4,w4] BT.lf)) [6,w0,w3,w1,w2,w4,w4,w8] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w2,w4,w4,we] BT.lf) [6,w0,w3,w1,w2,w4,w43] BT.lf) [6,w0,w3,w1,w2,w4,w16] (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w2,w4,w15] BT.lf) [6,w0,w3,w1,w2,w4,w8] BT.lf))) [6,w0,w3,w1,w2,w4,w8,w8] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w2,w4,w8,we] BT.lf) [6,w0,w3,w1,w2,w4,w8,w2b] BT.lf) [6,w0,w3,w1,w2,w4,w13] (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w2,w4,we] BT.lf) [6,w0,w3,w1,w2,w4,we,we] BT.lf)) [6,w0,w3,w1,w2,w4,we,w2b] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w2,w4,we,w20] BT.lf) [6,w0,w3,w1,w2,w4,we,w3d] BT.lf) [6,w0,w3,w1,w2,w4,w2b] (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w2,w4,w3d] BT.lf) [6,w0,w3,w1,w2,w4,w2c] BT.lf)))) [6,w0,w3,w1,w2,w16] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w2,w13] BT.lf) [6,w0,w3,w1,w2,we,w20] BT.lf) [7,65535,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [7,65535,w0,w3,w1,w2,w4] BT.lf) [7,w9,w0,w3,w1,w2,w4] BT.lf)) [7,w9,w0,w3,w1,w4] (BT.nd (BT.nd (BT.nd BT.lf [7,wb,w0,w3,w1,w2,w4] BT.lf) [7,wb,w3,w1,w2,w4] BT.lf) [7,wa,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [7,w7,w0,w3,w1,w2] BT.lf) [7,w7,w0,w3,w1,w2,w4] BT.lf))) [7,w0,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,w0,w5,w3,w1,w2,w4] BT.lf) [7,w0,wc,w3,w1,w2,w4] BT.lf) [7,w0,w3,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [7,w0,w3,wd,w1,w2,w4] BT.lf) [7,w0,w3,w1,w6,w2,w4] BT.lf)) [7,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [7,w0,w3,w1,w2,w4,w4] BT.lf) [7,w0,w3,w1,w2,w4,w8] BT.lf) [7,w0,w3,w1,w2,w4,we] (BT.nd BT.lf [8,w0,w3,w1,w2,w4] BT.lf))))))))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([2,w14,w7c,w13],[]),([2,w14,w38,w2],[]),([2,w58,3907578088,w2],[]),([2,w58,w7c,w6],[]),([3,wa,w7d,w38,w2],[]),([3,wa,w7,3768639648,w2],[]),([3,wa,w7,w2d,w71],[]),([3,wa,w7,w2d,w2],[]),([3,w14,w7,w5,w2],[]),([3,w14,w7,w67,w2],[]),([3,w14,w7,w38,w2],[]),([3,w14,w58,w5,w2],[]),([3,w14,w0,w38,w2],[]),([3,w14,w5,w7c,w4],[]),([3,w14,w5,w68,w2],[]),([3,w14,w5,w38,w2],[]),([3,w14,w3,w38,w2],[]),([3,w14,w38,w6,w2],[]),([3,w14,w38,w2],[]),([3,w14,w38,w2,w4],[]),([3,w14,w1b,w2,w13],[]),([3,w14,w1d,w72,w2],[]),([3,2863179944,w5,w2,w4],[]),([3,w21,w5,w73,w4],[]),([3,w58,w3,w7c,w1],[]),([3,w58,w1b,w6,w2],[]),([3,w32,wc,w2d,w2],[]),([3,2863310984,w7e,w1,w2],[]),([3,w4f,w5,w12,w2],[]),([3,w0,w5,w73,w46],[]),([3,w0,w5,w12,w93],[]),([3,w0,w5f,w11,w33],[(76,2),(100,2)]),([3,w0,w3,w94,w33],[(100,2)]),([3,w0,w3,w7f,w34],[(100,2)]),([3,w0,w3,w7f,w11],[(100,2)]),([3,w0,w3,w95,w5a],[]),([3,w0,w3,4210618608,w5a],[]),([3,w0,w85,w72,4288741120],[]),([3,w3,w22,w11,w33],[]),([3,w22,w59,w11,w4],[]),([4,43690,w7,w3,w1,w2],[]),([4,11184810,w7,w3,w1,w2],[]),([4,16776960,w0,w3,w1],[]),([4,67043328,w0,w3,w1,w2],[]),([4,178913280,w0,w3,w1,w2],[]),([4,w96,w0,w3,w3c,w4],[]),([4,w96,w0,w3,w4],[]),([4,w74,w0,w3,w3c,w11],[]),([4,w74,w0,w3,w1,w2],[]),([4,715795114,w3,w1,w2,w4],[]),([4,1073676288,w0,w3,w1,w2],[]),([4,1154272460,w7,w0,w1,w2],[]),([4,1154272460,w0,w1,w2,w4],[]),([4,1288457420,w0,w1,w2,w4],[]),([4,1431677610,w3,w1,w2],[]),([4,1437226410,w3,w1,w4],[]),([4,1610547200,w0,w3,w1,w2],[]),([4,w25,w0,w1d,w1,w2],[(96,4),(128,2)]),([4,w25,w0,w1d,w1,w26],[(56,2),(72,2),(96,1),(128,2)]),([4,wa,w7d,w7,w5,w2],[(96,1)]),([4,wa,2862656160,w3,w3c,w4],[]),([4,wa,w7,w0,w2d,w2],[]),([4,wa,w7,w3,w2d,w2],[]),([4,wa,w7,w2d,wd,w2],[]),([4,wa,w7,w2d,w1,w2],[]),([4,wa,w7,w2d,w2],[]),([4,wa,w7,w2d,w2,w4],[]),([4,wa,w7,w1b,w1,w2],[(148,0)]),([4,wa,w7,w28,w1,w2],[]),([4,wa,w7,wd,w1,w2],[(148,0)]),([4,wa,2863308800,w3,w1,w2],[]),([4,wa,w0,3768639648,w2,w4],[]),([4,wa,w0,w2d,w71,w4],[]),([4,wa,w0,w2d,w19,w2],[]),([4,wa,w0,w2d,w2,w4],[]),([4,wa,w0,w38,w1,w2],[(96,4)]),([4,wa,w2d,w71,w4],[]),([4,wa,w2d,w19,w2],[]),([4,wa,w22,w1,w2,w4],[]),([4,2290657962,w7,w3,w1,w2],[]),([4,2576980377,w1,w2,w4],[]),([4,2827528328,w7,w3,w1,w2],[]),([4,w86,w0,w3,w72,w2],[(72,3),(128,0)]),([4,w14,w7,w0,w5,w2],[]),([4,w14,w7,w5,w3,w2],[]),([4,w14,w7,w5,w6,w2],[])]
noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([4,w14,w7,w5,w2],[]),([4,w14,w7,w5,w2,w4],[]),([4,w14,w7,w3,w1,w2],[]),([4,w14,w7,w3,w72,w2],[]),([4,w14,w0,w5,w2,w4],[]),([4,w14,w0,w5,w2,w13],[(72,3)]),([4,w14,w5,w1b,w2,w4],[]),([4,2863136768,w21,w3,w1,w2],[]),([4,2863136768,w0,w3,w1,w2],[]),([4,2863179944,w3,w1,w2,w4],[]),([4,w21,w7,w3,w1,w2],[]),([4,w21,w5,w6,w2,w4],[]),([4,w21,w29,w1,w2,w4],[(116,2)]),([4,w21,w3,w1,w2,w46],[]),([4,w21,w3,w1,w2,w4],[]),([4,w7,w4f,w3,w1,w2],[]),([4,w7,w0,w5,w28,w2],[(72,3)]),([4,w7,w0,w5,w6,w2],[(72,3)]),([4,w7,w0,w5f,w1,w2],[(108,1),(140,3)]),([4,w7,w0,w67,w6,w2],[(72,3)]),([4,w7,w0,wf,w1,w75],[(108,1)]),([4,w7,w0,wf,w1,w2],[(108,1)]),([4,w7,w0,3435711680,w1,w2],[]),([4,w7,w0,w35,w1,w2],[]),([4,w7,w0,w23,w1,w2],[]),([4,w7,w0,w5b,w1,w2],[]),([4,w7,w0,w3,w1,w2],[]),([4,w7,w0,w3,w1,w87],[]),([4,w7,w0,w3,w1,4286643968],[]),([4,w7,w0,w3,w1,w39],[]),([4,w7,w0,w3,w1,w26],[(72,2)]),([4,w7,w0,w3,w1,w97],[(72,2),(96,0)]),([4,w7,w0,w3,w88,w26],[(72,1)]),([4,w7,w0,w3,w7f,w11],[(140,2)]),([4,w7,w0,w3,w95,w5a],[]),([4,w7,2863639215,w3,w1,w2],[]),([4,w7,w3,w22,w1,w2],[]),([4,2863289685,w0,w3,w1,w2],[]),([4,2863289685,w3,w1,w2],[]),([4,2863300608,w0,w3,w1,w2],[]),([4,w58,w0,w5,w6,w2],[(72,3)]),([4,w58,w0,w3,w1,w2],[]),([4,w58,w3,w1b,w1,w2],[]),([4,2863302784,w0,w3,w1,w2],[]),([4,w32,2863308960,w3,w1,w2],[]),([4,w32,w0,w1e,w1,w2],[]),([4,w32,wc,wd,w1,w2],[(148,0)]),([4,w32,w3,w2d,w2,w4],[]),([4,w32,w28,w1,w2,w4],[]),([4,2863310984,w3,w1,w2,w4],[]),([4,2863310984,w3,w1,w2,w33],[]),([4,w4f,w5,w6,w2,w4],[]),([4,w4f,w1e,w1,w2,w4],[]),([4,w4f,w3,w1,w12,w2],[]),([4,w4f,w3,w1,w93,w4],[]),([4,w4f,w3,w1,w2,w4],[]),([4,w4f,w3,w1,w2,w24],[]),([4,2863311528,w3,w1,w2,w4],[]),([4,w0,2863595520,w3,w1,w2],[]),([4,w0,2867724288,w3,w1,w2],[]),([4,w0,w76,w3,w1,w2],[]),([4,w0,2868838485,w3,w1,w2],[]),([4,w0,2952724480,w3,w1,w2],[]),([4,w0,w2e,w3,w11,w33],[]),([4,w0,w2e,w59,w11,w4],[]),([4,w0,w89,w8a,w2,w4],[]),([4,w0,w89,w6,w2,w4],[]),([4,w0,w5,3907578088,w2,w4],[(136,3)]),([4,w0,w5,w7c,w6,w4],[(136,3)]),([4,w0,w5,w68,w6,w2],[(80,3)])]
noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([4,w0,w5,w38,w6,w2],[(80,3),(104,3)]),([4,w0,w5,w28,w2,w4],[]),([4,w0,w5,w28,w2,w13],[]),([4,w0,w5,w71,w6,w4],[]),([4,w0,w5,w19,w6,w2],[]),([4,w0,w5,w73,w2f,w4],[]),([4,w0,w5,4238933160,w2,w4],[]),([4,w0,w5,w8a,w2,w4],[]),([4,w0,w5,w12,w2,w3d],[]),([4,w0,w5,w47,w2,w4],[]),([4,w0,w5,w50,w2,w20],[]),([4,w0,w5,w6d,w2,w4],[]),([4,w0,w5,4244438016,w2,w4],[]),([4,w0,w5,4244438220,w2,w4],[]),([4,w0,w5,w6,w98,w4],[]),([4,w0,w5,w6,w48,w2],[]),([4,w0,w5,w6,w93,w4],[]),([4,w0,w5,w6,w2,w69],[]),([4,w0,w5,w6,w2,w46],[]),([4,w0,w5,w6,w2,w4],[]),([4,w0,w5,w6,w2,w16],[]),([4,w0,w5,w6,w2,w3e],[]),([4,w0,w5,w6,w2,w49],[]),([4,w0,w5,w6,w2,w13],[]),([4,w0,w5,w6,w2,w6e],[]),([4,w0,w5,w6,w2,4294966272],[]),([4,w0,w5,w6,w39,w4],[]),([4,w0,w5,4261281277,w2,w4],[]),([4,w0,w5,w2,4294769916,w4],[]),([4,w0,3234647244,w1,w2,w4],[]),([4,w0,w99,w6,w2,w4],[]),([4,w0,w99,w2,w4],[]),([4,w0,w5f,4037079200,w2,w4],[]),([4,w0,w5f,w1,4205445120,w2],[]),([4,w0,w5f,w1,w2,w4],[]),([4,w0,w5f,w1,w2,w33],[(132,2)]),([4,w0,w80,w6,w2,w4],[]),([4,w0,w67,w1d,w1,w2],[(104,4)]),([4,w0,w67,w1,w2,we],[]),([4,w0,w67,w6,w2,w4],[]),([4,w0,3368601736,w1,w2,w4],[]),([4,w0,3368601792,w1,w2,w4],[]),([4,w0,wf,w2d,w2,w4],[]),([4,w0,wf,w68,w1,w2],[]),([4,w0,wf,w71,w1,w4],[]),([4,w0,wf,w19,w1,w2],[]),([4,w0,wf,w6a,w2,w20],[(132,1)]),([4,w0,wf,w8b,w2,w4],[]),([4,w0,wf,w1,w75,w51],[]),([4,w0,wf,w1,w75,w4],[]),([4,w0,wf,w1,w51,w2],[]),([4,w0,wf,w1,w98,w4],[]),([4,w0,wf,w1,w48,w2],[]),([4,w0,wf,w1,w9a,w4],[]),([4,w0,wf,w1,w2,w69],[]),([4,w0,wf,w1,w2,4294574080],[]),([4,w0,wf,w1,w2,w4],[]),([4,w0,wf,w1,w2,4294903045],[]),([4,w0,wf,w1,w2,w16],[]),([4,w0,wf,w1,w2,w13],[]),([4,w0,wf,w1,w2,4294952960],[]),([4,w0,wf,w1,w2,w6e],[]),([4,w0,wf,w1,w2,w33],[]),([4,w0,wf,w1,w87,w4],[]),([4,w0,wf,4126537205,w2,w4],[]),([4,w0,wf,4176541936,w2,w4],[]),([4,w0,wf,w88,w2,w4],[]),([4,w0,wf,w9b,w2,w4],[]),([4,w0,wf,w6b,w2,w4],[]),([4,w0,wf,w2,4293980400,w4],[]),([4,w0,3368602828,w1,w2,w4],[])]
noncomputable def K_3 : List (List ℕ × List (ℕ × ℕ)) := [([4,w0,3368863948,w1,w2,w4],[]),([4,w0,w29,w1,w2,w46],[(116,2)]),([4,w0,w29,w1,w10,w4],[]),([4,w0,3435710664,w1,w2,w4],[]),([4,w0,3435711680,w1,w2,w4],[]),([4,w0,w35,w1,w51,w2],[]),([4,w0,w35,w1,w2,4294574080],[]),([4,w0,w35,w1,w2,w4],[]),([4,w0,wc,w1d,w1,w2],[]),([4,w0,3435934515,w1,w2],[]),([4,w0,w8c,w1,w2,we],[]),([4,w0,w8c,w1,w2,w9c],[]),([4,w0,w7e,w1,w2,we],[]),([4,w0,w7e,w1,w2,4294966476],[]),([4,w0,w1e,w1d,w1,w2],[]),([4,w0,w1e,w1,w93,w4],[]),([4,w0,w1e,w1,w2,w15],[]),([4,w0,w1e,w1,w2,w6e],[]),([4,w0,w1e,w1,w2,we],[]),([4,w0,w1e,w2a,w2,w4],[]),([4,w0,w9d,w1,w2,w4],[]),([4,w0,w9d,w1,w2,w33],[]),([4,w0,3435972800,w1,w2,w4],[]),([4,w0,w23,w1,w51,w2],[]),([4,w0,w23,w1,w9a,w4],[]),([4,w0,w23,w1,w2,w4],[]),([4,w0,w23,w1,w2,w13],[]),([4,w0,w5b,w1,w2,w4c],[(116,2)]),([4,w0,w5b,w1,w2,w4],[]),([4,w0,w5b,w1,w2,w13],[]),([4,w0,w5b,w1,w2,w81],[]),([4,w0,w5b,w1,w2,we],[]),([4,w0,3435973832,w1,w2,w4],[]),([4,w0,w3,3489595392,w1,w2],[]),([4,w0,w3,3937009664,w1,w2],[]),([4,w0,w3,3937058816,w1,w2],[]),([4,w0,w3,w68,w1,w2],[]),([4,w0,w3,w38,w1,w2],[(104,3)]),([4,w0,w3,w38,w6,w2],[(104,3)]),([4,w0,w3,w85,w72,w2],[(80,3)]),([4,w0,w3,4008312832,w1,w2],[]),([4,w0,w3,4008365248,w1,w2],[]),([4,w0,w3,4008443904,w1,w2],[]),([4,w0,w3,w19,w1,w2],[]),([4,w0,w3,w19,w1,4279369489],[]),([4,w0,w3,4008592452,w1,w2],[]),([4,w0,w3,4008624320,w1,w2],[]),([4,w0,w3,w1d,w1,w26],[(80,2)]),([4,w0,w3,4008632320,w1,w2],[]),([4,w0,w3,4009689088,w1,w2],[]),([4,w0,w3,w1,4277010432,w2],[]),([4,w0,w3,w1,4277071872,w2],[]),([4,w0,w3,w1,4277927936,w2],[]),([4,w0,w3,w1,w48,w2],[]),([4,w0,w3,w1,w2,w46],[]),([4,w0,w3,w1,w2,4294836224],[]),([4,w0,w3,w1,w2,w4],[]),([4,w0,w3,w1,w2,4294901763],[]),([4,w0,w3,w1,w2,4294901765],[]),([4,w0,w3,w1,w2,4294901828],[]),([4,w0,w3,w1,w2,w8d],[]),([4,w0,w3,w1,w2,4294901952],[]),([4,w0,w3,w1,w2,4294903125],[]),([4,w0,w3,w1,w2,4294918208],[]),([4,w0,w3,w1,w2,w77],[]),([4,w0,w3,w1,w2,4294923348],[]),([4,w0,w3,w1,w2,w16],[]),([4,w0,w3,w1,w2,4294934528],[]),([4,w0,w3,w1,w2,w3e],[]),([4,w0,w3,w1,w2,4294936704],[]),([4,w0,w3,w1,w2,w49],[])]
noncomputable def K_4 : List (List ℕ × List (ℕ × ℕ)) := [([4,w0,w3,w1,w2,4294951040],[]),([4,w0,w3,w1,w2,w13],[]),([4,w0,w3,w1,w2,4294952132],[]),([4,w0,w3,w1,w2,4294953152],[]),([4,w0,w3,w1,w2,w81],[]),([4,w0,w3,w1,w2,4294956501],[]),([4,w0,w3,w1,4278255363,w4],[]),([4,w0,w3,w1,4278255365,w4],[]),([4,w0,w3,w1,4278320897,w4],[]),([4,w0,w3,w1,4278517508,w4],[]),([4,w0,w3,w1,4278583040,w4],[]),([4,w0,w3,w1,w87,w4],[]),([4,w0,w3,w1,w87,4294903045],[]),([4,w0,w3,w1,4279041792,w4],[]),([4,w0,w3,w1,4279631637,w4],[]),([4,w0,w3,w1,4286643968,w4],[]),([4,w0,w3,w1,w39,w4],[]),([4,w0,w3,w1,w39,w3e],[]),([4,w0,w3,w1,w39,w13],[]),([4,w0,w3,w1,w26,w69],[]),([4,w0,w3,w1,w26,w4],[]),([4,w0,w3,w1,w26,w15],[]),([4,w0,w3,w1,w26,we],[]),([4,w0,w3,w1,4287168384,w4],[]),([4,w0,w3,w1,w10,4294936576],[]),([4,w0,w3,w1,w10,w6e],[]),([4,w0,w3,w1,w97,w4],[]),([4,w0,w3,w1,w5a,w65],[]),([4,w0,w3,w1,w5a,4291611852],[]),([4,w0,w3,4059165169,4279369489,w4],[]),([4,w0,w3,4169726088,w11,w4],[]),([4,w0,w3,4176541936,w10,w4],[]),([4,w0,w3,w88,w26,w4],[]),([4,w0,w3,w7f,w11],[(100,2),(102,2),(101,2)]),([4,w0,w3,w7f,w11,w4],[(100,2)]),([4,w0,w3,w36,w11,w33],[(100,2),(132,2)]),([4,w0,w3,w95,w5a],[]),([4,w0,w3,w95,w5a,w4],[]),([4,w0,w3,w72,w5a,w11],[(132,2),(156,0)]),([4,2863311535,w3,w1,w2,w4],[]),([4,w1f,w3,w1,w2,w16],[]),([4,2863377067,w3,w1,w2,w4],[]),([4,w5,w22,w6,w2,w4],[(96,3),(128,3)]),([4,w5f,w22,w1,w2,w4],[]),([4,wf,w22,w1,w2,w4],[]),([4,w3,3937009664,w22,w1,w2],[]),([4,w3,3937053354,w1,w2,w4],[]),([4,w3,w22,w1,w2,w4],[]),([4,w3,w22,w1,w2,w49],[]),([4,w3,w22,w1,w2,w13],[(72,3)]),([4,w3,w22,w1,w5c,w4],[(72,3)]),([5,0,w7,w0,w3,w1,w2],[]),([5,0,w0,w3,w1,w2,w4],[]),([5,0,w0,w3,w1,w2,w16],[]),([5,15,w0,w3,w1,w2,w4],[(72,2)]),([5,85,w0,w3,w1,w2,w4],[(72,2),(96,0)]),([5,170,w0,w3,w1,w2,w4],[]),([5,204,w0,w3,w1,w2,w4],[]),([5,255,w7,w0,w3,w1,w2],[]),([5,255,w0,w3,w1,w4a],[(128,3)])]
noncomputable def K_5 : List (List ℕ × List (ℕ × ℕ)) := [([5,255,w0,w3,w1,w2,w4],[]),([5,4095,w0,w3,w1,w2],[(2,2)]),([5,4095,w0,w3,w1,w2,w4],[]),([5,4095,w0,w3,w1,w2,w33],[]),([5,17476,w0,w3,w1,w2,w4],[]),([5,21845,w7,w0,w3,w1,w2],[]),([5,21845,w7,w3,w1,w2],[]),([5,21845,w0,w3,w1,w2,w4],[]),([5,21845,w0,w3,w1,w2,w16],[]),([5,21845,w1f,w3,w1,w2,w4],[]),([5,22015,w0,w3,w1,w2,w4],[]),([5,34952,w0,w3,w1,w2,w4],[]),([5,43690,65535,w7,w3,w1,w2],[]),([5,43690,w9,w0,w3,w1],[]),([5,43690,wb,w3,w1,w2],[]),([5,43690,w3a,w7,w3,w1,w2],[]),([5,43690,w3a,w3,w1,w2],[]),([5,43690,w7,w0,w3,w1,w2],[]),([5,43690,w7,w3,w1,w2],[]),([5,43690,w7,w3,w1,w2,w4],[]),([5,43690,w0,w3,w1,w2],[]),([5,43690,w0,w3,w1,w2,w4],[]),([5,43690,w0,w3,w1,w2,w16],[]),([5,43690,w1f,w3,w1,w2],[]),([5,43690,w1f,w3,w1,w2,w4],[]),([5,49344,w0,w3,w1,w2,w4],[]),([5,52428,w7,w0,w3,w1,w2],[]),([5,52428,w0,wc,w1,w2,w4],[]),([5,52428,w0,w3,w1,w2,w4],[]),([5,52428,w0,w52,w1,w2],[]),([5,52428,w0,w52,w1,w2,w4],[])]
noncomputable def K_6 : List (List ℕ × List (ℕ × ℕ)) := [([5,61166,w0,w3,w1,w2],[(2,2)]),([5,61166,w0,w3,w1,w2,w4],[]),([5,64764,w0,w3,w1,w2,w4],[]),([5,65535,w9,w4b,w0,w3],[]),([5,65535,w9,wb,w3,w1],[]),([5,65535,w9,w0,w3,w1],[]),([5,65535,wb,w7,w3,w1,w2],[]),([5,65535,wb,w3,w1,w2],[]),([5,65535,wa,wd,w1,w2],[]),([5,65535,w7,w0,w3,w1,w2],[]),([5,65535,w7,w3,w1,w2,w8],[]),([5,65535,w0,w5,w6,w2],[]),([5,65535,w0,w5,w6,w2,w4],[]),([5,65535,w0,wf,w1,w2],[]),([5,65535,w0,wf,w1,w2,w4],[]),([5,65535,w0,wc,w1,w2,we],[]),([5,65535,w0,w3,w19,w1,w2],[]),([5,65535,w0,w3,w1,w2],[]),([5,65535,w0,w3,w1,w2,w4],[]),([5,65535,w0,w3,w1,w2,w16],[]),([5,65535,w0,w3,w1,w2,w13],[]),([5,196611,w0,w3,w1,w2,w4],[]),([5,327685,w0,w3,w1,w2,w4],[(72,2),(96,0)]),([5,655370,w0,w3,w1,w2,w4],[]),([5,786444,w0,w3,w1,w2,w4],[]),([5,983040,w0,w3,w1,w2,w4],[]),([5,w53,w7,w0,w3,w1,w2],[]),([5,w53,w0,w3,w3c,w11,w4],[(96,2)]),([5,w53,w0,w3,w3c,w4],[(2,2),(96,2)]),([5,w53,w0,w3,w1,w2,w4],[])]
noncomputable def K_7 : List (List ℕ × List (ℕ × ℕ)) := [([5,983295,w0,w3,w1,w2,w4],[]),([5,1048575,w0,w3,w1,w2,w4],[]),([5,4128831,w0,w3,w1,w2,w4],[]),([5,4456516,w0,w3,w1,w2,w4],[(96,0)]),([5,5570560,w0,w3,w1,w2,w4],[(72,2),(96,0)]),([5,w54,w55,w3,w1,w4],[(56,3)]),([5,w54,w7,w0,w3,w1,w2],[(96,2),(128,0)]),([5,w54,w0,w82,w1,w2,w4],[(72,2),(96,0),(128,0),(168,0)]),([5,w54,w0,w3,w1,w2,w69],[(72,4),(96,3)]),([5,w54,w0,w3,w1,w2,w4],[(72,2),(96,0)]),([5,w54,w0,w3,w1,w2,w8d],[(72,2),(96,0)]),([5,w54,w0,w3,4042649845,w2,w4],[(72,3),(96,0),(168,0)]),([5,5570815,w7,w0,w3,w1,w2],[]),([5,5570815,w0,w3,w1,w2,w4],[]),([5,5592405,w0,w3,w1,w2,w4],[]),([5,5636095,w0,w3,w1,w2],[(2,3)]),([5,5636095,w0,w3,w1,w2,w69],[]),([5,5636095,w0,w3,w1,w2,w4],[]),([5,6226015,w0,w3,w1,w2,w4],[]),([5,8913032,w0,w3,w1,w2,w4],[]),([5,11141120,w7,w0,w3,w1,w2],[]),([5,11141120,w0,w3,w1,w2,w4],[]),([5,w3f,w55,w3,w1,w2,w4],[]),([5,w3f,w7,w0,w3,w1,w2],[]),([5,w3f,w0,w3,w1,w2,w4],[]),([5,w3f,w40,w3,w1,w2,w4],[]),([5,w3f,w40,w3,w1,w4],[]),([5,11184810,w0,w3,w1,w2,w4],[]),([5,12583104,w0,w3,w1,w2,w4],[]),([5,13369344,w0,w3,w1,w2,w4],[(96,0)]),([5,w41,w7,w0,w3,w1,w2],[]),([5,w41,w0,w5d,w1,w2,w4],[(128,0)]),([5,w41,w0,w3,w1,w2,w4],[]),([5,w41,w0,w4d,w1,w2,w4],[]),([5,w41,w0,w4d,w1,w4],[]),([5,13421772,w0,w3,w1,w2,w4],[])]
noncomputable def K_8 : List (List ℕ × List (ℕ × ℕ)) := [([5,15597806,w0,w3,w1,w2,w4],[]),([5,15597806,w0,w3,w1,w4],[(2,1)]),([5,16515324,w0,w3,w1,w2,w4],[]),([5,w42,w7,w0,w3,w1,w2],[]),([5,w42,w0,w3,w1,w4a,w2],[]),([5,w42,w0,w3,w1,w2,w4],[]),([5,w42,w0,w3,w1,w2,w43],[]),([5,w42,w0,w3,w1,w2,we],[]),([5,w42,w0,w3,w1,w43],[]),([5,16711850,w0,w3,w1,w2,w4],[]),([5,16711884,w0,w3,w1,w2,w4],[]),([5,w9,w4b,858993459,w0,w4],[]),([5,w9,w4b,wb,w3,w4],[]),([5,w9,w4b,w7,w0,w3],[]),([5,w9,w4b,w0,w3,w4],[]),([5,w9,wb,w7,w3,w1],[]),([5,w9,wb,w3,w1,w4],[]),([5,w9,wb,w3,w1,w16],[]),([5,w9,w3a,w0,w3,w1],[]),([5,w9,wa,wd,w1,w4],[]),([5,w9,w55,w3,w1,w18,w4],[]),([5,w9,w7,w0,w3,w1],[]),([5,w9,w7,w0,w3,w1,w2],[]),([5,w9,w7,w3,w1,w8],[]),([5,w9,w0,w76,w3,w1],[]),([5,w9,w0,w76,w3,w1,w2],[])]
noncomputable def K_9 : List (List ℕ × List (ℕ × ℕ)) := [([5,w9,w0,w5,w6,w2,w4],[]),([5,w9,w0,w5,w6,w4],[]),([5,w9,w0,wf,w1,w2,w4],[]),([5,w9,w0,wf,w1,w4],[]),([5,w9,w0,w5d,w1,w27,w4],[]),([5,w9,w0,w82,w1,w2,w4],[]),([5,w9,w0,w82,w1,w4],[(2,0)]),([5,w9,w0,wc,w1,we],[]),([5,w9,w0,w3,w71,w1,w4],[]),([5,w9,w0,w3,w19,w1],[]),([5,w9,w0,w3,w19,w1,w2],[]),([5,w9,w0,w3,w1,w2,w69],[]),([5,w9,w0,w3,w1,w2,w4],[]),([5,w9,w0,w3,w1,w2,w16],[]),([5,w9,w0,w3,w1,w2,w13],[]),([5,w9,w0,w3,w1,w2,w6e],[]),([5,w9,w0,w3,w1,w69],[(2,3)]),([5,w9,w0,w3,w1,w4],[]),([5,w9,w0,w3,w1,w16],[]),([5,w9,w0,w3,w1,w13],[]),([5,w9,w0,w3,w1,w6e],[(2,0)]),([5,16715775,w0,w3,w1,w2,w4],[]),([5,16733695,w0,w3,w1,w2,w4],[]),([5,w66,w7,w0,w3,w1,w2],[]),([5,w66,w0,w3,w1,w2,w4],[]),([5,w66,w0,w3,w1,w24],[]),([5,67044351,w0,w3,w1,w2,w4],[]),([5,89458005,w0,w3,w1,w2,w4],[(72,2)]),([5,w9e,w0,w3,w1,w75,w4],[])]
noncomputable def K_10 : List (List ℕ × List (ℕ × ℕ)) := [([5,w9e,w0,w3,w1,w2,w4],[]),([5,w9e,w0,w3,w1,w4],[(2,4)]),([5,178916010,w0,w3,w1,w2,w4],[]),([5,214699212,w0,w3,w1,w2,w4],[]),([5,w74,w56,w0,w3,w1,w2],[]),([5,w74,w0,w3,w3c,w1,w2],[(96,2)]),([5,w74,w0,w3,w1,w2],[]),([5,w74,w0,w3,w1,w2,w4],[]),([5,w56,w7,w0,w3,w1,w2],[]),([5,w56,w0,w3,w3c,w11,w4],[]),([5,w56,w0,w3,w1,w2,w4],[]),([5,w56,w0,w3,w1,w2,w33],[]),([5,w56,w0,w3,w11,w4],[(2,2)]),([5,268435455,w0,w3,w1,w2,w4],[]),([5,1073692671,w0,w3,w1,w2,w4],[]),([5,1077952576,w0,w3,w1,w2,w4],[]),([5,w9f,w0,w3,w1,w2,w4],[]),([5,w30,wa,w0,w1,w2,w4],[]),([5,w30,w7,w0,w3,w1,w2],[]),([5,w30,w0,w3,w1,w2,w4],[]),([5,w30,w0,w3,w1,w2,w77],[]),([5,w30,w0,w3,w1,w2,w16],[]),([5,w30,w0,w44,w1,w2,w4],[]),([5,w30,w44,w1,w2,w4],[]),([5,1145359564,w7,w0,w3,w1,w2],[]),([5,1145359564,w0,w3,w1,w2,w4],[]),([5,w60,w0,w3,w1,w2,w4],[]),([5,1414812756,w0,w3,w1,w2,w4],[]),([5,w17,w7,w0,w3,w1,w2],[]),([5,w17,w0,w3,w1,w2,w4],[]),([5,w17,w0,w3,w1,w2,w16],[]),([5,w17,w3,w1,w2,w16],[]),([5,1431651396,w0,w3,w1,w2,w4],[]),([5,wb,w3a,w3,w1,w2],[])]
noncomputable def K_11 : List (List ℕ × List (ℕ × ℕ)) := [([5,wb,w7,w0,w3,w1,w2],[]),([5,wb,w7,w3,w1,w2],[]),([5,wb,w0,w5,w6,w2,w4],[]),([5,wb,w0,wf,w1,w2,w4],[]),([5,wb,w0,w3,w19,w1,w2],[]),([5,wb,w0,w3,w1,w2,w4],[]),([5,wb,w0,w3,w1,w2,w77],[]),([5,wb,w0,w3,w1,w2,w16],[]),([5,wb,w0,w3,w1,w2,w13],[]),([5,wb,w1f,w3,w1,w2,w4],[]),([5,wb,w5,w6,w2,w4],[]),([5,wb,wf,w1,w2,w4],[]),([5,wb,wc,w1,w2,we],[]),([5,wb,w3,w19,w1,w2],[]),([5,wb,w3,w1,w2,w4],[]),([5,wb,w3,w1,w2,w77],[]),([5,wb,w3,w1,w2,w16],[]),([5,wb,w3,w1,w2,w13],[]),([5,1431655935,w0,w3,w1,w2,w4],[]),([5,w3a,w7,w0,w3,w1,w2],[]),([5,w3a,w0,w3,w1,w2],[]),([5,w3a,w0,w3,w1,w2,w4],[]),([5,w3a,w3,w1,w2,w8],[]),([5,1432311135,w0,w3,w1,w2,w4],[]),([5,w6f,w0,w3,w1,w2,w4],[]),([5,w57,w7,w0,w3,w1,w2],[]),([5,w57,w0,w3,w1,w2,w4],[]),([5,w57,w3,w1,w18,w4],[])]
noncomputable def K_12 : List (List ℕ × List (ℕ × ℕ)) := [([5,1442840575,w7,w0,w3,w1,w2],[(132,1)]),([5,1442840575,w0,w3,w1,w2,w4],[(100,1)]),([5,1610571775,w0,w3,w1,w2,w4],[]),([5,2147516416,w0,w3,w1,w2,w4],[]),([5,2155872256,w7,w0,w3,w1,w2],[]),([5,2155872256,w0,w3,w1,w2,w4],[]),([5,w31,w7,w0,w3,w1,w2],[]),([5,w31,w0,w5,w6,w2,w4],[]),([5,w31,w0,w3,w1,w2,w4],[]),([5,w31,w0,w3,w1,w2,w3e],[]),([5,w31,w0,w3,w1,w2,w13],[]),([5,w31,w0,w3,w1,w39,w4],[]),([5,w31,w0,w3,w2a,w2,w4],[(128,0),(168,0)]),([5,2290124928,w0,w3,w1,w2,w4],[(96,0)]),([5,w25,w7,w0,w3,w1,w2],[(128,0)]),([5,w25,w7,w0,w3,w1,w26],[]),([5,w25,w7,w0,w1d,w1,w2],[(128,4),(168,2)]),([5,w25,w0,w3,w1d,w1,w2],[(128,0)]),([5,w25,w0,w3,w1,w2,w4],[(96,0)]),([5,w25,w0,w3,w1,w2,w15],[(96,0)]),([5,w25,w0,w3,w1,w2,we],[(96,0)]),([5,w25,w0,w3,w1,w26,w4],[]),([5,w25,w0,w1d,w1,w2],[(96,4),(98,0),(97,1),(128,2),(129,3)]),([5,w25,w0,w1d,w1,w2,w4],[(96,4),(128,2)]),([5,2290647168,w0,w3,w1,w2,w4],[(96,0)]),([5,wa,w7d,w7,w3,w1,w2],[(128,1)]),([5,wa,w7d,w0,w5,w2,w4],[(96,1)]),([5,wa,2862656160,w3,w1,w2,w4],[]),([5,wa,w7,w0,w5,w1,w2],[(128,1)]),([5,wa,w7,w0,w3,w1,w2],[]),([5,wa,w7,w0,w1d,w1,w2],[]),([5,wa,w7,w0,wd,w1,w2],[(196,0)]),([5,wa,w7,w3,wd,w1,w2],[(196,0)]),([5,wa,w7,wd,w1,w2],[(148,0),(150,0),(149,0)]),([5,wa,w7,wd,w1,w2,w4],[(148,0)]),([5,wa,2863308960,w3,w1,w2,w4],[(96,1)]),([5,wa,w0,w2e,w1,w2,w4],[]),([5,wa,w0,w5,w1,w2,w4],[(96,1)])]
noncomputable def K_13 : List (List ℕ × List (ℕ × ℕ)) := [([5,wa,w0,w5,w1,w2,w13],[(96,1)]),([5,wa,w0,w5,w2a,w2,w4],[(56,1),(96,1)]),([5,wa,w0,w5,w6,w2,w4],[]),([5,wa,w0,wf,w1,w2,w4],[]),([5,wa,w0,w29,w1,w2,w4],[(96,0)]),([5,wa,w0,w1e,w1,w2,w4],[]),([5,wa,w0,w3,w2d,w2,w4],[(56,1),(72,1)]),([5,wa,w0,w3,w19,w1,w2],[]),([5,wa,w0,w3,w3c,w11,w4],[(56,2),(72,2)]),([5,wa,w0,w3,4037079200,w2,w4],[(56,2),(72,2)]),([5,wa,w0,w3,w1,w51,w2],[(56,1),(72,1)]),([5,wa,w0,w3,w1,w2,w4],[]),([5,wa,w0,w3,w1,w2,w16],[]),([5,wa,w0,w3,w1,w2,w3e],[(96,0)]),([5,wa,w0,w3,w1,w2,w13],[(96,0)]),([5,wa,w0,w3,w1,w2,w33],[(56,2),(72,2)]),([5,wa,w0,w3,w1,w39,w4],[(96,0)]),([5,wa,w0,w3,w1,w26,w4],[]),([5,wa,w0,w4d,w1,w2,w4],[]),([5,wa,w0,w2d,wd,w2,w4],[]),([5,wa,w0,w2d,w1,w2,w4],[]),([5,wa,w0,w2d,w2,w4],[]),([5,wa,w0,w1b,w1,w2,w4],[(148,0)]),([5,wa,w0,w28,w1,w2,w4],[]),([5,wa,w0,w19,wd,w1,w2],[(196,0)]),([5,wa,w0,w1d,w1,w2,w4],[]),([5,wa,w0,wd,w1,w2,w4],[(148,0)]),([5,wa,w2d,wd,w2,w4],[]),([5,wa,w1b,w1,w2,w4],[]),([5,wa,w19,wd,w1,w2],[(148,0)]),([5,wa,wd,w1,w2,w4],[]),([5,2290657962,w0,w3,w1,w2,w4],[]),([5,2290666700,w0,w3,w1,w2,w4],[]),([5,2290679807,w0,w3,w1,w2,w4],[]),([5,2292877482,w0,w3,w1,w2,w4],[])]
noncomputable def K_14 : List (List ℕ × List (ℕ × ℕ)) := [([5,2295105740,w0,w3,w1,w2,w4],[]),([5,2298448127,w0,w3,w1,w2,w4],[]),([5,2827528328,w0,w3,w1,w2,w4],[(72,2)]),([5,w86,w7,w0,w3,w1,w2],[(96,2),(128,0),(104,1)]),([5,w86,w0,w3,w1,w2,w4],[(72,2),(96,0)]),([5,2829617288,w0,w3,w1,w2,w4],[(72,2)]),([5,w14,w7,w0,w3,w1,w2],[]),([5,w14,w7,w3,w1,w6,w2],[]),([5,w14,w7,w3,w1,w2],[(82,1),(117,1)]),([5,w14,w7,w3,w1,w2,w4],[]),([5,w14,w0,w5,w3,w2,w4],[]),([5,w14,w0,w5,w6,w2,w4],[]),([5,w14,w0,w5,w2,w4],[(109,3)]),([5,w14,w0,w3,w1,w2,w4],[]),([5,w21,w0,w3,w1,w2,w4],[]),([5,w21,w3,w1,w6,w2,w4],[(156,3)]),([5,w21,w3,w1,w2,w2f,w4],[]),([5,w21,w3,w1,w2,w4],[]),([5,w7,w7,w0,w3,w1,w2],[]),([5,w7,w32,w0,w3,w1,w2],[]),([5,w7,w0,w0,w3,w1,w2],[]),([5,w7,w0,w1f,w3,w1,w2],[]),([5,w7,w0,2868838655,w3,w1,w2],[]),([5,w7,w0,w40,w3,w1,w2],[]),([5,w7,w0,w2e,w3,w1,w2],[]),([5,w7,w0,w37,w3,w1,w2],[]),([5,w7,w0,w5,w3,w1,w2],[]),([5,w7,w0,w5,w3,w6,w2],[]),([5,w7,w0,w5,w6,w2],[(72,3),(74,3)]),([5,w7,w0,w5,w6,w2,w4],[(72,3)]),([5,w7,w0,w67,w3,w1,w2],[(144,0)]),([5,w7,w0,wf,w3,w1,w2],[(140,1)]),([5,w7,w0,wf,w1,w1c,w2],[(108,1)]),([5,w7,w0,wf,w1,w2],[(108,1),(110,1),(109,1)]),([5,w7,w0,wf,w1,w2,w4],[(108,1)])]
noncomputable def K_15 : List (List ℕ × List (ℕ × ℕ)) := [([5,w7,w0,w29,w3,w1,w2],[]),([5,w7,w0,wc,w3,w1,w2],[]),([5,w7,w0,wc,w1d,w1,w2],[]),([5,w7,w0,w1a,w3,w1,w2],[]),([5,w7,w0,w1e,w3,w1,w2],[]),([5,w7,w0,w3,w3,w1,w2],[]),([5,w7,w0,w3,w52,w1,w2],[]),([5,w7,w0,w3,w4d,w1,w2],[]),([5,w7,w0,w3,w44,w1,w2],[]),([5,w7,w0,w3,3722313727,w1,w2],[]),([5,w7,w0,w3,w38,w1,w2],[(144,3)]),([5,w7,w0,w3,w1b,w1,w2],[(140,1),(156,1),(196,3)]),([5,w7,w0,w3,w85,w1,w2],[(112,2)]),([5,w7,w0,w3,w28,w1,w2],[(156,1)]),([5,w7,w0,w3,w19,w1,w2],[]),([5,w7,w0,w3,w45,w1,w2],[]),([5,w7,w0,w3,w1d,w1,w2],[]),([5,w7,w0,w3,wd,w1,w2],[(156,1),(196,3)]),([5,w7,w0,w3,w1,w59,w2],[]),([5,w7,w0,w3,w1,w12,w2],[(72,2),(96,0)]),([5,w7,w0,w3,w1,w50,w2],[(96,0)]),([5,w7,w0,w3,w1,w6,w2],[]),([5,w7,w0,w3,w1,4278123772,w2],[(204,3)]),([5,w7,w0,w3,w1,w3b,w2],[(204,3)]),([5,w7,w0,w3,w1,w2],[]),([5,w7,w0,w3,w1,w2,w2f],[]),([5,w7,w0,w3,w1,w2,w4],[]),([5,w7,w0,w3,w1,w2,w43],[]),([5,w7,w0,w3,w1,w2,w16],[]),([5,w7,w0,w3,w1,w2,w15],[]),([5,w7,w0,w3,w1,w2,w8],[]),([5,w7,w0,w3,w1,w2,w13],[]),([5,w7,w0,w3,w1,w2,we],[]),([5,w7,w0,w3,w1,w2,w2b],[(196,1),(204,3)]),([5,w7,w0,w3,w1,w2,w3d],[(204,3)]),([5,w7,w0,w3,w1,w2,w2c],[]),([5,w7,w0,w3,w1,w26],[(72,2),(74,2)]),([5,w7,w0,w3,w1,w26,w4],[(72,2)])]
noncomputable def K_16 : List (List ℕ × List (ℕ × ℕ)) := [([5,w7,w0,w3,w1,w5a,w27],[(72,1),(172,0),(180,0),(148,0)]),([5,w7,w3,w45,w1,w2],[]),([5,w7,w3,w1,w2,w16],[]),([5,w7,w3,w1,w2,w8],[]),([5,2863268010,w0,w3,w1,w2,w4],[]),([5,w58,w0,w5,w3,w1,w2],[]),([5,w58,w0,w3,w1,w2],[(141,3)]),([5,w58,w0,w3,w1,w2,w4],[]),([5,w58,w0,w3,w1,w2,w13],[]),([5,w32,w0,wc,w3,w1,w2],[]),([5,w32,w0,w3,w1,w2,w4],[]),([5,w32,w0,w3,w1,w2,w20],[]),([5,w32,w3,wd,w1,w2,w4],[(148,0)]),([5,w4f,w0,w3,w1,w2,w4],[]),([5,w4f,w3,w1,w6,w2,w4],[]),([5,w4f,w3,w1,w2,w4],[]),([5,w4f,w3,w1,w2,w4,we],[(188,1)]),([5,w4f,w3,w1,w2,w4,w3d],[]),([5,w0,w0,w5,w6,w2,w4],[]),([5,w0,w0,wf,w1,w2,w4],[(100,1)]),([5,w0,w0,w3,w19,w1,w2],[]),([5,w0,w0,w3,w1,w2,w4],[]),([5,w0,w0,w3,w1,w2,w16],[]),([5,w0,w0,w3,w1,w2,w13],[]),([5,w0,2863311615,w3,w1,w2,w4],[]),([5,w0,2863329006,w3,w1,w2,w4],[]),([5,w0,w1f,w3,w1,w2,w4],[]),([5,w0,2863639215,w3,w1,w2,w4],[]),([5,w0,2867768046,w3,w1,w2,w4],[]),([5,w0,w76,w40,w3,w1,w2],[]),([5,w0,w76,w3,w1,w2],[]),([5,w0,w76,w3,w1,w2,w4],[]),([5,w0,2868838655,w3,w1,w2,w4],[])]
noncomputable def K_17 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,2868882090,w3,w1,w2,w4],[]),([5,w0,w40,w3,w1,w2,w4],[]),([5,w0,2868903935,w3,w1,w2,w4],[]),([5,w0,2952769535,w3,w1,w2,w4],[]),([5,w0,3221225472,w3,w1,w2,w4],[]),([5,w0,w2e,w5,w6,w2,w4],[(144,3),(184,3)]),([5,w0,w2e,w3,w1,w2,w4],[]),([5,w0,w2e,w3,w1,w2,w49],[]),([5,w0,w2e,w3,w1,w2,w13],[(112,3)]),([5,w0,w2e,w3,w1,w5c,w4],[(112,3)]),([5,w0,w89,w82,w1,w2,w4],[(56,0),(80,0),(104,0),(136,0),(176,0),(112,1)]),([5,w0,w89,w3,w1,w2,w4],[]),([5,w0,w37,w5,w6,w2,w4],[]),([5,w0,w37,w3,w1,w2,w4],[]),([5,w0,w37,w3,w1,w2,w13],[]),([5,w0,3233841280,w3,w1,w2,w4],[]),([5,w0,3233857536,w3,w1,w2,w4],[]),([5,w0,w5,w5,w6,w2,w4],[]),([5,w0,w5,wf,w1,w2,w4],[(112,1)]),([5,w0,w5,w5d,w1,w27,w4],[(104,0),(136,0),(176,0)]),([5,w0,w5,w82,w1,w2,w4],[(104,0),(136,0),(176,0),(112,1)]),([5,w0,w5,wc,w1,w2,we],[(112,1)]),([5,w0,w5,wc,w6,w2,w4],[]),([5,w0,w5,w1a,w1,w2,w4],[(112,1)]),([5,w0,w5,3435973632,w1,w2,w4],[(176,0),(112,1)]),([5,w0,w5,w3,w7c,w1,w4],[(80,3),(136,3),(176,3)]),([5,w0,w5,w3,w68,w1,w2],[]),([5,w0,w5,w3,w38,w1,w2],[]),([5,w0,w5,w3,w28,w2,w4],[]),([5,w0,w5,w3,w71,w1,w4],[(80,3),(136,3),(176,3)]),([5,w0,w5,w3,w19,w1,w2],[]),([5,w0,w5,w3,w1,w2,w69],[(80,3),(104,3),(176,3)]),([5,w0,w5,w3,w1,w2,w4],[]),([5,w0,w5,w3,w1,w2,w16],[]),([5,w0,w5,w3,w1,w2,w3e],[]),([5,w0,w5,w3,w1,w2,w49],[]),([5,w0,w5,w3,w1,w2,w13],[]),([5,w0,w5,w3,w1,w2,w6e],[(80,0),(104,0)]),([5,w0,w5,w3,w1,w39,w4],[])]
noncomputable def K_18 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w5,w3,4126537205,w2,w4],[]),([5,w0,w5,w3,w2a,w2,w4],[(84,1),(176,0)]),([5,w0,w5,w3,w9b,w2,w4],[]),([5,w0,w5,w3,w6b,w2,w4],[(184,1)]),([5,w0,w5,w3,w6,w2,w4],[]),([5,w0,w5,w3,w6,w2,w13],[]),([5,w0,w5,w3,w2,4293980400,w4],[]),([5,w0,w5,w1b,w6,w2,w4],[(176,3)]),([5,w0,w5,w28,w2,w4],[]),([5,w0,w5,wd,w6,w2,w4],[]),([5,w0,w5,w73,w6,w2,w4],[]),([5,w0,w5,w12,w6,w2,w4],[]),([5,w0,w5,w6,w6,w2,w4],[]),([5,w0,w5,w6,w3b,w2,w4],[]),([5,w0,w5,w6,w4a,w2,w4],[]),([5,w0,w5,w6,w2,w2,w4],[]),([5,w0,w5,w6,w2,w18,w4],[]),([5,w0,w5,w6,w2,w5c,w4],[(108,3)]),([5,w0,w5,w6,w2,w27,w4],[]),([5,w0,w5,w6,w2,w2f,w4],[]),([5,w0,w5,w6,w2,w4],[]),([5,w0,w5,w6,w2,w4,w4],[]),([5,w0,w5,w6,w2,w4,w8],[]),([5,w0,w5,w6,w2,w4,w13],[]),([5,w0,w5,w6,w2,w4,we],[]),([5,w0,w5,w6,w2,w4,w3d],[]),([5,w0,w5,w6,w2,w4,w24],[]),([5,w0,w5,w6,w2,w13],[(58,3),(109,3)]),([5,w0,3233860812,w3,w1,w2,w4],[]),([5,w0,3233873919,w3,w1,w2],[(6,3)]),([5,w0,3233873919,w3,w1,w2,w4],[]),([5,w0,3234644172,w3,w1,w2,w4],[]),([5,w0,3237986559,w3,w1,w2,w4],[]),([5,w0,3301229764,w3,w1,w2,w4],[]),([5,w0,w5f,w3,w1,w2,w4],[]),([5,w0,w5f,w1,w36,w2,w4],[(156,0)])]
noncomputable def K_19 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w5f,w1,w2,w4],[(78,1),(102,3)]),([5,w0,w80,w3,w1,w2,w4],[(104,0)]),([5,w0,wa0,wf,w1,w2,w4],[]),([5,w0,wa0,w3,w1,w51,w2],[(80,1),(104,0),(136,1)]),([5,w0,wa0,w3,w1,w2,w4],[(104,0)]),([5,w0,3368585352,w3,w1,w2,w4],[]),([5,w0,w67,w3,w1,w2,w4],[(104,0)]),([5,w0,wf,wf,w1,w2,w4],[]),([5,w0,wf,wc,w1,w2,w4],[]),([5,w0,wf,w3,w1,w75,w4],[(80,4)]),([5,w0,wf,w3,w1,w51,w2],[(80,1)]),([5,w0,wf,w3,w1,w2,w4],[]),([5,w0,wf,w1b,w1,w2,w4],[(148,3)]),([5,w0,wf,wd,w1,w2,w4],[]),([5,w0,wf,w6a,w1,w2,w4],[]),([5,w0,wf,w1,w1,w2,w4],[]),([5,w0,wf,w1,w2a,w2,w4],[(84,1)]),([5,w0,wf,w1,w75,w1c,w4],[]),([5,w0,wf,w1,w75,w4],[(76,1),(78,1)]),([5,w0,wf,w1,w51,w1c,w2],[]),([5,w0,wf,w1,w51,w2],[(76,1),(78,1)]),([5,w0,wf,w1,w51,w2,w4],[]),([5,w0,wf,w1,w1c,w2,w4],[]),([5,w0,wf,w1,w6,w2,w4],[]),([5,w0,wf,w1,w3b,w2,w4],[]),([5,w0,wf,w1,w4a,w2,w4],[]),([5,w0,wf,w1,w2,w2,w4],[]),([5,w0,wf,w1,w2,w18,w4],[(148,2)]),([5,w0,wf,w1,w2,4291362760,w4],[(108,3)]),([5,w0,wf,w1,w2,w27,w4],[(108,0)]),([5,w0,wf,w1,w2,w11,w4],[(116,2)]),([5,w0,wf,w1,w2,4294639610,w4],[]),([5,w0,wf,w1,w2,w4],[(78,1)]),([5,w0,wf,w1,w2,w4,w4],[]),([5,w0,wf,w1,w2,w4,w8],[])]
noncomputable def K_20 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,wf,w1,w2,w4,4294953160],[]),([5,w0,wf,w1,w2,w4,we],[]),([5,w0,wf,w1,w2,w4,w20],[(172,1)]),([5,w0,wf,w1,w2,w4,wa1],[]),([5,w0,wf,w1,w2,w4,w24],[]),([5,w0,wa2,w3,w1,w2,w4],[]),([5,w0,3435184320,w3,w1,w2,w4],[]),([5,w0,w29,wc,w1,w2,w4],[]),([5,w0,w29,w3,w1,w2,w4],[]),([5,w0,w29,w3,w1,w2,w81],[]),([5,w0,w29,w1,w6,w2,w4],[]),([5,w0,w29,w1,w2,w2f,w4],[(116,2)]),([5,w0,w35,w3,w1,w2,w4],[]),([5,w0,w35,w1,w1c,w2,w4],[(156,4)]),([5,w0,w35,w1,w2,w11,w4],[(116,2)]),([5,w0,w35,w1,w2,4294639610,w4],[]),([5,w0,w35,w1,w2,w4],[]),([5,w0,wc,w3,w19,w1,w2],[]),([5,w0,wc,w3,w1d,w1,w2],[]),([5,w0,wc,w3,w1,w51,w2],[(80,1)]),([5,w0,wc,w3,w1,w2,w4c],[]),([5,w0,wc,w3,w1,w2,w4],[]),([5,w0,wc,w3,w1,w2,w16],[]),([5,w0,wc,w3,w1,w2,w15],[]),([5,w0,wc,w3,w1,w2,w13],[]),([5,w0,wc,w3,w1,w2,we],[]),([5,w0,wc,w3,w1,w2,w33],[(80,2),(176,2)]),([5,w0,wc,w3,w1,w26,w4],[]),([5,w0,wc,w1d,w1,w2],[(105,2),(137,4)]),([5,w0,wc,w1d,w1,w2,w4],[]),([5,w0,wc,wd,w1,w2,we],[(116,1),(148,3)]),([5,w0,wc,w1,w2,we],[]),([5,w0,3435921612,w3,w1,w2,w4],[]),([5,w0,w8c,w3,w1,w2,w4],[]),([5,w0,w8c,w3,w1,w2,w16],[]),([5,w0,3435954304,w3,w1,w2,w4],[]),([5,w0,w1a,w3,w1,w2,w4],[])]
noncomputable def K_21 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w1a,wd,w1,w2,w4],[(116,1),(148,3)]),([5,w0,w7e,w3,w1,w2,w4],[]),([5,w0,w7e,w3,w1,w2,w33],[(80,2),(176,2)]),([5,w0,w1e,w3,w1,w2,w4],[]),([5,w0,w1e,w3,w1,w2,w13],[]),([5,w0,w1e,w3,w1,w2,we],[]),([5,w0,w1e,w1,w6,w2,w4],[]),([5,w0,w1e,w1,w2,w4,we],[]),([5,w0,w1e,w1,w2,w4,w3d],[]),([5,w0,w1e,w1,w2,we],[]),([5,w0,w1e,w1,w2,we,w20],[]),([5,w0,w23,w3,w1,w2,w4],[]),([5,w0,w23,w1,w1c,w2,w4],[(156,4)]),([5,w0,w23,w1,w2,w4],[]),([5,w0,w23,w1,w2,w4,w8],[]),([5,w0,w23,w1,w2,w4,w20],[]),([5,w0,w23,w1,w2,w4,wa1],[]),([5,w0,w5b,w3,w1,w2,w4],[]),([5,w0,w5b,w1,w2,w11,w4],[(116,2)]),([5,w0,w5b,w1,w2,w4],[]),([5,w0,w5b,w1,w2,w4,w20],[(196,4)]),([5,w0,w5b,w1,w2,w4,4294967280],[(172,2)]),([5,w0,w3,w3,w19,w1,w2],[]),([5,w0,w3,w3,w1,w51,w2],[(64,1),(68,1)]),([5,w0,w3,w3,w1,w2,w4],[]),([5,w0,w3,w3,w1,w2,w16],[]),([5,w0,w3,w3,w1,w2,w13],[]),([5,w0,w3,w3,w1,w2,w33],[(64,2),(68,2)]),([5,w0,w3,3435973887,w1,w2,w4],[]),([5,w0,w3,3435978205,w1,w2,w4],[]),([5,w0,w3,3435982574,w1,w2,w4],[]),([5,w0,w3,3435986172,w1,w2,w4],[]),([5,w0,w3,w52,w1,w2,w4],[]),([5,w0,w3,3436170447,w1,w2,w4],[]),([5,w0,w3,3437087965,w1,w2,w4],[(80,2)]),([5,w0,w3,3438202094,w1,w2,w4],[])]
noncomputable def K_22 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w3,3439119612,w1,w2,w4],[]),([5,w0,w3,3439263744,w1,w2,w4],[]),([5,w0,w3,3439263999,w1,w2,w4],[]),([5,w0,w3,3439316172,w1,w2,w4],[]),([5,w0,w3,w4d,w1,w2,w4],[]),([5,w0,w3,3439329279,w1,w2,w4],[(116,1)]),([5,w0,w3,3489648639,w1,w2,w4],[]),([5,w0,w3,3587560917,w1,w2,w4],[]),([5,w0,w3,3705461980,w1,w2,w4],[]),([5,w0,w3,w78,w1,w2,w4],[]),([5,w0,w3,3722270037,w1,w2,w4],[]),([5,w0,w3,w8e,w1,w2,w4],[]),([5,w0,w3,w44,w1,w2,w4],[]),([5,w0,w3,w44,w1,w2,w16],[]),([5,w0,w3,3722313727,w1,w2,w4],[]),([5,w0,w3,3724533247,w1,w2,w4],[]),([5,w0,w3,w22,w1,w2,w4],[(100,1),(132,3),(116,1),(148,3)]),([5,w0,w3,3938511552,w1,w2,w4],[(104,3),(148,3)]),([5,w0,w3,w68,w1b,w1,w2],[(156,1),(196,3)]),([5,w0,w3,w68,w1,w2],[]),([5,w0,w3,w68,w1,w2,w4],[]),([5,w0,w3,w5e,w1,w2,w4],[]),([5,w0,w3,w38,w1,w2],[(102,1),(104,3),(105,1)]),([5,w0,w3,w38,w1,w2,w4],[(104,3)]),([5,w0,w3,w1b,w1,w2,w4],[(116,1),(148,3)]),([5,w0,w3,w1b,w1,w2,w13],[(104,3),(116,1),(148,3)]),([5,w0,w3,3972852940,w1,w2,w4],[(80,2)]),([5,w0,w3,3974889472,w1,w2,w4],[(80,2)]),([5,w0,w3,3974930592,w1,w2,w4],[]),([5,w0,w3,w85,w1,w2,w4],[(80,2)]),([5,w0,w3,w28,w1,w2,w4],[(116,1)]),([5,w0,w3,4007718624,w1,w2,w4],[(116,1),(148,3),(156,2)]),([5,w0,w3,4008373994,w1,w2,w4],[(116,1),(148,3)]),([5,w0,w3,4008505068,w1,w2,w4],[(116,1),(148,3)]),([5,w0,w3,w19,w19,w1,w2],[]),([5,w0,w3,w19,w45,w1,w2],[]),([5,w0,w3,w19,w1d,w1,w2],[]),([5,w0,w3,w19,wd,w1,w2],[(156,1),(196,3)])]
noncomputable def K_23 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w3,w19,w1,w1c,w2],[(204,4)]),([5,w0,w3,w19,w1,w6,w2],[]),([5,w0,w3,w19,w1,4278120688,w2],[]),([5,w0,w3,w19,w1,w3b,w2],[(204,3)]),([5,w0,w3,w19,w1,w2],[]),([5,w0,w3,w19,w1,w2,w11],[(156,2)]),([5,w0,w3,w19,w1,w2,w4],[]),([5,w0,w3,w19,w1,w2,w8],[]),([5,w0,w3,w19,w1,w2,we],[]),([5,w0,w3,w19,w1,w2,w2b],[(196,1),(204,3)]),([5,w0,w3,w19,w1,w2,w20],[]),([5,w0,w3,w45,w1,w2,w4],[]),([5,w0,w3,w1d,w1,w72,w2],[(104,3),(116,1)]),([5,w0,w3,w1d,w1,w2,w4],[]),([5,w0,w3,w1d,w1,w2,w20],[(116,1)]),([5,w0,w3,4008632544,w1,w2,w4],[(116,1)]),([5,w0,w3,4008635114,w1,w2,w4],[(116,1),(148,3)]),([5,w0,w3,4008635628,w1,w2,w4],[(116,1),(148,3)]),([5,w0,w3,wd,w1,w48,w2],[(116,1),(188,3)]),([5,w0,w3,wd,w1,w2,w4],[(116,1),(148,3)]),([5,w0,w3,wd,w1,w2,4294906129],[(76,2),(84,2),(116,1),(148,3)]),([5,w0,w3,wd,w1,w2,w16],[(116,1),(148,3)]),([5,w0,w3,wd,w1,w2,w13],[(116,1),(148,3)]),([5,w0,w3,wd,w1,w2,w33],[(76,2),(84,2),(116,1),(148,3)]),([5,w0,w3,wd,w1,4279369489,w4],[(76,1),(84,1),(116,1),(148,3)]),([5,w0,w3,4008640511,w1,w2,w4],[(116,1),(148,3)]),([5,w0,w3,4009750271,w1,w2,w4],[(116,1),(148,3)]),([5,w0,w3,w1,w8f,w2,w4],[]),([5,w0,w3,w1,wa3,w2,w4],[]),([5,w0,w3,w1,4241289216,w2,w4],[(192,2)]),([5,w0,w3,w1,w59,w2,w4],[]),([5,w0,w3,w1,w59,w2,w33],[(108,2)]),([5,w0,w3,w1,w8a,w2,w4],[(116,1)]),([5,w0,w3,w1,w12,w2,w4],[]),([5,w0,w3,w1,w12,w2,we],[]),([5,w0,w3,w1,w12,w2,w3d],[(204,3)]),([5,w0,w3,w1,w47,w2,w4],[]),([5,w0,w3,w1,w50,w2,w4],[]),([5,w0,w3,w1,w50,w2,w20],[(116,1)])]
noncomputable def K_24 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w3,w1,w6d,w2,w4],[(116,1)]),([5,w0,w3,w1,4244438016,w2,w4],[(192,3)]),([5,w0,w3,w1,4244438220,w2,w4],[(116,1)]),([5,w0,w3,w1,w6,w48,w2],[]),([5,w0,w3,w1,w6,w2,w46],[(156,3)]),([5,w0,w3,w1,w6,w2,w4],[]),([5,w0,w3,w1,w6,w2,w16],[]),([5,w0,w3,w1,w6,w2,w13],[]),([5,w0,w3,w1,w6,w2,w6e],[(108,0),(116,0)]),([5,w0,w3,w1,w6,w2,4294966272],[(108,3),(116,3)]),([5,w0,w3,w1,4244439039,w2,w4],[]),([5,w0,w3,w1,4244634879,w2,w4],[]),([5,w0,w3,w1,4261281277,w2,w4],[]),([5,w0,w3,w1,4277075694,w2,w4],[(116,1),(156,3)]),([5,w0,w3,w1,wa4,w2,w4],[(156,3)]),([5,w0,w3,w1,w48,w3b,w2],[(204,3)]),([5,w0,w3,w1,w48,w2],[]),([5,w0,w3,w1,w48,w2,w4],[]),([5,w0,w3,w1,w61,w2,w4],[]),([5,w0,w3,w1,4278111436,w2,w4],[]),([5,w0,w3,w1,4278120174,w2,w4],[(116,1),(156,3)]),([5,w0,w3,w1,4278123772,w2,w4],[(156,3)]),([5,w0,w3,w1,w3b,w2,w4],[(156,3)]),([5,w0,w3,w1,w2,w46],[]),([5,w0,w3,w1,w2,w46,w2f],[]),([5,w0,w3,w1,w2,w46,w4],[]),([5,w0,w3,w1,w2,wa5,w4],[]),([5,w0,w3,w1,w2,4294769916,w4],[(156,3)]),([5,w0,w3,w1,w2,w2f,w4],[]),([5,w0,w3,w1,w2,4294901758,w4],[]),([5,w0,w3,w1,w2,w4],[]),([5,w0,w3,w1,w2,w4,w4],[]),([5,w0,w3,w1,w2,w4,w90],[]),([5,w0,w3,w1,w2,w4,w8d],[]),([5,w0,w3,w1,w2,w4,w79],[]),([5,w0,w3,w1,w2,w4,4294901964],[]),([5,w0,w3,w1,w2,w4,w43],[])]
noncomputable def K_25 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w3,w1,w2,w4,4294905855],[]),([5,w0,w3,w1,w2,w4,w77],[]),([5,w0,w3,w1,w2,w4,w16],[]),([5,w0,w3,w1,w2,w4,4294923775],[]),([5,w0,w3,w1,w2,w4,w3e],[]),([5,w0,w3,w1,w2,w4,w15],[]),([5,w0,w3,w1,w2,w4,w70],[]),([5,w0,w3,w1,w2,w4,w8],[]),([5,w0,w3,w1,w2,w4,4294945535],[]),([5,w0,w3,w1,w2,w4,w49],[]),([5,w0,w3,w1,w2,w4,w13],[]),([5,w0,w3,w1,w2,w4,4294953160],[]),([5,w0,w3,w1,w2,w4,w81],[]),([5,w0,w3,w1,w2,w4,we],[]),([5,w0,w3,w1,w2,w4,4294954239],[]),([5,w0,w3,w1,w2,w4,w9c],[]),([5,w0,w3,w1,w2,w4,w91],[(188,1),(196,3)]),([5,w0,w3,w1,w2,w4,4294962412],[(188,1),(196,3)]),([5,w0,w3,w1,w2,w4,w2b],[(188,1),(196,3)]),([5,w0,w3,w1,w2,w4,4294966476],[(188,1),(196,3)]),([5,w0,w3,w1,w2,w4,w3d],[(196,3)]),([5,w0,w3,w1,w2,w4,4294967038],[(196,3)]),([5,w0,w3,w1,w2,w4,4294967292],[]),([5,w0,w3,w1,w2,w4,w2c],[]),([5,w0,w3,w1,w2,w8d],[]),([5,w0,w3,w1,w2,w43,w24],[]),([5,w0,w3,w1,w2,w77],[]),([5,w0,w3,w1,w2,w16],[]),([5,w0,w3,w1,w2,w16,w16],[]),([5,w0,w3,w1,w2,w16,w8],[]),([5,w0,w3,w1,w2,w16,we],[]),([5,w0,w3,w1,w2,w16,w9c],[]),([5,w0,w3,w1,w2,w16,w2c],[]),([5,w0,w3,w1,w2,w3e],[]),([5,w0,w3,w1,w2,w15,w20],[]),([5,w0,w3,w1,w2,w8,w13],[])]
noncomputable def K_26 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w3,w1,w2,w49],[]),([5,w0,w3,w1,w2,w13],[]),([5,w0,w3,w1,w2,w13,w13],[]),([5,w0,w3,w1,w2,w13,we],[]),([5,w0,w3,w1,w2,w13,w91],[(188,1),(196,3)]),([5,w0,w3,w1,w2,w13,w24],[(180,0),(188,2),(156,3)]),([5,w0,w3,w1,w2,w13,4294967232],[(172,3),(188,1),(156,3)]),([5,w0,w3,w1,w2,w81],[]),([5,w0,w3,w1,w2,we,w20],[(148,1)]),([5,w0,w3,w1,w2,we,4294967280],[(172,2)]),([5,w0,w3,w1,4278255615,w4,w24],[]),([5,w0,w3,w1,w87,w4],[]),([5,w0,w3,w1,4279238415,w11,w4],[(116,2)]),([5,w0,w3,w1,4283826005,w18,w4],[(140,0),(148,2)]),([5,w0,w3,w1,w39,w4],[]),([5,w0,w3,w1,w26,w4],[]),([5,w0,w3,w1,w10,w11,w4],[(116,2)]),([5,w0,w3,w1,w10,w4,w24],[(172,3),(180,0)]),([5,w0,w3,w1,w5a,w27,w4],[(108,0)]),([5,w0,w3,w1,w18,w5c,w4],[(108,0),(116,2)]),([5,w0,w3,w1,w18,w83,w4],[(108,0),(116,2)]),([5,w1f,w3,w1,w2,w4,w8],[]),([5,w40,w3,w1,w2,w18,w4],[]),([5,w2e,w3,w22,w1,w2,w4],[]),([5,w5,w3,w22,w1,w2,w4],[]),([5,w3,w22,w1,w2,w4],[(86,1),(110,3)]),([5,w3,w1b,w1,w2,w18,w4],[]),([6,0,65535,w0,w3,w1,w2],[]),([6,0,65535,w0,w3,w1,w2,w4],[])]
noncomputable def K_27 : List (List ℕ × List (ℕ × ℕ)) := [([6,0,w9,w0,w3,w1,w2,w4],[]),([6,0,w9,w0,w3,w1,w4],[]),([6,0,wb,w0,w3,w1,w2,w4],[]),([6,0,wb,w3,w1,w2,w4],[]),([6,0,w0,w3,w1,w2,w4],[(97,1),(129,3)]),([6,255,w0,w3,w1,w2,w4],[(2,3),(97,1),(101,1),(129,3)]),([6,255,w0,w3,w1,w2,w4,w24],[]),([6,21845,w0,w3,w1,w2,w4],[(97,1),(101,1),(129,3),(133,3)]),([6,21845,w0,w3,w1,w2,w4,w8],[]),([6,43690,65535,w0,w3,w1,w2],[]),([6,43690,65535,w0,w3,w1,w2,w4],[]),([6,43690,w0,w3,w1,w2],[(10,2),(14,0)]),([6,43690,w0,w3,w1,w2,w4],[(97,1),(101,1),(129,3),(133,3)]),([6,52428,65535,w0,w3,w1,w2],[]),([6,52428,65535,w0,w3,w1,w2,w4],[])]
noncomputable def K_28 : List (List ℕ × List (ℕ × ℕ)) := [([6,52428,w0,w3,w1,w2,w4],[(2,2),(97,1),(129,3),(133,0)]),([6,65535,65535,w0,w3,w1,w2],[]),([6,65535,65535,w0,w3,w1,w2,w4],[]),([6,65535,w9,w0,w3,w1],[(14,1)]),([6,65535,w9,w0,w3,w1,w2],[]),([6,65535,w9,w0,w3,w1,w2,w4],[]),([6,65535,w9,w0,w3,w1,w4],[]),([6,65535,wb,w0,w3,w1,w2],[]),([6,65535,wb,w0,w3,w1,w2,w4],[]),([6,65535,wb,w3,w1,w2],[(10,2),(14,0)]),([6,65535,wb,w3,w1,w2,w4],[]),([6,65535,wa,w0,w3,w1,w2],[]),([6,65535,wa,w0,w3,w1,w2,w4],[]),([6,65535,w7,w0,w3,w1,w2],[(129,1),(133,1),(169,3),(173,3)])]
noncomputable def K_29 : List (List ℕ × List (ℕ × ℕ)) := [([6,65535,w7,w0,w3,w1,w2,w4],[]),([6,65535,w0,w0,w3,w1,w2],[]),([6,65535,w0,w0,w3,w1,w2,w4],[]),([6,65535,w0,w1f,w3,w1,w2],[]),([6,65535,w0,w1f,w3,w1,w2,w4],[]),([6,65535,w0,w5,w3,w1,w2],[]),([6,65535,w0,w5,w3,w1,w2,w4],[]),([6,65535,w0,wc,w3,w1,w2],[]),([6,65535,w0,wc,w3,w1,w2,w4],[]),([6,65535,w0,w3,w3,w1,w2],[]),([6,65535,w0,w3,w3,w1,w2,w4],[]),([6,65535,w0,w3,w52,w1,w2],[]),([6,65535,w0,w3,w52,w1,w2,w4],[]),([6,65535,w0,w3,wd,w1,w2],[(156,1),(196,3)]),([6,65535,w0,w3,wd,w1,w2,w4],[(156,1),(196,3)])]
noncomputable def K_30 : List (List ℕ × List (ℕ × ℕ)) := [([6,65535,w0,w3,w1,w6,w2],[]),([6,65535,w0,w3,w1,w6,w2,w4],[]),([6,65535,w0,w3,w1,w2],[(10,2),(14,0)]),([6,65535,w0,w3,w1,w2,w4],[(97,1),(101,1),(129,3),(133,3)]),([6,65535,w0,w3,w1,w2,w4,w4],[]),([6,65535,w0,w3,w1,w2,w4,w8],[]),([6,65535,w0,w3,w1,w2,w4,we],[(72,2)]),([6,65535,w0,w3,w1,w2,w4,w2c],[]),([6,65535,w0,w3,w1,w2,w8],[]),([6,65535,w0,w3,w1,w2,we],[]),([6,65535,w0,w3,w1,w2,w2c],[]),([6,w53,w0,w3,w1,w2,w11,w4],[(96,0)]),([6,w53,w0,w3,w1,w2,w4],[(2,2),(97,1),(129,3)]),([6,w54,w0,w3,w1,w2,w18,w4],[(72,4),(96,3),(216,3),(196,1)]),([6,w54,w0,w3,w1,w2,w4],[(2,3),(72,2),(74,1),(96,0),(97,1),(101,1),(129,3)]),([6,w3f,w9,w0,w3,w1,w2,w4],[])]
noncomputable def K_31 : List (List ℕ × List (ℕ × ℕ)) := [([6,w3f,w9,w0,w3,w1,w4],[]),([6,w3f,w0,w3,w1,w2,w4],[(2,3),(97,1),(101,1),(129,3)]),([6,w41,w9,w0,w3,w1,w2,w4],[]),([6,w41,w9,w0,w3,w1,w4],[]),([6,w41,w0,w3,w1,w2,w4],[(2,4),(97,1),(129,0)]),([6,w42,w9,w0,w3,w1,w2,w4],[]),([6,w42,w9,w0,w3,w1,w4],[]),([6,w42,w0,w3,w1,w2,w4],[(2,3),(97,1),(101,1),(129,3),(194,1)]),([6,w9,w9,w0,w3,w1,w2,w4],[]),([6,w9,w9,w0,w3,w1,w4],[]),([6,w9,w4b,w0,w3,w1,w2,w4],[]),([6,w9,w4b,w0,w3,w1,w4],[(2,0)]),([6,w9,w4b,w0,w3,w4],[(2,0)]),([6,w9,wb,w0,w3,w1,w2,w4],[])]
noncomputable def K_32 : List (List ℕ × List (ℕ × ℕ)) := [([6,w9,wb,w0,w3,w1,w4],[]),([6,w9,wb,w3,w1,w2,w4],[]),([6,w9,wb,w3,w1,w4],[(10,1)]),([6,w9,wa,w0,w3,w1,w2,w4],[]),([6,w9,wa,w0,w3,w1,w4],[]),([6,w9,w55,w0,w3,w1,w2,w4],[]),([6,w9,w55,w0,w3,w1,w4],[(2,3)]),([6,w9,w7,w0,w3,w1],[(14,1)]),([6,w9,w7,w0,w3,w1,w2],[(2,3),(129,1),(133,1)]),([6,w9,w7,w0,w3,w1,w2,w4],[]),([6,w9,w7,w0,w3,w1,w4],[]),([6,w9,w0,w0,w3,w1,w2,w4],[]),([6,w9,w0,w0,w3,w1,w4],[]),([6,w9,w0,w40,w3,w1,w2,w4],[])]
noncomputable def K_33 : List (List ℕ × List (ℕ × ℕ)) := [([6,w9,w0,w40,w3,w1,w4],[]),([6,w9,w0,w5,w3,w1,w2,w4],[]),([6,w9,w0,w5,w3,w1,w4],[]),([6,w9,w0,w5d,w3,w1,w2,w4],[]),([6,w9,w0,w5d,w3,w1,w4],[(2,0)]),([6,w9,w0,wc,w3,w1,w2,w4],[]),([6,w9,w0,wc,w3,w1,w4],[]),([6,w9,w0,w3,w3,w1,w2,w4],[]),([6,w9,w0,w3,w3,w1,w4],[]),([6,w9,w0,w3,w4d,w1,w2,w4],[]),([6,w9,w0,w3,w4d,w1,w4],[]),([6,w9,w0,w3,wd,w1,w2,w4],[(156,1)]),([6,w9,w0,w3,wd,w1,w4],[(156,1)]),([6,w9,w0,w3,w1,w6,w2,w4],[]),([6,w9,w0,w3,w1,w6,w4],[])]
noncomputable def K_34 : List (List ℕ × List (ℕ × ℕ)) := [([6,w9,w0,w3,w1,w4a,w2,w4],[]),([6,w9,w0,w3,w1,w4a,w4],[(2,3)]),([6,w9,w0,w3,w1,w2,w2,w4],[]),([6,w9,w0,w3,w1,w2,w18,w4],[(196,1)]),([6,w9,w0,w3,w1,w2,w27,w4],[(72,2)]),([6,w9,w0,w3,w1,w2,w4],[(2,3),(97,1),(101,1)]),([6,w9,w0,w3,w1,w2,w4,w4],[]),([6,w9,w0,w3,w1,w2,w4,w43],[]),([6,w9,w0,w3,w1,w2,w4,w8],[]),([6,w9,w0,w3,w1,w2,w4,we],[]),([6,w9,w0,w3,w1,w2,w4,w24],[]),([6,w9,w0,w3,w1,w2,w4,w2c],[]),([6,w9,w0,w3,w1,w18,w4],[(2,3),(156,1)]),([6,w9,w0,w3,w1,w27,w4],[(2,0)]),([6,w9,w0,w3,w1,w4],[(10,1)]),([6,w9,w0,w3,w1,w4,w4],[]),([6,w9,w0,w3,w1,w4,w43],[])]
noncomputable def K_35 : List (List ℕ × List (ℕ × ℕ)) := [([6,w9,w0,w3,w1,w4,w8],[]),([6,w9,w0,w3,w1,w4,we],[]),([6,w9,w0,w3,w1,w4,w24],[(2,3)]),([6,w9,w0,w3,w1,w4,w2c],[]),([6,w66,w0,w3,w1,w4a,w2,w4],[(172,3)]),([6,w66,w0,w3,w1,w2,w4],[(2,3),(97,1),(101,1),(133,3)]),([6,w56,w0,w3,w3c,w1,w2,w4],[(132,1),(172,3)]),([6,w56,w0,w3,w1,w2,w4],[(2,2),(101,1),(133,3)]),([6,w30,wb,w0,w3,w1,w2,w4],[]),([6,w30,wb,w3,w1,w2,w4],[]),([6,w30,w0,w3,w1,w2,w4],[(2,2),(97,1),(129,3),(133,0)]),([6,w17,wb,w0,w3,w1,w2,w4],[]),([6,w17,wb,w3,w1,w2,w4],[])]
noncomputable def K_36 : List (List ℕ × List (ℕ × ℕ)) := [([6,w17,w0,w3,w1,w2,w4],[(97,1),(101,1),(129,3),(133,3)]),([6,wb,wb,w0,w3,w1,w2,w4],[]),([6,wb,wb,w3,w1,w2,w4],[]),([6,wb,wa,w0,w3,w1,w2,w4],[]),([6,wb,wa,w3,w1,w2,w4],[]),([6,wb,w7,w0,w3,w1,w2],[(129,1),(133,1),(169,3),(173,3)]),([6,wb,w7,w0,w3,w1,w2,w4],[]),([6,wb,w7,w3,w1,w2],[(10,2),(14,0)]),([6,wb,w7,w3,w1,w2,w4],[]),([6,wb,w0,w0,w3,w1,w2,w4],[]),([6,wb,w0,w5,w3,w1,w2,w4],[(96,1)]),([6,wb,w0,wc,w3,w1,w2,w4],[]),([6,wb,w0,w3,w3,w1,w2,w4],[]),([6,wb,w0,w3,w44,w1,w2,w4],[]),([6,wb,w0,w3,wd,w1,w2,w4],[(72,2),(156,1),(196,3)]),([6,wb,w0,w3,w1,w6,w2,w4],[]),([6,wb,w0,w3,w1,w2,w4],[(97,1),(101,1),(129,3),(133,3)])]
noncomputable def K_37 : List (List ℕ × List (ℕ × ℕ)) := [([6,wb,w0,w3,w1,w2,w4,w4],[]),([6,wb,w0,w3,w1,w2,w4,w16],[]),([6,wb,w0,w3,w1,w2,w4,w8],[]),([6,wb,w0,w3,w1,w2,w4,we],[]),([6,wb,w0,w3,w1,w2,w4,w2c],[]),([6,wb,w0,w3,w1,w2,w16],[(97,1),(101,1),(129,3),(133,3)]),([6,wb,w5,w3,w1,w2,w4],[]),([6,wb,wc,w3,w1,w2,w4],[]),([6,wb,w3,w3,w1,w2,w4],[]),([6,wb,w3,w44,w1,w2,w4],[]),([6,wb,w3,wd,w1,w2,w4],[(116,1),(148,3)]),([6,wb,w3,w1,w6,w2,w4],[]),([6,wb,w3,w1,w2,w4],[(6,2),(10,0)]),([6,wb,w3,w1,w2,w4,w4],[])]
noncomputable def K_38 : List (List ℕ × List (ℕ × ℕ)) := [([6,wb,w3,w1,w2,w4,w16],[]),([6,wb,w3,w1,w2,w4,w8],[]),([6,wb,w3,w1,w2,w4,we],[]),([6,wb,w3,w1,w2,w4,w2c],[]),([6,wb,w3,w1,w2,w16],[(6,2),(10,0)]),([6,w3a,w7,w0,w3,w1,w2],[(129,1),(133,1),(169,3),(173,3)]),([6,w3a,w7,w0,w3,w1,w2,w4],[]),([6,w3a,w0,w3,w1,w2],[(10,2),(14,0)]),([6,w3a,w0,w3,w1,w2,w4],[(97,1),(101,1),(129,3),(133,3)]),([6,w57,w55,w0,w3,w1,w2,w4],[(172,3)]),([6,w57,w0,w3,w1,w2,w4],[(2,3),(97,1),(101,1),(133,3)]),([6,w31,wa,w0,w3,w1,w2,w4],[]),([6,w31,w0,w5,w3,w1,w2,w4],[]),([6,w31,w0,w3,w1,w2,w4],[(2,3),(97,1),(129,3)])]
noncomputable def K_39 : List (List ℕ × List (ℕ × ℕ)) := [([6,w25,wa,w0,w3,w1,w2,w4],[(128,0)]),([6,w25,w7,w0,w3,w1,w2],[(2,2),(128,0),(130,0),(129,1),(169,3),(173,0)]),([6,w25,w7,w0,w3,w1,w2,w4],[(128,0)]),([6,w25,w0,wc,w3,w1,w2,w4],[(128,0)]),([6,w25,w0,w3,w1,w2,w4],[(2,2),(96,0),(98,0),(97,1),(129,3),(133,0)]),([6,wa,wa,w0,w3,w1,w2,w4],[]),([6,wa,w7d,w0,w3,w1,w2,w4],[(72,1),(96,1),(128,1)]),([6,wa,w7,w0,w3,w1,w2],[(2,2),(129,1),(169,3),(173,0),(189,0),(197,0)]),([6,wa,w7,w0,w3,w1,w2,w4],[]),([6,wa,w0,w0,w3,w1,w2,w4],[]),([6,wa,w0,w5,w3,w1,w2,w4],[]),([6,wa,w0,w5,w1,w2,w4],[(96,1),(97,1)]),([6,wa,w0,wc,w3,w1,w2,w4],[]),([6,wa,w0,w3,w3,w1,w2,w4],[]),([6,wa,w0,w3,wd,w1,w2,w4],[(196,0)]),([6,wa,w0,w3,w3c,w1,w2,w4],[(56,2),(72,2),(96,2)]),([6,wa,w0,w3,w6a,w1,w2,w4],[(56,1),(72,1),(96,1)]),([6,wa,w0,w3,w1,w1,w2,w4],[(56,1),(72,1),(96,1)]),([6,wa,w0,w3,w1,w2a,w2,w4],[(56,1),(72,1),(128,1)])]
noncomputable def K_40 : List (List ℕ × List (ℕ × ℕ)) := [([6,wa,w0,w3,w1,w1c,w2,w4],[(56,1),(72,1),(128,1),(204,0)]),([6,wa,w0,w3,w1,w6,w2,w4],[]),([6,wa,w0,w3,w1,w2,w11,w4],[(56,2),(72,2),(96,0),(168,2)]),([6,wa,w0,w3,w1,w2,w4],[(2,2),(97,1),(129,3),(133,0),(149,0)]),([6,wa,w0,w3,w1,w2,w4,w4],[]),([6,wa,w0,w3,w1,w2,w4,w15],[]),([6,wa,w0,w3,w1,w2,w4,w8],[]),([6,wa,w0,w3,w1,w2,w4,we],[]),([6,wa,w0,w3,w1,w2,w4,w20],[(56,1),(72,1),(96,0),(216,1)]),([6,wa,w0,wd,w1,w2,w4],[(148,0),(150,0),(149,0)]),([6,wa,w3,wd,w1,w2,w4],[(6,2)]),([6,wa,wd,w1,w2,w4],[(2,2),(6,2),(110,0),(10,0)]),([6,w14,w0,w3,w1,w6,w2,w4],[]),([6,w14,w0,w3,w1,w2,w4],[(2,3),(97,1),(101,1),(129,3),(133,3),(141,3),(117,1)]),([6,w7,w7,w0,w3,w1,w2],[(129,1),(133,1),(169,3),(173,3)]),([6,w7,w7,w0,w3,w1,w2,w4],[])]
noncomputable def K_41 : List (List ℕ × List (ℕ × ℕ)) := [([6,w7,w0,w0,w3,w1,w2],[(137,1),(141,1),(177,3),(181,3)]),([6,w7,w0,w0,w3,w1,w2,w4],[]),([6,w7,w0,w5,w3,w1,w2],[(142,1),(10,3),(145,1),(185,3),(153,1)]),([6,w7,w0,w5,w3,w1,w2,w4],[]),([6,w7,w0,wc,w3,w1,w2],[(10,2),(145,1),(185,3),(189,0)]),([6,w7,w0,wc,w3,w1,w2,w4],[]),([6,w7,w0,w3,w3,w1,w2],[(10,2),(185,0),(189,0)]),([6,w7,w0,w3,w3,w1,w2,w4],[]),([6,w7,w0,w3,w1d,w1,w2],[(169,0),(145,2),(185,4),(14,2),(157,1),(193,0),(197,3)]),([6,w7,w0,w3,w1d,w1,w2,w4],[]),([6,w7,w0,w3,wd,w1,w2],[(14,2),(156,1),(158,1),(157,1),(193,0),(196,3),(198,3),(197,3)]),([6,w7,w0,w3,wd,w1,w2,w4],[(156,1),(196,3)]),([6,w7,w0,w3,w1,w6,w2],[(74,2),(98,0),(117,1),(158,1),(18,3),(205,3)]),([6,w7,w0,w3,w1,w6,w2,w4],[(72,2),(96,0)]),([6,w7,w0,w3,w1,w2],[(99,1),(103,1),(131,3),(135,3),(107,1),(111,1),(139,3),(143,3),(10,2),(11,2),(147,0),(151,0),(13,1),(14,0),(15,0),(155,2),(159,2),(17,3)])]
noncomputable def K_42 : List (List ℕ × List (ℕ × ℕ)) := [([6,w7,w0,w3,w1,w2,w4],[(97,1),(101,1),(129,3),(133,3),(194,1),(198,1),(202,3),(206,3)]),([6,w7,w0,w3,w1,w2,w4,w4],[]),([6,w7,w0,w3,w1,w2,w4,w8],[]),([6,w7,w0,w3,w1,w2,w4,we],[]),([6,w7,w0,w3,w1,w2,w8],[(194,1),(198,1),(202,3),(206,3)]),([6,w7,w0,w3,w1,w2,we],[(97,1),(129,3),(198,1),(202,0),(206,3),(22,2)]),([6,w7,w3,w1,w2,w4,w8],[]),([6,w7,w3,w1,w2,w8],[(6,2),(10,0)]),([6,w32,w0,w3,w1,w2,w4],[(2,2),(97,1),(101,1),(129,3),(133,3),(109,1),(141,3),(202,0)]),([6,w32,w0,w3,w1,w2,w4,we],[]),([6,w0,w0,w0,w3,w1,w2,w4],[]),([6,w0,w0,w5,w3,w1,w2,w4],[(132,1)]),([6,w0,w0,wc,w3,w1,w2,w4],[]),([6,w0,w0,w3,w3,w1,w2,w4],[]),([6,w0,w0,w3,wd,w1,w2,w4],[(156,1),(196,3)]),([6,w0,w0,w3,w1,w6,w2,w4],[])]
noncomputable def K_43 : List (List ℕ × List (ℕ × ℕ)) := [([6,w0,w0,w3,w1,w2,w4],[(97,1),(101,1),(129,3),(133,3)]),([6,w0,w0,w3,w1,w2,w4,w4],[]),([6,w0,w0,w3,w1,w2,w4,w8],[]),([6,w0,w0,w3,w1,w2,w4,we],[]),([6,w0,w1f,w3,w1,w2,w4],[(105,1),(109,1),(137,3),(141,3)]),([6,w0,w40,w3,w1,w2,w4],[(6,3),(105,1),(109,1),(141,3)]),([6,w0,w2e,w5,w3,w1,w2,w4],[]),([6,w0,w2e,w3,w1,w2,w4],[(102,1),(134,3),(105,1),(137,3)]),([6,w0,w37,w5,w3,w1,w2,w4],[]),([6,w0,w37,wc,w3,w1,w2,w4],[]),([6,w0,w37,w3,w1,w2,w4],[(6,3),(105,1),(137,3)]),([6,w0,w5,w5,w3,w1,w2,w4],[]),([6,w0,w5,w5d,w3,w1,w2,w4],[(104,0),(136,0),(176,0),(224,0),(152,0)]),([6,w0,w5,wc,w3,w1,w2,w4],[]),([6,w0,w5,w3,w3,w1,w2,w4],[]),([6,w0,w5,w3,w1b,w1,w2,w4],[(156,1)]),([6,w0,w5,w3,wd,w1,w2,w4],[(156,1)]),([6,w0,w5,w3,w1,w6,w2,w4],[(84,1),(144,1)])]
noncomputable def K_44 : List (List ℕ × List (ℕ × ℕ)) := [([6,w0,w5,w3,w1,w4a,w2,w4],[(80,3),(104,3),(136,3),(224,3),(144,1)]),([6,w0,w5,w3,w1,w2,w2,w4],[(80,3),(104,3),(136,3),(224,3)]),([6,w0,w5,w3,w1,w2,w18,w4],[(80,3),(104,3),(176,3),(224,3),(196,1)]),([6,w0,w5,w3,w1,w2,w5c,w4],[(80,3),(104,3),(176,3),(224,3)]),([6,w0,w5,w3,w1,w2,w27,w4],[(80,0),(104,0),(176,0),(224,0)]),([6,w0,w5,w3,w1,w2,w4],[(102,1),(6,3),(105,1),(137,3),(113,1)]),([6,w0,w5,w3,w1,w2,w4,w4],[]),([6,w0,w5,w3,w1,w2,w4,w8],[(244,1)]),([6,w0,w5,w3,w1,w2,w4,w13],[]),([6,w0,w5,w3,w1,w2,w4,we],[]),([6,w0,w5,w3,w1,w2,w4,w24],[(80,3),(104,3),(224,3),(244,1)]),([6,w0,w5,w3,w1,w2,w13],[(102,1),(6,3),(105,1),(137,3),(113,1)]),([6,w0,w5,w3,w6,w2,w4],[(10,2),(149,0)]),([6,w0,w5,w6,w2,w4],[(103,3),(6,3),(7,3),(10,3),(11,3)]),([6,w0,wf,w3,w1,w1c,w2,w4],[(80,1),(136,1)]),([6,w0,wf,w3,w1,w2,w4],[(102,1),(6,4),(105,1),(137,3),(141,0),(10,2),(149,0)]),([6,w0,wf,w1,w1c,w2,w4],[(76,1),(78,1),(14,0),(157,4)])]
noncomputable def K_45 : List (List ℕ × List (ℕ × ℕ)) := [([6,w0,wf,w1,w2,w4],[(78,1),(79,1),(103,3),(6,4),(7,4),(111,0),(10,0),(11,0),(119,2)]),([6,w0,w29,w3,w1,w2,w11,w4],[(80,2),(176,2),(224,2),(156,2)]),([6,w0,w29,w3,w1,w2,w4],[(6,2),(105,1),(137,3),(141,0),(145,0)]),([6,w0,wc,wc,w3,w1,w2,w4],[]),([6,w0,wc,w3,w3,w1,w2,w4],[]),([6,w0,wc,w3,w45,w1,w2,w4],[]),([6,w0,wc,w3,wd,w1,w2,w4],[(156,1),(196,3)]),([6,w0,wc,w3,w6a,w1,w2,w4],[(80,1),(224,1)]),([6,w0,wc,w3,w1,w1,w2,w4],[(80,1),(104,1),(224,1)]),([6,w0,wc,w3,w1,w1c,w2,w4],[(80,1),(104,0),(136,1),(224,1),(204,4)]),([6,w0,wc,w3,w1,w6b,w2,w4],[(80,1),(136,1),(224,1)]),([6,w0,wc,w3,w1,w6,w2,w4],[]),([6,w0,wc,w3,w1,w2,w11,w4],[(80,2),(176,2),(224,2),(156,2)]),([6,w0,wc,w3,w1,w2,w4],[(6,2),(105,1),(137,3),(141,0)]),([6,w0,wc,w3,w1,w2,w4,w4],[]),([6,w0,wc,w3,w1,w2,w4,w8],[]),([6,w0,wc,w3,w1,w2,w4,we],[]),([6,w0,wc,w3,w1,w2,w4,w20],[(80,1),(176,1),(224,1)]),([6,w0,wc,w3,w1,w2,we],[(105,1),(137,3),(149,0)])]
noncomputable def K_46 : List (List ℕ × List (ℕ × ℕ)) := [([6,w0,wc,w1,w2,w4,we],[]),([6,w0,wc,w1,w2,we],[(6,2),(10,0),(18,2)]),([6,w0,w1a,w3,w1,w2,w4],[(6,2),(105,1),(137,3),(141,0),(149,0)]),([6,w0,w1a,w3,w1,w2,w4,w8],[]),([6,w0,w1e,w3,w1,w2,w4],[(6,4),(105,1),(137,3),(141,0),(149,0)]),([6,w0,w1e,w3,w1,w2,w4,w20],[(80,1),(176,1),(224,1)]),([6,w0,w3,w3,w3,w1,w2,w4],[]),([6,w0,w3,w3,wd,w1,w2,w4],[(156,1),(196,3)]),([6,w0,w3,w3,w1,w1,w2,w4],[(64,1),(68,1)]),([6,w0,w3,w3,w1,w1c,w2,w4],[(64,1),(68,1),(204,4)]),([6,w0,w3,w3,w1,w6,w2,w4],[]),([6,w0,w3,w3,w1,w2,w11,w4],[(64,2),(68,2),(156,2)]),([6,w0,w3,w3,w1,w2,w4],[(6,2),(137,0),(141,0)]),([6,w0,w3,w3,w1,w2,w4,w4],[]),([6,w0,w3,w3,w1,w2,w4,w8],[]),([6,w0,w3,w3,w1,w2,w4,we],[]),([6,w0,w3,w3,w1,w2,w4,w20],[(64,1),(68,1)])]
noncomputable def K_47 : List (List ℕ × List (ℕ × ℕ)) := [([6,w0,w3,w52,w1,w2,w4],[(177,2),(10,2),(117,1),(145,0),(149,3)]),([6,w0,w3,w4d,w1,w2,w4],[(137,2),(10,4),(117,1),(149,0)]),([6,w0,w3,w44,w1,w2,w4],[(58,2),(109,1),(141,3),(10,2),(117,1),(145,0),(149,3)]),([6,w0,w3,w1b,w1,w2,w4],[(100,1),(102,1),(10,3),(113,1),(116,1),(118,1),(117,1),(145,3),(148,3),(150,3),(149,3)]),([6,w0,w3,w28,w1,w2,w4],[(109,1),(137,2),(177,2),(10,4),(116,1),(118,1),(117,1),(145,0),(149,3)]),([6,w0,w3,w19,wd,w1,w2],[(14,2),(156,1),(158,1),(157,1),(193,0),(196,3),(198,3),(197,3)]),([6,w0,w3,w19,wd,w1,w2,w4],[(156,1),(196,3)]),([6,w0,w3,w19,w1,w2],[(103,1),(131,0),(135,3),(6,2),(7,2),(139,0),(143,0),(10,2),(11,2),(119,1),(147,0),(151,3),(13,1),(14,0),(15,0),(159,2),(17,3)]),([6,w0,w3,w19,w1,w2,w4],[(10,2),(113,1),(117,1),(145,3),(149,3),(198,1),(202,0),(206,3)]),([6,w0,w3,w45,w1,w2,w4],[(10,2),(113,1),(117,1),(145,3),(149,3)]),([6,w0,w3,w1d,w1,w2,w4],[(105,2),(137,4),(10,2),(117,1),(145,0),(149,3),(202,0)]),([6,w0,w3,wd,wd,w1,w2,w4],[(148,1),(188,3)]),([6,w0,w3,wd,w1,w1c,w2,w4],[(76,1),(84,1),(116,1),(188,3),(204,4),(252,1)]),([6,w0,w3,wd,w1,w6,w2,w4],[(116,1),(188,3)])]
noncomputable def K_48 : List (List ℕ × List (ℕ × ℕ)) := [([6,w0,w3,wd,w1,w3b,w2,w4],[(116,1),(188,3),(204,3)]),([6,w0,w3,wd,w1,w2,w11,w4],[(76,2),(84,2),(116,1),(148,3),(156,2)]),([6,w0,w3,wd,w1,w2,w4],[(10,2),(116,1),(118,1),(117,1),(145,0),(148,3),(150,3),(149,3)]),([6,w0,w3,wd,w1,w2,w4,w4],[(116,1),(148,3)]),([6,w0,w3,wd,w1,w2,w4,w8],[(116,1),(148,3)]),([6,w0,w3,wd,w1,w2,w4,we],[(116,1),(148,3)]),([6,w0,w3,wd,w1,w2,w4,w2b],[(116,1),(148,3),(244,1),(252,3)]),([6,w0,w3,wd,w1,w2,w4,w20],[(76,1),(84,1),(116,1),(148,3)]),([6,w0,w3,w1,w59,w2,w4],[(58,2),(85,1),(141,3),(118,1),(14,2),(153,0),(157,3)]),([6,w0,w3,w1,w12,w6,w2,w4],[]),([6,w0,w3,w1,w12,w2,w4],[(114,1),(118,1),(186,1),(14,3),(153,3),(157,3),(206,3)]),([6,w0,w3,w1,w50,w2,w4],[(58,2),(85,1),(141,3),(118,1),(14,4),(153,0),(157,3)]),([6,w0,w3,w1,w6,w6,w2,w4],[]),([6,w0,w3,w1,w6,w3b,w2,w4],[(204,3)]),([6,w0,w3,w1,w6,w2,w27,w4],[(108,0),(140,0),(116,0),(188,1),(156,3)]),([6,w0,w3,w1,w6,w2,w2f,w4],[(156,3)]),([6,w0,w3,w1,w6,w2,w4],[(85,1),(118,1),(14,3),(157,3)]),([6,w0,w3,w1,w6,w2,w4,w4],[])]
noncomputable def K_49 : List (List ℕ × List (ℕ × ℕ)) := [([6,w0,w3,w1,w6,w2,w4,w8],[]),([6,w0,w3,w1,w6,w2,w4,we],[(236,1)]),([6,w0,w3,w1,w6,w2,w4,w3d],[(252,3)]),([6,w0,w3,w1,w6,w2,w4,w24],[(108,3),(116,3),(192,3)]),([6,w0,w3,w1,w3b,w2,w4],[(118,1),(14,3),(156,3),(158,3),(157,3)]),([6,w0,w3,w1,w2,w2f,w4],[(150,1),(158,3)]),([6,w0,w3,w1,w2,w4],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(147,1),(151,1),(13,3),(155,3),(159,3)]),([6,w0,w3,w1,w2,w4,w4],[(146,1),(150,1),(154,3),(158,3)]),([6,w0,w3,w1,w2,w4,w4,w4],[]),([6,w0,w3,w1,w2,w4,w4,w8],[]),([6,w0,w3,w1,w2,w4,w4,we],[]),([6,w0,w3,w1,w2,w4,w43],[(186,1),(190,1),(198,3),(22,3)]),([6,w0,w3,w1,w2,w4,w16],[(146,1),(150,1),(186,1),(190,1),(154,3),(158,3),(194,3),(198,3)]),([6,w0,w3,w1,w2,w4,w15],[(186,1),(190,1),(154,0),(194,3),(198,3),(22,2)]),([6,w0,w3,w1,w2,w4,w8],[(186,1),(190,1),(194,3),(198,3)])]
noncomputable def K_50 : List (List ℕ × List (ℕ × ℕ)) := [([6,w0,w3,w1,w2,w4,w8,w8],[]),([6,w0,w3,w1,w2,w4,w8,we],[]),([6,w0,w3,w1,w2,w4,w8,w2b],[(236,1),(244,3)]),([6,w0,w3,w1,w2,w4,w13],[(146,1),(150,1),(186,1),(190,1),(158,3),(194,3),(198,3),(22,3)]),([6,w0,w3,w1,w2,w4,we],[(190,1),(154,0),(194,0),(198,3),(22,2)]),([6,w0,w3,w1,w2,w4,we,we],[]),([6,w0,w3,w1,w2,w4,we,w2b],[(236,1),(244,3)]),([6,w0,w3,w1,w2,w4,we,w20],[(180,1),(188,1),(204,1)]),([6,w0,w3,w1,w2,w4,we,w3d],[(188,1),(244,3)]),([6,w0,w3,w1,w2,w4,w2b],[(188,1),(190,1),(189,1),(194,0),(196,3),(198,3),(197,3),(22,2)]),([6,w0,w3,w1,w2,w4,w3d],[(190,1),(154,3),(196,3),(198,3),(197,3),(22,3)]),([6,w0,w3,w1,w2,w4,w2c],[(190,1),(198,3)]),([6,w0,w3,w1,w2,w16],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(147,1),(151,1),(13,3),(155,3),(159,3)]),([6,w0,w3,w1,w2,w13],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(147,1),(151,1),(13,3),(159,3),(18,3),(19,3)]),([6,w0,w3,w1,w2,we,w20],[(174,1),(148,1),(150,1),(149,1),(154,1),(205,1)])]
noncomputable def K_51 : List (List ℕ × List (ℕ × ℕ)) := [([7,65535,w0,w3,w1,w2],[(99,1),(103,1),(131,3),(135,3),(107,1),(111,1),(139,3),(143,3),(10,2),(11,2),(147,0),(151,0),(13,1),(14,0),(15,0),(155,2),(159,2),(17,3)]),([7,65535,w0,w3,w1,w2,w4],[(97,1),(99,1),(101,1),(103,1),(129,3),(131,3),(133,3),(135,3),(107,1),(111,1),(139,3),(143,3),(10,2),(11,2),(147,0),(151,0),(13,1),(14,0),(15,0),(155,2),(159,2),(194,1),(195,1),(198,1),(199,1),(17,3),(202,3),(203,3),(206,3),(207,3)]),([7,w9,w0,w3,w1,w2,w4],[(2,3),(97,1),(99,1),(101,1),(103,1),(107,1),(111,1),(10,2),(11,1),(13,1),(14,0),(154,1),(155,1),(158,1),(159,1),(195,1),(199,1)]),([7,w9,w0,w3,w1,w4],[(99,1),(103,1),(107,1),(111,1),(10,1),(11,1),(13,1),(155,1),(159,1)]),([7,wb,w0,w3,w1,w2,w4],[(97,1),(99,1),(101,1),(103,1),(129,3),(131,3),(133,3),(135,3),(105,1),(107,1),(109,1),(111,1),(137,3),(139,3),(141,3),(143,3),(10,2),(11,2),(147,0),(151,0),(13,1),(14,0),(15,0),(155,2),(159,2),(195,1),(199,1),(17,3),(203,3),(207,3)]),([7,wb,w3,w1,w2,w4],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(147,1),(151,1),(13,3),(155,3),(159,3)]),([7,wa,w0,w3,w1,w2,w4],[(2,2),(3,2),(97,1),(129,3),(131,0),(133,0),(135,0),(139,0),(143,0),(10,2),(11,2),(147,0),(149,0),(151,0),(14,0),(15,0),(17,0),(203,0),(207,0)]),([7,w7,w0,w3,w1,w2],[(99,1),(103,1),(131,3),(135,3),(107,1),(111,1),(139,3),(143,3),(10,2),(11,2),(147,0),(151,0),(13,1),(14,0),(15,0),(155,2),(159,2),(17,3)]),([7,w7,w0,w3,w1,w2,w4],[(97,1),(99,1),(101,1),(103,1),(129,3),(131,3),(133,3),(135,3),(107,1),(111,1),(139,3),(143,3),(10,2),(11,2),(147,0),(151,0),(13,1),(14,0),(15,0),(155,2),(159,2),(194,1),(195,1),(198,1),(199,1),(17,3),(202,3),(203,3),(206,3),(207,3)])]
noncomputable def K_52 : List (List ℕ × List (ℕ × ℕ)) := [([7,w0,w0,w3,w1,w2,w4],[(97,1),(99,1),(101,1),(103,1),(129,3),(131,3),(133,3),(135,3),(10,2),(11,2),(147,0),(151,0),(13,1),(14,0),(15,0),(155,2),(159,2),(195,1),(199,1),(17,3),(203,3),(207,3)]),([7,w0,w5,w3,w1,w2,w4],[(99,1),(102,1),(103,1),(135,3),(6,3),(7,3),(105,1),(107,1),(137,3),(10,2),(11,2),(113,1),(13,1),(14,0),(15,0),(155,1),(159,1),(195,1),(199,1)]),([7,w0,wc,w3,w1,w2,w4],[(103,1),(131,0),(135,3),(6,2),(7,2),(105,1),(137,3),(139,0),(141,0),(143,0),(10,2),(11,2),(147,0),(151,0),(14,0),(15,0),(159,2),(17,0),(203,0),(207,0)]),([7,w0,w3,w3,w1,w2,w4],[(103,1),(131,0),(135,3),(6,2),(7,2),(137,0),(139,0),(141,0),(143,0),(14,0),(15,0),(159,2),(199,1),(17,0),(203,0),(207,3)]),([7,w0,w3,wd,w1,w2,w4],[(103,1),(131,0),(135,3),(6,2),(7,2),(139,0),(143,0),(10,2),(11,2),(116,1),(118,1),(117,1),(119,1),(145,0),(147,0),(148,3),(150,3),(149,3),(151,3),(13,1),(14,0),(15,0),(159,2),(199,1),(17,3),(203,0),(207,3)]),([7,w0,w3,w1,w6,w2,w4],[(75,1),(79,1),(131,3),(135,3),(6,2),(7,2),(85,1),(143,0),(9,1),(10,0),(11,0),(118,1),(119,1),(147,1),(151,2),(187,1),(191,1),(14,3),(15,3),(157,3),(159,3),(17,3),(207,3)]),([7,w0,w3,w1,w2,w4],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(147,1),(151,1),(13,3),(155,3),(159,3)]),([7,w0,w3,w1,w2,w4,w4],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(146,1),(147,1),(150,1),(151,1),(13,3),(154,3),(155,3),(158,3),(159,3)])]
noncomputable def K_53 : List (List ℕ × List (ℕ × ℕ)) := [([7,w0,w3,w1,w2,w4,w8],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(147,1),(151,1),(186,1),(187,1),(190,1),(191,1),(13,3),(155,3),(159,3),(194,3),(195,3),(198,3),(199,3)]),([7,w0,w3,w1,w2,w4,we],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(151,1),(190,1),(191,1),(13,3),(154,0),(155,0),(159,3),(194,0),(195,0),(198,3),(199,3),(22,2),(23,2)]),([8,w0,w3,w1,w2,w4],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(147,1),(151,1),(13,3),(155,3),(159,3)])]
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_3 : K_3.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_4 : K_4.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_5 : K_5.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_6 : K_6.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_7 : K_7.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_8 : K_8.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_9 : K_9.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_10 : K_10.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_11 : K_11.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_12 : K_12.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_13 : K_13.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_14 : K_14.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_15 : K_15.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_16 : K_16.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_17 : K_17.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_18 : K_18.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_19 : K_19.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_20 : K_20.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_21 : K_21.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_22 : K_22.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_23 : K_23.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_24 : K_24.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_25 : K_25.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_26 : K_26.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_27 : K_27.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_28 : K_28.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_29 : K_29.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_30 : K_30.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_31 : K_31.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_32 : K_32.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_33 : K_33.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_34 : K_34.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_35 : K_35.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_36 : K_36.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_37 : K_37.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_38 : K_38.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_39 : K_39.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_40 : K_40.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_41 : K_41.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_42 : K_42.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_43 : K_43.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_44 : K_44.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_45 : K_45.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_46 : K_46.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_47 : K_47.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_48 : K_48.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_49 : K_49.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_50 : K_50.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_51 : K_51.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_52 : K_52.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_53 : K_53.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem hK_cert : T_cert.toList = (((((K_0 ++ (K_1 ++ K_2)) ++ (K_3 ++ (K_4 ++ K_5))) ++ ((K_6 ++ (K_7 ++ K_8)) ++ ((K_9 ++ K_10) ++ (K_11 ++ K_12)))) ++ (((K_13 ++ (K_14 ++ K_15)) ++ ((K_16 ++ K_17) ++ (K_18 ++ K_19))) ++ ((K_20 ++ (K_21 ++ K_22)) ++ ((K_23 ++ K_24) ++ (K_25 ++ K_26))))) ++ ((((K_27 ++ (K_28 ++ K_29)) ++ (K_30 ++ (K_31 ++ K_32))) ++ ((K_33 ++ (K_34 ++ K_35)) ++ ((K_36 ++ K_37) ++ (K_38 ++ K_39)))) ++ (((K_40 ++ (K_41 ++ K_42)) ++ ((K_43 ++ K_44) ++ (K_45 ++ K_46))) ++ ((K_47 ++ (K_48 ++ K_49)) ++ ((K_50 ++ K_51) ++ (K_52 ++ K_53)))))).map Prod.fst := by decide +kernel
set_option maxRecDepth 100000 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert ((all_app (all_app (all_app (all_app (all_app c_0 (all_app c_1 c_2)) (all_app c_3 (all_app c_4 c_5))) (all_app (all_app c_6 (all_app c_7 c_8)) (all_app (all_app c_9 c_10) (all_app c_11 c_12)))) (all_app (all_app (all_app c_13 (all_app c_14 c_15)) (all_app (all_app c_16 c_17) (all_app c_18 c_19))) (all_app (all_app c_20 (all_app c_21 c_22)) (all_app (all_app c_23 c_24) (all_app c_25 c_26))))) (all_app (all_app (all_app (all_app c_27 (all_app c_28 c_29)) (all_app c_30 (all_app c_31 c_32))) (all_app (all_app c_33 (all_app c_34 c_35)) (all_app (all_app c_36 c_37) (all_app c_38 c_39)))) (all_app (all_app (all_app c_40 (all_app c_41 c_42)) (all_app (all_app c_43 c_44) (all_app c_45 c_46))) (all_app (all_app c_47 (all_app c_48 c_49)) (all_app (all_app c_50 c_51) (all_app c_52 c_53)))))))

theorem lb : ∀ s : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xeaa8e880 (idx5 x)) s → 9 ≤ s :=
  lb_cert _ L_ M_ Y_ XS_ PD_ PM_ G_ T_cert 8 9 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨fun _ => false, fun _ => true, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) hT_cert (by decide +kernel)

set_option maxRecDepth 100000 in
theorem main : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xeaa8e880 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeaa8e880 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  simp only [sum_eq] at h ⊢
  exact ⟨⟨[⟨.and, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [9, 7]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [12, 11]⟩], 13⟩, by simp [PEqualNP.MetaComplexity.Monotone2], le_trans (by decide) (lb s h), by decide +kernel⟩

end Cert0
namespace Cert1


def L_ : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def M_ : ℕ := w2c
def Y_ : ℕ := w92
def XS_ : List ℕ := [w0,w3,w1,w2,w4]
def PD_ : List (ℕ × ℕ) := [(1,18093396),(2,17960962),(4,17171458),(8,1441858),(16,5184)]
def PM_ : List (ℕ × ℕ) := [(6,w92),(10,w92),(12,w92),(17,w92),(18,w92),(20,w92),(24,w92)]

def G_ : List (List ℕ) := [[0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,16,17,18,19,24,25,26,27,20,21,22,23,28,29,30,31],[0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15,16,17,20,21,18,19,22,23,24,25,28,29,26,27,30,31],[0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15,16,17,20,21,24,25,28,29,18,19,22,23,26,27,30,31],[0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15,16,17,24,25,18,19,26,27,20,21,28,29,22,23,30,31],[0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15,16,17,24,25,20,21,28,29,18,19,26,27,22,23,30,31]]


noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [2,w5,w61,w4e] BT.lf) [2,w3,w94,4294617770] BT.lf) [2,w3,w36,w7a] (BT.nd (BT.nd BT.lf [2,w1b,w12,w4e] BT.lf) [3,w14,w5,w61,w2] BT.lf)) [3,w14,w1b,w12,w2] (BT.nd (BT.nd (BT.nd BT.lf [3,w21,w5,w73,w4] BT.lf) [3,w21,w5,w12,w2] BT.lf) [3,w0,w5,w12,w4e] (BT.nd (BT.nd BT.lf [3,w0,w5,w47,w2] BT.lf) [3,w0,wf,w47,w2] BT.lf))) [3,w0,w1a,4042317984,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,w0,w1a,w6c,4278251008] BT.lf) [3,w0,w1a,w6c,w2] BT.lf) [3,w0,w3,w94,w4c] (BT.nd (BT.nd BT.lf [3,w0,w3,w36,w7a] BT.lf) [3,w0,wa3,w11,w33] BT.lf)) [3,w0,w59,w11,w49] (BT.nd (BT.nd (BT.nd BT.lf [3,w5,w1b,w47,w2] BT.lf) [3,w1a,w1b,w8b,w2] BT.lf) [3,w3,w1b,w47,w2] (BT.nd (BT.nd BT.lf [3,w3,w1,4272597674,4294770432] BT.lf) [3,w3,w1,w61,w4e] BT.lf)))) [3,w3,4205488810,w11,w33] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,w3,4205505194,w11,w4] BT.lf) [3,w3,w36,w7a] BT.lf) [3,w3,w36,w7a,w11] (BT.nd (BT.nd BT.lf [3,w3,w36,w7a,w4] BT.lf) [3,w3,w36,w7a,w8] BT.lf)) [3,w3,w36,4293982960,w8] (BT.nd (BT.nd (BT.nd BT.lf [3,w3,w36,w11,4294617770] BT.lf) [3,w3,w36,w11,4294945440] BT.lf) [3,w3,w36,w11,w8] (BT.nd (BT.nd BT.lf [3,w3,w34,4289374890,w24] BT.lf) [3,w3,w34,w18,w8] BT.lf))) [3,w3,4210621176,w18,w8] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,w3,w1c,w18,w7a] BT.lf) [3,w22,w59,w11,w4] BT.lf) [3,w1b,w6,w4e,w4] (BT.nd (BT.nd BT.lf [3,w28,w1c,w62,w8] BT.lf) [4,16776960,w0,w3,w1] BT.lf)) [4,178916010,w3,w1,w2,w8] (BT.nd (BT.nd (BT.nd BT.lf [4,178956970,w3,w1,w2,w4] BT.lf) [4,214748364,w0,w1,w2,w4] BT.lf) [4,w96,w0,w3,w3c,w4] (BT.nd (BT.nd BT.lf [4,w96,w0,w3,w4] BT.lf) [4,715795114,w3,w1,w2,w4] BT.lf))))) [4,1073676288,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,1077952576,w0,w6,w2,w4] BT.lf) [4,w9f,w0,w8e,w1,w2] BT.lf) [4,w30,w0,w1,w10,w4] (BT.nd (BT.nd BT.lf [4,1145848908,w0,w1,w2,w4] BT.lf) [4,w60,1357926640,w0,w2,w4] BT.lf)) [4,w60,w6f,w0,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [4,w60,w0,w1,w2,w4] BT.lf) [4,w60,w0,w1,w2,w63] BT.lf) [4,w60,w0,w1,w2,w8] (BT.nd (BT.nd BT.lf [4,w60,w0,w34,w2,w4] BT.lf) [4,1154272460,w0,w1,w2,w4] BT.lf))) [4,1288457420,w0,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,1414791168,w0,w3,w1,w2] BT.lf) [4,w17,w0,w5,w6,w2] BT.lf) [4,w17,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [4,w17,w0,w3,w1,w10] BT.lf) [4,1431677610,w0,w3,w1,w2] BT.lf)) [4,1431677610,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [4,1432289280,w0,w3,w1,w2] BT.lf) [4,1437226410,w3,w1,w4] BT.lf) [4,w6f,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [4,w6f,w0,w3,w34,w2] BT.lf) [4,1442775210,w0,w3,w1,w2] BT.lf)))) [4,1610547200,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,wa,w45,w1,w2,we] BT.lf) [4,wa,wd,w1,w2,w8] BT.lf) [4,wa,wd,w1,w10,w8] (BT.nd (BT.nd BT.lf [4,2576980377,w1,w2,w4] BT.lf) [4,w14,w0,w5,w12,w2] BT.lf)) [4,w14,w3,w1,w61,w2] (BT.nd (BT.nd (BT.nd BT.lf [4,w14,w3,w1c,w2,w8] BT.lf) [4,w14,w1b,w6,w2,w4] BT.lf) [4,w21,w5,w6,w2,w4] (BT.nd (BT.nd BT.lf [4,w21,w29,w1,w2,w4] BT.lf) [4,w21,w3,w1,w12,w2] BT.lf))) [4,w21,w3,w1,w2,w46] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w21,w3,w1,w2,w4] BT.lf) [4,w21,w3,w1,w2,4294945448] BT.lf) [4,w21,w3,w1,w2,w8] (BT.nd (BT.nd BT.lf [4,w21,w3,w1,w10,w4] BT.lf) [4,w21,w3,w1,w4e,w4] BT.lf)) [4,w21,w3,w1,w18,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,2863289685,w3,w1,w2] BT.lf) [4,2863311528,w3,w1,w2,w4] BT.lf) [4,w0,w2e,w59,w11,w4] (BT.nd BT.lf [4,w0,w37,w6,w2,w13] BT.lf)))))) [4,w0,3233857536,w6,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w5,w1a,w8b,w2] BT.lf) [4,w0,w5,w3,w47,w2] BT.lf) [4,w0,w5,w73,w2f,w4] (BT.nd (BT.nd BT.lf [4,w0,w5,4238933160,w2,w4] BT.lf) [4,w0,w5,w8a,w2,w4] BT.lf)) [4,w0,w5,w12,w6,w2] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w5,w12,w2,w2f] BT.lf) [4,w0,w5,w47,w6,w2] BT.lf) [4,w0,w5,w47,w2] (BT.nd (BT.nd BT.lf [4,w0,w5,w47,w2,w4] BT.lf) [4,w0,w5,w47,w2,w8] BT.lf))) [4,w0,w5,w6d,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w5,w6d,w2,w8] BT.lf) [4,w0,w5,w6,w98,w4] BT.lf) [4,w0,w5,w6,w48,w2] (BT.nd (BT.nd BT.lf [4,w0,w5,w6,w61,w2] BT.lf) [4,w0,w5,w6,w2,4290772992] BT.lf)) [4,w0,w5,w6,w2,w65] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w5,w6,w2,w46] BT.lf) [4,w0,w5,w6,w2,w4] BT.lf) [4,w0,w5,w6,w2,4294902531] (BT.nd (BT.nd BT.lf [4,w0,w5,w6,w2,w3e] BT.lf) [4,w0,w5,w6,w2,w15] BT.lf)))) [4,w0,w5,w6,w2,w70] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w5,w6,w2,w63] BT.lf) [4,w0,w5,w6,w2,w8] BT.lf) [4,w0,w5,w6,w2,w49] (BT.nd (BT.nd BT.lf [4,w0,w5,w6,w39,w4] BT.lf) [4,w0,w5,w6,w10,w4] BT.lf)) [4,w0,w5,w6,w4e,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w5,w6,w64,w4] BT.lf) [4,w0,w5,wa4,w2,w4] BT.lf) [4,w0,w99,w6,w2,w4] (BT.nd (BT.nd BT.lf [4,w0,w99,w2,w4] BT.lf) [4,w0,3301754060,w1,w2,w4] BT.lf))) [4,w0,w80,w6,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w80,wa4,w2,w4] BT.lf) [4,w0,w67,w6,w2,w4] BT.lf) [4,w0,wf,w1,w12,w2] (BT.nd (BT.nd BT.lf [4,w0,wf,w1,w98,w4] BT.lf) [4,w0,wf,w1,w48,w2] BT.lf)) [4,w0,wf,w9b,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,wf,w12,w6,w2] BT.lf) [4,w0,wf,w6b,w2,w4] BT.lf) [4,w0,wf,w6,w2,w4] (BT.nd BT.lf [4,w0,wf,w6,w2,w8] BT.lf))))) [4,w0,wa2,w1,w2,wa5] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,3435184320,w6,w2,w4] BT.lf) [4,w0,w29,w1,w10,w4] BT.lf) [4,w0,3435710664,w1,w2,w4] (BT.nd (BT.nd BT.lf [4,w0,w35,w1,w2,w4c] BT.lf) [4,w0,w35,w1,w2,4294574080] BT.lf)) [4,w0,w35,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w35,w1,w2,w8] BT.lf) [4,w0,w35,w1,w10,w4] BT.lf) [4,w0,wc,w3,w6c,w2] (BT.nd (BT.nd BT.lf [4,w0,wc,w8e,w1,w2] BT.lf) [4,w0,wc,4042309824,w6,w2] BT.lf))) [4,w0,wc,w1,wa3,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,wc,w1,w50,w2] BT.lf) [4,w0,wc,w1,w6d,w2] BT.lf) [4,w0,wc,w1,w2,wa5] (BT.nd (BT.nd BT.lf [4,w0,wc,w1,w10,we] BT.lf) [4,w0,3435934515,w1,w2] BT.lf)) [4,w0,3435939020,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w1a,w3,w6c,w2] BT.lf) [4,w0,w1a,4042309824,w1,w2] BT.lf) [4,w0,w1a,w6c,w1,w2] (BT.nd (BT.nd BT.lf [4,w0,w1a,w6c,w2] BT.lf) [4,w0,w1a,w6c,w2,w4] BT.lf)))) [4,w0,w1a,w6c,w2,w8] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w1a,w6c,w2,w2b] BT.lf) [4,w0,w1a,w1,w50,w2] BT.lf) [4,w0,w1a,w1,w6d,w2] (BT.nd (BT.nd BT.lf [4,w0,w1a,w1,w2,w13] BT.lf) [4,w0,w1a,w1,w2,we] BT.lf)) [4,w0,w1a,w1,w2,w91] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w1a,w1,w2,w2b] BT.lf) [4,w0,w1e,w1,w10,w4] BT.lf) [4,w0,w1e,w2a,w2,w4] (BT.nd (BT.nd BT.lf [4,w0,3435970764,w1,w2,w4] BT.lf) [4,w0,w9d,w1,w2,w4] BT.lf))) [4,w0,w9d,w1,w2,w8] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w23,w1,w51,w2] BT.lf) [4,w0,w23,w1,w9a,w4] BT.lf) [4,w0,w23,w1,w9a,w8] (BT.nd (BT.nd BT.lf [4,w0,w23,w1,w2,w4] BT.lf) [4,w0,w23,w1,w2,w15] BT.lf)) [4,w0,w23,w1,w2,w8] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w23,w2a,w2,w4] BT.lf) [4,w0,3435973832,w1,w2,w4] BT.lf) [4,w0,3435973832,w1,w2,w8] (BT.nd BT.lf [4,w0,w3,3587506176,w1,w2] BT.lf))))))) [4,w0,w3,3705405440,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w78,w1,w2] BT.lf) [4,w0,w3,3722283144,w1,w2] BT.lf) [4,w0,w3,3724476416,w1,w2] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w8f,w2] BT.lf) [4,w0,w3,w1,4241270920,w2] BT.lf)) [4,w0,w3,w1,4243324928,w2] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w12,w2] BT.lf) [4,w0,w3,w1,w12,w10] BT.lf) [4,w0,w3,w1,w12,w97] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w12,w4e] BT.lf) [4,w0,w3,w1,4244408456,w2] BT.lf))) [4,w0,w3,w1,4244416512,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w47,w2] BT.lf) [4,w0,w3,w1,4244570112,w2] BT.lf) [4,w0,w3,w1,4261216256,w2] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,4277010432,w2] BT.lf) [4,w0,w3,w1,4277054122,w2] BT.lf)) [4,w0,w3,w1,4277927936,w2] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,4277971456,w2] BT.lf) [4,w0,w3,w1,w48,w2] BT.lf) [4,w0,w3,w1,w61,w2] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w2,w46] BT.lf) [4,w0,w3,w1,w2,4294748840] BT.lf)))) [4,w0,w3,w1,w2,4294836224] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w2,4294879914] BT.lf) [4,w0,w3,w1,w2,w4] BT.lf) [4,w0,w3,w1,w2,4294901763] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w2,4294901765] BT.lf) [4,w0,w3,w1,w2,4294901770] BT.lf)) [4,w0,w3,w1,w2,4294901772] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w2,w90] BT.lf) [4,w0,w3,w1,w2,4294901823] BT.lf) [4,w0,w3,w1,w2,4294901896] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w2,w79] BT.lf) [4,w0,w3,w1,w2,4294904490] BT.lf))) [4,w0,w3,w1,w2,4294934528] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w2,w3e] BT.lf) [4,w0,w3,w1,w2,4294936704] BT.lf) [4,w0,w3,w1,w2,w15] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w2,4294936746] BT.lf) [4,w0,w3,w1,w2,4294944904] BT.lf)) [4,w0,w3,w1,w2,w70] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w2,4294945448] BT.lf) [4,w0,w3,w1,w2,w8] BT.lf) [4,w0,w3,w1,w2,4294945455] (BT.nd BT.lf [4,w0,w3,w1,w2,w49] BT.lf))))) [4,w0,w3,w1,w2,4294951040] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w2,4294953096] BT.lf) [4,w0,w3,w1,w2,4294961834] BT.lf) [4,w0,w3,w1,4278255365,w4] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,4278255365,w8] BT.lf) [4,w0,w3,w1,4278255372,w4] BT.lf)) [4,w0,w3,w1,4278255496,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,4278320897,w4] BT.lf) [4,w0,w3,w1,4278779656,w4] BT.lf) [4,w0,w3,w1,4286643968,w4] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w39,w4] BT.lf) [4,w0,w3,w1,w39,w3e] BT.lf))) [4,w0,w3,w1,w39,w15] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w39,w8] BT.lf) [4,w0,w3,w1,w26,w65] BT.lf) [4,w0,w3,w1,w26,w4] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w26,w15] BT.lf) [4,w0,w3,w1,w26,w8] BT.lf)) [4,w0,w3,w1,4287168384,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w10,w65] BT.lf) [4,w0,w3,w1,w10,w4c] BT.lf) [4,w0,w3,w1,w10,4294443008] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w10,w4] BT.lf) [4,w0,w3,w1,w10,w3e] BT.lf)))) [4,w0,w3,w1,w10,4294936576] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w10,w15] BT.lf) [4,w0,w3,w1,w10,w7b] BT.lf) [4,w0,w3,w1,w10,w63] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w10,4294945416] BT.lf) [4,w0,w3,w1,w10,w8] BT.lf)) [4,w0,w3,w1,w97,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,4289265544,w4] BT.lf) [4,w0,w3,w1,w4e,w4] BT.lf) [4,w0,w3,w1,w4e,w70] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w4e,w8] BT.lf) [4,w0,w3,w1,w69,w83] BT.lf))) [4,w0,w3,w1,4289374890,w83] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w18,4291603080] BT.lf) [4,w0,w3,w1,4290772992,w64] BT.lf) [4,w0,w3,w1,w64,w65] (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w64,w4] BT.lf) [4,w0,w3,w1,w64,w8] BT.lf)) [4,w0,w3,w1,w64,w13] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,4290838400,w4] BT.lf) [4,w0,w3,w1,4290838400,w8] BT.lf) [4,w0,w3,w1,w5c,w49] (BT.nd BT.lf [4,w0,w3,w1,4291362560,w4] BT.lf)))))) [4,w0,w3,w1,4291362696,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w1,w65,4293984000] BT.lf) [4,w0,w3,4169726088,w11,w4] BT.lf) [4,w0,w3,4176541936,w10,w4] (BT.nd (BT.nd BT.lf [4,w0,w3,w88,w26,w4] BT.lf) [4,w0,w3,w88,w10,w4] BT.lf)) [4,w0,w3,w2a,w10,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w2a,w10,w15] BT.lf) [4,w0,w3,w2a,w10,w8] BT.lf) [4,w0,w3,w2a,w62,w4] (BT.nd (BT.nd BT.lf [4,w0,w3,w2a,w4e,w4] BT.lf) [4,w0,w3,w94,w11,w4] BT.lf))) [4,w0,w3,w7f,w11,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w36,w4c,w11] BT.lf) [4,w0,w3,w36,w11,w4] BT.lf) [4,w0,w3,w36,w11,w8] (BT.nd (BT.nd BT.lf [4,w0,w3,w34,w62,w4] BT.lf) [4,w0,w3,w34,w5a,w4] BT.lf)) [4,w0,w3,w34,w18,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,w0,w3,w34,w18,w63] BT.lf) [4,w0,w3,w34,w18,w8] BT.lf) [4,w0,w3,4210621176,w18,w4] (BT.nd (BT.nd BT.lf [4,w0,w3,4241289216,w11,w4] BT.lf) [4,w0,w3,4243648752,w83,w4] BT.lf)))) [4,w0,w28,w1c,w62,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311615,w3,w1,w2,w8] BT.lf) [4,2863329006,w3,w1,w2,w8] BT.lf) [4,w1f,w3,w1,w2,w8] (BT.nd (BT.nd BT.lf [4,2863377067,w3,w1,w2,w4] BT.lf) [4,w5,w22,w6,w2,w4] BT.lf)) [4,w5,w5e,w6,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,w5,w1b,w6,w2,w8] BT.lf) [4,wf,w45,w1,w2,w4] BT.lf) [4,wf,wd,w1,w2,w8] (BT.nd (BT.nd BT.lf [4,wc,w3,w1,4205488810,w2] BT.lf) [4,w1a,w1b,w1,w2,w8] BT.lf))) [4,w3,3937053354,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w3,w22,w1,w2,w4] BT.lf) [4,w3,w22,w1,w2,w8] BT.lf) [4,w3,w22,w1,w2,w49] (BT.nd (BT.nd BT.lf [4,w3,w22,w1,w2,4294961834] BT.lf) [4,w3,w22,w1,w5c,w4] BT.lf)) [4,w3,w5e,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [4,w3,w5e,w1,w2,w8] BT.lf) [4,w3,w5e,w1,w2,w13] BT.lf) [4,w3,w5e,w1,w64,w4] (BT.nd BT.lf [4,w3,w5e,w6b,w2,w4] BT.lf))))) [4,w3,3941264042,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w3,w1b,w1,w2,w8] BT.lf) [4,w3,w1b,w6,w2,w8] BT.lf) [4,w3,w28,w1c,w2,w8] (BT.nd (BT.nd BT.lf [4,w3,4008356522,w1,w2,w4c] BT.lf) [4,w3,4008356522,w1,w2,w4] BT.lf)) [4,w3,4008373994,w1,w2,w8] (BT.nd (BT.nd (BT.nd BT.lf [4,w3,w45,w1,4210731690,w2] BT.lf) [4,w3,w45,w1,w10,w4] BT.lf) [4,w3,wd,w1,w2,4294617770] (BT.nd (BT.nd BT.lf [4,w3,wd,w1,w10,w8] BT.lf) [4,w3,wd,w36,w11,w4] BT.lf))) [4,w3,w36,w11,w4,w8] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,w3,w36,w11,w8] BT.lf) [4,w3,w34,w18,w4,w8] BT.lf) [4,w3,w34,w18,w63] (BT.nd (BT.nd BT.lf [4,w3,w34,w18,w8] BT.lf) [4,w3,w1c,w18,w11,w8] BT.lf)) [4,w28,w1c,w62,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,0,w17,w0,w3,w1,w2] BT.lf) [5,0,w0,w3,w1,w2,w4] BT.lf) [5,0,w0,w3,w1,w2,w8] (BT.nd (BT.nd BT.lf [5,15,w0,w3,w1,w2,w4] BT.lf) [5,85,w0,w3,w1,w2,w4] BT.lf)))) [5,85,w0,w3,w1,w2,w8] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,170,w0,w3,w1,w2,w4] BT.lf) [5,204,w0,w3,w1,w2,w4] BT.lf) [5,255,w0,w3,w1,w4a] (BT.nd (BT.nd BT.lf [5,255,w0,w3,w1,w2,w4] BT.lf) [5,255,w0,w3,w1,w2,w8] BT.lf)) [5,4095,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,17476,w0,w3,w1,w2,w4] BT.lf) [5,17476,w0,w3,w1,w2,w8] BT.lf) [5,21845,w9,w0,w3,w1] (BT.nd (BT.nd BT.lf [5,21845,wb,w3,w1,w2] BT.lf) [5,21845,w7,w3,w1,w2] BT.lf))) [5,21845,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,21845,w0,w3,w1,w2,w4] BT.lf) [5,21845,w0,w3,w1,w2,w8] BT.lf) [5,21845,w1f,w3,w1,w2] (BT.nd (BT.nd BT.lf [5,21845,w1f,w3,w1,w2,w8] BT.lf) [5,22015,w0,w3,w1,w2] BT.lf)) [5,22015,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,22015,w0,w3,w1,w2,w63] BT.lf) [5,34952,w0,w3,w1,w2,w4] BT.lf) [5,43690,w7,w3,w1,w2,w4] (BT.nd BT.lf [5,43690,w0,w3,w1,w2,w4] BT.lf)))))))) [5,43690,w0,w3,w1,w2,w8] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,43690,w1f,w3,w1,w2] BT.lf) [5,43690,w1f,w3,w1,w2,w4] BT.lf) [5,49344,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,52428,w0,wc,w1,w2,w4] BT.lf) [5,52428,w0,w3,w1,w2,w4] BT.lf)) [5,52428,w0,w3,w1,w2,w8] (BT.nd (BT.nd (BT.nd BT.lf [5,52428,w0,w52,w1,w2] BT.lf) [5,52428,w0,w52,w1,w2,w4] BT.lf) [5,61166,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,64764,w0,w3,w1,w2] BT.lf) [5,64764,w0,w3,w1,w2,w4] BT.lf))) [5,65535,w9,w4b,w0,w3] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,65535,w9,wb,w3,w1] BT.lf) [5,65535,w9,w0,w3,w1] BT.lf) [5,65535,w17,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [5,65535,wb,w3,w1,w2] BT.lf) [5,65535,wa,wd,w1,w2] BT.lf)) [5,65535,w7,w3,w1,w2,w8] (BT.nd (BT.nd (BT.nd BT.lf [5,65535,w0,w5,w6,w2] BT.lf) [5,65535,w0,w5,w6,w2,w4] BT.lf) [5,65535,w0,wc,w1,w2,we] (BT.nd (BT.nd BT.lf [5,65535,w0,w3,w1,w12,w2] BT.lf) [5,65535,w0,w3,w1,w2] BT.lf)))) [5,65535,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,65535,w0,w3,w1,w2,w15] BT.lf) [5,65535,w0,w3,w1,w2,w8] BT.lf) [5,65535,w0,w3,w1,w10] (BT.nd (BT.nd BT.lf [5,65535,w0,w3,w1,w10,w4] BT.lf) [5,65535,w1f,w3,w1,w2,w8] BT.lf)) [5,196611,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,327685,w0,w3,w1,w2,w4] BT.lf) [5,655370,w0,w3,w1,w2,w4] BT.lf) [5,786444,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,983040,w0,w3,w1,w2,w4] BT.lf) [5,w53,w0,w3,w3c,w11,w4] BT.lf))) [5,w53,w0,w3,w3c,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w53,w0,w3,w1,w2,w4c] BT.lf) [5,w53,w0,w3,w1,w2,w4] BT.lf) [5,w53,w0,w3,w1,w2,w90] (BT.nd (BT.nd BT.lf [5,w53,w0,w3,w1,w2,w8] BT.lf) [5,983295,w0,w3,w1,w2,w4] BT.lf)) [5,1048575,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [5,1048575,w0,w3,w1,w2,w4c] BT.lf) [5,1048575,w0,w3,w1,w2,w4] BT.lf) [5,4128831,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,4456516,w0,w3,w1,w2,w4] BT.lf) [5,5570560,w0,w3,w1,w2,w4] BT.lf))))) [5,w54,w55,w3,w1,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w54,w0,w3,w1,w2,w4] BT.lf) [5,w54,w0,w3,w1,w2,w8] BT.lf) [5,5570815,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,5592405,w0,w3,w1,w2,w4] BT.lf) [5,5636095,w0,w3,w1,w2,w4] BT.lf)) [5,6226015,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,6226015,w0,w3,w1,w62,w4] BT.lf) [5,6226015,w0,w3,w1,w4] BT.lf) [5,8913032,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,11141120,w0,w3,w1,w2,w4] BT.lf) [5,w3f,w55,w3,w1,w2,w4] BT.lf))) [5,w3f,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w3f,w0,w3,w1,w2,w79] BT.lf) [5,w3f,w0,w3,w1,w2,w8] BT.lf) [5,w3f,w40,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w3f,w40,w3,w1,w4] BT.lf) [5,11184810,w0,w3,w1,w2,w4] BT.lf)) [5,12583104,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,13369344,w0,w3,w1,w2,w4] BT.lf) [5,w41,w0,w5d,w1,w2,w4] BT.lf) [5,w41,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w41,w0,w3,w1,w2,w8] BT.lf) [5,w41,w0,w4d,w1,w2,w4] BT.lf)))) [5,w41,w0,w4d,w1,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w41,w0,wd,w1,w2,w4] BT.lf) [5,13421772,w0,w3,w1,w2,w4] BT.lf) [5,15597806,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,16515324,w0,w3,w1,w2,w4] BT.lf) [5,w42,w0,w3,w1,w4a,w2] BT.lf)) [5,w42,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w42,w0,w3,w1,w2,w43] BT.lf) [5,w42,w0,w3,w1,w2,w8] BT.lf) [5,w42,w0,w3,w1,w43] (BT.nd (BT.nd BT.lf [5,16711850,w0,w3,w1,w2,w4] BT.lf) [5,16711850,w0,w3,w1,w2,w8] BT.lf))) [5,16711884,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w9,w4b,858993459,w0,w4] BT.lf) [5,w9,w4b,wb,w3,w4] BT.lf) [5,w9,w4b,w0,w3,w4] (BT.nd (BT.nd BT.lf [5,w9,w4b,w0,w3,w8] BT.lf) [5,w9,w17,wb,w3,w1] BT.lf)) [5,w9,w17,w0,w3,w1] (BT.nd (BT.nd (BT.nd BT.lf [5,w9,w17,w0,w3,w1,w2] BT.lf) [5,w9,wb,w3,w1,w4] BT.lf) [5,w9,wb,w3,w1,w8] (BT.nd BT.lf [5,w9,wa,wd,w1,w4] BT.lf)))))) [5,w9,w55,w3,w1,w18,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w9,w7,w3,w1,w8] BT.lf) [5,w9,w0,w1f,w3,w1] BT.lf) [5,w9,w0,w5,w6,w2,w4] (BT.nd (BT.nd BT.lf [5,w9,w0,w5,w6,w4] BT.lf) [5,w9,w0,w5d,w1,w27,w4] BT.lf)) [5,w9,w0,wc,w1,we] (BT.nd (BT.nd (BT.nd BT.lf [5,w9,w0,w3,w1,w12] BT.lf) [5,w9,w0,w3,w1,w12,w2] BT.lf) [5,w9,w0,w3,w1,w2,w65] (BT.nd (BT.nd BT.lf [5,w9,w0,w3,w1,w2,w4] BT.lf) [5,w9,w0,w3,w1,w2,w79] BT.lf))) [5,w9,w0,w3,w1,w2,w15] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w9,w0,w3,w1,w2,w63] BT.lf) [5,w9,w0,w3,w1,w2,w8] BT.lf) [5,w9,w0,w3,w1,w10,w4] (BT.nd (BT.nd BT.lf [5,w9,w0,w3,w1,w65] BT.lf) [5,w9,w0,w3,w1,w4] BT.lf)) [5,w9,w0,w3,w1,w79] (BT.nd (BT.nd (BT.nd BT.lf [5,w9,w0,w3,w1,w15] BT.lf) [5,w9,w0,w3,w1,w63] BT.lf) [5,w9,w0,w3,w1,w8] (BT.nd (BT.nd BT.lf [5,w9,w0,w3,w2a,w2,w4] BT.lf) [5,w9,w0,w3,w2a,w4] BT.lf)))) [5,w9,w0,w3,w34,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w9,w0,w3,w34,w4] BT.lf) [5,16715775,w0,w3,w1,w2,w4] BT.lf) [5,16733695,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,16733695,w0,w3,w1,w2,w8] BT.lf) [5,w66,w0,w3,w1,w2,w4] BT.lf)) [5,w66,w0,w3,w1,w2,w8] (BT.nd (BT.nd (BT.nd BT.lf [5,w66,w0,w3,w1,w24] BT.lf) [5,67044351,w0,w3,w1,w2,w4] BT.lf) [5,89458005,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w9e,w0,w3,w1,w2,w4] BT.lf) [5,178916010,w0,w3,w1,w2,w4] BT.lf))) [5,214699212,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w74,w0,w3,w1,w2,w4] BT.lf) [5,w56,w0,w3,w3c,w11,w4] BT.lf) [5,w56,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w56,w0,w3,w1,w2,w8] BT.lf) [5,w56,w0,w3,w11,w4] BT.lf)) [5,268435455,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,1073692671,w0,w3,w1,w2,w4] BT.lf) [5,1077952576,w0,w3,w1,w2,w4] BT.lf) [5,w9f,w17,w0,w3,w1,w2] (BT.nd BT.lf [5,w9f,w0,w3,w1,w2,w4] BT.lf))))) [5,w30,w17,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w30,wa,w0,w1,w2,w4] BT.lf) [5,w30,w0,w3,w1,w2,w4] BT.lf) [5,w30,w0,w3,w1,w2,w8] (BT.nd (BT.nd BT.lf [5,w30,w0,w44,w1,w2,w4] BT.lf) [5,w30,w0,w1,w6,w2,w4] BT.lf)) [5,w30,w44,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,1145359564,w0,w3,w1,w2,w4] BT.lf) [5,w60,w57,w0,w1,w2,w4] BT.lf) [5,w60,w55,w0,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w60,w0,w3,w1,w2,w4] BT.lf) [5,w60,w0,w1,w2,w4] BT.lf))) [5,1414812756,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w17,w17,w0,w3,w1,w2] BT.lf) [5,w17,wb,w0,w3,w1,w2] BT.lf) [5,w17,wb,w3,w1,w2] (BT.nd (BT.nd BT.lf [5,w17,w3a,w0,w3,w1,w2] BT.lf) [5,w17,wa,w0,w3,w1,w2] BT.lf)) [5,w17,w7,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [5,w17,w0,w0,w3,w1,w2] BT.lf) [5,w17,w0,w1f,w3,w1,w2] BT.lf) [5,w17,w0,w5,w3,w1,w2] (BT.nd (BT.nd BT.lf [5,w17,w0,wc,w3,w1,w2] BT.lf) [5,w17,w0,w3,w3,w1,w2] BT.lf)))) [5,w17,w0,w3,w8e,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w17,w0,w3,w44,w1,w2] BT.lf) [5,w17,w0,w3,wd,w1,w2] BT.lf) [5,w17,w0,w3,w1,w6,w2] (BT.nd (BT.nd BT.lf [5,w17,w0,w3,w1,w2] BT.lf) [5,w17,w0,w3,w1,w2,w4] BT.lf)) [5,w17,w0,w3,w1,w2,w16] (BT.nd (BT.nd (BT.nd BT.lf [5,w17,w0,w3,w1,w2,w8] BT.lf) [5,w17,w0,w3,w1,w2,we] BT.lf) [5,w17,w0,w3,w1,w2,w2c] (BT.nd (BT.nd BT.lf [5,w17,w3,w1,w2,w16] BT.lf) [5,w17,w3,w1,w2,w8] BT.lf))) [5,1431651396,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,wb,w0,w5,w6,w2,w4] BT.lf) [5,wb,w0,w3,w78,w1,w2] BT.lf) [5,wb,w0,w3,w1,w12,w2] (BT.nd (BT.nd BT.lf [5,wb,w0,w3,w1,w2,w4] BT.lf) [5,wb,w0,w3,w1,w2,w15] BT.lf)) [5,wb,w0,w3,w1,w2,w8] (BT.nd (BT.nd (BT.nd BT.lf [5,wb,w0,w3,w1,w10,w4] BT.lf) [5,wb,w1f,w3,w1,w2] BT.lf) [5,wb,w5,w6,w2,w4] (BT.nd BT.lf [5,wb,wc,w1,w2,we] BT.lf))))))) [5,wb,w3,w78,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,wb,w3,w1,w12,w2] BT.lf) [5,wb,w3,w1,w2,w4] BT.lf) [5,wb,w3,w1,w2,w15] (BT.nd (BT.nd BT.lf [5,wb,w3,w1,w2,w8] BT.lf) [5,wb,w3,w1,w10,w4] BT.lf)) [5,1431655935,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w3a,w0,w3,w1,w2,w4] BT.lf) [5,w3a,w0,w3,w1,w2,w8] BT.lf) [5,w3a,w3,w1,w2,w8] (BT.nd (BT.nd BT.lf [5,1432311135,w0,w3,w1,w2,w4] BT.lf) [5,w6f,w57,w0,w3,w1,w2] BT.lf))) [5,w6f,w55,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w6f,w0,w3,w1,w2] BT.lf) [5,w6f,w0,w3,w1,w2,w4] BT.lf) [5,w57,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w57,w0,w3,w1,w2,w63] BT.lf) [5,w57,w0,w3,w1,w2,w8] BT.lf)) [5,w57,w0,w3,w34,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w57,w3,w1,w18,w4] BT.lf) [5,1442840575,w0,w3,w1,w2,w4] BT.lf) [5,1610571775,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,2147516416,w0,w3,w1,w2,w4] BT.lf) [5,2155872256,w0,w3,w1,w2,w4] BT.lf)))) [5,w31,w0,w5,w6,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w31,w0,w3,w1,w2,w4] BT.lf) [5,w31,w0,w3,w1,w2,w3e] BT.lf) [5,w31,w0,w3,w1,w2,w15] (BT.nd (BT.nd BT.lf [5,w31,w0,w3,w1,w2,w8] BT.lf) [5,w31,w0,w3,w1,w39,w4] BT.lf)) [5,w31,w0,w3,w1,w10,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w31,w0,w3,w2a,w2,w4] BT.lf) [5,2290124928,w0,w3,w1,w2,w4] BT.lf) [5,w25,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w25,w0,w3,w1,w2,w15] BT.lf) [5,w25,w0,w3,w1,w2,w8] BT.lf))) [5,w25,w0,w3,w1,w26,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w25,w0,w3,w1,w10,w4] BT.lf) [5,2290647168,w0,w3,w1,w2,w4] BT.lf) [5,wa,2862656160,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,wa,w0,w5,w6,w2,w4] BT.lf) [5,wa,w0,w29,w1,w2,w4] BT.lf)) [5,wa,w0,wc,w1,w2,we] (BT.nd (BT.nd (BT.nd BT.lf [5,wa,w0,w1e,w1,w2,w4] BT.lf) [5,wa,w0,w3,w3c,w11,w4] BT.lf) [5,wa,w0,w3,w1,w12,w2] (BT.nd BT.lf [5,wa,w0,w3,w1,w2,w4c] BT.lf))))) [5,wa,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,wa,w0,w3,w1,w2,w3e] BT.lf) [5,wa,w0,w3,w1,w2,w15] BT.lf) [5,wa,w0,w3,w1,w2,w7b] (BT.nd (BT.nd BT.lf [5,wa,w0,w3,w1,w2,w8] BT.lf) [5,wa,w0,w3,w1,w39,w4] BT.lf)) [5,wa,w0,w3,w1,w26,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,wa,w0,w3,w1,w10,w4] BT.lf) [5,wa,w0,w3,w1,w10,w15] BT.lf) [5,wa,w0,w3,w1,w10,w8] (BT.nd (BT.nd BT.lf [5,wa,w0,w3,w1,w62,w4] BT.lf) [5,wa,w0,w3,w2a,w10,w4] BT.lf))) [5,wa,w0,w28,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,wa,w0,w1d,w1,w2,w4] BT.lf) [5,wa,w0,wd,w1,w2,w4] BT.lf) [5,wa,w0,wd,w1,w2,w15] (BT.nd (BT.nd BT.lf [5,wa,w0,wd,w1,w2,w8] BT.lf) [5,wa,w0,wd,w1,w10,w4] BT.lf)) [5,wa,w3,w45,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,wa,w3,wd,w1,w2,w8] BT.lf) [5,wa,wd,w1,w2,w4] BT.lf) [5,wa,wd,w1,w2,w4,w8] (BT.nd (BT.nd BT.lf [5,wa,wd,w1,w2,w15] BT.lf) [5,wa,wd,w1,w2,w8] BT.lf)))) [5,wa,wd,w1,w10,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290657962,w0,w3,w1,w2,w4] BT.lf) [5,2290666700,w0,w3,w1,w2,w4] BT.lf) [5,2290679807,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [5,2290679807,w0,w3,w1,w2,w4] BT.lf) [5,2292877482,w0,w3,w1,w2,w4] BT.lf)) [5,2295105740,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,2298448127,w0,w3,w1,w2,w4] BT.lf) [5,2298448127,w0,w3,w1,w4] BT.lf) [5,2827528328,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w86,w0,w3,w1,w12,w2] BT.lf) [5,w86,w0,w3,w1,w2,w4] BT.lf))) [5,2829617288,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w14,w0,w5,w6,w2,w4] BT.lf) [5,w14,w0,w3,w1,w12,w2] BT.lf) [5,w14,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w14,w0,w3,w1,w2,w70] BT.lf) [5,w14,w0,w3,w1,w2,w8] BT.lf)) [5,w14,w0,w3,w1,w4e,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w14,w0,w3,w2a,w2,w4] BT.lf) [5,w14,w0,w3,w1c,w2,w4] BT.lf) [5,w14,w3,w1c,w2,w4] (BT.nd BT.lf [5,w21,w0,w3,w1,w2,w4] BT.lf)))))) [5,w21,w3,w1,w6,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w21,w3,w1,w2,w2f,w4] BT.lf) [5,w21,w3,w1,w2,w4] BT.lf) [5,w7,w0,w5,w6,w2,w4] (BT.nd (BT.nd BT.lf [5,w7,w0,w3,w1,w12,w2] BT.lf) [5,w7,w0,w3,w1,w2,w4] BT.lf)) [5,w7,w0,w3,w1,w2,w15] (BT.nd (BT.nd (BT.nd BT.lf [5,w7,w0,w3,w1,w2,w8] BT.lf) [5,w7,w0,w3,w1,w26,w4] BT.lf) [5,w7,w0,w3,w1,w10,w4] (BT.nd (BT.nd BT.lf [5,w7,w3,w1,w2,w8] BT.lf) [5,2863268010,w0,w3,w1,w2,w4] BT.lf))) [5,w58,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w32,w0,w3,w1,w2,w4] BT.lf) [5,w32,w0,w3,w1,w2,w15] BT.lf) [5,w32,w0,w3,w1,w2,w8] (BT.nd (BT.nd BT.lf [5,w32,w3,w1,w2,w8] BT.lf) [5,w4f,w0,w3,w1,w2,w4] BT.lf)) [5,w0,w0,w5,w6,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w0,w3,w1,w12,w2] BT.lf) [5,w0,w0,w3,w1,w2,w4] BT.lf) [5,w0,w0,w3,w1,w2,w15] (BT.nd (BT.nd BT.lf [5,w0,w0,w3,w1,w2,w8] BT.lf) [5,w0,w0,w3,w1,w10,w4] BT.lf)))) [5,w0,2863311615,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,2863329006,w3,w1,w2,w4] BT.lf) [5,w0,w1f,w3,w1,w2] BT.lf) [5,w0,w1f,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w1f,w3,w1,w2,w8] BT.lf) [5,w0,2863639215,w3,w1,w2,w4] BT.lf)) [5,w0,2867768046,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w76,w3,w1,w2,w4] BT.lf) [5,w0,2868838655,w3,w1,w2,w4] BT.lf) [5,w0,2868882090,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w40,w3,w1,w2,w4] BT.lf) [5,w0,w40,w3,w1,w2,w8] BT.lf))) [5,w0,2868903935,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,2952769535,w3,w1,w2,w4] BT.lf) [5,w0,3221225472,w3,w1,w2,w4] BT.lf) [5,w0,w2e,w5,w6,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w2e,w3,w1,w2,w4] BT.lf) [5,w0,w2e,w3,w1,w2,w8] BT.lf)) [5,w0,w2e,w3,w1,w2,w49] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w2e,w3,w1,w5c,w4] BT.lf) [5,w0,w89,w3,w1,w2,w4] BT.lf) [5,w0,w37,w5,w6,w2,w4] (BT.nd BT.lf [5,w0,w37,w3,w1,w4a,w2] BT.lf))))) [5,w0,w37,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w37,w3,w1,w2,w8] BT.lf) [5,w0,w37,w3,w1,w2,w13] BT.lf) [5,w0,w37,w3,w1,w64,w4] (BT.nd (BT.nd BT.lf [5,w0,w37,w3,w6b,w2,w4] BT.lf) [5,w0,3233841280,w3,w1,w2,w4] BT.lf)) [5,w0,3233841280,w3,w1,w2,w8] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,3233857536,w3,w1,w2,w4] BT.lf) [5,w0,w5,w5,w6,w2,w4] BT.lf) [5,w0,w5,w5d,w1,w27,w4] (BT.nd (BT.nd BT.lf [5,w0,w5,w82,w1,w2,w4] BT.lf) [5,w0,w5,wc,w6,w2,w4] BT.lf))) [5,w0,w5,w1a,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w5,w1a,w1,w2,w8] BT.lf) [5,w0,w5,w3,w1,w12,w2] BT.lf) [5,w0,w5,w3,w1,w2,4290772992] (BT.nd (BT.nd BT.lf [5,w0,w5,w3,w1,w2,w65] BT.lf) [5,w0,w5,w3,w1,w2,w4] BT.lf)) [5,w0,w5,w3,w1,w2,w3e] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w5,w3,w1,w2,w15] BT.lf) [5,w0,w5,w3,w1,w2,w63] BT.lf) [5,w0,w5,w3,w1,w2,w8] (BT.nd (BT.nd BT.lf [5,w0,w5,w3,w1,w2,w49] BT.lf) [5,w0,w5,w3,w1,w39,w4] BT.lf)))) [5,w0,w5,w3,w1,w10,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w5,w3,w1,w64,w4] BT.lf) [5,w0,w5,w3,w2a,w2,w4] BT.lf) [5,w0,w5,w3,w34,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w5,w3,w9b,w2,w4] BT.lf) [5,w0,w5,w3,w12,w6,w2] BT.lf)) [5,w0,w5,w3,w6b,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w5,w3,w6,w2,w4] BT.lf) [5,w0,w5,w3,w6,w2,w8] BT.lf) [5,w0,w5,w1b,w6,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w5,wd,w6,w2,w4] BT.lf) [5,w0,w5,w73,w6,w2,w4] BT.lf))) [5,w0,w5,w12,w6,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w5,w12,w6,w2,w4] BT.lf) [5,w0,w5,w6,w6,w2,w4] BT.lf) [5,w0,w5,w6,w3b,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w5,w6,w4a,w2,w4] BT.lf) [5,w0,w5,w6,w2,w2,w4] BT.lf)) [5,w0,w5,w6,w2,w18,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w5,w6,w2,w5c,w4] BT.lf) [5,w0,w5,w6,w2,w27,w4] BT.lf) [5,w0,w5,w6,w2,w2f,w4] (BT.nd BT.lf [5,w0,w5,w6,w2,w4] BT.lf))))))))) [5,w0,w5,w6,w2,w4,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w5,w6,w2,w4,w8] BT.lf) [5,w0,w5,w6,w2,w4,w13] BT.lf) [5,w0,w5,w6,w2,w4,we] (BT.nd (BT.nd BT.lf [5,w0,w5,w6,w2,w4,w3d] BT.lf) [5,w0,w5,w6,w2,w4,w24] BT.lf)) [5,w0,w5,w6,w2,w8] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,3233860812,w3,w1,w2,w4] BT.lf) [5,w0,3233873919,w3,w1,w2,w4] BT.lf) [5,w0,3234644172,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,3237986559,w3,w1,w2,w4] BT.lf) [5,w0,3301229764,w3,w1,w2,w4] BT.lf))) [5,w0,w5f,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w80,w3,w1,w2,w4] BT.lf) [5,w0,w80,w3,w34,w2,w4] BT.lf) [5,w0,wa0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,3368585352,w3,w1,w2,w4] BT.lf) [5,w0,w67,w3,w1,w2,w4] BT.lf)) [5,w0,wf,wc,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,wf,w3,w1,w2,w4] BT.lf) [5,w0,wf,w3,w1,w2,w8] BT.lf) [5,w0,wf,w3,w2a,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,wf,w3,w6,w2,w4] BT.lf) [5,w0,wf,wd,w1,w2,w4] BT.lf)))) [5,w0,wf,w1,w6,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,wf,w1,w3b,w2,w4] BT.lf) [5,w0,wf,w1c,w6,w2,w4] BT.lf) [5,w0,wf,w6,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,wa2,w3,w1,w2,w4c] BT.lf) [5,w0,wa2,w3,w1,w2,w4] BT.lf)) [5,w0,3435184320,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w29,w3,w1,w2,w4c] BT.lf) [5,w0,w29,w3,w1,w2,w4] BT.lf) [5,w0,w29,w3,w1,w2,w8] (BT.nd (BT.nd BT.lf [5,w0,w29,w1,w6,w2,w4] BT.lf) [5,w0,w29,w1,w2,w2f,w4] BT.lf))) [5,w0,w35,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w35,w1,w1c,w2,w4] BT.lf) [5,w0,w35,w1,w2,w11,w4] BT.lf) [5,w0,w35,w1,w2,4294639610,w4] (BT.nd (BT.nd BT.lf [5,w0,w35,w1,w2,w4] BT.lf) [5,w0,wc,w3,w6a,w1,w2] BT.lf)) [5,w0,wc,w3,w6a,w6b,w2] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,wc,w3,w8b,w1,w2] BT.lf) [5,w0,wc,w3,4042309824,w1,w2] BT.lf) [5,w0,wc,w3,w1,w51,w2] (BT.nd (BT.nd BT.lf [5,w0,wc,w3,w1,4210731690,w2] BT.lf) [5,w0,wc,w3,w1,w12,w2] BT.lf))))) [5,w0,wc,w3,w1,w50,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,wc,w3,w1,w2,w4c] BT.lf) [5,w0,wc,w3,w1,w2,w4] BT.lf) [5,w0,wc,w3,w1,w2,w43] (BT.nd (BT.nd BT.lf [5,w0,wc,w3,w1,w2,w15] BT.lf) [5,w0,wc,w3,w1,w2,w7b] BT.lf)) [5,w0,wc,w3,w1,w2,w8] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,wc,w3,w1,w2,w13] BT.lf) [5,w0,wc,w3,w1,w2,we] BT.lf) [5,w0,wc,w3,w1,w2,w2b] (BT.nd (BT.nd BT.lf [5,w0,wc,w3,w1,w26,w4] BT.lf) [5,w0,wc,w3,w1,w10,w4] BT.lf))) [5,w0,wc,w3,w1,w62,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,wc,w3,w1,w64,w4] BT.lf) [5,w0,wc,w28,w1,w2,w4] BT.lf) [5,w0,wc,w1,w50,w2] (BT.nd (BT.nd BT.lf [5,w0,wc,w1,w50,w2,w4] BT.lf) [5,w0,wc,w1,w6,w2,we] BT.lf)) [5,w0,wc,w1,w2,we] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,3435921612,w3,w1,w2,w4] BT.lf) [5,w0,w8c,w3,w1,w2,w4] BT.lf) [5,w0,3435954304,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,3435954304,w3,w1,w2,w7b] BT.lf) [5,w0,w1a,w3,w8b,w1,w2] BT.lf)))) [5,w0,w1a,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w1a,w3,w1,w2,w15] BT.lf) [5,w0,w1a,w3,w1,w2,w8] BT.lf) [5,w0,w1a,w3,w1,w2,we] (BT.nd (BT.nd BT.lf [5,w0,w1a,w3,w1,w2,w2b] BT.lf) [5,w0,w1a,wd,w1,w2,w4] BT.lf)) [5,w0,w1a,wd,w1,w2,w8] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w1a,w1,w2,w4,we] BT.lf) [5,w0,w1a,w1,w2,w4,w2b] BT.lf) [5,w0,w1a,w1,w2,w8,we] (BT.nd (BT.nd BT.lf [5,w0,w1a,w1,w2,w8,w2b] BT.lf) [5,w0,w1a,w1,w2,we] BT.lf))) [5,w0,w1a,w1,w2,w2b] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w7e,w3,w1,w2,w4] BT.lf) [5,w0,w1e,w3,w1,w2,w4] BT.lf) [5,w0,w1e,w3,w1,w2,w8] (BT.nd (BT.nd BT.lf [5,w0,w1e,w1,w6,w2,w4] BT.lf) [5,w0,w1e,w1,w2,w27,w4] BT.lf)) [5,w0,w23,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w23,w3,w1,w2,w8] BT.lf) [5,w0,w23,w1,w1c,w2,w4] BT.lf) [5,w0,w23,w1,w2,w4] (BT.nd BT.lf [5,w0,w23,w1,w2,w4,w8] BT.lf)))))) [5,w0,w23,w1,w2,w4,w20] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w23,w1,w2,w4,wa1] BT.lf) [5,w0,w23,w1,w2,w8] BT.lf) [5,w0,w23,w1,w2,w8,wa1] (BT.nd (BT.nd BT.lf [5,w0,w5b,w3,w1,w2,w4] BT.lf) [5,w0,w3,w3,w1,w12,w2] BT.lf)) [5,w0,w3,w3,w1,w2,w4c] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w3,w1,w2,w4] BT.lf) [5,w0,w3,w3,w1,w2,w15] BT.lf) [5,w0,w3,w3,w1,w2,w7b] (BT.nd (BT.nd BT.lf [5,w0,w3,w3,w1,w2,w8] BT.lf) [5,w0,w3,w3,w1,w10,w4] BT.lf))) [5,w0,w3,w3,w1,w62,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,3435973887,w1,w2,w4] BT.lf) [5,w0,w3,3435978205,w1,w2,w4] BT.lf) [5,w0,w3,3435978205,w1,w2,w8] (BT.nd (BT.nd BT.lf [5,w0,w3,3435982574,w1,w2,w4] BT.lf) [5,w0,w3,3435986172,w1,w2,w4] BT.lf)) [5,w0,w3,w52,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w52,w1,w2,w8] BT.lf) [5,w0,w3,3436170447,w1,w2,w4] BT.lf) [5,w0,w3,3437087965,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,3438202094,w1,w2,w4] BT.lf) [5,w0,w3,3439119612,w1,w2,w4] BT.lf)))) [5,w0,w3,3439263744,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,3439263999,w1,w2,w4] BT.lf) [5,w0,w3,3439316172,w1,w2,w4] BT.lf) [5,w0,w3,w4d,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,w4d,w1,w2,w8] BT.lf) [5,w0,w3,3439329279,w1,w2,w4] BT.lf)) [5,w0,w3,3489648639,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,3587560917,w1,w2,w4] BT.lf) [5,w0,w3,3705461980,w1,w2,w4] BT.lf) [5,w0,w3,w78,w44,w1,w2] (BT.nd (BT.nd BT.lf [5,w0,w3,w78,w1,w2] BT.lf) [5,w0,w3,w78,w1,w2,w4] BT.lf))) [5,w0,w3,3722270037,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w8e,w1,w2,w4] BT.lf) [5,w0,w3,w44,w1,w2,w4] BT.lf) [5,w0,w3,w44,w1,w2,w8] (BT.nd (BT.nd BT.lf [5,w0,w3,3722313727,w1,w2,w4] BT.lf) [5,w0,w3,3724533247,w1,w2,w4] BT.lf)) [5,w0,w3,w22,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,3938511552,w1,w2,w4] BT.lf) [5,w0,w3,w68,w1,w2,w4] BT.lf) [5,w0,w3,w5e,w1,w2,w4] (BT.nd BT.lf [5,w0,w3,w38,w1,w2,w4] BT.lf))))) [5,w0,w3,w1b,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1b,w1,w2,w8] BT.lf) [5,w0,w3,w1b,w6,w2,w4] BT.lf) [5,w0,w3,3972852940,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,3974889472,w1,w2,w4] BT.lf) [5,w0,w3,3974930592,w1,w2,w4] BT.lf)) [5,w0,w3,w85,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w28,w1,w2,w4] BT.lf) [5,w0,w3,w28,w1,w2,w7b] BT.lf) [5,w0,w3,w28,w1,w2,w8] (BT.nd (BT.nd BT.lf [5,w0,w3,w28,w1,w62,w4] BT.lf) [5,w0,w3,w28,w1c,w2,w4] BT.lf))) [5,w0,w3,4007718624,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,4008373994,w1,w2,w4] BT.lf) [5,w0,w3,4008505068,w1,w2,w4] BT.lf) [5,w0,w3,w19,w1,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,w19,w1,w2,w8] BT.lf) [5,w0,w3,w19,w1,w2,we] BT.lf)) [5,w0,w3,w19,w1,w2,w2b] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w45,w1,w2,w4] BT.lf) [5,w0,w3,w45,w1,w2,w8] BT.lf) [5,w0,w3,w45,w1,w2,we] (BT.nd (BT.nd BT.lf [5,w0,w3,w1d,w1,w2,w4] BT.lf) [5,w0,w3,w1d,w1,w2,w8] BT.lf)))) [5,w0,w3,4008632544,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,4008635114,w1,w2,w4] BT.lf) [5,w0,w3,4008635628,w1,w2,w4] BT.lf) [5,w0,w3,wd,w1,w12,w2] (BT.nd (BT.nd BT.lf [5,w0,w3,wd,w1,w48,w2] BT.lf) [5,w0,w3,wd,w1,w2,w4c] BT.lf)) [5,w0,w3,wd,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,wd,w1,w2,w15] BT.lf) [5,w0,w3,wd,w1,w2,w7b] BT.lf) [5,w0,w3,wd,w1,w2,w8] (BT.nd (BT.nd BT.lf [5,w0,w3,wd,w1,w10,w4] BT.lf) [5,w0,w3,wd,w1,w62,w4] BT.lf))) [5,w0,w3,4008640511,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,4009750271,w1,w2,w4] BT.lf) [5,w0,w3,w1,w8f,w59,w2] BT.lf) [5,w0,w3,w1,w8f,w2] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w8f,w2,w4] BT.lf) [5,w0,w3,w1,wa3,w2,w4] BT.lf)) [5,w0,w3,w1,4241289216,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w59,w2,w4] BT.lf) [5,w0,w3,w1,w59,w2,w8] BT.lf) [5,w0,w3,w1,w8a,w2,w4] (BT.nd BT.lf [5,w0,w3,w1,w12,w12,w2] BT.lf))))))) [5,w0,w3,w1,w12,w50,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w12,w6,w2] BT.lf) [5,w0,w3,w1,w12,w61,w2] BT.lf) [5,w0,w3,w1,w12,w3b,w2] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w12,w2] BT.lf) [5,w0,w3,w1,w12,w2,w27] BT.lf)) [5,w0,w3,w1,w12,w2,4294770432] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w12,w2,w2f] BT.lf) [5,w0,w3,w1,w12,w2,w4] BT.lf) [5,w0,w3,w1,w12,w2,w8] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w12,w2,we] BT.lf) [5,w0,w3,w1,w12,w2,w3d] BT.lf))) [5,w0,w3,w1,w12,w2,w24] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w47,w6,w2] BT.lf) [5,w0,w3,w1,w47,w2] BT.lf) [5,w0,w3,w1,w47,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w47,w2,w8] BT.lf) [5,w0,w3,w1,w50,w2,w4] BT.lf)) [5,w0,w3,w1,w50,w2,w8] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w6d,w2,w4] BT.lf) [5,w0,w3,w1,w6d,w2,w8] BT.lf) [5,w0,w3,w1,4244438016,w2,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,4244438220,w2,w4] BT.lf) [5,w0,w3,w1,w6,w48,w2] BT.lf)))) [5,w0,w3,w1,w6,w61,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w6,w2,w46] BT.lf) [5,w0,w3,w1,w6,w2,w4] BT.lf) [5,w0,w3,w1,w6,w2,4294902531] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w6,w2,w15] BT.lf) [5,w0,w3,w1,w6,w2,w70] BT.lf)) [5,w0,w3,w1,w6,w2,w63] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w6,w2,w8] BT.lf) [5,w0,w3,w1,w6,w10,w4] BT.lf) [5,w0,w3,w1,w6,w4e,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,4244439039,w2,w4] BT.lf) [5,w0,w3,w1,4244634879,w2,w4] BT.lf))) [5,w0,w3,w1,4261281277,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,4277075694,w2,w4] BT.lf) [5,w0,w3,w1,wa4,w2,w4] BT.lf) [5,w0,w3,w1,w48,w3b,w2] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w48,w2] BT.lf) [5,w0,w3,w1,w48,w2,w4] BT.lf)) [5,w0,w3,w1,w61,w2] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w61,w2,w4] BT.lf) [5,w0,w3,w1,4278111436,w2,w4] BT.lf) [5,w0,w3,w1,4278120174,w2,w4] (BT.nd BT.lf [5,w0,w3,w1,4278123772,w2,w4] BT.lf))))) [5,w0,w3,w1,w3b,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w3b,w2,w8] BT.lf) [5,w0,w3,w1,w2,w46] BT.lf) [5,w0,w3,w1,w2,w46,w2f] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w46,w4] BT.lf) [5,w0,w3,w1,w2,wa5,w4] BT.lf)) [5,w0,w3,w1,w2,4294769916,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w2f,w4] BT.lf) [5,w0,w3,w1,w2,w2f,w8] BT.lf) [5,w0,w3,w1,w2,4294901758,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4] BT.lf) [5,w0,w3,w1,w2,w4,w4] BT.lf))) [5,w0,w3,w1,w2,w4,w90] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,w8d] BT.lf) [5,w0,w3,w1,w2,w4,w79] BT.lf) [5,w0,w3,w1,w2,w4,4294901964] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,w43] BT.lf) [5,w0,w3,w1,w2,w4,4294905855] BT.lf)) [5,w0,w3,w1,w2,w4,w77] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,w16] BT.lf) [5,w0,w3,w1,w2,w4,4294923775] BT.lf) [5,w0,w3,w1,w2,w4,w3e] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,w15] BT.lf) [5,w0,w3,w1,w2,w4,w70] BT.lf)))) [5,w0,w3,w1,w2,w4,w8] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,4294945535] BT.lf) [5,w0,w3,w1,w2,w4,w49] BT.lf) [5,w0,w3,w1,w2,w4,w13] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,4294953160] BT.lf) [5,w0,w3,w1,w2,w4,w81] BT.lf)) [5,w0,w3,w1,w2,w4,we] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,4294954239] BT.lf) [5,w0,w3,w1,w2,w4,w9c] BT.lf) [5,w0,w3,w1,w2,w4,w91] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,4294962412] BT.lf) [5,w0,w3,w1,w2,w4,w2b] BT.lf))) [5,w0,w3,w1,w2,w4,4294966476] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,w3d] BT.lf) [5,w0,w3,w1,w2,w4,4294967038] BT.lf) [5,w0,w3,w1,w2,w4,4294967292] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w4,w2c] BT.lf) [5,w0,w3,w1,w2,w90] BT.lf)) [5,w0,w3,w1,w2,w79] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w43,w8] BT.lf) [5,w0,w3,w1,w2,w43,w24] BT.lf) [5,w0,w3,w1,w2,w16,w8] (BT.nd BT.lf [5,w0,w3,w1,w2,w3e] BT.lf)))))) [5,w0,w3,w1,w2,w15] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w15,w15] BT.lf) [5,w0,w3,w1,w2,w15,w8] BT.lf) [5,w0,w3,w1,w2,w15,we] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w15,w20] BT.lf) [5,w0,w3,w1,w2,w15,4294965496] BT.lf)) [5,w0,w3,w1,w2,w70] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w8] BT.lf) [5,w0,w3,w1,w2,w8,w8] BT.lf) [5,w0,w3,w1,w2,w8,4294945535] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w8,w13] BT.lf) [5,w0,w3,w1,w2,w8,we] BT.lf))) [5,w0,w3,w1,w2,w8,w91] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w8,w2b] BT.lf) [5,w0,w3,w1,w2,w8,w3d] BT.lf) [5,w0,w3,w1,w2,w8,4294967038] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w2,w8,w2c] BT.lf) [5,w0,w3,w1,w2,w49] BT.lf)) [5,w0,w3,w1,w2,w13,w24] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,4278255615,w4,w24] BT.lf) [5,w0,w3,w1,4279238415,w11,w4] BT.lf) [5,w0,w3,w1,4283826005,w18,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w39,w4] BT.lf) [5,w0,w3,w1,4287102976,w10,w4] BT.lf)))) [5,w0,w3,w1,w26,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w10,w10,w4] BT.lf) [5,w0,w3,w1,w10,w18,w4] BT.lf) [5,w0,w3,w1,w10,w27,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w10,w11,w4] BT.lf) [5,w0,w3,w1,w10,4294508536,w4] BT.lf)) [5,w0,w3,w1,w10,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w10,w4,w4] BT.lf) [5,w0,w3,w1,w10,w4,w15] BT.lf) [5,w0,w3,w1,w10,w4,w8] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w10,w4,we] BT.lf) [5,w0,w3,w1,w10,w4,w20] BT.lf))) [5,w0,w3,w1,w10,w4,w24] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w10,w4,4294967176] BT.lf) [5,w0,w3,w1,w10,w15] BT.lf) [5,w0,w3,w1,w10,w8] (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w4e,w4] BT.lf) [5,w0,w3,w1,w5a,w27,w4] BT.lf)) [5,w0,w3,w1,w18,w5c,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w18,w65,w27] BT.lf) [5,w0,w3,w1,w18,w83,w4] BT.lf) [5,w0,w3,w1,w18,w27,w4] (BT.nd BT.lf [5,w0,w3,w1,w18,w27,w8] BT.lf))))) [5,w0,w3,w1,w18,w2f,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1,w64,w4] BT.lf) [5,w0,w3,w1,w5c,w4,w24] BT.lf) [5,w0,w3,w1,w83,w11,w4] (BT.nd (BT.nd BT.lf [5,w0,w3,w2a,w10,w4] BT.lf) [5,w0,w3,w36,w11,w4] BT.lf)) [5,w0,w3,w34,w18,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w0,w3,w1c,w18,w11,w4] BT.lf) [5,w1f,w3,w1,w2,w4,w8] BT.lf) [5,w1f,w3,w1,w2,w8] (BT.nd (BT.nd BT.lf [5,w40,w3,w1,w2,w18,w4] BT.lf) [5,w2e,w3,w22,w1,w2,w4] BT.lf))) [5,w37,w3,w5e,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,w5,w3,w22,w1,w2,w4] BT.lf) [5,w5,w3,w5e,w1,w2,w4] BT.lf) [5,w5,w3,w1b,w1,w2,w8] (BT.nd (BT.nd BT.lf [5,wc,w3,w5e,w1,w2,w4] BT.lf) [5,w3,w22,w1,w2,w4] BT.lf)) [5,w3,w5e,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [5,w3,w1b,w1,w2,w18,w4] BT.lf) [5,w3,w1b,w1,w2,w4,w8] BT.lf) [5,w3,w1b,w1,w2,w8] (BT.nd (BT.nd BT.lf [5,w3,w45,w1,w1c,w2,w4] BT.lf) [5,w3,wd,w1,w1c,w2,w8] BT.lf)))) [6,0,65535,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,0,65535,w0,w3,w1,w2,w4] BT.lf) [6,0,w9,w0,w3,w1,w2,w4] BT.lf) [6,0,w9,w0,w3,w1,w4] (BT.nd (BT.nd BT.lf [6,0,wb,w0,w3,w1,w2,w4] BT.lf) [6,0,wb,w3,w1,w2,w4] BT.lf)) [6,0,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,255,w0,w3,w1,w2,w4] BT.lf) [6,255,w0,w3,w1,w2,w4,w24] BT.lf) [6,21845,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [6,21845,w0,w3,w1,w2,w4] BT.lf) [6,21845,w0,w3,w1,w2,w4,w8] BT.lf))) [6,21845,w0,w3,w1,w2,w8] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,43690,65535,w0,w3,w1,w2] BT.lf) [6,43690,65535,w0,w3,w1,w2,w4] BT.lf) [6,43690,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,52428,65535,w0,w3,w1,w2] BT.lf) [6,52428,65535,w0,w3,w1,w2,w4] BT.lf)) [6,52428,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,65535,w0,w3,w1,w2] BT.lf) [6,65535,65535,w0,w3,w1,w2,w4] BT.lf) [6,65535,w9,w0,w3,w1] (BT.nd BT.lf [6,65535,w9,w0,w3,w1,w2] BT.lf)))))))) [6,65535,w9,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,w9,w0,w3,w1,w4] BT.lf) [6,65535,wb,w0,w3,w1,w2] BT.lf) [6,65535,wb,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,65535,wb,w3,w1,w2] BT.lf) [6,65535,wb,w3,w1,w2,w4] BT.lf)) [6,65535,wa,w0,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,wa,w0,w3,w1,w2,w4] BT.lf) [6,65535,w7,w0,w3,w1,w2] BT.lf) [6,65535,w7,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,65535,w0,w0,w3,w1,w2] BT.lf) [6,65535,w0,w0,w3,w1,w2,w4] BT.lf))) [6,65535,w0,w1f,w3,w1,w2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,w0,w1f,w3,w1,w2,w4] BT.lf) [6,65535,w0,w5,w3,w1,w2] BT.lf) [6,65535,w0,w5,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,65535,w0,wc,w3,w1,w2] BT.lf) [6,65535,w0,wc,w3,w1,w2,w4] BT.lf)) [6,65535,w0,w3,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,w0,w3,w3,w1,w2,w4] BT.lf) [6,65535,w0,w3,w52,w1,w2] BT.lf) [6,65535,w0,w3,w52,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,65535,w0,w3,wd,w1,w2] BT.lf) [6,65535,w0,w3,wd,w1,w2,w4] BT.lf)))) [6,65535,w0,w3,w1,w6,w2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,w0,w3,w1,w6,w2,w4] BT.lf) [6,65535,w0,w3,w1,w2] BT.lf) [6,65535,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,65535,w0,w3,w1,w2,w4,w4] BT.lf) [6,65535,w0,w3,w1,w2,w4,w8] BT.lf)) [6,65535,w0,w3,w1,w2,w4,we] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,w0,w3,w1,w2,w4,w2c] BT.lf) [6,65535,w0,w3,w1,w2,w8] BT.lf) [6,65535,w0,w3,w1,w2,we] (BT.nd (BT.nd BT.lf [6,65535,w0,w3,w1,w2,w2c] BT.lf) [6,w53,w0,w3,w1,w2,w11,w4] BT.lf))) [6,w53,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w54,w0,w3,w1,w2,w18,w4] BT.lf) [6,w54,w0,w3,w1,w2,w4] BT.lf) [6,w3f,w9,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w3f,w9,w0,w3,w1,w4] BT.lf) [6,w3f,w0,w3,w1,w2,w4] BT.lf)) [6,w41,w9,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w41,w9,w0,w3,w1,w4] BT.lf) [6,w41,w0,w3,w1,w2,w4] BT.lf) [6,w42,w9,w0,w3,w1,w2,w4] (BT.nd BT.lf [6,w42,w9,w0,w3,w1,w4] BT.lf))))) [6,w42,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w9,w9,w0,w3,w1,w2,w4] BT.lf) [6,w9,w9,w0,w3,w1,w4] BT.lf) [6,w9,w4b,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w9,w4b,w0,w3,w1,w4] BT.lf) [6,w9,w4b,w0,w3,w4] BT.lf)) [6,w9,wb,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w9,wb,w0,w3,w1,w4] BT.lf) [6,w9,wb,w3,w1,w2,w4] BT.lf) [6,w9,wb,w3,w1,w4] (BT.nd (BT.nd BT.lf [6,w9,wa,w0,w3,w1,w2,w4] BT.lf) [6,w9,wa,w0,w3,w1,w4] BT.lf))) [6,w9,w55,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w9,w55,w0,w3,w1,w4] BT.lf) [6,w9,w7,w0,w3,w1,w2,w4] BT.lf) [6,w9,w7,w0,w3,w1,w4] (BT.nd (BT.nd BT.lf [6,w9,w0,w0,w3,w1,w2,w4] BT.lf) [6,w9,w0,w0,w3,w1,w4] BT.lf)) [6,w9,w0,w40,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w9,w0,w40,w3,w1,w4] BT.lf) [6,w9,w0,w5,w3,w1,w2,w4] BT.lf) [6,w9,w0,w5,w3,w1,w4] (BT.nd (BT.nd BT.lf [6,w9,w0,w5d,w3,w1,w2,w4] BT.lf) [6,w9,w0,w5d,w3,w1,w4] BT.lf)))) [6,w9,w0,wc,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w9,w0,wc,w3,w1,w4] BT.lf) [6,w9,w0,w3,w3,w1,w2,w4] BT.lf) [6,w9,w0,w3,w3,w1,w4] (BT.nd (BT.nd BT.lf [6,w9,w0,w3,w4d,w1,w2,w4] BT.lf) [6,w9,w0,w3,w4d,w1,w4] BT.lf)) [6,w9,w0,w3,wd,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w9,w0,w3,wd,w1,w4] BT.lf) [6,w9,w0,w3,w1,w6,w2,w4] BT.lf) [6,w9,w0,w3,w1,w6,w4] (BT.nd (BT.nd BT.lf [6,w9,w0,w3,w1,w4a,w2,w4] BT.lf) [6,w9,w0,w3,w1,w4a,w4] BT.lf))) [6,w9,w0,w3,w1,w2,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w9,w0,w3,w1,w2,w18,w4] BT.lf) [6,w9,w0,w3,w1,w2,w27,w4] BT.lf) [6,w9,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w9,w0,w3,w1,w2,w4,w4] BT.lf) [6,w9,w0,w3,w1,w2,w4,w43] BT.lf)) [6,w9,w0,w3,w1,w2,w4,w8] (BT.nd (BT.nd (BT.nd BT.lf [6,w9,w0,w3,w1,w2,w4,we] BT.lf) [6,w9,w0,w3,w1,w2,w4,w24] BT.lf) [6,w9,w0,w3,w1,w2,w4,w2c] (BT.nd BT.lf [6,w9,w0,w3,w1,w2,w8] BT.lf)))))) [6,w9,w0,w3,w1,w18,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w9,w0,w3,w1,w27,w4] BT.lf) [6,w9,w0,w3,w1,w4] BT.lf) [6,w9,w0,w3,w1,w4,w4] (BT.nd (BT.nd BT.lf [6,w9,w0,w3,w1,w4,w43] BT.lf) [6,w9,w0,w3,w1,w4,w8] BT.lf)) [6,w9,w0,w3,w1,w4,we] (BT.nd (BT.nd (BT.nd BT.lf [6,w9,w0,w3,w1,w4,w24] BT.lf) [6,w9,w0,w3,w1,w4,w2c] BT.lf) [6,w9,w0,w3,w1,w8] (BT.nd (BT.nd BT.lf [6,w66,w0,w3,w1,w4a,w2,w4] BT.lf) [6,w66,w0,w3,w1,w2,w4] BT.lf))) [6,w56,w0,w3,w3c,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w56,w0,w3,w1,w2,w4] BT.lf) [6,w30,wb,w0,w3,w1,w2,w4] BT.lf) [6,w30,wb,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w30,w0,w3,w1,w2,w4] BT.lf) [6,w17,wb,w0,w3,w1,w2] BT.lf)) [6,w17,wb,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w17,wb,w3,w1,w2] BT.lf) [6,w17,wb,w3,w1,w2,w4] BT.lf) [6,w17,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [6,w17,w0,w3,w1,w2,w4] BT.lf) [6,wb,wb,w0,w3,w1,w2,w4] BT.lf)))) [6,wb,wb,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,wb,wa,w0,w3,w1,w2,w4] BT.lf) [6,wb,wa,w3,w1,w2,w4] BT.lf) [6,wb,w7,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,wb,w7,w3,w1,w2,w4] BT.lf) [6,wb,w0,w0,w3,w1,w2,w4] BT.lf)) [6,wb,w0,w5,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,wb,w0,wc,w3,w1,w2,w4] BT.lf) [6,wb,w0,w3,w3,w1,w2,w4] BT.lf) [6,wb,w0,w3,w44,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,wb,w0,w3,wd,w1,w2,w4] BT.lf) [6,wb,w0,w3,w1,w6,w2,w4] BT.lf))) [6,wb,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,wb,w0,w3,w1,w2,w4,w4] BT.lf) [6,wb,w0,w3,w1,w2,w4,w16] BT.lf) [6,wb,w0,w3,w1,w2,w4,w8] (BT.nd (BT.nd BT.lf [6,wb,w0,w3,w1,w2,w4,we] BT.lf) [6,wb,w0,w3,w1,w2,w4,w2c] BT.lf)) [6,wb,w0,w3,w1,w2,w8] (BT.nd (BT.nd (BT.nd BT.lf [6,wb,w5,w3,w1,w2,w4] BT.lf) [6,wb,wc,w3,w1,w2,w4] BT.lf) [6,wb,w3,w3,w1,w2,w4] (BT.nd BT.lf [6,wb,w3,w44,w1,w2,w4] BT.lf))))) [6,wb,w3,wd,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,wb,w3,w1,w6,w2,w4] BT.lf) [6,wb,w3,w1,w2,w4] BT.lf) [6,wb,w3,w1,w2,w4,w4] (BT.nd (BT.nd BT.lf [6,wb,w3,w1,w2,w4,w16] BT.lf) [6,wb,w3,w1,w2,w4,w8] BT.lf)) [6,wb,w3,w1,w2,w4,we] (BT.nd (BT.nd (BT.nd BT.lf [6,wb,w3,w1,w2,w4,w2c] BT.lf) [6,wb,w3,w1,w2,w8] BT.lf) [6,w3a,w7,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w3a,w0,w3,w1,w2,w4] BT.lf) [6,w57,w55,w0,w3,w1,w2,w4] BT.lf))) [6,w57,w0,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w31,wa,w0,w3,w1,w2,w4] BT.lf) [6,w31,w0,w5,w3,w1,w2,w4] BT.lf) [6,w31,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w25,wa,w0,w3,w1,w2,w4] BT.lf) [6,w25,w7,w0,w3,w1,w2,w4] BT.lf)) [6,w25,w0,wc,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w25,w0,w3,w1,w2,w4] BT.lf) [6,wa,wa,w0,w3,w1,w2,w4] BT.lf) [6,wa,w7d,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,wa,w7,w0,w3,w1,w2,w4] BT.lf) [6,wa,w0,w0,w3,w1,w2,w4] BT.lf)))) [6,wa,w0,w5,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,wa,w0,wc,w3,w1,w2,w4] BT.lf) [6,wa,w0,w3,w3,w1,w2,w4] BT.lf) [6,wa,w0,w3,wd,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,wa,w0,w3,w3c,w1,w2,w4] BT.lf) [6,wa,w0,w3,w6a,w1,w2,w4] BT.lf)) [6,wa,w0,w3,w1,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,wa,w0,w3,w1,w2a,w2,w4] BT.lf) [6,wa,w0,w3,w1,w1c,w2,w4] BT.lf) [6,wa,w0,w3,w1,w6,w2,w4] (BT.nd (BT.nd BT.lf [6,wa,w0,w3,w1,w2,w11,w4] BT.lf) [6,wa,w0,w3,w1,w2,w4] BT.lf))) [6,wa,w0,w3,w1,w2,w4,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,wa,w0,w3,w1,w2,w4,w15] BT.lf) [6,wa,w0,w3,w1,w2,w4,w8] BT.lf) [6,wa,w0,w3,w1,w2,w4,we] (BT.nd (BT.nd BT.lf [6,wa,w0,w3,w1,w2,w4,w20] BT.lf) [6,wa,w0,w3,w1,w2,w15] BT.lf)) [6,wa,w0,w3,w1,w2,w8] (BT.nd (BT.nd (BT.nd BT.lf [6,wa,w0,w3,w1,w10,w4] BT.lf) [6,wa,w0,wd,w1,w2,w4] BT.lf) [6,wa,w3,wd,w1,w2,w4] (BT.nd BT.lf [6,wa,wd,w1,w2,w4] BT.lf))))))) [6,w14,w0,w3,w1,w6,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w14,w0,w3,w1,w2,w4] BT.lf) [6,w7,w7,w0,w3,w1,w2,w4] BT.lf) [6,w7,w0,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w7,w0,w5,w3,w1,w2,w4] BT.lf) [6,w7,w0,wc,w3,w1,w2,w4] BT.lf)) [6,w7,w0,w3,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w7,w0,w3,w1d,w1,w2,w4] BT.lf) [6,w7,w0,w3,wd,w1,w2,w4] BT.lf) [6,w7,w0,w3,w1,w6,w2,w4] (BT.nd (BT.nd BT.lf [6,w7,w0,w3,w1,w2,w4] BT.lf) [6,w7,w0,w3,w1,w2,w4,w4] BT.lf))) [6,w7,w0,w3,w1,w2,w4,w8] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w7,w0,w3,w1,w2,w4,we] BT.lf) [6,w7,w0,w3,w1,w2,w8] BT.lf) [6,w7,w3,w1,w2,w4,w8] (BT.nd (BT.nd BT.lf [6,w7,w3,w1,w2,w8] BT.lf) [6,w32,w0,w3,w1,w2,w4] BT.lf)) [6,w32,w0,w3,w1,w2,w4,we] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w0,w0,w3,w1,w2,w4] BT.lf) [6,w0,w0,w5,w3,w1,w2,w4] BT.lf) [6,w0,w0,wc,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,w0,w3,w3,w1,w2,w4] BT.lf) [6,w0,w0,w3,wd,w1,w2,w4] BT.lf)))) [6,w0,w0,w3,w1,w6,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w0,w3,w1,w2,w4] BT.lf) [6,w0,w0,w3,w1,w2,w4,w4] BT.lf) [6,w0,w0,w3,w1,w2,w4,w8] (BT.nd (BT.nd BT.lf [6,w0,w0,w3,w1,w2,w4,we] BT.lf) [6,w0,w0,w3,w1,w2,w8] BT.lf)) [6,w0,w1f,w3,w1,w2] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w1f,w3,w1,w2,w4] BT.lf) [6,w0,w40,w3,w1,w2,w4] BT.lf) [6,w0,w2e,w5,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,w2e,w3,w1,w2,w4] BT.lf) [6,w0,w37,w5,w3,w1,w2,w4] BT.lf))) [6,w0,w37,wc,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w37,w3,w1,w2,w4] BT.lf) [6,w0,w5,w5,w3,w1,w2,w4] BT.lf) [6,w0,w5,w5d,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,w5,wc,w3,w1,w2,w4] BT.lf) [6,w0,w5,w3,w3,w1,w2,w4] BT.lf)) [6,w0,w5,w3,w1b,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w5,w3,wd,w1,w2,w4] BT.lf) [6,w0,w5,w3,w1,w6,w2,w4] BT.lf) [6,w0,w5,w3,w1,w4a,w2,w4] (BT.nd BT.lf [6,w0,w5,w3,w1,w2,w2,w4] BT.lf))))) [6,w0,w5,w3,w1,w2,w18,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w5,w3,w1,w2,w5c,w4] BT.lf) [6,w0,w5,w3,w1,w2,w27,w4] BT.lf) [6,w0,w5,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,w5,w3,w1,w2,w4,w4] BT.lf) [6,w0,w5,w3,w1,w2,w4,w8] BT.lf)) [6,w0,w5,w3,w1,w2,w4,w13] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w5,w3,w1,w2,w4,we] BT.lf) [6,w0,w5,w3,w1,w2,w4,w24] BT.lf) [6,w0,w5,w3,w1,w2,w8] (BT.nd (BT.nd BT.lf [6,w0,w5,w3,w6,w2,w4] BT.lf) [6,w0,w5,w6,w2,w4] BT.lf))) [6,w0,wf,w3,w1,w1c,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,wf,w3,w1,w2,w4] BT.lf) [6,w0,w29,w3,w1,w2,w11,w4] BT.lf) [6,w0,w29,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,wc,wc,w3,w1,w2,w4] BT.lf) [6,w0,wc,w3,w3,w1,w2,w4] BT.lf)) [6,w0,wc,w3,w45,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,wc,w3,wd,w1,w2,w4] BT.lf) [6,w0,wc,w3,w6a,w1,w2] BT.lf) [6,w0,wc,w3,w6a,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,wc,w3,w1,w1,w2,w4] BT.lf) [6,w0,wc,w3,w1,w1c,w2,w4] BT.lf)))) [6,w0,wc,w3,w1,w6b,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,wc,w3,w1,w6,w2,w4] BT.lf) [6,w0,wc,w3,w1,w2,w11,w4] BT.lf) [6,w0,wc,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,wc,w3,w1,w2,w4,w4] BT.lf) [6,w0,wc,w3,w1,w2,w4,w8] BT.lf)) [6,w0,wc,w3,w1,w2,w4,we] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,wc,w3,w1,w2,w4,w20] BT.lf) [6,w0,wc,w3,w1,w2,w8] BT.lf) [6,w0,wc,w3,w1,w2,we] (BT.nd (BT.nd BT.lf [6,w0,wc,w1,w2,w4,we] BT.lf) [6,w0,wc,w1,w2,we] BT.lf))) [6,w0,w1a,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w1a,w3,w1,w2,w4,w8] BT.lf) [6,w0,w1a,w3,w1,w2,w8] BT.lf) [6,w0,w1e,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,w1e,w3,w1,w2,w4,w20] BT.lf) [6,w0,w3,w3,w3,w1,w2,w4] BT.lf)) [6,w0,w3,w3,wd,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w3,w1,w1,w2,w4] BT.lf) [6,w0,w3,w3,w1,w1c,w2,w4] BT.lf) [6,w0,w3,w3,w1,w6,w2,w4] (BT.nd BT.lf [6,w0,w3,w3,w1,w2,w11,w4] BT.lf)))))) [6,w0,w3,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w3,w1,w2,w4,w4] BT.lf) [6,w0,w3,w3,w1,w2,w4,w8] BT.lf) [6,w0,w3,w3,w1,w2,w4,we] (BT.nd (BT.nd BT.lf [6,w0,w3,w3,w1,w2,w4,w20] BT.lf) [6,w0,w3,w3,w1,w2,w8] BT.lf)) [6,w0,w3,w52,w1,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w4d,w1,w2,w4] BT.lf) [6,w0,w3,w44,w1,w2,w4] BT.lf) [6,w0,w3,w1b,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,w3,w28,w1,w2,w4] BT.lf) [6,w0,w3,w19,wd,w1,w2,w4] BT.lf))) [6,w0,w3,w19,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w45,w1,w2,w4] BT.lf) [6,w0,w3,w1d,w1,w2,w4] BT.lf) [6,w0,w3,wd,wd,w1,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,w3,wd,w1,w1c,w2,w4] BT.lf) [6,w0,w3,wd,w1,w6,w2,w4] BT.lf)) [6,w0,w3,wd,w1,w3b,w2,w4] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,wd,w1,w2,w11,w4] BT.lf) [6,w0,w3,wd,w1,w2,w4] BT.lf) [6,w0,w3,wd,w1,w2,w4,w4] (BT.nd (BT.nd BT.lf [6,w0,w3,wd,w1,w2,w4,w8] BT.lf) [6,w0,w3,wd,w1,w2,w4,we] BT.lf)))) [6,w0,w3,wd,w1,w2,w4,w2b] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,wd,w1,w2,w4,w20] BT.lf) [6,w0,w3,wd,w1,w2,w8] BT.lf) [6,w0,w3,w1,w59,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w12,w6,w2] BT.lf) [6,w0,w3,w1,w12,w6,w2,w4] BT.lf)) [6,w0,w3,w1,w12,w2] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w12,w2,w4] BT.lf) [6,w0,w3,w1,w50,w2,w4] BT.lf) [6,w0,w3,w1,w6,w6,w2,w4] (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w6,w3b,w2,w4] BT.lf) [6,w0,w3,w1,w6,w2,w27,w4] BT.lf))) [6,w0,w3,w1,w6,w2,w2f,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w6,w2,w4] BT.lf) [6,w0,w3,w1,w6,w2,w4,w4] BT.lf) [6,w0,w3,w1,w6,w2,w4,w8] (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w6,w2,w4,we] BT.lf) [6,w0,w3,w1,w6,w2,w4,w3d] BT.lf)) [6,w0,w3,w1,w6,w2,w4,w24] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w6,w2,w8] BT.lf) [6,w0,w3,w1,w3b,w2,w4] BT.lf) [6,w0,w3,w1,w2,w2f,w4] (BT.nd BT.lf [6,w0,w3,w1,w2,w4] BT.lf))))) [6,w0,w3,w1,w2,w4,w4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w2,w4,w4,w4] BT.lf) [6,w0,w3,w1,w2,w4,w4,w8] BT.lf) [6,w0,w3,w1,w2,w4,w4,we] (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w2,w4,w43] BT.lf) [6,w0,w3,w1,w2,w4,w16] BT.lf)) [6,w0,w3,w1,w2,w4,w15] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w2,w4,w8] BT.lf) [6,w0,w3,w1,w2,w4,w8,w8] BT.lf) [6,w0,w3,w1,w2,w4,w8,we] (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w2,w4,w8,w2b] BT.lf) [6,w0,w3,w1,w2,w4,w13] BT.lf))) [6,w0,w3,w1,w2,w4,we] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w2,w4,we,we] BT.lf) [6,w0,w3,w1,w2,w4,we,w2b] BT.lf) [6,w0,w3,w1,w2,w4,we,w20] (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w2,w4,we,w3d] BT.lf) [6,w0,w3,w1,w2,w4,w2b] BT.lf)) [6,w0,w3,w1,w2,w4,w3d] (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w2,w4,w2c] BT.lf) [6,w0,w3,w1,w2,w15] BT.lf) [6,w0,w3,w1,w2,w8] (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w2,w8,w8] BT.lf) [6,w0,w3,w1,w2,w8,we] BT.lf)))) [6,w0,w3,w1,w2,w8,w2b] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,w0,w3,w1,w10,w4] BT.lf) [6,w0,w3,w1,w18,w27,w4] BT.lf) [7,65535,w0,w3,w1,w2] (BT.nd (BT.nd BT.lf [7,65535,w0,w3,w1,w2,w4] BT.lf) [7,w9,w0,w3,w1,w2,w4] BT.lf)) [7,w9,w0,w3,w1,w4] (BT.nd (BT.nd (BT.nd BT.lf [7,wb,w0,w3,w1,w2,w4] BT.lf) [7,wb,w3,w1,w2,w4] BT.lf) [7,wa,w0,w3,w1,w2,w4] (BT.nd (BT.nd BT.lf [7,w7,w0,w3,w1,w2,w4] BT.lf) [7,w0,w0,w3,w1,w2,w4] BT.lf))) [7,w0,w5,w3,w1,w2,w4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,w0,wc,w3,w1,w2,w4] BT.lf) [7,w0,w3,w3,w1,w2,w4] BT.lf) [7,w0,w3,wd,w1,w2,w4] (BT.nd (BT.nd BT.lf [7,w0,w3,w1,w6,w2,w4] BT.lf) [7,w0,w3,w1,w2,w4] BT.lf)) [7,w0,w3,w1,w2,w4,w4] (BT.nd (BT.nd (BT.nd BT.lf [7,w0,w3,w1,w2,w4,w8] BT.lf) [7,w0,w3,w1,w2,w4,we] BT.lf) [7,w0,w3,w1,w2,w8] (BT.nd BT.lf [8,w0,w3,w1,w2,w4] BT.lf))))))))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([2,w5,w61,w4e],[]),([2,w3,w94,4294617770],[]),([2,w3,w36,w7a],[]),([2,w1b,w12,w4e],[]),([3,w14,w5,w61,w2],[(56,3)]),([3,w14,w1b,w12,w2],[(72,3)]),([3,w21,w5,w73,w4],[]),([3,w21,w5,w12,w2],[]),([3,w0,w5,w12,w4e],[]),([3,w0,w5,w47,w2],[(56,3)]),([3,w0,wf,w47,w2],[(56,3)]),([3,w0,w1a,4042317984,w2],[]),([3,w0,w1a,w6c,4278251008],[]),([3,w0,w1a,w6c,w2],[]),([3,w0,w3,w94,w4c],[]),([3,w0,w3,w36,w7a],[]),([3,w0,wa3,w11,w33],[]),([3,w0,w59,w11,w49],[]),([3,w5,w1b,w47,w2],[(56,3)]),([3,w1a,w1b,w8b,w2],[(72,3)]),([3,w3,w1b,w47,w2],[]),([3,w3,w1,4272597674,4294770432],[]),([3,w3,w1,w61,w4e],[]),([3,w3,4205488810,w11,w33],[]),([3,w3,4205505194,w11,w4],[]),([3,w3,w36,w7a],[]),([3,w3,w36,w7a,w11],[]),([3,w3,w36,w7a,w4],[]),([3,w3,w36,w7a,w8],[]),([3,w3,w36,4293982960,w8],[]),([3,w3,w36,w11,4294617770],[]),([3,w3,w36,w11,4294945440],[]),([3,w3,w36,w11,w8],[]),([3,w3,w34,4289374890,w24],[]),([3,w3,w34,w18,w8],[]),([3,w3,4210621176,w18,w8],[]),([3,w3,w1c,w18,w7a],[]),([3,w22,w59,w11,w4],[]),([3,w1b,w6,w4e,w4],[]),([3,w28,w1c,w62,w8],[]),([4,16776960,w0,w3,w1],[]),([4,178916010,w3,w1,w2,w8],[]),([4,178956970,w3,w1,w2,w4],[]),([4,214748364,w0,w1,w2,w4],[]),([4,w96,w0,w3,w3c,w4],[]),([4,w96,w0,w3,w4],[]),([4,715795114,w3,w1,w2,w4],[]),([4,1073676288,w0,w3,w1,w2],[]),([4,1077952576,w0,w6,w2,w4],[]),([4,w9f,w0,w8e,w1,w2],[]),([4,w30,w0,w1,w10,w4],[]),([4,1145848908,w0,w1,w2,w4],[]),([4,w60,1357926640,w0,w2,w4],[]),([4,w60,w6f,w0,w1,w2],[]),([4,w60,w0,w1,w2,w4],[]),([4,w60,w0,w1,w2,w63],[]),([4,w60,w0,w1,w2,w8],[]),([4,w60,w0,w34,w2,w4],[]),([4,1154272460,w0,w1,w2,w4],[]),([4,1288457420,w0,w1,w2,w4],[]),([4,1414791168,w0,w3,w1,w2],[]),([4,w17,w0,w5,w6,w2],[]),([4,w17,w0,w3,w1,w2],[]),([4,w17,w0,w3,w1,w10],[]),([4,1431677610,w0,w3,w1,w2],[]),([4,1431677610,w3,w1,w2],[]),([4,1432289280,w0,w3,w1,w2],[]),([4,1437226410,w3,w1,w4],[]),([4,w6f,w0,w3,w1,w2],[]),([4,w6f,w0,w3,w34,w2],[]),([4,1442775210,w0,w3,w1,w2],[]),([4,1610547200,w0,w3,w1,w2],[]),([4,wa,w45,w1,w2,we],[(72,4),(96,2)]),([4,wa,wd,w1,w2,w8],[(72,4),(96,2)]),([4,wa,wd,w1,w10,w8],[(56,2),(72,1),(96,2),(128,2)]),([4,2576980377,w1,w2,w4],[]),([4,w14,w0,w5,w12,w2],[(72,3)]),([4,w14,w3,w1,w61,w2],[]),([4,w14,w3,w1c,w2,w8],[(56,3),(96,0)]),([4,w14,w1b,w6,w2,w4],[(128,3)]),([4,w21,w5,w6,w2,w4],[]),([4,w21,w29,w1,w2,w4],[(116,2)]),([4,w21,w3,w1,w12,w2],[]),([4,w21,w3,w1,w2,w46],[]),([4,w21,w3,w1,w2,w4],[]),([4,w21,w3,w1,w2,4294945448],[]),([4,w21,w3,w1,w2,w8],[]),([4,w21,w3,w1,w10,w4],[]),([4,w21,w3,w1,w4e,w4],[])]
noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([4,w21,w3,w1,w18,w4],[]),([4,2863289685,w3,w1,w2],[]),([4,2863311528,w3,w1,w2,w4],[]),([4,w0,w2e,w59,w11,w4],[]),([4,w0,w37,w6,w2,w13],[(56,3),(104,3)]),([4,w0,3233857536,w6,w2,w4],[(56,3)]),([4,w0,w5,w1a,w8b,w2],[(80,1)]),([4,w0,w5,w3,w47,w2],[]),([4,w0,w5,w73,w2f,w4],[]),([4,w0,w5,4238933160,w2,w4],[]),([4,w0,w5,w8a,w2,w4],[]),([4,w0,w5,w12,w6,w2],[]),([4,w0,w5,w12,w2,w2f],[]),([4,w0,w5,w47,w6,w2],[(56,3)]),([4,w0,w5,w47,w2],[(56,3),(58,3)]),([4,w0,w5,w47,w2,w4],[(56,3)]),([4,w0,w5,w47,w2,w8],[(56,3)]),([4,w0,w5,w6d,w2,w4],[]),([4,w0,w5,w6d,w2,w8],[(56,3)]),([4,w0,w5,w6,w98,w4],[]),([4,w0,w5,w6,w48,w2],[]),([4,w0,w5,w6,w61,w2],[(56,3)]),([4,w0,w5,w6,w2,4290772992],[]),([4,w0,w5,w6,w2,w65],[]),([4,w0,w5,w6,w2,w46],[]),([4,w0,w5,w6,w2,w4],[]),([4,w0,w5,w6,w2,4294902531],[]),([4,w0,w5,w6,w2,w3e],[]),([4,w0,w5,w6,w2,w15],[]),([4,w0,w5,w6,w2,w70],[(56,3)]),([4,w0,w5,w6,w2,w63],[]),([4,w0,w5,w6,w2,w8],[(56,3)]),([4,w0,w5,w6,w2,w49],[(104,3)]),([4,w0,w5,w6,w39,w4],[]),([4,w0,w5,w6,w10,w4],[]),([4,w0,w5,w6,w4e,w4],[]),([4,w0,w5,w6,w64,w4],[(136,3)]),([4,w0,w5,wa4,w2,w4],[]),([4,w0,w99,w6,w2,w4],[]),([4,w0,w99,w2,w4],[]),([4,w0,3301754060,w1,w2,w4],[]),([4,w0,w80,w6,w2,w4],[]),([4,w0,w80,wa4,w2,w4],[]),([4,w0,w67,w6,w2,w4],[]),([4,w0,wf,w1,w12,w2],[]),([4,w0,wf,w1,w98,w4],[]),([4,w0,wf,w1,w48,w2],[]),([4,w0,wf,w9b,w2,w4],[]),([4,w0,wf,w12,w6,w2],[]),([4,w0,wf,w6b,w2,w4],[]),([4,w0,wf,w6,w2,w4],[]),([4,w0,wf,w6,w2,w8],[(56,3)]),([4,w0,wa2,w1,w2,wa5],[(56,2)]),([4,w0,3435184320,w6,w2,w4],[]),([4,w0,w29,w1,w10,w4],[]),([4,w0,3435710664,w1,w2,w4],[]),([4,w0,w35,w1,w2,w4c],[]),([4,w0,w35,w1,w2,4294574080],[]),([4,w0,w35,w1,w2,w4],[]),([4,w0,w35,w1,w2,w8],[]),([4,w0,w35,w1,w10,w4],[]),([4,w0,wc,w3,w6c,w2],[]),([4,w0,wc,w8e,w1,w2],[]),([4,w0,wc,4042309824,w6,w2],[]),([4,w0,wc,w1,wa3,w2],[]),([4,w0,wc,w1,w50,w2],[]),([4,w0,wc,w1,w6d,w2],[]),([4,w0,wc,w1,w2,wa5],[]),([4,w0,wc,w1,w10,we],[(56,2)])]
noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([4,w0,3435934515,w1,w2],[]),([4,w0,3435939020,w1,w2,w4],[]),([4,w0,w1a,w3,w6c,w2],[]),([4,w0,w1a,4042309824,w1,w2],[]),([4,w0,w1a,w6c,w1,w2],[]),([4,w0,w1a,w6c,w2],[]),([4,w0,w1a,w6c,w2,w4],[]),([4,w0,w1a,w6c,w2,w8],[]),([4,w0,w1a,w6c,w2,w2b],[]),([4,w0,w1a,w1,w50,w2],[]),([4,w0,w1a,w1,w6d,w2],[]),([4,w0,w1a,w1,w2,w13],[]),([4,w0,w1a,w1,w2,we],[]),([4,w0,w1a,w1,w2,w91],[(156,0)]),([4,w0,w1a,w1,w2,w2b],[(156,0)]),([4,w0,w1e,w1,w10,w4],[]),([4,w0,w1e,w2a,w2,w4],[]),([4,w0,3435970764,w1,w2,w4],[]),([4,w0,w9d,w1,w2,w4],[]),([4,w0,w9d,w1,w2,w8],[(148,1),(156,3)]),([4,w0,w23,w1,w51,w2],[]),([4,w0,w23,w1,w9a,w4],[]),([4,w0,w23,w1,w9a,w8],[(148,1)]),([4,w0,w23,w1,w2,w4],[]),([4,w0,w23,w1,w2,w15],[]),([4,w0,w23,w1,w2,w8],[(148,1)]),([4,w0,w23,w2a,w2,w4],[]),([4,w0,3435973832,w1,w2,w4],[]),([4,w0,3435973832,w1,w2,w8],[]),([4,w0,w3,3587506176,w1,w2],[]),([4,w0,w3,3705405440,w1,w2],[]),([4,w0,w3,w78,w1,w2],[]),([4,w0,w3,3722283144,w1,w2],[]),([4,w0,w3,3724476416,w1,w2],[]),([4,w0,w3,w1,w8f,w2],[]),([4,w0,w3,w1,4241270920,w2],[]),([4,w0,w3,w1,4243324928,w2],[]),([4,w0,w3,w1,w12,w2],[]),([4,w0,w3,w1,w12,w10],[]),([4,w0,w3,w1,w12,w97],[]),([4,w0,w3,w1,w12,w4e],[]),([4,w0,w3,w1,4244408456,w2],[]),([4,w0,w3,w1,4244416512,w2],[]),([4,w0,w3,w1,w47,w2],[]),([4,w0,w3,w1,4244570112,w2],[]),([4,w0,w3,w1,4261216256,w2],[]),([4,w0,w3,w1,4277010432,w2],[]),([4,w0,w3,w1,4277054122,w2],[]),([4,w0,w3,w1,4277927936,w2],[]),([4,w0,w3,w1,4277971456,w2],[]),([4,w0,w3,w1,w48,w2],[]),([4,w0,w3,w1,w61,w2],[]),([4,w0,w3,w1,w2,w46],[]),([4,w0,w3,w1,w2,4294748840],[]),([4,w0,w3,w1,w2,4294836224],[]),([4,w0,w3,w1,w2,4294879914],[]),([4,w0,w3,w1,w2,w4],[]),([4,w0,w3,w1,w2,4294901763],[]),([4,w0,w3,w1,w2,4294901765],[]),([4,w0,w3,w1,w2,4294901770],[]),([4,w0,w3,w1,w2,4294901772],[]),([4,w0,w3,w1,w2,w90],[]),([4,w0,w3,w1,w2,4294901823],[]),([4,w0,w3,w1,w2,4294901896],[]),([4,w0,w3,w1,w2,w79],[]),([4,w0,w3,w1,w2,4294904490],[]),([4,w0,w3,w1,w2,4294934528],[]),([4,w0,w3,w1,w2,w3e],[]),([4,w0,w3,w1,w2,4294936704],[]),([4,w0,w3,w1,w2,w15],[])]
noncomputable def K_3 : List (List ℕ × List (ℕ × ℕ)) := [([4,w0,w3,w1,w2,4294936746],[]),([4,w0,w3,w1,w2,4294944904],[]),([4,w0,w3,w1,w2,w70],[]),([4,w0,w3,w1,w2,4294945448],[]),([4,w0,w3,w1,w2,w8],[]),([4,w0,w3,w1,w2,4294945455],[]),([4,w0,w3,w1,w2,w49],[]),([4,w0,w3,w1,w2,4294951040],[]),([4,w0,w3,w1,w2,4294953096],[]),([4,w0,w3,w1,w2,4294961834],[]),([4,w0,w3,w1,4278255365,w4],[]),([4,w0,w3,w1,4278255365,w8],[]),([4,w0,w3,w1,4278255372,w4],[]),([4,w0,w3,w1,4278255496,w4],[]),([4,w0,w3,w1,4278320897,w4],[]),([4,w0,w3,w1,4278779656,w4],[]),([4,w0,w3,w1,4286643968,w4],[]),([4,w0,w3,w1,w39,w4],[]),([4,w0,w3,w1,w39,w3e],[]),([4,w0,w3,w1,w39,w15],[]),([4,w0,w3,w1,w39,w8],[]),([4,w0,w3,w1,w26,w65],[]),([4,w0,w3,w1,w26,w4],[]),([4,w0,w3,w1,w26,w15],[]),([4,w0,w3,w1,w26,w8],[]),([4,w0,w3,w1,4287168384,w4],[]),([4,w0,w3,w1,w10,w65],[]),([4,w0,w3,w1,w10,w4c],[]),([4,w0,w3,w1,w10,4294443008],[]),([4,w0,w3,w1,w10,w4],[]),([4,w0,w3,w1,w10,w3e],[]),([4,w0,w3,w1,w10,4294936576],[]),([4,w0,w3,w1,w10,w15],[]),([4,w0,w3,w1,w10,w7b],[]),([4,w0,w3,w1,w10,w63],[]),([4,w0,w3,w1,w10,4294945416],[]),([4,w0,w3,w1,w10,w8],[(56,2)]),([4,w0,w3,w1,w97,w4],[]),([4,w0,w3,w1,4289265544,w4],[]),([4,w0,w3,w1,w4e,w4],[]),([4,w0,w3,w1,w4e,w70],[]),([4,w0,w3,w1,w4e,w8],[(56,2),(72,0)]),([4,w0,w3,w1,w69,w83],[]),([4,w0,w3,w1,4289374890,w83],[]),([4,w0,w3,w1,w18,4291603080],[(56,1),(108,0)]),([4,w0,w3,w1,4290772992,w64],[]),([4,w0,w3,w1,w64,w65],[]),([4,w0,w3,w1,w64,w4],[]),([4,w0,w3,w1,w64,w8],[]),([4,w0,w3,w1,w64,w13],[(80,3)]),([4,w0,w3,w1,4290838400,w4],[]),([4,w0,w3,w1,4290838400,w8],[]),([4,w0,w3,w1,w5c,w49],[(80,3)]),([4,w0,w3,w1,4291362560,w4],[]),([4,w0,w3,w1,4291362696,w4],[]),([4,w0,w3,w1,w65,4293984000],[]),([4,w0,w3,4169726088,w11,w4],[]),([4,w0,w3,4176541936,w10,w4],[]),([4,w0,w3,w88,w26,w4],[]),([4,w0,w3,w88,w10,w4],[]),([4,w0,w3,w2a,w10,w4],[]),([4,w0,w3,w2a,w10,w15],[]),([4,w0,w3,w2a,w10,w8],[(56,1)]),([4,w0,w3,w2a,w62,w4],[]),([4,w0,w3,w2a,w4e,w4],[]),([4,w0,w3,w94,w11,w4],[]),([4,w0,w3,w7f,w11,w4],[]),([4,w0,w3,w36,w4c,w11],[(132,2)]),([4,w0,w3,w36,w11,w4],[]),([4,w0,w3,w36,w11,w8],[]),([4,w0,w3,w34,w62,w4],[]),([4,w0,w3,w34,w5a,w4],[])]
noncomputable def K_4 : List (List ℕ × List (ℕ × ℕ)) := [([4,w0,w3,w34,w18,w4],[]),([4,w0,w3,w34,w18,w63],[]),([4,w0,w3,w34,w18,w8],[]),([4,w0,w3,4210621176,w18,w4],[]),([4,w0,w3,4241289216,w11,w4],[]),([4,w0,w3,4243648752,w83,w4],[]),([4,w0,w28,w1c,w62,w4],[]),([4,2863311615,w3,w1,w2,w8],[]),([4,2863329006,w3,w1,w2,w8],[]),([4,w1f,w3,w1,w2,w8],[]),([4,2863377067,w3,w1,w2,w4],[]),([4,w5,w22,w6,w2,w4],[(96,3)]),([4,w5,w5e,w6,w2,w4],[(128,3)]),([4,w5,w1b,w6,w2,w8],[(56,3),(72,3)]),([4,wf,w45,w1,w2,w4],[]),([4,wf,wd,w1,w2,w8],[(72,4)]),([4,wc,w3,w1,4205488810,w2],[]),([4,w1a,w1b,w1,w2,w8],[(72,4)]),([4,w3,3937053354,w1,w2,w4],[]),([4,w3,w22,w1,w2,w4],[]),([4,w3,w22,w1,w2,w8],[]),([4,w3,w22,w1,w2,w49],[]),([4,w3,w22,w1,w2,4294961834],[]),([4,w3,w22,w1,w5c,w4],[(72,3)]),([4,w3,w5e,w1,w2,w4],[]),([4,w3,w5e,w1,w2,w8],[]),([4,w3,w5e,w1,w2,w13],[(72,3)]),([4,w3,w5e,w1,w64,w4],[]),([4,w3,w5e,w6b,w2,w4],[]),([4,w3,3941264042,w1,w2,w4],[(72,3)]),([4,w3,w1b,w1,w2,w8],[(72,3)]),([4,w3,w1b,w6,w2,w8],[(72,3)]),([4,w3,w28,w1c,w2,w8],[(56,3)]),([4,w3,4008356522,w1,w2,w4c],[(128,2)]),([4,w3,4008356522,w1,w2,w4],[]),([4,w3,4008373994,w1,w2,w8],[]),([4,w3,w45,w1,4210731690,w2],[]),([4,w3,w45,w1,w10,w4],[(128,2)]),([4,w3,wd,w1,w2,4294617770],[]),([4,w3,wd,w1,w10,w8],[(56,2)]),([4,w3,wd,w36,w11,w4],[]),([4,w3,w36,w11,w4,w8],[]),([4,w3,w36,w11,w8],[]),([4,w3,w34,w18,w4,w8],[]),([4,w3,w34,w18,w63],[]),([4,w3,w34,w18,w8],[]),([4,w3,w1c,w18,w11,w8],[(116,0)]),([4,w28,w1c,w62,w4],[]),([5,0,w17,w0,w3,w1,w2],[]),([5,0,w0,w3,w1,w2,w4],[]),([5,0,w0,w3,w1,w2,w8],[]),([5,15,w0,w3,w1,w2,w4],[]),([5,85,w0,w3,w1,w2,w4],[(72,2),(96,0)]),([5,85,w0,w3,w1,w2,w8],[(72,2),(96,0)]),([5,170,w0,w3,w1,w2,w4],[]),([5,204,w0,w3,w1,w2,w4],[(96,0)]),([5,255,w0,w3,w1,w4a],[(128,3)]),([5,255,w0,w3,w1,w2,w4],[])]
noncomputable def K_5 : List (List ℕ × List (ℕ × ℕ)) := [([5,255,w0,w3,w1,w2,w8],[]),([5,4095,w0,w3,w1,w2,w4],[]),([5,17476,w0,w3,w1,w2,w4],[]),([5,17476,w0,w3,w1,w2,w8],[]),([5,21845,w9,w0,w3,w1],[]),([5,21845,wb,w3,w1,w2],[]),([5,21845,w7,w3,w1,w2],[]),([5,21845,w0,w3,w1,w2],[]),([5,21845,w0,w3,w1,w2,w4],[]),([5,21845,w0,w3,w1,w2,w8],[]),([5,21845,w1f,w3,w1,w2],[]),([5,21845,w1f,w3,w1,w2,w8],[]),([5,22015,w0,w3,w1,w2],[(2,3)]),([5,22015,w0,w3,w1,w2,w4],[]),([5,22015,w0,w3,w1,w2,w63],[]),([5,34952,w0,w3,w1,w2,w4],[(96,0)]),([5,43690,w7,w3,w1,w2,w4],[]),([5,43690,w0,w3,w1,w2,w4],[]),([5,43690,w0,w3,w1,w2,w8],[]),([5,43690,w1f,w3,w1,w2],[]),([5,43690,w1f,w3,w1,w2,w4],[]),([5,49344,w0,w3,w1,w2,w4],[]),([5,52428,w0,wc,w1,w2,w4],[]),([5,52428,w0,w3,w1,w2,w4],[]),([5,52428,w0,w3,w1,w2,w8],[]),([5,52428,w0,w52,w1,w2],[]),([5,52428,w0,w52,w1,w2,w4],[]),([5,61166,w0,w3,w1,w2,w4],[]),([5,64764,w0,w3,w1,w2],[(2,3)]),([5,64764,w0,w3,w1,w2,w4],[])]
noncomputable def K_6 : List (List ℕ × List (ℕ × ℕ)) := [([5,65535,w9,w4b,w0,w3],[]),([5,65535,w9,wb,w3,w1],[]),([5,65535,w9,w0,w3,w1],[]),([5,65535,w17,w0,w3,w1,w2],[]),([5,65535,wb,w3,w1,w2],[]),([5,65535,wa,wd,w1,w2],[]),([5,65535,w7,w3,w1,w2,w8],[]),([5,65535,w0,w5,w6,w2],[]),([5,65535,w0,w5,w6,w2,w4],[]),([5,65535,w0,wc,w1,w2,we],[]),([5,65535,w0,w3,w1,w12,w2],[]),([5,65535,w0,w3,w1,w2],[]),([5,65535,w0,w3,w1,w2,w4],[]),([5,65535,w0,w3,w1,w2,w15],[]),([5,65535,w0,w3,w1,w2,w8],[]),([5,65535,w0,w3,w1,w10],[]),([5,65535,w0,w3,w1,w10,w4],[]),([5,65535,w1f,w3,w1,w2,w8],[]),([5,196611,w0,w3,w1,w2,w4],[]),([5,327685,w0,w3,w1,w2,w4],[(72,2)]),([5,655370,w0,w3,w1,w2,w4],[]),([5,786444,w0,w3,w1,w2,w4],[]),([5,983040,w0,w3,w1,w2,w4],[]),([5,w53,w0,w3,w3c,w11,w4],[(96,2),(168,2)]),([5,w53,w0,w3,w3c,w4],[(2,2),(96,2)]),([5,w53,w0,w3,w1,w2,w4c],[]),([5,w53,w0,w3,w1,w2,w4],[]),([5,w53,w0,w3,w1,w2,w90],[]),([5,w53,w0,w3,w1,w2,w8],[]),([5,983295,w0,w3,w1,w2,w4],[])]
noncomputable def K_7 : List (List ℕ × List (ℕ × ℕ)) := [([5,1048575,w0,w3,w1,w2],[(2,2)]),([5,1048575,w0,w3,w1,w2,w4c],[]),([5,1048575,w0,w3,w1,w2,w4],[]),([5,4128831,w0,w3,w1,w2,w4],[]),([5,4456516,w0,w3,w1,w2,w4],[]),([5,5570560,w0,w3,w1,w2,w4],[]),([5,w54,w55,w3,w1,w4],[(56,3)]),([5,w54,w0,w3,w1,w2,w4],[]),([5,w54,w0,w3,w1,w2,w8],[]),([5,5570815,w0,w3,w1,w2,w4],[]),([5,5592405,w0,w3,w1,w2,w4],[]),([5,5636095,w0,w3,w1,w2,w4],[]),([5,6226015,w0,w3,w1,w2,w4],[]),([5,6226015,w0,w3,w1,w62,w4],[]),([5,6226015,w0,w3,w1,w4],[(2,1)]),([5,8913032,w0,w3,w1,w2,w4],[(96,0)]),([5,11141120,w0,w3,w1,w2,w4],[]),([5,w3f,w55,w3,w1,w2,w4],[]),([5,w3f,w0,w3,w1,w2,w4],[]),([5,w3f,w0,w3,w1,w2,w79],[]),([5,w3f,w0,w3,w1,w2,w8],[]),([5,w3f,w40,w3,w1,w2,w4],[]),([5,w3f,w40,w3,w1,w4],[]),([5,11184810,w0,w3,w1,w2,w4],[]),([5,12583104,w0,w3,w1,w2,w4],[]),([5,13369344,w0,w3,w1,w2,w4],[]),([5,w41,w0,w5d,w1,w2,w4],[(128,0)]),([5,w41,w0,w3,w1,w2,w4],[]),([5,w41,w0,w3,w1,w2,w8],[]),([5,w41,w0,w4d,w1,w2,w4],[]),([5,w41,w0,w4d,w1,w4],[]),([5,w41,w0,wd,w1,w2,w4],[]),([5,13421772,w0,w3,w1,w2,w4],[]),([5,15597806,w0,w3,w1,w2,w4],[]),([5,16515324,w0,w3,w1,w2,w4],[])]
noncomputable def K_8 : List (List ℕ × List (ℕ × ℕ)) := [([5,w42,w0,w3,w1,w4a,w2],[]),([5,w42,w0,w3,w1,w2,w4],[]),([5,w42,w0,w3,w1,w2,w43],[]),([5,w42,w0,w3,w1,w2,w8],[]),([5,w42,w0,w3,w1,w43],[]),([5,16711850,w0,w3,w1,w2,w4],[]),([5,16711850,w0,w3,w1,w2,w8],[]),([5,16711884,w0,w3,w1,w2,w4],[]),([5,w9,w4b,858993459,w0,w4],[]),([5,w9,w4b,wb,w3,w4],[]),([5,w9,w4b,w0,w3,w4],[]),([5,w9,w4b,w0,w3,w8],[]),([5,w9,w17,wb,w3,w1],[]),([5,w9,w17,w0,w3,w1],[]),([5,w9,w17,w0,w3,w1,w2],[]),([5,w9,wb,w3,w1,w4],[]),([5,w9,wb,w3,w1,w8],[]),([5,w9,wa,wd,w1,w4],[]),([5,w9,w55,w3,w1,w18,w4],[]),([5,w9,w7,w3,w1,w8],[]),([5,w9,w0,w1f,w3,w1],[]),([5,w9,w0,w5,w6,w2,w4],[]),([5,w9,w0,w5,w6,w4],[]),([5,w9,w0,w5d,w1,w27,w4],[]),([5,w9,w0,wc,w1,we],[])]
noncomputable def K_9 : List (List ℕ × List (ℕ × ℕ)) := [([5,w9,w0,w3,w1,w12],[]),([5,w9,w0,w3,w1,w12,w2],[]),([5,w9,w0,w3,w1,w2,w65],[]),([5,w9,w0,w3,w1,w2,w4],[]),([5,w9,w0,w3,w1,w2,w79],[]),([5,w9,w0,w3,w1,w2,w15],[]),([5,w9,w0,w3,w1,w2,w63],[]),([5,w9,w0,w3,w1,w2,w8],[]),([5,w9,w0,w3,w1,w10,w4],[]),([5,w9,w0,w3,w1,w65],[(2,0)]),([5,w9,w0,w3,w1,w4],[]),([5,w9,w0,w3,w1,w79],[]),([5,w9,w0,w3,w1,w15],[]),([5,w9,w0,w3,w1,w63],[(2,3)]),([5,w9,w0,w3,w1,w8],[]),([5,w9,w0,w3,w2a,w2,w4],[]),([5,w9,w0,w3,w2a,w4],[(2,0)]),([5,w9,w0,w3,w34,w2,w4],[]),([5,w9,w0,w3,w34,w4],[(2,3)]),([5,16715775,w0,w3,w1,w2,w4],[]),([5,16733695,w0,w3,w1,w2,w4],[]),([5,16733695,w0,w3,w1,w2,w8],[]),([5,w66,w0,w3,w1,w2,w4],[]),([5,w66,w0,w3,w1,w2,w8],[]),([5,w66,w0,w3,w1,w24],[]),([5,67044351,w0,w3,w1,w2,w4],[]),([5,89458005,w0,w3,w1,w2,w4],[]),([5,w9e,w0,w3,w1,w2,w4],[]),([5,178916010,w0,w3,w1,w2,w4],[]),([5,214699212,w0,w3,w1,w2,w4],[])]
noncomputable def K_10 : List (List ℕ × List (ℕ × ℕ)) := [([5,w74,w0,w3,w1,w2,w4],[]),([5,w56,w0,w3,w3c,w11,w4],[]),([5,w56,w0,w3,w1,w2,w4],[]),([5,w56,w0,w3,w1,w2,w8],[]),([5,w56,w0,w3,w11,w4],[(2,2)]),([5,268435455,w0,w3,w1,w2,w4],[]),([5,1073692671,w0,w3,w1,w2,w4],[]),([5,1077952576,w0,w3,w1,w2,w4],[]),([5,w9f,w17,w0,w3,w1,w2],[]),([5,w9f,w0,w3,w1,w2,w4],[]),([5,w30,w17,w0,w3,w1,w2],[]),([5,w30,wa,w0,w1,w2,w4],[(104,0)]),([5,w30,w0,w3,w1,w2,w4],[]),([5,w30,w0,w3,w1,w2,w8],[]),([5,w30,w0,w44,w1,w2,w4],[]),([5,w30,w0,w1,w6,w2,w4],[]),([5,w30,w44,w1,w2,w4],[]),([5,1145359564,w0,w3,w1,w2,w4],[]),([5,w60,w57,w0,w1,w2,w4],[]),([5,w60,w55,w0,w1,w2,w4],[(56,4)]),([5,w60,w0,w3,w1,w2,w4],[]),([5,w60,w0,w1,w2,w4],[]),([5,1414812756,w0,w3,w1,w2,w4],[]),([5,w17,w17,w0,w3,w1,w2],[]),([5,w17,wb,w0,w3,w1,w2],[]),([5,w17,wb,w3,w1,w2],[]),([5,w17,w3a,w0,w3,w1,w2],[]),([5,w17,wa,w0,w3,w1,w2],[(136,0)]),([5,w17,w7,w0,w3,w1,w2],[]),([5,w17,w0,w0,w3,w1,w2],[]),([5,w17,w0,w1f,w3,w1,w2],[]),([5,w17,w0,w5,w3,w1,w2],[]),([5,w17,w0,wc,w3,w1,w2],[]),([5,w17,w0,w3,w3,w1,w2],[]),([5,w17,w0,w3,w8e,w1,w2],[]),([5,w17,w0,w3,w44,w1,w2],[])]
noncomputable def K_11 : List (List ℕ × List (ℕ × ℕ)) := [([5,w17,w0,w3,wd,w1,w2],[]),([5,w17,w0,w3,w1,w6,w2],[]),([5,w17,w0,w3,w1,w2],[]),([5,w17,w0,w3,w1,w2,w4],[]),([5,w17,w0,w3,w1,w2,w16],[]),([5,w17,w0,w3,w1,w2,w8],[]),([5,w17,w0,w3,w1,w2,we],[]),([5,w17,w0,w3,w1,w2,w2c],[]),([5,w17,w3,w1,w2,w16],[]),([5,w17,w3,w1,w2,w8],[]),([5,1431651396,w0,w3,w1,w2,w4],[]),([5,wb,w0,w5,w6,w2,w4],[]),([5,wb,w0,w3,w78,w1,w2],[]),([5,wb,w0,w3,w1,w12,w2],[]),([5,wb,w0,w3,w1,w2,w4],[]),([5,wb,w0,w3,w1,w2,w15],[]),([5,wb,w0,w3,w1,w2,w8],[]),([5,wb,w0,w3,w1,w10,w4],[]),([5,wb,w1f,w3,w1,w2],[]),([5,wb,w5,w6,w2,w4],[]),([5,wb,wc,w1,w2,we],[]),([5,wb,w3,w78,w1,w2],[]),([5,wb,w3,w1,w12,w2],[]),([5,wb,w3,w1,w2,w4],[]),([5,wb,w3,w1,w2,w15],[]),([5,wb,w3,w1,w2,w8],[]),([5,wb,w3,w1,w10,w4],[]),([5,1431655935,w0,w3,w1,w2,w4],[])]
noncomputable def K_12 : List (List ℕ × List (ℕ × ℕ)) := [([5,w3a,w0,w3,w1,w2,w4],[]),([5,w3a,w0,w3,w1,w2,w8],[]),([5,w3a,w3,w1,w2,w8],[]),([5,1432311135,w0,w3,w1,w2,w4],[]),([5,w6f,w57,w0,w3,w1,w2],[(140,1)]),([5,w6f,w55,w0,w3,w1,w2],[(56,3),(104,1)]),([5,w6f,w0,w3,w1,w2],[]),([5,w6f,w0,w3,w1,w2,w4],[]),([5,w57,w0,w3,w1,w2,w4],[(100,1)]),([5,w57,w0,w3,w1,w2,w63],[(100,1)]),([5,w57,w0,w3,w1,w2,w8],[(100,1)]),([5,w57,w0,w3,w34,w2,w4],[(100,1),(132,3)]),([5,w57,w3,w1,w18,w4],[]),([5,1442840575,w0,w3,w1,w2,w4],[(100,1)]),([5,1610571775,w0,w3,w1,w2,w4],[(100,1),(132,3)]),([5,2147516416,w0,w3,w1,w2,w4],[]),([5,2155872256,w0,w3,w1,w2,w4],[]),([5,w31,w0,w5,w6,w2,w4],[]),([5,w31,w0,w3,w1,w2,w4],[]),([5,w31,w0,w3,w1,w2,w3e],[]),([5,w31,w0,w3,w1,w2,w15],[]),([5,w31,w0,w3,w1,w2,w8],[]),([5,w31,w0,w3,w1,w39,w4],[]),([5,w31,w0,w3,w1,w10,w4],[]),([5,w31,w0,w3,w2a,w2,w4],[(56,0),(72,0),(96,0),(128,0),(168,0)]),([5,2290124928,w0,w3,w1,w2,w4],[(96,0)]),([5,w25,w0,w3,w1,w2,w4],[(96,0)]),([5,w25,w0,w3,w1,w2,w15],[(96,0)]),([5,w25,w0,w3,w1,w2,w8],[(96,0)]),([5,w25,w0,w3,w1,w26,w4],[]),([5,w25,w0,w3,w1,w10,w4],[]),([5,2290647168,w0,w3,w1,w2,w4],[(96,0)]),([5,wa,2862656160,w3,w1,w2,w4],[]),([5,wa,w0,w5,w6,w2,w4],[]),([5,wa,w0,w29,w1,w2,w4],[(96,0)]),([5,wa,w0,wc,w1,w2,we],[(96,0)]),([5,wa,w0,w1e,w1,w2,w4],[])]
noncomputable def K_13 : List (List ℕ × List (ℕ × ℕ)) := [([5,wa,w0,w3,w3c,w11,w4],[(56,2),(72,2),(128,2),(168,2)]),([5,wa,w0,w3,w1,w12,w2],[(96,0)]),([5,wa,w0,w3,w1,w2,w4c],[(56,2),(72,2),(96,0),(168,2)]),([5,wa,w0,w3,w1,w2,w4],[(96,0)]),([5,wa,w0,w3,w1,w2,w3e],[(96,0)]),([5,wa,w0,w3,w1,w2,w15],[(96,0)]),([5,wa,w0,w3,w1,w2,w7b],[(56,1),(72,1),(96,0)]),([5,wa,w0,w3,w1,w2,w8],[(96,0)]),([5,wa,w0,w3,w1,w39,w4],[(96,0)]),([5,wa,w0,w3,w1,w26,w4],[(96,0)]),([5,wa,w0,w3,w1,w10,w4],[]),([5,wa,w0,w3,w1,w10,w15],[]),([5,wa,w0,w3,w1,w10,w8],[]),([5,wa,w0,w3,w1,w62,w4],[(56,1),(72,1),(168,1)]),([5,wa,w0,w3,w2a,w10,w4],[]),([5,wa,w0,w28,w1,w2,w4],[(56,2),(72,2),(96,3),(128,1),(168,2)]),([5,wa,w0,w1d,w1,w2,w4],[(96,4),(128,2)]),([5,wa,w0,wd,w1,w2,w4],[(96,4),(128,2)]),([5,wa,w0,wd,w1,w2,w15],[(96,4),(128,2)]),([5,wa,w0,wd,w1,w2,w8],[(96,4),(128,2)]),([5,wa,w0,wd,w1,w10,w4],[(56,2),(72,2),(96,1),(128,2),(168,2)]),([5,wa,w3,w45,w1,w2,w4],[(96,0)]),([5,wa,w3,wd,w1,w2,w8],[(96,0)]),([5,wa,wd,w1,w2,w4],[]),([5,wa,wd,w1,w2,w4,w8],[(72,4),(96,2)]),([5,wa,wd,w1,w2,w15],[(72,4),(96,2)]),([5,wa,wd,w1,w2,w8],[(72,4),(74,0),(73,1),(96,2),(97,3)]),([5,wa,wd,w1,w10,w4],[(72,1),(128,2)]),([5,2290657962,w0,w3,w1,w2,w4],[]),([5,2290666700,w0,w3,w1,w2,w4],[]),([5,2290679807,w0,w3,w1,w2],[(2,2)]),([5,2290679807,w0,w3,w1,w2,w4],[]),([5,2292877482,w0,w3,w1,w2,w4],[]),([5,2295105740,w0,w3,w1,w2,w4],[]),([5,2298448127,w0,w3,w1,w2,w4],[])]
noncomputable def K_14 : List (List ℕ × List (ℕ × ℕ)) := [([5,2298448127,w0,w3,w1,w4],[(2,4)]),([5,2827528328,w0,w3,w1,w2,w4],[(72,2),(96,0)]),([5,w86,w0,w3,w1,w12,w2],[(72,2),(96,0)]),([5,w86,w0,w3,w1,w2,w4],[(72,2),(96,0)]),([5,2829617288,w0,w3,w1,w2,w4],[(72,2),(96,0)]),([5,w14,w0,w5,w6,w2,w4],[(72,3)]),([5,w14,w0,w3,w1,w12,w2],[(72,2),(96,0)]),([5,w14,w0,w3,w1,w2,w4],[(72,2),(96,0)]),([5,w14,w0,w3,w1,w2,w70],[(72,2),(96,0)]),([5,w14,w0,w3,w1,w2,w8],[(72,2),(96,0),(80,1)]),([5,w14,w0,w3,w1,w4e,w4],[(72,1)]),([5,w14,w0,w3,w2a,w2,w4],[(56,0),(72,3),(96,0),(168,0)]),([5,w14,w0,w3,w1c,w2,w4],[(72,3),(128,0)]),([5,w14,w3,w1c,w2,w4],[]),([5,w21,w0,w3,w1,w2,w4],[(72,2),(96,0),(80,2),(104,0)]),([5,w21,w3,w1,w6,w2,w4],[(156,3)]),([5,w21,w3,w1,w2,w2f,w4],[]),([5,w21,w3,w1,w2,w4],[(58,2),(74,0)]),([5,w7,w0,w5,w6,w2,w4],[(72,3)]),([5,w7,w0,w3,w1,w12,w2],[]),([5,w7,w0,w3,w1,w2,w4],[]),([5,w7,w0,w3,w1,w2,w15],[]),([5,w7,w0,w3,w1,w2,w8],[]),([5,w7,w0,w3,w1,w26,w4],[]),([5,w7,w0,w3,w1,w10,w4],[(72,2)]),([5,w7,w3,w1,w2,w8],[]),([5,2863268010,w0,w3,w1,w2,w4],[]),([5,w58,w0,w3,w1,w2,w4],[]),([5,w32,w0,w3,w1,w2,w4],[]),([5,w32,w0,w3,w1,w2,w15],[]),([5,w32,w0,w3,w1,w2,w8],[]),([5,w32,w3,w1,w2,w8],[]),([5,w4f,w0,w3,w1,w2,w4],[]),([5,w0,w0,w5,w6,w2,w4],[(72,3)]),([5,w0,w0,w3,w1,w12,w2],[])]
noncomputable def K_15 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w0,w3,w1,w2,w4],[]),([5,w0,w0,w3,w1,w2,w15],[]),([5,w0,w0,w3,w1,w2,w8],[]),([5,w0,w0,w3,w1,w10,w4],[(72,2)]),([5,w0,2863311615,w3,w1,w2,w4],[]),([5,w0,2863329006,w3,w1,w2,w4],[]),([5,w0,w1f,w3,w1,w2],[]),([5,w0,w1f,w3,w1,w2,w4],[]),([5,w0,w1f,w3,w1,w2,w8],[]),([5,w0,2863639215,w3,w1,w2,w4],[]),([5,w0,2867768046,w3,w1,w2,w4],[]),([5,w0,w76,w3,w1,w2,w4],[]),([5,w0,2868838655,w3,w1,w2,w4],[]),([5,w0,2868882090,w3,w1,w2,w4],[]),([5,w0,w40,w3,w1,w2,w4],[]),([5,w0,w40,w3,w1,w2,w8],[]),([5,w0,2868903935,w3,w1,w2,w4],[]),([5,w0,2952769535,w3,w1,w2,w4],[]),([5,w0,3221225472,w3,w1,w2,w4],[]),([5,w0,w2e,w5,w6,w2,w4],[(144,3)]),([5,w0,w2e,w3,w1,w2,w4],[]),([5,w0,w2e,w3,w1,w2,w8],[]),([5,w0,w2e,w3,w1,w2,w49],[]),([5,w0,w2e,w3,w1,w5c,w4],[(112,3)]),([5,w0,w89,w3,w1,w2,w4],[]),([5,w0,w37,w5,w6,w2,w4],[]),([5,w0,w37,w3,w1,w4a,w2],[(56,3),(136,3),(176,3)]),([5,w0,w37,w3,w1,w2,w4],[]),([5,w0,w37,w3,w1,w2,w8],[]),([5,w0,w37,w3,w1,w2,w13],[]),([5,w0,w37,w3,w1,w64,w4],[]),([5,w0,w37,w3,w6b,w2,w4],[(136,0)]),([5,w0,3233841280,w3,w1,w2,w4],[]),([5,w0,3233841280,w3,w1,w2,w8],[]),([5,w0,3233857536,w3,w1,w2,w4],[]),([5,w0,w5,w5,w6,w2,w4],[]),([5,w0,w5,w5d,w1,w27,w4],[(104,0),(136,0)]),([5,w0,w5,w82,w1,w2,w4],[(136,0),(112,1)])]
noncomputable def K_16 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w5,wc,w6,w2,w4],[]),([5,w0,w5,w1a,w1,w2,w4],[(112,1)]),([5,w0,w5,w1a,w1,w2,w8],[(112,1)]),([5,w0,w5,w3,w1,w12,w2],[]),([5,w0,w5,w3,w1,w2,4290772992],[(80,3),(104,3)]),([5,w0,w5,w3,w1,w2,w65],[(80,0),(104,0)]),([5,w0,w5,w3,w1,w2,w4],[]),([5,w0,w5,w3,w1,w2,w3e],[]),([5,w0,w5,w3,w1,w2,w15],[]),([5,w0,w5,w3,w1,w2,w63],[(80,3),(104,3)]),([5,w0,w5,w3,w1,w2,w8],[]),([5,w0,w5,w3,w1,w2,w49],[]),([5,w0,w5,w3,w1,w39,w4],[]),([5,w0,w5,w3,w1,w10,w4],[]),([5,w0,w5,w3,w1,w64,w4],[]),([5,w0,w5,w3,w2a,w2,w4],[(80,0),(104,0)]),([5,w0,w5,w3,w34,w2,w4],[(80,3),(104,3)]),([5,w0,w5,w3,w9b,w2,w4],[]),([5,w0,w5,w3,w12,w6,w2],[]),([5,w0,w5,w3,w6b,w2,w4],[]),([5,w0,w5,w3,w6,w2,w4],[]),([5,w0,w5,w3,w6,w2,w8],[]),([5,w0,w5,w1b,w6,w2,w4],[(80,3),(104,3)]),([5,w0,w5,wd,w6,w2,w4],[]),([5,w0,w5,w73,w6,w2,w4],[]),([5,w0,w5,w12,w6,w2],[(58,3)]),([5,w0,w5,w12,w6,w2,w4],[]),([5,w0,w5,w6,w6,w2,w4],[]),([5,w0,w5,w6,w3b,w2,w4],[]),([5,w0,w5,w6,w4a,w2,w4],[(104,3)]),([5,w0,w5,w6,w2,w2,w4],[]),([5,w0,w5,w6,w2,w18,w4],[(56,3)]),([5,w0,w5,w6,w2,w5c,w4],[(108,3)]),([5,w0,w5,w6,w2,w27,w4],[]),([5,w0,w5,w6,w2,w2f,w4],[]),([5,w0,w5,w6,w2,w4],[(58,3)]),([5,w0,w5,w6,w2,w4,w4],[])]
noncomputable def K_17 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w5,w6,w2,w4,w8],[(56,3)]),([5,w0,w5,w6,w2,w4,w13],[]),([5,w0,w5,w6,w2,w4,we],[]),([5,w0,w5,w6,w2,w4,w3d],[]),([5,w0,w5,w6,w2,w4,w24],[]),([5,w0,w5,w6,w2,w8],[(56,3),(58,3)]),([5,w0,3233860812,w3,w1,w2,w4],[]),([5,w0,3233873919,w3,w1,w2,w4],[]),([5,w0,3234644172,w3,w1,w2,w4],[]),([5,w0,3237986559,w3,w1,w2,w4],[]),([5,w0,3301229764,w3,w1,w2,w4],[]),([5,w0,w5f,w3,w1,w2,w4],[(104,0)]),([5,w0,w80,w3,w1,w2,w4],[(104,0)]),([5,w0,w80,w3,w34,w2,w4],[(80,3),(104,3)]),([5,w0,wa0,w3,w1,w2,w4],[(104,0)]),([5,w0,3368585352,w3,w1,w2,w4],[(104,0)]),([5,w0,w67,w3,w1,w2,w4],[(104,0)]),([5,w0,wf,wc,w1,w2,w4],[]),([5,w0,wf,w3,w1,w2,w4],[(104,0)]),([5,w0,wf,w3,w1,w2,w8],[(104,0)]),([5,w0,wf,w3,w2a,w2,w4],[(80,0),(104,0)]),([5,w0,wf,w3,w6,w2,w4],[]),([5,w0,wf,wd,w1,w2,w4],[(104,4)]),([5,w0,wf,w1,w6,w2,w4],[]),([5,w0,wf,w1,w3b,w2,w4],[]),([5,w0,wf,w1c,w6,w2,w4],[]),([5,w0,wf,w6,w2,w4],[(58,3)]),([5,w0,wa2,w3,w1,w2,w4c],[(80,2),(104,3),(136,1),(176,2)]),([5,w0,wa2,w3,w1,w2,w4],[(104,0)]),([5,w0,3435184320,w3,w1,w2,w4],[(104,0)]),([5,w0,w29,w3,w1,w2,w4c],[(80,2)]),([5,w0,w29,w3,w1,w2,w4],[]),([5,w0,w29,w3,w1,w2,w8],[]),([5,w0,w29,w1,w6,w2,w4],[]),([5,w0,w29,w1,w2,w2f,w4],[(116,2)]),([5,w0,w35,w3,w1,w2,w4],[]),([5,w0,w35,w1,w1c,w2,w4],[(156,4)]),([5,w0,w35,w1,w2,w11,w4],[(116,2)])]
noncomputable def K_18 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w35,w1,w2,4294639610,w4],[]),([5,w0,w35,w1,w2,w4],[]),([5,w0,wc,w3,w6a,w1,w2],[(136,1)]),([5,w0,wc,w3,w6a,w6b,w2],[(80,1),(136,1)]),([5,w0,wc,w3,w8b,w1,w2],[(104,1),(136,1)]),([5,w0,wc,w3,4042309824,w1,w2],[]),([5,w0,wc,w3,w1,w51,w2],[(104,0)]),([5,w0,wc,w3,w1,4210731690,w2],[(104,0)]),([5,w0,wc,w3,w1,w12,w2],[]),([5,w0,wc,w3,w1,w50,w2],[]),([5,w0,wc,w3,w1,w2,w4c],[(80,2),(104,3),(136,1)]),([5,w0,wc,w3,w1,w2,w4],[]),([5,w0,wc,w3,w1,w2,w43],[]),([5,w0,wc,w3,w1,w2,w15],[]),([5,w0,wc,w3,w1,w2,w7b],[(80,1),(176,1)]),([5,w0,wc,w3,w1,w2,w8],[]),([5,w0,wc,w3,w1,w2,w13],[]),([5,w0,wc,w3,w1,w2,we],[]),([5,w0,wc,w3,w1,w2,w2b],[(204,0)]),([5,w0,wc,w3,w1,w26,w4],[]),([5,w0,wc,w3,w1,w10,w4],[]),([5,w0,wc,w3,w1,w62,w4],[(80,1),(176,1)]),([5,w0,wc,w3,w1,w64,w4],[(104,0)]),([5,w0,wc,w28,w1,w2,w4],[(80,2),(176,2)]),([5,w0,wc,w1,w50,w2],[(58,2)]),([5,w0,wc,w1,w50,w2,w4],[]),([5,w0,wc,w1,w6,w2,we],[]),([5,w0,wc,w1,w2,we],[]),([5,w0,3435921612,w3,w1,w2,w4],[]),([5,w0,w8c,w3,w1,w2,w4],[]),([5,w0,3435954304,w3,w1,w2,w4],[]),([5,w0,3435954304,w3,w1,w2,w7b],[(80,1),(176,1)]),([5,w0,w1a,w3,w8b,w1,w2],[(136,1)]),([5,w0,w1a,w3,w1,w2,w4],[]),([5,w0,w1a,w3,w1,w2,w15],[]),([5,w0,w1a,w3,w1,w2,w8],[]),([5,w0,w1a,w3,w1,w2,we],[])]
noncomputable def K_19 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w1a,w3,w1,w2,w2b],[(204,0)]),([5,w0,w1a,wd,w1,w2,w4],[]),([5,w0,w1a,wd,w1,w2,w8],[]),([5,w0,w1a,w1,w2,w4,we],[]),([5,w0,w1a,w1,w2,w4,w2b],[(196,0)]),([5,w0,w1a,w1,w2,w8,we],[]),([5,w0,w1a,w1,w2,w8,w2b],[(196,0)]),([5,w0,w1a,w1,w2,we],[(158,0)]),([5,w0,w1a,w1,w2,w2b],[(156,0),(158,0),(157,0)]),([5,w0,w7e,w3,w1,w2,w4],[]),([5,w0,w1e,w3,w1,w2,w4],[]),([5,w0,w1e,w3,w1,w2,w8],[(196,1)]),([5,w0,w1e,w1,w6,w2,w4],[(188,1)]),([5,w0,w1e,w1,w2,w27,w4],[(108,0)]),([5,w0,w23,w3,w1,w2,w4],[]),([5,w0,w23,w3,w1,w2,w8],[(196,1)]),([5,w0,w23,w1,w1c,w2,w4],[]),([5,w0,w23,w1,w2,w4],[(150,1)]),([5,w0,w23,w1,w2,w4,w8],[(188,1)]),([5,w0,w23,w1,w2,w4,w20],[]),([5,w0,w23,w1,w2,w4,wa1],[]),([5,w0,w23,w1,w2,w8],[(148,1),(150,1),(149,1)]),([5,w0,w23,w1,w2,w8,wa1],[(148,1)]),([5,w0,w5b,w3,w1,w2,w4],[]),([5,w0,w3,w3,w1,w12,w2],[]),([5,w0,w3,w3,w1,w2,w4c],[(64,2),(68,2)]),([5,w0,w3,w3,w1,w2,w4],[]),([5,w0,w3,w3,w1,w2,w15],[]),([5,w0,w3,w3,w1,w2,w7b],[(64,1),(68,1)]),([5,w0,w3,w3,w1,w2,w8],[]),([5,w0,w3,w3,w1,w10,w4],[]),([5,w0,w3,w3,w1,w62,w4],[(64,1),(68,1)]),([5,w0,w3,3435973887,w1,w2,w4],[]),([5,w0,w3,3435978205,w1,w2,w4],[]),([5,w0,w3,3435978205,w1,w2,w8],[])]
noncomputable def K_20 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w3,3435982574,w1,w2,w4],[]),([5,w0,w3,3435986172,w1,w2,w4],[]),([5,w0,w3,w52,w1,w2,w4],[]),([5,w0,w3,w52,w1,w2,w8],[]),([5,w0,w3,3436170447,w1,w2,w4],[]),([5,w0,w3,3437087965,w1,w2,w4],[]),([5,w0,w3,3438202094,w1,w2,w4],[]),([5,w0,w3,3439119612,w1,w2,w4],[]),([5,w0,w3,3439263744,w1,w2,w4],[]),([5,w0,w3,3439263999,w1,w2,w4],[]),([5,w0,w3,3439316172,w1,w2,w4],[]),([5,w0,w3,w4d,w1,w2,w4],[]),([5,w0,w3,w4d,w1,w2,w8],[]),([5,w0,w3,3439329279,w1,w2,w4],[]),([5,w0,w3,3489648639,w1,w2,w4],[]),([5,w0,w3,3587560917,w1,w2,w4],[]),([5,w0,w3,3705461980,w1,w2,w4],[]),([5,w0,w3,w78,w44,w1,w2],[]),([5,w0,w3,w78,w1,w2],[]),([5,w0,w3,w78,w1,w2,w4],[]),([5,w0,w3,3722270037,w1,w2,w4],[]),([5,w0,w3,w8e,w1,w2,w4],[]),([5,w0,w3,w44,w1,w2,w4],[]),([5,w0,w3,w44,w1,w2,w8],[]),([5,w0,w3,3722313727,w1,w2,w4],[]),([5,w0,w3,3724533247,w1,w2,w4],[(116,1)]),([5,w0,w3,w22,w1,w2,w4],[]),([5,w0,w3,3938511552,w1,w2,w4],[(80,4),(104,3),(112,3)]),([5,w0,w3,w68,w1,w2,w4],[]),([5,w0,w3,w5e,w1,w2,w4],[]),([5,w0,w3,w38,w1,w2,w4],[(104,3)]),([5,w0,w3,w1b,w1,w2,w4],[(104,3)]),([5,w0,w3,w1b,w1,w2,w8],[(104,3)]),([5,w0,w3,w1b,w6,w2,w4],[(104,3)]),([5,w0,w3,3972852940,w1,w2,w4],[(80,2)]),([5,w0,w3,3974889472,w1,w2,w4],[(80,2)]),([5,w0,w3,3974930592,w1,w2,w4],[(80,2),(184,1)]),([5,w0,w3,w85,w1,w2,w4],[(80,2)]),([5,w0,w3,w28,w1,w2,w4],[(80,2)])]
noncomputable def K_21 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w3,w28,w1,w2,w7b],[(80,2),(84,1)]),([5,w0,w3,w28,w1,w2,w8],[(80,2)]),([5,w0,w3,w28,w1,w62,w4],[(80,1),(84,1)]),([5,w0,w3,w28,w1c,w2,w4],[(80,3)]),([5,w0,w3,4007718624,w1,w2,w4],[(80,2),(156,2)]),([5,w0,w3,4008373994,w1,w2,w4],[]),([5,w0,w3,4008505068,w1,w2,w4],[(80,2)]),([5,w0,w3,w19,w1,w2,w4],[]),([5,w0,w3,w19,w1,w2,w8],[]),([5,w0,w3,w19,w1,w2,we],[]),([5,w0,w3,w19,w1,w2,w2b],[(196,1),(204,3)]),([5,w0,w3,w45,w1,w2,w4],[]),([5,w0,w3,w45,w1,w2,w8],[]),([5,w0,w3,w45,w1,w2,we],[]),([5,w0,w3,w1d,w1,w2,w4],[]),([5,w0,w3,w1d,w1,w2,w8],[]),([5,w0,w3,4008632544,w1,w2,w4],[]),([5,w0,w3,4008635114,w1,w2,w4],[]),([5,w0,w3,4008635628,w1,w2,w4],[]),([5,w0,w3,wd,w1,w12,w2],[(116,1)]),([5,w0,w3,wd,w1,w48,w2],[(116,1)]),([5,w0,w3,wd,w1,w2,w4c],[(76,2),(84,2)]),([5,w0,w3,wd,w1,w2,w4],[]),([5,w0,w3,wd,w1,w2,w15],[]),([5,w0,w3,wd,w1,w2,w7b],[(76,1),(84,1)]),([5,w0,w3,wd,w1,w2,w8],[]),([5,w0,w3,wd,w1,w10,w4],[(80,2)]),([5,w0,w3,wd,w1,w62,w4],[(76,1),(84,1)]),([5,w0,w3,4008640511,w1,w2,w4],[]),([5,w0,w3,4009750271,w1,w2,w4],[]),([5,w0,w3,w1,w8f,w59,w2],[]),([5,w0,w3,w1,w8f,w2],[(105,2)]),([5,w0,w3,w1,w8f,w2,w4],[(104,2)]),([5,w0,w3,w1,wa3,w2,w4],[(104,2)]),([5,w0,w3,w1,4241289216,w2,w4],[]),([5,w0,w3,w1,w59,w2,w4],[]),([5,w0,w3,w1,w59,w2,w8],[]),([5,w0,w3,w1,w8a,w2,w4],[(116,1)])]
noncomputable def K_22 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w3,w1,w12,w12,w2],[]),([5,w0,w3,w1,w12,w50,w2],[]),([5,w0,w3,w1,w12,w6,w2],[]),([5,w0,w3,w1,w12,w61,w2],[]),([5,w0,w3,w1,w12,w3b,w2],[(204,3)]),([5,w0,w3,w1,w12,w2],[]),([5,w0,w3,w1,w12,w2,w27],[(140,0)]),([5,w0,w3,w1,w12,w2,4294770432],[(156,3)]),([5,w0,w3,w1,w12,w2,w2f],[]),([5,w0,w3,w1,w12,w2,w4],[]),([5,w0,w3,w1,w12,w2,w8],[]),([5,w0,w3,w1,w12,w2,we],[]),([5,w0,w3,w1,w12,w2,w3d],[]),([5,w0,w3,w1,w12,w2,w24],[]),([5,w0,w3,w1,w47,w6,w2],[]),([5,w0,w3,w1,w47,w2],[(58,2),(74,0),(85,1)]),([5,w0,w3,w1,w47,w2,w4],[]),([5,w0,w3,w1,w47,w2,w8],[]),([5,w0,w3,w1,w50,w2,w4],[]),([5,w0,w3,w1,w50,w2,w8],[]),([5,w0,w3,w1,w6d,w2,w4],[(116,1)]),([5,w0,w3,w1,w6d,w2,w8],[(116,1)]),([5,w0,w3,w1,4244438016,w2,w4],[]),([5,w0,w3,w1,4244438220,w2,w4],[]),([5,w0,w3,w1,w6,w48,w2],[]),([5,w0,w3,w1,w6,w61,w2],[]),([5,w0,w3,w1,w6,w2,w46],[]),([5,w0,w3,w1,w6,w2,w4],[]),([5,w0,w3,w1,w6,w2,4294902531],[(108,3),(116,3)]),([5,w0,w3,w1,w6,w2,w15],[]),([5,w0,w3,w1,w6,w2,w70],[]),([5,w0,w3,w1,w6,w2,w63],[(108,3),(116,3)]),([5,w0,w3,w1,w6,w2,w8],[]),([5,w0,w3,w1,w6,w10,w4],[]),([5,w0,w3,w1,w6,w4e,w4],[]),([5,w0,w3,w1,4244439039,w2,w4],[]),([5,w0,w3,w1,4244634879,w2,w4],[]),([5,w0,w3,w1,4261281277,w2,w4],[])]
noncomputable def K_23 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w3,w1,4277075694,w2,w4],[(116,1),(156,3)]),([5,w0,w3,w1,wa4,w2,w4],[(156,3)]),([5,w0,w3,w1,w48,w3b,w2],[(204,3)]),([5,w0,w3,w1,w48,w2],[]),([5,w0,w3,w1,w48,w2,w4],[]),([5,w0,w3,w1,w61,w2],[(129,3)]),([5,w0,w3,w1,w61,w2,w4],[]),([5,w0,w3,w1,4278111436,w2,w4],[]),([5,w0,w3,w1,4278120174,w2,w4],[(116,1),(156,3)]),([5,w0,w3,w1,4278123772,w2,w4],[]),([5,w0,w3,w1,w3b,w2,w4],[(156,3)]),([5,w0,w3,w1,w3b,w2,w8],[(156,3)]),([5,w0,w3,w1,w2,w46],[]),([5,w0,w3,w1,w2,w46,w2f],[]),([5,w0,w3,w1,w2,w46,w4],[]),([5,w0,w3,w1,w2,wa5,w4],[]),([5,w0,w3,w1,w2,4294769916,w4],[]),([5,w0,w3,w1,w2,w2f,w4],[]),([5,w0,w3,w1,w2,w2f,w8],[]),([5,w0,w3,w1,w2,4294901758,w4],[]),([5,w0,w3,w1,w2,w4],[]),([5,w0,w3,w1,w2,w4,w4],[]),([5,w0,w3,w1,w2,w4,w90],[]),([5,w0,w3,w1,w2,w4,w8d],[]),([5,w0,w3,w1,w2,w4,w79],[]),([5,w0,w3,w1,w2,w4,4294901964],[]),([5,w0,w3,w1,w2,w4,w43],[]),([5,w0,w3,w1,w2,w4,4294905855],[]),([5,w0,w3,w1,w2,w4,w77],[]),([5,w0,w3,w1,w2,w4,w16],[]),([5,w0,w3,w1,w2,w4,4294923775],[(188,1)]),([5,w0,w3,w1,w2,w4,w3e],[]),([5,w0,w3,w1,w2,w4,w15],[]),([5,w0,w3,w1,w2,w4,w70],[]),([5,w0,w3,w1,w2,w4,w8],[]),([5,w0,w3,w1,w2,w4,4294945535],[])]
noncomputable def K_24 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w3,w1,w2,w4,w49],[]),([5,w0,w3,w1,w2,w4,w13],[]),([5,w0,w3,w1,w2,w4,4294953160],[]),([5,w0,w3,w1,w2,w4,w81],[]),([5,w0,w3,w1,w2,w4,we],[]),([5,w0,w3,w1,w2,w4,4294954239],[(188,1)]),([5,w0,w3,w1,w2,w4,w9c],[]),([5,w0,w3,w1,w2,w4,w91],[(188,1),(196,3)]),([5,w0,w3,w1,w2,w4,4294962412],[(188,1)]),([5,w0,w3,w1,w2,w4,w2b],[(188,1),(196,3)]),([5,w0,w3,w1,w2,w4,4294966476],[]),([5,w0,w3,w1,w2,w4,w3d],[]),([5,w0,w3,w1,w2,w4,4294967038],[(196,3)]),([5,w0,w3,w1,w2,w4,4294967292],[]),([5,w0,w3,w1,w2,w4,w2c],[]),([5,w0,w3,w1,w2,w90],[]),([5,w0,w3,w1,w2,w79],[]),([5,w0,w3,w1,w2,w43,w8],[]),([5,w0,w3,w1,w2,w43,w24],[]),([5,w0,w3,w1,w2,w16,w8],[]),([5,w0,w3,w1,w2,w3e],[]),([5,w0,w3,w1,w2,w15],[]),([5,w0,w3,w1,w2,w15,w15],[]),([5,w0,w3,w1,w2,w15,w8],[]),([5,w0,w3,w1,w2,w15,we],[]),([5,w0,w3,w1,w2,w15,w20],[]),([5,w0,w3,w1,w2,w15,4294965496],[]),([5,w0,w3,w1,w2,w70],[]),([5,w0,w3,w1,w2,w8],[]),([5,w0,w3,w1,w2,w8,w8],[]),([5,w0,w3,w1,w2,w8,4294945535],[]),([5,w0,w3,w1,w2,w8,w13],[(148,1)]),([5,w0,w3,w1,w2,w8,we],[]),([5,w0,w3,w1,w2,w8,w91],[(148,1),(188,1),(196,3)])]
noncomputable def K_25 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w3,w1,w2,w8,w2b],[(188,1),(196,3)]),([5,w0,w3,w1,w2,w8,w3d],[]),([5,w0,w3,w1,w2,w8,4294967038],[(196,3)]),([5,w0,w3,w1,w2,w8,w2c],[]),([5,w0,w3,w1,w2,w49],[]),([5,w0,w3,w1,w2,w13,w24],[]),([5,w0,w3,w1,4278255615,w4,w24],[]),([5,w0,w3,w1,4279238415,w11,w4],[(116,2)]),([5,w0,w3,w1,4283826005,w18,w4],[]),([5,w0,w3,w1,w39,w4],[]),([5,w0,w3,w1,4287102976,w10,w4],[]),([5,w0,w3,w1,w26,w4],[]),([5,w0,w3,w1,w10,w10,w4],[]),([5,w0,w3,w1,w10,w18,w4],[]),([5,w0,w3,w1,w10,w27,w4],[(108,0)]),([5,w0,w3,w1,w10,w11,w4],[(116,2)]),([5,w0,w3,w1,w10,4294508536,w4],[(116,2)]),([5,w0,w3,w1,w10,w4],[(58,2)]),([5,w0,w3,w1,w10,w4,w4],[]),([5,w0,w3,w1,w10,w4,w15],[]),([5,w0,w3,w1,w10,w4,w8],[(56,2)]),([5,w0,w3,w1,w10,w4,we],[]),([5,w0,w3,w1,w10,w4,w20],[]),([5,w0,w3,w1,w10,w4,w24],[(180,0)]),([5,w0,w3,w1,w10,w4,4294967176],[(180,0)]),([5,w0,w3,w1,w10,w15],[(56,2),(58,2)]),([5,w0,w3,w1,w10,w8],[(56,2),(58,2)]),([5,w0,w3,w1,w4e,w4],[(58,2),(74,0)]),([5,w0,w3,w1,w5a,w27,w4],[(108,0)]),([5,w0,w3,w1,w18,w5c,w4],[(108,0),(116,2)]),([5,w0,w3,w1,w18,w65,w27],[(108,0)]),([5,w0,w3,w1,w18,w83,w4],[(108,0)]),([5,w0,w3,w1,w18,w27,w4],[(108,0)])]
noncomputable def K_26 : List (List ℕ × List (ℕ × ℕ)) := [([5,w0,w3,w1,w18,w27,w8],[(56,1),(132,0),(108,0)]),([5,w0,w3,w1,w18,w2f,w4],[]),([5,w0,w3,w1,w64,w4],[]),([5,w0,w3,w1,w5c,w4,w24],[]),([5,w0,w3,w1,w83,w11,w4],[(116,2),(204,1)]),([5,w0,w3,w2a,w10,w4],[(56,1),(58,1)]),([5,w0,w3,w36,w11,w4],[(101,2)]),([5,w0,w3,w34,w18,w4],[]),([5,w0,w3,w1c,w18,w11,w4],[(156,0)]),([5,w1f,w3,w1,w2,w4,w8],[]),([5,w1f,w3,w1,w2,w8],[]),([5,w40,w3,w1,w2,w18,w4],[]),([5,w2e,w3,w22,w1,w2,w4],[]),([5,w37,w3,w5e,w1,w2,w4],[]),([5,w5,w3,w22,w1,w2,w4],[]),([5,w5,w3,w5e,w1,w2,w4],[]),([5,w5,w3,w1b,w1,w2,w8],[]),([5,wc,w3,w5e,w1,w2,w4],[]),([5,w3,w22,w1,w2,w4],[]),([5,w3,w5e,w1,w2,w4],[(158,3)]),([5,w3,w1b,w1,w2,w18,w4],[(72,3)]),([5,w3,w1b,w1,w2,w4,w8],[(72,3)]),([5,w3,w1b,w1,w2,w8],[(72,3),(73,1),(149,1)]),([5,w3,w45,w1,w1c,w2,w4],[]),([5,w3,wd,w1,w1c,w2,w8],[(72,3),(84,1)]),([6,0,65535,w0,w3,w1,w2],[]),([6,0,65535,w0,w3,w1,w2,w4],[]),([6,0,w9,w0,w3,w1,w2,w4],[])]
noncomputable def K_27 : List (List ℕ × List (ℕ × ℕ)) := [([6,0,w9,w0,w3,w1,w4],[]),([6,0,wb,w0,w3,w1,w2,w4],[]),([6,0,wb,w3,w1,w2,w4],[]),([6,0,w0,w3,w1,w2,w4],[(97,1),(129,3)]),([6,255,w0,w3,w1,w2,w4],[(2,3),(97,1),(101,1),(129,3)]),([6,255,w0,w3,w1,w2,w4,w24],[]),([6,21845,w0,w3,w1,w2],[(10,2),(14,0)]),([6,21845,w0,w3,w1,w2,w4],[(97,1),(101,1),(129,3),(133,3)]),([6,21845,w0,w3,w1,w2,w4,w8],[]),([6,21845,w0,w3,w1,w2,w8],[(97,1),(101,1),(129,3),(133,3)]),([6,43690,65535,w0,w3,w1,w2],[]),([6,43690,65535,w0,w3,w1,w2,w4],[]),([6,43690,w0,w3,w1,w2,w4],[(97,1),(101,1),(129,3),(133,3)]),([6,52428,65535,w0,w3,w1,w2],[])]
noncomputable def K_28 : List (List ℕ × List (ℕ × ℕ)) := [([6,52428,65535,w0,w3,w1,w2,w4],[]),([6,52428,w0,w3,w1,w2,w4],[(2,2),(97,1),(129,3),(133,0)]),([6,65535,65535,w0,w3,w1,w2],[]),([6,65535,65535,w0,w3,w1,w2,w4],[]),([6,65535,w9,w0,w3,w1],[(14,1)]),([6,65535,w9,w0,w3,w1,w2],[]),([6,65535,w9,w0,w3,w1,w2,w4],[]),([6,65535,w9,w0,w3,w1,w4],[]),([6,65535,wb,w0,w3,w1,w2],[]),([6,65535,wb,w0,w3,w1,w2,w4],[]),([6,65535,wb,w3,w1,w2],[(10,2),(14,0)]),([6,65535,wb,w3,w1,w2,w4],[]),([6,65535,wa,w0,w3,w1,w2],[(136,0)]),([6,65535,wa,w0,w3,w1,w2,w4],[(136,0)])]
noncomputable def K_29 : List (List ℕ × List (ℕ × ℕ)) := [([6,65535,w7,w0,w3,w1,w2],[]),([6,65535,w7,w0,w3,w1,w2,w4],[]),([6,65535,w0,w0,w3,w1,w2],[]),([6,65535,w0,w0,w3,w1,w2,w4],[]),([6,65535,w0,w1f,w3,w1,w2],[]),([6,65535,w0,w1f,w3,w1,w2,w4],[]),([6,65535,w0,w5,w3,w1,w2],[]),([6,65535,w0,w5,w3,w1,w2,w4],[]),([6,65535,w0,wc,w3,w1,w2],[]),([6,65535,w0,wc,w3,w1,w2,w4],[]),([6,65535,w0,w3,w3,w1,w2],[]),([6,65535,w0,w3,w3,w1,w2,w4],[]),([6,65535,w0,w3,w52,w1,w2],[]),([6,65535,w0,w3,w52,w1,w2,w4],[]),([6,65535,w0,w3,wd,w1,w2],[])]
noncomputable def K_30 : List (List ℕ × List (ℕ × ℕ)) := [([6,65535,w0,w3,wd,w1,w2,w4],[]),([6,65535,w0,w3,w1,w6,w2],[]),([6,65535,w0,w3,w1,w6,w2,w4],[]),([6,65535,w0,w3,w1,w2],[(10,2),(14,0)]),([6,65535,w0,w3,w1,w2,w4],[(97,1),(101,1),(129,3),(133,3)]),([6,65535,w0,w3,w1,w2,w4,w4],[]),([6,65535,w0,w3,w1,w2,w4,w8],[]),([6,65535,w0,w3,w1,w2,w4,we],[(72,2)]),([6,65535,w0,w3,w1,w2,w4,w2c],[]),([6,65535,w0,w3,w1,w2,w8],[(97,1),(101,1),(129,3),(133,3)]),([6,65535,w0,w3,w1,w2,we],[]),([6,65535,w0,w3,w1,w2,w2c],[]),([6,w53,w0,w3,w1,w2,w11,w4],[(96,0),(216,2)]),([6,w53,w0,w3,w1,w2,w4],[(2,2),(97,1),(129,3)]),([6,w54,w0,w3,w1,w2,w18,w4],[]),([6,w54,w0,w3,w1,w2,w4],[(2,3),(97,1),(101,1),(129,3)])]
noncomputable def K_31 : List (List ℕ × List (ℕ × ℕ)) := [([6,w3f,w9,w0,w3,w1,w2,w4],[]),([6,w3f,w9,w0,w3,w1,w4],[]),([6,w3f,w0,w3,w1,w2,w4],[(2,3),(97,1),(101,1),(129,3)]),([6,w41,w9,w0,w3,w1,w2,w4],[]),([6,w41,w9,w0,w3,w1,w4],[]),([6,w41,w0,w3,w1,w2,w4],[(2,4),(97,1),(129,0)]),([6,w42,w9,w0,w3,w1,w2,w4],[]),([6,w42,w9,w0,w3,w1,w4],[]),([6,w42,w0,w3,w1,w2,w4],[(2,3),(97,1),(101,1),(129,3)]),([6,w9,w9,w0,w3,w1,w2,w4],[]),([6,w9,w9,w0,w3,w1,w4],[]),([6,w9,w4b,w0,w3,w1,w2,w4],[]),([6,w9,w4b,w0,w3,w1,w4],[(2,0)]),([6,w9,w4b,w0,w3,w4],[(2,0)])]
noncomputable def K_32 : List (List ℕ × List (ℕ × ℕ)) := [([6,w9,wb,w0,w3,w1,w2,w4],[]),([6,w9,wb,w0,w3,w1,w4],[]),([6,w9,wb,w3,w1,w2,w4],[]),([6,w9,wb,w3,w1,w4],[(10,1)]),([6,w9,wa,w0,w3,w1,w2,w4],[]),([6,w9,wa,w0,w3,w1,w4],[]),([6,w9,w55,w0,w3,w1,w2,w4],[(104,1)]),([6,w9,w55,w0,w3,w1,w4],[(2,3),(104,1)]),([6,w9,w7,w0,w3,w1,w2,w4],[]),([6,w9,w7,w0,w3,w1,w4],[]),([6,w9,w0,w0,w3,w1,w2,w4],[]),([6,w9,w0,w0,w3,w1,w4],[]),([6,w9,w0,w40,w3,w1,w2,w4],[]),([6,w9,w0,w40,w3,w1,w4],[]),([6,w9,w0,w5,w3,w1,w2,w4],[])]
noncomputable def K_33 : List (List ℕ × List (ℕ × ℕ)) := [([6,w9,w0,w5,w3,w1,w4],[]),([6,w9,w0,w5d,w3,w1,w2,w4],[]),([6,w9,w0,w5d,w3,w1,w4],[(2,0)]),([6,w9,w0,wc,w3,w1,w2,w4],[]),([6,w9,w0,wc,w3,w1,w4],[]),([6,w9,w0,w3,w3,w1,w2,w4],[]),([6,w9,w0,w3,w3,w1,w4],[]),([6,w9,w0,w3,w4d,w1,w2,w4],[]),([6,w9,w0,w3,w4d,w1,w4],[]),([6,w9,w0,w3,wd,w1,w2,w4],[]),([6,w9,w0,w3,wd,w1,w4],[]),([6,w9,w0,w3,w1,w6,w2,w4],[]),([6,w9,w0,w3,w1,w6,w4],[]),([6,w9,w0,w3,w1,w4a,w2,w4],[]),([6,w9,w0,w3,w1,w4a,w4],[(2,3)])]
noncomputable def K_34 : List (List ℕ × List (ℕ × ℕ)) := [([6,w9,w0,w3,w1,w2,w2,w4],[]),([6,w9,w0,w3,w1,w2,w18,w4],[]),([6,w9,w0,w3,w1,w2,w27,w4],[(72,2)]),([6,w9,w0,w3,w1,w2,w4],[(2,3),(97,1),(101,1)]),([6,w9,w0,w3,w1,w2,w4,w4],[]),([6,w9,w0,w3,w1,w2,w4,w43],[]),([6,w9,w0,w3,w1,w2,w4,w8],[]),([6,w9,w0,w3,w1,w2,w4,we],[]),([6,w9,w0,w3,w1,w2,w4,w24],[]),([6,w9,w0,w3,w1,w2,w4,w2c],[]),([6,w9,w0,w3,w1,w2,w8],[(2,3),(97,1),(101,1)]),([6,w9,w0,w3,w1,w18,w4],[(2,3)]),([6,w9,w0,w3,w1,w27,w4],[(2,0)]),([6,w9,w0,w3,w1,w4],[(10,1)]),([6,w9,w0,w3,w1,w4,w4],[]),([6,w9,w0,w3,w1,w4,w43],[])]
noncomputable def K_35 : List (List ℕ × List (ℕ × ℕ)) := [([6,w9,w0,w3,w1,w4,w8],[]),([6,w9,w0,w3,w1,w4,we],[]),([6,w9,w0,w3,w1,w4,w24],[(2,3)]),([6,w9,w0,w3,w1,w4,w2c],[]),([6,w9,w0,w3,w1,w8],[(10,1)]),([6,w66,w0,w3,w1,w4a,w2,w4],[(172,3)]),([6,w66,w0,w3,w1,w2,w4],[(2,3),(97,1),(101,1),(133,3)]),([6,w56,w0,w3,w3c,w1,w2,w4],[(132,1),(172,3)]),([6,w56,w0,w3,w1,w2,w4],[(2,2),(101,1),(133,3)]),([6,w30,wb,w0,w3,w1,w2,w4],[]),([6,w30,wb,w3,w1,w2,w4],[]),([6,w30,w0,w3,w1,w2,w4],[(2,2),(97,1),(129,3),(133,0),(145,0)]),([6,w17,wb,w0,w3,w1,w2],[(137,1),(141,1),(177,3),(181,3)]),([6,w17,wb,w0,w3,w1,w2,w4],[])]
noncomputable def K_36 : List (List ℕ × List (ℕ × ℕ)) := [([6,w17,wb,w3,w1,w2],[(10,2),(14,0)]),([6,w17,wb,w3,w1,w2,w4],[]),([6,w17,w0,w3,w1,w2],[(99,1),(103,1),(131,3),(135,3),(107,1),(111,1),(139,3),(143,3),(10,2),(11,2),(147,0),(151,0),(13,1),(14,0),(15,0),(155,2),(159,2),(17,3)]),([6,w17,w0,w3,w1,w2,w4],[(97,1),(101,1),(129,3),(133,3),(194,1),(198,1),(202,3),(206,3)]),([6,wb,wb,w0,w3,w1,w2,w4],[]),([6,wb,wb,w3,w1,w2,w4],[]),([6,wb,wa,w0,w3,w1,w2,w4],[(136,0)]),([6,wb,wa,w3,w1,w2,w4],[(104,0)]),([6,wb,w7,w0,w3,w1,w2,w4],[]),([6,wb,w7,w3,w1,w2,w4],[]),([6,wb,w0,w0,w3,w1,w2,w4],[]),([6,wb,w0,w5,w3,w1,w2,w4],[]),([6,wb,w0,wc,w3,w1,w2,w4],[]),([6,wb,w0,w3,w3,w1,w2,w4],[]),([6,wb,w0,w3,w44,w1,w2,w4],[]),([6,wb,w0,w3,wd,w1,w2,w4],[(72,2)]),([6,wb,w0,w3,w1,w6,w2,w4],[(100,1)])]
noncomputable def K_37 : List (List ℕ × List (ℕ × ℕ)) := [([6,wb,w0,w3,w1,w2,w4],[(97,1),(101,1),(129,3),(133,3)]),([6,wb,w0,w3,w1,w2,w4,w4],[]),([6,wb,w0,w3,w1,w2,w4,w16],[]),([6,wb,w0,w3,w1,w2,w4,w8],[]),([6,wb,w0,w3,w1,w2,w4,we],[]),([6,wb,w0,w3,w1,w2,w4,w2c],[]),([6,wb,w0,w3,w1,w2,w8],[(97,1),(101,1),(129,3),(133,3)]),([6,wb,w5,w3,w1,w2,w4],[]),([6,wb,wc,w3,w1,w2,w4],[]),([6,wb,w3,w3,w1,w2,w4],[]),([6,wb,w3,w44,w1,w2,w4],[]),([6,wb,w3,wd,w1,w2,w4],[]),([6,wb,w3,w1,w6,w2,w4],[]),([6,wb,w3,w1,w2,w4],[(6,2),(10,0)])]
noncomputable def K_38 : List (List ℕ × List (ℕ × ℕ)) := [([6,wb,w3,w1,w2,w4,w4],[]),([6,wb,w3,w1,w2,w4,w16],[]),([6,wb,w3,w1,w2,w4,w8],[]),([6,wb,w3,w1,w2,w4,we],[]),([6,wb,w3,w1,w2,w4,w2c],[]),([6,wb,w3,w1,w2,w8],[(6,2),(10,0)]),([6,w3a,w7,w0,w3,w1,w2,w4],[]),([6,w3a,w0,w3,w1,w2,w4],[(97,1),(101,1),(129,3),(133,3)]),([6,w57,w55,w0,w3,w1,w2,w4],[(132,1),(172,3),(104,1)]),([6,w57,w0,w3,w1,w2,w4],[(2,3),(97,1),(100,1),(102,1),(101,1),(133,3)]),([6,w31,wa,w0,w3,w1,w2,w4],[]),([6,w31,w0,w5,w3,w1,w2,w4],[]),([6,w31,w0,w3,w1,w2,w4],[(2,3),(97,1),(129,3)]),([6,w25,wa,w0,w3,w1,w2,w4],[(128,0),(136,0)]),([6,w25,w7,w0,w3,w1,w2,w4],[(128,0)])]
noncomputable def K_39 : List (List ℕ × List (ℕ × ℕ)) := [([6,w25,w0,wc,w3,w1,w2,w4],[(128,0)]),([6,w25,w0,w3,w1,w2,w4],[(2,2),(96,0),(98,0),(97,1),(129,3),(133,0)]),([6,wa,wa,w0,w3,w1,w2,w4],[(128,0)]),([6,wa,w7d,w0,w3,w1,w2,w4],[(72,1),(96,1),(128,1),(168,1),(216,1)]),([6,wa,w7,w0,w3,w1,w2,w4],[(128,0)]),([6,wa,w0,w0,w3,w1,w2,w4],[(128,0)]),([6,wa,w0,w5,w3,w1,w2,w4],[]),([6,wa,w0,wc,w3,w1,w2,w4],[(128,0)]),([6,wa,w0,w3,w3,w1,w2,w4],[(128,0)]),([6,wa,w0,w3,wd,w1,w2,w4],[(128,0)]),([6,wa,w0,w3,w3c,w1,w2,w4],[(56,2),(72,2),(96,2),(128,4),(168,2),(216,2)]),([6,wa,w0,w3,w6a,w1,w2,w4],[(56,1),(72,1),(96,1),(128,1),(168,1),(216,1)]),([6,wa,w0,w3,w1,w1,w2,w4],[(56,1),(72,1),(96,1),(168,1),(216,1)]),([6,wa,w0,w3,w1,w2a,w2,w4],[(56,1),(72,1),(96,0),(128,1),(168,1),(216,1),(152,0)]),([6,wa,w0,w3,w1,w1c,w2,w4],[(56,1),(72,1),(96,0),(128,1),(168,1),(216,1)]),([6,wa,w0,w3,w1,w6,w2,w4],[(96,0)]),([6,wa,w0,w3,w1,w2,w11,w4],[(56,2),(72,2),(96,0),(168,2),(216,2)]),([6,wa,w0,w3,w1,w2,w4],[(2,2),(96,0),(98,0),(97,1),(129,3),(133,0)]),([6,wa,w0,w3,w1,w2,w4,w4],[(96,0)]),([6,wa,w0,w3,w1,w2,w4,w15],[(96,0)]),([6,wa,w0,w3,w1,w2,w4,w8],[(96,0)]),([6,wa,w0,w3,w1,w2,w4,we],[(96,0)])]
noncomputable def K_40 : List (List ℕ × List (ℕ × ℕ)) := [([6,wa,w0,w3,w1,w2,w4,w20],[(56,1),(72,1),(96,0),(216,1)]),([6,wa,w0,w3,w1,w2,w15],[(2,2),(96,0),(98,0),(97,1),(129,3),(133,0)]),([6,wa,w0,w3,w1,w2,w8],[(2,2),(96,0),(98,0),(97,1),(129,3),(133,0)]),([6,wa,w0,w3,w1,w10,w4],[(2,2),(97,1)]),([6,wa,w0,wd,w1,w2,w4],[(96,4),(98,0),(97,1),(128,2),(129,3)]),([6,wa,w3,wd,w1,w2,w4],[(6,2)]),([6,wa,wd,w1,w2,w4],[(2,2),(74,0),(6,2),(10,0)]),([6,w14,w0,w3,w1,w6,w2,w4],[(72,2),(96,0)]),([6,w14,w0,w3,w1,w2,w4],[(2,3),(72,2),(74,1),(96,0),(97,1),(101,1),(129,3),(133,3),(80,1),(82,1),(141,3)]),([6,w7,w7,w0,w3,w1,w2,w4],[]),([6,w7,w0,w0,w3,w1,w2,w4],[]),([6,w7,w0,w5,w3,w1,w2,w4],[]),([6,w7,w0,wc,w3,w1,w2,w4],[]),([6,w7,w0,w3,w3,w1,w2,w4],[]),([6,w7,w0,w3,w1d,w1,w2,w4],[]),([6,w7,w0,w3,wd,w1,w2,w4],[]),([6,w7,w0,w3,w1,w6,w2,w4],[(72,2),(96,0)])]
noncomputable def K_41 : List (List ℕ × List (ℕ × ℕ)) := [([6,w7,w0,w3,w1,w2,w4],[(97,1),(101,1),(129,3),(133,3)]),([6,w7,w0,w3,w1,w2,w4,w4],[]),([6,w7,w0,w3,w1,w2,w4,w8],[]),([6,w7,w0,w3,w1,w2,w4,we],[]),([6,w7,w0,w3,w1,w2,w8],[(97,1),(101,1),(129,3),(133,3)]),([6,w7,w3,w1,w2,w4,w8],[]),([6,w7,w3,w1,w2,w8],[(6,2),(10,0)]),([6,w32,w0,w3,w1,w2,w4],[(2,2),(97,1),(101,1),(129,3),(133,3)]),([6,w32,w0,w3,w1,w2,w4,we],[]),([6,w0,w0,w0,w3,w1,w2,w4],[]),([6,w0,w0,w5,w3,w1,w2,w4],[]),([6,w0,w0,wc,w3,w1,w2,w4],[]),([6,w0,w0,w3,w3,w1,w2,w4],[]),([6,w0,w0,w3,wd,w1,w2,w4],[]),([6,w0,w0,w3,w1,w6,w2,w4],[(72,2),(96,0)]),([6,w0,w0,w3,w1,w2,w4],[(97,1),(101,1),(129,3),(133,3)]),([6,w0,w0,w3,w1,w2,w4,w4],[])]
noncomputable def K_42 : List (List ℕ × List (ℕ × ℕ)) := [([6,w0,w0,w3,w1,w2,w4,w8],[]),([6,w0,w0,w3,w1,w2,w4,we],[]),([6,w0,w0,w3,w1,w2,w8],[(97,1),(101,1),(129,3),(133,3)]),([6,w0,w1f,w3,w1,w2],[(10,2),(14,0)]),([6,w0,w1f,w3,w1,w2,w4],[(105,1),(109,1),(137,3),(141,3)]),([6,w0,w40,w3,w1,w2,w4],[(6,3),(105,1),(109,1),(141,3)]),([6,w0,w2e,w5,w3,w1,w2,w4],[]),([6,w0,w2e,w3,w1,w2,w4],[(105,1),(137,3)]),([6,w0,w37,w5,w3,w1,w2,w4],[]),([6,w0,w37,wc,w3,w1,w2,w4],[]),([6,w0,w37,w3,w1,w2,w4],[(6,3),(105,1),(137,3)]),([6,w0,w5,w5,w3,w1,w2,w4],[]),([6,w0,w5,w5d,w3,w1,w2,w4],[(104,0),(136,0),(176,0),(152,0)]),([6,w0,w5,wc,w3,w1,w2,w4],[]),([6,w0,w5,w3,w3,w1,w2,w4],[]),([6,w0,w5,w3,w1b,w1,w2,w4],[]),([6,w0,w5,w3,wd,w1,w2,w4],[]),([6,w0,w5,w3,w1,w6,w2,w4],[(84,1),(144,1)])]
noncomputable def K_43 : List (List ℕ × List (ℕ × ℕ)) := [([6,w0,w5,w3,w1,w4a,w2,w4],[(80,3),(104,3),(136,3)]),([6,w0,w5,w3,w1,w2,w2,w4],[(80,3),(104,3),(136,3)]),([6,w0,w5,w3,w1,w2,w18,w4],[(80,3),(104,3),(176,3),(196,1)]),([6,w0,w5,w3,w1,w2,w5c,w4],[(80,3),(104,3),(176,3)]),([6,w0,w5,w3,w1,w2,w27,w4],[(80,0),(104,0),(176,0)]),([6,w0,w5,w3,w1,w2,w4],[(6,3),(105,1),(137,3),(113,1)]),([6,w0,w5,w3,w1,w2,w4,w4],[]),([6,w0,w5,w3,w1,w2,w4,w8],[(244,1)]),([6,w0,w5,w3,w1,w2,w4,w13],[]),([6,w0,w5,w3,w1,w2,w4,we],[]),([6,w0,w5,w3,w1,w2,w4,w24],[(80,3),(104,3),(224,3)]),([6,w0,w5,w3,w1,w2,w8],[(6,3),(105,1),(137,3),(113,1),(197,1)]),([6,w0,w5,w3,w6,w2,w4],[(10,2),(149,0)]),([6,w0,w5,w6,w2,w4],[(58,3),(103,3),(6,3),(7,3),(10,3),(11,3)]),([6,w0,wf,w3,w1,w1c,w2,w4],[(80,1),(104,0),(136,1)]),([6,w0,wf,w3,w1,w2,w4],[(6,4),(104,0),(105,1),(137,3),(141,0),(149,0)]),([6,w0,w29,w3,w1,w2,w11,w4],[(80,2),(176,2),(156,2)]),([6,w0,w29,w3,w1,w2,w4],[(6,2),(105,1),(137,3),(141,0),(145,0)])]
noncomputable def K_44 : List (List ℕ × List (ℕ × ℕ)) := [([6,w0,wc,wc,w3,w1,w2,w4],[]),([6,w0,wc,w3,w3,w1,w2,w4],[]),([6,w0,wc,w3,w45,w1,w2,w4],[]),([6,w0,wc,w3,wd,w1,w2,w4],[]),([6,w0,wc,w3,w6a,w1,w2],[(58,1),(105,1),(136,1),(137,1),(181,0),(113,1),(197,2)]),([6,w0,wc,w3,w6a,w1,w2,w4],[(80,1),(136,1),(224,1)]),([6,w0,wc,w3,w1,w1,w2,w4],[(80,1),(104,1),(224,1)]),([6,w0,wc,w3,w1,w1c,w2,w4],[(80,1),(104,0),(136,1),(224,1)]),([6,w0,wc,w3,w1,w6b,w2,w4],[(80,1),(136,1),(224,1)]),([6,w0,wc,w3,w1,w6,w2,w4],[]),([6,w0,wc,w3,w1,w2,w11,w4],[(80,2),(104,0),(176,2),(224,2),(156,2)]),([6,w0,wc,w3,w1,w2,w4],[(6,2),(105,1),(137,3),(141,0),(206,0)]),([6,w0,wc,w3,w1,w2,w4,w4],[]),([6,w0,wc,w3,w1,w2,w4,w8],[]),([6,w0,wc,w3,w1,w2,w4,we],[]),([6,w0,wc,w3,w1,w2,w4,w20],[(80,1),(176,1),(224,1)]),([6,w0,wc,w3,w1,w2,w8],[(6,2),(105,1),(137,3),(141,0),(206,0)]),([6,w0,wc,w3,w1,w2,we],[(145,0),(206,0)])]
noncomputable def K_45 : List (List ℕ × List (ℕ × ℕ)) := [([6,w0,wc,w1,w2,w4,we],[]),([6,w0,wc,w1,w2,we],[(6,2),(10,0),(18,2)]),([6,w0,w1a,w3,w1,w2,w4],[(6,2),(105,1),(137,3),(141,0),(149,0),(198,1),(206,3)]),([6,w0,w1a,w3,w1,w2,w4,w8],[]),([6,w0,w1a,w3,w1,w2,w8],[(6,2),(105,1),(137,3),(141,0),(149,0),(206,0)]),([6,w0,w1e,w3,w1,w2,w4],[(6,4),(105,1),(137,3),(141,0),(198,1)]),([6,w0,w1e,w3,w1,w2,w4,w20],[(80,1),(224,1)]),([6,w0,w3,w3,w3,w1,w2,w4],[]),([6,w0,w3,w3,wd,w1,w2,w4],[]),([6,w0,w3,w3,w1,w1,w2,w4],[(64,1),(68,1)]),([6,w0,w3,w3,w1,w1c,w2,w4],[(64,1),(68,1),(104,0)]),([6,w0,w3,w3,w1,w6,w2,w4],[]),([6,w0,w3,w3,w1,w2,w11,w4],[(64,2),(68,2),(156,2)]),([6,w0,w3,w3,w1,w2,w4],[(6,2),(137,0),(141,0)]),([6,w0,w3,w3,w1,w2,w4,w4],[]),([6,w0,w3,w3,w1,w2,w4,w8],[]),([6,w0,w3,w3,w1,w2,w4,we],[])]
noncomputable def K_46 : List (List ℕ × List (ℕ × ℕ)) := [([6,w0,w3,w3,w1,w2,w4,w20],[(64,1),(68,1)]),([6,w0,w3,w3,w1,w2,w8],[(6,2),(137,0),(141,0)]),([6,w0,w3,w52,w1,w2,w4],[(177,2),(10,2),(117,1),(145,0),(149,3)]),([6,w0,w3,w4d,w1,w2,w4],[(137,2),(10,4),(117,1),(149,0)]),([6,w0,w3,w44,w1,w2,w4],[(58,2),(10,2),(117,1),(145,0),(149,3)]),([6,w0,w3,w1b,w1,w2,w4],[(104,3),(105,1),(10,3),(113,1),(117,1),(145,3),(149,3)]),([6,w0,w3,w28,w1,w2,w4],[(58,2),(6,2),(80,2),(81,2),(105,2),(109,1),(137,2),(141,3),(177,2),(10,4),(117,1),(145,0),(149,3)]),([6,w0,w3,w19,wd,w1,w2,w4],[]),([6,w0,w3,w19,w1,w2,w4],[(10,2),(113,1),(117,1),(145,3),(149,3),(198,1),(206,3)]),([6,w0,w3,w45,w1,w2,w4],[(129,0),(10,2),(113,1),(117,1),(145,3),(149,3),(198,1),(206,3)]),([6,w0,w3,w1d,w1,w2,w4],[(105,2),(137,4),(10,2),(117,1),(145,0),(149,3)]),([6,w0,w3,wd,wd,w1,w2,w4],[]),([6,w0,w3,wd,w1,w1c,w2,w4],[(76,1),(84,1),(104,3),(116,1)]),([6,w0,w3,wd,w1,w6,w2,w4],[(80,2),(136,2),(116,1)])]
noncomputable def K_47 : List (List ℕ × List (ℕ × ℕ)) := [([6,w0,w3,wd,w1,w3b,w2,w4],[(116,1),(204,3)]),([6,w0,w3,wd,w1,w2,w11,w4],[(76,2),(84,2),(176,2),(156,2)]),([6,w0,w3,wd,w1,w2,w4],[(105,2),(137,4),(10,2),(117,1),(145,0),(149,3)]),([6,w0,w3,wd,w1,w2,w4,w4],[]),([6,w0,w3,wd,w1,w2,w4,w8],[]),([6,w0,w3,wd,w1,w2,w4,we],[]),([6,w0,w3,wd,w1,w2,w4,w2b],[(244,1),(252,3)]),([6,w0,w3,wd,w1,w2,w4,w20],[(76,1),(84,1)]),([6,w0,w3,wd,w1,w2,w8],[(129,0),(105,2),(137,4),(10,2),(117,1),(145,0),(149,3)]),([6,w0,w3,w1,w59,w2,w4],[(58,2),(85,1),(141,3),(177,2),(118,1),(14,2),(153,0),(157,3)]),([6,w0,w3,w1,w12,w6,w2],[(58,2),(74,0),(85,1),(150,1),(18,3),(205,3)]),([6,w0,w3,w1,w12,w6,w2,w4],[]),([6,w0,w3,w1,w12,w2],[(75,1),(79,1),(131,3),(135,3),(6,2),(7,2),(143,0),(9,1),(10,0),(11,0),(115,1),(119,1),(147,1),(151,2),(14,3),(15,3),(159,3),(17,3)]),([6,w0,w3,w1,w12,w2,w4],[(114,1),(118,1),(186,1),(190,1),(14,3),(153,3),(157,3),(206,3)]),([6,w0,w3,w1,w50,w2,w4],[(58,2),(85,1),(137,2),(118,1),(14,4),(153,0),(157,3)]),([6,w0,w3,w1,w6,w6,w2,w4],[]),([6,w0,w3,w1,w6,w3b,w2,w4],[(204,3)])]
noncomputable def K_48 : List (List ℕ × List (ℕ × ℕ)) := [([6,w0,w3,w1,w6,w2,w27,w4],[(108,0),(140,0),(116,0),(188,1),(156,3),(260,0)]),([6,w0,w3,w1,w6,w2,w2f,w4],[(156,3)]),([6,w0,w3,w1,w6,w2,w4],[(58,2),(74,0),(85,1),(118,1),(14,3),(157,3)]),([6,w0,w3,w1,w6,w2,w4,w4],[]),([6,w0,w3,w1,w6,w2,w4,w8],[]),([6,w0,w3,w1,w6,w2,w4,we],[(236,1)]),([6,w0,w3,w1,w6,w2,w4,w3d],[]),([6,w0,w3,w1,w6,w2,w4,w24],[(108,3),(228,0),(116,3),(236,2)]),([6,w0,w3,w1,w6,w2,w8],[(58,2),(74,0),(85,1),(118,1),(14,3),(157,3)]),([6,w0,w3,w1,w3b,w2,w4],[(118,1),(14,3),(156,3),(158,3),(157,3)]),([6,w0,w3,w1,w2,w2f,w4],[(58,2),(74,0),(150,1),(158,3)]),([6,w0,w3,w1,w2,w4],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(147,1),(151,1),(13,3),(155,3),(159,3)]),([6,w0,w3,w1,w2,w4,w4],[(146,1),(150,1),(154,3),(158,3)]),([6,w0,w3,w1,w2,w4,w4,w4],[]),([6,w0,w3,w1,w2,w4,w4,w8],[]),([6,w0,w3,w1,w2,w4,w4,we],[])]
noncomputable def K_49 : List (List ℕ × List (ℕ × ℕ)) := [([6,w0,w3,w1,w2,w4,w43],[(150,1),(186,1),(190,1),(198,3),(22,3)]),([6,w0,w3,w1,w2,w4,w16],[(186,1),(190,1),(194,3),(198,3)]),([6,w0,w3,w1,w2,w4,w15],[(150,1),(186,1),(190,1),(154,0),(158,3),(194,3),(198,3),(22,2)]),([6,w0,w3,w1,w2,w4,w8],[(146,1),(150,1),(186,1),(190,1),(154,3),(158,3),(194,3),(198,3)]),([6,w0,w3,w1,w2,w4,w8,w8],[]),([6,w0,w3,w1,w2,w4,w8,we],[]),([6,w0,w3,w1,w2,w4,w8,w2b],[(236,1),(244,3)]),([6,w0,w3,w1,w2,w4,w13],[(150,1),(186,1),(190,1),(194,3),(198,3),(22,3)]),([6,w0,w3,w1,w2,w4,we],[(190,1),(194,0),(198,3),(22,2)]),([6,w0,w3,w1,w2,w4,we,we],[]),([6,w0,w3,w1,w2,w4,we,w2b],[(236,1),(244,3)]),([6,w0,w3,w1,w2,w4,we,w20],[(180,1),(204,1)]),([6,w0,w3,w1,w2,w4,we,w3d],[]),([6,w0,w3,w1,w2,w4,w2b],[(188,1),(190,1),(189,1),(194,0),(196,3),(198,3),(197,3),(22,2)]),([6,w0,w3,w1,w2,w4,w3d],[(190,1),(198,3),(22,3)])]
noncomputable def K_50 : List (List ℕ × List (ℕ × ℕ)) := [([6,w0,w3,w1,w2,w4,w2c],[(190,1),(198,3)]),([6,w0,w3,w1,w2,w15],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(151,1),(13,3),(155,0),(159,3),(18,2),(19,2)]),([6,w0,w3,w1,w2,w8],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(147,1),(151,1),(13,3),(155,3),(159,3)]),([6,w0,w3,w1,w2,w8,w8],[(146,1),(150,1),(154,3),(158,3)]),([6,w0,w3,w1,w2,w8,we],[(190,1),(194,0),(198,3),(22,2)]),([6,w0,w3,w1,w2,w8,w2b],[(188,1),(190,1),(189,1),(194,0),(196,3),(198,3),(197,3),(22,2)]),([6,w0,w3,w1,w10,w4],[(58,2),(75,1),(79,1),(103,0),(6,2),(7,2),(111,0),(9,1),(10,0),(11,0),(119,2),(151,1),(14,1),(15,1)]),([6,w0,w3,w1,w18,w27,w4],[(58,1),(132,0),(134,0),(108,0),(110,0),(109,0)]),([7,65535,w0,w3,w1,w2],[(99,1),(103,1),(131,3),(135,3),(107,1),(111,1),(139,3),(143,3),(10,2),(11,2),(147,0),(151,0),(13,1),(14,0),(15,0),(155,2),(159,2),(17,3)]),([7,65535,w0,w3,w1,w2,w4],[(97,1),(99,1),(101,1),(103,1),(129,3),(131,3),(133,3),(135,3),(107,1),(111,1),(139,3),(143,3),(10,2),(11,2),(147,0),(151,0),(13,1),(14,0),(15,0),(155,2),(159,2),(194,1),(195,1),(198,1),(199,1),(17,3),(202,3),(203,3),(206,3),(207,3)]),([7,w9,w0,w3,w1,w2,w4],[(2,3),(97,1),(99,1),(101,1),(103,1),(107,1),(111,1),(10,2),(11,1),(13,1),(14,0),(154,1),(155,1),(158,1),(159,1),(195,1),(199,1)])]
noncomputable def K_51 : List (List ℕ × List (ℕ × ℕ)) := [([7,w9,w0,w3,w1,w4],[(99,1),(103,1),(107,1),(111,1),(10,1),(11,1),(13,1),(155,1),(159,1)]),([7,wb,w0,w3,w1,w2,w4],[(97,1),(99,1),(101,1),(103,1),(129,3),(131,3),(133,3),(135,3),(105,1),(107,1),(109,1),(111,1),(137,3),(139,3),(141,3),(143,3),(10,2),(11,2),(147,0),(151,0),(13,1),(14,0),(15,0),(155,2),(159,2),(195,1),(199,1),(17,3),(203,3),(207,3)]),([7,wb,w3,w1,w2,w4],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(147,1),(151,1),(13,3),(155,3),(159,3)]),([7,wa,w0,w3,w1,w2,w4],[(2,2),(3,2),(96,0),(98,0),(97,1),(129,3),(131,0),(133,0),(135,0),(139,0),(143,0),(10,2),(11,2),(147,0),(151,0),(14,0),(15,0),(17,0),(203,0),(207,0)]),([7,w7,w0,w3,w1,w2,w4],[(97,1),(99,1),(101,1),(103,1),(129,3),(131,3),(133,3),(135,3),(107,1),(111,1),(139,3),(143,3),(10,2),(11,2),(147,0),(151,0),(13,1),(14,0),(15,0),(155,2),(159,2),(195,1),(199,1),(17,3),(203,3),(207,3)]),([7,w0,w0,w3,w1,w2,w4],[(97,1),(99,1),(101,1),(103,1),(129,3),(131,3),(133,3),(135,3),(10,2),(11,2),(147,0),(151,0),(13,1),(14,0),(15,0),(155,2),(159,2),(195,1),(199,1),(17,3),(203,3),(207,3)]),([7,w0,w5,w3,w1,w2,w4],[(99,1),(103,1),(135,3),(6,3),(7,3),(105,1),(107,1),(137,3),(10,2),(11,2),(113,1),(13,1),(14,0),(15,0),(155,1),(159,1),(195,1),(199,1)]),([7,w0,wc,w3,w1,w2,w4],[(103,1),(131,0),(135,3),(6,2),(7,2),(105,1),(137,3),(139,0),(141,0),(143,0),(10,2),(11,2),(147,0),(151,0),(14,0),(15,0),(159,2),(17,0),(203,0),(206,0),(207,0)]),([7,w0,w3,w3,w1,w2,w4],[(103,1),(131,0),(135,3),(6,2),(7,2),(137,0),(139,0),(141,0),(143,0),(14,0),(15,0),(159,2),(199,1),(17,0),(203,0),(207,3)])]
noncomputable def K_52 : List (List ℕ × List (ℕ × ℕ)) := [([7,w0,w3,wd,w1,w2,w4],[(103,1),(131,0),(135,3),(6,2),(7,2),(105,2),(137,4),(139,0),(143,0),(10,2),(11,2),(117,1),(119,1),(145,0),(147,0),(149,3),(151,3),(13,1),(14,0),(15,0),(159,2),(199,1),(17,3),(203,0),(207,3)]),([7,w0,w3,w1,w6,w2,w4],[(58,2),(74,0),(75,1),(79,1),(131,3),(135,3),(6,2),(7,2),(85,1),(143,0),(9,1),(10,0),(11,0),(118,1),(119,1),(147,1),(151,2),(187,1),(191,1),(14,3),(15,3),(157,3),(159,3),(17,3),(207,3)]),([7,w0,w3,w1,w2,w4],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(147,1),(151,1),(13,3),(155,3),(159,3)]),([7,w0,w3,w1,w2,w4,w4],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(146,1),(147,1),(150,1),(151,1),(13,3),(154,3),(155,3),(158,3),(159,3)]),([7,w0,w3,w1,w2,w4,w8],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(146,1),(147,1),(150,1),(151,1),(186,1),(187,1),(190,1),(191,1),(13,3),(154,3),(155,3),(158,3),(159,3),(194,3),(195,3),(198,3),(199,3)]),([7,w0,w3,w1,w2,w4,we],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(151,1),(190,1),(191,1),(13,3),(155,0),(159,3),(194,0),(195,0),(198,3),(199,3),(22,2),(23,2)]),([7,w0,w3,w1,w2,w8],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(147,1),(151,1),(13,3),(155,3),(159,3)]),([8,w0,w3,w1,w2,w4],[(75,1),(79,1),(99,3),(103,3),(6,2),(7,2),(107,0),(111,0),(9,1),(10,0),(11,0),(115,2),(119,2),(147,1),(151,1),(13,3),(155,3),(159,3)])]
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_3 : K_3.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_4 : K_4.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_5 : K_5.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_6 : K_6.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_7 : K_7.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_8 : K_8.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_9 : K_9.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_10 : K_10.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_11 : K_11.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_12 : K_12.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_13 : K_13.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_14 : K_14.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_15 : K_15.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_16 : K_16.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_17 : K_17.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_18 : K_18.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_19 : K_19.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_20 : K_20.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_21 : K_21.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_22 : K_22.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_23 : K_23.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_24 : K_24.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_25 : K_25.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_26 : K_26.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_27 : K_27.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_28 : K_28.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_29 : K_29.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_30 : K_30.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_31 : K_31.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_32 : K_32.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_33 : K_33.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_34 : K_34.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_35 : K_35.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_36 : K_36.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_37 : K_37.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_38 : K_38.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_39 : K_39.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_40 : K_40.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_41 : K_41.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_42 : K_42.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_43 : K_43.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_44 : K_44.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_45 : K_45.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_46 : K_46.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_47 : K_47.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_48 : K_48.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_49 : K_49.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_50 : K_50.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_51 : K_51.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_52 : K_52.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem hK_cert : T_cert.toList = (((((K_0 ++ (K_1 ++ K_2)) ++ (K_3 ++ (K_4 ++ K_5))) ++ ((K_6 ++ (K_7 ++ K_8)) ++ ((K_9 ++ K_10) ++ (K_11 ++ K_12)))) ++ (((K_13 ++ (K_14 ++ K_15)) ++ (K_16 ++ (K_17 ++ K_18))) ++ ((K_19 ++ (K_20 ++ K_21)) ++ ((K_22 ++ K_23) ++ (K_24 ++ K_25))))) ++ ((((K_26 ++ (K_27 ++ K_28)) ++ (K_29 ++ (K_30 ++ K_31))) ++ ((K_32 ++ (K_33 ++ K_34)) ++ ((K_35 ++ K_36) ++ (K_37 ++ K_38)))) ++ (((K_39 ++ (K_40 ++ K_41)) ++ ((K_42 ++ K_43) ++ (K_44 ++ K_45))) ++ ((K_46 ++ (K_47 ++ K_48)) ++ ((K_49 ++ K_50) ++ (K_51 ++ K_52)))))).map Prod.fst := by decide +kernel
set_option maxRecDepth 100000 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert ((all_app (all_app (all_app (all_app (all_app c_0 (all_app c_1 c_2)) (all_app c_3 (all_app c_4 c_5))) (all_app (all_app c_6 (all_app c_7 c_8)) (all_app (all_app c_9 c_10) (all_app c_11 c_12)))) (all_app (all_app (all_app c_13 (all_app c_14 c_15)) (all_app c_16 (all_app c_17 c_18))) (all_app (all_app c_19 (all_app c_20 c_21)) (all_app (all_app c_22 c_23) (all_app c_24 c_25))))) (all_app (all_app (all_app (all_app c_26 (all_app c_27 c_28)) (all_app c_29 (all_app c_30 c_31))) (all_app (all_app c_32 (all_app c_33 c_34)) (all_app (all_app c_35 c_36) (all_app c_37 c_38)))) (all_app (all_app (all_app c_39 (all_app c_40 c_41)) (all_app (all_app c_42 c_43) (all_app c_44 c_45))) (all_app (all_app c_46 (all_app c_47 c_48)) (all_app (all_app c_49 c_50) (all_app c_51 c_52)))))))

theorem lb : ∀ s : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xfee8eaa8 (idx5 x)) s → 9 ≤ s :=
  lb_cert _ L_ M_ Y_ XS_ PD_ PM_ G_ T_cert 8 9 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨fun _ => false, fun _ => true, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) hT_cert (by decide +kernel)

set_option maxRecDepth 100000 in
theorem main : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xfee8eaa8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xfee8eaa8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  simp only [sum_eq] at h ⊢
  exact ⟨⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [7, 3]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [8, 10]⟩, ⟨.and, [11, 5]⟩, ⟨.or, [9, 12]⟩], 13⟩, by simp [PEqualNP.MetaComplexity.Monotone2], le_trans (by decide) (lb s h), by decide +kernel⟩

end Cert1

-- The shared elimination and certificate checker, and the two finite certificates, come from upstream L_meta_8653 and L_meta_8694.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4276682368 * 2^32 + 4276650112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sixWitness : Circuit := ⟨[⟨.and, [3, 5]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [11, 10]⟩, ⟨.or, [12, 9]⟩, ⟨.and, [13, 2]⟩, ⟨.and, [12, 9]⟩, ⟨.or, [15, 14]⟩], 16⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem sixBound (s : ℕ) (h : HasCircuitSize 6 target s) : 11 ≤ s := by
  have dep : ∃ x : Fin 6 → Bool, target (Function.update x 5 (!x 5)) ≠ target x := by decide +kernel
  have nc : ∀ b : Bool, ∃ x y : Fin 6 → Bool, target (Function.update x 5 b) ≠ target (Function.update y 5 b) := by decide +kernel
  obtain ⟨b, s', hs, hc⟩ := gate_elim_at 5 target 5 s dep nc h
  cases b
  · let m : Fin 6 → Fin 5 := ![1, 2, 3, 4, 0, 0]
    have permuted := relabel_size m (fun x => target (Function.update x 5 false)) s' hc
    have eq : (fun x : Fin 5 → Bool => target (Function.update (x ∘ m) 5 false)) = (fun x => Nat.testBit w84 (idx5 x)) := by
      funext x
      exact (by decide +kernel : ∀ x : Fin 5 → Bool, target (Function.update (x ∘ m) 5 false) = Nat.testBit w84 (idx5 x)) x
    rw [eq] at permuted
    have hl := Cert0.lb s' permuted
    omega
  · let m : Fin 6 → Fin 5 := ![1, 2, 3, 0, 4, 0]
    have permuted := relabel_size m (fun x => target (Function.update x 5 true)) s' hc
    have eq : (fun x : Fin 5 → Bool => target (Function.update (x ∘ m) 5 true)) = (fun x => Nat.testBit w92 (idx5 x)) := by
      funext x
      exact (by decide +kernel : ∀ x : Fin 5 → Bool, target (Function.update (x ∘ m) 5 true) = Nat.testBit w92 (idx5 x)) x
    rw [eq] at permuted
    have hl := Cert1.lb s' permuted
    omega
end PEqualNP.Outside.L_meta_12333.Core
open PEqualNP.Outside.L_meta_12333.Core PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_12333 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682368 * 2 ^ 32 + 4276650112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s →
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
    ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682368 * 2 ^ 32 + 4276650112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have lower := sixBound s h
  refine ⟨sixWitness, by simp [Monotone2,sixWitness], ?_, ?_⟩
  · have hw : sixWitness.size ≤ 11 := by decide
    omega
  · change ∀ x : Fin 6 → Bool, sixWitness.eval (List.ofFn x) = target x
    decide +kernel
