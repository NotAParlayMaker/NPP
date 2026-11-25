import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9431

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
    let a := code &&& 4095
    let b := (code >>> 12) &&& 4095
    let c := (code >>> 24) &&& 4095
    let d := (code >>> 36) &&& 4095
    let e := (code >>> 48) &&& 4095
    let f := (code >>> 60) &&& 4095
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

def bsr (load : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if load ((lo + hi) / 2) ≤ h then bsr load h f ((lo + hi) / 2) hi
       else bsr load h f lo ((lo + hi) / 2))
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


def gfn {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) : BFn n :=
  fun x => A.any (fun a => x a) || E.any (fun e => x e.1 && x e.2)

def dedupAux {α : Type} [BEq α] : List α → List α → List α
  | [], acc => acc.reverse
  | a :: t, acc => if acc.contains a then dedupAux t acc else dedupAux t (a :: acc)

def dedup {α : Type} [BEq α] (l : List α) : List α := dedupAux l []

theorem mem_dedupAux {α : Type} [DecidableEq α] : ∀ (l acc : List α) (x : α),
    x ∈ dedupAux l acc ↔ x ∈ l ∨ x ∈ acc
  | [], acc, x => by simp [dedupAux]
  | a :: t, acc, x => by
    simp only [dedupAux]
    by_cases h : acc.contains a = true
    · simp only [h, ↓reduceIte, mem_dedupAux, List.mem_cons]
      have ha : a ∈ acc := by simpa using h
      constructor
      · rintro (ht | hacc)
        · exact Or.inl (Or.inr ht)
        · exact Or.inr hacc
      · rintro ((rfl | ht) | hacc)
        · exact Or.inr ha
        · exact Or.inl ht
        · exact Or.inr hacc
    · simp only [h, Bool.false_eq_true, ↓reduceIte, mem_dedupAux, List.mem_cons]
      tauto

theorem mem_dedup {α : Type} [DecidableEq α] (l : List α) (x : α) :
    x ∈ dedup l ↔ x ∈ l := by
  simpa [dedup] using mem_dedupAux l [] x

def fix0A {n : ℕ} (A : List (Fin n)) (p : Fin n) : List (Fin n) :=
  A.filter (· != p)

def fix0E {n : ℕ} (E : List (Fin n × Fin n)) (p : Fin n) : List (Fin n × Fin n) :=
  E.filter (fun e => e.1 != p && e.2 != p)

def nbrs {n : ℕ} (E : List (Fin n × Fin n)) (p : Fin n) : List (Fin n) :=
  E.filterMap (fun e => if e.1 == p then some e.2 else if e.2 == p then some e.1 else none)

def fix1A {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (p : Fin n) : List (Fin n) :=
  dedup (A ++ nbrs E p)

def fix1E {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (p : Fin n) : List (Fin n × Fin n) :=
  let A1 := fix1A A E p
  E.filter (fun e => e.1 != p && e.2 != p && !A1.contains e.1 && !A1.contains e.2)

def depCheck {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (p : Fin n) : Bool :=
  A.contains p ||
    (E.all (fun e => e.1 != e.2) &&
      E.any (fun e => (e.1 == p && !A.contains e.2) || (e.2 == p && !A.contains e.1)))

def isoCheck {n k : ℕ} (E : List (Fin n × Fin n)) (Eb : List (Fin k × Fin k)) (π : Fin n → Fin k) : Bool :=
  E.all (fun e => Eb.any (fun e' => (π e.1 == e'.1 && π e.2 == e'.2) || (π e.1 == e'.2 && π e.2 == e'.1))) &&
  Eb.all (fun e' => E.any (fun e => (π e.1 == e'.1 && π e.2 == e'.2) || (π e.1 == e'.2 && π e.2 == e'.1)))

theorem gfn_le {n val1 val2 : ℕ} {f : BFn n} (hle : val1 ≤ val2)
    (h : ∀ s, HasCircuitSize n f s → val2 ≤ s) : ∀ s, HasCircuitSize n f s → val1 ≤ s :=
  fun s hs => le_trans hle (h s hs)

theorem gfn_empty {n : ℕ} (A : List (Fin n)) (hnd : A.Nodup) :
    ∀ s : ℕ, HasCircuitSize n (gfn A []) s → A.length - 1 ≤ s := by
  intro s h
  have hd := dep_lower_set n (gfn A []) A.toFinset (by
    intro i hi
    have hiA : i ∈ A := List.mem_toFinset.1 hi
    refine ⟨fun _ => false, ?_⟩
    have h0 : gfn A [] (fun _ => false) = false := by simp [gfn]
    have h1 : gfn A [] (Function.update (fun _ => false) i true) = true := by
      simp only [gfn, List.any_nil, Bool.or_false, List.any_eq_true]
      exact ⟨i, hiA, by simp⟩
    simpa [h0, h1]) s h
  rw [List.toFinset_card_of_nodup hnd] at hd
  omega

theorem gfn_nc {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n))
    (h : (!A.isEmpty || !E.isEmpty) = true) :
    ∃ x y : Fin n → Bool, gfn A E x ≠ gfn A E y := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  have h0 : gfn A E (fun _ => false) = false := by simp [gfn]
  have h1 : gfn A E (fun _ => true) = true := by
    cases A with
    | cons a t => simp [gfn]
    | nil =>
      cases E with
      | nil => simp at h
      | cons e t => simp [gfn]
  rw [h0, h1]; decide

theorem gfn_dep {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (p : Fin n)
    (h : depCheck A E p = true) :
    ∃ x : Fin n → Bool, gfn A E (Function.update x p (!x p)) ≠ gfn A E x := by
  simp only [depCheck, Bool.or_eq_true, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq,
    List.all_eq_true, List.any_eq_true, bne_iff_ne, beq_iff_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  rcases h with hpA | ⟨hloop, ⟨e, heE, ⟨rfl, hqA⟩ | ⟨rfl, hqA⟩⟩⟩
  · refine ⟨fun _ => false, ?_⟩
    have h0 : gfn A E (fun _ => false) = false := by simp [gfn]
    have h1 : gfn A E (Function.update (fun _ => false) p true) = true := by
      simp only [gfn, Bool.or_eq_true, List.any_eq_true]
      exact Or.inl ⟨p, hpA, by simp⟩
    simpa [h0, h1]
  · have hne : e.1 ≠ e.2 := hloop e heE
    refine ⟨fun i => decide (i = e.2), ?_⟩
    have h0 : gfn A E (fun i => decide (i = e.2)) = false := by
      simp only [gfn, Bool.or_eq_false_iff, List.any_eq_false, decide_eq_true_eq, Bool.and_eq_true]
      refine ⟨fun a ha hEq => hqA (hEq ▸ ha), fun e' he' => ?_⟩
      intro ⟨h1, h2⟩
      exact hloop e' he' (h1.trans h2.symm)
    have h1 : gfn A E (Function.update (fun i => decide (i = e.2)) e.1 (!decide (e.1 = e.2))) = true := by
      simp only [gfn, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
      refine Or.inr ⟨e, heE, ?_, ?_⟩
      · simp [hne]
      · simp [Function.update_of_ne (Ne.symm hne)]
    rw [h0, h1]; decide
  · have hne : e.1 ≠ e.2 := hloop e heE
    refine ⟨fun i => decide (i = e.1), ?_⟩
    have h0 : gfn A E (fun i => decide (i = e.1)) = false := by
      simp only [gfn, Bool.or_eq_false_iff, List.any_eq_false, decide_eq_true_eq, Bool.and_eq_true]
      refine ⟨fun a ha hEq => hqA (hEq ▸ ha), fun e' he' => ?_⟩
      intro ⟨h1, h2⟩
      exact hloop e' he' (h1.trans h2.symm)
    have h1 : gfn A E (Function.update (fun i => decide (i = e.1)) e.2 (!decide (e.2 = e.1))) = true := by
      simp only [gfn, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
      refine Or.inr ⟨e, heE, ?_, ?_⟩
      · simp [Function.update_of_ne hne]
      · simp [Ne.symm hne]
    rw [h0, h1]; decide

theorem gfn_restrict_false {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (p : Fin n) :
    (fun x => gfn A E (Function.update x p false)) = gfn (fix0A A p) (fix0E E p) := by
  funext x
  apply Bool.eq_iff_iff.2
  simp only [gfn, fix0A, fix0E, Bool.or_eq_true, List.any_eq_true, List.mem_filter,
    Bool.and_eq_true, bne_iff_ne]
  constructor
  · rintro (⟨a, ha, hxa⟩ | ⟨e, he, h1, h2⟩)
    · by_cases hap : a = p
      · subst hap; simp at hxa
      · exact Or.inl ⟨a, ⟨ha, hap⟩, by simpa [Function.update_of_ne hap] using hxa⟩
    · by_cases h1p : e.1 = p
      · rw [h1p, Function.update_self] at h1; cases h1
      · by_cases h2p : e.2 = p
        · rw [h2p, Function.update_self] at h2; cases h2
        · exact Or.inr ⟨e, ⟨he, h1p, h2p⟩,
            by simpa [Function.update_of_ne h1p] using h1,
            by simpa [Function.update_of_ne h2p] using h2⟩
  · rintro (⟨a, ⟨ha, hap⟩, hxa⟩ | ⟨e, ⟨he, h1p, h2p⟩, h1, h2⟩)
    · exact Or.inl ⟨a, ha, by simpa [Function.update_of_ne hap] using hxa⟩
    · exact Or.inr ⟨e, he,
        by simpa [Function.update_of_ne h1p] using h1,
        by simpa [Function.update_of_ne h2p] using h2⟩

theorem mem_nbrs {n : ℕ} (E : List (Fin n × Fin n)) (p q : Fin n) :
    q ∈ nbrs E p ↔ ∃ e ∈ E, (e.1 = p ∧ e.2 = q) ∨ (e.1 ≠ p ∧ e.2 = p ∧ e.1 = q) := by
  simp only [nbrs, List.mem_filterMap, beq_iff_eq]
  constructor
  · rintro ⟨e, he, h⟩
    split_ifs at h with h1 h2
    · cases h; exact ⟨e, he, Or.inl ⟨h1, rfl⟩⟩
    · cases h; exact ⟨e, he, Or.inr ⟨h1, h2, rfl⟩⟩
  · rintro ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2, h3⟩⟩
    · exact ⟨e, he, by rw [if_pos h1, h2]⟩
    · exact ⟨e, he, by rw [if_neg h1, if_pos h2, h3]⟩

theorem gfn_restrict_true {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (p : Fin n)
    (hpA : !A.contains p = true) (hloop : E.all (fun e => e.1 != e.2) = true) :
    (fun x => gfn A E (Function.update x p true)) = gfn (fix1A A E p) (fix1E A E p) := by
  have hpnot : p ∉ A := by simpa [List.contains_eq_mem] using hpA
  have hne : ∀ e ∈ E, e.1 ≠ e.2 := by simpa [List.all_eq_true, bne_iff_ne] using hloop
  funext x
  apply Bool.eq_iff_iff.2
  simp only [gfn, fix1E, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, List.mem_filter,
    bne_iff_ne, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
  constructor
  · rintro (⟨a, ha, hxa⟩ | ⟨e, he, h1, h2⟩)
    · have hap : a ≠ p := fun h => hpnot (h ▸ ha)
      refine Or.inl ⟨a, ?_, by simpa [Function.update_of_ne hap] using hxa⟩
      rw [fix1A, mem_dedup]; exact List.mem_append_left _ ha
    · by_cases h1p : e.1 = p
      · have h2p : e.2 ≠ p := fun h => hne e he (h1p.trans h.symm)
        refine Or.inl ⟨e.2, ?_, by simpa [Function.update_of_ne h2p] using h2⟩
        rw [fix1A, mem_dedup]; exact List.mem_append_right _ ((mem_nbrs E p e.2).2 ⟨e, he, Or.inl ⟨h1p, rfl⟩⟩)
      · by_cases h2p : e.2 = p
        · refine Or.inl ⟨e.1, ?_, by simpa [Function.update_of_ne h1p] using h1⟩
          rw [fix1A, mem_dedup]; exact List.mem_append_right _ ((mem_nbrs E p e.1).2 ⟨e, he, Or.inr ⟨h1p, h2p, rfl⟩⟩)
        · have hx1 : x e.1 = true := by simpa [Function.update_of_ne h1p] using h1
          have hx2 : x e.2 = true := by simpa [Function.update_of_ne h2p] using h2
          by_cases m1 : e.1 ∈ fix1A A E p
          · exact Or.inl ⟨e.1, m1, hx1⟩
          · by_cases m2 : e.2 ∈ fix1A A E p
            · exact Or.inl ⟨e.2, m2, hx2⟩
            · exact Or.inr ⟨e, ⟨he, ⟨⟨h1p, h2p⟩, m1⟩, m2⟩, hx1, hx2⟩
  · rintro (⟨a, ha, hxa⟩ | ⟨e, ⟨he, ⟨⟨h1p, h2p⟩, _⟩, _⟩, hx1, hx2⟩)
    · rw [fix1A, mem_dedup, List.mem_append] at ha
      rcases ha with haA | han
      · have hap : a ≠ p := fun h => hpnot (h ▸ haA)
        exact Or.inl ⟨a, haA, by simpa [Function.update_of_ne hap] using hxa⟩
      · obtain ⟨e, he, ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩⟩ := (mem_nbrs E p a).1 han
        · have h2p : e.2 ≠ p := fun h => hne e he (h1.trans h.symm)
          exact Or.inr ⟨e, he, by simp [h1], by simpa [Function.update_of_ne h2p] using hxa⟩
        · exact Or.inr ⟨e, he, by simpa [Function.update_of_ne h1] using hxa, by simp [h2]⟩
    · exact Or.inr ⟨e, he,
        by simpa [Function.update_of_ne h1p] using hx1,
        by simpa [Function.update_of_ne h2p] using hx2⟩

theorem gfn_fix0 {n : ℕ} (A : List (Fin (n + 1))) (E : List (Fin (n + 1) × Fin (n + 1)))
    (p : Fin (n + 1)) (A' : List (Fin (n + 1))) (E' : List (Fin (n + 1) × Fin (n + 1))) (k : ℕ)
    (hdep : depCheck A E p = true)
    (hA : A' = fix0A A p) (hE : E' = fix0E E p)
    (hnc : (!A'.isEmpty || !E'.isEmpty) = true)
    (ih : ∀ s, HasCircuitSize (n + 1) (gfn A' E') s → k ≤ s) :
    ∀ s, HasCircuitSize (n + 1) (gfn A E) s → k + 1 ≤ s := by
  intro s h
  have hres : (fun x => gfn A E (Function.update x p false)) = gfn A' E' := by
    rw [hA, hE]; exact gfn_restrict_false A E p
  have hnc' : ∃ x y, gfn A E (Function.update x p false) ≠ gfn A E (Function.update y p false) := by
    obtain ⟨x, y, hxy⟩ := gfn_nc A' E' hnc
    exact ⟨x, y, by simpa [congrFun hres] using hxy⟩
  obtain ⟨s', hs', h'⟩ := one_gate_at n (gfn A E) p false s (gfn_dep A E p hdep) hnc' h
  rw [hres] at h'
  have := ih s' h'
  omega

theorem gfn_fix1 {n : ℕ} (A : List (Fin (n + 1))) (E : List (Fin (n + 1) × Fin (n + 1)))
    (p : Fin (n + 1)) (A' : List (Fin (n + 1))) (E' : List (Fin (n + 1) × Fin (n + 1))) (k : ℕ)
    (hdep : depCheck A E p = true)
    (hpA : !A.contains p = true) (hloop : E.all (fun e => e.1 != e.2) = true)
    (hA : A' = fix1A A E p) (hE : E' = fix1E A E p)
    (hnc : (!A'.isEmpty || !E'.isEmpty) = true)
    (ih : ∀ s, HasCircuitSize (n + 1) (gfn A' E') s → k ≤ s) :
    ∀ s, HasCircuitSize (n + 1) (gfn A E) s → k + 1 ≤ s := by
  intro s h
  have hres : (fun x => gfn A E (Function.update x p true)) = gfn A' E' := by
    rw [hA, hE]; exact gfn_restrict_true A E p hpA hloop
  have hnc' : ∃ x y, gfn A E (Function.update x p true) ≠ gfn A E (Function.update y p true) := by
    obtain ⟨x, y, hxy⟩ := gfn_nc A' E' hnc
    exact ⟨x, y, by simpa [congrFun hres] using hxy⟩
  obtain ⟨s', hs', h'⟩ := one_gate_at n (gfn A E) p true s (gfn_dep A E p hdep) hnc' h
  rw [hres] at h'
  have := ih s' h'
  omega

theorem gfn_branch2 {n : ℕ} (A : List (Fin (n + 1))) (E : List (Fin (n + 1) × Fin (n + 1)))
    (p : Fin (n + 1))
    (A0 : List (Fin (n + 1))) (E0 : List (Fin (n + 1) × Fin (n + 1)))
    (A1 : List (Fin (n + 1))) (E1 : List (Fin (n + 1) × Fin (n + 1))) (k : ℕ)
    (hdep : depCheck A E p = true)
    (hpA : !A.contains p = true) (hloop : E.all (fun e => e.1 != e.2) = true)
    (hA0 : A0 = fix0A A p) (hE0 : E0 = fix0E E p)
    (hA1 : A1 = fix1A A E p) (hE1 : E1 = fix1E A E p)
    (hnc0 : (!A0.isEmpty || !E0.isEmpty) = true)
    (hnc1 : (!A1.isEmpty || !E1.isEmpty) = true)
    (ih0 : ∀ s, HasCircuitSize (n + 1) (gfn A0 E0) s → k ≤ s)
    (ih1 : ∀ s, HasCircuitSize (n + 1) (gfn A1 E1) s → k ≤ s) :
    ∀ s, HasCircuitSize (n + 1) (gfn A E) s → k + 2 ≤ s := by
  intro s h
  have hres0 : (fun x => gfn A E (Function.update x p false)) = gfn A0 E0 := by
    rw [hA0, hE0]; exact gfn_restrict_false A E p
  have hres1 : (fun x => gfn A E (Function.update x p true)) = gfn A1 E1 := by
    rw [hA1, hE1]; exact gfn_restrict_true A E p hpA hloop
  have hnc : ∀ b : Bool, ∃ x y, gfn A E (Function.update x p b) ≠ gfn A E (Function.update y p b) := by
    intro b
    cases b with
    | false =>
      obtain ⟨x, y, hxy⟩ := gfn_nc A0 E0 hnc0
      exact ⟨x, y, by simpa [congrFun hres0] using hxy⟩
    | true =>
      obtain ⟨x, y, hxy⟩ := gfn_nc A1 E1 hnc1
      exact ⟨x, y, by simpa [congrFun hres1] using hxy⟩
  obtain ⟨b, s', hs', h'⟩ := gate_elim_at n (gfn A E) p s (gfn_dep A E p hdep) hnc h
  cases b with
  | false => rw [hres0] at h'; have := ih0 s' h'; omega
  | true => rw [hres1] at h'; have := ih1 s' h'; omega

theorem gfn_iso {n k : ℕ} (E : List (Fin n × Fin n)) (Eb : List (Fin k × Fin k))
    (π : Fin n → Fin k) (hiso : isoCheck E Eb π = true) :
    (fun y : Fin k → Bool => gfn [] E (y ∘ π)) = gfn [] Eb := by
  simp only [isoCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true, beq_iff_eq] at hiso
  obtain ⟨h1, h2⟩ := hiso
  funext y
  apply Bool.eq_iff_iff.2
  simp only [gfn, List.any_nil, Bool.false_or, List.any_eq_true, Bool.and_eq_true, Function.comp_apply]
  constructor
  · rintro ⟨e, he, hy1, hy2⟩
    obtain ⟨e', he', ⟨a, b⟩ | ⟨a, b⟩⟩ := h1 e he
    · exact ⟨e', he', a ▸ hy1, b ▸ hy2⟩
    · exact ⟨e', he', b ▸ hy2, a ▸ hy1⟩
  · rintro ⟨e', he', hy1, hy2⟩
    obtain ⟨e, he, ⟨a, b⟩ | ⟨a, b⟩⟩ := h2 e' he'
    · exact ⟨e, he, a.symm ▸ hy1, b.symm ▸ hy2⟩
    · exact ⟨e, he, a.symm ▸ hy2, b.symm ▸ hy1⟩

theorem gfn_base {n k val : ℕ} (E : List (Fin n × Fin n)) (Eb : List (Fin k × Fin k))
    (π : Fin n → Fin k) (hiso : isoCheck E Eb π = true)
    (hb : ∀ s : ℕ, HasCircuitSize k (gfn [] Eb) s → val ≤ s) :
    ∀ s : ℕ, HasCircuitSize n (gfn [] E) s → val ≤ s := by
  intro s h
  have h' := relabel_size π (gfn [] E) s h
  rw [gfn_iso E Eb π hiso] at h'
  exact hb s h'

def edgeList : List (Fin 7 × Fin 7) := [(0, 3), (0, 4), (1, 4), (0, 5), (3, 5), (1, 6), (2, 6), (3, 6)]
def core : BFn 7 := gfn [] edgeList

def sampleRows : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 0, 9, 11, 13, 17, 18, 19, 21, 22, 25, 26, 33, 35, 37, 40, 41, 42, 44, 49, 50, 56, 66, 67, 68, 69, 70, 72, 73, 74, 76, 81, 82, 84, 88, 97, 98, 100, 104, 9, 11, 13, 15, 17, 18, 19, 21, 23, 25, 27, 29, 33, 35, 37, 39, 40, 41, 43, 45, 49, 51, 53, 57, 66, 67, 68, 69, 71, 72, 73, 75, 77, 81, 83, 85, 89, 97, 99, 101, 105, 113, 9, 11, 15, 17, 18, 19, 22, 23, 26, 27, 30, 33, 35, 39, 40, 42, 43, 46, 50, 51, 54, 58, 66, 67, 68, 70, 71, 72, 74, 75, 78, 82, 83, 86, 90, 98, 99, 102, 106, 114, 9, 11, 13, 15, 17, 18, 19, 21, 22, 23, 25, 26, 27, 31, 33, 35, 37, 39, 41, 42, 43, 47, 49, 50, 51, 55, 59, 66, 67, 69, 70, 71, 73, 74, 75, 79, 81, 82, 83, 87, 91, 97, 98, 99, 103, 107, 115, 9, 13, 15, 17, 18, 21, 22, 23, 29, 30, 33, 37, 39, 40, 44, 45, 46, 53, 54, 60, 66, 68, 69, 70, 71, 72, 76, 77, 78, 84, 85, 86, 92, 100, 101, 102, 108, 116, 9, 11, 13, 15, 17, 19, 21, 22, 23, 25, 29, 31, 33, 35, 37, 39, 41, 44, 45, 47, 49, 53, 55, 61, 67, 68, 69, 70, 71, 73, 76, 77, 79, 81, 84, 85, 87, 93, 97, 100, 101, 103, 109, 117, 11, 13, 15, 18, 19, 21, 22, 23, 26, 30, 31, 35, 37, 39, 42, 44, 46, 47, 50, 54, 55, 62, 66, 67, 68, 69, 70, 71, 74, 76, 78, 79, 82, 84, 86, 87, 94, 98, 100, 102, 103, 110, 118, 9, 11, 13, 15, 17, 18, 19, 21, 22, 23, 27, 29, 30, 31, 33, 35, 37, 39, 40, 43, 45, 46, 47, 51, 53, 54, 55, 63, 66, 67, 68, 69, 70, 71, 72, 75, 77, 78, 79, 83, 85, 86, 87, 95, 99, 101, 102, 103, 111, 119, 9, 11, 13, 15, 17, 18, 25, 26, 27, 29, 30, 33, 40, 41, 42, 43, 44, 45, 46, 56, 57, 58, 60, 66, 68, 72, 73, 74, 75, 76, 77, 78, 88, 89, 90, 92, 104, 105, 106, 108, 120, 9, 11, 13, 15, 18, 19, 22, 25, 26, 27, 30, 31, 35, 40, 41, 42, 43, 44, 46, 47, 50, 56, 58, 59, 62, 66, 67, 70, 72, 73, 74, 75, 76, 78, 79, 82, 88, 90, 91, 94, 98, 104, 106, 107, 110, 122, 9, 11, 13, 15, 21, 22, 25, 26, 29, 30, 31, 37, 40, 41, 42, 44, 45, 46, 47, 56, 60, 61, 62, 68, 69, 70, 72, 73, 74, 76, 77, 78, 79, 84, 88, 92, 93, 94, 100, 104, 108, 109, 110, 124, 9, 11, 13, 15, 17, 18, 22, 23, 26, 27, 29, 30, 31, 33, 39, 40, 42, 43, 44, 45, 46, 47, 54, 58, 60, 62, 63, 66, 68, 70, 71, 72, 74, 75, 76, 77, 78, 79, 86, 90, 92, 94, 95, 102, 106, 108, 110, 111, 126, 9, 17, 18, 19, 21, 22, 23, 25, 26, 27, 29, 30, 33, 40, 49, 50, 51, 53, 54, 56, 57, 58, 60, 66, 68, 72, 81, 82, 83, 84, 85, 86, 88, 89, 90, 92, 113, 114, 116, 120, 13, 17, 18, 19, 21, 22, 23, 25, 26, 29, 30, 31, 37, 44, 49, 50, 53, 54, 55, 56, 60, 61, 62, 68, 69, 70, 76, 81, 82, 84, 85, 86, 87, 88, 92, 93, 94, 100, 116, 117, 118, 124, 9, 11, 13, 17, 18, 19, 21, 22, 25, 26, 27, 29, 30, 31, 40, 41, 42, 44, 49, 50, 56, 57, 58, 59, 60, 61, 62, 72, 73, 74, 76, 81, 82, 84, 88, 89, 90, 91, 92, 93, 94, 104, 120, 121, 122, 124, 9, 13, 15, 17, 18, 21, 22, 23, 25, 26, 27, 29, 30, 31, 33, 40, 44, 45, 46, 53, 54, 56, 57, 58, 60, 61, 62, 63, 66, 68, 72, 76, 77, 78, 84, 85, 86, 88, 89, 90, 92, 93, 94, 95, 108, 116, 120, 124, 125, 126, 9, 17, 18, 33, 35, 37, 39, 40, 41, 42, 43, 44, 45, 46, 49, 50, 51, 53, 54, 56, 57, 58, 60, 66, 68, 72, 97, 98, 99, 100, 101, 102, 104, 105, 106, 108, 113, 114, 116, 120, 11, 18, 19, 22, 26, 33, 35, 37, 39, 40, 41, 42, 43, 44, 46, 47, 49, 50, 51, 54, 55, 56, 58, 59, 62, 66, 67, 70, 74, 82, 97, 98, 99, 100, 102, 103, 104, 106, 107, 110, 114, 115, 118, 122, 13, 21, 22, 33, 35, 37, 39, 40, 41, 42, 44, 45, 46, 47, 49, 50, 53, 54, 55, 56, 60, 61, 62, 68, 69, 70, 76, 84, 97, 98, 100, 101, 102, 103, 104, 108, 109, 110, 116, 117, 118, 124, 9, 15, 17, 18, 22, 23, 30, 33, 35, 37, 39, 40, 42, 43, 44, 45, 46, 47, 50, 51, 53, 54, 55, 58, 60, 62, 63, 66, 68, 70, 71, 72, 78, 86, 98, 99, 100, 101, 102, 103, 106, 108, 110, 111, 114, 116, 118, 119, 126, 17, 18, 19, 21, 22, 25, 26, 33, 35, 37, 40, 41, 42, 44, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 81, 82, 84, 88, 97, 98, 100, 104, 113, 114, 115, 116, 117, 118, 120, 121, 122, 124, 9, 17, 18, 21, 22, 23, 29, 30, 33, 37, 39, 40, 44, 45, 46, 49, 50, 51, 53, 54, 55, 56, 57, 58, 60, 61, 62, 63, 66, 68, 72, 84, 85, 86, 92, 100, 101, 102, 108, 113, 114, 116, 117, 118, 119, 120, 124, 125, 126, 9, 17, 18, 33, 40, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 81, 82, 83, 84, 85, 86, 88, 89, 90, 92, 97, 98, 99, 100, 101, 102, 104, 105, 106, 108, 113, 114, 116, 120, 9, 11, 13, 17, 18, 19, 21, 25, 33, 35, 37, 40, 41, 49, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 79, 81, 82, 83, 84, 85, 87, 88, 89, 91, 93, 97, 98, 99, 100, 101, 103, 104, 105, 107, 109, 113, 115, 117, 121, 17, 18, 19, 21, 22, 25, 26, 49, 50, 56, 66, 67, 68, 69, 70, 72, 73, 74, 76, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 97, 98, 100, 104, 113, 114, 115, 116, 117, 118, 120, 121, 122, 124, 33, 35, 37, 40, 41, 42, 44, 49, 50, 56, 66, 67, 68, 69, 70, 72, 73, 74, 76, 81, 82, 84, 88, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 113, 114, 115, 116, 117, 118, 120, 121, 122, 124, 9, 17, 18, 33, 40, 49, 50, 51, 53, 54, 56, 57, 58, 60, 66, 68, 72, 81, 82, 83, 84, 85, 86, 88, 89, 90, 92, 97, 98, 99, 100, 101, 102, 104, 105, 106, 108, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]
def cutCount : Nat := 1207
def inputs : List Nat := [0x2aaa92a4a826ac9555544944b92a2aaa928adfed7b5d556fde24a92aaaa5a5244295a9dac9511556975a88a8445aa7a724a4495a5ec9251256579449504d55ed0a490a4a6daf22a24a92b5bc8949255adb12541356db421522153b4f908a49296af90894912b55e225412ab5fef76ab76fbb7c8445491e5bfbddafeffbf8892853b5fef76dddfdb7c449224eabfffdafeffdf112512eb78000000000000000000000000000000000001ffffffffffffc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ffffffffffff80000000000fffffffffff0000000003fffffffffff80000000007fffffffffe000000000, 0x333324c9314b112699989269124c533324d56249926999846449324d333246488726d12d1262299b22adddcf6eef357a48c891ac953fb6ff7b657c92629699520c921c9436d444c49324dac91192468d6c2498a58b6cef79b779adf5210c92323557bdd9fbb3ef44498a4c5aaf7bacfbaaddabdeee7fb7ee9088ca454d511232a25a9f7bb7eeaedabffdbfedfd8449324a56a2249a4559000000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffffffffe00000000007ffffffffff8000000000000000000000000000000000000000000000000000001ffffffffffff00000000000fffffffffffc0000000001fffffffffffffffffffffff000000000000000000003fffffffffffffffffffff80000000000000000000, 0x3c3c4711c28c0238e1e1238224709c3c4701848e238e1e088891c471c3c0779febc71dbe23844e1c4431eef37773c672fef3fdcf19d23824638621238518e183bf1faf1f38e687091c08e313fde7f73e7148e1460c70f7be3bbe2e667bdf1fbc79e210e121c189888e147060cfbdcf3dccee33ef779ddb737deef7766e67ffbdfb7cc4223888c8e30891c489310891c48c98c448e08862000000000000000000000000000000000000000000000000000000000000ffffffffffff800000000003ffffffffffffffffffffff8000000000000000000007fffffffffffe000000000007fffffffffe0000000001fffffffffffffffffffffff0000000000000000000001fffffffffffffffffffffffffffffffffffffffffffc00000000000000000000000000000000000000000, 0x3fc0781e04f047c0fe023c13c7811fc0782608f03c0fe0310f1e0781fc08f81113f81e307c088fe078c10f018783f8438f011e0fe063c04783f8463c09e0fe07dfe3cfe7bf07fff1ffcffc1e1e04782f818f02782f81fbdfc3dfcf87fdefe3ffbe7fdefe3dfdf1ffffe7ff7cf421f021f0f03d087811e383a10f0478707a23c13c60e843c10f0f03d11e08f1c1d11e08f0e0f88f04f18380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007fffffffffffffffffffffff800000000000000000001ffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x3fff801ff8ff9bff0003c01c07fe1fff803fff003ff00041f1e007fe00037fe1e3ffe03fbff0ffff80fff00207fc007cf0021ff001bc0087fc007bc001ff001beffc0ff83ff8f7fe1ff0ffe3dff87fcffefffc7fcffe83e003e00ff841f003c03f841f003e01fe10f007807f083e003e00ffc20f801e03fc41f007807f843c01c07f107c01f00ffc21e00f01fe21e00f00ff00f00701fc3ffffffffffff800000000000fffffffffffe00000000000000000000000fffffffffffffffffffffffc00000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x3fffffe000ffe3fffffc001fffffe00000380fffc000007e01fff800000c7ffe03ffffc03fff0fffff01fffc07ffff80fffc1ffffe3fff07ffff83fff1ffffe3f0000fffc000f8001fff0003e0007ff000f0007ff000fc0003fff0007e0003ffc007e0003ffe001f0007ff800fc0003fff0003f0001ffc007e0007ff8007c001ff801f8001fff0003e000ffe003e000fff000f0007fe003ffffffffffffffffffffffff00000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x3fffffffff0003ffffffffe007ffffffffc00fffffffff8001fffffffff07ffffc0000003ffff0000001fffff8000000ffffe000003ffff8000003fffe000003fffff0000000ffffe0000003ffff800000ffff800000fffffc0000007ffffc000007ffffc000001ffff800000fffffc0000003ffffe000007ffff8000007fffe00001ffffe0000003ffff000003ffff000000ffff800003fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def scorePool : List Nat := [0x3391231d84c44b74c1, 0x1d81233394c44c14b7, 0x3391d81234c14b74c4, 0x3392891234c14b74c4, 0x3391232894c44b74c1, 0x3971232894c44b74c1, 0x2891233394c44c14b7, 0x3971231d84c44b74c1, 0x2891233974c44c14b7, 0x3f23391d84c44b74c1, 0x3972891234c14b74c4, 0x1d81233974c44c14b7, 0x3971d81234c14b74c4, 0x3f23972894c44b74c1, 0x4833f22894c44b74c1, 0x4831231d84c44b74c1, 0x4831232894c44b74c1, 0x3f23392894c44b74c1, 0x3f23971d84c44b74c1, 0x4833f21d84c44b74c1, 0x3971232894c44ba4c1, 0x3391232894c44ba4c1, 0x2891233974c44ba4b7, 0x1d81233974c44ba4b7, 0x3f22894834c44c14b7, 0x3f23972894c44ba4c1, 0x3f21d83394c44c14b7, 0x3f22893974c44c14b7, 0x4833f22894c44ba4c1, 0x2891231d84bb4b74ba, 0x2891234834c44c14b7, 0x1d81234834c44c14b7, 0x3f21d84834c44c14b7, 0x4831232894c44ba4c1, 0x3972893f24c14b74c4, 0x4832893f24c14b74c4, 0x4832891234c14b74c4, 0x3f23392894c44ba4c1, 0x4831d81234c14b74c4, 0x3f21d83974c44c14b7, 0x3391d83f24c14b74c4, 0x3971231d84bb4b74ba, 0x3f22893394c44c14b7, 0x3971233394c14bb4ba, 0x3f22894834d04c14b7, 0x4831d83f24c14b74c4, 0x3392893f24c14b74c4, 0x3f22894834c44ba4b7, 0x3971d83f24c14b74c4, 0x3f22891d84bb4b74ba, 0x3f22894834d04ba4b7, 0x2891233394c14bb4ba, 0x2891234834d04c14b7, 0x3f22893974c44ba4b7, 0x4831231d84bb4b74ba, 0x1d81234834d04c14b7, 0x3f21d84834d04c14b7, 0x3f21d81234cb4b74d0, 0x3f21d84834c44ba4b7, 0x2891234834c44ba4b7]
def stateCount : Nat → Nat
  | 3 => 1
  | 4 => 19
  | 5 => 100
  | 6 => 666
  | 7 => 2297
  | 8 => 1552
  | 9 => 67
  | 10 => 1
  | _ => 0

def stateKeys : Nat → Nat → Nat
  | 3, 0 => 0x7a9af500
  | 4, 0 => 0xdf7bd77cd53618bed2a00d90bd850fc7afd38da4a30970d6a00b6029904204727bdd1a3d70682ca957a03fe653aa77ff51c47ccb501bb00a24b9b7db05176fda
  | 4, 1 => 0xed6911e3eb0b61e3e0aa13c9
  | 5, 0 => 0x305ac8f62cdc0cb929a31f2b2727fca92266251715bc9751146cdb5410c956660ce21b840c4dd6c809937ea80769ba8a061a7ef705afb1f20493998700954a0c
  | 5, 1 => 0x5bb68832592a0293560736c051999c0a4df7f4ba4ca79ae44c39d6ee4417130443ed03f44037395f3f9868aa3c1390e638fb76e038cbe0f734b957f3342662af
  | 5, 2 => 0x8798115685ff1d437f9367317cc0728f7a3174c2793b49f07515269f6e7590766e3ed02f6b59798e683dd9f567297778666f20f95f9b24745dcd54ea5d5cf5d1
  | 5, 3 => 0xb0f87a9aaf9b96daaeb99e77adc79bbcac7f9012aba3d92fa67a643ca63028f3a3d9c1f2a0f4688c9a5c6b8494044e438c6f311d8b5273a68b053b2e8959df2a
  | 5, 4 => 0xcd0d0670cc225aabc9522082c6be5ee4c66c6b01c578a4b3c5719407c4dd0d92c46ebf61c21acb4ac1c918aabdf19b0fba68d34bb440c4a7b27b7acdb24dd6be
  | 5, 5 => 0xf7fe369ef46e03e6f32db6c1eee1c0b5ee142c1eea918445e72fe4d2e5694123e38c7a92e1d77b95dd2844b8db4dedd8da6dd619d93692e7d4933e46d1ad1177
  | 5, 6 => 0xfeb7d667fe557ee5fcbbe10cf997ee48
  | 6, 0 => 0x833025708035b3d06a34b01063bbf5a05ff234605ca339a05c5012205aa85dc055a70ed0467131d04230a4001e420a201468e2500e7cfae00d12aa700699d44
  | 6, 1 => 0xda5c6070d27fca90d10ada30c88fec00c6236240af889880ae7aaf60a504f720a4b9e4b0a260a810992143308f1933a08eaa3a508de4fe308599b9c08449ecb
  | 6, 2 => 0x1531339614fbaf8514a8d6f3149621a913c2a1641352ebaf1320398712ccad42126ad80e1204933f10a79f0e10a696191091561b0f6ba37d0f226ceb0e6769b6
  | 6, 3 => 0x1a050c0519d82b2a1909636a18efe3e318ae86c31867c5071805a62117f532d017d925d0175a354e16d8e1af16c23f2916c196a816396a12160ff38415d4dd66
  | 6, 4 => 0x1d7f00511d2430491d0caebf1cf846aa1cf3b1811ce2eae81c97d38e1c87fcda1c0d19e51b87abe71b7a0d541b68ea171b10c9b31add2a811adafa911aa9d452
  | 6, 5 => 0x24a8c715246e357c245cae8e23ba978d224f768021fe59f921f7f1a721deb7e121ae211b21a85801212d680020abba95205d8f3a1f7255f91f0053621eaf4a59
  | 6, 6 => 0x2ac473e72ab8db332a8879f529c50e6a2988aa6b2960a396290e6cec282c3d8127fa8cb327b9b42926e7bc89260a10fb25f54a302594426f2548350924f9dcc0
  | 6, 7 => 0x30a3699a3079c5543042fd932fdaf49f2eff67702eaf53112ea62a112e5716292e3774a32e34edd72d76f6442ceaf6492cadf7b92c561cdb2c103bbf2b5bbc15
  | 6, 8 => 0x35118927347a58d43445c8fb33add1c232aff55f32a8d26b324c3dcc32327a5e321643f531efd8ae31edb006315b3fe6312c495530de977230b5137830b38e16
  | 6, 9 => 0x3affb71c3af93f763ad542eb3ac09f723aa8fea03a3b72263a066b583955e91c38f5d9273845cd47377b1416375639943743ba3837114c2f364d38cb35b39229
  | 6, 10 => 0x41510c234139f08641119dd940ec1e293ef949d43ec431b83e7656c13e3a80af3de15e6b3dd272b33d089a4c3cc57b853c90dd633c1657333b7edd5d3b5b0dbc
  | 6, 11 => 0x46c338964663b2db45fe393545fb6c3f45e33c0a45956c1844c967e844c5c3bd448c5afa4432de044432093f43c01cb6432520f942f90f9a4216d2a842099792
  | 6, 12 => 0x4b7f4c524b4a1a474b3e79d34af25b064adfb2784a5d51b84a3a21f649f8ed254949934748ec9a9f47e79b4847ddb40f47d5202d475533974706732646f2822d
  | 6, 13 => 0x53ccf96e529283c05290fac85230cdf451c4d67d51341001512b8d175025ce8a4fff9fb24ec74e1f4ea1b1ad4e0fe0df4d744cbc4c8106424bf885ee4b8387f4
  | 6, 14 => 0x590cd39d590be54757a42e5a5792b3d356c54baa56a4f16856a0d4d156645df05647e1b05641ddbe563eb8795564ea6854d498c254c9efc2548edf8c54294545
  | 6, 15 => 0x5f9f49875f0710195e298b9e5d9642a05d917c9c5c7bd27b5c4756b95befef895be9803f5b085fa65aa61db05a83186e5a5a47565a048c9a59e681da5972e9b3
  | 6, 16 => 0x63edfe9963679d20634bf83e62c0efde6211cfd761ae9be8614c57716128f11660d7371f60ca260360b7edae606021b6600c0f705fe2a3905fceeb9b5fc23dcf
  | 6, 17 => 0x69f3f0a9691a841a690ae36167ee304267a6bff867956d4267297a9166e930eb666b485a65efa9c865ea4731656e929964f2d26e64ed4c0864e907c06400a708
  | 6, 18 => 0x6fffd28b6ff504796f64d2106f4739d36f38b4036ef0ab486e6949b16de2f9f36dd086fe6d8eb64c6d6637a46c3290376bbb72966b76e7d06b50db706b0e068a
  | 6, 19 => 0x7536484874fb700774dcb6b07461c1d173c5e42d73b1b8857365fe5872fc270f72f96f0b726d0d787228d6a370f26a937090f34c705b3e9a7026a4267020ee17
  | 6, 20 => 0x794df09e790ac6137906223d78cbf01878ca4b5078b3a04e78a3a86378820f3e77c1efc5775abadc76fcfd9176c89d0e769cc3d175f1928975c1305a7597c47a
  | 6, 21 => 0x7db11dbc7d89f4317d4a82327d0b38f87ce08fc37ccc8a0e7ca6960d7c6e2dfe7b452df17adca0877aba5b2a7a8b0db97a6a06257a19717a79bfae34798b7f2e
  | 6, 22 => 0x86db0e5885d8cfa384d6f5d584410a8884027a1c83dd4a3183c0516d8355dd28830ec81a828c34b481f1fa0b818697e77f5f6e1c7ef8f3b47e7b5db07dcc2fef
  | 6, 23 => 0x8c0d32f48bcfb1a68b9ef1188a6e50d28a01b85689c166718985cce4897517c38970be5e88e0cebf88b147f988385577882057a887b4b5cc876c9358871c4262
  | 6, 24 => 0x923f7d9c9218529f912edf999107323490eaedae90a86b7d907fd433902bbcfe8f4e4b168f4cdddf8f1f99908e99b92f8e7bb1e88d6aa1df8c59677c8c386997
  | 6, 25 => 0x9a7b1ff0998b58da996b6df6985a90ab9841559e9833fbaf977cd64c954fda1d9539637694de302d949e36f9946ba650944039c693371a689313e37e925c9ac4
  | 6, 26 => 0xa08c9d6ea0788e18a060ea979fdf95289facd0539ef0bcd79edee1989eb4fe619e9972fe9df9b9609db94f0d9d7159779cf9686d9cd529689c3ee0a89c298907
  | 6, 27 => 0xa916bd6aa901416da896aac3a78b462da7795dcea76706b6a736f081a705fef5a6ea81a2a6d63747a4f1903fa43bf76ca369ae2da31a1487a29062b3a0ddb9f5
  | 6, 28 => 0xad8d4affad88a3a8ad3d9686ace5599eacc3314cac73d771ac2a97b9abf6dc01ab8dd3f9ab48d886ab3c3b2eab259862aaf0bccbaae36056aaaaca86a9e9ff8a
  | 6, 29 => 0xb2a417feb25053f8b23c1537b235991eb1ce2293b0597a12aff7da0dafba8ccaafb41579afa93129aed5d1f2aea7d011ae342704ae33791eae305820addcbd3e
  | 6, 30 => 0xb992453bb98dfa91b8c7f61ab8b576beb894aecdb6aef6f6b5eb6f35b51f9987b4fa3048b4851a2db4612e8ab45d1426b376737db3089c49b2e43654b2c427be
  | 6, 31 => 0xc10d0c56c109d9f8bf8c3507bf092b8cbdd8a63dbd878d49bd4289b4bce86523bc82b912bc6f83afbc46ff71bc1dba95bb1f20d8baca105bba05600fb994ac77
  | 6, 32 => 0xc77ade14c6b08f7bc69c9de6c63b246ec5ba149bc581bc2fc555acb7c4ce8daec4c8cf97c496dd7fc46acc20c41cacacc37b5418c2d60f0ec2cc13dcc24e602b
  | 6, 33 => 0xcb56d827cb26a49acb0f49b7cabb4fcdcab0620eca38f925c99a0cacc9791edcc962167fc95703c5c8fe31c7c8641fd3c85a6b1ec84ee752c834f51cc7d56f61
  | 6, 34 => 0xd3a28a7ad2fae3b5d277ee18d262ec7ccfb1be40cf3bdc5bcf0a5e71cee60942ce8de327cd70104fcd4966aacd288bc3ccf108d8ccb03659cbabcbf4cb6aa9ab
  | 6, 35 => 0xd7eb4ef0d79b8c93d79a28bcd712a96ed67e3d20d6465548d5eafbb6d5d5e5c6d5aecf7ad54155f1d4ef647bd488a4f5d46cb580d443023ed4044046d3f32ddd
  | 6, 36 => 0xde9a52e5de56b813ddc53dc2dc7a1c2cdc3b1ef9dbda25d7db2f652bdb2b82ecdac7ecbada13979cd9cf6655d8e88acbd84c15afd81b8314d814d7ebd8129157
  | 6, 37 => 0xe4d959a6e4af2112e48bf437e4788aa6e41350b8e3ace44ce37b8f7de37042b6e2b4487de1cda97fe14b6288e0f79485e03cdf5de0079826df6ae6b6ded8d589
  | 6, 38 => 0xedcb4217ed8e3d03ed60a07ced12cd16ecd8fb46e9da7a3de9d34a70e8f12213e89b3717e7a1b559e75e4743e757f5dfe741b84de7135e54e6feda3be63f30f4
  | 6, 39 => 0xf44f73cff353d484f2f00546f2d6a620f25b40d9f197ccf1f1476bbef0e48615f07c3d0ef01b5682f002d64cef1f36c1ef09a80eef0072d2eeb4e79beeac41ed
  | 6, 40 => 0xf99af480f92d308af8a9b905f8a7b4eff80bddc9f7e92257f7dc3413f75a338df741e3c3f73f71c5f7166d8ef7163b53f558495bf54c5e3ef52b0746f47fd5fe
  | 6, 41 => 0xfea6fde6fe8cf5a6fe88730ffd049b83fbe6eaf1fb6ed338fb5acd83fa1564e9fa0b4330f9cdf5b0
  | 7, 0 => 0x1da57ca01cd1cb401bd496301bb2aa901b19ad1018e8de0017eeb270157b52c01498c81010fa0630108a39700dbbbfd00cee63800aa76300069acec00474d10
  | 7, 1 => 0x2ed3f8b02e8a61b02d253a202bc94bc02afe86702af5498028f186e024b1210024599410219afa202130589020719a801fff32901f84aaf01dcad5201dbc7f4
  | 7, 2 => 0x57ae5660559e3c60558f13a0527dbf5051c1cf204c28193048ced0a03a77553037f330c0368e67f0362c57c03600741034734ae033d6609030ded170308a011
  | 7, 3 => 0x78077600772e59b06f9933506dab6bd06c931810686bdb8063eedfd063ce3650635171f062737fd06264bed061096110605a88505e69cde05cfc4250595a548
  | 7, 4 => 0x8e524cc08bbb8ec08aa50fc08a9411c08a38305089c00c7088aa7ab0878284f086fef680850377d0837bec5081087a4080249cf07ebd54807e3a1fa07e02575
  | 7, 5 => 0xa25c4a20a07e1f909fda71809ea612d09bc724709b637eb0985c380097e1786095acfff0955602d0950b8b4092d66590923fb9a0919c05c0917444f090d1869
  | 7, 6 => 0xbda92a90b9c5f6d0b9b2f460b90a7000b7516ac0b48fbbe0b42d1740b324c410b3143cc0b01fef50af17f0b0aeae5330ae8c5d10ad295690a8c7f330a8a5733
  | 7, 7 => 0xd98a1da0d90efae0d7478680d6d4b6d0d685b8f0d37d1de0d363d760cef116b0cb981860cb597700cb4736d0cb267200c8253e60c5ffe650c3866950c09b102
  | 7, 8 => 0xf1c5bfe0f17eba70f1705990eff84de0efc74d40ef453ea0ed019950eb74f8f0ea1d98c0e6a60da0e6536cf0e0e08630df8d8c90dec88780dea880a0dc9b48f
  | 7, 9 => 0x113929ec1129f4c11107a27410e3ae0f10c358e810a01b2f103822861019df970ff425ec0fc1a2af0faaa5ba0fa6d8e30f8526cc0f7674f30f71e4010f6fccf3
  | 7, 10 => 0x1296d5db125608e212524c41121f3d82121924b512177a0e11f4531611e6162711d4042111cd8fb511885b9f118419221180e7311176ca5e1149cccb113ad7f6
  | 7, 11 => 0x1479b0361467e75814598f10142d7db1141bd5e7141043fc13fdc4a013f6ea4a13f421f613f2bad013c58643136d4540134b40bf133e05a91335310512c8be99
  | 7, 12 => 0x1625cb1f161dede11619cc3315fdd5ff15ecab4715c32659157cc62c1574d24315620e4f153c68b5152415d515185e4815185bdb14eb621714cb51d114981de4
  | 7, 13 => 0x17f7a6ad17ec465117cde14b179820f2173bb64b172108e6171db3ad1704e8b316f79bd116ea135816de000116c9da2f16a8d21016953c8c166459f316488da5
  | 7, 14 => 0x19a1f4d7197a1df2195cbe3d19531efe193b377d18fa0373189e238e187d150f186ec9761853254c1845251018279d6b1818f93d181227ae180f28fb1809638e
  | 7, 15 => 0x1af352401ade52fa1ad751f31acbe4c81a8642bf1a7e015e1a4b78901a469d901a2fa0c51a2dc2ea1a2702341a26dc2c19fd16c719c6e9c319b5d24719b05e81
  | 7, 16 => 0x1c4ef8d01c2e2ecc1c17b49f1c0adbdb1bf8b7b01bd53c6b1bcc4d071bc602601bb374ab1b99d3351b940cde1b9325eb1b74e5d71b7355f41b6e900d1b2d5b3c
  | 7, 17 => 0x1e68d27a1e5ef5221e4f70b21df790a41dbb21521d3f8f941d2a9e251d1777ee1d0c183b1d023c3f1ccea3d41ccd11011cb3ba691ca00cd61c92c2b41c72e7ea
  | 7, 18 => 0x1fdf2b611fd61fc41facc83c1f74f4791f4bad031eec1c191ee8b6061ed7ed931ec873261ec3a1fa1ea8bad31e9e6c001e89a2b91e785c971e723d5e1e70363e
  | 7, 19 => 0x20f79f6d20f61a0b20f4f43220f24b2720e9b148209dfa9920979c13208a39a820899e7320431c412032acb1202acea6201cadf9200a9eec200437fd1ffc5026
  | 7, 20 => 0x22750653226c70ef22393031222dda482229a05721f7f1a721e14bfb21d6794f21be368721bcfe7a218972b72166cf572161ffca2145696a2139e219211d8770
  | 7, 21 => 0x23ce9ef323c6f1d723bd20d123653c0b23448237233cb1a7232b2242232950e7231dbd4322fbb37522f9449422eb5e6022e4569622de014322c98b5e22bd925e
  | 7, 22 => 0x267a4ce5264ee2f9264105d126263ef226141f57260906d925f61e1e25ddce5425dcd938256bd13f256526f025122bb4248c13a4246c422a245ee91024105e95
  | 7, 23 => 0x27d542e827cffa2827cda20727c6ce1a27c191af27aad6bf27a518a82768ba9a2742a47626ecffb326c7d3a426b2f78d26af36ad26ae70df26acde0d269ad9e0
  | 7, 24 => 0x29a67b5829a458bc29890fce295602e3294ee46f2934d64e28b90dd128a1886828a0f52a28632db3285cb1aa2856f5d0284bbbfb28432fa02825deef27eb1a19
  | 7, 25 => 0x2bb786852ba176cb2b764c112b654a102b1d39442ab8db332aa2d5332a85ed642a7886912a6e6e092a52f0ca29f737ef29f4d49729f0dcef29e47ec329cd7c69
  | 7, 26 => 0x2d95bda62d83eded2d7bc4d02d6baf642d523b6e2d245da02d1df5252ceaf6492ccb1bf32ca05a5f2c9a150b2c4a96842c3ccdbd2bf615592be0059f2bc79f64
  | 7, 27 => 0x2e91e7db2e7ee0e52e7274612e59d5722e4fbc482e3774a32e3062ee2e23ea602df75d482deda9122deb92c82de352f82de000d32dbc54d92dafb6c12da35b90
  | 7, 28 => 0x2fe5d4f82fd396752fc357ad2f5bbada2f56591e2f4c8e282f440da02f2300a42f185d882f14c9aa2f12b2542f06bdad2f03aadc2ee29e712e9b871a2e9ad0d5
  | 7, 29 => 0x31660664312eaa1e3127429330fd454130ea765830e7abca30d523db30d0a3d230c2273030ad097530953e3b307b6ec1303e99ae302998892ff845a92ff13e46
  | 7, 30 => 0x32f9ea2f32b88cca32b28ea0329544f1329242173276fa0e326f0e41325640cb31fe941a31f200fc31dbc4a931a9700531a6ab1f3193604b318ea32a318b6b52
  | 7, 31 => 0x349a749234749534346070b534467068342ae4f6341dbd5c34053c5e33c0bf4333add1c2339e26da33793aa0336c7643335f9806335adf393353f337333333e0
  | 7, 32 => 0x3608701e35ed7ec335a3be82358c68773588a348357dd6d73575b0fb3554a5ef353909a2353467c3352cf22634f9cd6a34f6740d34bb3e96349eaa1b349c0b37
  | 7, 33 => 0x3748fe91374433593743ba38373a14d7372d4ad8372ba660370907a53705895f36ee6e1936d60fe536cf76ee369f45c9365d50c336596a4e3653ac3736384a18
  | 7, 34 => 0x39170fd53901612139005b3a38a9f9f1386a88b438672d85385de8a838388c2f3836d26f38330f8e382a273d381208d938086cc53804967237d81a6437668d5b
  | 7, 35 => 0x3b34e6fb3b2f958d3b1c97313b100f143ae7b7ae3adf343a3acd64883aad28163a6e92aa3a5dfb803a191ee63a048b353985fbd1395e90ed3951818639183263
  | 7, 36 => 0x3d66fe4e3d50ee943d38cf933d1f169f3d1e2b0c3d1414a03c7a9e443c688aa53c61fef73c4d6bca3c47c3813c3b11e33c2145a13c0c34cf3b8f0ac23b455a62
  | 7, 37 => 0x3f07ead23efae6623eef64893ee65dc23ec324633ebb28bf3e8e1ffa3e7838f13e498cd43e3ef5ed3e1a88313e01229d3dd108543db910a13d913dba3d7aee72
  | 7, 38 => 0x408a2b774062f52840426c2b3ff5fcff3fdb2e563fd0a69f3fbdbaae3fba13013f963f593f7efc683f7239f83f6ef2a13f6cbeb53f43e6f43f22f33e3f1d2aa3
  | 7, 39 => 0x4272164e4265bf8342447dc3422ae68a421df26a41ea97f641c82644419e48a441769bf64162023b413440a2412f6feb4105d0e740cf10b340c260c740bbbafb
  | 7, 40 => 0x44bf14b244a19884449f61d5446f49134402737143e384f94396e07443779b5243766edd433d89d7432520f9431df9fa42f4443742d386bd42c1620042b2f872
  | 7, 41 => 0x466ab65f4657d88e4649ec5b463e5bb2463d261645f7922045cff0f545cddc9a45c15812457e0a7d455e29b5450f0fcf44f8887044f60b5f44f3835644bf990a
  | 7, 42 => 0x48a0f691485938034836121f4827e28147f343b347e7709e47e3dcca47b9ac8647b6264647a54df64732a3b34730187a470ebb1946d8e8df469667624690dc1a
  | 7, 43 => 0x4a63a1724a5372304a30e8b149efb8fd49d8167a498539454975b59c4944053b49323a49492e0f9b4912ed8a48f65ddc48f4e48c48f3ab2248ec9a9f48d68ae5
  | 7, 44 => 0x4c8583904c7521534c49c20e4c46a4b74c36e7d44bde0ea64b62763a4b440e4a4b0e08b64aefff024ae6eb354adac7574ad46bd94aab4e084aa17d9a4a6bbb03
  | 7, 45 => 0x4ea002f14e7ef0494e52e3a04e4337804d9737764d937d7e4d8d77444d7d6e4b4d6be7b94d59e2034d58b5c14d5444384d1771044ce373264cd4f57f4c952e73
  | 7, 46 => 0x50076f5a4ff3d32b4fe86fbc4fde037a4fd3846b4fb544574f9b10c24f99dda84f499c0e4f3a79234f305a124f0aa5f24f0270034ee31eb24edb76464ea48fde
  | 7, 47 => 0x51f052b051e2e3135177ee555157d66e515056ba512a1531511daaee50d97a1950d4747450a7d9725094ac205093dc33506aa0885025ce8a50252f85500e40e2
  | 7, 48 => 0x53fe0a2653f3b1cc53909af1538fef48538ab2a95376bfdf5371e08f5353fd74532c7a99531fb30a52fa9f8a52f7d97e52995ad1526b414152545bcc51fb7fd2
  | 7, 49 => 0x55c0809955a72dd7559a4933558e10cc558c439a558a046455292bf555135f3f54d4d06b54d498c25496795e549134bc547489c95461bc1b5456470e54383320
  | 7, 50 => 0x5897792e583f6529581f30f15807505757d909b657c3a38d5792b3d35774a1d2576c701a572bbce057213a8d56b5d29a5689c13b5635f3dd563235bd5601c0aa
  | 7, 51 => 0x5a36e5e25a367c9e5a2591975a1e2cd459f4647c59ecbcf859c11df459829b4e5954c5bf59488f6b592ef3185924d30d58ff88b558e5933858a5ac8f58a1016f
  | 7, 52 => 0x5c7de7835c62b5785c549fef5c4bb04c5c42110d5c330c145c28adc85b9367655b58753d5b34171f5aff10d65af80bbf5ad6491a5ac6b9eb5a9cf2925a84dc68
  | 7, 53 => 0x5ea266ba5e8217fa5e63d7e65e4a18415debb4485ddfbf6e5dd45fde5da7e3d05d899ec65d74dafc5d45b8e35d2af8e35cd35f2f5ca175895c8f983b5c8345be
  | 7, 54 => 0x60637a0c605407a760502290603f1ce56019593b600669fd60011ce25fe12a0c5f7b00df5f55c8655f4d9d4c5f31dfb95eeb06535ee6679c5ee24dc45ec2aa36
  | 7, 55 => 0x6297152862502154624fa5ca6235964461db0e286164bc20614719d36120327e6112d47260e6af8160dd066b60c22dc960a13f1760a0b7226095c54a606c119f
  | 7, 56 => 0x6503753d64da621064d7e0b164d5f6ff64becf42649182e8646b887f6455c1666454913464018853638ceca863709bb3635e776d633aec1863302edb62f786f9
  | 7, 57 => 0x66b138da669a184566844834664ca141664b79df6623356166037d3c65f2242065da506f65d2a51065a91c15659f7cd665830b6a656e92996555881e65483d0b
  | 7, 58 => 0x692f75ea6927d38f68eab5d568da428c68ccc06368b0a96c6886cee868654a63683960c4682ce92f6829e3e0682156c767ee304267df83c3673f8986673ce2f0
  | 7, 59 => 0x6a9fdc0d6a6e4fa86a3186726a20fdfb6a1c26946a1befe26a077f2a69ef149b69e2aad969cffd9969ad84ac696d50a66968dd3769668d416963d5c6694e932b
  | 7, 60 => 0x6bf35a8b6be73e366be1801f6bd9a3f86b971f656b85793f6b7cb4d46b3879f16b02d8d56affc0506aeace426adfa4496ad44ad66ac1f3b36ab05af56aa544e4
  | 7, 61 => 0x6d011ba86cf310086ceb53546cea58716cdb7fd16ccd36376cc28cd46cc1e8ef6cac5cc56ca8dec06c935d476c86b66e6c6a4fec6c59e8206c3290376c2fddf6
  | 7, 62 => 0x6eedbd246ee919de6ebb1f646e8d9d386e6d7c166e6b55336e2cc65f6e23f9b16e1f45b76dd676ed6da14a4a6d926a5a6d5130076d174e506d0d511c6d0d193e
  | 7, 63 => 0x712d95df712a78a8710bce6770f0baca70b78aae708140a9707c25a17044b48470134faf6ff61f236fd8085a6f80a12a6f7e11ec6f3f83186f37bc386f32ff4d
  | 7, 64 => 0x7287949e72876f6b725c396c725902be72427bf6722a2c2c7228d6a37212280c7209e48571ff9a5971f96f2171c10b8571b036797190ab587190a1d5715d5129
  | 7, 65 => 0x740ebc0273af5121739f7db3736351be736237af7345b328733e1c18732d1ec8732a4f12730e7c477308950f72ffe0cc72cc216b72b4765472979192728cb52d
  | 7, 66 => 0x7599ac74759143ce75316c9875241341751981ca74ff9d6774fb700774e5fc2674d33d9874b94adb74ab1ad074a83b98749b96607494f38e74253079741eafdf
  | 7, 67 => 0x77f0e02c77e401e977b2f50577aa93b477a7b1b37797a4ea777c20a0772eeffc77238e1e76f42e6d769cc3d17697eb2f768cfbe27672cc997656c49a75bb63e3
  | 7, 68 => 0x799556be798968d279517fb3793cb8e0792cceea79235ab4792291a978cc913f78b2fcf878adcbe57894d7b17858f8d6785833ef784aec3e7833c17d781be435
  | 7, 69 => 0x7b1e6da17b0bde657af6424c7ae2a5fa7aba5b2a7aba2c327aa70c097a8b17e97a7c32967a52008d7a4b2b817a32c0b27a29fe717a10415679aa861f799e8835
  | 7, 70 => 0x7d4b126b7d46a7d67d4045207ce155117cd1c76b7cabfe9c7c85a48f7c76709f7c3af8bc7c243b4a7be5ac767bdf389d7b98ec007b8b6a1e7b33d6907b30ecfd
  | 7, 71 => 0x7f5fc6d87f5a109d7f4199267f3693af7f3349127f0e03fc7ec218fc7e72049d7e2472f07e19c7b57df79f637ddf389c7ddc138e7dd9c0d17dc8d6b27d95d7a7
  | 7, 72 => 0x80a802b08092ce408080a42f80689b3f8060c109805a3eee805944a780519a3680381d0d800a83b27fdc3e287fc8415b7fc341d87fad321e7fa2d4ba7f8f69d4
  | 7, 73 => 0x83b5e1d083760aec8370834e8340232182eba3a182c49e09826ec40c825de4b08211e54d81d795f681c7dd3981bad8f181794ffe8136a59780eefae180c63813
  | 7, 74 => 0x84e98c0484d43ab384bbc16384b4003d849212d0848c54b98484a10d8459c748845383fc844dc5e5843d0a60843519f1842f501984087a878402565583e734af
  | 7, 75 => 0x86e163e9869c066f867e230a86674e0186446b5786340c9e85feb02085e44afb85e1e0c3856e8ed0856bd762853cbf5d852695868522a0968518e02584ffa30d
  | 7, 76 => 0x88ccc68588c6f9e988af1a4f88642456884d1bc4881f18ec87dd98d687b23f0f87b175f387a1390c87957a4387736841876b535987585964873e63368711a7ef
  | 7, 77 => 0x8a364ecb8a1d247f8a0bfbc28a056e798a01fca189f94f7a89f7a0ee89c91ce4899f640689914b62898363338964bdbe895d91ce89189aa888de67c588d1933c
  | 7, 78 => 0x8bf69f048bbb50798b8fe8a08b6f51168b61da798b25042e8aee41da8aed8f3c8ae877108ae341458ad2ced98ac268a88a9440058a456d7c8a3faf658a3e6644
  | 7, 79 => 0x8e7b81bd8e5168498e351c588dd3dea98dd3a08e8d95243f8d9059078d5e4a568cf37a448cf1bde28c8bd6348c7497328c550a118c538eef8c345a048c1f09bc
  | 7, 80 => 0x9113bdaf9106aa5990f50fe490efdf6690d3f2b890c1eb079089a82d908629859008cf488fa4ddea8f8e16d88f5f9fc68ef61f9f8ebbfb608e8c2fe88e80a677
  | 7, 81 => 0x93b6b2ff93ac0a739382ce42936a50ba9333349c9326c61c93187d6b928c0e65924d02aa91dfb77991d9843491cfe4f591cf023091aa878d917bc464917bbb3b
  | 7, 82 => 0x9585df4695581da495270e0194fc941f94db9b3194c9b7339496dd119490811094826ff794303aa2942649b8940febe293fe266b93f1abce93bae07e93ba7d50
  | 7, 83 => 0x96c57de996c1c89096af1ad696aba03b96a1f4db967faed89660d29e9637e7499602fbc595fd3dae95e47bb495c5651d95bf469f959f89e695943de5958afebe
  | 7, 84 => 0x98c11fb898af4c2b98ac0fed988cc47297c979bd97c95be297bd064e97bbcfc297ba4a2b97aed41297ae27e9978026cb977de5fa976b26119768e210975dadde
  | 7, 85 => 0x9a7b883a9a698e3f9a6393e19a43dbbc9a3282a09a20034499e3954e99a8f8ed996e18f6996a0dab995bab2f99283028991ac0909909af4098eeb16798d4e105
  | 7, 86 => 0x9c90a0659c85d4199c47836b9c43b7ce9c3f890d9bd05fee9bc81a1b9bb109499b9f9b8e9b6c7bf89b6824579b5ce7499afd44f99ace7ac39ab86b099a8cffc1
  | 7, 87 => 0x9e6d4d5c9e6463399e615c7b9e5dd8079e5c4e629e5a944b9e463b8d9e1f49339e11c95c9e0b8f629dd81d289d8666e99d7c686c9d0128de9ce03a0b9cb1fa78
  | 7, 88 => 0x9fc2513e9fbe3e679f9262ff9f7bf7e69f7ab9ad9f6589349f429b5e9f3fd0d09eeae9899ed393c79ed15fb69ecf162f9eb96a779e9c5aab9e7605139e72e415
  | 7, 89 => 0xa20b3b97a1d559aba1b982f1a189f6eaa1889816a182d9ffa14ba7a7a139c7e7a134dbd3a0dd9294a0bb19a7a0ab9966a051245fa0394187a0220a22a000647f
  | 7, 90 => 0xa3b168d0a377067aa369ae2da3686c82a34835d5a33f149fa338b471a2fa0f35a2cc4f02a2b04b31a2ab9e9fa28bba2ba2768c44a269740da2493847a242dd7c
  | 7, 91 => 0xa5279bf4a5193978a513300da508905aa4e5e09ea4ae9132a49b9773a46dbe1ca4636b91a44c4b59a4497ff0a43c0fc8a41132b3a3d5a190a3d232d4a3c0ffaa
  | 7, 92 => 0xa7b505daa72d3611a71d8ecba6c25f5da69876b2a65b2797a63ff8d9a6218b2ba612bb95a6016a05a5b3bf2ba5a12397a59d12a6a5549db9a54f941fa52d2026
  | 7, 93 => 0xa93ffbe7a93b9350a93b182ba9354969a92e30cda91fbd07a8f26f4ba8e1162fa8e08bbea8ce96d3a8b6ab4ea892685ba87f2064a875852ba7d36a2aa7c9541f
  | 7, 94 => 0xab6bffd2ab4da5bfab32c574ab042dfaaac8482faa94f044aa8458ceaa81b98caa5bafdeaa45c9faaa3c2abbaa1cf8e2aa1344eea9ef6a74a9b401f8a940174b
  | 7, 95 => 0xad0ff00aad0ae1f1ad0a5bccacfc1f97acec5193acec0515acd53631acc3365fac9c8068ac8d1abaac820255ac7c31a8ac2a97b9abf35385abc6dfd6abbe77b5
  | 7, 96 => 0xaea42d0fae8860cbae786cbdae5f9e85ae297017ae1817fcae0083abadd21cfdadaf1844ada9b81dad88db27ad7d1760ad452569ad41a0f9ad395beaad330d59
  | 7, 97 => 0xb037b37ab0346b13b00d43a0b00c71fbb005cef3aff79429aff733e6aff449d9afd527d6afcec0fcafa93129af8794f1af1c0bc0af0abed4aee2bbe3aed62c5e
  | 7, 98 => 0xb1a5ba03b191467ab1870656b181a8cab1714d74b16b5c02b162faccb1383192b126bfe8b0fbfceeb0fae5e5b0eba2a2b0e5cd0db0ad3845b0830b90b07c90e9
  | 7, 99 => 0xb3314dacb30ef7bfb2ea1a1db2b38a68b298ff19b26f9339b25ee9efb24fdb14b240f8c5b23e81f8b23c1537b22c029cb210a803b1e23fb5b1cfc058b1afd700
  | 7, 100 => 0xb47f9266b45c8801b4435b20b42bc769b41d4f0fb412f8f1b406be3ab40666bcb3ae112bb3ac1639b39d4343b394742db38b1749b353bbfcb347b89cb34360cb
  | 7, 101 => 0xb5e05e26b5ddfd41b5c44824b5acf8bdb599c2fab583408db56eccccb50904bbb4fb5912b4ee8c68b4e4e3d0b4b58bfeb4b583fab4affd94b4a11f89b496168f
  | 7, 102 => 0xb7b55521b7b0e1ceb79fb935b786df85b77f0617b759a19fb746778bb742721eb71db8afb70568e5b702f6e7b6e605b0b6df29dbb6684dbab635d698b5eb6f35
  | 7, 103 => 0xb9f6b5ccb9e87da7b9c6539db9a4a274b97d1dddb9748a80b96990a2b910fbb1b8b576beb89cf713b86fae99b86b3a11b842b4d5b8334852b7ee8f76b7ebb898
  | 7, 104 => 0xbb83c9c0bb7917bcbb545d4dbb3989ccbb32585abb21224dbb1e52a5bae24110badda896bacb3dc5baaa3c2bbaa1e714ba693096ba679ed7ba4ed5fcb9f87ab5
  | 7, 105 => 0xbd367775bd1296aabd0d2505bd061801bcf1dff6bcd1135bbcb8c391bca76f0bbc8f6612bc8ee82dbc2baaefbbf541c3bbeba284bbcf45f8bbb96a21bb9781f3
  | 7, 106 => 0xbeb35cd4be587838be50b88dbe4bf831be2ba971be1e94bdbe1858a0be0d695dbdec5acabddaefacbdb44e08bd9df04ebd931fdfbd7df155bd74a137bd3f7e9f
  | 7, 107 => 0xc0a62514c0760b3fc0731c7dc062667fc0577f83c053a4d8c03599e5c02d2261c0297389bfe955b2bfaffb74bf8c3507bf83b1bcbf56ce0cbf239fc5becc3895
  | 7, 108 => 0xc24643bcc23881b2c2341d4dc1e25043c1cbcd4cc1a7a5bfc1a3f94bc18f8c9cc1849f9fc14bfb3fc13ec1f7c11dbc88c0efd21ec0e5b306c0ce4827c0b2d816
  | 7, 109 => 0xc4411446c42a983ac424735dc4198970c40b656ac400abebc3ff52ddc34fb318c34b3e6bc3367e1fc32dbcfac31e4c19c310e5dac2fc150bc28505a7c26af1b2
  | 7, 110 => 0xc5b44415c58916b8c583e1e6c56e0af9c53c1243c52f7c25c52cd6efc5145138c4ee481bc4ea27a8c4e13589c4d859a7c4c78525c4c30c71c496dd7fc46e86f7
  | 7, 111 => 0xc7885186c7832801c77ade14c75b006bc74c1aaec74a0554c71e4228c6ad6e1ec6a3d4b7c66afb4bc664be11c65f755dc630d138c625fca6c615fde3c5ccc6d8
  | 7, 112 => 0xc9783401c958c243c95269dcc910a22ac8f4101cc8d608b2c8d03ee2c8c10884c898c4d2c88ea1a4c87651dac873dfdcc85742b2c7f420a4c7c6e05ac7c16023
  | 7, 113 => 0xcbd94129cbbbb894cba5b479cb8bd88acb2ac515cb2165a5cafdaff7cae0319bcac00d58ca8b4886ca7d12a2ca50fd07ca428de9ca05c39dc9dc2306c99305ae
  | 7, 114 => 0xcdd23354cdcfe7f6cd7acc24cd7a3b06cd4887bacd3db71bcd2931ecccf4e078cceb81c6ccaa4aeccca3414fcc8f3b9acc4c83ddcc14b49acbeea686cbe11e41
  | 7, 115 => 0xd05e8abfd057fe5ed04eb42dd04dfc93d00b5ed6cff167c9cfbce126cfb9812ecf6d3ff6cf3918afcf0ed943cea21c5ecea17ab7ce95b2cfce91f51dce64e2cc
  | 7, 116 => 0xd30cc730d2fa4cf9d2dedd7cd2adabdcd2a30686d1e511aed19e0b56d18dee7dd1891d35d12f30d3d12086a5d1097e37d0bea76fd08fbdadd07badf1d06a1b36
  | 7, 117 => 0xd54155f1d519245dd50ff825d4fcb26ed4d3c2d9d450e4d5d4458a68d43bfb03d41c5441d4143df5d3fbee2bd3ef7041d3ea68e8d3c2e4c7d3533938d3188eb4
  | 7, 118 => 0xd6f20bd1d6f1bc3dd6def3eed69dbfe4d685c446d6465548d628070ad61c5e10d6176de4d6087dacd5ee460ad59b812fd56859d0d553e4fcd54e391dd54ce291
  | 7, 119 => 0xd81bd2ecd8129154d80da136d7f747f5d7f1c750d7e31052d7d6d2e0d7c575acd7a9ba8fd79dc0b9d78ab0c7d763910ed7632d93d756acfad725bca3d6f7cf8d
  | 7, 120 => 0xd96f7c1bd96ea0e7d9637578d937c94fd92a8d86d91f1ddcd8d27ca9d8cce887d8b78529d8b4572cd8b06cc1d879858bd85f3f4fd8598138d84f6169d84c15af
  | 7, 121 => 0xdac8df18dac7ecbadac7e7f2dab15616daaf16b9da9b8617da15d665da13979cda113d63d9c89122d9b121afd9ad5e2ed9a608d1d991b1bbd990ed77d98a024e
  | 7, 122 => 0xdc70cd5cdc62a353dc60b55adc4b81f7dc3fae50dc391ef2dc362745dc1c1908dc193b63dbc7afc7dba115e6db516d48db4b3104db427d77db0b8fb5dae2e364
  | 7, 123 => 0xddc42c63ddbd6cd2dda75d18dd72d6eddd5ce37fdd5563ebdd43ba9ddd42856edd205090dd084659dcf346ffdcca31c3dcb5e3abdca295b6dc9ed332dc87e621
  | 7, 124 => 0xdf1d8324deef5ea8ded965afded3883bdec96738deb8e8a8deb8784bde9ffb58de804333de6eea17de5c6abbde567756de4e9982de44371fde139fd7de12ce72
  | 7, 125 => 0xe0fe8bb0e0de64c9e0acf2c4e09ae926e0694a2de0519427e0456241e0319cdae0148ec2dfbe3995dfbbd4c7dfaf97dfdfa34efbdf7bebcedf703314df63f36d
  | 7, 126 => 0xe226c512e2235c35e2127b7de211c2f5e20c74e0e2077627e2012f03e1db042be1bb76c4e1a8113ae16ff6fce16bdd1ee15c3f6be154a308e1418e79e12d4e4a
  | 7, 127 => 0xe48e5545e45aec4ce43a2a4ee4131c36e3d0bdfae3abe7cce35c6e73e329fdfce2cc0cb0e29dc3f2e298b5d9e28fcbc8e281550ee276d5c5e264903fe24800a8
  | 7, 128 => 0xe6be861ce6aa2294e6a05adfe645e43ae641b686e627f15ae5efc9f0e5b8cf4de5a2dd4fe58b723ae57a4079e5657e53e557fe06e557c78ce4bd65a0e4aca89e
  | 7, 129 => 0xe7ec562fe7c79c26e783df7ee76ed170e75e4743e75415cce7492fa2e73f0bbae72db741e71f37cae714bf9be704c8e1e6ff0d42e6fe7d74e6fa9896e6c124e3
  | 7, 130 => 0xea1284f2ea0af849e9eb78d6e9c2e269e97b34c1e94a19a6e93528ede9224815e8f9f25ae8f0512ae8915fbae85e1d3be85dad8fe8550bb1e7fd6721e7f6ad3b
  | 7, 131 => 0xebdec0d7eb8de31aeb70e86deb6c29f9eb64773aeb54463deb397a17eaff3e28eafca0b4ead849c7eace95a5eab9ab34ea7c6050ea4dcf25ea3dd17cea3756cf
  | 7, 132 => 0xedb1cedbed97dfb5ed93a381ed7c635eed775d53ed54b59fed449a97ed0d7577ed08dbebecf735c5ecd298d2ecbc19f9ec9292d6ec4e0ca5ec46f4d9ec02884f
  | 7, 133 => 0xeffdc6a8eff38adaefde80bcefd0df01efcf7359ef696b32ef5af53fef0d5d67eee0f33eeec60ab3eec2ea1ceeb36e63ee2d4a22ee0cacc2edfaf9c0edbc6aec
  | 7, 134 => 0xf19b4aebf18b76e1f11849eff1119da8f10b7435f0d1cd2ff0cbea14f0c10f0cf0c00d07f0abaa88f0a21c8ff08761b5f0638dbbf0490dc3f02fbafcf02f87fc
  | 7, 135 => 0xf2eddb14f2dcc613f2c80d73f2ace590f28a3929f283c601f282837af24978a8f22b0486f21994cdf1fbe29cf1dd2ef0f1cfbb3ef1b97ed7f1b89287f1a11304
  | 7, 136 => 0xf431436ef42e8521f41e6a25f416974bf3ff7bdcf3f56499f3cd90fef3c23688f3ae546cf3954033f37c498cf36a783af364ba23f3328e71f32c5fb9f3158432
  | 7, 137 => 0xf6791d6af6630afcf655773bf6368cd6f6283a18f60a6415f5e4fce4f5c36dcdf56eef35f55a1ca5f53bd635f52b0746f515a45ef50fe74ef4bc8f56f4b5b64f
  | 7, 138 => 0xf7b17112f79d5573f78c62f6f735acfef729b842f719beb1f711c784f70c411ef7073f55f6fc95ccf6c8b081f6bf1668f6aebfd9f68c6261f67f23a1f67d15a5
  | 7, 139 => 0xfa01b2c9f9c102cdf9ab3443f975307cf958efdbf9196e39f8eab0a9f8dd8700f8c87f26f8c43764f8ae0d49f87120f9f85ced65f82c2329f8093c47f7d14aac
  | 7, 140 => 0xfb437a03fb3c68f5fb160d6ffb0a09b8fb071344fb04fb9ffadb3637fadb2651fad27a58fac93c31faa611e2fa98c808fa73bc10fa4b8f0afa1e7ad5fa0d2558
  | 7, 141 => 0xfcc6f621fcba9a01fcac1610fca74d45fc85fb79fc7f1c4cfc7d9e83fc49fdd0fbed4945fbbaa7bbfba2c1c1fb990824fb906461fb84ad17fb8223e9fb5c4916
  | 7, 142 => 0xfeb1fc0afea3043afe88730ffe7dfab9fe626264fe51854dfe4383f1fdf9459efdf76115fde210fdfdc70806fdb98554fd1a5976fcddaf80fcdd4784fccd195d
  | 7, 143 => 0xfffab5d6ff9906c3ff8abdc4ff747dcaff6be2b5ff547b88ff3a9338ff0d866cfefad343
  | 8, 0 => 0x25bb0aa0217c15e0213058901f17e1201d6d5750183149d017eeb2701657872014f54a5014b1ff40125ac5d0085e5e9006a198000592aa9004757150032b257
  | 8, 1 => 0x4f66f9e04a847e1049078c4048299d404663ffb04440b00041aa958037f330c03733af503486dc802e8a61b02b8d8f3029a877802725854026ceb6d02666f6c
  | 8, 2 => 0x772e59b06eb4bfa06dd3ea9066079d60652deae063c3efb0639409505f0020e05c1a73405a680ba057a2b0a0562c8c9055b92d0054baff50549442d051c62a8
  | 8, 3 => 0x9937c43097ecdf5091d64c108e524cc08bfa10408bbb8ec089c00c7089ad5d2088aa7ab088628be0881a9cc0878284f086a29600845670008410b9608078c1e
  | 8, 4 => 0xcc8d6ea0cb981860cb4736d0cab48ae0c80cffa0c47710e0b6cba4c0b5ddb6f0b5b69750b5591820afe8de40a546d400a539ca00a35f4800a0fd547099b15bb
  | 8, 5 => 0xf0a05220e23cbe70e10b0b90de14cfb0ddee8da0dd275ed0daf0c5b0da5b4440d9d2ef10d7523b10d62523d0d60a1df0d40a2e60d2861e10ce7c3e90cd292cd
  | 8, 6 => 0x1270663d121924b511f6cede11e236f311a501d4119cbdd11134d71c112bb65910a1cd72107f3dc90f976f240f8659510f8067e70f50eb740f3e17c00f0cdef5
  | 8, 7 => 0x15185e4814ca14e714b759f514981de414598f101434d7e7142d7db1141cc89d136c96ec133e05a91314d38a1313fc8b12e52d2e12d092ea12afcfed129e29c7
  | 8, 8 => 0x1802ea4b17e2b61317c45b7717a4273f17a3b496179820f2176e1c8216a83df716452fb21640c353163fa0b6161b2d3015f382c915ef1cfc15d1030015ca2121
  | 8, 9 => 0x1a95bfcd1a8407241a4b78901a09fd0419e9074d19deacf519b38a3d1996b3b119774e7f1934a8ac18e3811f18c63f3718a6e2da18357452182636a118041da4
  | 8, 10 => 0x1cb3c7641c723f531c3333021c2a14d71c1d225d1c11466c1c0f356e1bd53c6b1bc2a4ea1bb8d8061b9524001b2d5b3c1b231abc1b1bfa5f1b0070111ac295f8
  | 8, 11 => 0x1f26e6f01f252a661ee8f51e1ed18ad41ec9a0281ebd96d21e820a961e4d01371e0d9d631dd8499b1dcf0e8f1db644f71d9610bf1d7c6b2f1d59bf3b1cda39a5
  | 8, 12 => 0x217f267921791f1a215730d620fda4c320b1acc620ae074620adadca2075f0a420547d182050ea48203d56c12035ea11202860ed1fdf2b611fb84f451f6baf23
  | 8, 13 => 0x23ea77f323c6f1d723c0f80f239e5517236768cd230c4b8a22fe713a22f9449422c1783322bfe26622a89d4822997177225e834822348cf121fe519c21c2901a
  | 8, 14 => 0x269ad9e0266a7f36261fd2f8260906d925bee454256ca137254c5277253e45df2530b1b4251b0e3224e1873a24a8165d24a64ea6247369f22429e7b7241792cb
  | 8, 15 => 0x29d93f4629b10f8429a11ce22973d34029539f08292a126328eb838f28b1cbe628a548a52831ccb527ef187f27d542e8277ca0cc26d0a47a26c7d3a4269fdcb8
  | 8, 16 => 0x2b654a102b5aa4872b52c9e42b48fe612b2bcfe12b1ffbe32b1c15b32b0a6f8d2b04566b2adc92422a8570532a8069652a5f71122a5727252a0cbc7729dfabb6
  | 8, 17 => 0x2df066192de5abb72d801e632d7bc4d02d73fdd02d2bf3272d245da02cf971d22cf398ec2ced6fde2c8ce3542c63d1962c58f30f2c337eed2bf615592bb92441
  | 8, 18 => 0x30d1eec830c09b0b30aef3d53030be772fcbd3d62f9e4b542f9306622f7e86582eff7dd72edd6d0f2ecaef972e9b8f8c2e8c18c92e81fd8a2e29ff382e1a42b2
  | 8, 19 => 0x3482876a346f5a2f33adbcd033a8a8623374b4d0336c76433356a9ec32f58467326a3a5c3261248f32039991318ea32a3171fbe0310dff3330fc590d30d71b4c
  | 8, 20 => 0x37b2b04a3777ae7b372e5084372dc6343710582d36dd8a2c368a75163619c539361340bd359345f535672af0354dcce0351b4e1234f96f9134d93b5934ca93ba
  | 8, 21 => 0x3958dbe039274a6b391a4d0c39183263390e04a13905bab438de8a5a38de89f438c60b77388a42b7385de8a8385ce9a0385a896c3859a5ba37b91b3e37b32799
  | 8, 22 => 0x3c94a2563c8ab24a3c56bdb93c4929b13c323a093c0a9add3b9e85ff3b5094ab3b2fe2663b2baa7a3b0422a93a9afb583a59d70f3a0205b439e5178339d6f5a4
  | 8, 23 => 0x3dbf2c753dbb62973db3d6333d9c6df83d8c5bd43d876b133d66fe4e3d50ee943d4dcd003d4a6f953d3091193cf5cb9c3ccb8d7c3cb9e7563cb415b53c954c8d
  | 8, 24 => 0x3ff4f6803fb8ae723f9e25133f5851053f565e713f44fbf83f3eec643f0c368c3ee61eb23e6618f43e498cd43e0fede83e05c7bf3dfd867f3de6c0e03dc1a017
  | 8, 25 => 0x42c12ad8427597d1426b706a4263267d4248a739422c38bb422ae68a41fc845d41eb2b4141bd10d44128ffc04105d0e740e7fb1540b53bfc405dea8f40208f6f
  | 8, 26 => 0x4565b328453f0927450f0fcf44e4783144b7f43444a9d611446fa8e84447d100439e84a14381efe74376bcae43733aa1433fb680432f2ef6432a89e542ead028
  | 8, 27 => 0x4737355d4736ed6346f85e8f46e26b1146d630fc46cac5db46b074d8468dfce246874dba466ab65f4649ec5b4632d5c9462097a94618d7d24586cf62456c14d9
  | 8, 28 => 0x49281f2d48fc171548f3ab2248dc1fca48ba8f5848b0994348a2a772485129cd483f83a7483dcb9c47f1238e47d91710479bbe644775c43147723d2d475a055b
  | 8, 29 => 0x4c6dc0044bba24264b975e734b3bf7624b2a00254b0e08b64ac9c4d54ab1c6fc4a98c2bd4a6d9af14a4cd6e349f3586d49da3e0949d8167a49c15047497dfb38
  | 8, 30 => 0x4fd5cca54f9ce6704f97d0ec4f2d04634efd44c94e0635824df8a17a4ded7ff34dba12a64da54b244d9857544d8e01474d291edd4cea480f4ce7415a4c6fb093
  | 8, 31 => 0x52feaf7652f29f10529ead765212720e520e050c51ef3eab51ed431f51cc532e519d095650f8a48850c2f8045081a8da507263db506aa088500b4fe55002114b
  | 8, 32 => 0x555db2cb55496468553efd125538746e551ba2c654d498c254d156e954adbb7e5494db98548dded254531268541aa86853d56cef53abfc26536278b95337a9d2
  | 8, 33 => 0x584fc6535807505757506402574aebbc573d72f45729a1a1570cfa6156b5d29a564f612656488221562b293a55e0485255cb2bcd55bd8d2b5598141355902795
  | 8, 34 => 0x5b0e58a55ae1dd975a82e11a5a6389f05a23410e5a1071e9598bd1d3595b6cb25954c5bf593faef75904fea159003f2858e6ad2658a7d65858a1016f58670908
  | 8, 35 => 0x5e27e85b5de4051b5dc8b1c25d7814315d2b0d1b5d0fc22c5ced3e955ce205df5c5f1b5c5c49593b5c22aff15c0ba0655c0aca675baaefdb5b95d4e95b206c6b
  | 8, 36 => 0x614d7c0c614cbd82612dce5e610eed386101e13e60d3c717607ac03f605407a7601a944f5fc32d1f5f9ed82e5f698a6f5e94e4d85e8d28d25e84a01b5e7457aa
  | 8, 37 => 0x648d51bf646c4977645a952664509de3642d72a963f1d6e963a8455263a8169a6351083c63436f2763335f1f630df24b62a149d56230c49961fcb3e76164bc20
  | 8, 38 => 0x68178e25680a0041680416b2679540b56757d0d96700d6b866e88d4b66ba4d5d6684483465b12cb865149582650b2a8f6503753d64f340b264cc157c64c576d0
  | 8, 39 => 0x6afbb91f6aef26c06aa81f5b6a9fdc0d6a8ef5036a5d575c6a47ddf06a094f1c69b9e2a2693f6be768e47dd468c2e5ea689fdb30689f942868654a636842a586
  | 8, 40 => 0x6ed44c626e9bd8896e938e9c6e8fc2776e820ed96dfad3fe6df600326dba42306d8a9dfd6ca0daf06c9155606c7c3bd16c0d530e6bd016ca6bafe2926b1688d0
  | 8, 41 => 0x712a78a870f2ac7e70df582870c510737099ceb2707a25a57034369170134faf7005cdcd6ffb389c6fdc61ed6fbca9c86fb7cefb6fa252cd6f7940276f5e4b53
  | 8, 42 => 0x7429e00e73da2a8773d51c6e73cbf1af735aff3e72be650171ff9a5971f434b371dac9e271cefb2271c10b8571a6e9c4717516417173fbe571676c0a713d8a01
  | 8, 43 => 0x77b34f0777b2f50577717979772d315c76cb9db976caf6d5763cfe717623a47e75ae934875ae63577598ae73756b29a7754698ca752f6ba57501f5fc749ea054
  | 8, 44 => 0x7b60546b7b1e58ae7b163cb37ad74e777a7097d47a5458227a4b2b817a3cc3f179b38e7b793fde817939cdb67924d6b1790985de785ef6557816f1b177d38b3c
  | 8, 45 => 0x7dacd8357d3826597d2ea8eb7d2dd7457d1e5ae27d0350b27cf997857cf73ee27cbac7bb7c52eb347c3ace287c1f6b037c145c607bb8c6e57b927aa17b7a3811
  | 8, 46 => 0x7f7c55e27f6811f17f5b758b7f5431fd7f2a5eff7f27d1067f162ae07ecebbdd7ec9f5747e947db67e938b3e7e72049d7e4401527e3e6d2b7e19c7b57e018f27
  | 8, 47 => 0x820645e081fb93ec81e3ae5a818f526e816c21918150c39a814ed2178128b7f080eefae180cee54280a2c842805551ad8015bb587ff073f37fe6e8387fdc3e28
  | 8, 48 => 0x84938457848f557c8463c7328454ca648429d65084162b2584087a8783c1807783a70857837b53db8370834e82f5e56c82eb810582e19fab82c57bc782a9a382
  | 8, 49 => 0x8746ad238742ad1a873e633687081e4f86ffd46286f6fb0986db4fb586bb1b7d86446b57860fad2285bc6d27855694f485392acc8519525484b2c25b849d1430
  | 8, 50 => 0x8a936f9c8a8f7fdc8a00340b89e9bb3b89a87c50899afb62897b3fc2895b819a88de67c58899c81b88901539884146ed87fe5bb787f924d087d36a4087a4afb7
  | 8, 51 => 0x8d95243f8d749ff78d29afda8d26085f8cfa07cf8cf1bde28ce602cd8cae54418c5cf5c28c4f92248c4e9f098ba5bf688b8254c58b7dd1748b69399b8b2aaac7
  | 8, 52 => 0x901656308fc8a1048faf72a18f7413198f7370198ef61f9f8ea90f4e8ea3e8708e6151088e5937f18e2ae9718e1aa91d8de87ca58dc3d4298dbb82e18da97964
  | 8, 53 => 0x93003b6392e4db8292cd875292c4beb49285f31192653e38922de07a9213dbb59201979d91d6d6a4915988539130d6099123a8d1911c94479062790c9041c5ee
  | 8, 54 => 0x95baac6f954e7870952880109497b8ba9477f7fe946e32a794367f89940c929d94038b9f93dfd96393b9926f937b4066936a50ba936155ea932bdf659316be5a
  | 8, 55 => 0x97f297c997d457b797ae27e9979210319788553a96e941c596d4ca5b96af1ad696ac407896aab2f19696242d96460669962d87ec961f8f579602fbc595fd3dae
  | 8, 56 => 0x9a2c65039a2163cb998549839977d55e996707ad9949707a98ff1fe998d1430f98bad31a98b8112098b7961898af4c2b986e8e699856f83e9812e68b980277cd
  | 8, 57 => 0x9c222a7d9c1a18929bf9e45a9bf9ac679beab8b19be799a19b42f0b09b3b57389b22df0c9b0419e29aa668869a955dd19a8d1f449a67d9b29a3309f19a2eab9f
  | 8, 58 => 0x9e8025619e5d0c299e58aca69deb6ec39dcce7b49dc641379d97d4299d527bff9d23149d9cee32f69cda3fd59cda22909cbec1b39c9c9c719c43b7ce9c262875
  | 8, 59 => 0xa0bccbaba0a1e9eba09bfca8a059c332a0546b5aa03f620da038db64a032ebd39fca20e69f90e9c09f56e7509f3fd0d09f294ff69ee87ddb9ed9c43f9e85d7b4
  | 8, 60 => 0xa3706f46a36bc29da2b21f2ea2b1e37da283ae18a27ab3e4a25350eaa23a0020a224cbaaa214c216a205e1d6a1d98321a1c5cdf9a17c1ae1a1329be4a126607d
  | 8, 61 => 0xa5a12397a5792a11a56a35d5a5560c68a550c258a5279bf4a50769e1a494534ba43d3269a434e87ca3f09d20a3b10f66a39ea9d3a39647f1a389d0cca378d37b
  | 8, 62 => 0xa7e7bb88a7e4337ba79b5dbea78b40e5a7159f81a6f8e6fca6bad89aa6afe7c8a66d2c10a65ca364a64d0e47a63ff8d9a616f65ea6016a05a5f465d6a5c60f59
  | 8, 63 => 0xaa4b6c7caa40569aa9ce7d6ba9a02405a98fee97a983cf80a94b8f8ba94ad524a8f84885a8746530a85fbee1a85a2abaa832889da831414aa82679e8a806ab96
  | 8, 64 => 0xad1f456eacff4d61acfc2964acfc1f97acf02a2dacd61e46ac64c13eac17517bac0f8af7ac05a930abf35385ab6db1f7ab4fbd37ab218f1baad986aaaa8458ce
  | 8, 65 => 0xaf81d817af71d2ceaf602ca8af4356a1af2f045faf2c0ec8aeed98eaae881472ae5ae495ae057adfadf6d9fdadc67722ad97116aad6a955cad4140aaad3ae275
  | 8, 66 => 0xb22eb1b7b212d2e0b2034379b1c1ad4eb17c17a9b1714d74b16c170fb13d88d5b0830b90b03e37cab035b277b01685bab0145423afcec0fcafc63db1af8794f1
  | 8, 67 => 0xb51aa88bb5096bd1b4ee8c68b4dc8cbeb4affd94b4615b46b45c1565b4546ed3b450baf6b3fe8f49b3dfc70bb3c439dfb2e405f2b2bf3c6ab27b0da7b24d3d62
  | 8, 68 => 0xb78b4989b762e6a8b72f7255b6f47d33b6b73ccdb64e299bb649f14db642a8c3b6309c2ab60f52cdb60419efb5ed4fb3b5cde937b5acf8bdb58f5a63b55db24e
  | 8, 69 => 0xba39c43fba2ecfd6ba2924d4ba07dc2db9c6bc17b9b99073b996f374b98974e6b941e8d4b93a339eb91cadbbb86a5063b861f7c8b7df2afcb7b0e1ceb79cedcc
  | 8, 70 => 0xbc565869bc0fd205bbf6036fbbf541c3bbeba284bbce647fbbaaa92bbb8143e3bb3f6660bb1bae35bb1a8dafbafb79fdbadda896babfab7dbaa1e714ba8cc153
  | 8, 71 => 0xbe150a6fbe0d695dbddb59e2bdd67b9bbd984a2ebd7f3b97bd700a27bd613e28bd60ff36bd53d031bd378647bcf6e9c5bcd106e4bc7e5bccbc5b5c5abc57408f
  | 8, 72 => 0xbfe955b2bfd7721dbfc3f505bfaffb74bfa75d16bf49d630bf444209bf2494a0bf1800aabed971d6beabcb6abeaa32c7be4bf831be2e3192be2ba971be168ffb
  | 8, 73 => 0xc36d11b5c364c74dc3463150c3367e1fc2ed009ec2dcf096c250d2cbc1a38a1bc18739fbc1849f9fc126614dc0ac7ad4c0a945fac06f655cc06057f8c053a4d8
  | 8, 74 => 0xc5b44415c5aa21fbc583e1e6c56b9327c55228f6c5164ecec4cb5b56c48f9d54c408ff84c3ff52ddc3f69b1fc3e84c9bc3c8651bc3b8bd59c384fb7ac36dc354
  | 8, 75 => 0xc88ea1a4c87651dac8762d27c852929cc8458703c80992e4c7ef2509c7b391b8c7741febc7500ee9c73ed22cc6c502b1c65f755dc6173524c5fca122c5ccc6d8
  | 8, 76 => 0xcb499156cb21bea5cb1d5a71caa99e93c9f8d1d5c9f85d54c9dc3b3ac9dc2306c9ca41c4c9aa0d8cc91076bdc8ef29d2c8edb7a3c8a1cb44c89c0d2dc88fe97a
  | 8, 77 => 0xce06b858cd8af5afcd4fe056cd474037ccf86fa0cca3414fcc89ed71cc446396cc42d64dcc2db194cc241e3ecbfdaa48cb8cf278cb7db99dcb5d7ca7cb4e1baa
  | 8, 78 => 0xcfd4f4dccfd15adfcfbce126cfba38ebcf9c5510cf85f364cf80461ecf71c9f7cf5cea7ccef4b4bfcedb70c4ce9ce1f0ce736871ce729cefce61c24bce555a67
  | 8, 79 => 0xd21c8c3fd20fcfc1d1e511aed1c44f57d1b4ba3dd1a2f2ccd198d619d139e066d1307b19d10552d8d088e99fd0448ad1d025e176d02017b3d01e5985cfeaf2f5
  | 8, 80 => 0xd51e97a3d51d3b1dd4f78946d4e59957d4c5c8b3d48ecb70d3f3b606d3a9ca23d35dcfded3392e09d327ad8dd3188eb4d3077955d2e04fe7d2c46e7dd2b79313
  | 8, 81 => 0xd7fe1314d7c575acd71b0af0d709eec9d6def3eed69dbfe4d6465548d616614cd60c12c2d5f8cf8bd5e7593ad5cd83eed5c9f312d56adc98d55c7eedd53f1597
  | 8, 82 => 0xdba7032fdb427d77db13d9a2db0b8fb5daf169dcdae8b94cdab8bfc9da0da625d937c94fd93260a5d920435ad8fd2cbdd8e71a09d88d2db1d84b21a9d83ff316
  | 8, 83 => 0xdd98c458dd5bcbf4dd454fd6dd21fc00dd1055dadcd64232dc79a22cdc719fcadc6391f3dc3171e9dc25031fdc14fedcdc0e85f0dbcfa06edbca2722dbbf6d6e
  | 8, 84 => 0xdf61ed9bdf4d2619df472044df379ab2df36661adf142ffaded39e06dec88010dea09123de903465de881f8ade86b9e7de37b8b4de23347cddd9a682ddd62f76
  | 8, 85 => 0xe15b6f98e0fd6736e0bed862e0a51fbee0960a05e07c3e86e0608782e0519427e04c59b9e0292b3edfd9e0a6dfbf4ccfdfba127ddfae1077df8e97c2df6b669f
  | 8, 86 => 0xe39e2cfae3934ec7e360b1dde3401404e324e552e2eb33f6e2ccc51ee2c651f6e2a0a741e293fdd8e2266470e216ec9fe2077627e1bb76c4e199fe6ce17d40b0
  | 8, 87 => 0xe6625249e644db22e5c8e7b2e57e6a72e56e5337e564aa53e554546ae5364b3ee5046ef8e50285b1e4dfe074e4db690ce4921a86e44ed5a5e3ba4d03e3a74d2a
  | 8, 88 => 0xe8e16845e8650d85e8267eb1e7f6ad3be7f58ec5e7db114ae7c5d915e7bf17b0e77cfbb7e7504845e74d5918e6b0c1e2e6a9a5e9e67f67c9e66ee45fe66dc1a3
  | 8, 89 => 0xeb8b2481eb4c95adeb397a17eb2b509eeb203359eace95a5eab66e44ea912c4fea8e881bea7c6050ea4fb14dea3dd17ce9d59687e9c8c065e966d557e9528599
  | 8, 90 => 0xee5ca406ee186831ee10812aedfaf9c0ede98dcdedd47ae8edafc923ed651458ecbc19f9ec759017ec59d3cdec108bc3ebe54db6ebe0130aebd7c535ebd1f60a
  | 8, 91 => 0xf0eac7b0f0ac38dcf067b7d8f057caa9f02fbafcefff10c6eff354f4efcd49b9efb4c363efa0b6f7ef76348fef67287aef5bda3fef53b34dee739505ee5f0c37
  | 8, 92 => 0xf41266e3f3cefd42f32c5fb9f30ae761f3029808f2f8d013f2dcc613f2c6a6a6f2bd41a3f2a13b88f26e502bf25a6ca0f20ecfaff13f474ff13e7f2df1116564
  | 8, 93 => 0xf709b3d9f7073f55f70274a4f6d01ba2f69e225cf67f1181f6207d69f61f128df616c8a0f60a6415f5d91c92f5bdb117f5681e0ff4d454e8f47d9f22f43c46d0
  | 8, 94 => 0xfa0e2a23fa0d2558fa0ab053f9d5f67af978a80bf95a1739f93d1baaf9355f75f8fe44dcf8b11f16f898c83ff7d94cb0f7c01698f7ba0fcff76decf3f729b842
  | 8, 95 => 0xfdf3ec7cfdd35aebfdcfc3d7fda95e5efd9ba9eafd319d5bfcfc0d76fcb589e0fc3e2361fbff948dfbed4945fbcfb9ecfb912b18fa8af9bbfa842b64fa419f05
  | 8, 96 => 0xfffaa94cffcff52cffbff8f3ff8b0246ff6be2b5ff621d25ff5815acff3965beff37e174fee4657cfeced0eafec7b9ebfe9083b2fe8bb786fe393055fe15ea13
  | 9, 0 => 0x346f5a2f318ea32a2f7e86582c337eed2973d34029539f08260906d91a4b789015f382c914981de414598f1011f6cede0daf0c5b0d40a2e6025bb0aa0125ac5d
  | 9, 1 => 0x79b38e7b72be65016dba42306c91556068654a635f698a6f58e6ad2658a7d6584efd44c94e0635824dba12a64ac9c4d53ccb8d7c3cb9e7563b5094ab3a9afb58
  | 9, 2 => 0xad97116aac17517ba983cf80a85a2aba9fca20e69cda229098b7961898af4c2b93003b638ea90f4e8dc3d4298d29afda8370834e816c21918128b7f07bb8c6e5
  | 9, 3 => 0xf30ae761f26e502bedd47ae8e77cfbb7e04c59b9d71b0af0d088e99fcfbce126cf85f364c7b391b8c73ed22cc65f755dc2ed009ebb3f6660b7b0e1ceb3c439df
  | 9, 4 => 0xfcfc0d76fbed4945f9d5f67a
  | 10, 0 => 0x260906d9
  | _, _ => 0

def stateMoves : Nat → Nat → Nat
  | 3, 0 => 0x9314
  | 4, 0 => 0x2192816cc0c0ae62a0143040039828078c0800662804220302b18080b0c0807660804b33500c901818481003462a05a315
  | 4, 1 => 0x188c9404266a003305
  | 5, 0 => 0x181830388c183e262627a31508298309a4c543fe40a16920402a50103f4c1042c60a18830508f5010058c581e060a156336
  | 5, 1 => 0x22982802881442a40815630301d18a838885010860a0113130f519b03f8c4c42660a0dd6020fe18a871ccd815a6041f8315
  | 5, 2 => 0xf98a8280c0c31262c06a20408f39285fc8182a062c2703040379010194c0c31064c1b73020f898a09d8c5822c40a17b304
  | 5, 3 => 0x11c98305d4c08270608072305134500847ac1038662c28b3040d218a0414c1438c64c1b62060f219b0684c9842c60c084235
  | 5, 4 => 0x6198300988941fc6282703060e39828938c0c3f86281863150ba9820414c0825240a08032500f989843cc182be608079204
  | 5, 5 => 0x9983001cc5822c66c14e31405390280c0c5030640a182225009992819885408a60c0d433606eb820344c941c460828f316
  | 5, 6 => 0x147101868480c23ce2a186314
  | 6, 0 => 0x39718b058cc0c59e40c35b3173cc98b1025c989fc62a6ec30532f18990ecc58a0c6086ca3253771822171c589a662c6b8314
  | 6, 1 => 0x214d809230c5859262872331424098b1d8cc58ef24065337050c998a9026c145526081bb3062949020a90c147006262a1304
  | 6, 2 => 0x12619b888dc9060a62658720403e98b18d44001d040a68130430c58215d0c110ae60c4a031617118289f4c14a8c62a869305
  | 6, 3 => 0x3cb1822234894f1060a7e2304214d821d7ec1019460875b31544f98b210cc5c61ae4c08e30518c18282e0c10b0462c85ca01
  | 6, 4 => 0x3d490a805cc18c1a60442431735a0821418c1d11a6067ac3152001828cb9c58350cac56730427f18b0dc0c0c652e2a6fa205
  | 6, 5 => 0x4139891518c580b060c6c92041b998a0db4c14bd262a63931716e9828340c18bc460c40e30335a0801148c50d1660438a206
  | 6, 6 => 0x2ba18320ccc1075860e2413030c818994cdc58ad466e6b4f3417698b004c890f3d40216e3034041821540c58fde60a548326
  | 6, 7 => 0x204d830b9cc5032662c67630623398a0f7cc10db860a8e932642898a0f50c510e460865c3061e31828a09808f0a408582317
  | 6, 8 => 0x35218a8fb8c191d26484063043ce11b1d7c41046e4086a53041659921264c5452040e79c2041f99828238c18b5c62c548304
  | 6, 9 => 0x2d688002e0c14f5242c8e330540c902a3b0c141ae60c6cc3152551810adcc9c3ee2008aa3042f498b203cc1cf8646c5d2316
  | 6, 10 => 0x24098a0eb8c5909e40a6473371bf1822354c544b460804d3163aff9a1198c100d462c0ca3051f71821b90c58256e260d3204
  | 6, 11 => 0x1d18a1b2cc1904c60a6e030502f98280b4c50eae62a3623050cc1891ca0c1810e60c72331500f1828070c1401e62800e303
  | 6, 12 => 0x46318a96a0c5d18c62c6a53072851031a90c58fbc62846b3252979821304c1029844a68931643330222288100d4628857304
  | 6, 13 => 0x37218b82b8c14d68e267de3150529821eccc10ff260e2f330327f1898548cd8d9862c32120510e8801394c0ca9060a696317
  | 6, 14 => 0xd09811c8cc58ae844c10a30432a1829fbcc0c1a260a329100407189a250400a5060a51f3050601820fb084cd9e60c451205
  | 6, 15 => 0x4768801d7ec08e8a40881b1001361829930c1c11c60810730539418383f0c510146060f83152a698a1084c144be60c535a01
  | 6, 16 => 0x20a9011f78c58bb642c7b63373ad98b1640c1410440c31c3140c59839508c4c812cac09c3042be1821ad04142cc62c3ae713
  | 6, 17 => 0x3d998314ccc14f5862c5c930425598107d8c0811c6062742241f61029f01c14b6860c8513150f818b16a8c1033062c64f315
  | 6, 18 => 0xe698a06b2c14fde60c8b130629499307c0c50f3ce4c7fc3041b298206acc9113660c1a23141d18800294c08f8064c20a316
  | 6, 19 => 0xa41029a1c8187d062a31c316111992159cc1d01460c6b4625214880007cc5c8aa4084b13063089820b04850c1a60c75b314
  | 6, 20 => 0x798a9026c08a346084c93031ad98b1998c1445460a1313042a118a87b4c1099c6084c930532b1819934c10c9460675f105
  | 6, 21 => 0x3c050122c0cdca8462885cb0432110980b4c5485ae2a69220240898205488590a262c4c631421a88019d0c10dd2604409b03
  | 6, 22 => 0x37498222e8c58d4a6061ac7262da18114a8c18350e4c6ca32403698a9700c107ec60c00d30402118b2054c10f8260a89b303
  | 6, 23 => 0x22eb8b066840059262a37f2020c01019af0c4cd9460470130505a9022354c58ebec2a25f3041549829678c1054860c6ec304
  | 6, 24 => 0x7e18a80b4c5822840864a30222d88022d8c10cbc66c3ae6030dd0801d7ec0c5c460c00f31630c5810548cd466c406429b05
  | 6, 25 => 0x3c418201cc81066a60a06d3163441821424c1481ce063183031a198b1f04c1023262c11f30408b18b0c14c5101c628236216
  | 6, 26 => 0x1b69831628c0c27260a8693041d99030d608546be6083803043151031eb0c50a8462c429b023cab8b1b88c18a54e2a370305
  | 6, 27 => 0x1d61829318c582a466e0fc3161d018a2020c0c39a62a0f831618590294cdc98cbc60e2851000d118a951cc18252406373315
  | 6, 28 => 0x30418205f8cdc7be60c46b3261ea18a88908110666061163173e03020adc81078c60c4b5214204d8220a4c50a5e60a119317
  | 6, 29 => 0x4619021424c1880c60a35821402c1839495c4cbe62003f33041bc9822144c4d1dc40a3ea30309f18b1e0040027860c232303
  | 6, 30 => 0x47a903852840115460c1a231629798315a8c1862c2004803162261829a6081807060a24c30630a880212cc186f260a688302
  | 6, 31 => 0xd639b0038c0858e606429b032d418b1f78c4cee660824c3130e698b0f78c106b042c01320642598201a8c54358e2c2e7315
  | 6, 32 => 0x2609829af0c5846460c31c3150f81899d7c40005060a4ab3052551828078c1003860e65b3040071828b24c58da66082c4315
  | 6, 33 => 0x3679820de4c189ca6080d730414138293fcc149a662a244316109b921e79958812e2c6e110007210281a0c4c074626286306
  | 6, 34 => 0x1bf1828b208083da60a0e5216449192858cc14c9860c67710027f18a11488147a220081b71423398a919cc5862062a8e9325
  | 6, 35 => 0x2a318a0bf8cdc58862c6cf3052f519b0300c0c4dac082f210042d98298508511c264e72e315293182200cc1415c60851f303
  | 6, 36 => 0x2be18286e08147ec60e0fc3131811822098c10b8060a6b320335b1831da840001a60e54d3151639830650c146e662c0d1304
  | 6, 37 => 0x1bf1831318c54fc460a5b43052949921d7ec14b5460a3213370f818a9fb4c10d68e283103162c81830fa8c0874c60c582315
  | 6, 38 => 0x3e98a8684c146e662e8561002fb9829200c54db848a3ae31328498206b881c01260825f307283181035cc1509660a64f316
  | 6, 39 => 0x32518281f4c50eae62c7c13061f71829d7ec0445e408688305434181807c818db860c681302136182119cc4cc1a60a047213
  | 6, 40 => 0x69121f0cc1827260e6743061e39021a54c1091862a6673053331831994c9090262a1863053fc98307d8c14cac60864d305
  | 6, 41 => 0x105e60817e3033561820e48400d6e64868b30525018a88a8c107b464c7ce306
  | 7, 0 => 0x2cb58181d9918592c262501062be38a0fec85813ac0c5b330606f98212acc141c460809320116698b89204180dc208545716
  | 7, 1 => 0xcf98901ed8d89ae60807966716c18388a4c107b420a2e02040a0302923ec1caae60e59a705210381904881456064e45c206
  | 7, 2 => 0x30018b0f10c4cb5962605b1001970801720c1c6cc60c07f6461388800f8841407640c4473041d698212bdc486e46463df105
  | 7, 3 => 0x20f91317d44083d84082671062bb1938e7080c02c60851f607004b890bf0c1cc0a4242922041d698292b8c1823c406463716
  | 7, 4 => 0x3e38189c441895b60a0ba305124982827441000a60c2d23072c238b1467c1495462c52c7270d01890aa6c1472a604565225
  | 7, 5 => 0x10c30b084cc1877c60a27c7030b8193117cc14b1062e581a03202882858cc1088e60a1551000e1182923cc108ba60c20e304
  | 7, 6 => 0x18f18386b8c148002000a871218a98b82a2c0c8c060c40c7070089029180c1c63a6062df3070c019304b0c186c8608360316
  | 7, 7 => 0x2d01839411c18013606374304088b8a177840084420a420105138b8b0211c8c13a20003c1002213938445c58a5a200412207
  | 7, 8 => 0x73991975984836ae0618c10028e18286d68147066084a671621030a09bd80c22362c12d3050dd9818b25c9c84e20a57b307
  | 7, 9 => 0x21050115fcc5c415c0648f6160878801088400ae460c4db3060e19829548c1c9202001e930505798316a4c5c9ac40a19b306
  | 7, 10 => 0x1ae98181148543fa2000a81000079898a9441877c60c2b121227319181584001b0c8c4d730314f8831380c98b6a60a3c4203
  | 7, 11 => 0x881029718c5c1d82085c57161151820130c1863a60e06020512c903154cc102f1e0a39c3160fb982119c81894460a371100
  | 7, 12 => 0x29a9838ed2c049b4e0c3db30608298903d281060860833c10001b8800c8cc1c3a4e0e4511051c918210eec1029860a0ec626
  | 7, 13 => 0x2091018624c1482260c35f3072e99828135818406e4e48e205088b0a96288144a664c20b31403b79311708100c042a20ae14
  | 7, 14 => 0x1de90383d0400a4a60c46b1052d89838b7cc146184084207162117a28530c188c620a420f3528698b0f00c1c67f4062be106
  | 7, 15 => 0x17f18295c8c10a7260a5ac10018890309a0c101d8e46015b0420e9818eb8c1494a20036a317004b820f24c182da60a533203
  | 7, 16 => 0x2621021658400ac860e4e530521498309c58189c860a38130408cb1b01e8c5834c60e48110523f0828dbcce085c60a1ea306
  | 7, 17 => 0x235b030ee0c186104082363041c018b8b9c81463b60a48c105236080110ac1446060a1adf0526a18314dcc1834860e4d4307
  | 7, 18 => 0x9a0820d80c5c7386262dd20525f38b125841487260c3dfa0217208312d0818068200553306275982097481c3e84085af307
  | 7, 19 => 0x1b298b8c8cc942ec40a1856141df9821270414b08c4c39310010098b14650005e020c4ca20415a982961880c7d840a22b303
  | 7, 20 => 0x20a98280a5c5036b40806f3131329019000c543e840a20af142851829390c1865240a4a61051bc3030bdc418abc60816f305
  | 7, 21 => 0x2b1028c14418c08e0842e30609a9039418c0c77c60e12f1001d8183893cc1000a6084ad10513388013b8c94a33c0617a307
  | 7, 22 => 0x13099218248104706081e530719388003b000070c62e1dc30605818381dac1041c60c348205293d028026c14b5e60a519500
  | 7, 23 => 0x2d518393b881cbc460e4983020a010205fcc105de6085b53060b79831394c108106082293061c19831390c1085e6084b3b03
  | 7, 24 => 0x4d9898dc5c5877e60c49c6161ac1018d8881473862e58e3072103920571818b8864a228304131b8b02a2c14aee60c0c8716
  | 7, 25 => 0x13c18294d4c1814c6261ea3040f01031658c10802608076b010bb1030361c541aa60c3a6205004d8209c0c14c064061f2b02
  | 7, 26 => 0x21050094b1c10aae60822a30623018213b4414990e0e442306164b8a1428c1030a2081b5a0630588001f2c0c2f0c8c59f305
  | 7, 27 => 0x24c1890130c1491ee0c21020522f30996b0c501482004adf4501418384e940067e20c1922073040801788c14bb64041c4716
  | 7, 28 => 0x3730a03c540022220022a3070009030d284187042004db30314138b8d0c40079260e5a33161da38180ea808b6060c51e716
  | 7, 29 => 0x1499830f54ce0b7e60a07e7140089020ed040c7eee0c19630729f1021040c188ac60819910406c0801120c084386085b7304
  | 7, 30 => 0x20898414d4c0c1e2c0c1293031d19028c10c18a9460a4153041391820a04c1050440629630526d3829590c101d82043ae307
  | 7, 31 => 0xa8801818c1c35860603e3171f598208d0c5ca3420a3a820415498206b5918b7860c5573051c918297a8c1ca096040a8b02
  | 7, 32 => 0x30018a9818c104b460e2d830323f98312b6c0419860816930507f9839108c103b8608561205174182157c81066a61042e307
  | 7, 33 => 0x1ef881873441080062c06e7160db08003e8c089c860637810620d18209a0c189ae60a2423070ed3818dc44186e020c2fe306
  | 7, 34 => 0x1ed7829680c1420060452e10511e98b074989caae6061b5a02134982936980c0de44c248f05054389915484836b4022f0100
  | 7, 35 => 0x20a98413dc81049260e3ad3072ddb8b1620c5450620058520601518913b8cd8bd46063d22151a89820d3c84c778608005305
  | 7, 36 => 0x16918216a8c1447060c0846031f410215d8c8cbee6060663060441129360c14b1e40832332621039317d0c141494043ad306
  | 7, 37 => 0x1ed7010298c144b86082de30626a182023481437240a0cc3062fad890885c0c3a4e482d63052b79028e38c1022040804c303
  | 7, 38 => 0x28b1038a84c10415e0a4802050e71039718c50ae660a1c62031da08301f4ce08b462e5631052179838128c1c55360c020317
  | 7, 39 => 0xc38801235c18012c28451a0324298317dcc088fe60834530126d98214b98182f220042010303690296e0c0c4c7404178f26
  | 7, 40 => 0xe1831108c1c48060e0d53070989819680c1025860654e2041bb880146785402a60a5723031758801089c5047060a511304
  | 7, 41 => 0x2e61020f884180f82002617251a60800f7c41840a40640a3152e318a8f684182fa60e408305186982077cc0445460a13c727
  | 7, 42 => 0x2ce8829300c8c23e40a58b306235a800190c1444ec6c23d3141ce9819650414ac6e0622162703318202a8c5c31242a0f7100
  | 7, 43 => 0x4d830de140075c60c5df3051c238102e8c209546284153060cb3931010c0c9d660e27230618f98213b680863a6085ea305
  | 7, 44 => 0x1cc9890690c1080a20c40c703004d890ab0c20553606309b04138b0a11ac40034c60c43db0423f9838530c1c840200249304
  | 7, 45 => 0x1c198289c8c14568c0a03e3012dd88291ac40cb6e60445c20728238285f0c8c56660e4de30519898209284009ac40c5e8206
  | 7, 46 => 0x1a318189418d856664c42010612f18909404108d6e0620d205256d8102fcc5cb5660a11c10021050a0921918ae460a392306
  | 7, 47 => 0x3019028040c10bbe60e4db3052063938a4dc1c1d66084271062d99829360c108a060a52530707e10207c8c0c84420c3dc203
  | 7, 48 => 0x6f98382c4c0c4066084be100247b93800cc48552e0a039726259182949c400b2d60441d3040ca382109d81895462e4d7307
  | 7, 49 => 0x33181804cc50bf640c3663240a490293b8ce017e62a26764607c98b01f0c1077860c4043041701028c76c180d260c483b04
  | 7, 50 => 0x1bd182023cc1411c60a4511062559820bdfc181506085ee105026b8b04cc854bac2002711040a038b16e4c089c0e0c5cda02
  | 7, 51 => 0x9902136cc1c1c460c2ef306288983837cc1470260a5773032fa8829467c0c4f8c2e4a030414f880073cc485c040c285100
  | 7, 52 => 0x861810191c0c72a60a0a9305235883118d81860c6084e032720038a918c41814060c13010003b5828498c983fc60e124326
  | 7, 53 => 0x10e10a12044188fc20c0b7305247d828284c1074060839c3141a898306888107bc4085b33072929820f2c81c1e420002b100
  | 7, 54 => 0x25518a9020c1854ac8c1da1002f6880123041811420035e20614f8820f40c1039ac0c4637260b69818af98584f8e284c4205
  | 7, 55 => 0x19618284458506da60c50d31724b08313b440c415c0a42770320518b0060414354e261d271218ed8186ccc0cb9061040c617
  | 7, 56 => 0x4eb8b00bc41431e6065bc3042a518201b9c0c3ee6064a610624f8800f24c1093820c23431620d1828364c1047060e420606
  | 7, 57 => 0x9698308f8c1c2c860c2a970422138312c041807220a24230625688316c0c1c1d460a5e630311598416b0c5434c608327705
  | 7, 58 => 0x303183174cc488a06062c966725f0830c75c142fe60e0ecb12247983865580c0fc40a5047071f218214b9c0c58660839c204
  | 7, 59 => 0x2750800838c1425860e4b07260801830134414ae460e267f262651019250c1463b60e2ef30510578103e8c0caee608502204
  | 7, 60 => 0x1619828bf8c0c9446064503060871830430c187fa60a54230503cb8b896485813660635d3072871820136c0484f602553307
  | 7, 61 => 0x1723230f6b89463c60852e103198b828769c541fa60c13731229f90285c0c9c7526082a9b020b698394588142226282e0203
  | 7, 62 => 0x139183844585864a60e5847062c99938bc18d85e0208076b02105702118c4004d260c02f60623018287d081c1f26022e4100
  | 7, 63 => 0x1d89018590c1073060c463a0611f18317ba80409ae0650d315276883071280c1aa60806e10517bb2316d4c103a040a4dab04
  | 7, 64 => 0x1b698215f080c33660e16d3062bb9838decc185924085b03040d99830c158d89c260a07b1052910801280c147b040c492206
  | 7, 65 => 0x69080158c40c61a60a3e4b0500b183178040034262e1f27042159829284810b02e6e14920620818384a4c182e064a378100
  | 7, 66 => 0x2a51830be5c50ba660852020320a98196f4c1c8c640c49330725598307f8c20bb460c48fb062941020e68c14674c0e2f0b13
  | 7, 67 => 0x2241820d6c40013a20a54a30720058a95c4c1088660a55f2052ac080146841887a60620370528d0800904c142f84065e5203
  | 7, 68 => 0xaf9928a70814ac42004b061620318b168cc5c6e02002a32132d9982104881080860e0e9312107183866cc1020e64851e106
  | 7, 69 => 0x2d81840198c1477664c4103042d618b0354c14a6c40a2092250a61820900c18b8ae0c3b63162741019605c5ca33e042a8306
  | 7, 70 => 0x1df182030841421ea0059d1030b8182859c80c2d860c2522062301890cfd8d867e2082683052970830c75c104186082ac307
  | 7, 71 => 0x29638b9334c58b34e0852f30113e3830d8c4009a860a16830608399287a8c1ca4a6062343141df98280d480c2f660a5bc307
  | 7, 72 => 0x2ac083084cc1c4c6200596b041211821060c1035a20057730520a08007188102c86064c870325598184b0c147c96064adb04
  | 7, 73 => 0x1a5b9a0804c5c1d820a50e30520098387c9c0c95662656310621ed828494c50aa660a59e2051bd982098dc4c00a606519f15
  | 7, 74 => 0x1121930150c18b626062f22041b8b1b0dc18d858860e5e37171c918194d4c1090a60e30c10007888287a8c141bd6085acb14
  | 7, 75 => 0x3218214a4c1c59c64e1252042099821680c0c184c2c11e2071ad18291ecc1456c6261dc3070f9080135881c4fe406378104
  | 7, 76 => 0x20218285148107c960c2f771517a9830040ce097f4081c230311f18206dac0c1626081be3052d898292b8c14708c2e3cc304
  | 7, 77 => 0x17290180508101be6065803042ce88014acc0437660c2683071149838128c14ac6c0c201315154d8201acc58b9840a552304
  | 7, 78 => 0x1052000734400b3a20c483b050d99820a74814800e2c49d2061c318085f4c1460c4285cd1002ca0830ef0c14ac860a026308
  | 7, 79 => 0x29630390f6c083d260c5c120324a18397d440c76820844230520058b0e11c5070060204c3040db5821214c103a4e460eb307
  | 7, 80 => 0x2a1820eedc946f84064533060be9830615c0ca33c265bb106295182103189445260a2f0b0309a08290b8c10b72406076b06
  | 7, 81 => 0x1ed3230a3c40015260c5f9204190983901581831c4083ee3052651038af08143ee60a0e53030481828cb4c187b84080f3204
  | 7, 82 => 0x20030a882cc540302063ce10022f9820320810ac8e243e26461641028f7d8982f0e2c02f70311a18a8f7c41055060e229303
  | 7, 83 => 0x193b8202a8c509706081c62071708800908c1487ae0806630720418196a8c0c10864617d30409e1018ab0c180d26080b8307
  | 7, 84 => 0x21d18203b140802b60455850011e98b89204005de6061da61328cf0a120ec0c268c0c5af30303b0800026c0808660a43db06
  | 7, 85 => 0x1249840b0cc1cbdc20c4051041ae9830150c1c7bee4616f30705d1820498c948586081243250178819810c1436b406015b05
  | 7, 86 => 0x1aa18388d8c180946085f51061869831381810acc60a18510503cb09964081856c40a23030620c8801494c143b860a3e4704
  | 7, 87 => 0x14810301acc5cbdce4c42263624e5009288c188b660e0fd30329b9829250c1084020846362420658117244001d460c4a4205
  | 7, 88 => 0x54981920dc1033220a0d8b041b3182855840053840800f20325f782909c41048664a5ac7152a19030c76c1097e200069307
  | 7, 89 => 0x1399828f108489b060c24f30522818217a8c104d260e2493031f28801788c0c90760c504603230d808061c0c3fc60c42a627
  | 7, 90 => 0x154880076ac1422262a1f020528cf8a0e6885443e40848fb0403288016c4c18abc60c1a63030d68828bd4c1c34860a316714
  | 7, 91 => 0xb218291e8c102a040a2613250f09030970c185586063253062a9181946780834860c44265709498280604183e640a06e103
  | 7, 92 => 0x29c9830cd4c1c70440a41030523890187344148a2c6c4772050ff1821144410674e4c5f510126f184161480c5d8608422626
  | 7, 93 => 0x7218390f5c0c4ae60a04e60523188203a8c1007220c03710616c18302a4c1c2fe6063daf261381830768414030e2c02f106
  | 7, 94 => 0x3118215bc81894cc0c1fe3051b1d81124cc140f96080a8b0613018209e0c188d62082783032c71830c0d81015e60e077215
  | 7, 95 => 0x2dc9898134418acc60e27150012d1831810c10aa460c2fe30723f31b14588100d260a4811042cb181888cc5065a60e2ac304
  | 7, 96 => 0x7c98b88f8c1491ecae0186060ca0801470c0c1fa6083192052bf38b1288c1019860e5ee61611e98a82e0c2009d40452e601
  | 7, 97 => 0x11c18187d0818b6060a527f030ac182152081049260c29330706b18285a0c0cb586263b731328e18388c881c7d842a18b307
  | 7, 98 => 0x18a98b11868089382085a7a051c23830eedc1cb6e60c58b3071ef8810fa8810a33c0a3db30511539386ccc14446408383307
  | 7, 99 => 0x51902871cc0c7846023663072df98181b841833e6264a61040cf9841004c1855260a0ea30706d0800f1cc483cc40816f304
  | 7, 100 => 0x545820354c0c95f40458460410c08292b58d877860648d7240ed7a28c408105b46060761061b85818139400a2c40c564303
  | 7, 101 => 0x20e1828eed81495a2003496031da30313ec8140fe20c0aa315240b03104c850a8e40c49660618218381ec4186ba608126327
  | 7, 102 => 0x5d18303b040cb2d60a58b30417d1818c4881889e6082a331221090a92f99186cc60834420107e98392984000e060820a100
  | 7, 103 => 0x19d393977cc106d044a0f07251779839810c1c27420026620608898b00cc8142fe60a4c864710f5821214c1427260e02f702
  | 7, 104 => 0x2d79830a10c0c3766084d620326d50a0350c10b5962a4ad616138b8186dac1886660809d106078b8b0d2dc18921408545706
  | 7, 105 => 0x22e1028ef4814aa460a1c620513110304a4c1cac860c14070616b181910ac18b724242d23050f59818472c10ae062e4e8204
  | 7, 106 => 0x1821828c00c4c9524064ed62609a3818cec4008324064ed1042fb982111cc18a58c2a3e4b0405798217d0c105bc60825a305
  | 7, 107 => 0x1169808d44c1c10460a2383131b518b0590c1c18420c483b02054589171580c2d06081da3030ed3830c24400550608250105
  | 7, 108 => 0x1057010b60c10a33e26111b1410570a857c4008bce2c40c70609f18285c4c1c2fa6062e230312708017044005be60c3e7205
  | 7, 109 => 0x17a101958ac587b660e420e232479828f20c5c9dae460d81060d318284d040c3bc64c4ca2061cf10201cc80c2f66042be726
  | 7, 110 => 0x1c238381b981876e40a4802151b69838e48c1ca34c8c2a830507e98281f4814bc460c442b042d8189151084802a608558606
  | 7, 111 => 0x2da9838c7cc1863a60a18810026188004f1c5c1e220c0797142ef9830b268106a260a0ec10600e18294e4c10a6a60a271105
  | 7, 112 => 0x28b101917080c7f840c1f730621b38b09f1c1c16440647830726d18205a0c1cb5460c3db30401318183c440092442c411303
  | 7, 113 => 0xd998396bcc1066260a46a3131b69828ef0c1c6d46281293041ae98285e2c10af260e4ca2051a818b8aa0c0c70a20052e104
  | 7, 114 => 0x17a98201dac0c23220c5d330728910280d2808a6e604178e022cb5830b70c94bf220020b31621ed818862c08b2ce084bef26
  | 7, 115 => 0x43103958c4105316060aa31605d181861440c1d82025c43242d638a11dc8100a860a1083051153830d18c1453e20a5ac716
  | 7, 116 => 0xd6d8202e8c1c7d26083d320505d98204d04181d46064227151bd9838e30c1c592e2e4032150a29019369c1c4266085acb16
  | 7, 117 => 0x21010a1788c1088040c1502040ed58180a8c4c88560e4582051b319286ecc1cbd460c4adb060cb1828bd4c146c062a1d9100
  | 7, 118 => 0x23650115f440081060e16830527298301f0c0cc0062e482305161983090cc981666081cc317256d819360c1c32c60c0be304
  | 7, 119 => 0x68800c448144b46084473071f20800dd4c14415e065aa30419d38b9028c5c06c4064a66022ddb0307ecc0c6f460a543205
  | 7, 120 => 0x18b102857041830a2000053072089839218818b342005946360e6b818bd4c0c35ae2c1de3272d898204b0c1070260c1da306
  | 7, 121 => 0x2b5102923cc181d660a41f71501d902073440c87246c5191001df983967585811e6085fd1000661828ed8c5c11c60859d104
  | 7, 122 => 0x501828e80c1409c200015b031309931428c1873862a0d120720318b8058c1c64840c51e100047b8b93b4408708e26395306
  | 7, 123 => 0x1a798182a4c102f020c1f53052da98190a4c1c5e020a39c2061969828040c1c9ac4081117152f73121249c5015e60a405716
  | 7, 124 => 0x5438b06b78087324042303042cb3818890c9c1c460e1851062dd8821470c183ee60e2423031901020704400a33c081da714
  | 7, 125 => 0x5a38b8ef8c4807064e26930411290205c8c1087260e5902073031828080c5816e60636370419011b9675c4c92c20003f306
  | 7, 126 => 0xac90986ecc148cc40a32d30424b28004d1c085ee20020b31703e58287cac0c80860c5173072181029479818854e24514307
  | 7, 127 => 0x22a1820055c1400e4061996062089820114c1490840851ab042009828615c58b762003c93050cc88305704008a060e5ac713
  | 7, 128 => 0x2ea90188a9c5c9fb6021f32060e310300618503f86085e0a1322d18b170cc142da6081ad1062109028056c1809860e0d9306
  | 7, 129 => 0x8d982911cc0c5b060a29630600498203acc18012e2a2da30400b18294c0c1ca3040a37b3051511031598c1853ec0c362204
  | 7, 130 => 0x5a1018ff4c0cacc42a2e020706c98107344187c9604353206164b0212fe80801220058c1002f70820324818a40626557306
  | 7, 131 => 0x1285018400c1092661019b3050ed083090cc9c7e860637f31319f88283e8c149ea40a4692052fab1308e8c9cbea2082cc207
  | 7, 132 => 0x11539b8ff8c183b560c27530720030b07f8c0c33660620a5000871828430c106e0e2c0fc71724999b82fcc580f462e5d3704
  | 7, 133 => 0x2418800088c1459e6463bb32501cb0b1620c58a7260e3b631505430a1467c1042660a4122060421939149c0c0f9604278304
  | 7, 134 => 0x22b1828984c9c82a60e0df3061beb8188b0814a374084c720424a184082bc109ca60e39c2052721838c54c54beae463e1304
  | 7, 135 => 0x2c5982961cc1c332e0614220307f9820139c5482260a4eb30616f9820c34c1c2fe60c37b30300c082061581885660c3da100
  | 7, 136 => 0x28fb8a1479400840a0037810500c5808921c58a58e4c37d70414b1820ab0c14b4060c3711050ee181884cc0c5a460c1f4203
  | 7, 137 => 0xdb58286d5c10a1460e48c500133f0101f1c1099a62e02f10424608016a4c582f020043d3041a530b0accc0c62f402371b03
  | 7, 138 => 0x25b1821004c0c1c460a0157040f518180dd95895660e21810603e58313acc144f060e43530324a18300eac04890606530304
  | 7, 139 => 0x3021830e8c80c44e20c08f70528d8800446c5408820051c304054382162481475c6080fe10028d38a935cc189ecc0a36f205
  | 7, 140 => 0xd79820128c1839c40c2187260af9920134410854e0e4943031969819180c940a860639c207133f829718c58a0a408271103
  | 7, 141 => 0x12e1838a58c1c5fc6083b410505f98a0e86c0c8be6063aa10007608013b8cdc3b560825332503498189988104b860a2bb303
  | 7, 142 => 0x18e9830dc7d149066081da6262e598391fcc142e06061963040b61829598c10afce0c4a2307246303178dc1cba6e2c5d3306
  | 7, 143 => 0x3c43022ea18296e0c4c818e282d230310578a85ecc0c442e0e36a315
  | 8, 0 => 0x4a808079c5807660e003b1401eb830021018010c0c03f6030147a30101c48013c6a006f1401470a00b5c5c00be8c01c717
  | 8, 1 => 0x1b3828055808001e6e00764700f0820055c4800be0601b100018382805d81000ac6c038f0501c2818031818063e08010e26
  | 8, 2 => 0x2088100e9c5007c20000160300df8300fb818011e2c00b60601608300a399c055e8c041e12007722808f81006ec2c03db05
  | 8, 3 => 0xcb0280b8418070808006703015b83806c4180102080007160001830007c9801de4c020307015fa3007ac04064e0c02d100
  | 8, 4 => 0x17b83006dc5801020000ee350098800045818037c08028f35018a0280a1000046a0c00ee06020f1a0023c90037c2601b403
  | 8, 5 => 0x1828000d9c4803a20e00110301330280bec10013e26023f05011f028071c1c03ac08031e36004a0300c1c1c03820e005e06
  | 8, 6 => 0x15a818004c4c013e6c01b400010582803181c083c28030106013b81807985001ae0e00160401528180ad818016e2c03d707
  | 8, 7 => 0x188828085c9c05deac0096260048820002c1407ce2c03750001fd0200c881803c20e01971400dfab00c7d14083c48041e15
  | 8, 8 => 0x5d0a002a85000be2c005e1600cb02009cc1c002e2c02b71301c7920023c0c02b402000712004f8200d381806ce06015704
  | 8, 9 => 0x1b828017c54012e4601f10700f301009dc18066e0e01460600da82803bc8c056e4a00e40601908300b5810037c0603e604
  | 8, 10 => 0x1b3030078408027624028f1600bb8280bac0c05ec2801b606010b0280ac400081624016306018f83001bc14051c2400c647
  | 8, 11 => 0xb58180d3808060c06024104014b0180a389402ac0e026e03006b0b80b1c0c01a20a008f26004713003bcd8069c0201c607
  | 8, 12 => 0x10883803bc50076e0c00f60700ad808107c98047e04008f2501d30a0065c58050a0e01bf05000b028038410047c06019614
  | 8, 13 => 0x20f0b008c41801ae2804150401c202805dc0c01ecae000304001b930055854037c6c01d60301afab0029c0c06ee08022107
  | 8, 14 => 0x1a58180a3c48063c0a00900001b30380e3898050e0801670501758900d841803cc24031e5601a88300b181003ce06028f06
  | 8, 15 => 0xdf2300ddc1402ac26009f06004f03004191c02020a008e14007b82805dc1003cc0203d307000b838045c1005c608011703
  | 8, 16 => 0xb182004d89c011e0a01264700bb8300e3c8c02ac28005e2501dd8900e3d14051c0800d604018f9200a0410002a0a011647
  | 8, 17 => 0x1d38b80a3c9004820e03b30400208000e9c0807020a02f70500250280dc418040e0c02b727014b8b8027c1400d606019703
  | 8, 18 => 0x77818049c48022c4e01be2500a3020033c9c011c68009e120130838042c50082a06010712020a0080a8410016e2a025107
  | 8, 19 => 0x11a0000278d0063c0200c71601450080ecc1405ec2e0277040147010079c040782000091020158820089894011c6a00a704
  | 8, 20 => 0x3b8b00e388c04ae0e02c60601138300e1008056e0801c60600538300a3858037e8c041404002f02803bc5801dc2c01bf34
  | 8, 21 => 0x1058900e380400be6c00030501488380a041c006e2a03a60301d3038023c18076606038f3501478380dac1001de2a007707
  | 8, 22 => 0x830280a540000bc4c01564700df22801500004cc08009e1401608000c7cd4050c26009e0301471a00b041005080803e606
  | 8, 23 => 0x18f0a00e9808047c8c00170200bb1b801181c04060803d30500b8828031c1c05420e001703004f120027854071cac016a14
  | 8, 24 => 0x771a00b9c5c083c0401bf16005b0380ae814062a0c02272701eb82003dc0c08362402a404008793808fc0c051602016712
  | 8, 25 => 0x5f038107c90002e2a03850200471b00a3c4c0634060085040003830031814018e2a00420500df01002fc1c060e4e02b107
  | 8, 26 => 0xe301800d81805c60a023e56000d8980f5c5c04ca00022707020f8a806f8d4032e0800f60600bb9a00a3d9c02d60c028e06
  | 8, 27 => 0xc88280618dc03020a040706007712005581807de0c02a10201e38380fc81000c20000d70600770980f9018014e24030104
  | 8, 28 => 0x1438180bdc08071404020b0601830300b041c082800028615007712800040004ae2403272701cb02006591c024e0802af67
  | 8, 29 => 0x17083801bc1001ee0c03a612019303806d850013e4c006f060193930023c10056c0601371201688380a1c08050a0c001712
  | 8, 30 => 0x1f083006d01808280a038f04004f008027858034c8e034400004a820065c08064a0003ef1600cd8a0061cd0032e2402b706
  | 8, 31 => 0x1c70300a391c01ee0801960301c70900e581402f624012b12020f13009dc1c084c0a011100011fab002c810037e26028f05
  | 8, 32 => 0x7780801b814006e0e041e030105818018c10056e2800ef02018f1a8059c18037e6c030107005d02002101002d608038f25
  | 8, 33 => 0xdf9200c4418083e4603850601d30b0035818083e8a01b10401438b809dc48044e0a03fa0501c70a00edc1c000e08031f05
  | 8, 34 => 0x1f7930055c5002e206023f2601472b808580c01dc4c0196130208828039410002e0c010b12004a818025004038200003717
  | 8, 35 => 0x10583804181c07b606038f120103828045c5805d60e008e06017b83807591c040e0e000b03002f92809bd9c06420e01c627
  | 8, 36 => 0xf31b800d81006e20801e105003b030089c94051c4c02e30601db82000441801f62400940400378180e9854069c08041e06
  | 8, 37 => 0x20f9a803940c037e0603d60700c081800181c080e0e041e23010b0200cc41c069e0404140201738900c7d58011e6a038103
  | 8, 38 => 0x428000d841c00a80a0351070183028079cd0064c0c01360700818300a3d5c051e8a03960700438b00e3c4c00de0402b604
  | 8, 39 => 0xfa3003901004680c037100018f03010a81000c800005e3600f30180abd14083cac031505003b02808981c01362401f647
  | 8, 40 => 0x9b820107c50082a0401bf25016b030059c0c01080a009f1501658180e3894013e48028e5600df82006fc98037c4c003106
  | 8, 41 => 0x818200e100c05ee2e019705014301801d81c00be02038106010382008989c06e20e022105010b2b80a3cdc02ae2c023f46
  | 8, 42 => 0x608000ddc9c044200028e460038830025400046c6c019617006b890107c1400a20a01d6060147038099c1c002c28033705
  | 8, 43 => 0x1cb01802041407420e02b70300df1a004dc0c040e06041f010042000079c4805ec0e008f4501eb0a8075c58002a06011712
  | 8, 44 => 0x8d8900f2c4802160c027100010b03803140007ce0c038f56004a02803bc94002e26031e4601fb020107c0c050e2a011705
  | 8, 45 => 0xdf0a009995c03ae0e03db1200ff9380bd80800be8a01be2301b589009589c02ec0600ee020128828027898003406024105
  | 8, 46 => 0x18f0a8107c9408020001e604014b0200dd854037c2a02f60301d383808440000feac01130600f081807984c02c60e016100
  | 8, 47 => 0x12d89007985402ae04006e16004f918017958060200009f4500018180e141405ec2a028f3401a701804840005080e010303
  | 8, 48 => 0x10f9b809ec1c020c0c0177070143028065c5402c60a038f03009b82810541801220a03760700478a8029c14078e06032716
  | 8, 49 => 0x14b238023958050c2e0157130140828035c0c047e2c023e1601798200f9c5c02160803aa0100720280c9c14063e8c028f47
  | 8, 50 => 0x11f80809dc14071c6c00150700f38980e9c48032e0e00460301f90280a3c9403cc0e032f570173098095c1405ec2c032f15
  | 8, 51 => 0x208818101c0c01280403771700479a00a1c5001a20c00ef45020303801dc1807dc06004606016a8000c7914054c6e02a105
  | 8, 52 => 0xda8200eac0401dc0802d707000b010038414013e6a031f2600938300ad8dc07a20e02b105017382002788c069e06008e04
  | 8, 53 => 0x4f2b0017c10032c2c03e10700b38200d3814011c0a026f37002f82803c41802f626038e4600f38a00a9cd0037c2c03db06
  | 8, 54 => 0x87ab00e6814056c2e01270300cb030042c0c04cc0c02b734000882001b80802360c00760302110200bdc58060e2a020b04
  | 8, 55 => 0x147820017cd401cc0c001f2401c70a80b185c074e0a03630401f30280b0414006c0a023e02011f03005dc4805c60603d303
  | 8, 56 => 0x2008380e984c060e0c04260601130280a185004ae06041e25009b030044418013e28009502012b0300a5c1c05ac4e010106
  | 8, 57 => 0x1c79a00a3c9c051c4e00650000f3830015418036a06031e04011f008062c0c05cc8e028e0101db82805584802620c00ef35
  | 8, 58 => 0x1b8300b981c05cc0c02260601bb030089c98083c2602f713020a0180fbd9c01a20000940001c7a300b1c5008220c02fa14
  | 8, 59 => 0x1b302801b810064e0e008e2401eb890079c08000e0a038e05004f8080f6c10032e2600120300e28000c5018051e4c00ee56
  | 8, 60 => 0x1e3830101c1400220e005e03001d820079c10060c2e03bb0601470980c0414032c0400850600da02000041c011c06026607
  | 8, 61 => 0x208808005c14083e24041f060163038040c14051e020157050077920039000023eac01570600cb8b8109400071c8a00b603
  | 8, 62 => 0x19b8200e9814063e28010707014722800c40000bc04001717020fab0036c48080e0803163600b58380c441005ac06029706
  | 8, 63 => 0x198800085818064c8e008f020190828027c94063c06001607003b8a80ca818054206009e02012b83008fcd8008c0a030714
  | 8, 64 => 0x1a782810541401ae0801b50001130200bac1002e20c009e0401c200005ac14032628023e260158818054418071c6a006b04
  | 8, 65 => 0x1958a00a3854051c6c01d60501db8180fc40006ee2a00b10000e302000c41c051c6a042603004a830080400051c48006e06
  | 8, 66 => 0x1bb12809581c006e4e008e02019b1380a1c18055c08005e3500c90200e9c18074c0c01bf1501c7010044c0c022e0e02b313
  | 8, 67 => 0xf59180a1c5805e42802b7160028830055810057c48000b0701e58380b9c18050c24009f0200630180b1c18020e0602f715
  | 8, 68 => 0x5b020005c50044c4c03840601fb03806441800e20e036647020f1b006041806c20a00ab1201ab23809980c06a20a030704
  | 8, 69 => 0x1f71b0041c1807ec0c03d10001f3038042c1403340201bf0201038900e380c01ca0c01560301908000a181001220600ee14
  | 8, 70 => 0x1dd83806d01406d62802030500b98180a3c0c071e6c035b04004f8180c7c58083c08031e1600db81810781401020c006e03
  | 8, 71 => 0x1bb0b80e0410063e2a037105014b02808980c051e2e041e46018f8100b1c14018c0800ef0500d08300a3c0802e200005f02
  | 8, 72 => 0x1f30180d9c1c050c0401130401c78a00a1c4805962402510000378b0017d58066c0e032f2701c31300bd81401ce0602e707
  | 8, 73 => 0x1e382803b80c074e0600e103004f1280bdc0c074c0801750300a303803cc1401a208028e370087128001c1c050a0a010307
  | 8, 74 => 0x1438380e991c05640a00550500df030046c0c011eac01d71700cd8080e1c8c06ee0e01970601bb8a0079858037e8a005e04
  | 8, 75 => 0x898380f4c18056c0e041f34017d00806bd58060c0e009e13007b8900c980c01280600ef130048830065854028c0a01b105
  | 8, 76 => 0x770080e9c4c05d60a035f2700e08300b8400071c08029100017b8900bd84806ec0a041f46006b8280b9c0c07ae06000b12
  | 8, 77 => 0xab8180fb898069e0803c712018f12010840001820e01760700cb0900ec400044e2e00d6070142820071c18010a0a018503
  | 8, 78 => 0x68838043c48012202041e450163028027c4804ac0a01e707020f8200b1c4800dc28005e46018f1a00a1858063c4a011715
  | 8, 79 => 0x8b8300a101401c20c0167070078800006804026e0c00ef0601c783006fcd4013eac02860600f08300dd850060e2c00fb05
  | 8, 80 => 0x18f818055814023608010b070078838023858017e2e02d605003b02003b88c071e2c01410001c70b0107c5801c80602fb01
  | 8, 81 => 0x10b8b80f4c10012a0a041e350171838044c1400c606005f0600370a8040400071e2a01561701bb020087c18037cac004717
  | 8, 82 => 0x888380e0408037e28028713008083800d80c052c0e001704000183800584c047c6c02960600cb03805180c020e08041501
  | 8, 83 => 0x938380a1c1403a20001310700908380cdc0c01ac0a031f3601eb23808fc1800bc2a001b010077ab009840001dc0a008e46
  | 8, 84 => 0x18a8200c7c04067624028f15015591805d81804420c036100007b8380e9c58020e0a03d70501f38380e38d006ee0c011b07
  | 8, 85 => 0xab8b80f995c02ae2a01710401d382004dc1c051e6c012304004f1b006f814056e2a02f604008b0380c7898058e08042607
  | 8, 86 => 0x10b838107c4c033408028e03020a03009bc18078e08042716007282800d81c057626008e25007381001ac1400de2a030604
  | 8, 87 => 0x1758300b9c1404ae08026717016b03807940c03ac0e01e605000b0a80edc4802f60601e60600230200e384c063c04000b06
  | 8, 88 => 0x7782010195c02ac2c03b30600bb028107cd802ae0e03bb04004f2300e3c04011e8c008f1401c78100e3890064e2a001616
  | 8, 89 => 0x2150a0017c98058606025106017b8a00e4814058e26024106018a000105898030208041104013d89009bc58014e0e034f01
  | 8, 90 => 0x17b09802391402a20e006b02019302802781407760a02f704005b8b802840005080c03a715008d8280ddc5803ce2a00ee36
  | 8, 91 => 0xb1b8004414074c2e003625020b9180fd814036a0c041e0100032b80f6c1c00bc8a012705005b02805c41c037c48028e17
  | 8, 92 => 0x1478a00a3d5804060c009f46007723001780407860e00be05019b8900eec0c013e68016b12017b0300f7c9c011e6c031404
  | 8, 93 => 0x9303801ac18025608028e05000b9a0005818060e260291060140830019c1007de6e03910000470a8071814071e4c023f04
  | 8, 94 => 0x20f81006c40c064c08009e4500f382803b85403220e00cf6700c083800584807de6c014500000381800585c070a08016303
  | 8, 95 => 0x779a007a80406ce0802b70500df9180ac418013e2c034f06001b23800c414012200002a04002a03010981000e20002a106
  | 8, 96 => 0x1b383009140003420e03370601018180c7c9403ce2e02c70700f30b80ad814050c0e0396060077a300dd80c063e68000b04
  | 9, 0 => 0x71a0000408001c24000f0500078300038180000000007230007820001898000208000f360007898001018000a02000e35
  | 9, 1 => 0x2028001400001e2a000f240005890001010000a060004010007008003858000a08000f260007120003854001c28000e03
  | 9, 2 => 0x2830003810001e4a000e020007808001000001e2800050200072b0003cd4001c460004020000828003c8c001e8a000e26
  | 9, 3 => 0x7a30003cd0001c0a000e4600071b0001414001eac000101000789000384c0008060001060007128003c0c000206000f02
  | 9, 4 => 0x3c58000200000e45
  | 10, 0 => 0x0
  | _, _ => 0

def readState : Nat → Nat → Nat → List Nat
  | 0, _, _ => inputs
  | d + 1, s, j =>
    let code := fld (stateMoves s (j / 16)) 25 (j % 16)
    mv (mask cutCount) (code % 4096) (readState d (s + 1) (code / 4096))

def state (s j : Nat) : List Nat := readState (10 - s) s j

def stateIndex (s : Nat) (xs : List Nat) : Nat :=
  bsr (fun i => fld (stateKeys s (i / 16)) 32 (i % 16)) (hk xs) 16 0 (stateCount s)

def checkState (s : Nat) := bar cutCount state stateCount stateIndex id scorePool s

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem inputsEncoded :
    (List.ofFn fun i : Fin 7 => (fun x : Fin 7 → Bool => x i)).map (fun a => encL a sampleRows) = inputs := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem goalEncoded : encL core sampleRows = goal cutCount := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem properFail : ∀ zs ∈ inputs.sublists, zs ≠ inputs →
    (cov cutCount zs &&& lo cutCount) ≠ lo cutCount := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_3_0 : span (checkState 3) 1 0 = true := by decide +kernel

theorem all_3 : span (checkState 3) 1 0 = true := block_3_0

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_4_0 : span (checkState 4) 8 0 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_4_8 : span (checkState 4) 8 8 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_4_16 : span (checkState 4) 3 16 = true := by decide +kernel

theorem combined_4_1_0 : span (checkState 4) 16 0 = true := @span_join (checkState 4) 8 0 8 block_4_0 block_4_8
theorem combined_4_2_0 : span (checkState 4) 19 0 = true := @span_join (checkState 4) 16 0 3 combined_4_1_0 block_4_16
theorem all_4 : span (checkState 4) 19 0 = true := combined_4_2_0

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_5_0 : span (checkState 5) 8 0 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_5_8 : span (checkState 5) 8 8 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_5_16 : span (checkState 5) 8 16 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_5_24 : span (checkState 5) 8 24 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_5_32 : span (checkState 5) 8 32 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_5_40 : span (checkState 5) 8 40 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_5_48 : span (checkState 5) 8 48 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_5_56 : span (checkState 5) 8 56 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_5_64 : span (checkState 5) 8 64 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_5_72 : span (checkState 5) 8 72 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_5_80 : span (checkState 5) 8 80 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_5_88 : span (checkState 5) 8 88 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_5_96 : span (checkState 5) 4 96 = true := by decide +kernel

theorem combined_5_1_0 : span (checkState 5) 16 0 = true := @span_join (checkState 5) 8 0 8 block_5_0 block_5_8
theorem combined_5_1_1 : span (checkState 5) 16 16 = true := @span_join (checkState 5) 8 16 8 block_5_16 block_5_24
theorem combined_5_1_2 : span (checkState 5) 16 32 = true := @span_join (checkState 5) 8 32 8 block_5_32 block_5_40
theorem combined_5_1_3 : span (checkState 5) 16 48 = true := @span_join (checkState 5) 8 48 8 block_5_48 block_5_56
theorem combined_5_1_4 : span (checkState 5) 16 64 = true := @span_join (checkState 5) 8 64 8 block_5_64 block_5_72
theorem combined_5_1_5 : span (checkState 5) 16 80 = true := @span_join (checkState 5) 8 80 8 block_5_80 block_5_88
theorem combined_5_2_0 : span (checkState 5) 32 0 = true := @span_join (checkState 5) 16 0 16 combined_5_1_0 combined_5_1_1
theorem combined_5_2_1 : span (checkState 5) 32 32 = true := @span_join (checkState 5) 16 32 16 combined_5_1_2 combined_5_1_3
theorem combined_5_2_2 : span (checkState 5) 32 64 = true := @span_join (checkState 5) 16 64 16 combined_5_1_4 combined_5_1_5
theorem combined_5_4_0 : span (checkState 5) 64 0 = true := @span_join (checkState 5) 32 0 32 combined_5_2_0 combined_5_2_1
theorem combined_5_4_1 : span (checkState 5) 36 64 = true := @span_join (checkState 5) 32 64 4 combined_5_2_2 block_5_96
theorem combined_5_8_0 : span (checkState 5) 100 0 = true := @span_join (checkState 5) 64 0 36 combined_5_4_0 combined_5_4_1
theorem all_5 : span (checkState 5) 100 0 = true := combined_5_8_0

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_0 : span (checkState 6) 8 0 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_8 : span (checkState 6) 8 8 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_16 : span (checkState 6) 8 16 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_24 : span (checkState 6) 8 24 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_32 : span (checkState 6) 8 32 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_40 : span (checkState 6) 8 40 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_48 : span (checkState 6) 8 48 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_56 : span (checkState 6) 8 56 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_64 : span (checkState 6) 8 64 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_72 : span (checkState 6) 8 72 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_80 : span (checkState 6) 8 80 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_88 : span (checkState 6) 8 88 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_96 : span (checkState 6) 8 96 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_104 : span (checkState 6) 8 104 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_112 : span (checkState 6) 8 112 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_120 : span (checkState 6) 8 120 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_128 : span (checkState 6) 8 128 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_136 : span (checkState 6) 8 136 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_144 : span (checkState 6) 8 144 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_152 : span (checkState 6) 8 152 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_160 : span (checkState 6) 8 160 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_168 : span (checkState 6) 8 168 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_176 : span (checkState 6) 8 176 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_184 : span (checkState 6) 8 184 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_192 : span (checkState 6) 8 192 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_200 : span (checkState 6) 8 200 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_208 : span (checkState 6) 8 208 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_216 : span (checkState 6) 8 216 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_224 : span (checkState 6) 8 224 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_232 : span (checkState 6) 8 232 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_240 : span (checkState 6) 8 240 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_248 : span (checkState 6) 8 248 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_256 : span (checkState 6) 8 256 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_264 : span (checkState 6) 8 264 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_272 : span (checkState 6) 8 272 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_280 : span (checkState 6) 8 280 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_288 : span (checkState 6) 8 288 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_296 : span (checkState 6) 8 296 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_304 : span (checkState 6) 8 304 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_312 : span (checkState 6) 8 312 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_320 : span (checkState 6) 8 320 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_328 : span (checkState 6) 8 328 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_336 : span (checkState 6) 8 336 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_344 : span (checkState 6) 8 344 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_352 : span (checkState 6) 8 352 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_360 : span (checkState 6) 8 360 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_368 : span (checkState 6) 8 368 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_376 : span (checkState 6) 8 376 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_384 : span (checkState 6) 8 384 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_392 : span (checkState 6) 8 392 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_400 : span (checkState 6) 8 400 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_408 : span (checkState 6) 8 408 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_416 : span (checkState 6) 8 416 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_424 : span (checkState 6) 8 424 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_432 : span (checkState 6) 8 432 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_440 : span (checkState 6) 8 440 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_448 : span (checkState 6) 8 448 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_456 : span (checkState 6) 8 456 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_464 : span (checkState 6) 8 464 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_472 : span (checkState 6) 8 472 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_480 : span (checkState 6) 8 480 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_488 : span (checkState 6) 8 488 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_496 : span (checkState 6) 8 496 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_504 : span (checkState 6) 8 504 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_512 : span (checkState 6) 8 512 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_520 : span (checkState 6) 8 520 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_528 : span (checkState 6) 8 528 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_536 : span (checkState 6) 8 536 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_544 : span (checkState 6) 8 544 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_552 : span (checkState 6) 8 552 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_560 : span (checkState 6) 8 560 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_568 : span (checkState 6) 8 568 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_576 : span (checkState 6) 8 576 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_584 : span (checkState 6) 8 584 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_592 : span (checkState 6) 8 592 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_600 : span (checkState 6) 8 600 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_608 : span (checkState 6) 8 608 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_616 : span (checkState 6) 8 616 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_624 : span (checkState 6) 8 624 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_632 : span (checkState 6) 8 632 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_640 : span (checkState 6) 8 640 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_648 : span (checkState 6) 8 648 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_656 : span (checkState 6) 8 656 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_6_664 : span (checkState 6) 2 664 = true := by decide +kernel

theorem combined_6_1_0 : span (checkState 6) 16 0 = true := @span_join (checkState 6) 8 0 8 block_6_0 block_6_8
theorem combined_6_1_1 : span (checkState 6) 16 16 = true := @span_join (checkState 6) 8 16 8 block_6_16 block_6_24
theorem combined_6_1_2 : span (checkState 6) 16 32 = true := @span_join (checkState 6) 8 32 8 block_6_32 block_6_40
theorem combined_6_1_3 : span (checkState 6) 16 48 = true := @span_join (checkState 6) 8 48 8 block_6_48 block_6_56
theorem combined_6_1_4 : span (checkState 6) 16 64 = true := @span_join (checkState 6) 8 64 8 block_6_64 block_6_72
theorem combined_6_1_5 : span (checkState 6) 16 80 = true := @span_join (checkState 6) 8 80 8 block_6_80 block_6_88
theorem combined_6_1_6 : span (checkState 6) 16 96 = true := @span_join (checkState 6) 8 96 8 block_6_96 block_6_104
theorem combined_6_1_7 : span (checkState 6) 16 112 = true := @span_join (checkState 6) 8 112 8 block_6_112 block_6_120
theorem combined_6_1_8 : span (checkState 6) 16 128 = true := @span_join (checkState 6) 8 128 8 block_6_128 block_6_136
theorem combined_6_1_9 : span (checkState 6) 16 144 = true := @span_join (checkState 6) 8 144 8 block_6_144 block_6_152
theorem combined_6_1_10 : span (checkState 6) 16 160 = true := @span_join (checkState 6) 8 160 8 block_6_160 block_6_168
theorem combined_6_1_11 : span (checkState 6) 16 176 = true := @span_join (checkState 6) 8 176 8 block_6_176 block_6_184
theorem combined_6_1_12 : span (checkState 6) 16 192 = true := @span_join (checkState 6) 8 192 8 block_6_192 block_6_200
theorem combined_6_1_13 : span (checkState 6) 16 208 = true := @span_join (checkState 6) 8 208 8 block_6_208 block_6_216
theorem combined_6_1_14 : span (checkState 6) 16 224 = true := @span_join (checkState 6) 8 224 8 block_6_224 block_6_232
theorem combined_6_1_15 : span (checkState 6) 16 240 = true := @span_join (checkState 6) 8 240 8 block_6_240 block_6_248
theorem combined_6_1_16 : span (checkState 6) 16 256 = true := @span_join (checkState 6) 8 256 8 block_6_256 block_6_264
theorem combined_6_1_17 : span (checkState 6) 16 272 = true := @span_join (checkState 6) 8 272 8 block_6_272 block_6_280
theorem combined_6_1_18 : span (checkState 6) 16 288 = true := @span_join (checkState 6) 8 288 8 block_6_288 block_6_296
theorem combined_6_1_19 : span (checkState 6) 16 304 = true := @span_join (checkState 6) 8 304 8 block_6_304 block_6_312
theorem combined_6_1_20 : span (checkState 6) 16 320 = true := @span_join (checkState 6) 8 320 8 block_6_320 block_6_328
theorem combined_6_1_21 : span (checkState 6) 16 336 = true := @span_join (checkState 6) 8 336 8 block_6_336 block_6_344
theorem combined_6_1_22 : span (checkState 6) 16 352 = true := @span_join (checkState 6) 8 352 8 block_6_352 block_6_360
theorem combined_6_1_23 : span (checkState 6) 16 368 = true := @span_join (checkState 6) 8 368 8 block_6_368 block_6_376
theorem combined_6_1_24 : span (checkState 6) 16 384 = true := @span_join (checkState 6) 8 384 8 block_6_384 block_6_392
theorem combined_6_1_25 : span (checkState 6) 16 400 = true := @span_join (checkState 6) 8 400 8 block_6_400 block_6_408
theorem combined_6_1_26 : span (checkState 6) 16 416 = true := @span_join (checkState 6) 8 416 8 block_6_416 block_6_424
theorem combined_6_1_27 : span (checkState 6) 16 432 = true := @span_join (checkState 6) 8 432 8 block_6_432 block_6_440
theorem combined_6_1_28 : span (checkState 6) 16 448 = true := @span_join (checkState 6) 8 448 8 block_6_448 block_6_456
theorem combined_6_1_29 : span (checkState 6) 16 464 = true := @span_join (checkState 6) 8 464 8 block_6_464 block_6_472
theorem combined_6_1_30 : span (checkState 6) 16 480 = true := @span_join (checkState 6) 8 480 8 block_6_480 block_6_488
theorem combined_6_1_31 : span (checkState 6) 16 496 = true := @span_join (checkState 6) 8 496 8 block_6_496 block_6_504
theorem combined_6_1_32 : span (checkState 6) 16 512 = true := @span_join (checkState 6) 8 512 8 block_6_512 block_6_520
theorem combined_6_1_33 : span (checkState 6) 16 528 = true := @span_join (checkState 6) 8 528 8 block_6_528 block_6_536
theorem combined_6_1_34 : span (checkState 6) 16 544 = true := @span_join (checkState 6) 8 544 8 block_6_544 block_6_552
theorem combined_6_1_35 : span (checkState 6) 16 560 = true := @span_join (checkState 6) 8 560 8 block_6_560 block_6_568
theorem combined_6_1_36 : span (checkState 6) 16 576 = true := @span_join (checkState 6) 8 576 8 block_6_576 block_6_584
theorem combined_6_1_37 : span (checkState 6) 16 592 = true := @span_join (checkState 6) 8 592 8 block_6_592 block_6_600
theorem combined_6_1_38 : span (checkState 6) 16 608 = true := @span_join (checkState 6) 8 608 8 block_6_608 block_6_616
theorem combined_6_1_39 : span (checkState 6) 16 624 = true := @span_join (checkState 6) 8 624 8 block_6_624 block_6_632
theorem combined_6_1_40 : span (checkState 6) 16 640 = true := @span_join (checkState 6) 8 640 8 block_6_640 block_6_648
theorem combined_6_1_41 : span (checkState 6) 10 656 = true := @span_join (checkState 6) 8 656 2 block_6_656 block_6_664
theorem combined_6_2_0 : span (checkState 6) 32 0 = true := @span_join (checkState 6) 16 0 16 combined_6_1_0 combined_6_1_1
theorem combined_6_2_1 : span (checkState 6) 32 32 = true := @span_join (checkState 6) 16 32 16 combined_6_1_2 combined_6_1_3
theorem combined_6_2_2 : span (checkState 6) 32 64 = true := @span_join (checkState 6) 16 64 16 combined_6_1_4 combined_6_1_5
theorem combined_6_2_3 : span (checkState 6) 32 96 = true := @span_join (checkState 6) 16 96 16 combined_6_1_6 combined_6_1_7
theorem combined_6_2_4 : span (checkState 6) 32 128 = true := @span_join (checkState 6) 16 128 16 combined_6_1_8 combined_6_1_9
theorem combined_6_2_5 : span (checkState 6) 32 160 = true := @span_join (checkState 6) 16 160 16 combined_6_1_10 combined_6_1_11
theorem combined_6_2_6 : span (checkState 6) 32 192 = true := @span_join (checkState 6) 16 192 16 combined_6_1_12 combined_6_1_13
theorem combined_6_2_7 : span (checkState 6) 32 224 = true := @span_join (checkState 6) 16 224 16 combined_6_1_14 combined_6_1_15
theorem combined_6_2_8 : span (checkState 6) 32 256 = true := @span_join (checkState 6) 16 256 16 combined_6_1_16 combined_6_1_17
theorem combined_6_2_9 : span (checkState 6) 32 288 = true := @span_join (checkState 6) 16 288 16 combined_6_1_18 combined_6_1_19
theorem combined_6_2_10 : span (checkState 6) 32 320 = true := @span_join (checkState 6) 16 320 16 combined_6_1_20 combined_6_1_21
theorem combined_6_2_11 : span (checkState 6) 32 352 = true := @span_join (checkState 6) 16 352 16 combined_6_1_22 combined_6_1_23
theorem combined_6_2_12 : span (checkState 6) 32 384 = true := @span_join (checkState 6) 16 384 16 combined_6_1_24 combined_6_1_25
theorem combined_6_2_13 : span (checkState 6) 32 416 = true := @span_join (checkState 6) 16 416 16 combined_6_1_26 combined_6_1_27
theorem combined_6_2_14 : span (checkState 6) 32 448 = true := @span_join (checkState 6) 16 448 16 combined_6_1_28 combined_6_1_29
theorem combined_6_2_15 : span (checkState 6) 32 480 = true := @span_join (checkState 6) 16 480 16 combined_6_1_30 combined_6_1_31
theorem combined_6_2_16 : span (checkState 6) 32 512 = true := @span_join (checkState 6) 16 512 16 combined_6_1_32 combined_6_1_33
theorem combined_6_2_17 : span (checkState 6) 32 544 = true := @span_join (checkState 6) 16 544 16 combined_6_1_34 combined_6_1_35
theorem combined_6_2_18 : span (checkState 6) 32 576 = true := @span_join (checkState 6) 16 576 16 combined_6_1_36 combined_6_1_37
theorem combined_6_2_19 : span (checkState 6) 32 608 = true := @span_join (checkState 6) 16 608 16 combined_6_1_38 combined_6_1_39
theorem combined_6_2_20 : span (checkState 6) 26 640 = true := @span_join (checkState 6) 16 640 10 combined_6_1_40 combined_6_1_41
theorem combined_6_4_0 : span (checkState 6) 64 0 = true := @span_join (checkState 6) 32 0 32 combined_6_2_0 combined_6_2_1
theorem combined_6_4_1 : span (checkState 6) 64 64 = true := @span_join (checkState 6) 32 64 32 combined_6_2_2 combined_6_2_3
theorem combined_6_4_2 : span (checkState 6) 64 128 = true := @span_join (checkState 6) 32 128 32 combined_6_2_4 combined_6_2_5
theorem combined_6_4_3 : span (checkState 6) 64 192 = true := @span_join (checkState 6) 32 192 32 combined_6_2_6 combined_6_2_7
theorem combined_6_4_4 : span (checkState 6) 64 256 = true := @span_join (checkState 6) 32 256 32 combined_6_2_8 combined_6_2_9
theorem combined_6_4_5 : span (checkState 6) 64 320 = true := @span_join (checkState 6) 32 320 32 combined_6_2_10 combined_6_2_11
theorem combined_6_4_6 : span (checkState 6) 64 384 = true := @span_join (checkState 6) 32 384 32 combined_6_2_12 combined_6_2_13
theorem combined_6_4_7 : span (checkState 6) 64 448 = true := @span_join (checkState 6) 32 448 32 combined_6_2_14 combined_6_2_15
theorem combined_6_4_8 : span (checkState 6) 64 512 = true := @span_join (checkState 6) 32 512 32 combined_6_2_16 combined_6_2_17
theorem combined_6_4_9 : span (checkState 6) 64 576 = true := @span_join (checkState 6) 32 576 32 combined_6_2_18 combined_6_2_19
theorem combined_6_8_0 : span (checkState 6) 128 0 = true := @span_join (checkState 6) 64 0 64 combined_6_4_0 combined_6_4_1
theorem combined_6_8_1 : span (checkState 6) 128 128 = true := @span_join (checkState 6) 64 128 64 combined_6_4_2 combined_6_4_3
theorem combined_6_8_2 : span (checkState 6) 128 256 = true := @span_join (checkState 6) 64 256 64 combined_6_4_4 combined_6_4_5
theorem combined_6_8_3 : span (checkState 6) 128 384 = true := @span_join (checkState 6) 64 384 64 combined_6_4_6 combined_6_4_7
theorem combined_6_8_4 : span (checkState 6) 128 512 = true := @span_join (checkState 6) 64 512 64 combined_6_4_8 combined_6_4_9
theorem combined_6_16_0 : span (checkState 6) 256 0 = true := @span_join (checkState 6) 128 0 128 combined_6_8_0 combined_6_8_1
theorem combined_6_16_1 : span (checkState 6) 256 256 = true := @span_join (checkState 6) 128 256 128 combined_6_8_2 combined_6_8_3
theorem combined_6_16_2 : span (checkState 6) 154 512 = true := @span_join (checkState 6) 128 512 26 combined_6_8_4 combined_6_2_20
theorem combined_6_32_0 : span (checkState 6) 512 0 = true := @span_join (checkState 6) 256 0 256 combined_6_16_0 combined_6_16_1
theorem combined_6_64_0 : span (checkState 6) 666 0 = true := @span_join (checkState 6) 512 0 154 combined_6_32_0 combined_6_16_2
theorem all_6 : span (checkState 6) 666 0 = true := combined_6_64_0

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_0 : span (checkState 7) 8 0 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_8 : span (checkState 7) 8 8 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_16 : span (checkState 7) 8 16 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_24 : span (checkState 7) 8 24 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_32 : span (checkState 7) 8 32 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_40 : span (checkState 7) 8 40 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_48 : span (checkState 7) 8 48 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_56 : span (checkState 7) 8 56 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_64 : span (checkState 7) 8 64 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_72 : span (checkState 7) 8 72 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_80 : span (checkState 7) 8 80 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_88 : span (checkState 7) 8 88 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_96 : span (checkState 7) 8 96 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_104 : span (checkState 7) 8 104 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_112 : span (checkState 7) 8 112 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_120 : span (checkState 7) 8 120 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_128 : span (checkState 7) 8 128 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_136 : span (checkState 7) 8 136 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_144 : span (checkState 7) 8 144 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_152 : span (checkState 7) 8 152 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_160 : span (checkState 7) 8 160 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_168 : span (checkState 7) 8 168 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_176 : span (checkState 7) 8 176 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_184 : span (checkState 7) 8 184 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_192 : span (checkState 7) 8 192 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_200 : span (checkState 7) 8 200 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_208 : span (checkState 7) 8 208 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_216 : span (checkState 7) 8 216 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_224 : span (checkState 7) 8 224 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_232 : span (checkState 7) 8 232 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_240 : span (checkState 7) 8 240 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_248 : span (checkState 7) 8 248 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_256 : span (checkState 7) 8 256 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_264 : span (checkState 7) 8 264 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_272 : span (checkState 7) 8 272 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_280 : span (checkState 7) 8 280 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_288 : span (checkState 7) 8 288 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_296 : span (checkState 7) 8 296 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_304 : span (checkState 7) 8 304 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_312 : span (checkState 7) 8 312 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_320 : span (checkState 7) 8 320 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_328 : span (checkState 7) 8 328 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_336 : span (checkState 7) 8 336 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_344 : span (checkState 7) 8 344 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_352 : span (checkState 7) 8 352 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_360 : span (checkState 7) 8 360 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_368 : span (checkState 7) 8 368 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_376 : span (checkState 7) 8 376 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_384 : span (checkState 7) 8 384 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_392 : span (checkState 7) 8 392 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_400 : span (checkState 7) 8 400 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_408 : span (checkState 7) 8 408 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_416 : span (checkState 7) 8 416 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_424 : span (checkState 7) 8 424 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_432 : span (checkState 7) 8 432 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_440 : span (checkState 7) 8 440 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_448 : span (checkState 7) 8 448 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_456 : span (checkState 7) 8 456 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_464 : span (checkState 7) 8 464 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_472 : span (checkState 7) 8 472 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_480 : span (checkState 7) 8 480 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_488 : span (checkState 7) 8 488 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_496 : span (checkState 7) 8 496 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_504 : span (checkState 7) 8 504 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_512 : span (checkState 7) 8 512 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_520 : span (checkState 7) 8 520 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_528 : span (checkState 7) 8 528 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_536 : span (checkState 7) 8 536 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_544 : span (checkState 7) 8 544 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_552 : span (checkState 7) 8 552 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_560 : span (checkState 7) 8 560 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_568 : span (checkState 7) 8 568 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_576 : span (checkState 7) 8 576 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_584 : span (checkState 7) 8 584 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_592 : span (checkState 7) 8 592 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_600 : span (checkState 7) 8 600 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_608 : span (checkState 7) 8 608 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_616 : span (checkState 7) 8 616 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_624 : span (checkState 7) 8 624 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_632 : span (checkState 7) 8 632 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_640 : span (checkState 7) 8 640 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_648 : span (checkState 7) 8 648 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_656 : span (checkState 7) 8 656 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_664 : span (checkState 7) 8 664 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_672 : span (checkState 7) 8 672 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_680 : span (checkState 7) 8 680 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_688 : span (checkState 7) 8 688 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_696 : span (checkState 7) 8 696 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_704 : span (checkState 7) 8 704 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_712 : span (checkState 7) 8 712 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_720 : span (checkState 7) 8 720 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_728 : span (checkState 7) 8 728 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_736 : span (checkState 7) 8 736 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_744 : span (checkState 7) 8 744 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_752 : span (checkState 7) 8 752 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_760 : span (checkState 7) 8 760 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_768 : span (checkState 7) 8 768 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_776 : span (checkState 7) 8 776 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_784 : span (checkState 7) 8 784 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_792 : span (checkState 7) 8 792 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_800 : span (checkState 7) 8 800 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_808 : span (checkState 7) 8 808 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_816 : span (checkState 7) 8 816 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_824 : span (checkState 7) 8 824 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_832 : span (checkState 7) 8 832 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_840 : span (checkState 7) 8 840 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_848 : span (checkState 7) 8 848 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_856 : span (checkState 7) 8 856 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_864 : span (checkState 7) 8 864 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_872 : span (checkState 7) 8 872 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_880 : span (checkState 7) 8 880 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_888 : span (checkState 7) 8 888 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_896 : span (checkState 7) 8 896 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_904 : span (checkState 7) 8 904 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_912 : span (checkState 7) 8 912 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_920 : span (checkState 7) 8 920 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_928 : span (checkState 7) 8 928 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_936 : span (checkState 7) 8 936 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_944 : span (checkState 7) 8 944 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_952 : span (checkState 7) 8 952 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_960 : span (checkState 7) 8 960 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_968 : span (checkState 7) 8 968 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_976 : span (checkState 7) 8 976 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_984 : span (checkState 7) 8 984 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_992 : span (checkState 7) 8 992 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1000 : span (checkState 7) 8 1000 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1008 : span (checkState 7) 8 1008 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1016 : span (checkState 7) 8 1016 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1024 : span (checkState 7) 8 1024 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1032 : span (checkState 7) 8 1032 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1040 : span (checkState 7) 8 1040 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1048 : span (checkState 7) 8 1048 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1056 : span (checkState 7) 8 1056 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1064 : span (checkState 7) 8 1064 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1072 : span (checkState 7) 8 1072 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1080 : span (checkState 7) 8 1080 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1088 : span (checkState 7) 8 1088 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1096 : span (checkState 7) 8 1096 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1104 : span (checkState 7) 8 1104 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1112 : span (checkState 7) 8 1112 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1120 : span (checkState 7) 8 1120 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1128 : span (checkState 7) 8 1128 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1136 : span (checkState 7) 8 1136 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1144 : span (checkState 7) 8 1144 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1152 : span (checkState 7) 8 1152 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1160 : span (checkState 7) 8 1160 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1168 : span (checkState 7) 8 1168 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1176 : span (checkState 7) 8 1176 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1184 : span (checkState 7) 8 1184 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1192 : span (checkState 7) 8 1192 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1200 : span (checkState 7) 8 1200 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1208 : span (checkState 7) 8 1208 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1216 : span (checkState 7) 8 1216 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1224 : span (checkState 7) 8 1224 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1232 : span (checkState 7) 8 1232 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1240 : span (checkState 7) 8 1240 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1248 : span (checkState 7) 8 1248 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1256 : span (checkState 7) 8 1256 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1264 : span (checkState 7) 8 1264 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1272 : span (checkState 7) 8 1272 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1280 : span (checkState 7) 8 1280 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1288 : span (checkState 7) 8 1288 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1296 : span (checkState 7) 8 1296 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1304 : span (checkState 7) 8 1304 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1312 : span (checkState 7) 8 1312 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1320 : span (checkState 7) 8 1320 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1328 : span (checkState 7) 8 1328 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1336 : span (checkState 7) 8 1336 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1344 : span (checkState 7) 8 1344 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1352 : span (checkState 7) 8 1352 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1360 : span (checkState 7) 8 1360 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1368 : span (checkState 7) 8 1368 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1376 : span (checkState 7) 8 1376 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1384 : span (checkState 7) 8 1384 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1392 : span (checkState 7) 8 1392 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1400 : span (checkState 7) 8 1400 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1408 : span (checkState 7) 8 1408 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1416 : span (checkState 7) 8 1416 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1424 : span (checkState 7) 8 1424 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1432 : span (checkState 7) 8 1432 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1440 : span (checkState 7) 8 1440 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1448 : span (checkState 7) 8 1448 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1456 : span (checkState 7) 8 1456 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1464 : span (checkState 7) 8 1464 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1472 : span (checkState 7) 8 1472 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1480 : span (checkState 7) 8 1480 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1488 : span (checkState 7) 8 1488 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1496 : span (checkState 7) 8 1496 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1504 : span (checkState 7) 8 1504 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1512 : span (checkState 7) 8 1512 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1520 : span (checkState 7) 8 1520 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1528 : span (checkState 7) 8 1528 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1536 : span (checkState 7) 8 1536 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1544 : span (checkState 7) 8 1544 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1552 : span (checkState 7) 8 1552 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1560 : span (checkState 7) 8 1560 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1568 : span (checkState 7) 8 1568 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1576 : span (checkState 7) 8 1576 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1584 : span (checkState 7) 8 1584 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1592 : span (checkState 7) 8 1592 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1600 : span (checkState 7) 8 1600 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1608 : span (checkState 7) 8 1608 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1616 : span (checkState 7) 8 1616 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1624 : span (checkState 7) 8 1624 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1632 : span (checkState 7) 8 1632 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1640 : span (checkState 7) 8 1640 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1648 : span (checkState 7) 8 1648 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1656 : span (checkState 7) 8 1656 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1664 : span (checkState 7) 8 1664 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1672 : span (checkState 7) 8 1672 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1680 : span (checkState 7) 8 1680 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1688 : span (checkState 7) 8 1688 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1696 : span (checkState 7) 8 1696 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1704 : span (checkState 7) 8 1704 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1712 : span (checkState 7) 8 1712 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1720 : span (checkState 7) 8 1720 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1728 : span (checkState 7) 8 1728 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1736 : span (checkState 7) 8 1736 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1744 : span (checkState 7) 8 1744 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1752 : span (checkState 7) 8 1752 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1760 : span (checkState 7) 8 1760 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1768 : span (checkState 7) 8 1768 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1776 : span (checkState 7) 8 1776 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1784 : span (checkState 7) 8 1784 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1792 : span (checkState 7) 8 1792 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1800 : span (checkState 7) 8 1800 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1808 : span (checkState 7) 8 1808 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1816 : span (checkState 7) 8 1816 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1824 : span (checkState 7) 8 1824 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1832 : span (checkState 7) 8 1832 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1840 : span (checkState 7) 8 1840 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1848 : span (checkState 7) 8 1848 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1856 : span (checkState 7) 8 1856 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1864 : span (checkState 7) 8 1864 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1872 : span (checkState 7) 8 1872 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1880 : span (checkState 7) 8 1880 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1888 : span (checkState 7) 8 1888 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1896 : span (checkState 7) 8 1896 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1904 : span (checkState 7) 8 1904 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1912 : span (checkState 7) 8 1912 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1920 : span (checkState 7) 8 1920 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1928 : span (checkState 7) 8 1928 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1936 : span (checkState 7) 8 1936 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1944 : span (checkState 7) 8 1944 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1952 : span (checkState 7) 8 1952 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1960 : span (checkState 7) 8 1960 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1968 : span (checkState 7) 8 1968 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1976 : span (checkState 7) 8 1976 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1984 : span (checkState 7) 8 1984 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_1992 : span (checkState 7) 8 1992 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2000 : span (checkState 7) 8 2000 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2008 : span (checkState 7) 8 2008 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2016 : span (checkState 7) 8 2016 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2024 : span (checkState 7) 8 2024 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2032 : span (checkState 7) 8 2032 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2040 : span (checkState 7) 8 2040 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2048 : span (checkState 7) 8 2048 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2056 : span (checkState 7) 8 2056 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2064 : span (checkState 7) 8 2064 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2072 : span (checkState 7) 8 2072 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2080 : span (checkState 7) 8 2080 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2088 : span (checkState 7) 8 2088 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2096 : span (checkState 7) 8 2096 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2104 : span (checkState 7) 8 2104 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2112 : span (checkState 7) 8 2112 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2120 : span (checkState 7) 8 2120 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2128 : span (checkState 7) 8 2128 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2136 : span (checkState 7) 8 2136 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2144 : span (checkState 7) 8 2144 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2152 : span (checkState 7) 8 2152 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2160 : span (checkState 7) 8 2160 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2168 : span (checkState 7) 8 2168 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2176 : span (checkState 7) 8 2176 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2184 : span (checkState 7) 8 2184 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2192 : span (checkState 7) 8 2192 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2200 : span (checkState 7) 8 2200 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2208 : span (checkState 7) 8 2208 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2216 : span (checkState 7) 8 2216 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2224 : span (checkState 7) 8 2224 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2232 : span (checkState 7) 8 2232 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2240 : span (checkState 7) 8 2240 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2248 : span (checkState 7) 8 2248 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2256 : span (checkState 7) 8 2256 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2264 : span (checkState 7) 8 2264 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2272 : span (checkState 7) 8 2272 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2280 : span (checkState 7) 8 2280 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2288 : span (checkState 7) 8 2288 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_7_2296 : span (checkState 7) 1 2296 = true := by decide +kernel

theorem combined_7_1_0 : span (checkState 7) 16 0 = true := @span_join (checkState 7) 8 0 8 block_7_0 block_7_8
theorem combined_7_1_1 : span (checkState 7) 16 16 = true := @span_join (checkState 7) 8 16 8 block_7_16 block_7_24
theorem combined_7_1_2 : span (checkState 7) 16 32 = true := @span_join (checkState 7) 8 32 8 block_7_32 block_7_40
theorem combined_7_1_3 : span (checkState 7) 16 48 = true := @span_join (checkState 7) 8 48 8 block_7_48 block_7_56
theorem combined_7_1_4 : span (checkState 7) 16 64 = true := @span_join (checkState 7) 8 64 8 block_7_64 block_7_72
theorem combined_7_1_5 : span (checkState 7) 16 80 = true := @span_join (checkState 7) 8 80 8 block_7_80 block_7_88
theorem combined_7_1_6 : span (checkState 7) 16 96 = true := @span_join (checkState 7) 8 96 8 block_7_96 block_7_104
theorem combined_7_1_7 : span (checkState 7) 16 112 = true := @span_join (checkState 7) 8 112 8 block_7_112 block_7_120
theorem combined_7_1_8 : span (checkState 7) 16 128 = true := @span_join (checkState 7) 8 128 8 block_7_128 block_7_136
theorem combined_7_1_9 : span (checkState 7) 16 144 = true := @span_join (checkState 7) 8 144 8 block_7_144 block_7_152
theorem combined_7_1_10 : span (checkState 7) 16 160 = true := @span_join (checkState 7) 8 160 8 block_7_160 block_7_168
theorem combined_7_1_11 : span (checkState 7) 16 176 = true := @span_join (checkState 7) 8 176 8 block_7_176 block_7_184
theorem combined_7_1_12 : span (checkState 7) 16 192 = true := @span_join (checkState 7) 8 192 8 block_7_192 block_7_200
theorem combined_7_1_13 : span (checkState 7) 16 208 = true := @span_join (checkState 7) 8 208 8 block_7_208 block_7_216
theorem combined_7_1_14 : span (checkState 7) 16 224 = true := @span_join (checkState 7) 8 224 8 block_7_224 block_7_232
theorem combined_7_1_15 : span (checkState 7) 16 240 = true := @span_join (checkState 7) 8 240 8 block_7_240 block_7_248
theorem combined_7_1_16 : span (checkState 7) 16 256 = true := @span_join (checkState 7) 8 256 8 block_7_256 block_7_264
theorem combined_7_1_17 : span (checkState 7) 16 272 = true := @span_join (checkState 7) 8 272 8 block_7_272 block_7_280
theorem combined_7_1_18 : span (checkState 7) 16 288 = true := @span_join (checkState 7) 8 288 8 block_7_288 block_7_296
theorem combined_7_1_19 : span (checkState 7) 16 304 = true := @span_join (checkState 7) 8 304 8 block_7_304 block_7_312
theorem combined_7_1_20 : span (checkState 7) 16 320 = true := @span_join (checkState 7) 8 320 8 block_7_320 block_7_328
theorem combined_7_1_21 : span (checkState 7) 16 336 = true := @span_join (checkState 7) 8 336 8 block_7_336 block_7_344
theorem combined_7_1_22 : span (checkState 7) 16 352 = true := @span_join (checkState 7) 8 352 8 block_7_352 block_7_360
theorem combined_7_1_23 : span (checkState 7) 16 368 = true := @span_join (checkState 7) 8 368 8 block_7_368 block_7_376
theorem combined_7_1_24 : span (checkState 7) 16 384 = true := @span_join (checkState 7) 8 384 8 block_7_384 block_7_392
theorem combined_7_1_25 : span (checkState 7) 16 400 = true := @span_join (checkState 7) 8 400 8 block_7_400 block_7_408
theorem combined_7_1_26 : span (checkState 7) 16 416 = true := @span_join (checkState 7) 8 416 8 block_7_416 block_7_424
theorem combined_7_1_27 : span (checkState 7) 16 432 = true := @span_join (checkState 7) 8 432 8 block_7_432 block_7_440
theorem combined_7_1_28 : span (checkState 7) 16 448 = true := @span_join (checkState 7) 8 448 8 block_7_448 block_7_456
theorem combined_7_1_29 : span (checkState 7) 16 464 = true := @span_join (checkState 7) 8 464 8 block_7_464 block_7_472
theorem combined_7_1_30 : span (checkState 7) 16 480 = true := @span_join (checkState 7) 8 480 8 block_7_480 block_7_488
theorem combined_7_1_31 : span (checkState 7) 16 496 = true := @span_join (checkState 7) 8 496 8 block_7_496 block_7_504
theorem combined_7_1_32 : span (checkState 7) 16 512 = true := @span_join (checkState 7) 8 512 8 block_7_512 block_7_520
theorem combined_7_1_33 : span (checkState 7) 16 528 = true := @span_join (checkState 7) 8 528 8 block_7_528 block_7_536
theorem combined_7_1_34 : span (checkState 7) 16 544 = true := @span_join (checkState 7) 8 544 8 block_7_544 block_7_552
theorem combined_7_1_35 : span (checkState 7) 16 560 = true := @span_join (checkState 7) 8 560 8 block_7_560 block_7_568
theorem combined_7_1_36 : span (checkState 7) 16 576 = true := @span_join (checkState 7) 8 576 8 block_7_576 block_7_584
theorem combined_7_1_37 : span (checkState 7) 16 592 = true := @span_join (checkState 7) 8 592 8 block_7_592 block_7_600
theorem combined_7_1_38 : span (checkState 7) 16 608 = true := @span_join (checkState 7) 8 608 8 block_7_608 block_7_616
theorem combined_7_1_39 : span (checkState 7) 16 624 = true := @span_join (checkState 7) 8 624 8 block_7_624 block_7_632
theorem combined_7_1_40 : span (checkState 7) 16 640 = true := @span_join (checkState 7) 8 640 8 block_7_640 block_7_648
theorem combined_7_1_41 : span (checkState 7) 16 656 = true := @span_join (checkState 7) 8 656 8 block_7_656 block_7_664
theorem combined_7_1_42 : span (checkState 7) 16 672 = true := @span_join (checkState 7) 8 672 8 block_7_672 block_7_680
theorem combined_7_1_43 : span (checkState 7) 16 688 = true := @span_join (checkState 7) 8 688 8 block_7_688 block_7_696
theorem combined_7_1_44 : span (checkState 7) 16 704 = true := @span_join (checkState 7) 8 704 8 block_7_704 block_7_712
theorem combined_7_1_45 : span (checkState 7) 16 720 = true := @span_join (checkState 7) 8 720 8 block_7_720 block_7_728
theorem combined_7_1_46 : span (checkState 7) 16 736 = true := @span_join (checkState 7) 8 736 8 block_7_736 block_7_744
theorem combined_7_1_47 : span (checkState 7) 16 752 = true := @span_join (checkState 7) 8 752 8 block_7_752 block_7_760
theorem combined_7_1_48 : span (checkState 7) 16 768 = true := @span_join (checkState 7) 8 768 8 block_7_768 block_7_776
theorem combined_7_1_49 : span (checkState 7) 16 784 = true := @span_join (checkState 7) 8 784 8 block_7_784 block_7_792
theorem combined_7_1_50 : span (checkState 7) 16 800 = true := @span_join (checkState 7) 8 800 8 block_7_800 block_7_808
theorem combined_7_1_51 : span (checkState 7) 16 816 = true := @span_join (checkState 7) 8 816 8 block_7_816 block_7_824
theorem combined_7_1_52 : span (checkState 7) 16 832 = true := @span_join (checkState 7) 8 832 8 block_7_832 block_7_840
theorem combined_7_1_53 : span (checkState 7) 16 848 = true := @span_join (checkState 7) 8 848 8 block_7_848 block_7_856
theorem combined_7_1_54 : span (checkState 7) 16 864 = true := @span_join (checkState 7) 8 864 8 block_7_864 block_7_872
theorem combined_7_1_55 : span (checkState 7) 16 880 = true := @span_join (checkState 7) 8 880 8 block_7_880 block_7_888
theorem combined_7_1_56 : span (checkState 7) 16 896 = true := @span_join (checkState 7) 8 896 8 block_7_896 block_7_904
theorem combined_7_1_57 : span (checkState 7) 16 912 = true := @span_join (checkState 7) 8 912 8 block_7_912 block_7_920
theorem combined_7_1_58 : span (checkState 7) 16 928 = true := @span_join (checkState 7) 8 928 8 block_7_928 block_7_936
theorem combined_7_1_59 : span (checkState 7) 16 944 = true := @span_join (checkState 7) 8 944 8 block_7_944 block_7_952
theorem combined_7_1_60 : span (checkState 7) 16 960 = true := @span_join (checkState 7) 8 960 8 block_7_960 block_7_968
theorem combined_7_1_61 : span (checkState 7) 16 976 = true := @span_join (checkState 7) 8 976 8 block_7_976 block_7_984
theorem combined_7_1_62 : span (checkState 7) 16 992 = true := @span_join (checkState 7) 8 992 8 block_7_992 block_7_1000
theorem combined_7_1_63 : span (checkState 7) 16 1008 = true := @span_join (checkState 7) 8 1008 8 block_7_1008 block_7_1016
theorem combined_7_1_64 : span (checkState 7) 16 1024 = true := @span_join (checkState 7) 8 1024 8 block_7_1024 block_7_1032
theorem combined_7_1_65 : span (checkState 7) 16 1040 = true := @span_join (checkState 7) 8 1040 8 block_7_1040 block_7_1048
theorem combined_7_1_66 : span (checkState 7) 16 1056 = true := @span_join (checkState 7) 8 1056 8 block_7_1056 block_7_1064
theorem combined_7_1_67 : span (checkState 7) 16 1072 = true := @span_join (checkState 7) 8 1072 8 block_7_1072 block_7_1080
theorem combined_7_1_68 : span (checkState 7) 16 1088 = true := @span_join (checkState 7) 8 1088 8 block_7_1088 block_7_1096
theorem combined_7_1_69 : span (checkState 7) 16 1104 = true := @span_join (checkState 7) 8 1104 8 block_7_1104 block_7_1112
theorem combined_7_1_70 : span (checkState 7) 16 1120 = true := @span_join (checkState 7) 8 1120 8 block_7_1120 block_7_1128
theorem combined_7_1_71 : span (checkState 7) 16 1136 = true := @span_join (checkState 7) 8 1136 8 block_7_1136 block_7_1144
theorem combined_7_1_72 : span (checkState 7) 16 1152 = true := @span_join (checkState 7) 8 1152 8 block_7_1152 block_7_1160
theorem combined_7_1_73 : span (checkState 7) 16 1168 = true := @span_join (checkState 7) 8 1168 8 block_7_1168 block_7_1176
theorem combined_7_1_74 : span (checkState 7) 16 1184 = true := @span_join (checkState 7) 8 1184 8 block_7_1184 block_7_1192
theorem combined_7_1_75 : span (checkState 7) 16 1200 = true := @span_join (checkState 7) 8 1200 8 block_7_1200 block_7_1208
theorem combined_7_1_76 : span (checkState 7) 16 1216 = true := @span_join (checkState 7) 8 1216 8 block_7_1216 block_7_1224
theorem combined_7_1_77 : span (checkState 7) 16 1232 = true := @span_join (checkState 7) 8 1232 8 block_7_1232 block_7_1240
theorem combined_7_1_78 : span (checkState 7) 16 1248 = true := @span_join (checkState 7) 8 1248 8 block_7_1248 block_7_1256
theorem combined_7_1_79 : span (checkState 7) 16 1264 = true := @span_join (checkState 7) 8 1264 8 block_7_1264 block_7_1272
theorem combined_7_1_80 : span (checkState 7) 16 1280 = true := @span_join (checkState 7) 8 1280 8 block_7_1280 block_7_1288
theorem combined_7_1_81 : span (checkState 7) 16 1296 = true := @span_join (checkState 7) 8 1296 8 block_7_1296 block_7_1304
theorem combined_7_1_82 : span (checkState 7) 16 1312 = true := @span_join (checkState 7) 8 1312 8 block_7_1312 block_7_1320
theorem combined_7_1_83 : span (checkState 7) 16 1328 = true := @span_join (checkState 7) 8 1328 8 block_7_1328 block_7_1336
theorem combined_7_1_84 : span (checkState 7) 16 1344 = true := @span_join (checkState 7) 8 1344 8 block_7_1344 block_7_1352
theorem combined_7_1_85 : span (checkState 7) 16 1360 = true := @span_join (checkState 7) 8 1360 8 block_7_1360 block_7_1368
theorem combined_7_1_86 : span (checkState 7) 16 1376 = true := @span_join (checkState 7) 8 1376 8 block_7_1376 block_7_1384
theorem combined_7_1_87 : span (checkState 7) 16 1392 = true := @span_join (checkState 7) 8 1392 8 block_7_1392 block_7_1400
theorem combined_7_1_88 : span (checkState 7) 16 1408 = true := @span_join (checkState 7) 8 1408 8 block_7_1408 block_7_1416
theorem combined_7_1_89 : span (checkState 7) 16 1424 = true := @span_join (checkState 7) 8 1424 8 block_7_1424 block_7_1432
theorem combined_7_1_90 : span (checkState 7) 16 1440 = true := @span_join (checkState 7) 8 1440 8 block_7_1440 block_7_1448
theorem combined_7_1_91 : span (checkState 7) 16 1456 = true := @span_join (checkState 7) 8 1456 8 block_7_1456 block_7_1464
theorem combined_7_1_92 : span (checkState 7) 16 1472 = true := @span_join (checkState 7) 8 1472 8 block_7_1472 block_7_1480
theorem combined_7_1_93 : span (checkState 7) 16 1488 = true := @span_join (checkState 7) 8 1488 8 block_7_1488 block_7_1496
theorem combined_7_1_94 : span (checkState 7) 16 1504 = true := @span_join (checkState 7) 8 1504 8 block_7_1504 block_7_1512
theorem combined_7_1_95 : span (checkState 7) 16 1520 = true := @span_join (checkState 7) 8 1520 8 block_7_1520 block_7_1528
theorem combined_7_1_96 : span (checkState 7) 16 1536 = true := @span_join (checkState 7) 8 1536 8 block_7_1536 block_7_1544
theorem combined_7_1_97 : span (checkState 7) 16 1552 = true := @span_join (checkState 7) 8 1552 8 block_7_1552 block_7_1560
theorem combined_7_1_98 : span (checkState 7) 16 1568 = true := @span_join (checkState 7) 8 1568 8 block_7_1568 block_7_1576
theorem combined_7_1_99 : span (checkState 7) 16 1584 = true := @span_join (checkState 7) 8 1584 8 block_7_1584 block_7_1592
theorem combined_7_1_100 : span (checkState 7) 16 1600 = true := @span_join (checkState 7) 8 1600 8 block_7_1600 block_7_1608
theorem combined_7_1_101 : span (checkState 7) 16 1616 = true := @span_join (checkState 7) 8 1616 8 block_7_1616 block_7_1624
theorem combined_7_1_102 : span (checkState 7) 16 1632 = true := @span_join (checkState 7) 8 1632 8 block_7_1632 block_7_1640
theorem combined_7_1_103 : span (checkState 7) 16 1648 = true := @span_join (checkState 7) 8 1648 8 block_7_1648 block_7_1656
theorem combined_7_1_104 : span (checkState 7) 16 1664 = true := @span_join (checkState 7) 8 1664 8 block_7_1664 block_7_1672
theorem combined_7_1_105 : span (checkState 7) 16 1680 = true := @span_join (checkState 7) 8 1680 8 block_7_1680 block_7_1688
theorem combined_7_1_106 : span (checkState 7) 16 1696 = true := @span_join (checkState 7) 8 1696 8 block_7_1696 block_7_1704
theorem combined_7_1_107 : span (checkState 7) 16 1712 = true := @span_join (checkState 7) 8 1712 8 block_7_1712 block_7_1720
theorem combined_7_1_108 : span (checkState 7) 16 1728 = true := @span_join (checkState 7) 8 1728 8 block_7_1728 block_7_1736
theorem combined_7_1_109 : span (checkState 7) 16 1744 = true := @span_join (checkState 7) 8 1744 8 block_7_1744 block_7_1752
theorem combined_7_1_110 : span (checkState 7) 16 1760 = true := @span_join (checkState 7) 8 1760 8 block_7_1760 block_7_1768
theorem combined_7_1_111 : span (checkState 7) 16 1776 = true := @span_join (checkState 7) 8 1776 8 block_7_1776 block_7_1784
theorem combined_7_1_112 : span (checkState 7) 16 1792 = true := @span_join (checkState 7) 8 1792 8 block_7_1792 block_7_1800
theorem combined_7_1_113 : span (checkState 7) 16 1808 = true := @span_join (checkState 7) 8 1808 8 block_7_1808 block_7_1816
theorem combined_7_1_114 : span (checkState 7) 16 1824 = true := @span_join (checkState 7) 8 1824 8 block_7_1824 block_7_1832
theorem combined_7_1_115 : span (checkState 7) 16 1840 = true := @span_join (checkState 7) 8 1840 8 block_7_1840 block_7_1848
theorem combined_7_1_116 : span (checkState 7) 16 1856 = true := @span_join (checkState 7) 8 1856 8 block_7_1856 block_7_1864
theorem combined_7_1_117 : span (checkState 7) 16 1872 = true := @span_join (checkState 7) 8 1872 8 block_7_1872 block_7_1880
theorem combined_7_1_118 : span (checkState 7) 16 1888 = true := @span_join (checkState 7) 8 1888 8 block_7_1888 block_7_1896
theorem combined_7_1_119 : span (checkState 7) 16 1904 = true := @span_join (checkState 7) 8 1904 8 block_7_1904 block_7_1912
theorem combined_7_1_120 : span (checkState 7) 16 1920 = true := @span_join (checkState 7) 8 1920 8 block_7_1920 block_7_1928
theorem combined_7_1_121 : span (checkState 7) 16 1936 = true := @span_join (checkState 7) 8 1936 8 block_7_1936 block_7_1944
theorem combined_7_1_122 : span (checkState 7) 16 1952 = true := @span_join (checkState 7) 8 1952 8 block_7_1952 block_7_1960
theorem combined_7_1_123 : span (checkState 7) 16 1968 = true := @span_join (checkState 7) 8 1968 8 block_7_1968 block_7_1976
theorem combined_7_1_124 : span (checkState 7) 16 1984 = true := @span_join (checkState 7) 8 1984 8 block_7_1984 block_7_1992
theorem combined_7_1_125 : span (checkState 7) 16 2000 = true := @span_join (checkState 7) 8 2000 8 block_7_2000 block_7_2008
theorem combined_7_1_126 : span (checkState 7) 16 2016 = true := @span_join (checkState 7) 8 2016 8 block_7_2016 block_7_2024
theorem combined_7_1_127 : span (checkState 7) 16 2032 = true := @span_join (checkState 7) 8 2032 8 block_7_2032 block_7_2040
theorem combined_7_1_128 : span (checkState 7) 16 2048 = true := @span_join (checkState 7) 8 2048 8 block_7_2048 block_7_2056
theorem combined_7_1_129 : span (checkState 7) 16 2064 = true := @span_join (checkState 7) 8 2064 8 block_7_2064 block_7_2072
theorem combined_7_1_130 : span (checkState 7) 16 2080 = true := @span_join (checkState 7) 8 2080 8 block_7_2080 block_7_2088
theorem combined_7_1_131 : span (checkState 7) 16 2096 = true := @span_join (checkState 7) 8 2096 8 block_7_2096 block_7_2104
theorem combined_7_1_132 : span (checkState 7) 16 2112 = true := @span_join (checkState 7) 8 2112 8 block_7_2112 block_7_2120
theorem combined_7_1_133 : span (checkState 7) 16 2128 = true := @span_join (checkState 7) 8 2128 8 block_7_2128 block_7_2136
theorem combined_7_1_134 : span (checkState 7) 16 2144 = true := @span_join (checkState 7) 8 2144 8 block_7_2144 block_7_2152
theorem combined_7_1_135 : span (checkState 7) 16 2160 = true := @span_join (checkState 7) 8 2160 8 block_7_2160 block_7_2168
theorem combined_7_1_136 : span (checkState 7) 16 2176 = true := @span_join (checkState 7) 8 2176 8 block_7_2176 block_7_2184
theorem combined_7_1_137 : span (checkState 7) 16 2192 = true := @span_join (checkState 7) 8 2192 8 block_7_2192 block_7_2200
theorem combined_7_1_138 : span (checkState 7) 16 2208 = true := @span_join (checkState 7) 8 2208 8 block_7_2208 block_7_2216
theorem combined_7_1_139 : span (checkState 7) 16 2224 = true := @span_join (checkState 7) 8 2224 8 block_7_2224 block_7_2232
theorem combined_7_1_140 : span (checkState 7) 16 2240 = true := @span_join (checkState 7) 8 2240 8 block_7_2240 block_7_2248
theorem combined_7_1_141 : span (checkState 7) 16 2256 = true := @span_join (checkState 7) 8 2256 8 block_7_2256 block_7_2264
theorem combined_7_1_142 : span (checkState 7) 16 2272 = true := @span_join (checkState 7) 8 2272 8 block_7_2272 block_7_2280
theorem combined_7_1_143 : span (checkState 7) 9 2288 = true := @span_join (checkState 7) 8 2288 1 block_7_2288 block_7_2296
theorem combined_7_2_0 : span (checkState 7) 32 0 = true := @span_join (checkState 7) 16 0 16 combined_7_1_0 combined_7_1_1
theorem combined_7_2_1 : span (checkState 7) 32 32 = true := @span_join (checkState 7) 16 32 16 combined_7_1_2 combined_7_1_3
theorem combined_7_2_2 : span (checkState 7) 32 64 = true := @span_join (checkState 7) 16 64 16 combined_7_1_4 combined_7_1_5
theorem combined_7_2_3 : span (checkState 7) 32 96 = true := @span_join (checkState 7) 16 96 16 combined_7_1_6 combined_7_1_7
theorem combined_7_2_4 : span (checkState 7) 32 128 = true := @span_join (checkState 7) 16 128 16 combined_7_1_8 combined_7_1_9
theorem combined_7_2_5 : span (checkState 7) 32 160 = true := @span_join (checkState 7) 16 160 16 combined_7_1_10 combined_7_1_11
theorem combined_7_2_6 : span (checkState 7) 32 192 = true := @span_join (checkState 7) 16 192 16 combined_7_1_12 combined_7_1_13
theorem combined_7_2_7 : span (checkState 7) 32 224 = true := @span_join (checkState 7) 16 224 16 combined_7_1_14 combined_7_1_15
theorem combined_7_2_8 : span (checkState 7) 32 256 = true := @span_join (checkState 7) 16 256 16 combined_7_1_16 combined_7_1_17
theorem combined_7_2_9 : span (checkState 7) 32 288 = true := @span_join (checkState 7) 16 288 16 combined_7_1_18 combined_7_1_19
theorem combined_7_2_10 : span (checkState 7) 32 320 = true := @span_join (checkState 7) 16 320 16 combined_7_1_20 combined_7_1_21
theorem combined_7_2_11 : span (checkState 7) 32 352 = true := @span_join (checkState 7) 16 352 16 combined_7_1_22 combined_7_1_23
theorem combined_7_2_12 : span (checkState 7) 32 384 = true := @span_join (checkState 7) 16 384 16 combined_7_1_24 combined_7_1_25
theorem combined_7_2_13 : span (checkState 7) 32 416 = true := @span_join (checkState 7) 16 416 16 combined_7_1_26 combined_7_1_27
theorem combined_7_2_14 : span (checkState 7) 32 448 = true := @span_join (checkState 7) 16 448 16 combined_7_1_28 combined_7_1_29
theorem combined_7_2_15 : span (checkState 7) 32 480 = true := @span_join (checkState 7) 16 480 16 combined_7_1_30 combined_7_1_31
theorem combined_7_2_16 : span (checkState 7) 32 512 = true := @span_join (checkState 7) 16 512 16 combined_7_1_32 combined_7_1_33
theorem combined_7_2_17 : span (checkState 7) 32 544 = true := @span_join (checkState 7) 16 544 16 combined_7_1_34 combined_7_1_35
theorem combined_7_2_18 : span (checkState 7) 32 576 = true := @span_join (checkState 7) 16 576 16 combined_7_1_36 combined_7_1_37
theorem combined_7_2_19 : span (checkState 7) 32 608 = true := @span_join (checkState 7) 16 608 16 combined_7_1_38 combined_7_1_39
theorem combined_7_2_20 : span (checkState 7) 32 640 = true := @span_join (checkState 7) 16 640 16 combined_7_1_40 combined_7_1_41
theorem combined_7_2_21 : span (checkState 7) 32 672 = true := @span_join (checkState 7) 16 672 16 combined_7_1_42 combined_7_1_43
theorem combined_7_2_22 : span (checkState 7) 32 704 = true := @span_join (checkState 7) 16 704 16 combined_7_1_44 combined_7_1_45
theorem combined_7_2_23 : span (checkState 7) 32 736 = true := @span_join (checkState 7) 16 736 16 combined_7_1_46 combined_7_1_47
theorem combined_7_2_24 : span (checkState 7) 32 768 = true := @span_join (checkState 7) 16 768 16 combined_7_1_48 combined_7_1_49
theorem combined_7_2_25 : span (checkState 7) 32 800 = true := @span_join (checkState 7) 16 800 16 combined_7_1_50 combined_7_1_51
theorem combined_7_2_26 : span (checkState 7) 32 832 = true := @span_join (checkState 7) 16 832 16 combined_7_1_52 combined_7_1_53
theorem combined_7_2_27 : span (checkState 7) 32 864 = true := @span_join (checkState 7) 16 864 16 combined_7_1_54 combined_7_1_55
theorem combined_7_2_28 : span (checkState 7) 32 896 = true := @span_join (checkState 7) 16 896 16 combined_7_1_56 combined_7_1_57
theorem combined_7_2_29 : span (checkState 7) 32 928 = true := @span_join (checkState 7) 16 928 16 combined_7_1_58 combined_7_1_59
theorem combined_7_2_30 : span (checkState 7) 32 960 = true := @span_join (checkState 7) 16 960 16 combined_7_1_60 combined_7_1_61
theorem combined_7_2_31 : span (checkState 7) 32 992 = true := @span_join (checkState 7) 16 992 16 combined_7_1_62 combined_7_1_63
theorem combined_7_2_32 : span (checkState 7) 32 1024 = true := @span_join (checkState 7) 16 1024 16 combined_7_1_64 combined_7_1_65
theorem combined_7_2_33 : span (checkState 7) 32 1056 = true := @span_join (checkState 7) 16 1056 16 combined_7_1_66 combined_7_1_67
theorem combined_7_2_34 : span (checkState 7) 32 1088 = true := @span_join (checkState 7) 16 1088 16 combined_7_1_68 combined_7_1_69
theorem combined_7_2_35 : span (checkState 7) 32 1120 = true := @span_join (checkState 7) 16 1120 16 combined_7_1_70 combined_7_1_71
theorem combined_7_2_36 : span (checkState 7) 32 1152 = true := @span_join (checkState 7) 16 1152 16 combined_7_1_72 combined_7_1_73
theorem combined_7_2_37 : span (checkState 7) 32 1184 = true := @span_join (checkState 7) 16 1184 16 combined_7_1_74 combined_7_1_75
theorem combined_7_2_38 : span (checkState 7) 32 1216 = true := @span_join (checkState 7) 16 1216 16 combined_7_1_76 combined_7_1_77
theorem combined_7_2_39 : span (checkState 7) 32 1248 = true := @span_join (checkState 7) 16 1248 16 combined_7_1_78 combined_7_1_79
theorem combined_7_2_40 : span (checkState 7) 32 1280 = true := @span_join (checkState 7) 16 1280 16 combined_7_1_80 combined_7_1_81
theorem combined_7_2_41 : span (checkState 7) 32 1312 = true := @span_join (checkState 7) 16 1312 16 combined_7_1_82 combined_7_1_83
theorem combined_7_2_42 : span (checkState 7) 32 1344 = true := @span_join (checkState 7) 16 1344 16 combined_7_1_84 combined_7_1_85
theorem combined_7_2_43 : span (checkState 7) 32 1376 = true := @span_join (checkState 7) 16 1376 16 combined_7_1_86 combined_7_1_87
theorem combined_7_2_44 : span (checkState 7) 32 1408 = true := @span_join (checkState 7) 16 1408 16 combined_7_1_88 combined_7_1_89
theorem combined_7_2_45 : span (checkState 7) 32 1440 = true := @span_join (checkState 7) 16 1440 16 combined_7_1_90 combined_7_1_91
theorem combined_7_2_46 : span (checkState 7) 32 1472 = true := @span_join (checkState 7) 16 1472 16 combined_7_1_92 combined_7_1_93
theorem combined_7_2_47 : span (checkState 7) 32 1504 = true := @span_join (checkState 7) 16 1504 16 combined_7_1_94 combined_7_1_95
theorem combined_7_2_48 : span (checkState 7) 32 1536 = true := @span_join (checkState 7) 16 1536 16 combined_7_1_96 combined_7_1_97
theorem combined_7_2_49 : span (checkState 7) 32 1568 = true := @span_join (checkState 7) 16 1568 16 combined_7_1_98 combined_7_1_99
theorem combined_7_2_50 : span (checkState 7) 32 1600 = true := @span_join (checkState 7) 16 1600 16 combined_7_1_100 combined_7_1_101
theorem combined_7_2_51 : span (checkState 7) 32 1632 = true := @span_join (checkState 7) 16 1632 16 combined_7_1_102 combined_7_1_103
theorem combined_7_2_52 : span (checkState 7) 32 1664 = true := @span_join (checkState 7) 16 1664 16 combined_7_1_104 combined_7_1_105
theorem combined_7_2_53 : span (checkState 7) 32 1696 = true := @span_join (checkState 7) 16 1696 16 combined_7_1_106 combined_7_1_107
theorem combined_7_2_54 : span (checkState 7) 32 1728 = true := @span_join (checkState 7) 16 1728 16 combined_7_1_108 combined_7_1_109
theorem combined_7_2_55 : span (checkState 7) 32 1760 = true := @span_join (checkState 7) 16 1760 16 combined_7_1_110 combined_7_1_111
theorem combined_7_2_56 : span (checkState 7) 32 1792 = true := @span_join (checkState 7) 16 1792 16 combined_7_1_112 combined_7_1_113
theorem combined_7_2_57 : span (checkState 7) 32 1824 = true := @span_join (checkState 7) 16 1824 16 combined_7_1_114 combined_7_1_115
theorem combined_7_2_58 : span (checkState 7) 32 1856 = true := @span_join (checkState 7) 16 1856 16 combined_7_1_116 combined_7_1_117
theorem combined_7_2_59 : span (checkState 7) 32 1888 = true := @span_join (checkState 7) 16 1888 16 combined_7_1_118 combined_7_1_119
theorem combined_7_2_60 : span (checkState 7) 32 1920 = true := @span_join (checkState 7) 16 1920 16 combined_7_1_120 combined_7_1_121
theorem combined_7_2_61 : span (checkState 7) 32 1952 = true := @span_join (checkState 7) 16 1952 16 combined_7_1_122 combined_7_1_123
theorem combined_7_2_62 : span (checkState 7) 32 1984 = true := @span_join (checkState 7) 16 1984 16 combined_7_1_124 combined_7_1_125
theorem combined_7_2_63 : span (checkState 7) 32 2016 = true := @span_join (checkState 7) 16 2016 16 combined_7_1_126 combined_7_1_127
theorem combined_7_2_64 : span (checkState 7) 32 2048 = true := @span_join (checkState 7) 16 2048 16 combined_7_1_128 combined_7_1_129
theorem combined_7_2_65 : span (checkState 7) 32 2080 = true := @span_join (checkState 7) 16 2080 16 combined_7_1_130 combined_7_1_131
theorem combined_7_2_66 : span (checkState 7) 32 2112 = true := @span_join (checkState 7) 16 2112 16 combined_7_1_132 combined_7_1_133
theorem combined_7_2_67 : span (checkState 7) 32 2144 = true := @span_join (checkState 7) 16 2144 16 combined_7_1_134 combined_7_1_135
theorem combined_7_2_68 : span (checkState 7) 32 2176 = true := @span_join (checkState 7) 16 2176 16 combined_7_1_136 combined_7_1_137
theorem combined_7_2_69 : span (checkState 7) 32 2208 = true := @span_join (checkState 7) 16 2208 16 combined_7_1_138 combined_7_1_139
theorem combined_7_2_70 : span (checkState 7) 32 2240 = true := @span_join (checkState 7) 16 2240 16 combined_7_1_140 combined_7_1_141
theorem combined_7_2_71 : span (checkState 7) 25 2272 = true := @span_join (checkState 7) 16 2272 9 combined_7_1_142 combined_7_1_143
theorem combined_7_4_0 : span (checkState 7) 64 0 = true := @span_join (checkState 7) 32 0 32 combined_7_2_0 combined_7_2_1
theorem combined_7_4_1 : span (checkState 7) 64 64 = true := @span_join (checkState 7) 32 64 32 combined_7_2_2 combined_7_2_3
theorem combined_7_4_2 : span (checkState 7) 64 128 = true := @span_join (checkState 7) 32 128 32 combined_7_2_4 combined_7_2_5
theorem combined_7_4_3 : span (checkState 7) 64 192 = true := @span_join (checkState 7) 32 192 32 combined_7_2_6 combined_7_2_7
theorem combined_7_4_4 : span (checkState 7) 64 256 = true := @span_join (checkState 7) 32 256 32 combined_7_2_8 combined_7_2_9
theorem combined_7_4_5 : span (checkState 7) 64 320 = true := @span_join (checkState 7) 32 320 32 combined_7_2_10 combined_7_2_11
theorem combined_7_4_6 : span (checkState 7) 64 384 = true := @span_join (checkState 7) 32 384 32 combined_7_2_12 combined_7_2_13
theorem combined_7_4_7 : span (checkState 7) 64 448 = true := @span_join (checkState 7) 32 448 32 combined_7_2_14 combined_7_2_15
theorem combined_7_4_8 : span (checkState 7) 64 512 = true := @span_join (checkState 7) 32 512 32 combined_7_2_16 combined_7_2_17
theorem combined_7_4_9 : span (checkState 7) 64 576 = true := @span_join (checkState 7) 32 576 32 combined_7_2_18 combined_7_2_19
theorem combined_7_4_10 : span (checkState 7) 64 640 = true := @span_join (checkState 7) 32 640 32 combined_7_2_20 combined_7_2_21
theorem combined_7_4_11 : span (checkState 7) 64 704 = true := @span_join (checkState 7) 32 704 32 combined_7_2_22 combined_7_2_23
theorem combined_7_4_12 : span (checkState 7) 64 768 = true := @span_join (checkState 7) 32 768 32 combined_7_2_24 combined_7_2_25
theorem combined_7_4_13 : span (checkState 7) 64 832 = true := @span_join (checkState 7) 32 832 32 combined_7_2_26 combined_7_2_27
theorem combined_7_4_14 : span (checkState 7) 64 896 = true := @span_join (checkState 7) 32 896 32 combined_7_2_28 combined_7_2_29
theorem combined_7_4_15 : span (checkState 7) 64 960 = true := @span_join (checkState 7) 32 960 32 combined_7_2_30 combined_7_2_31
theorem combined_7_4_16 : span (checkState 7) 64 1024 = true := @span_join (checkState 7) 32 1024 32 combined_7_2_32 combined_7_2_33
theorem combined_7_4_17 : span (checkState 7) 64 1088 = true := @span_join (checkState 7) 32 1088 32 combined_7_2_34 combined_7_2_35
theorem combined_7_4_18 : span (checkState 7) 64 1152 = true := @span_join (checkState 7) 32 1152 32 combined_7_2_36 combined_7_2_37
theorem combined_7_4_19 : span (checkState 7) 64 1216 = true := @span_join (checkState 7) 32 1216 32 combined_7_2_38 combined_7_2_39
theorem combined_7_4_20 : span (checkState 7) 64 1280 = true := @span_join (checkState 7) 32 1280 32 combined_7_2_40 combined_7_2_41
theorem combined_7_4_21 : span (checkState 7) 64 1344 = true := @span_join (checkState 7) 32 1344 32 combined_7_2_42 combined_7_2_43
theorem combined_7_4_22 : span (checkState 7) 64 1408 = true := @span_join (checkState 7) 32 1408 32 combined_7_2_44 combined_7_2_45
theorem combined_7_4_23 : span (checkState 7) 64 1472 = true := @span_join (checkState 7) 32 1472 32 combined_7_2_46 combined_7_2_47
theorem combined_7_4_24 : span (checkState 7) 64 1536 = true := @span_join (checkState 7) 32 1536 32 combined_7_2_48 combined_7_2_49
theorem combined_7_4_25 : span (checkState 7) 64 1600 = true := @span_join (checkState 7) 32 1600 32 combined_7_2_50 combined_7_2_51
theorem combined_7_4_26 : span (checkState 7) 64 1664 = true := @span_join (checkState 7) 32 1664 32 combined_7_2_52 combined_7_2_53
theorem combined_7_4_27 : span (checkState 7) 64 1728 = true := @span_join (checkState 7) 32 1728 32 combined_7_2_54 combined_7_2_55
theorem combined_7_4_28 : span (checkState 7) 64 1792 = true := @span_join (checkState 7) 32 1792 32 combined_7_2_56 combined_7_2_57
theorem combined_7_4_29 : span (checkState 7) 64 1856 = true := @span_join (checkState 7) 32 1856 32 combined_7_2_58 combined_7_2_59
theorem combined_7_4_30 : span (checkState 7) 64 1920 = true := @span_join (checkState 7) 32 1920 32 combined_7_2_60 combined_7_2_61
theorem combined_7_4_31 : span (checkState 7) 64 1984 = true := @span_join (checkState 7) 32 1984 32 combined_7_2_62 combined_7_2_63
theorem combined_7_4_32 : span (checkState 7) 64 2048 = true := @span_join (checkState 7) 32 2048 32 combined_7_2_64 combined_7_2_65
theorem combined_7_4_33 : span (checkState 7) 64 2112 = true := @span_join (checkState 7) 32 2112 32 combined_7_2_66 combined_7_2_67
theorem combined_7_4_34 : span (checkState 7) 64 2176 = true := @span_join (checkState 7) 32 2176 32 combined_7_2_68 combined_7_2_69
theorem combined_7_4_35 : span (checkState 7) 57 2240 = true := @span_join (checkState 7) 32 2240 25 combined_7_2_70 combined_7_2_71
theorem combined_7_8_0 : span (checkState 7) 128 0 = true := @span_join (checkState 7) 64 0 64 combined_7_4_0 combined_7_4_1
theorem combined_7_8_1 : span (checkState 7) 128 128 = true := @span_join (checkState 7) 64 128 64 combined_7_4_2 combined_7_4_3
theorem combined_7_8_2 : span (checkState 7) 128 256 = true := @span_join (checkState 7) 64 256 64 combined_7_4_4 combined_7_4_5
theorem combined_7_8_3 : span (checkState 7) 128 384 = true := @span_join (checkState 7) 64 384 64 combined_7_4_6 combined_7_4_7
theorem combined_7_8_4 : span (checkState 7) 128 512 = true := @span_join (checkState 7) 64 512 64 combined_7_4_8 combined_7_4_9
theorem combined_7_8_5 : span (checkState 7) 128 640 = true := @span_join (checkState 7) 64 640 64 combined_7_4_10 combined_7_4_11
theorem combined_7_8_6 : span (checkState 7) 128 768 = true := @span_join (checkState 7) 64 768 64 combined_7_4_12 combined_7_4_13
theorem combined_7_8_7 : span (checkState 7) 128 896 = true := @span_join (checkState 7) 64 896 64 combined_7_4_14 combined_7_4_15
theorem combined_7_8_8 : span (checkState 7) 128 1024 = true := @span_join (checkState 7) 64 1024 64 combined_7_4_16 combined_7_4_17
theorem combined_7_8_9 : span (checkState 7) 128 1152 = true := @span_join (checkState 7) 64 1152 64 combined_7_4_18 combined_7_4_19
theorem combined_7_8_10 : span (checkState 7) 128 1280 = true := @span_join (checkState 7) 64 1280 64 combined_7_4_20 combined_7_4_21
theorem combined_7_8_11 : span (checkState 7) 128 1408 = true := @span_join (checkState 7) 64 1408 64 combined_7_4_22 combined_7_4_23
theorem combined_7_8_12 : span (checkState 7) 128 1536 = true := @span_join (checkState 7) 64 1536 64 combined_7_4_24 combined_7_4_25
theorem combined_7_8_13 : span (checkState 7) 128 1664 = true := @span_join (checkState 7) 64 1664 64 combined_7_4_26 combined_7_4_27
theorem combined_7_8_14 : span (checkState 7) 128 1792 = true := @span_join (checkState 7) 64 1792 64 combined_7_4_28 combined_7_4_29
theorem combined_7_8_15 : span (checkState 7) 128 1920 = true := @span_join (checkState 7) 64 1920 64 combined_7_4_30 combined_7_4_31
theorem combined_7_8_16 : span (checkState 7) 128 2048 = true := @span_join (checkState 7) 64 2048 64 combined_7_4_32 combined_7_4_33
theorem combined_7_8_17 : span (checkState 7) 121 2176 = true := @span_join (checkState 7) 64 2176 57 combined_7_4_34 combined_7_4_35
theorem combined_7_16_0 : span (checkState 7) 256 0 = true := @span_join (checkState 7) 128 0 128 combined_7_8_0 combined_7_8_1
theorem combined_7_16_1 : span (checkState 7) 256 256 = true := @span_join (checkState 7) 128 256 128 combined_7_8_2 combined_7_8_3
theorem combined_7_16_2 : span (checkState 7) 256 512 = true := @span_join (checkState 7) 128 512 128 combined_7_8_4 combined_7_8_5
theorem combined_7_16_3 : span (checkState 7) 256 768 = true := @span_join (checkState 7) 128 768 128 combined_7_8_6 combined_7_8_7
theorem combined_7_16_4 : span (checkState 7) 256 1024 = true := @span_join (checkState 7) 128 1024 128 combined_7_8_8 combined_7_8_9
theorem combined_7_16_5 : span (checkState 7) 256 1280 = true := @span_join (checkState 7) 128 1280 128 combined_7_8_10 combined_7_8_11
theorem combined_7_16_6 : span (checkState 7) 256 1536 = true := @span_join (checkState 7) 128 1536 128 combined_7_8_12 combined_7_8_13
theorem combined_7_16_7 : span (checkState 7) 256 1792 = true := @span_join (checkState 7) 128 1792 128 combined_7_8_14 combined_7_8_15
theorem combined_7_16_8 : span (checkState 7) 249 2048 = true := @span_join (checkState 7) 128 2048 121 combined_7_8_16 combined_7_8_17
theorem combined_7_32_0 : span (checkState 7) 512 0 = true := @span_join (checkState 7) 256 0 256 combined_7_16_0 combined_7_16_1
theorem combined_7_32_1 : span (checkState 7) 512 512 = true := @span_join (checkState 7) 256 512 256 combined_7_16_2 combined_7_16_3
theorem combined_7_32_2 : span (checkState 7) 512 1024 = true := @span_join (checkState 7) 256 1024 256 combined_7_16_4 combined_7_16_5
theorem combined_7_32_3 : span (checkState 7) 512 1536 = true := @span_join (checkState 7) 256 1536 256 combined_7_16_6 combined_7_16_7
theorem combined_7_64_0 : span (checkState 7) 1024 0 = true := @span_join (checkState 7) 512 0 512 combined_7_32_0 combined_7_32_1
theorem combined_7_64_1 : span (checkState 7) 1024 1024 = true := @span_join (checkState 7) 512 1024 512 combined_7_32_2 combined_7_32_3
theorem combined_7_128_0 : span (checkState 7) 2048 0 = true := @span_join (checkState 7) 1024 0 1024 combined_7_64_0 combined_7_64_1
theorem combined_7_256_0 : span (checkState 7) 2297 0 = true := @span_join (checkState 7) 2048 0 249 combined_7_128_0 combined_7_16_8
theorem all_7 : span (checkState 7) 2297 0 = true := combined_7_256_0

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_0 : span (checkState 8) 8 0 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_8 : span (checkState 8) 8 8 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_16 : span (checkState 8) 8 16 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_24 : span (checkState 8) 8 24 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_32 : span (checkState 8) 8 32 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_40 : span (checkState 8) 8 40 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_48 : span (checkState 8) 8 48 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_56 : span (checkState 8) 8 56 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_64 : span (checkState 8) 8 64 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_72 : span (checkState 8) 8 72 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_80 : span (checkState 8) 8 80 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_88 : span (checkState 8) 8 88 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_96 : span (checkState 8) 8 96 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_104 : span (checkState 8) 8 104 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_112 : span (checkState 8) 8 112 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_120 : span (checkState 8) 8 120 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_128 : span (checkState 8) 8 128 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_136 : span (checkState 8) 8 136 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_144 : span (checkState 8) 8 144 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_152 : span (checkState 8) 8 152 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_160 : span (checkState 8) 8 160 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_168 : span (checkState 8) 8 168 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_176 : span (checkState 8) 8 176 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_184 : span (checkState 8) 8 184 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_192 : span (checkState 8) 8 192 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_200 : span (checkState 8) 8 200 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_208 : span (checkState 8) 8 208 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_216 : span (checkState 8) 8 216 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_224 : span (checkState 8) 8 224 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_232 : span (checkState 8) 8 232 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_240 : span (checkState 8) 8 240 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_248 : span (checkState 8) 8 248 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_256 : span (checkState 8) 8 256 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_264 : span (checkState 8) 8 264 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_272 : span (checkState 8) 8 272 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_280 : span (checkState 8) 8 280 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_288 : span (checkState 8) 8 288 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_296 : span (checkState 8) 8 296 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_304 : span (checkState 8) 8 304 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_312 : span (checkState 8) 8 312 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_320 : span (checkState 8) 8 320 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_328 : span (checkState 8) 8 328 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_336 : span (checkState 8) 8 336 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_344 : span (checkState 8) 8 344 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_352 : span (checkState 8) 8 352 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_360 : span (checkState 8) 8 360 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_368 : span (checkState 8) 8 368 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_376 : span (checkState 8) 8 376 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_384 : span (checkState 8) 8 384 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_392 : span (checkState 8) 8 392 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_400 : span (checkState 8) 8 400 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_408 : span (checkState 8) 8 408 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_416 : span (checkState 8) 8 416 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_424 : span (checkState 8) 8 424 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_432 : span (checkState 8) 8 432 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_440 : span (checkState 8) 8 440 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_448 : span (checkState 8) 8 448 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_456 : span (checkState 8) 8 456 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_464 : span (checkState 8) 8 464 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_472 : span (checkState 8) 8 472 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_480 : span (checkState 8) 8 480 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_488 : span (checkState 8) 8 488 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_496 : span (checkState 8) 8 496 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_504 : span (checkState 8) 8 504 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_512 : span (checkState 8) 8 512 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_520 : span (checkState 8) 8 520 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_528 : span (checkState 8) 8 528 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_536 : span (checkState 8) 8 536 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_544 : span (checkState 8) 8 544 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_552 : span (checkState 8) 8 552 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_560 : span (checkState 8) 8 560 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_568 : span (checkState 8) 8 568 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_576 : span (checkState 8) 8 576 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_584 : span (checkState 8) 8 584 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_592 : span (checkState 8) 8 592 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_600 : span (checkState 8) 8 600 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_608 : span (checkState 8) 8 608 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_616 : span (checkState 8) 8 616 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_624 : span (checkState 8) 8 624 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_632 : span (checkState 8) 8 632 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_640 : span (checkState 8) 8 640 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_648 : span (checkState 8) 8 648 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_656 : span (checkState 8) 8 656 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_664 : span (checkState 8) 8 664 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_672 : span (checkState 8) 8 672 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_680 : span (checkState 8) 8 680 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_688 : span (checkState 8) 8 688 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_696 : span (checkState 8) 8 696 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_704 : span (checkState 8) 8 704 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_712 : span (checkState 8) 8 712 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_720 : span (checkState 8) 8 720 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_728 : span (checkState 8) 8 728 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_736 : span (checkState 8) 8 736 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_744 : span (checkState 8) 8 744 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_752 : span (checkState 8) 8 752 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_760 : span (checkState 8) 8 760 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_768 : span (checkState 8) 8 768 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_776 : span (checkState 8) 8 776 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_784 : span (checkState 8) 8 784 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_792 : span (checkState 8) 8 792 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_800 : span (checkState 8) 8 800 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_808 : span (checkState 8) 8 808 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_816 : span (checkState 8) 8 816 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_824 : span (checkState 8) 8 824 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_832 : span (checkState 8) 8 832 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_840 : span (checkState 8) 8 840 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_848 : span (checkState 8) 8 848 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_856 : span (checkState 8) 8 856 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_864 : span (checkState 8) 8 864 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_872 : span (checkState 8) 8 872 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_880 : span (checkState 8) 8 880 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_888 : span (checkState 8) 8 888 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_896 : span (checkState 8) 8 896 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_904 : span (checkState 8) 8 904 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_912 : span (checkState 8) 8 912 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_920 : span (checkState 8) 8 920 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_928 : span (checkState 8) 8 928 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_936 : span (checkState 8) 8 936 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_944 : span (checkState 8) 8 944 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_952 : span (checkState 8) 8 952 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_960 : span (checkState 8) 8 960 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_968 : span (checkState 8) 8 968 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_976 : span (checkState 8) 8 976 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_984 : span (checkState 8) 8 984 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_992 : span (checkState 8) 8 992 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1000 : span (checkState 8) 8 1000 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1008 : span (checkState 8) 8 1008 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1016 : span (checkState 8) 8 1016 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1024 : span (checkState 8) 8 1024 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1032 : span (checkState 8) 8 1032 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1040 : span (checkState 8) 8 1040 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1048 : span (checkState 8) 8 1048 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1056 : span (checkState 8) 8 1056 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1064 : span (checkState 8) 8 1064 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1072 : span (checkState 8) 8 1072 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1080 : span (checkState 8) 8 1080 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1088 : span (checkState 8) 8 1088 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1096 : span (checkState 8) 8 1096 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1104 : span (checkState 8) 8 1104 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1112 : span (checkState 8) 8 1112 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1120 : span (checkState 8) 8 1120 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1128 : span (checkState 8) 8 1128 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1136 : span (checkState 8) 8 1136 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1144 : span (checkState 8) 8 1144 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1152 : span (checkState 8) 8 1152 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1160 : span (checkState 8) 8 1160 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1168 : span (checkState 8) 8 1168 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1176 : span (checkState 8) 8 1176 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1184 : span (checkState 8) 8 1184 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1192 : span (checkState 8) 8 1192 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1200 : span (checkState 8) 8 1200 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1208 : span (checkState 8) 8 1208 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1216 : span (checkState 8) 8 1216 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1224 : span (checkState 8) 8 1224 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1232 : span (checkState 8) 8 1232 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1240 : span (checkState 8) 8 1240 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1248 : span (checkState 8) 8 1248 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1256 : span (checkState 8) 8 1256 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1264 : span (checkState 8) 8 1264 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1272 : span (checkState 8) 8 1272 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1280 : span (checkState 8) 8 1280 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1288 : span (checkState 8) 8 1288 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1296 : span (checkState 8) 8 1296 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1304 : span (checkState 8) 8 1304 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1312 : span (checkState 8) 8 1312 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1320 : span (checkState 8) 8 1320 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1328 : span (checkState 8) 8 1328 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1336 : span (checkState 8) 8 1336 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1344 : span (checkState 8) 8 1344 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1352 : span (checkState 8) 8 1352 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1360 : span (checkState 8) 8 1360 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1368 : span (checkState 8) 8 1368 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1376 : span (checkState 8) 8 1376 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1384 : span (checkState 8) 8 1384 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1392 : span (checkState 8) 8 1392 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1400 : span (checkState 8) 8 1400 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1408 : span (checkState 8) 8 1408 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1416 : span (checkState 8) 8 1416 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1424 : span (checkState 8) 8 1424 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1432 : span (checkState 8) 8 1432 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1440 : span (checkState 8) 8 1440 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1448 : span (checkState 8) 8 1448 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1456 : span (checkState 8) 8 1456 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1464 : span (checkState 8) 8 1464 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1472 : span (checkState 8) 8 1472 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1480 : span (checkState 8) 8 1480 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1488 : span (checkState 8) 8 1488 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1496 : span (checkState 8) 8 1496 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1504 : span (checkState 8) 8 1504 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1512 : span (checkState 8) 8 1512 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1520 : span (checkState 8) 8 1520 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1528 : span (checkState 8) 8 1528 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1536 : span (checkState 8) 8 1536 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_8_1544 : span (checkState 8) 8 1544 = true := by decide +kernel

theorem combined_8_1_0 : span (checkState 8) 16 0 = true := @span_join (checkState 8) 8 0 8 block_8_0 block_8_8
theorem combined_8_1_1 : span (checkState 8) 16 16 = true := @span_join (checkState 8) 8 16 8 block_8_16 block_8_24
theorem combined_8_1_2 : span (checkState 8) 16 32 = true := @span_join (checkState 8) 8 32 8 block_8_32 block_8_40
theorem combined_8_1_3 : span (checkState 8) 16 48 = true := @span_join (checkState 8) 8 48 8 block_8_48 block_8_56
theorem combined_8_1_4 : span (checkState 8) 16 64 = true := @span_join (checkState 8) 8 64 8 block_8_64 block_8_72
theorem combined_8_1_5 : span (checkState 8) 16 80 = true := @span_join (checkState 8) 8 80 8 block_8_80 block_8_88
theorem combined_8_1_6 : span (checkState 8) 16 96 = true := @span_join (checkState 8) 8 96 8 block_8_96 block_8_104
theorem combined_8_1_7 : span (checkState 8) 16 112 = true := @span_join (checkState 8) 8 112 8 block_8_112 block_8_120
theorem combined_8_1_8 : span (checkState 8) 16 128 = true := @span_join (checkState 8) 8 128 8 block_8_128 block_8_136
theorem combined_8_1_9 : span (checkState 8) 16 144 = true := @span_join (checkState 8) 8 144 8 block_8_144 block_8_152
theorem combined_8_1_10 : span (checkState 8) 16 160 = true := @span_join (checkState 8) 8 160 8 block_8_160 block_8_168
theorem combined_8_1_11 : span (checkState 8) 16 176 = true := @span_join (checkState 8) 8 176 8 block_8_176 block_8_184
theorem combined_8_1_12 : span (checkState 8) 16 192 = true := @span_join (checkState 8) 8 192 8 block_8_192 block_8_200
theorem combined_8_1_13 : span (checkState 8) 16 208 = true := @span_join (checkState 8) 8 208 8 block_8_208 block_8_216
theorem combined_8_1_14 : span (checkState 8) 16 224 = true := @span_join (checkState 8) 8 224 8 block_8_224 block_8_232
theorem combined_8_1_15 : span (checkState 8) 16 240 = true := @span_join (checkState 8) 8 240 8 block_8_240 block_8_248
theorem combined_8_1_16 : span (checkState 8) 16 256 = true := @span_join (checkState 8) 8 256 8 block_8_256 block_8_264
theorem combined_8_1_17 : span (checkState 8) 16 272 = true := @span_join (checkState 8) 8 272 8 block_8_272 block_8_280
theorem combined_8_1_18 : span (checkState 8) 16 288 = true := @span_join (checkState 8) 8 288 8 block_8_288 block_8_296
theorem combined_8_1_19 : span (checkState 8) 16 304 = true := @span_join (checkState 8) 8 304 8 block_8_304 block_8_312
theorem combined_8_1_20 : span (checkState 8) 16 320 = true := @span_join (checkState 8) 8 320 8 block_8_320 block_8_328
theorem combined_8_1_21 : span (checkState 8) 16 336 = true := @span_join (checkState 8) 8 336 8 block_8_336 block_8_344
theorem combined_8_1_22 : span (checkState 8) 16 352 = true := @span_join (checkState 8) 8 352 8 block_8_352 block_8_360
theorem combined_8_1_23 : span (checkState 8) 16 368 = true := @span_join (checkState 8) 8 368 8 block_8_368 block_8_376
theorem combined_8_1_24 : span (checkState 8) 16 384 = true := @span_join (checkState 8) 8 384 8 block_8_384 block_8_392
theorem combined_8_1_25 : span (checkState 8) 16 400 = true := @span_join (checkState 8) 8 400 8 block_8_400 block_8_408
theorem combined_8_1_26 : span (checkState 8) 16 416 = true := @span_join (checkState 8) 8 416 8 block_8_416 block_8_424
theorem combined_8_1_27 : span (checkState 8) 16 432 = true := @span_join (checkState 8) 8 432 8 block_8_432 block_8_440
theorem combined_8_1_28 : span (checkState 8) 16 448 = true := @span_join (checkState 8) 8 448 8 block_8_448 block_8_456
theorem combined_8_1_29 : span (checkState 8) 16 464 = true := @span_join (checkState 8) 8 464 8 block_8_464 block_8_472
theorem combined_8_1_30 : span (checkState 8) 16 480 = true := @span_join (checkState 8) 8 480 8 block_8_480 block_8_488
theorem combined_8_1_31 : span (checkState 8) 16 496 = true := @span_join (checkState 8) 8 496 8 block_8_496 block_8_504
theorem combined_8_1_32 : span (checkState 8) 16 512 = true := @span_join (checkState 8) 8 512 8 block_8_512 block_8_520
theorem combined_8_1_33 : span (checkState 8) 16 528 = true := @span_join (checkState 8) 8 528 8 block_8_528 block_8_536
theorem combined_8_1_34 : span (checkState 8) 16 544 = true := @span_join (checkState 8) 8 544 8 block_8_544 block_8_552
theorem combined_8_1_35 : span (checkState 8) 16 560 = true := @span_join (checkState 8) 8 560 8 block_8_560 block_8_568
theorem combined_8_1_36 : span (checkState 8) 16 576 = true := @span_join (checkState 8) 8 576 8 block_8_576 block_8_584
theorem combined_8_1_37 : span (checkState 8) 16 592 = true := @span_join (checkState 8) 8 592 8 block_8_592 block_8_600
theorem combined_8_1_38 : span (checkState 8) 16 608 = true := @span_join (checkState 8) 8 608 8 block_8_608 block_8_616
theorem combined_8_1_39 : span (checkState 8) 16 624 = true := @span_join (checkState 8) 8 624 8 block_8_624 block_8_632
theorem combined_8_1_40 : span (checkState 8) 16 640 = true := @span_join (checkState 8) 8 640 8 block_8_640 block_8_648
theorem combined_8_1_41 : span (checkState 8) 16 656 = true := @span_join (checkState 8) 8 656 8 block_8_656 block_8_664
theorem combined_8_1_42 : span (checkState 8) 16 672 = true := @span_join (checkState 8) 8 672 8 block_8_672 block_8_680
theorem combined_8_1_43 : span (checkState 8) 16 688 = true := @span_join (checkState 8) 8 688 8 block_8_688 block_8_696
theorem combined_8_1_44 : span (checkState 8) 16 704 = true := @span_join (checkState 8) 8 704 8 block_8_704 block_8_712
theorem combined_8_1_45 : span (checkState 8) 16 720 = true := @span_join (checkState 8) 8 720 8 block_8_720 block_8_728
theorem combined_8_1_46 : span (checkState 8) 16 736 = true := @span_join (checkState 8) 8 736 8 block_8_736 block_8_744
theorem combined_8_1_47 : span (checkState 8) 16 752 = true := @span_join (checkState 8) 8 752 8 block_8_752 block_8_760
theorem combined_8_1_48 : span (checkState 8) 16 768 = true := @span_join (checkState 8) 8 768 8 block_8_768 block_8_776
theorem combined_8_1_49 : span (checkState 8) 16 784 = true := @span_join (checkState 8) 8 784 8 block_8_784 block_8_792
theorem combined_8_1_50 : span (checkState 8) 16 800 = true := @span_join (checkState 8) 8 800 8 block_8_800 block_8_808
theorem combined_8_1_51 : span (checkState 8) 16 816 = true := @span_join (checkState 8) 8 816 8 block_8_816 block_8_824
theorem combined_8_1_52 : span (checkState 8) 16 832 = true := @span_join (checkState 8) 8 832 8 block_8_832 block_8_840
theorem combined_8_1_53 : span (checkState 8) 16 848 = true := @span_join (checkState 8) 8 848 8 block_8_848 block_8_856
theorem combined_8_1_54 : span (checkState 8) 16 864 = true := @span_join (checkState 8) 8 864 8 block_8_864 block_8_872
theorem combined_8_1_55 : span (checkState 8) 16 880 = true := @span_join (checkState 8) 8 880 8 block_8_880 block_8_888
theorem combined_8_1_56 : span (checkState 8) 16 896 = true := @span_join (checkState 8) 8 896 8 block_8_896 block_8_904
theorem combined_8_1_57 : span (checkState 8) 16 912 = true := @span_join (checkState 8) 8 912 8 block_8_912 block_8_920
theorem combined_8_1_58 : span (checkState 8) 16 928 = true := @span_join (checkState 8) 8 928 8 block_8_928 block_8_936
theorem combined_8_1_59 : span (checkState 8) 16 944 = true := @span_join (checkState 8) 8 944 8 block_8_944 block_8_952
theorem combined_8_1_60 : span (checkState 8) 16 960 = true := @span_join (checkState 8) 8 960 8 block_8_960 block_8_968
theorem combined_8_1_61 : span (checkState 8) 16 976 = true := @span_join (checkState 8) 8 976 8 block_8_976 block_8_984
theorem combined_8_1_62 : span (checkState 8) 16 992 = true := @span_join (checkState 8) 8 992 8 block_8_992 block_8_1000
theorem combined_8_1_63 : span (checkState 8) 16 1008 = true := @span_join (checkState 8) 8 1008 8 block_8_1008 block_8_1016
theorem combined_8_1_64 : span (checkState 8) 16 1024 = true := @span_join (checkState 8) 8 1024 8 block_8_1024 block_8_1032
theorem combined_8_1_65 : span (checkState 8) 16 1040 = true := @span_join (checkState 8) 8 1040 8 block_8_1040 block_8_1048
theorem combined_8_1_66 : span (checkState 8) 16 1056 = true := @span_join (checkState 8) 8 1056 8 block_8_1056 block_8_1064
theorem combined_8_1_67 : span (checkState 8) 16 1072 = true := @span_join (checkState 8) 8 1072 8 block_8_1072 block_8_1080
theorem combined_8_1_68 : span (checkState 8) 16 1088 = true := @span_join (checkState 8) 8 1088 8 block_8_1088 block_8_1096
theorem combined_8_1_69 : span (checkState 8) 16 1104 = true := @span_join (checkState 8) 8 1104 8 block_8_1104 block_8_1112
theorem combined_8_1_70 : span (checkState 8) 16 1120 = true := @span_join (checkState 8) 8 1120 8 block_8_1120 block_8_1128
theorem combined_8_1_71 : span (checkState 8) 16 1136 = true := @span_join (checkState 8) 8 1136 8 block_8_1136 block_8_1144
theorem combined_8_1_72 : span (checkState 8) 16 1152 = true := @span_join (checkState 8) 8 1152 8 block_8_1152 block_8_1160
theorem combined_8_1_73 : span (checkState 8) 16 1168 = true := @span_join (checkState 8) 8 1168 8 block_8_1168 block_8_1176
theorem combined_8_1_74 : span (checkState 8) 16 1184 = true := @span_join (checkState 8) 8 1184 8 block_8_1184 block_8_1192
theorem combined_8_1_75 : span (checkState 8) 16 1200 = true := @span_join (checkState 8) 8 1200 8 block_8_1200 block_8_1208
theorem combined_8_1_76 : span (checkState 8) 16 1216 = true := @span_join (checkState 8) 8 1216 8 block_8_1216 block_8_1224
theorem combined_8_1_77 : span (checkState 8) 16 1232 = true := @span_join (checkState 8) 8 1232 8 block_8_1232 block_8_1240
theorem combined_8_1_78 : span (checkState 8) 16 1248 = true := @span_join (checkState 8) 8 1248 8 block_8_1248 block_8_1256
theorem combined_8_1_79 : span (checkState 8) 16 1264 = true := @span_join (checkState 8) 8 1264 8 block_8_1264 block_8_1272
theorem combined_8_1_80 : span (checkState 8) 16 1280 = true := @span_join (checkState 8) 8 1280 8 block_8_1280 block_8_1288
theorem combined_8_1_81 : span (checkState 8) 16 1296 = true := @span_join (checkState 8) 8 1296 8 block_8_1296 block_8_1304
theorem combined_8_1_82 : span (checkState 8) 16 1312 = true := @span_join (checkState 8) 8 1312 8 block_8_1312 block_8_1320
theorem combined_8_1_83 : span (checkState 8) 16 1328 = true := @span_join (checkState 8) 8 1328 8 block_8_1328 block_8_1336
theorem combined_8_1_84 : span (checkState 8) 16 1344 = true := @span_join (checkState 8) 8 1344 8 block_8_1344 block_8_1352
theorem combined_8_1_85 : span (checkState 8) 16 1360 = true := @span_join (checkState 8) 8 1360 8 block_8_1360 block_8_1368
theorem combined_8_1_86 : span (checkState 8) 16 1376 = true := @span_join (checkState 8) 8 1376 8 block_8_1376 block_8_1384
theorem combined_8_1_87 : span (checkState 8) 16 1392 = true := @span_join (checkState 8) 8 1392 8 block_8_1392 block_8_1400
theorem combined_8_1_88 : span (checkState 8) 16 1408 = true := @span_join (checkState 8) 8 1408 8 block_8_1408 block_8_1416
theorem combined_8_1_89 : span (checkState 8) 16 1424 = true := @span_join (checkState 8) 8 1424 8 block_8_1424 block_8_1432
theorem combined_8_1_90 : span (checkState 8) 16 1440 = true := @span_join (checkState 8) 8 1440 8 block_8_1440 block_8_1448
theorem combined_8_1_91 : span (checkState 8) 16 1456 = true := @span_join (checkState 8) 8 1456 8 block_8_1456 block_8_1464
theorem combined_8_1_92 : span (checkState 8) 16 1472 = true := @span_join (checkState 8) 8 1472 8 block_8_1472 block_8_1480
theorem combined_8_1_93 : span (checkState 8) 16 1488 = true := @span_join (checkState 8) 8 1488 8 block_8_1488 block_8_1496
theorem combined_8_1_94 : span (checkState 8) 16 1504 = true := @span_join (checkState 8) 8 1504 8 block_8_1504 block_8_1512
theorem combined_8_1_95 : span (checkState 8) 16 1520 = true := @span_join (checkState 8) 8 1520 8 block_8_1520 block_8_1528
theorem combined_8_1_96 : span (checkState 8) 16 1536 = true := @span_join (checkState 8) 8 1536 8 block_8_1536 block_8_1544
theorem combined_8_2_0 : span (checkState 8) 32 0 = true := @span_join (checkState 8) 16 0 16 combined_8_1_0 combined_8_1_1
theorem combined_8_2_1 : span (checkState 8) 32 32 = true := @span_join (checkState 8) 16 32 16 combined_8_1_2 combined_8_1_3
theorem combined_8_2_2 : span (checkState 8) 32 64 = true := @span_join (checkState 8) 16 64 16 combined_8_1_4 combined_8_1_5
theorem combined_8_2_3 : span (checkState 8) 32 96 = true := @span_join (checkState 8) 16 96 16 combined_8_1_6 combined_8_1_7
theorem combined_8_2_4 : span (checkState 8) 32 128 = true := @span_join (checkState 8) 16 128 16 combined_8_1_8 combined_8_1_9
theorem combined_8_2_5 : span (checkState 8) 32 160 = true := @span_join (checkState 8) 16 160 16 combined_8_1_10 combined_8_1_11
theorem combined_8_2_6 : span (checkState 8) 32 192 = true := @span_join (checkState 8) 16 192 16 combined_8_1_12 combined_8_1_13
theorem combined_8_2_7 : span (checkState 8) 32 224 = true := @span_join (checkState 8) 16 224 16 combined_8_1_14 combined_8_1_15
theorem combined_8_2_8 : span (checkState 8) 32 256 = true := @span_join (checkState 8) 16 256 16 combined_8_1_16 combined_8_1_17
theorem combined_8_2_9 : span (checkState 8) 32 288 = true := @span_join (checkState 8) 16 288 16 combined_8_1_18 combined_8_1_19
theorem combined_8_2_10 : span (checkState 8) 32 320 = true := @span_join (checkState 8) 16 320 16 combined_8_1_20 combined_8_1_21
theorem combined_8_2_11 : span (checkState 8) 32 352 = true := @span_join (checkState 8) 16 352 16 combined_8_1_22 combined_8_1_23
theorem combined_8_2_12 : span (checkState 8) 32 384 = true := @span_join (checkState 8) 16 384 16 combined_8_1_24 combined_8_1_25
theorem combined_8_2_13 : span (checkState 8) 32 416 = true := @span_join (checkState 8) 16 416 16 combined_8_1_26 combined_8_1_27
theorem combined_8_2_14 : span (checkState 8) 32 448 = true := @span_join (checkState 8) 16 448 16 combined_8_1_28 combined_8_1_29
theorem combined_8_2_15 : span (checkState 8) 32 480 = true := @span_join (checkState 8) 16 480 16 combined_8_1_30 combined_8_1_31
theorem combined_8_2_16 : span (checkState 8) 32 512 = true := @span_join (checkState 8) 16 512 16 combined_8_1_32 combined_8_1_33
theorem combined_8_2_17 : span (checkState 8) 32 544 = true := @span_join (checkState 8) 16 544 16 combined_8_1_34 combined_8_1_35
theorem combined_8_2_18 : span (checkState 8) 32 576 = true := @span_join (checkState 8) 16 576 16 combined_8_1_36 combined_8_1_37
theorem combined_8_2_19 : span (checkState 8) 32 608 = true := @span_join (checkState 8) 16 608 16 combined_8_1_38 combined_8_1_39
theorem combined_8_2_20 : span (checkState 8) 32 640 = true := @span_join (checkState 8) 16 640 16 combined_8_1_40 combined_8_1_41
theorem combined_8_2_21 : span (checkState 8) 32 672 = true := @span_join (checkState 8) 16 672 16 combined_8_1_42 combined_8_1_43
theorem combined_8_2_22 : span (checkState 8) 32 704 = true := @span_join (checkState 8) 16 704 16 combined_8_1_44 combined_8_1_45
theorem combined_8_2_23 : span (checkState 8) 32 736 = true := @span_join (checkState 8) 16 736 16 combined_8_1_46 combined_8_1_47
theorem combined_8_2_24 : span (checkState 8) 32 768 = true := @span_join (checkState 8) 16 768 16 combined_8_1_48 combined_8_1_49
theorem combined_8_2_25 : span (checkState 8) 32 800 = true := @span_join (checkState 8) 16 800 16 combined_8_1_50 combined_8_1_51
theorem combined_8_2_26 : span (checkState 8) 32 832 = true := @span_join (checkState 8) 16 832 16 combined_8_1_52 combined_8_1_53
theorem combined_8_2_27 : span (checkState 8) 32 864 = true := @span_join (checkState 8) 16 864 16 combined_8_1_54 combined_8_1_55
theorem combined_8_2_28 : span (checkState 8) 32 896 = true := @span_join (checkState 8) 16 896 16 combined_8_1_56 combined_8_1_57
theorem combined_8_2_29 : span (checkState 8) 32 928 = true := @span_join (checkState 8) 16 928 16 combined_8_1_58 combined_8_1_59
theorem combined_8_2_30 : span (checkState 8) 32 960 = true := @span_join (checkState 8) 16 960 16 combined_8_1_60 combined_8_1_61
theorem combined_8_2_31 : span (checkState 8) 32 992 = true := @span_join (checkState 8) 16 992 16 combined_8_1_62 combined_8_1_63
theorem combined_8_2_32 : span (checkState 8) 32 1024 = true := @span_join (checkState 8) 16 1024 16 combined_8_1_64 combined_8_1_65
theorem combined_8_2_33 : span (checkState 8) 32 1056 = true := @span_join (checkState 8) 16 1056 16 combined_8_1_66 combined_8_1_67
theorem combined_8_2_34 : span (checkState 8) 32 1088 = true := @span_join (checkState 8) 16 1088 16 combined_8_1_68 combined_8_1_69
theorem combined_8_2_35 : span (checkState 8) 32 1120 = true := @span_join (checkState 8) 16 1120 16 combined_8_1_70 combined_8_1_71
theorem combined_8_2_36 : span (checkState 8) 32 1152 = true := @span_join (checkState 8) 16 1152 16 combined_8_1_72 combined_8_1_73
theorem combined_8_2_37 : span (checkState 8) 32 1184 = true := @span_join (checkState 8) 16 1184 16 combined_8_1_74 combined_8_1_75
theorem combined_8_2_38 : span (checkState 8) 32 1216 = true := @span_join (checkState 8) 16 1216 16 combined_8_1_76 combined_8_1_77
theorem combined_8_2_39 : span (checkState 8) 32 1248 = true := @span_join (checkState 8) 16 1248 16 combined_8_1_78 combined_8_1_79
theorem combined_8_2_40 : span (checkState 8) 32 1280 = true := @span_join (checkState 8) 16 1280 16 combined_8_1_80 combined_8_1_81
theorem combined_8_2_41 : span (checkState 8) 32 1312 = true := @span_join (checkState 8) 16 1312 16 combined_8_1_82 combined_8_1_83
theorem combined_8_2_42 : span (checkState 8) 32 1344 = true := @span_join (checkState 8) 16 1344 16 combined_8_1_84 combined_8_1_85
theorem combined_8_2_43 : span (checkState 8) 32 1376 = true := @span_join (checkState 8) 16 1376 16 combined_8_1_86 combined_8_1_87
theorem combined_8_2_44 : span (checkState 8) 32 1408 = true := @span_join (checkState 8) 16 1408 16 combined_8_1_88 combined_8_1_89
theorem combined_8_2_45 : span (checkState 8) 32 1440 = true := @span_join (checkState 8) 16 1440 16 combined_8_1_90 combined_8_1_91
theorem combined_8_2_46 : span (checkState 8) 32 1472 = true := @span_join (checkState 8) 16 1472 16 combined_8_1_92 combined_8_1_93
theorem combined_8_2_47 : span (checkState 8) 32 1504 = true := @span_join (checkState 8) 16 1504 16 combined_8_1_94 combined_8_1_95
theorem combined_8_4_0 : span (checkState 8) 64 0 = true := @span_join (checkState 8) 32 0 32 combined_8_2_0 combined_8_2_1
theorem combined_8_4_1 : span (checkState 8) 64 64 = true := @span_join (checkState 8) 32 64 32 combined_8_2_2 combined_8_2_3
theorem combined_8_4_2 : span (checkState 8) 64 128 = true := @span_join (checkState 8) 32 128 32 combined_8_2_4 combined_8_2_5
theorem combined_8_4_3 : span (checkState 8) 64 192 = true := @span_join (checkState 8) 32 192 32 combined_8_2_6 combined_8_2_7
theorem combined_8_4_4 : span (checkState 8) 64 256 = true := @span_join (checkState 8) 32 256 32 combined_8_2_8 combined_8_2_9
theorem combined_8_4_5 : span (checkState 8) 64 320 = true := @span_join (checkState 8) 32 320 32 combined_8_2_10 combined_8_2_11
theorem combined_8_4_6 : span (checkState 8) 64 384 = true := @span_join (checkState 8) 32 384 32 combined_8_2_12 combined_8_2_13
theorem combined_8_4_7 : span (checkState 8) 64 448 = true := @span_join (checkState 8) 32 448 32 combined_8_2_14 combined_8_2_15
theorem combined_8_4_8 : span (checkState 8) 64 512 = true := @span_join (checkState 8) 32 512 32 combined_8_2_16 combined_8_2_17
theorem combined_8_4_9 : span (checkState 8) 64 576 = true := @span_join (checkState 8) 32 576 32 combined_8_2_18 combined_8_2_19
theorem combined_8_4_10 : span (checkState 8) 64 640 = true := @span_join (checkState 8) 32 640 32 combined_8_2_20 combined_8_2_21
theorem combined_8_4_11 : span (checkState 8) 64 704 = true := @span_join (checkState 8) 32 704 32 combined_8_2_22 combined_8_2_23
theorem combined_8_4_12 : span (checkState 8) 64 768 = true := @span_join (checkState 8) 32 768 32 combined_8_2_24 combined_8_2_25
theorem combined_8_4_13 : span (checkState 8) 64 832 = true := @span_join (checkState 8) 32 832 32 combined_8_2_26 combined_8_2_27
theorem combined_8_4_14 : span (checkState 8) 64 896 = true := @span_join (checkState 8) 32 896 32 combined_8_2_28 combined_8_2_29
theorem combined_8_4_15 : span (checkState 8) 64 960 = true := @span_join (checkState 8) 32 960 32 combined_8_2_30 combined_8_2_31
theorem combined_8_4_16 : span (checkState 8) 64 1024 = true := @span_join (checkState 8) 32 1024 32 combined_8_2_32 combined_8_2_33
theorem combined_8_4_17 : span (checkState 8) 64 1088 = true := @span_join (checkState 8) 32 1088 32 combined_8_2_34 combined_8_2_35
theorem combined_8_4_18 : span (checkState 8) 64 1152 = true := @span_join (checkState 8) 32 1152 32 combined_8_2_36 combined_8_2_37
theorem combined_8_4_19 : span (checkState 8) 64 1216 = true := @span_join (checkState 8) 32 1216 32 combined_8_2_38 combined_8_2_39
theorem combined_8_4_20 : span (checkState 8) 64 1280 = true := @span_join (checkState 8) 32 1280 32 combined_8_2_40 combined_8_2_41
theorem combined_8_4_21 : span (checkState 8) 64 1344 = true := @span_join (checkState 8) 32 1344 32 combined_8_2_42 combined_8_2_43
theorem combined_8_4_22 : span (checkState 8) 64 1408 = true := @span_join (checkState 8) 32 1408 32 combined_8_2_44 combined_8_2_45
theorem combined_8_4_23 : span (checkState 8) 64 1472 = true := @span_join (checkState 8) 32 1472 32 combined_8_2_46 combined_8_2_47
theorem combined_8_8_0 : span (checkState 8) 128 0 = true := @span_join (checkState 8) 64 0 64 combined_8_4_0 combined_8_4_1
theorem combined_8_8_1 : span (checkState 8) 128 128 = true := @span_join (checkState 8) 64 128 64 combined_8_4_2 combined_8_4_3
theorem combined_8_8_2 : span (checkState 8) 128 256 = true := @span_join (checkState 8) 64 256 64 combined_8_4_4 combined_8_4_5
theorem combined_8_8_3 : span (checkState 8) 128 384 = true := @span_join (checkState 8) 64 384 64 combined_8_4_6 combined_8_4_7
theorem combined_8_8_4 : span (checkState 8) 128 512 = true := @span_join (checkState 8) 64 512 64 combined_8_4_8 combined_8_4_9
theorem combined_8_8_5 : span (checkState 8) 128 640 = true := @span_join (checkState 8) 64 640 64 combined_8_4_10 combined_8_4_11
theorem combined_8_8_6 : span (checkState 8) 128 768 = true := @span_join (checkState 8) 64 768 64 combined_8_4_12 combined_8_4_13
theorem combined_8_8_7 : span (checkState 8) 128 896 = true := @span_join (checkState 8) 64 896 64 combined_8_4_14 combined_8_4_15
theorem combined_8_8_8 : span (checkState 8) 128 1024 = true := @span_join (checkState 8) 64 1024 64 combined_8_4_16 combined_8_4_17
theorem combined_8_8_9 : span (checkState 8) 128 1152 = true := @span_join (checkState 8) 64 1152 64 combined_8_4_18 combined_8_4_19
theorem combined_8_8_10 : span (checkState 8) 128 1280 = true := @span_join (checkState 8) 64 1280 64 combined_8_4_20 combined_8_4_21
theorem combined_8_8_11 : span (checkState 8) 128 1408 = true := @span_join (checkState 8) 64 1408 64 combined_8_4_22 combined_8_4_23
theorem combined_8_16_0 : span (checkState 8) 256 0 = true := @span_join (checkState 8) 128 0 128 combined_8_8_0 combined_8_8_1
theorem combined_8_16_1 : span (checkState 8) 256 256 = true := @span_join (checkState 8) 128 256 128 combined_8_8_2 combined_8_8_3
theorem combined_8_16_2 : span (checkState 8) 256 512 = true := @span_join (checkState 8) 128 512 128 combined_8_8_4 combined_8_8_5
theorem combined_8_16_3 : span (checkState 8) 256 768 = true := @span_join (checkState 8) 128 768 128 combined_8_8_6 combined_8_8_7
theorem combined_8_16_4 : span (checkState 8) 256 1024 = true := @span_join (checkState 8) 128 1024 128 combined_8_8_8 combined_8_8_9
theorem combined_8_16_5 : span (checkState 8) 256 1280 = true := @span_join (checkState 8) 128 1280 128 combined_8_8_10 combined_8_8_11
theorem combined_8_32_0 : span (checkState 8) 512 0 = true := @span_join (checkState 8) 256 0 256 combined_8_16_0 combined_8_16_1
theorem combined_8_32_1 : span (checkState 8) 512 512 = true := @span_join (checkState 8) 256 512 256 combined_8_16_2 combined_8_16_3
theorem combined_8_32_2 : span (checkState 8) 512 1024 = true := @span_join (checkState 8) 256 1024 256 combined_8_16_4 combined_8_16_5
theorem combined_8_64_0 : span (checkState 8) 1024 0 = true := @span_join (checkState 8) 512 0 512 combined_8_32_0 combined_8_32_1
theorem combined_8_64_1 : span (checkState 8) 528 1024 = true := @span_join (checkState 8) 512 1024 16 combined_8_32_2 combined_8_1_96
theorem combined_8_128_0 : span (checkState 8) 1552 0 = true := @span_join (checkState 8) 1024 0 528 combined_8_64_0 combined_8_64_1
theorem all_8 : span (checkState 8) 1552 0 = true := combined_8_128_0

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_9_0 : span (checkState 9) 8 0 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_9_8 : span (checkState 9) 8 8 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_9_16 : span (checkState 9) 8 16 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_9_24 : span (checkState 9) 8 24 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_9_32 : span (checkState 9) 8 32 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_9_40 : span (checkState 9) 8 40 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_9_48 : span (checkState 9) 8 48 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_9_56 : span (checkState 9) 8 56 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_9_64 : span (checkState 9) 3 64 = true := by decide +kernel

theorem combined_9_1_0 : span (checkState 9) 16 0 = true := @span_join (checkState 9) 8 0 8 block_9_0 block_9_8
theorem combined_9_1_1 : span (checkState 9) 16 16 = true := @span_join (checkState 9) 8 16 8 block_9_16 block_9_24
theorem combined_9_1_2 : span (checkState 9) 16 32 = true := @span_join (checkState 9) 8 32 8 block_9_32 block_9_40
theorem combined_9_1_3 : span (checkState 9) 16 48 = true := @span_join (checkState 9) 8 48 8 block_9_48 block_9_56
theorem combined_9_2_0 : span (checkState 9) 32 0 = true := @span_join (checkState 9) 16 0 16 combined_9_1_0 combined_9_1_1
theorem combined_9_2_1 : span (checkState 9) 32 32 = true := @span_join (checkState 9) 16 32 16 combined_9_1_2 combined_9_1_3
theorem combined_9_4_0 : span (checkState 9) 64 0 = true := @span_join (checkState 9) 32 0 32 combined_9_2_0 combined_9_2_1
theorem combined_9_8_0 : span (checkState 9) 67 0 = true := @span_join (checkState 9) 64 0 3 combined_9_4_0 block_9_64
theorem all_9 : span (checkState 9) 67 0 = true := combined_9_8_0

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem block_10_0 : span (checkState 10) 1 0 = true := by decide +kernel

theorem all_10 : span (checkState 10) 1 0 = true := block_10_0

theorem certificate (s : Nat) (hs : s ≤ 10) : ∀ i < stateCount s, checkState s i = true := by
  interval_cases s
  · simp [stateCount]
  · simp [stateCount]
  · simp [stateCount]
  · exact fun i hi => @span_ok (checkState 3) 1 0 all_3 i (Nat.zero_le i) hi
  · exact fun i hi => @span_ok (checkState 4) 19 0 all_4 i (Nat.zero_le i) hi
  · exact fun i hi => @span_ok (checkState 5) 100 0 all_5 i (Nat.zero_le i) hi
  · exact fun i hi => @span_ok (checkState 6) 666 0 all_6 i (Nat.zero_le i) hi
  · exact fun i hi => @span_ok (checkState 7) 2297 0 all_7 i (Nat.zero_le i) hi
  · exact fun i hi => @span_ok (checkState 8) 1552 0 all_8 i (Nat.zero_le i) hi
  · exact fun i hi => @span_ok (checkState 9) 67 0 all_9 i (Nat.zero_le i) hi
  · exact fun i hi => @span_ok (checkState 10) 1 0 all_10 i (Nat.zero_le i) hi

private theorem coreLower : ∀ s : Nat, HasCircuitSize 7 core s → 11 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run core
    ⟨fun _ => false, fun _ => true, by decide⟩ s h
  have hmask : mask cutCount = 2 ^ sampleRows.length - 1 := by decide +kernel
  have hr : NatRun (mask cutCount) (encL core sampleRows) s' (ws.map fun a => encL a sampleRows) :=
    Run.map (fun a : BFn 7 => encL a sampleRows)
      (fun a => by rw [hmask]; exact encL_inv a sampleRows)
      (fun a b => encL_and a b sampleRows) (fun a b => encL_or a b sampleRows) hrun
  rw [goalEncoded] at hr
  have hsub' : (ws.map fun a => encL a sampleRows).Sublist inputs := by
    rw [← inputsEncoded]
    exact hsub.map _
  by_cases he : (ws.map fun a => encL a sampleRows) = inputs
  · rw [he] at hr
    unfold inputs at hr
    have padded := extend_run hr (t := 10) (by omega)
    have hstart : 0 < stateCount 10 := by decide
    exact bar_all (fun h => h) certificate 10 le_rfl 0 hstart padded
  · exact properFail _ (List.mem_sublists.2 hsub') he (required hr)

def coreEdges : List (Fin 9 × Fin 9) := [(0, 4), (0, 6), (2, 6), (0, 7), (4, 7), (2, 8), (3, 8), (4, 8)]
def branchEdges : List (Fin 9 × Fin 9) := [(0, 4), (0, 6), (2, 6), (0, 7), (1, 7), (4, 7), (2, 8), (3, 8), (4, 8)]
def targetEdges : List (Fin 9 × Fin 9) := [(0, 4), (1, 5), (0, 6), (2, 6), (0, 7), (1, 7), (4, 7), (2, 8), (3, 8), (4, 8)]

def coreRelabel (i : Fin 9) : Fin 7 :=
  match i.val with
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

private theorem core9Lower : ∀ s : Nat, HasCircuitSize 9 (gfn [] coreEdges) s → 11 ≤ s :=
  gfn_base coreEdges edgeList coreRelabel (by decide) coreLower

private theorem targetLower : ∀ s : Nat, HasCircuitSize 9 (gfn [] targetEdges) s → 14 ≤ s := by
  apply gfn_branch2 [] targetEdges 5 [] branchEdges [1] coreEdges 12
  all_goals try decide
  · apply gfn_fix0 [] branchEdges 1 [] coreEdges 11
    all_goals first | decide | exact core9Lower
  · apply gfn_fix0 [1] coreEdges 1 [] coreEdges 11
    all_goals first | decide | exact core9Lower

end PEqualNP.Outside.L_meta_9431

theorem PEqualNP.Outside.L_meta_9431 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 4 && x 8)) t → 14 ≤ t := by
  have h : (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) ||
      (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 2 && x 8) ||
      (x 3 && x 8) || (x 4 && x 8)) =
      PEqualNP.Outside.L_meta_9431.gfn [] PEqualNP.Outside.L_meta_9431.targetEdges := by
    funext x
    simp [PEqualNP.Outside.L_meta_9431.gfn, PEqualNP.Outside.L_meta_9431.targetEdges, Bool.or_assoc]
  rw [h]
  exact PEqualNP.Outside.L_meta_9431.targetLower
