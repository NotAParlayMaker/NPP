import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13349_aux.Base

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

end PEqualNP.Outside.L_meta_13349_aux.Base

namespace PEqualNP.Outside.L_meta_13349_aux.Dual

open PEqualNP.CircuitLowerBounds

def dualGate (k : ℕ) : Gate → Gate
  | ⟨GateOp.and, l⟩ => if l.all (fun i => decide (i < k)) then ⟨GateOp.or, l⟩ else ⟨GateOp.and, []⟩
  | ⟨GateOp.or, l⟩ => ⟨GateOp.and, l.filter (fun i => decide (i < k))⟩
  | ⟨GateOp.not, l⟩ => if l.headD k < k then ⟨GateOp.not, l⟩ else ⟨GateOp.or, []⟩
  | ⟨GateOp.mod m, l⟩ => ⟨GateOp.mod m, l⟩
  | ⟨GateOp.maj, l⟩ => ⟨GateOp.maj, l⟩

def dualList : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: gs => dualGate k g :: dualList (k + 1) gs

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_snoc_lt (L : List Bool) (v : Bool) (j : ℕ) (hj : j < L.length) :
    (L ++ [v]).getD j false = L.getD j false := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hj,
    List.getElem_append_left hj]

lemma getD_snoc_eq (L : List Bool) (v : Bool) (k : ℕ) (hk : L.length = k) :
    (L ++ [v]).getD k false = v := by
  subst hk
  simp

lemma any_neg (l : List ℕ) (k : ℕ) (W W' : List Bool)
    (hneg : ∀ i < k, W'.getD i false = !(W.getD i false)) (hl : ∀ i ∈ l, i < k) :
    (l.map fun i => W'.getD i false).any id = !((l.map fun i => W.getD i false).all id) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.any_cons, List.all_cons, id_eq]
    rw [ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)), hneg a (hl a List.mem_cons_self)]
    cases W.getD a false <;> simp

lemma all_neg (l : List ℕ) (k : ℕ) (W W' : List Bool)
    (hneg : ∀ i < k, W'.getD i false = !(W.getD i false))
    (hbig : ∀ i, k ≤ i → W.getD i false = false) :
    ((l.filter fun i => decide (i < k)).map fun i => W'.getD i false).all id =
      !((l.map fun i => W.getD i false).any id) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases ha : a < k
    · rw [List.filter_cons_of_pos (by simpa using ha)]
      simp only [List.map_cons, List.any_cons, List.all_cons, id_eq]
      rw [ih, hneg a ha]
      cases W.getD a false <;> simp
    · rw [List.filter_cons_of_neg (by simpa using ha)]
      simp only [List.map_cons, List.any_cons, id_eq]
      rw [ih, hbig a (by omega)]
      simp

lemma gate_dual (k : ℕ) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (W W' : List Bool) (hW : W.length = k)
    (hneg : ∀ i < k, W'.getD i false = !(W.getD i false)) :
    (dualGate k g).op.eval ((dualGate k g).inputs.map fun i => W'.getD i false) =
      !(g.op.eval (g.inputs.map fun i => W.getD i false)) := by
  have hbig : ∀ i, k ≤ i → W.getD i false = false := by
    intro i hi
    rw [List.getD_eq_default _ _ (by omega)]
  obtain ⟨op, l⟩ := g
  simp only at hg
  rcases hg with h | h | h <;> subst h
  · by_cases hall : l.all (fun i => decide (i < k)) = true
    · simp only [dualGate, hall, if_true, GateOp.eval]
      apply any_neg l k W W' hneg
      intro i hi
      rw [List.all_eq_true] at hall
      simpa using hall i hi
    · simp only [dualGate, hall, GateOp.eval]
      simp only [Bool.false_eq_true, if_false, List.map_nil, List.all_nil]
      have hex : ∃ i ∈ l, ¬ i < k := by
        simp only [List.all_eq_true, decide_eq_true_eq, not_forall] at hall
        obtain ⟨i, hi, hik⟩ := hall
        exact ⟨i, hi, hik⟩
      obtain ⟨i, hi, hik⟩ := hex
      have hf : (l.map fun i => W.getD i false).all id = false := by
        rw [Bool.eq_false_iff]
        intro hcon
        rw [List.all_eq_true] at hcon
        have h1 := hcon (W.getD i false) (List.mem_map_of_mem hi)
        rw [hbig i (by omega)] at h1
        simp at h1
      rw [hf]
      rfl
  · simp only [dualGate, GateOp.eval]
    exact all_neg l k W W' hneg hbig
  · cases l with
    | nil =>
      simp [dualGate, GateOp.eval]
    | cons a t =>
      by_cases ha : a < k
      · simp only [dualGate, List.headD_cons, ha, if_true, GateOp.eval, List.map_cons]
        rw [hneg a ha]
      · simp only [dualGate, List.headD_cons, ha, if_false, GateOp.eval, List.map_cons]
        rw [hbig a (by omega)]
        rfl

lemma fold_dual (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    ∀ (k : ℕ) (W W' : List Bool), W.length = k → W'.length = k →
      (∀ i < k, W'.getD i false = !(W.getD i false)) →
      ∀ i < k + gs.length,
        ((dualList k gs).foldl step W').getD i false = !((gs.foldl step W).getD i false) := by
  induction gs with
  | nil =>
    intro k W W' hW hW' hneg i hi
    simp only [List.length_nil, Nat.add_zero] at hi
    exact hneg i hi
  | cons g gs ih =>
    intro k W W' hW hW' hneg i hi
    simp only [dualList, List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) (k + 1)
    · simp [step, hW]
    · simp [step, hW']
    · intro j hj
      by_cases hjk : j < k
      · rw [step, step, getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
        exact hneg j hjk
      · have hj' : j = k := by omega
        subst hj'
        rw [step, step, getD_snoc_eq _ _ _ hW, getD_snoc_eq _ _ _ hW']
        exact gate_dual j g (hg g List.mem_cons_self) W W' hW hneg
    · simp only [List.length_cons] at hi
      omega

lemma dualList_length : ∀ (k : ℕ) (gs : List Gate), (dualList k gs).length = gs.length
  | _, [] => rfl
  | k, g :: gs => by simp [dualList, dualList_length (k + 1) gs]

lemma mem_dualList : ∀ (gs : List Gate) (k : ℕ) (g' : Gate), g' ∈ dualList k gs →
    ∃ k' : ℕ, ∃ g ∈ gs, g' = dualGate k' g := by
  intro gs
  induction gs with
  | nil =>
    intro k g' h
    simp [dualList] at h
  | cons g gs ih =>
    intro k g' h
    simp only [dualList, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨k, g, List.mem_cons_self, h⟩
    · obtain ⟨k', g0, hg0, he⟩ := ih (k + 1) g' h
      exact ⟨k', g0, List.mem_cons_of_mem _ hg0, he⟩

lemma getElem?_dualList : ∀ (gs : List Gate) (k i : ℕ),
    (dualList k gs)[i]? = (gs[i]?).map (dualGate (k + i)) := by
  intro gs
  induction gs with
  | nil =>
    intro k i
    simp [dualList]
  | cons g gs ih =>
    intro k i
    cases i with
    | zero => simp [dualList]
    | succ i =>
      simp only [dualList, List.getElem?_cons_succ]
      rw [ih (k + 1) i]
      congr 2
      omega

lemma dualGate_ok (k : ℕ) (g : Gate)
    (h : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    ((dualGate k g).op = GateOp.and ∨ (dualGate k g).op = GateOp.or ∨
      (dualGate k g).op = GateOp.not) ∧ (dualGate k g).inputs.length ≤ 2 := by
  obtain ⟨op, l⟩ := g
  obtain ⟨hop, hl⟩ := h
  simp only at hop hl
  rcases hop with h | h | h <;> subst h
  · simp only [dualGate]
    split <;> simp [hl]
  · simp only [dualGate]
    refine ⟨by simp, ?_⟩
    exact le_trans (List.length_filter_le _ _) hl
  · simp only [dualGate]
    split <;> simp [hl]

lemma dualGate_not (k : ℕ) (g : Gate) (h : (dualGate k g).op = GateOp.not) :
    g.op = GateOp.not := by
  obtain ⟨op, l⟩ := g
  cases op with
  | and =>
    simp only [dualGate] at h
    split at h <;> simp at h
  | or => simp [dualGate] at h
  | not => rfl
  | mod m => simp [dualGate] at h
  | maj => simp [dualGate] at h

lemma main : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.length = gates.length ∧ (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ (i : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), gates'[i]? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ g : PEqualNP.CircuitLowerBounds.Gate, gates[i]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∀ (w : ℕ) (x : Fin n → Bool), w < n + gates.length → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates', 0⟩ (List.ofFn x)).getD w false = !((PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun p : Fin n => !x p))).getD w false) := by
  intro n gates hgates
  refine ⟨dualList n gates, dualList_length n gates, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨k, g, hg, rfl⟩ := mem_dualList gates n g' hg'
    exact dualGate_ok k g (hgates g hg)
  · intro i g' hi hop
    rw [getElem?_dualList] at hi
    cases hgi : gates[i]? with
    | none => simp [hgi] at hi
    | some g =>
      rw [hgi] at hi
      simp only [Option.map_some, Option.some.injEq] at hi
      subst hi
      exact ⟨g, rfl, dualGate_not _ g hop⟩
  · intro w x hw
    have hneg : ∀ i < n, (List.ofFn x).getD i false =
        !((List.ofFn (fun p : Fin n => !x p)).getD i false) := by
      intro i hi
      rw [List.getD_eq_getElem _ _ (by simpa using hi),
        List.getD_eq_getElem _ _ (by simpa using hi)]
      simp
    exact fold_dual gates (fun g hg => (hgates g hg).1) n (List.ofFn (fun p : Fin n => !x p))
      (List.ofFn x) (by simp) (by simp) hneg w hw

end PEqualNP.Outside.L_meta_13349_aux.Dual

namespace PEqualNP.Outside.L_meta_13349_aux.LowerFive

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace S

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)




def rv (w : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr t => w.getD t false

def fok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem rv_ext (hs e : List Gate) (y : List Bool) (r : Bool ⊕ ℕ) (h : ∀ t, r = .inr t → t < y.length + hs.length) :
    rv (run (hs ++ e) y) r = rv (run hs y) r := by
  rcases r with b | t
  · rfl
  · exact run_prefix _ _ _ _ (h t rfl)

theorem emit (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, fok g → (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro g h1 h2
    refine ⟨.inr (N + hs.length), [g], by simp, by simpa using h1, ?_, fun y hy => ?_⟩
    · intro t ht
      cases ht
      simp
    · have : N + hs.length = (run hs y).length := by rw [run_length, hy]
      simp only [rv]
      rw [run_snoc, this, getD_at]
      exact h2 y hy
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
  · have hr := hv r (by simp)
    rcases hop with rfl | rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · rcases r with b | t
      · exact keep (.inl (!b)) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · exact add ⟨GateOp.not, [t]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
  · have hr := hv r (by simp)
    have hs' := hv s (by simp)
    rcases hop with rfl | rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.and, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.or, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
    · rcases r with b | t
      · exact keep (.inl (!b)) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · exact add ⟨GateOp.not, [t]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
  · simp at hl

theorem engine (n : ℕ) (C : Circuit) (ρ : (Fin n → Bool) → Fin n → Bool) (F : Finset ℕ) (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (h0 : ∀ i : Fin n, (∃ b, ∀ x, ρ x i = b) ∨ ∀ x, ρ x i = x i)
    (hne : ∃ x y, C.eval (List.ofFn (ρ x)) ≠ C.eval (List.ofFn (ρ y)))
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (C.wires (List.ofFn (ρ x))).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (C.wires (List.ofFn (ρ x))).getD (n + j) false = (C.wires (List.ofFn (ρ x))).getD w false)) :
    PEqualNP.MetaComplexity.HasCircuitSize n (fun x => C.eval (List.ofFn (ρ x))) (C.size - F.card) := by
  classical
  have hwires : ∀ x, C.wires (List.ofFn (ρ x)) = run C.gates (List.ofFn (ρ x)) := fun x => rfl
  have hpre : ∀ (k : ℕ) (x : Fin n → Bool) (w : ℕ), k ≤ C.gates.length → w < n + k → (run (C.gates.take k) (List.ofFn (ρ x))).getD w false = (run C.gates (List.ofFn (ρ x))).getD w false := by
    intro k x w hk hw
    have := run_prefix (C.gates.take k) (C.gates.drop k) (List.ofFn (ρ x)) w (by rw [List.length_take]; simp; omega)
    rw [List.take_append_drop] at this
    exact this.symm
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ w t, w < n + k → m w = .inr t → t < n + hs.length) ∧
      ∀ x : Fin n → Bool, ∀ w < n + k, (run C.gates (List.ofFn (ρ x))).getD w false = rv (run hs (List.ofFn x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : w < n then (if hb : ∃ b, ∀ x, ρ x ⟨w, h⟩ = b then .inl hb.choose else .inr w) else .inl false, by simp, by simp, ?_, ?_⟩
      · intro w t hw ht
        simp only [Nat.add_zero] at hw
        beta_reduce at ht
        rw [dif_pos hw] at ht
        split_ifs at ht
        cases ht
        simpa using hw
      · intro x w hw
        simp only [Nat.add_zero] at hw
        rw [run_input _ _ _ (by simpa using hw), List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hw]
        beta_reduce
        rw [dif_pos hw]
        simp only [Option.getD_some]
        split_ifs with hb
        · exact hb.choose_spec x
        · simp only [rv, run, List.foldl_nil]
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hw]
          exact (h0 ⟨w, hw⟩).resolve_left hb x
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      -- extend with a value for wire `n + k`
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, fok g) → (∀ t, r = .inr t → t < n + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ x : Fin n → Bool, (run C.gates (List.ofFn (ρ x))).getD (n + k) false = rv (run (hs ++ e) (List.ofFn x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < n + hs.length) ∧
      ∀ x : Fin n → Bool, ∀ w < n + (k + 1), (run C.gates (List.ofFn (ρ x))).getD w false = rv (run hs (List.ofFn x)) (m w) := by
        intro r e he hr hlen hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (rv_ext hs e (List.ofFn x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            simpa using this
      by_cases hkF : k ∈ F
      · rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by simp [hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, e2, e3, e4⟩ := emit n hs C.gates[k].op hop (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e3 (by simp [hkF]; exact e1) (fun x => ?_)
        rw [e4 _ (by simp)]
        have rg := run_gate C.gates (List.ofFn (ρ x)) k hk'
        rw [List.length_ofFn] at rg
        rw [rg, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp, m']
        split_ifs with h
        · exact h4 x i h
        · rfl
  obtain ⟨hs, m, h1, h2, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : (F.filter fun j => j < C.gates.length) = F := Finset.filter_true_of_mem fun j hj => (hF j hj).1
  rw [hFc] at h2
  have hout : C.output < n + C.gates.length := by
    by_contra h
    obtain ⟨x, y, hxy⟩ := hne
    refine hxy ?_
    change (run C.gates (List.ofFn (ρ x))).getD C.output false = (run C.gates (List.ofFn (ρ y))).getD C.output false
    rw [List.getD_eq_default _ _ (by rw [run_length]; simp; omega), List.getD_eq_default _ _ (by rw [run_length]; simp; omega)]
  have hev : ∀ x, C.eval (List.ofFn (ρ x)) = rv (run hs (List.ofFn x)) (m C.output) := fun x => h4 x _ hout
  rcases hm : m C.output with b | t
  · obtain ⟨x, y, hxy⟩ := hne
    rw [hev, hev, hm] at hxy
    exact absurd rfl hxy
  · refine ⟨⟨hs, t⟩, ?_, ?_, fun x => ?_⟩
    · intro g hg
      exact ⟨by simpa using (h1 g hg).1, (h1 g hg).2⟩
    · have e1 : C.size = C.gates.length := rfl
      have e2 : PEqualNP.CircuitLowerBounds.Circuit.size ⟨hs, t⟩ = hs.length := rfl
      omega
    · have := hev x
      rw [hm] at this
      exact this.symm


def Wv (n : ℕ) (C : Circuit) (ρ : (Fin n → Bool) → Fin n → Bool) (x : Fin n → Bool) (w : ℕ) : Bool := (run C.gates (List.ofFn (ρ x))).getD w false

def Cst (n : ℕ) (C : Circuit) (ρ : (Fin n → Bool) → Fin n → Bool) (w : ℕ) : Prop := ∃ b, ∀ x, Wv n C ρ x w = b

def Red (n : ℕ) (C : Circuit) (ρ : (Fin n → Bool) → Fin n → Bool) (j : ℕ) : Prop :=
  Cst n C ρ (n + j) ∨ ∃ w < n + j, ∀ x, Wv n C ρ x (n + j) = Wv n C ρ x w

def Shp (n : ℕ) (C : Circuit) : Prop := PEqualNP.MetaComplexity.FanInTwo C ∧ (∀ j (h : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < n + j) ∧
  ∀ g ∈ C.gates, g.inputs.Nodup ∧ g.inputs.length = if g.op.eval [false] = true then 1 else 2

def Res (n : ℕ) (i0 : Fin n) : (Fin n → Bool) → Fin n → Bool := fun x => Function.update x i0 false

theorem mkShp (n : ℕ) (C : Circuit) (h1 : PEqualNP.MetaComplexity.FanInTwo C) (h2 : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (h3 : ∀ g ∈ C.gates, g.inputs.Nodup ∧ g.inputs.length = if g.op.eval [false] = true then 1 else 2) : Shp n C := by
  refine ⟨h1, fun j h i hi => ?_, h3⟩
  have e : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ h
  exact h2 j h i (by rw [e]; exact hi)

theorem Wg {n : ℕ} {C : Circuit} (h : Shp n C) (ρ : (Fin n → Bool) → Fin n → Bool) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    Wv n C ρ x (n + j) = C.gates[j].op.eval (C.gates[j].inputs.map (Wv n C ρ x)) := by
  have := run_gate C.gates (List.ofFn (ρ x)) j hj
  rw [List.length_ofFn] at this
  rw [Wv, this]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  rw [if_pos (h.2.1 j hj i hi)]
  rfl

theorem Wi {n : ℕ} (C : Circuit) (ρ : (Fin n → Bool) → Fin n → Bool) (x : Fin n → Bool) (i : Fin n) : Wv n C ρ x i = ρ x i := by
  rw [Wv, run_input _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem Wz {n : ℕ} (C : Circuit) (i : Fin n) (x : Fin n → Bool) : Wv n C (Res n i) x i = false := by
  rw [Wi]; simp [Res]

theorem sem {n : ℕ} {C : Circuit} (h : Shp n C) (j : ℕ) (hj : j < C.gates.length) (w : ℕ) (hw : w ∈ C.gates[j].inputs) :
    (C.gates[j].op = GateOp.not ∧ (∀ u ∈ C.gates[j].inputs, u = w) ∧ ∀ ρ x, Wv n C ρ x (n + j) = !Wv n C ρ x w) ∨
    ∃ v ∈ C.gates[j].inputs, (∀ u ∈ C.gates[j].inputs, u = w ∨ u = v) ∧
      ((C.gates[j].op = GateOp.and ∧ ∀ ρ x, Wv n C ρ x (n + j) = (Wv n C ρ x w && Wv n C ρ x v)) ∨
       (C.gates[j].op = GateOp.or ∧ ∀ ρ x, Wv n C ρ x (n + j) = (Wv n C ρ x w || Wv n C ρ x v))) := by
  obtain ⟨h1, h2⟩ := h.2.2 _ (List.getElem_mem hj)
  have hop := (h.1 _ (List.getElem_mem hj)).1
  have hg := fun ρ x => Wg h ρ x j hj
  generalize hl : C.gates[j].inputs = l at *
  have hop' : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or ∨ C.gates[j].op = GateOp.not := by simpa using hop
  rcases hop' with ho | ho | ho
  · rw [ho] at h2
    have h2' : l.length = 2 := by simpa [GateOp.eval] using h2
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 h2'
    right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨b, by simp, by simp, Or.inl ⟨ho, fun ρ x => by rw [hg, ho]; simp [GateOp.eval]⟩⟩
    · exact ⟨a, by simp, by simp; , Or.inl ⟨ho, fun ρ x => by rw [hg, ho]; simp [GateOp.eval, Bool.and_comm]⟩⟩
  · rw [ho] at h2
    have h2' : l.length = 2 := by simpa [GateOp.eval] using h2
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 h2'
    right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨b, by simp, by simp, Or.inr ⟨ho, fun ρ x => by rw [hg, ho]; simp [GateOp.eval]⟩⟩
    · exact ⟨a, by simp, by simp; , Or.inr ⟨ho, fun ρ x => by rw [hg, ho]; simp [GateOp.eval, Bool.or_comm]⟩⟩
  · rw [ho] at h2
    have h2' : l.length = 1 := by simpa [GateOp.eval] using h2
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 h2'
    left
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    subst hw
    exact ⟨ho, by simp, fun ρ x => by rw [hg, ho]; simp [GateOp.eval]⟩

theorem sem2 {n : ℕ} {C : Circuit} (h : Shp n C) (j : ℕ) (hj : j < C.gates.length) (w w' : ℕ) (hw : w ∈ C.gates[j].inputs) (hw' : w' ∈ C.gates[j].inputs) (hne : w' ≠ w) :
      (C.gates[j].op = GateOp.and ∧ ∀ ρ x, Wv n C ρ x (n + j) = (Wv n C ρ x w && Wv n C ρ x w')) ∨
       (C.gates[j].op = GateOp.or ∧ ∀ ρ x, Wv n C ρ x (n + j) = (Wv n C ρ x w || Wv n C ρ x w')) := by
  rcases sem h j hj w hw with ⟨_, h2, _⟩ | ⟨v, _, h2, h3⟩
  · exact absurd (h2 _ hw') hne
  · rcases h2 _ hw' with e | e
    · exact absurd e hne
    · rw [e]; exact h3

theorem redc {n : ℕ} {C : Circuit} (h : Shp n C) (ρ : (Fin n → Bool) → Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) (w : ℕ) (hw : w ∈ C.gates[j].inputs)
    (hc : Cst n C ρ w) : Cst n C ρ (n + j) ∨ ∃ v ∈ C.gates[j].inputs, ∀ x, Wv n C ρ x (n + j) = Wv n C ρ x v := by
  obtain ⟨b, hb⟩ := hc
  rcases sem h j hj w hw with ⟨_, _, h3⟩ | ⟨v, hv, _, ⟨_, h3⟩ | ⟨_, h3⟩⟩
  · exact Or.inl ⟨!b, fun x => by rw [h3, hb]⟩
  · cases b
    · exact Or.inl ⟨false, fun x => by rw [h3, hb]; rfl⟩
    · exact Or.inr ⟨v, hv, fun x => by rw [h3, hb]; simp⟩
  · cases b
    · exact Or.inr ⟨v, hv, fun x => by rw [h3, hb]; simp⟩
    · exact Or.inl ⟨true, fun x => by rw [h3, hb]; simp⟩

theorem redR {n : ℕ} {C : Circuit} (h : Shp n C) (ρ : (Fin n → Bool) → Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) (w : ℕ) (hw : w ∈ C.gates[j].inputs)
    (hc : Cst n C ρ w) : Red n C ρ j := by
  rcases redc h ρ j hj w hw hc with h1 | ⟨v, hv, h1⟩
  · exact Or.inl h1
  · exact Or.inr ⟨v, h.2.1 j hj v hv, h1⟩

theorem setrun (n : ℕ) (gs : List Gate) (t : ℕ) (ht : t < gs.length) (y : List Bool) (hy : y.length = n)
    (H : ∀ k (hk : k < gs.length), k ≠ t → gs[k].op.eval (gs[k].inputs.map fun i => if i < n + k then (if i = n + t then false else (run gs y).getD i false) else false) = (run gs y).getD (n + k) false) :
    ∀ w < n + gs.length, (run (gs.set t ⟨GateOp.or, []⟩) y).getD w false = if w = n + t then false else (run gs y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [if_neg (by omega), run_input _ _ _ (by omega), run_input _ _ _ (by omega)]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hwn)
      have hk : k < gs.length := by omega
      have e := run_gate (gs.set t ⟨GateOp.or, []⟩) y k (by rw [List.length_set]; exact hk)
      rw [hy] at e
      rw [e]
      by_cases hkt : k = t
      · subst hkt
        rw [if_pos rfl, List.getElem_set_self]
        rfl
      · rw [if_neg (by omega), List.getElem_set_ne (fun h => hkt h.symm), ← H k hk hkt]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split_ifs with h1 h2
        · rw [ih i (by omega) (by omega), if_pos h2]
        · rw [ih i (by omega) (by omega), if_neg h2]
        · rfl

theorem fanset (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C) (t o : ℕ) : PEqualNP.MetaComplexity.FanInTwo ⟨C.gates.set t ⟨GateOp.or, []⟩, o⟩ := by
  intro g hg
  rcases List.mem_or_eq_of_mem_set hg with h | rfl
  · exact hC g h
  · exact ⟨by simp, by simp⟩

theorem nored {n : ℕ} {C : Circuit} (hm : PEqualNP.MetaComplexity.IsMinimalCircuit n C) (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (j : ℕ) (hj : j < C.gates.length) : ¬Red n C (fun x => x) j := by
  intro hr
  obtain ⟨D, d1, d2, d3⟩ := engine n C (fun x => x) {j} hm.1 (fun i => Or.inr fun x => rfl) hnc (by
    intro k hk
    rw [Finset.mem_singleton] at hk
    subst hk
    exact ⟨hj, hr⟩)
  have := hm.2 D d1 (by funext x; exact d3 x)
  have hs : C.size = C.gates.length := rfl
  rw [Finset.card_singleton] at d2
  omega

theorem reader {n : ℕ} {C : Circuit} (h : Shp n C) (hm : PEqualNP.MetaComplexity.IsMinimalCircuit n C) (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (j : ℕ) (hj : j < C.gates.length) (ho : n + j ≠ C.output) : ∃ k, ∃ hk : k < C.gates.length, j < k ∧ n + j ∈ C.gates[k].inputs := by
  by_contra hcon
  have hno : ∀ k (hk : k < C.gates.length), n + j ∉ C.gates[k].inputs := by
    intro k hk hmem
    have := h.2.1 k hk _ hmem
    exact hcon ⟨k, hk, by omega, hmem⟩
  let C' : Circuit := ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩
  have hrun : ∀ x : Fin n → Bool, ∀ w < n + C.gates.length, (run C'.gates (List.ofFn x)).getD w false = if w = n + j then false else (run C.gates (List.ofFn x)).getD w false := by
    intro x
    refine setrun n C.gates j hj _ (by simp) ?_
    intro k hk hkj
    have e := run_gate C.gates (List.ofFn x) k hk
    rw [List.length_ofFn] at e
    rw [e]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hh : ¬ i = n + j := fun hh => hno k hk (by rw [← hh]; exact hi)
    simp only [if_neg hh, List.length_ofFn]
  have hlen : C'.gates.length = C.gates.length := List.length_set
  have hev : ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro x
    change (run C'.gates (List.ofFn x)).getD C.output false = (run C.gates (List.ofFn x)).getD C.output false
    by_cases hlt : C.output < n + C.gates.length
    · rw [hrun x _ hlt, if_neg (fun hh => ho hh.symm)]
    · rw [List.getD_eq_default _ _ (by rw [run_length, hlen]; simp; omega), List.getD_eq_default _ _ (by rw [run_length]; simp; omega)]
  obtain ⟨D, d1, d2, d3⟩ := engine n C' (fun x => x) {j} (fanset C hm.1 j C.output) (fun i => Or.inr fun x => rfl) (by
      obtain ⟨x, y, hxy⟩ := hnc
      exact ⟨x, y, by rw [hev, hev]; exact hxy⟩) (by
    intro k hk
    rw [Finset.mem_singleton] at hk
    subst hk
    refine ⟨by rw [hlen]; exact hj, Or.inl ⟨false, fun x => ?_⟩⟩
    have := hrun x (n + k) (by omega)
    rw [if_pos rfl] at this
    exact this)
  have := hm.2 D d1 (by funext x; exact (d3 x).trans (hev x))
  have hs : C.size = C.gates.length := rfl
  have hs' : C'.size = C.gates.length := hlen
  rw [Finset.card_singleton] at d2
  omega

theorem nout {n : ℕ} {C : Circuit} {ρ : (Fin n → Bool) → Fin n → Bool} (hne : ∃ x y, C.eval (List.ofFn (ρ x)) ≠ C.eval (List.ofFn (ρ y))) (w : ℕ) (hc : Cst n C ρ w) : w ≠ C.output := by
  rintro rfl
  obtain ⟨x, y, hxy⟩ := hne
  obtain ⟨b, hb⟩ := hc
  exact hxy ((hb x).trans (hb y).symm)

theorem resne {n : ℕ} {C : Circuit} {i0 : Fin n} (hne : ∃ x y, C.eval (List.ofFn (Res n i0 x)) ≠ C.eval (List.ofFn (Res n i0 y))) :
    ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
  obtain ⟨x, y, h⟩ := hne
  exact ⟨_, _, h⟩

theorem fin4 {n : ℕ} {C : Circuit} (h : Shp n C) {i0 : Fin n} (hne : ∃ x y, C.eval (List.ofFn (Res n i0 x)) ≠ C.eval (List.ofFn (Res n i0 y)))
    (a b c d : ℕ) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : a < C.gates.length ∧ Red n C (Res n i0) a) (hb : b < C.gates.length ∧ Red n C (Res n i0) b)
    (hc : c < C.gates.length ∧ Red n C (Res n i0) c) (hd : d < C.gates.length ∧ Red n C (Res n i0) d) :
    ∃ s, s + 4 ≤ C.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x => C.eval (List.ofFn (Res n i0 x))) s := by
  classical
  have hcard : ({a, b, c, d} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]), Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
  have hF : ∀ j ∈ ({a, b, c, d} : Finset ℕ), j < C.gates.length ∧ Red n C (Res n i0) j := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have hle : 4 ≤ C.size := by
    rw [← hcard]
    refine (Finset.card_le_card (fun j hj => Finset.mem_range.2 (hF j hj).1)).trans ?_
    rw [Finset.card_range]
    exact le_rfl
  have := engine n C (Res n i0) {a, b, c, d} h.1 (by
      intro i
      by_cases hi : i = i0
      · subst hi; exact Or.inl ⟨false, fun x => by simp [Res]⟩
      · exact Or.inr fun x => by simp [Res, Function.update_of_ne hi]) hne hF
  rw [hcard] at this
  exact ⟨C.size - 4, by omega, this⟩

theorem filt (gs : List Gate) (P : Gate → Bool) (r : ℕ) (hr : r < gs.length) (hP : P gs[r] = true) :
    gs.filter P = (gs.take r).filter P ++ gs[r] :: (gs.drop (r + 1)).filter P := by
  conv_lhs => rw [← List.take_append_drop r gs, List.drop_eq_getElem_cons hr]
  rw [List.filter_append, List.filter_cons_of_pos hP]

theorem filt1 (gs : List Gate) (P : Gate → Bool) (r : ℕ) (hr : r < gs.length) (hP : P gs[r] = true) (hu : ∀ k (hk : k < gs.length), P gs[k] = true → k = r) :
    gs.filter P = [gs[r]] := by
  have h1 : (gs.take r).filter P = [] := by
    rw [List.filter_eq_nil_iff]
    intro g hg hPg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    rw [List.length_take] at hk
    rw [List.getElem_take] at hPg
    have := hu k (by omega) hPg
    omega
  have h2 : (gs.drop (r + 1)).filter P = [] := by
    rw [List.filter_eq_nil_iff]
    intro g hg hPg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    rw [List.length_drop] at hk
    rw [List.getElem_drop] at hPg
    have := hu _ (by omega) hPg
    omega
  rw [filt gs P r hr hP, h1, h2]
  rfl

theorem filt2 (gs : List Gate) (P : Gate → Bool) (g : Gate) (h : gs.filter P = [g]) : ∃ r, ∃ hr : r < gs.length, gs[r] = g ∧ P gs[r] = true ∧ ∀ k (hk : k < gs.length), P gs[k] = true → k = r := by
  have hmem : g ∈ gs.filter P := by rw [h]; simp
  rw [List.mem_filter] at hmem
  obtain ⟨r, hr, e⟩ := List.getElem_of_mem hmem.1
  have hP : P gs[r] = true := by rw [e]; exact hmem.2
  refine ⟨r, hr, e, hP, ?_⟩
  intro k hk hPk
  have hlen : (gs.filter P).length = 1 := by rw [h]; rfl
  by_contra hne
  have e1 := filt gs P r hr hP
  have e2 := congrArg List.length e1
  rw [hlen, List.length_append, List.length_cons] at e2
  have h1 : (gs.take r).filter P = [] := List.length_eq_zero_iff.1 (by omega)
  have h2 : (gs.drop (r + 1)).filter P = [] := List.length_eq_zero_iff.1 (by omega)
  rw [List.filter_eq_nil_iff] at h1 h2
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · refine h1 gs[k] ?_ hPk
    rw [List.mem_take_iff_getElem]
    exact ⟨k, by omega, rfl⟩
  · refine h2 gs[k] ?_ hPk
    rw [List.mem_iff_getElem]
    refine ⟨k - (r + 1), by rw [List.length_drop]; omega, ?_⟩
    rw [List.getElem_drop]
    congr 1
    omega

theorem engine2 {X : Type} (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + F.card ≤ C.size ∧ (∀ x, D.eval (tgt x) = C.eval (src x)) ∧ ∀ w < n + C.gates.length, ∃ r : Bool ⊕ ℕ, ∀ x, (run C.gates (src x)).getD w false = rv (run D.gates (tgt x)) r := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then .inr h.choose else if hb : ∃ b, ∀ x, (src x).getD w false = b then .inl hb.choose else .inl false, by simp, by simp, ?_, ?_⟩
      · intro w t hw ht
        beta_reduce at ht
        split_ifs at ht with h1 h2
        cases ht
        simpa using h1.choose_spec.1
      · intro x w hw
        simp only [Nat.add_zero] at hw
        rw [run_input _ _ _ (by rw [hsrc]; exact hw)]
        beta_reduce
        split_ifs with h1 h2
        · exact h1.choose_spec.2 x
        · exact h2.choose_spec x
        · rcases h0 w hw with h | h
          · exact absurd h h2
          · exact absurd h h1
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      -- extend with a value for wire `n + k`
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, fok g) → (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he hr hlen hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (rv_ext hs e (tgt x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            rw [htgt]; exact this
      by_cases hkF : k ∈ F
      · rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by simp [hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, e2, e3, e4⟩ := emit M hs C.gates[k].op hop (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e3 (by simp [hkF]; exact e1) (fun x => ?_)
        rw [e4 _ (htgt x)]
        have rg := run_gate C.gates (src x) k hk'
        rw [hsrc] at rg
        rw [rg, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp, m']
        split_ifs with h
        · exact h4 x i h
        · rfl
  obtain ⟨hs, m, h1, h2, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : (F.filter fun j => j < C.gates.length) = F := Finset.filter_true_of_mem fun j hj => (hF j hj).1
  rw [hFc] at h2
  have hout : C.output < n + C.gates.length := by
    by_contra h
    refine hne ⟨false, fun x => ?_⟩
    change (run C.gates (src x)).getD C.output false = false
    rw [List.getD_eq_default _ _ (by rw [run_length, hsrc]; omega)]
  have hev : ∀ x, C.eval (src x) = rv (run hs (tgt x)) (m C.output) := fun x => h4 x _ hout
  rcases hm : m C.output with b | t
  · exact absurd ⟨b, fun x => by rw [hev, hm]; rfl⟩ hne
  · refine ⟨⟨hs, t⟩, ?_, h2, fun x => ?_, fun w hw => ⟨m w, fun x => h4 x w hw⟩⟩
    · intro g hg
      exact ⟨by simpa using (h1 g hg).1, (h1 g hg).2⟩
    · have := hev x
      rw [hm] at this
      exact this.symm

theorem prop {N : ℕ} {C : Circuit} (h : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < N + j) (B : ℕ → Prop) (x y : Fin N → Bool)
    (hi : ∀ i : Fin N, ¬B i → x i = y i)
    (hg : ∀ k (hk : k < C.gates.length), ¬B (N + k) → (∃ w ∈ C.gates[k].inputs, B w) → Wv N C (fun x => x) x (N + k) = Wv N C (fun x => x) y (N + k)) :
    ∀ w, ¬B w → Wv N C (fun x => x) x w = Wv N C (fun x => x) y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < N
    · have e1 := Wi C (fun x => x) x ⟨w, h1⟩
      have e2 := Wi C (fun x => x) y ⟨w, h1⟩
      simp only at e1 e2
      rw [e1, e2]; exact hi ⟨w, h1⟩ hw
    · by_cases h2 : w < N + C.gates.length
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h1)
        have hk : k < C.gates.length := by omega
        by_cases hb : ∃ u ∈ C.gates[k].inputs, B u
        · exact hg k hk hw hb
        · have r1 := run_gate C.gates (List.ofFn x) k hk
          have r2 := run_gate C.gates (List.ofFn y) k hk
          rw [List.length_ofFn] at r1 r2
          simp only [Wv]
          rw [r1, r2]
          congr 1
          refine List.map_congr_left fun i hi' => ?_
          rw [if_pos (h k hk i hi'), if_pos (h k hk i hi')]
          exact ih i (h k hk i hi') (fun hB => hb ⟨i, hi', hB⟩)
      · simp only [Wv]
        rw [List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega), List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)]

def nm (g : Gate) : Gate := ⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩

theorem nm_run (gs : List Gate) (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (d : List Bool) : run (gs.map nm) d = run gs d := by
  induction gs generalizing d with
  | nil => rfl
  | cons g gs ih =>
    have e : (nm g).op.eval ((nm g).inputs.map fun i => d.getD i false) = g.op.eval (g.inputs.map fun i => d.getD i false) := by
      obtain ⟨o, l⟩ := g
      rcases hop _ List.mem_cons_self with rfl | rfl | rfl
      · simp [nm, GateOp.eval]
      · simp [nm, GateOp.eval]
      · rcases l with _ | ⟨a, l⟩ <;> simp [nm, GateOp.eval]
    simp only [run, List.map_cons, List.foldl_cons]
    rw [e]
    exact ih (fun g' h' => hop g' (List.mem_cons_of_mem _ h')) _

theorem shp {N : ℕ} {C : Circuit} (hm : PEqualNP.MetaComplexity.IsMinimalCircuit N C) (hnc : ∃ x y : Fin N → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (hb : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < N + j) (hl : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) : Shp N C := by
  refine ⟨hm.1, hb, fun g hg => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  have hop : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or ∨ C.gates[j].op = GateOp.not := by simpa using (hm.1 _ hg).1
  have h2 := (hm.1 _ hg).2
  have hl' := hl _ hg
  have hr := nored hm hnc j hj
  have hbj := hb j hj
  have wg : ∀ x, Wv N C (fun x => x) x (N + j) = C.gates[j].op.eval (C.gates[j].inputs.map fun i => Wv N C (fun x => x) x i) := by
    intro x
    have r1 := run_gate C.gates (List.ofFn x) j hj
    rw [List.length_ofFn] at r1
    simp only [Wv]
    rw [r1]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    rw [if_pos (hbj i hi)]
  generalize C.gates[j].inputs = l at h2 hl' hbj wg
  generalize C.gates[j].op = o at hop hl' wg
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · exact absurd (Or.inl ⟨o.eval [], fun x => by rw [wg]; rfl⟩) hr
  · rcases hop with rfl | rfl | rfl
    · exact absurd (Or.inr ⟨a, hbj a (by simp), fun x => by rw [wg]; simp [GateOp.eval]⟩) hr
    · exact absurd (Or.inr ⟨a, hbj a (by simp), fun x => by rw [wg]; simp [GateOp.eval]⟩) hr
    · simp [GateOp.eval]
  · have hab : a ≠ b := by
      rintro rfl
      rcases hop with rfl | rfl | rfl
      · exact hr (Or.inr ⟨a, hbj a (by simp), fun x => by rw [wg]; simp [GateOp.eval]⟩)
      · exact hr (Or.inr ⟨a, hbj a (by simp), fun x => by rw [wg]; simp [GateOp.eval]⟩)
      · have := hl' rfl; simp at this
    rcases hop with rfl | rfl | rfl
    · simp [GateOp.eval, hab]
    · simp [GateOp.eval, hab]
    · have := hl' rfl; simp at this
  · simp at h2


theorem shpF {N : ℕ} {C : Circuit} (hm : PEqualNP.MetaComplexity.IsMinimalCircuit N C) (hnc : ∃ x y : Fin N → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (hl : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) : Shp N C := by
  have hb : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < N + j := by
    intro j hj i hi
    by_contra hlt
    have hop : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or ∨ C.gates[j].op = GateOp.not := by simpa using (hm.1 _ (List.getElem_mem hj)).1
    have h2 := (hm.1 _ (List.getElem_mem hj)).2
    have hl' := hl _ (List.getElem_mem hj)
    have hr := nored hm hnc j hj
    have wg : ∀ x, Wv N C (fun x => x) x (N + j) = C.gates[j].op.eval (C.gates[j].inputs.map fun i => if i < N + j then Wv N C (fun x => x) x i else false) := by
      intro x
      have r1 := run_gate C.gates (List.ofFn x) j hj
      rw [List.length_ofFn] at r1
      exact r1
    have cp : ∀ b, (∀ x, Wv N C (fun x => x) x (N + j) = if b < N + j then Wv N C (fun x => x) x b else false) → Red N C (fun x => x) j := by
      intro b hb
      by_cases h : b < N + j
      · exact Or.inr ⟨b, h, fun x => by rw [hb, if_pos h]⟩
      · exact Or.inl ⟨false, fun x => by rw [hb, if_neg h]⟩
    generalize C.gates[j].inputs = l at hi h2 hl' wg
    generalize C.gates[j].op = o at hop hl' wg
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · cases hi
    · have ha : i = a := by simpa using hi
      subst ha
      exact hr (Or.inl ⟨o.eval [false], fun x => by rw [wg]; simp only [List.map_cons, List.map_nil, if_neg hlt]⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · rcases hop with rfl | rfl | rfl
        · exact hr (Or.inl ⟨false, fun x => by rw [wg]; simp only [List.map_cons, List.map_nil, if_neg hlt]; rfl⟩)
        · exact hr (cp b fun x => by rw [wg]; simp only [List.map_cons, List.map_nil, if_neg hlt]; simp [GateOp.eval])
        · have := hl' rfl; simp at this
      · rcases hop with rfl | rfl | rfl
        · exact hr (Or.inl ⟨false, fun x => by rw [wg]; simp only [List.map_cons, List.map_nil, if_neg hlt]; simp [GateOp.eval]⟩)
        · exact hr (cp a fun x => by rw [wg]; simp only [List.map_cons, List.map_nil, if_neg hlt]; simp [GateOp.eval])
        · have := hl' rfl; simp at this
    · simp at h2
  exact shp hm hnc hb hl

theorem least {N : ℕ} (f : (Fin N → Bool) → Bool) (hf : ∃ x y, f x ≠ f y) (s : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize N f s) :
    ∃ C : Circuit, Shp N C ∧ PEqualNP.MetaComplexity.IsMinimalCircuit N C ∧ (∀ x, C.eval (List.ofFn x) = f x) ∧ C.size ≤ s := by
  classical
  have hex : ∃ k, ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ (∀ x, D.eval (List.ofFn x) = f x) ∧ D.size = k := by
    obtain ⟨D, d1, d2, d3⟩ := h
    exact ⟨_, D, d1, d3, rfl⟩
  obtain ⟨D, d1, d2, d3⟩ := Nat.find_spec hex
  have hs : D.size ≤ s := by
    obtain ⟨E, e1, e2, e3⟩ := h
    rw [d3]
    exact (Nat.find_min' hex ⟨E, e1, e3, rfl⟩).trans e2
  have hops : ∀ q ∈ D.gates, q.op = GateOp.and ∨ q.op = GateOp.or ∨ q.op = GateOp.not := fun q hq => by simpa using (d1 q hq).1
  let C : Circuit := ⟨D.gates.map nm, D.output⟩
  have hev : ∀ y, C.eval y = D.eval y := by
    intro y
    have := nm_run D.gates hops y
    change (run (D.gates.map nm) y).getD D.output false = _
    rw [this]; rfl
  have hlen : C.size = D.size := by simp [C, Circuit.size]
  have hC : PEqualNP.MetaComplexity.IsMinimalCircuit N C := by
    refine ⟨?_, fun E hE hfE => ?_⟩
    · intro q hq
      obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
      obtain ⟨h1, h2⟩ := d1 q' hq'
      refine ⟨h1, ?_⟩
      simp only [nm]
      split_ifs
      · rw [List.length_take]; omega
      · exact h2
    · rw [hlen, d3]
      exact Nat.find_min' hex ⟨E, hE, fun x => (congrFun hfE x).trans ((hev _).trans (d2 x)), rfl⟩
  have hfC : ∀ x, C.eval (List.ofFn x) = f x := fun x => (hev _).trans (d2 x)
  refine ⟨C, shpF hC ?_ ?_, hC, hfC, by rw [hlen]; exact hs⟩
  · obtain ⟨x, y, hxy⟩ := hf
    exact ⟨x, y, by rw [hfC, hfC]; exact hxy⟩
  · intro q hq hqo
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    have hqo' : q'.op = GateOp.not := hqo
    simp only [nm]
    rw [if_pos (by rw [hqo']; rfl), List.length_take]
    omega

theorem eng {n : ℕ} {C : Circuit} (hm : PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C) (i0 : Fin (n + 1)) (b : Bool)
    (hne : ∃ x y : Fin n → Bool, C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) b x)) ≠ C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) b y)))
    (F : Finset ℕ) (hF : ∀ j ∈ F, j < C.gates.length ∧ Red (n + 1) C (fun y => Function.update y i0 b) j) :
    ∃ s', PEqualNP.MetaComplexity.HasCircuitSize n (fun x => C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) b x))) s' ∧ s' + F.card ≤ C.size := by
  have hρ : ∀ x : Fin n → Bool, Function.update (i0.insertNth (α := fun _ => Bool) b x) i0 b = i0.insertNth (α := fun _ => Bool) b x := fun x => Fin.update_insertNth _ _ _ _
  obtain ⟨D, d1, d2, d3, _⟩ := engine2 (n + 1) n C (fun x : Fin n → Bool => List.ofFn (i0.insertNth (α := fun _ => Bool) b x)) (fun x => List.ofFn x) (fun x => List.length_ofFn) (fun x => List.length_ofFn) F hm.1 (by
    intro w hw
    have ew : ∀ x : Fin n → Bool, (List.ofFn (i0.insertNth (α := fun _ => Bool) b x)).getD w false = i0.insertNth (α := fun _ => Bool) b x ⟨w, hw⟩ := fun x => by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hw), List.getElem_ofFn]
    by_cases he : (⟨w, hw⟩ : Fin (n + 1)) = i0
    · refine Or.inl ⟨b, fun x => ?_⟩
      rw [ew, he]
      simp
    · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq he
      refine Or.inr ⟨k, k.isLt, fun x => ?_⟩
      rw [ew, ← hk, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      simp) (by
    rintro ⟨c, hb'⟩
    obtain ⟨x, y, h⟩ := hne
    exact h ((hb' x).trans (hb' y).symm)) (by
    intro j hj
    obtain ⟨h1, h2⟩ := hF j hj
    refine ⟨h1, ?_⟩
    rcases h2 with ⟨c, hb'⟩ | ⟨w, hw, h2⟩
    · refine Or.inl ⟨c, fun x => ?_⟩
      have := hb' (i0.insertNth (α := fun _ => Bool) b x)
      simp only [Wv] at this
      rw [hρ] at this
      exact this
    · refine Or.inr ⟨w, hw, fun x => ?_⟩
      have := h2 (i0.insertNth (α := fun _ => Bool) b x)
      simp only [Wv] at this
      rw [hρ] at this
      exact this)
  exact ⟨D.size, ⟨D, d1, le_rfl, d3⟩, d2⟩

theorem rdex {n : ℕ} {C : Circuit} (hS : Shp (n + 1) C) (i0 : Fin (n + 1)) (b : Bool)
    (hne : ∃ x y : Fin n → Bool, C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) b x)) ≠ C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) b y)))
    (hd : ∃ x : Fin n → Bool, C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) false x)) ≠ C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) true x))) :
    ∃ k, ∃ hk : k < C.gates.length, (i0 : ℕ) ∈ C.gates[k].inputs := by
  by_contra hcon
  obtain ⟨x0, hx⟩ := hd
  have hi : ∀ i : Fin (n + 1), i ≠ i0 → i0.insertNth (α := fun _ => Bool) false x0 i = i0.insertNth (α := fun _ => Bool) true x0 i := by
    intro i hi
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
    simp
  have oi : C.output ≠ (i0 : ℕ) := by
    intro ho
    obtain ⟨x, y, h⟩ := hne
    apply h
    have e : ∀ z : Fin n → Bool, C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) b z)) = b := by
      intro z
      have := Wi C (fun x => x) (i0.insertNth (α := fun _ => Bool) b z) i0
      simp only [Wv] at this
      change (run C.gates _).getD C.output false = b
      rw [ho, this]
      simp
    rw [e, e]
  have := prop hS.2.1 (fun w => w = (i0 : ℕ)) (i0.insertNth (α := fun _ => Bool) false x0) (i0.insertNth (α := fun _ => Bool) true x0) (fun i h => hi i (fun e => h (congrArg Fin.val e))) (by
    rintro k hk _ ⟨w, hw, rfl⟩
    exact absurd ⟨k, hk, hw⟩ hcon) C.output oi
  exact hx this

theorem cst0 {n : ℕ} (C : Circuit) (i0 : Fin (n + 1)) (b : Bool) : Cst (n + 1) C (fun y => Function.update y i0 b) i0 :=
  ⟨b, fun x => by rw [Wi]; simp⟩

theorem red1 (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (i0 : Fin (n + 1)) (b : Bool)
    (hne : ∃ x y : Fin n → Bool, f (i0.insertNth (α := fun _ => Bool) b x) ≠ f (i0.insertNth (α := fun _ => Bool) b y))
    (hd : ∃ x : Fin n → Bool, f (i0.insertNth (α := fun _ => Bool) false x) ≠ f (i0.insertNth (α := fun _ => Bool) true x)) (k : ℕ)
    (hk : ∀ s, PEqualNP.MetaComplexity.HasCircuitSize n (fun x => f (i0.insertNth (α := fun _ => Bool) b x)) s → k ≤ s) (s : ℕ)
    (h : PEqualNP.MetaComplexity.HasCircuitSize (n + 1) f s) : k + 1 ≤ s := by
  obtain ⟨C, hS, hm, hf, hs⟩ := least f (by obtain ⟨x, y, h⟩ := hne; exact ⟨_, _, h⟩) s h
  have hne' : ∃ x y : Fin n → Bool, C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) b x)) ≠ C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) b y)) := by
    obtain ⟨x, y, h⟩ := hne; exact ⟨x, y, by rw [hf, hf]; exact h⟩
  obtain ⟨g, hg, mg⟩ := rdex hS i0 b hne' (by obtain ⟨x, h⟩ := hd; exact ⟨x, by rw [hf, hf]; exact h⟩)
  obtain ⟨s', h1, h2⟩ := eng hm i0 b hne' {g} (by
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    exact ⟨hg, redR hS _ j hg _ mg (cst0 C i0 b)⟩)
  simp only [hf] at h1
  have := hk s' h1
  rw [Finset.card_singleton] at h2
  omega

theorem red2 (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (i0 : Fin (n + 1))
    (hne : ∀ b, ∃ x y : Fin n → Bool, f (i0.insertNth (α := fun _ => Bool) b x) ≠ f (i0.insertNth (α := fun _ => Bool) b y))
    (hd : ∃ x : Fin n → Bool, f (i0.insertNth (α := fun _ => Bool) false x) ≠ f (i0.insertNth (α := fun _ => Bool) true x)) (k : ℕ)
    (hk : ∀ b s, PEqualNP.MetaComplexity.HasCircuitSize n (fun x => f (i0.insertNth (α := fun _ => Bool) b x)) s → k ≤ s) (s : ℕ)
    (h : PEqualNP.MetaComplexity.HasCircuitSize (n + 1) f s) : k + 2 ≤ s := by
  obtain ⟨C, hS, hm, hf, hs⟩ := least f (by obtain ⟨x, y, h⟩ := hne false; exact ⟨_, _, h⟩) s h
  have hne' : ∀ b, ∃ x y : Fin n → Bool, C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) b x)) ≠ C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) b y)) := by
    intro b
    obtain ⟨x, y, h⟩ := hne b; exact ⟨x, y, by rw [hf, hf]; exact h⟩
  have hnc : ∃ x y : Fin (n + 1) → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
    obtain ⟨x, y, h⟩ := hne' false; exact ⟨_, _, h⟩
  obtain ⟨g, hg, mg⟩ := rdex hS i0 false (hne' false) (by obtain ⟨x, h⟩ := hd; exact ⟨x, by rw [hf, hf]; exact h⟩)
  have fin : ∀ (b : Bool) (a c : ℕ), a ≠ c → (a < C.gates.length ∧ Red (n + 1) C (fun y => Function.update y i0 b) a) → (c < C.gates.length ∧ Red (n + 1) C (fun y => Function.update y i0 b) c) → k + 2 ≤ s := by
    intro b a c hac ha hc
    obtain ⟨s', h1, h2⟩ := eng hm i0 b (hne' b) {a, c} (by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact ha
      · exact hc)
    simp only [hf] at h1
    have := hk b s' h1
    rw [Finset.card_pair hac] at h2
    omega
  by_cases h2 : ∃ g2, ∃ hg2 : g2 < C.gates.length, g2 ≠ g ∧ (i0 : ℕ) ∈ C.gates[g2].inputs
  · obtain ⟨g2, hg2, hne2, mg2⟩ := h2
    exact fin false g2 g hne2 ⟨hg2, redR hS _ g2 hg2 _ mg2 (cst0 C i0 false)⟩ ⟨hg, redR hS _ g hg _ mg (cst0 C i0 false)⟩
  · have go : ∀ b : Bool, Cst (n + 1) C (fun y => Function.update y i0 b) (n + 1 + g) → k + 2 ≤ s := by
      intro b hc
      have hneR : ∃ x y, C.eval (List.ofFn ((fun y : Fin (n + 1) → Bool => Function.update y i0 b) x)) ≠ C.eval (List.ofFn ((fun y : Fin (n + 1) → Bool => Function.update y i0 b) y)) := by
        obtain ⟨x, y, h⟩ := hne' b
        refine ⟨i0.insertNth (α := fun _ => Bool) b x, i0.insertNth (α := fun _ => Bool) b y, ?_⟩
        simp only [Fin.update_insertNth]
        exact h
      obtain ⟨r, hr, hgr, mr⟩ := reader hS hm hnc g hg (nout hneR _ hc)
      exact fin b g r (by omega) ⟨hg, Or.inl hc⟩ ⟨hr, redR hS _ r hr _ mr hc⟩
    have w0 : ∀ (b : Bool) x, Wv (n + 1) C (fun y => Function.update y i0 b) x i0 = b := fun b x => by rw [Wi]; simp
    rcases sem hS g hg _ mg with ⟨_, _, h3⟩ | ⟨v, _, _, ⟨_, h3⟩ | ⟨_, h3⟩⟩
    · exact go false ⟨true, fun x => by rw [h3, w0]; rfl⟩
    · exact go false ⟨false, fun x => by rw [h3, w0]; rfl⟩
    · exact go true ⟨true, fun x => by rw [h3, w0]; rfl⟩

theorem red0 (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (i0 : Fin (n + 1)) (b : Bool)
    (hne : ∃ x y : Fin n → Bool, f (i0.insertNth (α := fun _ => Bool) b x) ≠ f (i0.insertNth (α := fun _ => Bool) b y)) (k : ℕ)
    (hk : ∀ s, PEqualNP.MetaComplexity.HasCircuitSize n (fun x => f (i0.insertNth (α := fun _ => Bool) b x)) s → k ≤ s) (s : ℕ)
    (h : PEqualNP.MetaComplexity.HasCircuitSize (n + 1) f s) : k ≤ s := by
  obtain ⟨C, hS, hm, hf, hs⟩ := least f (by obtain ⟨x, y, h⟩ := hne; exact ⟨_, _, h⟩) s h
  obtain ⟨s', h1, h2⟩ := eng hm i0 b (by obtain ⟨x, y, h⟩ := hne; exact ⟨x, y, by rw [hf, hf]; exact h⟩) ∅ (by simp)
  simp only [hf] at h1
  have := hk s' h1
  rw [Finset.card_empty] at h2
  omega

end S

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



def rho (n d i : ℕ) : ℕ := if i < n + d then i else i - 1

def fx (n d L j i : ℕ) : ℕ := if i < n + j then rho n d i else n + L

def ng (n : ℕ) (gs : List Gate) (d : ℕ) : List Gate :=
  List.ofFn fun k : Fin (gs.length - 1) =>
    let j := if k.val < d then k.val else k.val + 1
    let h := gs.getD j ⟨GateOp.or, []⟩
    ⟨h.op, h.inputs.map (fx n d gs.length j)⟩

theorem ng_len (n : ℕ) (gs : List Gate) (d : ℕ) : (ng n gs d).length = gs.length - 1 := by
  simp [ng]

theorem sem (n : ℕ) (gs : List Gate) (d : ℕ) (hd : d < gs.length)
    (hno : ∀ (j : ℕ) (hj : j < gs.length), d < j → n + d ∉ gs[j].inputs)
    (x : List Bool) (hx : x.length = n) :
    ∀ w, w < n + gs.length → w ≠ n + d →
      (run (ng n gs d) x).getD (rho n d w) false = (run gs x).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hwd
    by_cases h9 : w < n
    · rw [rho, if_pos (by omega), run_input _ _ _ (by omega), run_input _ _ _ (by omega)]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < gs.length := by omega
      have old := run_gate gs x j hj
      rw [hx] at old
      rw [old]
      obtain ⟨k, hkj, hkL, hr⟩ : ∃ k, (if k < d then k else k + 1) = j ∧
          k < gs.length - 1 ∧ rho n d (n + j) = n + k := by
        by_cases h : j < d
        · exact ⟨j, by rw [if_pos h], by omega, by unfold rho; split_ifs <;> omega⟩
        · exact ⟨j - 1, by rw [if_neg (by omega)]; omega, by omega, by
            unfold rho; split_ifs <;> omega⟩
      have new := run_gate (ng n gs d) x k (by rw [ng_len]; omega)
      rw [hx] at new
      have e : (ng n gs d)[k]'(by rw [ng_len]; omega) =
          ⟨gs[j].op, gs[j].inputs.map (fx n d gs.length j)⟩ := by
        have hgd : gs.getD j ⟨GateOp.or, []⟩ = gs[j] := List.getD_eq_getElem _ _ hj
        simp only [ng, List.getElem_ofFn, hkj, hgd]
      rw [hr, new, e, List.map_map]
      refine congrArg _ (List.map_congr_left fun i hi => ?_)
      simp only [Function.comp]
      by_cases hij : i < n + j
      · have hne : i ≠ n + d := by
          rintro rfl
          exact hno j hj (by omega) hi
        have hlt : rho n d i < n + k := by
          by_cases hkd : k < d
          · rw [if_pos hkd] at hkj
            unfold rho; split_ifs <;> omega
          · rw [if_neg hkd] at hkj
            unfold rho; split_ifs <;> omega
        have hfx : fx n d gs.length j i = rho n d i := if_pos hij
        rw [hfx, if_pos hlt, if_pos hij]
        exact ih i hij (by omega) hne
      · have hfx : fx n d gs.length j i = n + gs.length := if_neg hij
        rw [hfx, if_neg hij, if_neg (by omega)]

theorem del (n : ℕ) (C : Circuit) (hC : FanInTwo C) (d : ℕ) (hd : d < C.gates.length)
    (hno : ∀ (j : ℕ) (hj : j < C.gates.length), d < j → n + d ∉ C.gates[j].inputs)
    (ho : C.output ≠ n + d) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 = C.size ∧ circuitFun n D = circuitFun n C := by
  let o := if C.output < n + C.gates.length then rho n d C.output else n + C.gates.length
  refine ⟨⟨ng n C.gates d, o⟩, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hh
    have hj : (if k.val < d then k.val else k.val + 1) < C.gates.length := by
      have := k.isLt
      split_ifs <;> omega
    dsimp only
    rw [List.getD_eq_getElem _ _ hj]
    have := hC _ (List.getElem_mem hj)
    exact ⟨this.1, by simpa using this.2⟩
  · change (ng n C.gates d).length + 1 = C.gates.length
    rw [ng_len]; omega
  · funext x
    change (run (ng n C.gates d) (List.ofFn x)).getD o false =
      (run C.gates (List.ofFn x)).getD C.output false
    by_cases h : C.output < n + C.gates.length
    · simp only [o, if_pos h]
      exact sem n _ d hd hno _ (by simp) _ h ho
    · simp only [o, if_neg h]
      rw [List.getD_eq_default _ _ (by rw [run_length, ng_len, List.length_ofFn]; omega),
        List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)]





def rds (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

theorem eval_congr (g : Gate) (u v : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (huv : ∀ i ∈ rds g, u i = v i) : g.op.eval (g.inputs.map u) = g.op.eval (g.inputs.map v) := by
  rcases hop with h | h | h
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [h]
    cases hi : g.inputs with
    | nil => rfl
    | cons a t =>
      have := huv a (by simp [hi])
      simp [GateOp.eval, this]

theorem getD_sn (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem indep (v : ℕ) (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hno : ∀ g ∈ gs, v ∉ rds g) (x y : List Bool) (hl : x.length = y.length)
    (hxy : ∀ i, i ≠ v → x.getD i false = y.getD i false) :
    ∀ i, i ≠ v → (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simpa [run] using hxy
  | append_singleton gs g ih =>
    have ih' := ih (fun g' h => hop g' (by simp [h])) (fun g' h => hno g' (by simp [h]))
    intro i hi
    have e : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) =
        g.op.eval (g.inputs.map fun i => (run gs y).getD i false) :=
      eval_congr g _ _ (hop g (by simp)) fun k hk =>
        ih' k fun hc => hno g (by simp) (hc ▸ hk)
    rw [run_snoc, run_snoc, getD_sn, getD_sn, run_length, run_length, hl, e]
    split_ifs
    · rfl
    · exact ih' i hi


def fn (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 ||
    x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def X0 (u t : Fin 9) : Fin 9 → Bool := fun i => decide (i = u) || decide (i = t)

def X1 (u t v : Fin 9) : Fin 9 → Bool := fun i => decide (i = u) || decide (i = t) || decide (i = v)

def picks : List ℕ → List (ℕ × List ℕ)
  | [] => []
  | a :: l => (a, l) :: (picks l).map fun q => (q.1, a :: q.2)

theorem picks_mem (V : ℕ → ℕ) : ∀ (U : List ℕ) (i : ℕ), i ∈ U → (V i, (U.erase i).map V) ∈ picks (U.map V)
  | [], i, h => by simp at h
  | a :: l, i, h => by
    by_cases e : i = a
    · subst e; simp [picks]
    · have hi : i ∈ l := by simpa [e] using h
      have := picks_mem V l i hi
      rw [List.erase_cons_tail (by simpa using fun h' : a = i => e h'.symm)]
      simp only [picks, List.map_cons, List.mem_cons, List.mem_map]
      exact Or.inr ⟨_, this, rfl⟩

def prs2 : List ℕ → List (ℕ × ℕ × List ℕ)
  | [] => []
  | a :: l => ((picks l).map fun p => (a, p.1, p.2)) ++ (prs2 l).map fun q => (q.1, q.2.1, a :: q.2.2)

theorem prs2_mem (V : ℕ → ℕ) : ∀ (U : List ℕ) (i i' : ℕ), i ∈ U → i' ∈ U → i ≠ i' →
    (V i, V i', ((U.erase i).erase i').map V) ∈ prs2 (U.map V) ∨
    (V i', V i, ((U.erase i).erase i').map V) ∈ prs2 (U.map V)
  | [], i, i', h, _, _ => by simp at h
  | a :: l, i, i', hi, hi', hne => by
    by_cases e : i = a
    · subst e
      have h2 : i' ∈ l := by simpa [hne.symm] using hi'
      left
      rw [List.erase_cons_head]
      simp only [prs2, List.map_cons, List.mem_append, List.mem_map]
      exact Or.inl ⟨_, picks_mem V l i' h2, rfl⟩
    · by_cases e' : i' = a
      · subst e'
        have h2 : i ∈ l := by simpa [e] using hi
        right
        rw [List.erase_comm, List.erase_cons_head]
        simp only [prs2, List.map_cons, List.mem_append, List.mem_map]
        exact Or.inl ⟨_, picks_mem V l i h2, rfl⟩
      · have h1 : i ∈ l := by simpa [e] using hi
        have h2 : i' ∈ l := by simpa [e'] using hi'
        rw [List.erase_cons_tail (by simpa using fun h' : a = i => e h'.symm),
          List.erase_cons_tail (by simpa using fun h' : a = i' => e' h'.symm)]
        simp only [prs2, List.map_cons, List.mem_append, List.mem_map]
        rcases prs2_mem V l i i' h1 h2 hne with h | h
        · exact Or.inl (Or.inr ⟨_, h, rfl⟩)
        · exact Or.inr (Or.inr ⟨_, h, rfl⟩)

def detc (F t : ℕ) : List ℕ → ℕ → Bool
  | [], m => (t &&& m == 0) || (t &&& m == m)
  | a :: l, m => detc F t l (m &&& a) && detc F t l (m &&& (F ^^^ a))

def s0 (F t : ℕ) : ℕ → List ℕ → Bool
  | 0, us => us == [t]
  | r + 1, us => detc F t us F && (prs2 us).any fun q =>
      s0 F t r ((q.1 &&& q.2.1) :: q.2.2) || s0 F t r ((q.1 ||| q.2.1) :: q.2.2)

def detE (F t : ℕ) : ℕ → List ℕ → List ℕ → Bool
  | 0, _, us => detc F t us F
  | e + 1, W, us => (0 :: W).any fun w => detE F t e W (w :: us)

def sE (F t : ℕ) : ℕ → ℕ → List ℕ → List ℕ → Bool
  | r, 0, _, us => s0 F t r us
  | 0, _ + 1, _, _ => false
  | r + 1, e + 1, W, us => detE F t (e + 1) W us && (((prs2 us).any fun q =>
        sE F t r (e + 1) ((q.1 &&& q.2.1) :: W) ((q.1 &&& q.2.1) :: q.2.2) ||
        sE F t r (e + 1) ((q.1 ||| q.2.1) :: W) ((q.1 ||| q.2.1) :: q.2.2)) ||
      (picks us).any fun q => ((0 :: W).any fun w => sE F t r e ((q.1 &&& w) :: W) ((q.1 &&& w) :: q.2) ||
        sE F t r e ((q.1 ||| w) :: W) ((q.1 ||| w) :: q.2)) ||
      sE F t r e ((F ^^^ q.1) :: W) ((F ^^^ q.1) :: q.2)) ||
    (match e with
      | 0 => false
      | d + 1 => detE F t (d + 2) W us && ((0 :: W).any fun w => ((0 :: W).any fun w' =>
          sE F t r d ((w &&& w') :: W) ((w &&& w') :: us) ||
          sE F t r d ((w ||| w') :: W) ((w ||| w') :: us)) ||
          sE F t r d ((F ^^^ w) :: W) ((F ^^^ w) :: us)))

def Det (N t : ℕ) (us : List ℕ) : Prop :=
  ∀ p < N, ∀ q < N, (∀ a ∈ us, a.testBit p = a.testBit q) → t.testBit p = t.testBit q

theorem full_bit (N p : ℕ) (hp : p < N) : (2 ^ N - 1).testBit p = true := by
  rw [Nat.testBit_two_pow_sub_one]; simpa using hp

theorem eqN {N a b : ℕ} (ha : a < 2 ^ N) (hb : b < 2 ^ N)
    (h : ∀ p < N, a.testBit p = b.testBit p) : a = b := by
  refine Nat.eq_of_testBit_eq fun p => ?_
  by_cases hp : p < N
  · exact h p hp
  · have e : 2 ^ N ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem detc_of (N t : ℕ) : ∀ (us : List ℕ) (m : ℕ), m < 2 ^ N →
    (∀ p q, m.testBit p = true → m.testBit q = true → (∀ a ∈ us, a.testBit p = a.testBit q) →
      t.testBit p = t.testBit q) → detc (2 ^ N - 1) t us m = true
  | [], m, hm, h => by
    simp only [detc, Bool.or_eq_true, beq_iff_eq]
    by_cases hx : ∃ p, m.testBit p = true ∧ t.testBit p = true
    · obtain ⟨p, hp, htp⟩ := hx
      right
      refine Nat.eq_of_testBit_eq fun q => ?_
      rw [Nat.testBit_and]
      cases hq : m.testBit q with
      | false => simp
      | true => rw [← h p q hp hq (by simp), htp]; rfl
    · left
      refine Nat.eq_of_testBit_eq fun q => ?_
      rw [Nat.testBit_and, Nat.zero_testBit]
      cases hq : m.testBit q with
      | false => simp
      | true =>
        cases hq' : t.testBit q with
        | false => rfl
        | true => exact absurd ⟨q, hq, hq'⟩ hx
  | a :: l, m, hm, h => by
    simp only [detc, Bool.and_eq_true]
    constructor
    · refine detc_of N t l _ (lt_of_le_of_lt Nat.and_le_left hm) fun p q hp hq hl => ?_
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hq
      refine h p q hp.1 hq.1 fun b hb => ?_
      rcases List.mem_cons.1 hb with rfl | hb
      · rw [hp.2, hq.2]
      · exact hl b hb
    · refine detc_of N t l _ (lt_of_le_of_lt Nat.and_le_left hm) fun p q hp hq hl => ?_
      rw [Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true] at hp hq
      have lt : ∀ p, m.testBit p = true → p < N := by
        intro p hp
        by_contra hge
        have e : 2 ^ N ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.testBit_lt_two_pow (by omega)] at hp; cases hp
      refine h p q hp.1 hq.1 fun b hb => ?_
      rcases List.mem_cons.1 hb with rfl | hb
      · have e1 := hp.2
        have e2 := hq.2
        rw [full_bit N p (lt p hp.1)] at e1
        rw [full_bit N q (lt q hq.1)] at e2
        revert e1 e2
        cases b.testBit p <;> cases b.testBit q <;> simp
      · exact hl b hb

theorem detc_full {N t : ℕ} {us : List ℕ} (h : Det N t us) :
    detc (2 ^ N - 1) t us (2 ^ N - 1) = true := by
  have hN : 0 < 2 ^ N := Nat.two_pow_pos N
  refine detc_of N t us _ (by omega) fun p q hp hq hl => ?_
  rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq] at hp hq
  exact h p hp q hq hl

def Wl (n : ℕ) (V : ℕ → ℕ) : ℕ → List ℕ
  | 0 => (List.range n).map V
  | k + 1 => V (n + k) :: Wl n V k

theorem Wl_mem (n : ℕ) (V : ℕ → ℕ) : ∀ k i, i < n + k → V i ∈ Wl n V k
  | 0, i, h => by
    simp only [Wl, List.mem_map, List.mem_range]
    exact ⟨i, by omega, rfl⟩
  | k + 1, i, h => by
    by_cases e : i = n + k
    · subst e; simp [Wl]
    · exact List.mem_cons_of_mem _ (Wl_mem n V k i (by omega))

def DE (N t e : ℕ) (W us : List ℕ) : Prop :=
  ∃ ws : List ℕ, ws.length = e ∧ (∀ w ∈ ws, w ∈ 0 :: W) ∧ Det N t (ws ++ us)

theorem detE_of {N t : ℕ} (W : List ℕ) : ∀ (ws us : List ℕ), (∀ w ∈ ws, w ∈ 0 :: W) →
    Det N t (ws ++ us) → detE (2 ^ N - 1) t ws.length W us = true
  | [], us, _, h => detc_full h
  | w :: ws, us, hw, h => by
    simp only [List.length_cons, detE, List.any_eq_true]
    refine ⟨w, hw w (by simp), detE_of W ws (w :: us) (fun x hx => hw x (by simp [hx])) ?_⟩
    intro p hp q hq hall
    refine h p hp q hq fun a ha => hall a ?_
    simp only [List.cons_append, List.mem_cons, List.mem_append] at ha ⊢
    tauto

theorem DE_det {N t e : ℕ} {W us : List ℕ} (h : DE N t e W us) :
    detE (2 ^ N - 1) t e W us = true := by
  obtain ⟨ws, rfl, h1, h2⟩ := h
  exact detE_of W ws us h1 h2


theorem DE_step {N t e : ℕ} {W us us' xs : List ℕ} {v : ℕ} (h : DE N t e (v :: W) (v :: us'))
    (hx : ∀ x ∈ xs, x ∈ 0 :: W) (hsub : ∀ a ∈ us', a ∈ us)
    (hv : ∀ p < N, ∀ q < N, (∀ a ∈ xs, a.testBit p = a.testBit q) →
      (∀ a ∈ us, a.testBit p = a.testBit q) → v.testBit p = v.testBit q) :
    DE N t (xs.length + e) W us := by
  classical
  obtain ⟨ws, rfl, h1, h2⟩ := h
  refine ⟨xs ++ ws.map (fun w => if w = v then 0 else w), by simp, ?_, ?_⟩
  · intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact hx w hw
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hw
      split_ifs with e1
      · simp
      · have := h1 y hy
        simp only [List.mem_cons] at this ⊢
        tauto
  · intro p hp q hq hall
    have hxs : ∀ a ∈ xs, a.testBit p = a.testBit q := fun a ha => hall a (by simp [ha])
    have hus : ∀ a ∈ us, a.testBit p = a.testBit q := fun a ha => hall a (by simp [ha])
    have hvv := hv p hp q hq hxs hus
    refine h2 p hp q hq fun a ha => ?_
    rcases List.mem_append.1 ha with ha | ha
    · by_cases e1 : a = v
      · rw [e1]; exact hvv
      · have := hall a (List.mem_append_left _ (List.mem_append_right _
          (List.mem_map.2 ⟨a, ha, if_neg e1⟩)))
        exact this
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact hvv
      · exact hus a (hsub a ha)

theorem search (N n m o t : ℕ) (V : ℕ → ℕ) (R : ℕ → List ℕ) (ho : V o = t)
    (Hu : ∀ k < m, n + k = o ∨ ∃ j, k + 1 ≤ j ∧ j < m ∧ n + k ∈ R j)
    (hG : ∀ j < m, (∃ i i', R j = [i, i'] ∧
        (V (n + j) = (if i < n + j then V i else 0) &&& (if i' < n + j then V i' else 0) ∨
         V (n + j) = (if i < n + j then V i else 0) ||| (if i' < n + j then V i' else 0))) ∨
      (∃ i, R j = [i] ∧ (V (n + j) = (if i < n + j then V i else 0) ∨
         V (n + j) = (2 ^ N - 1) ^^^ (if i < n + j then V i else 0))) ∨
      (R j = [] ∧ (V (n + j) = 0 ∨ V (n + j) = 2 ^ N - 1))) :
    ∀ r k (U : List ℕ), k + r = m → U.Nodup → U ≠ [] →
      (∀ i ∈ U, i < n + k ∧ (i = o ∨ ∃ j, k ≤ j ∧ j < m ∧ i ∈ R j)) →
      U.length ≤ r + 1 ∧ ∀ e, U.length + e = r + 1 →
        sE (2 ^ N - 1) t r e (Wl n V k) (U.map V) = true ∧ DE N t e (Wl n V k) (U.map V) := by
  intro r
  induction r with
  | zero =>
    intro k U hk hnd hne hU
    have all : ∀ i ∈ U, i = o := by
      intro i hi
      rcases (hU i hi).2 with h | ⟨j, h1, h2, _⟩
      · exact h
      · omega
    have hlen : U.length ≤ 1 := by
      rcases U with _ | ⟨a, _ | ⟨b, l⟩⟩
      · simp
      · simp
      · exfalso
        have e1 := all a (by simp)
        have e2 := all b (by simp)
        rw [e1, e2] at hnd
        simp at hnd
    have hpos := List.length_pos_iff.2 hne
    refine ⟨by omega, fun e he => ?_⟩
    have e0 : e = 0 := by omega
    subst e0
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 (show U.length = 1 by omega)
    have ea := all a (by simp)
    subst ea
    refine ⟨by simp [sE, s0, ho], [], rfl, by simp, fun p _ q _ h => ?_⟩
    have := h (V a) (by simp)
    rw [ho] at this; exact this
  | succ r ih =>
    intro k U hk hnd hne hU
    have hkm : k < m := by omega
    set v := V (n + k) with hv
    have step : ∀ U' : List ℕ, U'.Nodup → (∀ i ∈ U', i ∈ U ∧ i ∉ R k) →
        U'.length ≤ r ∧ ∀ e, U'.length + 1 + e = r + 1 →
          sE (2 ^ N - 1) t r e (v :: Wl n V k) (v :: U'.map V) = true ∧
          DE N t e (v :: Wl n V k) (v :: U'.map V) := by
      intro U' hnd' hU'
      obtain ⟨q1, q2⟩ := ih (k + 1) ((n + k) :: U') (by omega) (by
        rw [List.nodup_cons]
        refine ⟨fun h => ?_, hnd'⟩
        have := (hU _ (hU' _ h).1).1
        omega) (by simp) (by
        intro i hi
        rcases List.mem_cons.1 hi with rfl | hi
        · exact ⟨by omega, Hu k hkm⟩
        · obtain ⟨h1, h2⟩ := hU' i hi
          obtain ⟨h3, h4⟩ := hU i h1
          refine ⟨by omega, ?_⟩
          rcases h4 with h4 | ⟨j, h4, h5, h6⟩
          · exact Or.inl h4
          · right
            refine ⟨j, ?_, h5, h6⟩
            rcases Nat.lt_or_ge k j with h | h
            · omega
            · have : j = k := by omega
              rw [this] at h6; exact absurd h6 h2)
      rw [List.length_cons] at q1 q2
      exact ⟨by omega, fun e he => q2 e he⟩
    have hlenE : ∀ i ∈ U, (U.erase i).length + 1 = U.length := by
      intro i hi
      rw [List.length_erase_of_mem hi]
      have := List.length_pos_of_mem hi
      omega
    have w_mem : ∀ i, (if i < n + k then V i else 0) ∈ 0 :: Wl n V k := by
      intro i
      split_ifs with h
      · exact List.mem_cons_of_mem _ (Wl_mem n V k i h)
      · simp
    -- no unread wire is read
    have f0 : (∀ x ∈ U, x ∉ R k) →
        ((∃ w ∈ 0 :: Wl n V k, ∃ w' ∈ 0 :: Wl n V k, v = w &&& w' ∨ v = w ||| w') ∨
          ∃ w ∈ 0 :: Wl n V k, v = (2 ^ N - 1) ^^^ w) →
        U.length ≤ r + 1 + 1 ∧ ∀ e, U.length + e = r + 1 + 1 →
          sE (2 ^ N - 1) t (r + 1) e (Wl n V k) (U.map V) = true ∧ DE N t e (Wl n V k) (U.map V) := by
      intro h hval
      obtain ⟨q1, q2⟩ := step U hnd fun i hi => ⟨hi, h i hi⟩
      refine ⟨by omega, fun e he => ?_⟩
      obtain ⟨d, rfl⟩ : ∃ d, e = d + 2 := ⟨e - 2, by omega⟩
      obtain ⟨s, D⟩ := q2 d (by omega)
      have hDE : DE N t (d + 2) (Wl n V k) (U.map V) := by
        rcases hval with ⟨w, hw, w', hw', e1⟩ | ⟨w, hw, e1⟩
        · have := DE_step (xs := [w, w']) (us := U.map V) D (by
            intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · exact hw
            · have : x = w' := by simpa using hx
              rw [this]; exact hw') (fun a ha => ha) (by
            intro p _ q _ hx _
            have a1 := hx w (by simp)
            have a2 := hx w' (by simp)
            rcases e1 with e1 | e1 <;> rw [e1]
            · rw [Nat.testBit_and, Nat.testBit_and, a1, a2]
            · rw [Nat.testBit_or, Nat.testBit_or, a1, a2])
          rw [show [w, w'].length + d = d + 2 by simp; omega] at this
          exact this
        · have := DE_step (xs := [w, 0]) (us := U.map V) D (by
            intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · exact hw
            · simp at hx; simp [hx]) (fun a ha => ha) (by
            intro p hp q hq hx _
            have a1 := hx w (by simp)
            rw [e1, Nat.testBit_xor, Nat.testBit_xor, a1, full_bit N p hp, full_bit N q hq])
          rw [show [w, 0].length + d = d + 2 by simp; omega] at this
          exact this
      refine ⟨?_, hDE⟩
      simp only [sE, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true]
      right
      refine ⟨DE_det hDE, ?_⟩
      rcases hval with ⟨w, hw, w', hw', e1⟩ | ⟨w, hw, e1⟩
      · refine ⟨w, hw, Or.inl ⟨w', hw', ?_⟩⟩
        rcases e1 with e1 | e1
        · left; rw [← e1]; exact s
        · right; rw [← e1]; exact s
      · exact ⟨w, hw, Or.inr (by rw [← e1]; exact s)⟩
    have f1 : ∀ i ∈ U, (∀ x ∈ U, x ∈ R k → x = i) →
        ((∃ w ∈ 0 :: Wl n V k, v = V i &&& w ∨ v = V i ||| w) ∨ v = (2 ^ N - 1) ^^^ V i) →
        U.length ≤ r + 1 + 1 ∧ ∀ e, U.length + e = r + 1 + 1 →
          sE (2 ^ N - 1) t (r + 1) e (Wl n V k) (U.map V) = true ∧ DE N t e (Wl n V k) (U.map V) := by
      intro i hi h1 hval
      obtain ⟨q1, q2⟩ := step (U.erase i) (hnd.erase i) (by
        intro x hx
        obtain ⟨hxi, hxU⟩ := (hnd.mem_erase_iff).1 hx
        exact ⟨hxU, fun hR => hxi (h1 x hxU hR)⟩)
      have hl := hlenE i hi
      refine ⟨by omega, fun e he => ?_⟩
      obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
      obtain ⟨s, D⟩ := q2 d (by omega)
      have hmem := picks_mem V U i hi
      have sub : ∀ a ∈ (U.erase i).map V, a ∈ U.map V := by
        intro a ha
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
        exact List.mem_map_of_mem (List.mem_of_mem_erase hx)
      have hDE : DE N t (d + 1) (Wl n V k) (U.map V) := by
        rcases hval with ⟨w, hw, e1⟩ | e1
        · have := DE_step (xs := [w]) (us := U.map V) D (by simpa using hw) sub (by
            intro p _ q _ hx hu
            have a1 := hx w (by simp)
            have a2 := hu (V i) (List.mem_map_of_mem hi)
            rcases e1 with e1 | e1 <;> rw [e1]
            · rw [Nat.testBit_and, Nat.testBit_and, a1, a2]
            · rw [Nat.testBit_or, Nat.testBit_or, a1, a2])
          rw [show [w].length + d = d + 1 by simp; omega] at this
          exact this
        · have := DE_step (xs := [0]) (us := U.map V) D (by simp) sub (by
            intro p hp q hq _ hu
            have a2 := hu (V i) (List.mem_map_of_mem hi)
            rw [e1, Nat.testBit_xor, Nat.testBit_xor, a2, full_bit N p hp, full_bit N q hq])
          rw [show [0].length + d = d + 1 by simp; omega] at this
          exact this
      refine ⟨?_, hDE⟩
      simp only [sE, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true]
      left
      refine ⟨DE_det hDE, Or.inr ⟨_, hmem, ?_⟩⟩
      rcases hval with ⟨w, hw, e1 | e1⟩ | e1
      · exact Or.inl ⟨w, hw, Or.inl (by rw [← e1]; exact s)⟩
      · exact Or.inl ⟨w, hw, Or.inr (by rw [← e1]; exact s)⟩
      · exact Or.inr (by rw [← e1]; exact s)
    have f2 : ∀ i ∈ U, ∀ i' ∈ U, i ≠ i' → (∀ x ∈ R k, x = i ∨ x = i') →
        (v = V i &&& V i' ∨ v = V i ||| V i') →
        U.length ≤ r + 1 + 1 ∧ ∀ e, U.length + e = r + 1 + 1 →
          sE (2 ^ N - 1) t (r + 1) e (Wl n V k) (U.map V) = true ∧ DE N t e (Wl n V k) (U.map V) := by
      intro i hi i' hi' hne' hR hval
      have hi2 : i' ∈ U.erase i := (hnd.mem_erase_iff).2 ⟨hne'.symm, hi'⟩
      have hl := hlenE i hi
      have hl2 : ((U.erase i).erase i').length + 1 = (U.erase i).length := by
        rw [List.length_erase_of_mem hi2]
        have := List.length_pos_of_mem hi2
        omega
      obtain ⟨q1, q2⟩ := step ((U.erase i).erase i') ((hnd.erase i).erase i') (by
        intro x hx
        obtain ⟨h1, h2⟩ := ((hnd.erase i).mem_erase_iff).1 hx
        obtain ⟨h3, h4⟩ := (hnd.mem_erase_iff).1 h2
        exact ⟨h4, fun hR' => (hR x hR').elim h3 h1⟩)
      have m1 := prs2_mem V U i i' hi hi' hne'
      have sub : ∀ a ∈ ((U.erase i).erase i').map V, a ∈ U.map V := by
        intro a ha
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
        exact List.mem_map_of_mem (List.mem_of_mem_erase (List.mem_of_mem_erase hx))
      refine ⟨by omega, fun e he => ?_⟩
      obtain ⟨s, D⟩ := q2 e (by omega)
      have hDE : DE N t e (Wl n V k) (U.map V) := by
        have := DE_step (xs := []) (us := U.map V) D (by simp) sub (by
          intro p _ q _ _ hu
          have a1 := hu (V i) (List.mem_map_of_mem hi)
          have a2 := hu (V i') (List.mem_map_of_mem hi')
          rcases hval with e1 | e1 <;> rw [e1]
          · rw [Nat.testBit_and, Nat.testBit_and, a1, a2]
          · rw [Nat.testBit_or, Nat.testBit_or, a1, a2])
        simpa using this
      refine ⟨?_, hDE⟩
      rcases e with _ | e
      · simp only [sE] at s ⊢
        simp only [s0, Bool.and_eq_true, List.any_eq_true, Bool.or_eq_true]
        rcases m1 with m1 | m1 <;> refine ⟨DE_det hDE, _, m1, ?_⟩
        · rcases hval with e1 | e1
          · left; rw [← e1]; exact s
          · right; rw [← e1]; exact s
        · rcases hval with e1 | e1
          · left; rw [Nat.and_comm, ← e1]; exact s
          · right; rw [Nat.or_comm, ← e1]; exact s
      · simp only [sE, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true]
        left
        rcases m1 with m1 | m1 <;> refine ⟨DE_det hDE, Or.inl ⟨_, m1, ?_⟩⟩
        · rcases hval with e1 | e1
          · left; rw [← e1]; exact s
          · right; rw [← e1]; exact s
        · rcases hval with e1 | e1
          · left; rw [Nat.and_comm, ← e1]; exact s
          · right; rw [Nat.or_comm, ← e1]; exact s
    rcases hG k hkm with ⟨i, i', hR, hval⟩ | ⟨i, hR, hval⟩ | ⟨hR, hval⟩
    · by_cases hi : i ∈ U
      · have hi' := (hU i hi).1
        by_cases h2 : i' ∈ U ∧ i ≠ i'
        · have hi2 := (hU i' h2.1).1
          rw [if_pos hi', if_pos hi2] at hval
          exact f2 i hi i' h2.1 h2.2 (by rw [hR]; simp) hval
        · rw [if_pos hi'] at hval
          refine f1 i hi ?_ (Or.inl ⟨_, w_mem i', hval⟩)
          intro x hx hxR
          rw [hR] at hxR
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hxR
          rcases hxR with rfl | rfl
          · rfl
          · by_contra hne
            exact h2 ⟨hx, fun h => hne h.symm⟩
      · by_cases hi' : i' ∈ U
        · have hlt := (hU i' hi').1
          rw [if_pos hlt] at hval
          refine f1 i' hi' ?_ (Or.inl ⟨_, w_mem i, ?_⟩)
          · intro x hx hxR
            rw [hR] at hxR
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hxR
            rcases hxR with rfl | rfl
            · exact absurd hx hi
            · rfl
          · rcases hval with e | e
            · left; rw [Nat.and_comm]; exact e
            · right; rw [Nat.or_comm]; exact e
        · refine f0 (fun x hx hxR => ?_) (Or.inl ⟨_, w_mem i, _, w_mem i', hval⟩)
          rw [hR] at hxR
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hxR
          rcases hxR with rfl | rfl
          · exact hi hx
          · exact hi' hx
    · by_cases hi : i ∈ U
      · rw [if_pos (hU i hi).1] at hval
        refine f1 i hi ?_ ?_
        · intro x _ hxR
          rw [hR] at hxR
          simpa using hxR
        · rcases hval with e | e
          · exact Or.inl ⟨0, by simp, Or.inr (by rw [Nat.or_zero]; exact e)⟩
          · exact Or.inr e
      · refine f0 (fun x hx hxR => ?_) ?_
        · rw [hR] at hxR
          have : x = i := by simpa using hxR
          exact hi (this ▸ hx)
        · rcases hval with e | e
          · exact Or.inl ⟨_, w_mem i, 0, by simp, Or.inr (by rw [Nat.or_zero]; exact e)⟩
          · exact Or.inr ⟨_, w_mem i, e⟩
    · refine f0 (fun x _ hxR => by rw [hR] at hxR; simp at hxR) ?_
      rcases hval with e | e
      · exact Or.inl ⟨0, by simp, 0, by simp, Or.inl (by rw [Nat.and_zero]; exact e)⟩
      · exact Or.inr ⟨0, by simp, by rw [Nat.xor_zero]; exact e⟩


def nrm (g : Gate) : Gate := ⟨g.op, rds g⟩

theorem nrm_run (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (x : List Bool) :
    run (gs.map nrm) x = run gs x := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [List.map_append, List.map_singleton, run_snoc, run_snoc,
      ih fun g' h => hop g' (by simp [h])]
    congr 2
    rcases hop g (by simp) with h | h | h
    · simp [nrm, rds, h]
    · simp [nrm, rds, h]
    · rcases g with ⟨o, l⟩
      simp only at h
      subst h
      rcases l with _ | ⟨a, l⟩ <;> simp [nrm, rds, GateOp.eval]

def X (n p : ℕ) : List Bool := List.ofFn fun i : Fin n => p.testBit i

def tt (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ :=
  Nat.ofBits fun p : Fin (2 ^ n) => f fun i : Fin n => p.val.testBit i

def vars (n : ℕ) : List ℕ :=
  (List.range n).map fun i => Nat.ofBits fun p : Fin (2 ^ n) => p.val.testBit i

theorem final (n lb : ℕ) (f : (Fin n → Bool) → Bool)
    (hn0 : n ≠ 0) (hess : ∀ i : Fin n, ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!(x i))))
    (hs : ∀ e, n - 1 + e < lb →
      sE (2 ^ (2 ^ n) - 1) (tt n f) (n - 1 + e) e (vars n) (vars n) = false) (t : ℕ)
    (h : HasCircuitSize n f t) : lb ≤ t := by
  classical
  obtain ⟨C0, hC0, hsz0, hf0⟩ := h
  -- a smallest circuit for f
  have hex : ∃ s, ∃ D : Circuit, FanInTwo D ∧ circuitFun n D = f ∧ D.size = s :=
    ⟨C0.size, C0, hC0, funext hf0, rfl⟩
  obtain ⟨D, hD, hDf, hDs⟩ := Nat.find_spec hex
  have hmin : ∀ E : Circuit, FanInTwo E → circuitFun n E = f → D.size ≤ E.size := by
    intro E hE hEf
    rw [hDs]
    exact Nat.find_min' hex ⟨E, hE, hEf, rfl⟩
  have hle : D.size ≤ t := (hmin C0 hC0 (funext hf0)).trans hsz0
  by_contra hlt
  have hopD : ∀ g ∈ D.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    intro g hg
    simpa using (hD g hg).1
  -- normalise
  set C : Circuit := ⟨D.gates.map nrm, D.output⟩ with hCd
  have hlen : C.gates.length = D.gates.length := by simp [hCd]
  have hrun : ∀ x, run C.gates x = run D.gates x := fun x => nrm_run D.gates hopD x
  have hCf : circuitFun n C = f := by
    rw [← hDf]
    funext x
    change (run C.gates (List.ofFn x)).getD D.output false = (run D.gates (List.ofFn x)).getD D.output false
    rw [hrun]
  have hgC : ∀ j (hj : j < C.gates.length), ∃ g ∈ D.gates, C.gates[j] = nrm g := by
    intro j hj
    have hj' : j < D.gates.length := by omega
    exact ⟨D.gates[j], List.getElem_mem hj', by simp [hCd]⟩
  have hopC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact hopD g' hg'
  have hrl : ∀ g ∈ D.gates, (rds g).length ≤ 2 := by
    intro g hg
    have := (hD g hg).2
    rcases hopD g hg with h | h | h <;> simp [rds, h] <;> omega
  have hFC : FanInTwo C := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact ⟨(hD g' hg').1, hrl g' hg'⟩
  let m := C.gates.length
  have hm : m = D.size := hlen
  -- every gate is read or is the output
  have Hu : ∀ k < m, n + k = C.output ∨ ∃ j, k + 1 ≤ j ∧ ∃ hj : j < C.gates.length,
      n + k ∈ C.gates[j].inputs := by
    intro k hk
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨E, hE1, hE2, hE3⟩ := del n C hFC k hk
      (fun j hj hkj hin => hcon.2 ⟨j, hkj, hj, hin⟩) (fun h => hcon.1 h.symm)
    have := hmin E hE1 (hE3.trans hCf)
    have e : C.size = m := rfl
    omega
  -- every input is read or is the output
  have Hi : ∀ i < n, i = C.output ∨ ∃ j, ∃ hj : j < C.gates.length, i ∈ C.gates[j].inputs := by
    intro i hi
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨x, hx⟩ := hess ⟨i, hi⟩
    apply hx
    rw [← hCf]
    refine indep i C.gates hopC ?_ (List.ofFn x) (List.ofFn _) (by simp) ?_ C.output
      (fun h => hcon.1 h.symm)
    · intro g hg hig
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      obtain ⟨g', _, e⟩ := hgC j hj
      refine hcon.2 ⟨j, hj, ?_⟩
      rcases hopC _ (List.getElem_mem hj) with h | h | h
      · simpa [rds, h] using hig
      · simpa [rds, h] using hig
      · simp only [rds, h] at hig
        exact List.mem_of_mem_take hig
    · intro q hq
      by_cases hqn : q < n
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hqn, dif_pos, Option.getD_some]
        rw [Function.update_of_ne]
        intro h
        exact hq (by simpa using congrArg Fin.val h)
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  let N := 2 ^ n
  let V : ℕ → ℕ := fun i => Nat.ofBits fun p : Fin N => (run C.gates (X n p)).getD i false
  have Vb : ∀ i p, p < N → (V i).testBit p = (run C.gates (X n p)).getD i false := by
    intro i p hp
    simp only [V]
    rw [Nat.testBit_ofBits_lt _ _ hp]
  have Vlt : ∀ i, V i < 2 ^ N := fun i => Nat.ofBits_lt_two_pow _
  have Xl : ∀ p, (X n p).length = n := fun p => by simp [X]
  have Xd : ∀ p i, i < n → (X n p).getD i false = p.testBit i := by
    intro p i hi
    simp [X, List.getD_eq_getElem?_getD, hi]
  have hVi : ∀ i < n, V i = Nat.ofBits fun p : Fin (2 ^ n) => p.val.testBit i := by
    intro i hi
    refine eqN (Vlt i) (Nat.ofBits_lt_two_pow _) fun p hp => ?_
    rw [Vb i p hp, Nat.testBit_ofBits_lt _ _ hp, run_input _ _ _ (by rw [Xl]; exact hi), Xd p i hi]
  have hvars : (List.range n).map V = vars n := by
    unfold vars
    exact List.map_congr_left fun i hi => hVi i (List.mem_range.1 hi)
  have hVo : V C.output = tt n f := by
    refine eqN (Vlt _) (Nat.ofBits_lt_two_pow _) fun p hp => ?_
    rw [Vb _ p hp, tt, Nat.testBit_ofBits_lt _ _ hp, ← hCf]
    rfl
  let R : ℕ → List ℕ := fun j => if hj : j < C.gates.length then C.gates[j].inputs else []
  have hG : ∀ j < m, (∃ i i', R j = [i, i'] ∧
        (V (n + j) = (if i < n + j then V i else 0) &&& (if i' < n + j then V i' else 0) ∨
         V (n + j) = (if i < n + j then V i else 0) ||| (if i' < n + j then V i' else 0))) ∨
      (∃ i, R j = [i] ∧ (V (n + j) = (if i < n + j then V i else 0) ∨
         V (n + j) = (2 ^ N - 1) ^^^ (if i < n + j then V i else 0))) ∨ (R j = [] ∧ (V (n + j) = 0 ∨ V (n + j) = 2 ^ N - 1)) := by
    intro j hj
    have hRj : R j = C.gates[j].inputs := dif_pos hj
    have wb : ∀ i p, p < N → (if i < n + j then V i else 0).testBit p =
        if i < n + j then (run C.gates (X n p)).getD i false else false := by
      intro i p hp
      split_ifs
      · exact Vb i p hp
      · exact Nat.zero_testBit p
    have wlt : ∀ i, (if i < n + j then V i else 0) < 2 ^ N := by
      intro i
      split_ifs
      · exact Vlt i
      · exact Nat.two_pow_pos N
    have hv : ∀ p, p < N → (V (n + j)).testBit p = C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < n + j then (run C.gates (X n p)).getD i false else false) := by
      intro p hp
      have := run_gate C.gates (X n p) j hj
      rw [Xl] at this
      rw [Vb _ p hp, this]
    have hl2 : C.gates[j].inputs.length ≤ 2 := (hFC _ (List.getElem_mem hj)).2
    rw [hRj]
    obtain ⟨g', hg', eg⟩ := hgC j hj
    rcases hin : C.gates[j].inputs with _ | ⟨i, _ | ⟨i', _ | ⟨i'', l⟩⟩⟩
    · right; right
      refine ⟨rfl, ?_⟩
      rw [hin] at hv
      have h0 : (0 : ℕ) < 2 ^ N := Nat.two_pow_pos N
      rcases hopC _ (List.getElem_mem hj) with h | h | h <;> rw [h] at hv
      · right
        refine eqN (Vlt _) (by omega) fun p hp => ?_
        rw [hv p hp, full_bit N p hp]; simp [GateOp.eval]
      · left
        refine eqN (Vlt _) h0 fun p hp => ?_
        rw [hv p hp, Nat.zero_testBit]; simp [GateOp.eval]
      · right
        refine eqN (Vlt _) (by omega) fun p hp => ?_
        rw [hv p hp, full_bit N p hp]; simp [GateOp.eval]
    · right; left
      refine ⟨i, rfl, ?_⟩
      rw [hin] at hv
      rcases hopC _ (List.getElem_mem hj) with h | h | h <;> rw [h] at hv
      · left
        refine eqN (Vlt _) (wlt i) fun p hp => ?_
        rw [hv p hp, wb i p hp]; simp [GateOp.eval]
      · left
        refine eqN (Vlt _) (wlt i) fun p hp => ?_
        rw [hv p hp, wb i p hp]; simp [GateOp.eval]
      · right
        refine eqN (Vlt _) (Nat.xor_lt_two_pow (by have := Nat.two_pow_pos N; omega) (wlt i)) fun p hp => ?_
        rw [hv p hp, Nat.testBit_xor, full_bit N p hp, wb i p hp]; simp [GateOp.eval]
    · left
      refine ⟨i, i', rfl, ?_⟩
      rw [hin] at hv
      rcases hopC _ (List.getElem_mem hj) with h | h | h <;> rw [h] at hv
      · left
        refine eqN (Vlt _) (lt_of_le_of_lt Nat.and_le_left (wlt i)) fun p hp => ?_
        rw [hv p hp, Nat.testBit_and, wb i p hp, wb i' p hp]; simp [GateOp.eval]
      · right
        refine eqN (Vlt _) (Nat.or_lt_two_pow (wlt i) (wlt i')) fun p hp => ?_
        rw [hv p hp, Nat.testBit_or, wb i p hp, wb i' p hp]; simp [GateOp.eval]
      · exfalso
        rw [eg] at h hin
        change g'.op = _ at h
        change rds g' = _ at hin
        simp only [rds, h] at hin
        have := congrArg List.length hin
        simp at this
        omega
    · rw [hin] at hl2; simp at hl2
  have hS := search N n m C.output (tt n f) V R hVo
    (by
      intro k hk
      rcases Hu k hk with h | ⟨j, h1, h2, h3⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, h1, h2, by simp only [R, dif_pos h2]; exact h3⟩)
    hG m 0 (List.range n) (by omega) List.nodup_range (by
      intro h0
      have := congrArg List.length h0
      simp at this
      exact hn0 this) (by
      intro i hi
      have hi' := List.mem_range.1 hi
      refine ⟨by omega, ?_⟩
      rcases Hi i hi' with h | ⟨j, h2, h3⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, h2, by simp only [R, dif_pos h2]; exact h3⟩)
  obtain ⟨q1, q2⟩ := hS
  rw [List.length_range] at q1 q2
  rw [hvars] at q2
  have hmlb : m < lb := by omega
  obtain ⟨e, he⟩ : ∃ e, m = n - 1 + e := ⟨m - (n - 1), by omega⟩
  have h1 := (q2 e (by omega)).1
  have h2 := hs e (by omega)
  have hw : Wl n V 0 = vars n := hvars
  rw [hw, he, h2] at h1
  cases h1

end PEqualNP.Outside.L_meta_13349_aux.LowerFive

namespace PEqualNP.Outside.L_meta_13349_aux.LowerFive
 theorem lower : ∀ s, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xeee8eae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → 7 ≤ s := by
    refine PEqualNP.Outside.L_meta_13349_aux.LowerFive.S.red2 4 _ (4 : Fin 5) (by decide +kernel) (by decide +kernel) 5 ?_
    intro b
    cases b
    · exact fun s h => PEqualNP.Outside.L_meta_13349_aux.LowerFive.final 4 5 _ (by decide) (by decide +kernel) (fun e he => by
        have he' : e < 2 := by omega
        clear he
        interval_cases e <;> decide +kernel) s h
    · exact fun s h => PEqualNP.Outside.L_meta_13349_aux.LowerFive.final 4 5 _ (by decide) (by decide +kernel) (fun e he => by
        have he' : e < 2 := by omega
        clear he
        interval_cases e <;> decide +kernel) s h
end PEqualNP.Outside.L_meta_13349_aux.LowerFive

namespace PEqualNP.Outside.L_meta_13349_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def target (x : Fin 6 → Bool) : Bool := Nat.testBit (3937069224 * 2 ^ 32 + 3934840968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[⟨.or,[2,4]⟩,⟨.or,[3,5]⟩,⟨.and,[6,7]⟩,⟨.and,[0,8]⟩,⟨.and,[2,3]⟩,⟨.or,[0,10]⟩,⟨.and,[1,11]⟩,⟨.or,[9,12]⟩],13⟩
theorem witness_basis : Monotone2 witness := by simp [Monotone2, witness]
theorem witness_size : witness.size = 8 := rfl
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witness_correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel
end PEqualNP.Outside.L_meta_13349_aux


namespace PEqualNP.Outside.L_meta_13349_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def five (x : Fin 5 → Bool) : Bool := target (Fin.snoc x false)
def perm5 (i : Fin 5) : Fin 5 := ![0,1,3,2,4] i

theorem five_lower (s : ℕ) (h : HasCircuitSize 5 five s) : 7 ≤ s := by
  have hr := Base.relabel_size perm5 five s h
  obtain ⟨C, fits, size, computes⟩ := hr
  have valid : C.output < 5 + C.gates.length := by
    by_contra! bad
    have ht := computes (fun _ => true)
    have len : (C.wires (List.ofFn fun _ : Fin 5 => true)).length = 5 + C.gates.length := by
      obtain ⟨t, ht, hl⟩ := Base.wiresFrom_prefix C.gates (List.ofFn fun _ : Fin 5 => true)
      change (Base.wiresFrom C.gates (List.ofFn fun _ : Fin 5 => true)).length = _
      rw [ht, List.length_append, List.length_ofFn, hl]
    change (C.wires (List.ofFn fun _ : Fin 5 => true)).getD C.output false = _ at ht
    rw [List.getD_eq_default _ _ (by omega)] at ht
    have yes : five ((fun _ : Fin 5 => true) ∘ perm5) = true := by decide +kernel
    change false = five ((fun _ : Fin 5 => true) ∘ perm5) at ht
    rw [yes] at ht
    cases ht
  have legal (g : Gate) (hg : g ∈ C.gates) :
      (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using fits g hg
  obtain ⟨gs, glen, gok, _, geq⟩ := Dual.main 5 C.gates legal
  have hd : HasCircuitSize 5 (fun x => !(five ((fun p => !x p) ∘ perm5))) s := by
    refine ⟨⟨gs,C.output⟩, ?_, ?_, ?_⟩
    · intro g hg
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using gok g hg
    · simpa [Circuit.size, glen] using size
    · intro x
      have eq := geq C.output x valid
      change Circuit.eval ⟨gs,C.output⟩ (List.ofFn x) = !(C.eval (List.ofFn fun p => !x p)) at eq
      rw [computes] at eq
      exact eq
  have heq : (fun x : Fin 5 → Bool => !(five ((fun p => !x p) ∘ perm5))) =
      (fun x : Fin 5 → Bool => Nat.testBit 0xeee8eae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) := by
    decide +kernel
  rw [heq] at hd
  exact LowerFive.lower s hd

theorem target_lower (s : ℕ) (h : HasCircuitSize 6 target s) : 8 ≤ s := by
  have dep : ∃ x : Fin 6 → Bool, target (Function.update x (Fin.last 5) (!x (Fin.last 5))) ≠ target x := by
    decide +kernel
  have nonconstant : ∃ y y' : Fin 5 → Bool, target (Fin.snoc y false) ≠ target (Fin.snoc y' false) := by
    decide +kernel
  obtain ⟨s', less, hs⟩ := Base.gate_elim_one 5 target false s dep nonconstant h
  have low := five_lower s' hs
  omega

end PEqualNP.Outside.L_meta_13349_aux

theorem PEqualNP.Outside.L_meta_13349 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937069224 * 2 ^ 32 + 3934840968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937069224 * 2 ^ 32 + 3934840968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  refine ⟨PEqualNP.Outside.L_meta_13349_aux.witness, PEqualNP.Outside.L_meta_13349_aux.witness_basis, ?_, PEqualNP.Outside.L_meta_13349_aux.witness_correct⟩
  rw [PEqualNP.Outside.L_meta_13349_aux.witness_size]
  exact PEqualNP.Outside.L_meta_13349_aux.target_lower s h

