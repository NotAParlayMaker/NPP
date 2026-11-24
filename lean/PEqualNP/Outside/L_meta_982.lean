import Mathlib
import PEqualNP.Defs

-- Based in part on sanchan's L-meta-927 circuit proofs, Apache-2.0.
namespace PEqualNP.Outside.L_meta_982_aux


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

theorem spOK {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem sj {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
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
  bsr (HT s) 32 (hk zs) 10 0 (NN s)

theorem prove_base (n k cap : ℕ) (f : BFn n) (rows xs pool : List ℕ)
    (NN HT PT : ℕ → ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (hlen : rows.length = k + k)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun a => encL a rows) = xs)
    (hgoal : encL f rows = goal k)
    (hprop : ∀ zs ∈ xs.sublists, zs ≠ xs → (cov k zs &&& lo k) ≠ lo k)
    (hNcap : 0 < NN cap)
    (hchk : ∀ s ≤ cap, ∀ i < NN s,
      bar k (Sgen k cap xs PT) NN (idxGen NN HT) id pool s i = true) :
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
      have hS0 : Sgen k cap xs PT cap 0 = xs := by simp [Sgen, StGen]
      rw [← hS0] at hcap
      exact bar_all (fun h => h) hchk cap le_rfl 0 hNcap hcap
  · exact hprop _ (List.mem_sublists.2 hsub') he (required hr)



-- Base case K3 (n=3, cap=3, k=9, states=1, pool=1)
def f_K3 : BFn 3 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)
def rows_K3 : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 4, 3, 5, 6, 3, 5, 6, 3, 5, 6]
def xs_K3 : List ℕ := [0x1b607, 0x2da38, 0x36dc0]
def pool_K3 : List ℕ := [0xc000180b02809]
def NN_K3 : ℕ → ℕ
  | 3 => 1
  | _ => 0
def HT_K3 : ℕ → ℕ
  | 3 => 0xc03a13c3
  | _ => 0
def PT_K3 : ℕ → ℕ
  | _ => 0
def Z_K3 (s : ℕ) := bar 9 (Sgen 9 3 xs_K3 PT_K3) NN_K3 (idxGen NN_K3 HT_K3) id pool_K3 s
theorem z_K3_0 : span (Z_K3 0) 0 0 = true := rfl
theorem z_K3_1 : span (Z_K3 1) 0 0 = true := rfl
theorem z_K3_2 : span (Z_K3 2) 0 0 = true := rfl
theorem h_K3_3_0 : span (Z_K3 3) 1 0 = true := by decide +kernel
theorem z_K3_3 : span (Z_K3 3) 1 0 = true := h_K3_3_0
theorem base_K3 : ∀ s : ℕ, HasCircuitSize 3 f_K3 s → 4 ≤ s := by
  refine prove_base 3 9 3 f_K3 rows_K3 xs_K3 pool_K3 NN_K3 HT_K3 PT_K3
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => spOK z_K3_0 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3_1 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3_2 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3_3 i (Nat.zero_le i) hi
    )

-- Base case C5 (n=5, cap=6, k=50, states=7, pool=5)
def f_C5 : BFn 5 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)
def rows_C5 : List ℕ := [1, 1, 2, 2, 4, 4, 6, 6, 6, 6, 6, 6, 6, 6, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 3, 5, 3, 10, 5, 20, 3, 5, 7, 10, 14, 20, 22, 24, 10, 24, 3, 5, 10, 11, 13, 20, 24, 25, 3, 5, 10, 13, 14, 20, 24, 28, 20, 24, 3, 5, 10, 19, 20, 21, 24, 25, 3, 5, 10, 19, 20, 22, 24, 26]
def xs_C5 : List ℕ := [0xbab02e6c075c03fc00ff0003, 0xad0d054355d37fc0000003fcc, 0x32326e8c876c80000ff003ff0, 0xc4c4b737398200000ffffc000, 0xf8f8f8382e083ffff00000000]
def pool_C5 : List ℕ := [0x18000a8370c833, 0x38020883f0c835, 0x80040403f0cc37, 0x800060350cc32, 0x800e018370d43f]
def NN_C5 : ℕ → ℕ
  | 5 => 6
  | 6 => 1
  | _ => 0
def HT_C5 : ℕ → ℕ
  | 5 => 0xc6e3b2e569d2916d684aef2d399569702839ea7a276164fc
  | 6 => 0x2839ea7a
  | _ => 0
def PT_C5 : ℕ → ℕ
  | 5 => 0x40c0104004040100000000102
  | _ => 0
def Z_C5 (s : ℕ) := bar 50 (Sgen 50 6 xs_C5 PT_C5) NN_C5 (idxGen NN_C5 HT_C5) id pool_C5 s
theorem z_C5_0 : span (Z_C5 0) 0 0 = true := rfl
theorem z_C5_1 : span (Z_C5 1) 0 0 = true := rfl
theorem z_C5_2 : span (Z_C5 2) 0 0 = true := rfl
theorem z_C5_3 : span (Z_C5 3) 0 0 = true := rfl
theorem z_C5_4 : span (Z_C5 4) 0 0 = true := rfl
theorem h_C5_5_0 : span (Z_C5 5) 6 0 = true := by decide +kernel
theorem z_C5_5 : span (Z_C5 5) 6 0 = true := h_C5_5_0
theorem h_C5_6_0 : span (Z_C5 6) 1 0 = true := by decide +kernel
theorem z_C5_6 : span (Z_C5 6) 1 0 = true := h_C5_6_0
theorem base_C5 : ∀ s : ℕ, HasCircuitSize 5 f_C5 s → 7 ≤ s := by
  refine prove_base 5 50 6 f_C5 rows_C5 xs_C5 pool_C5 NN_C5 HT_C5 PT_C5
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => spOK z_C5_0 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_C5_1 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_C5_2 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_C5_3 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_C5_4 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_C5_5 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_C5_6 i (Nat.zero_le i) hi
    )

-- Base case BOWTIE (n=5, cap=7, k=50, states=79, pool=10)
def f_BOWTIE : BFn 5 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)
def rows_BOWTIE : List ℕ := [1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 20, 20, 3, 5, 6, 9, 17, 24, 3, 6, 5, 6, 9, 24, 3, 5, 6, 9, 11, 14, 17, 24, 26, 3, 5, 6, 9, 13, 14, 17, 24, 28, 17, 24, 3, 5, 6, 9, 17, 19, 22, 24, 26, 3, 5, 6, 9, 17, 21, 22, 24, 28]
def xs_BOWTIE : List ℕ := [0x1d8ed2d96d56c00000000003f, 0x22d9412cd4b1401ff001ff0c0, 0xb31189b098e1bfe003fe00300, 0xc4622dc6e30a000003ffffc00, 0xf87c3e07020c3ffffc0000000]
def pool_BOWTIE : List ℕ := [0x80000a4340cc32, 0x780a000360d437, 0x5400030340c833, 0x8000030370c836, 0x3000080370c835, 0x54000a4370cc35, 0xa400054370cc36, 0xa400080340c833, 0x3000054340cc32, 0x2006000330c834]
def NN_BOWTIE : ℕ → ℕ
  | 4 => 2
  | 5 => 40
  | 6 => 36
  | 7 => 1
  | _ => 0
def HT_BOWTIE : ℕ → ℕ
  | 4 => 0xe69f9bc42160bc5f
  | 5 => 0xf742a3d0f3d6a6caf2c4f573e8b66066e180f3e4dc87be0edbeab3c2d93b4845d6c8153bd3b86897cf20682cc92e1222c36e694fc2da43cfb73fc6f7b64bf507b61f6228b3b81b1bb2c6c34ba8357aafa51ea19ca01014059f6d175f992962fa933e75078d7ecc3487246ed6697d7a4456dfe4dc558d03dd549ad51f4869b93243677bab3e0dcfd73c0e3e7f28b49293203432401c85f03b16c64768158068a1
  | 6 => 0xf8103679f7ee878cf2c4f573f084fb7be4e1031be2a67339d9ce2dd4d311441ec7bfd293c7633531c6b10786bd88bbf8b2c6c34bae58d960ad239bdb9f6d175f99876a0897388465933e7507917398168d7ecc348aee859b83a2b2267f1563cf7cb80320792278b673133ce4697d7a4463f740d054f0553f4b2540302c47248c231776e01a45f6430cea2d5a081c1522
  | 7 => 0x697d7a44
  | _ => 0
def PT_BOWTIE : ℕ → ℕ
  | 4 => 0xc847302
  | 5 => 0x70d40420520409410188cc1110170d0003213c406234000d4111023c409f3033c410a3406cd0152032040052306ccc1b35020404034020410810364940031028d42235028cc1c33030885f3055c40941027cc1111033c40c0303
  | 6 => 0x38c80e100040804040390c0f41010000e3003900050103cc00503004000f3203c8001010100c0e420041004010040c0e31010080f4303c840e2003cc40000039040f4203c400f40014000504014080e21
  | _ => 0
def Z_BOWTIE (s : ℕ) := bar 50 (Sgen 50 7 xs_BOWTIE PT_BOWTIE) NN_BOWTIE (idxGen NN_BOWTIE HT_BOWTIE) id pool_BOWTIE s
theorem z_BOWTIE_0 : span (Z_BOWTIE 0) 0 0 = true := rfl
theorem z_BOWTIE_1 : span (Z_BOWTIE 1) 0 0 = true := rfl
theorem z_BOWTIE_2 : span (Z_BOWTIE 2) 0 0 = true := rfl
theorem z_BOWTIE_3 : span (Z_BOWTIE 3) 0 0 = true := rfl
theorem h_BOWTIE_4_0 : span (Z_BOWTIE 4) 2 0 = true := by decide +kernel
theorem z_BOWTIE_4 : span (Z_BOWTIE 4) 2 0 = true := h_BOWTIE_4_0
theorem h_BOWTIE_5_0 : span (Z_BOWTIE 5) 12 0 = true := by decide +kernel
theorem h_BOWTIE_5_12 : span (Z_BOWTIE 5) 12 12 = true := by decide +kernel
theorem h_BOWTIE_5_24 : span (Z_BOWTIE 5) 12 24 = true := by decide +kernel
theorem h_BOWTIE_5_36 : span (Z_BOWTIE 5) 4 36 = true := by decide +kernel
theorem z_BOWTIE_5 : span (Z_BOWTIE 5) 40 0 = true := by with_reducible exact (sj (sj h_BOWTIE_5_0 h_BOWTIE_5_12) (sj h_BOWTIE_5_24 h_BOWTIE_5_36))
theorem h_BOWTIE_6_0 : span (Z_BOWTIE 6) 12 0 = true := by decide +kernel
theorem h_BOWTIE_6_12 : span (Z_BOWTIE 6) 12 12 = true := by decide +kernel
theorem h_BOWTIE_6_24 : span (Z_BOWTIE 6) 12 24 = true := by decide +kernel
theorem z_BOWTIE_6 : span (Z_BOWTIE 6) 36 0 = true := by with_reducible exact (sj h_BOWTIE_6_0 (sj h_BOWTIE_6_12 h_BOWTIE_6_24))
theorem h_BOWTIE_7_0 : span (Z_BOWTIE 7) 1 0 = true := by decide +kernel
theorem z_BOWTIE_7 : span (Z_BOWTIE 7) 1 0 = true := h_BOWTIE_7_0
theorem base_BOWTIE : ∀ s : ℕ, HasCircuitSize 5 f_BOWTIE s → 8 ≤ s := by
  refine prove_base 5 50 7 f_BOWTIE rows_BOWTIE xs_BOWTIE pool_BOWTIE NN_BOWTIE HT_BOWTIE PT_BOWTIE
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => spOK z_BOWTIE_0 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_BOWTIE_1 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_BOWTIE_2 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_BOWTIE_3 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_BOWTIE_4 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_BOWTIE_5 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_BOWTIE_6 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_BOWTIE_7 i (Nat.zero_le i) hi
    )

-- Base case NET (n=6, cap=7, k=72, states=26, pool=9)
def f_TwoK3 : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def rows_TwoK3 : List ℕ := [1, 1, 2, 2, 4, 4, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 3, 5, 3, 6, 5, 6, 24, 40, 3, 5, 6, 11, 13, 24, 25, 40, 41, 48, 3, 5, 6, 11, 14, 24, 26, 40, 42, 48, 3, 5, 6, 13, 14, 24, 28, 40, 44, 48, 24, 48, 3, 5, 6, 19, 21, 24, 25, 40, 48, 49, 3, 5, 6, 19, 22, 24, 26, 40, 48, 50, 3, 5, 6, 21, 22, 24, 28, 40, 48, 52, 40, 48, 3, 5, 6, 24, 35, 37, 40, 41, 48, 49, 3, 5, 6, 24, 35, 38, 40, 42, 48, 50, 3, 5, 6, 24, 37, 38, 40, 44, 48, 52]
def xs_TwoK3 : List ℕ := [0x4c13acc02c0b96c02c0b56c5c00003ff000003ff000003ff03, 0x96b50540565d0340555d034b400ffc00000ffc00000ffc000c, 0xad8260989781605857816058ebff000003ff000003ff0000030, 0x320c8321380e03817e1f87e3000000000000000003fffffffc0, 0xc2308c22de378de3982609810000000003fffffffc000000000, 0xfc3f0fc3e0380e02e0380e0203fffffffc00000000000000000]
def pool_TwoK3 : List ℕ := [0xc8280f06919c66, 0x9806118771b46c, 0x48080706919c66, 0x10020006719869, 0x10000086919867]
def NN_TwoK3 : ℕ → ℕ
  | 4 => 2
  | 5 => 12
  | 6 => 58
  | 7 => 49
  | 8 => 1
  | _ => 0
def HT_TwoK3 : ℕ → ℕ
  | 4 => 0x4d8c177f15c49257
  | 5 => 0xf0e5633ee7484b31a8d065f8979d3f4793f63bc08671bd54863d7f2181afece53dbda1882359e6cf198b67e50853723f
  | 6 => 0xfff2feb1fbb42ec1f805c600f741e864f4956378f1569e11edfc6b6de33c240fde836f10ddbefff4d6536b5ed4908d11cfe8ef31cdab9dedccacded6cbc2310ec568bed5ba4ccae7ba49c705b387ff19b114f671ae607e3ca911d87ca7a10ad8a32309d196921a7d95b4c51295798f3993292937929c19388caa887f8a7b658488976d8f868eb994859c9f8d807d69288041d1617e30b21078e2632b77386d21729f95276e1d55396b13cd37690c11976636a31c53d68f2d49c3ea2044353bb331b2062a31897ba42cb2ed7d28204f2e24d3f01c20c002c41f2967b51d792b3f1c8bb31a0e1442b5
  | 7 => 0xf805c600f35b4616e5e0c18ae59fd215e4eeedf8ddbefff4da55ffa0cddc75e9cbb17652ca742a1bc87d2041c780807ac4cd528ec4852d77c0d065f9b72faa58b33f4aeba911d87ca32712718b7dca57859c9f8d83d6d5dc839707388036fa067963bc88788c92f66f6896bd6edcc4e06e513d8b6cfc2284600dbbaa4eac3ae54ab8d6c54a3175144723967344353bb343db4bcc39a4161334e138ec345fccb131897ba42eb8073529c048df29a9ef5c26bc3c25229404c81f2967b5108017bc05304534
  | 8 => 0xa911d87c
  | _ => 0
def PT_TwoK3 : ℕ → ℕ
  | 4 => 0xc404301
  | 5 => 0x38885422160d441321c8c86f32148885820504880f32164c499202
  | 6 => 0x6480c21057c404e32130c84e350a8d00c30630c15f10438d81c10200d00335020406a36078d802101704143303a8d42020600c40210300d40336078d40e34034405a22130c0de3040cc85e32170000810200cc1d20634411a20378c0c2102a8cc1626020410210438cc0d000048c08000ac408c3040cd00d10508000036000c848105
  | 7 => 0x101039080e5003d440f40004100e20038c00f5203cc40f3001404050003d4005020140c0f53000000e5303d500105039440f2003c840f23010040f43039040504039480e23039000402010140e43004000e54010100f42038c401030100c0f4101000050503884010203c400e10
  | _ => 0
def Z_TwoK3 (s : ℕ) := bar 102 (Sgen 102 8 xs_TwoK3 PT_TwoK3) NN_TwoK3 (idxGen NN_TwoK3 HT_TwoK3) id pool_TwoK3 s
theorem z_TwoK3_0 : span (Z_TwoK3 0) 0 0 = true := rfl
theorem z_TwoK3_1 : span (Z_TwoK3 1) 0 0 = true := rfl
theorem z_TwoK3_2 : span (Z_TwoK3 2) 0 0 = true := rfl
theorem z_TwoK3_3 : span (Z_TwoK3 3) 0 0 = true := rfl
theorem h_TwoK3_4_0 : span (Z_TwoK3 4) 2 0 = true := by decide +kernel
theorem z_TwoK3_4 : span (Z_TwoK3 4) 2 0 = true := h_TwoK3_4_0
theorem h_TwoK3_5_0 : span (Z_TwoK3 5) 12 0 = true := by decide +kernel
theorem z_TwoK3_5 : span (Z_TwoK3 5) 12 0 = true := h_TwoK3_5_0
theorem h_TwoK3_6_0 : span (Z_TwoK3 6) 12 0 = true := by decide +kernel
theorem h_TwoK3_6_12 : span (Z_TwoK3 6) 12 12 = true := by decide +kernel
theorem h_TwoK3_6_24 : span (Z_TwoK3 6) 12 24 = true := by decide +kernel
theorem h_TwoK3_6_36 : span (Z_TwoK3 6) 12 36 = true := by decide +kernel
theorem h_TwoK3_6_48 : span (Z_TwoK3 6) 10 48 = true := by decide +kernel
theorem z_TwoK3_6 : span (Z_TwoK3 6) 58 0 = true := by with_reducible exact (sj (sj h_TwoK3_6_0 h_TwoK3_6_12) (sj h_TwoK3_6_24 (sj h_TwoK3_6_36 h_TwoK3_6_48)))
theorem h_TwoK3_7_0 : span (Z_TwoK3 7) 12 0 = true := by decide +kernel
theorem h_TwoK3_7_12 : span (Z_TwoK3 7) 12 12 = true := by decide +kernel
theorem h_TwoK3_7_24 : span (Z_TwoK3 7) 12 24 = true := by decide +kernel
theorem h_TwoK3_7_36 : span (Z_TwoK3 7) 12 36 = true := by decide +kernel
theorem h_TwoK3_7_48 : span (Z_TwoK3 7) 1 48 = true := by decide +kernel
theorem z_TwoK3_7 : span (Z_TwoK3 7) 49 0 = true := by with_reducible exact (sj (sj h_TwoK3_7_0 h_TwoK3_7_12) (sj h_TwoK3_7_24 (sj h_TwoK3_7_36 h_TwoK3_7_48)))
theorem h_TwoK3_8_0 : span (Z_TwoK3 8) 1 0 = true := by decide +kernel
theorem z_TwoK3_8 : span (Z_TwoK3 8) 1 0 = true := h_TwoK3_8_0
theorem base_TwoK3 : ∀ s : ℕ, HasCircuitSize 6 f_TwoK3 s → 9 ≤ s := by
  refine prove_base 6 102 8 f_TwoK3 rows_TwoK3 xs_TwoK3 pool_TwoK3 NN_TwoK3 HT_TwoK3 PT_TwoK3
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => spOK z_TwoK3_0 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_TwoK3_1 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_TwoK3_2 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_TwoK3_3 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_TwoK3_4 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_TwoK3_5 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_TwoK3_6 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_TwoK3_7 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_TwoK3_8 i (Nat.zero_le i) hi
    )

-- Base case K3C5 (n=6, cap=8, k=88, states=111, pool=5)
def f_K3C5 : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def rows_K3C5 : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 20, 20, 20, 24, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 3, 5, 9, 3, 6, 18, 5, 6, 9, 40, 3, 5, 6, 9, 11, 14, 18, 26, 40, 42, 48, 13, 14, 44, 18, 48, 3, 5, 6, 9, 18, 19, 21, 25, 40, 48, 49, 21, 22, 52, 25, 26, 56, 3, 5, 6, 9, 18, 29, 30, 40, 48, 60, 40, 48, 3, 5, 6, 9, 18, 35, 37, 40, 41, 48, 49, 3, 5, 6, 9, 18, 35, 38, 40, 42, 48, 50, 3, 5, 6, 9, 18, 37, 38, 40, 44, 48, 52]
def xs_K3C5 : List ℕ := [0x560aeb5815933ac206d4f000003ff80001ffc000007, 0xab5d41a82aa40d54bd4b9001ffc00000000001ffc38, 0xacc118231330e118e098d2ffe000001ff8e000e000c0, 0x310620c437470620eee304000000001fff0000ffff00, 0xc21843085b87fbc3130020000000001fffffff000000, 0xfc1f83f07c049c029c0200ffffffffe0000000000000]
def pool_K3C5 : List ℕ := [0x108371345c16458, 0xd418028611746c, 0xd4080686c16861, 0x1803000591605c, 0x180000c5c16059]
def NN_K3C5 : ℕ → ℕ
  | 5 => 2
  | 6 => 59
  | 7 => 49
  | 8 => 1
  | _ => 0
def HT_K3C5 : ℕ → ℕ
  | 5 => 0xaf7f705075df09eb
  | 6 => 0xff05e072f727b177f3068765eaa33932db11b933d8cc5b6dcd35058ccc15227dca2f76a5c83ad31bc7250273c15a0367b4a0336cb10a8789afa7431baca18245a8900a13a2695142a1496e339ff66ae49c594e299b4c90679920e7e69912aafc9669f83595b74714954a15269059f51c8b53f7cd85bd41f47c32030e752ab69a72c697296f78934d6d024dd56a88734369689034692b5d8d653017b36252b02e43fac3934359dbb44239f8a53d49d89b37e19f5a2dcc7be728df8ae4233bb3a41f61f4541e1edb431b5f2e0917711a07161b410c15acbf2f11a788f510e7b25a08bdd900062edfb000979a5e
  | 7 => 0xfad5aba9f2eecca3e97ae7ace6bcb686e3778b7fe03ffe4fd963b263d4da459cd3c109c0d32c8367cea5d07ecbb58782cb9bad62c03ecc65bd3d402baec4164fab8da282aa9335c4a77738ef9ff66ae49a72143c980ef4d38d5b9238853ae9e8813088c1801c66e67c90fda2795c361d752ab69a692b5d8d652373366061f0715bb0fd5d57c5b116504f73f14825eea6435ca5264359dbb44239f8a53d49d89b38731eb53663a28d345f23502a623341161b410c13fb51330a946a4a0112919d00f8fd3a
  | 8 => 0x161b410c
  | _ => 0
def PT_K3C5 : ℕ → ℕ
  | 5 => 0x1cc848302
  | 6 => 0x141013cd413101bcc0d533040d80b10128406f3604c410910144c12c23054d01130554d42e3402c410a10510400910444c181321a8814b10384818a10324409634070d41635010411536028411a3052440c910510409035058d82e3031040c410510404135004d01033040d02f30404d80c22104cc01310b8d81130358cc2f35064982e350
  | 7 => 0xe510394c0e210100c0f10014100f50010140e40014080501038c40f54014000f4103d440f4003cc00401004000e2303cc40e4203d0c0404010080e10039040104004080e50039500e300390c0f53039480f210040c0105004040f20010000f4203d4800000140c0f23038800505
  | _ => 0
def Z_K3C5 (s : ℕ) := bar 88 (Sgen 88 8 xs_K3C5 PT_K3C5) NN_K3C5 (idxGen NN_K3C5 HT_K3C5) id pool_K3C5 s
theorem z_K3C5_0 : span (Z_K3C5 0) 0 0 = true := rfl
theorem z_K3C5_1 : span (Z_K3C5 1) 0 0 = true := rfl
theorem z_K3C5_2 : span (Z_K3C5 2) 0 0 = true := rfl
theorem z_K3C5_3 : span (Z_K3C5 3) 0 0 = true := rfl
theorem z_K3C5_4 : span (Z_K3C5 4) 0 0 = true := rfl
theorem h_K3C5_5_0 : span (Z_K3C5 5) 2 0 = true := by decide +kernel
theorem z_K3C5_5 : span (Z_K3C5 5) 2 0 = true := h_K3C5_5_0
theorem h_K3C5_6_0 : span (Z_K3C5 6) 12 0 = true := by decide +kernel
theorem h_K3C5_6_12 : span (Z_K3C5 6) 12 12 = true := by decide +kernel
theorem h_K3C5_6_24 : span (Z_K3C5 6) 12 24 = true := by decide +kernel
theorem h_K3C5_6_36 : span (Z_K3C5 6) 12 36 = true := by decide +kernel
theorem h_K3C5_6_48 : span (Z_K3C5 6) 11 48 = true := by decide +kernel
theorem z_K3C5_6 : span (Z_K3C5 6) 59 0 = true := by with_reducible exact (sj (sj h_K3C5_6_0 h_K3C5_6_12) (sj h_K3C5_6_24 (sj h_K3C5_6_36 h_K3C5_6_48)))
theorem h_K3C5_7_0 : span (Z_K3C5 7) 12 0 = true := by decide +kernel
theorem h_K3C5_7_12 : span (Z_K3C5 7) 12 12 = true := by decide +kernel
theorem h_K3C5_7_24 : span (Z_K3C5 7) 12 24 = true := by decide +kernel
theorem h_K3C5_7_36 : span (Z_K3C5 7) 12 36 = true := by decide +kernel
theorem h_K3C5_7_48 : span (Z_K3C5 7) 1 48 = true := by decide +kernel
theorem z_K3C5_7 : span (Z_K3C5 7) 49 0 = true := by with_reducible exact (sj (sj h_K3C5_7_0 h_K3C5_7_12) (sj h_K3C5_7_24 (sj h_K3C5_7_36 h_K3C5_7_48)))
theorem h_K3C5_8_0 : span (Z_K3C5 8) 1 0 = true := by decide +kernel
theorem z_K3C5_8 : span (Z_K3C5 8) 1 0 = true := h_K3C5_8_0
theorem base_K3C5 : ∀ s : ℕ, HasCircuitSize 6 f_K3C5 s → 9 ≤ s := by
  refine prove_base 6 88 8 f_K3C5 rows_K3C5 xs_K3C5 pool_K3C5 NN_K3C5 HT_K3C5 PT_K3C5
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => spOK z_K3C5_0 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3C5_1 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3C5_2 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3C5_3 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3C5_4 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3C5_5 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3C5_6 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3C5_7 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3C5_8 i (Nat.zero_le i) hi
    )




def gfn {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) : BFn n :=
  fun x => A.any (fun a => x a) || E.any (fun e => x e.1 && x e.2)

def Eb_K3 : List (Fin 3 × Fin 3) := [(0,1),(0,2),(1,2)]
def Eb_C5 : List (Fin 5 × Fin 5) := [(0,1),(0,2),(1,3),(2,4),(3,4)]
def Eb_BOWTIE : List (Fin 5 × Fin 5) := [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)]
def Eb_TwoK3 : List (Fin 6 × Fin 6) := [(0,1),(0,2),(1,2),(3,4),(3,5),(4,5)]
def Eb_K3C5 : List (Fin 6 × Fin 6) := [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,5)]

theorem base_K3_gfn : ∀ s, HasCircuitSize 3 (gfn [] Eb_K3) s → 4 ≤ s := by
  have : gfn [] Eb_K3 = f_K3 := by funext x; simp [gfn, Eb_K3, f_K3, Bool.or_assoc]
  rw [this]; exact base_K3

theorem base_C5_gfn : ∀ s, HasCircuitSize 5 (gfn [] Eb_C5) s → 7 ≤ s := by
  have : gfn [] Eb_C5 = f_C5 := by funext x; simp [gfn, Eb_C5, f_C5, Bool.or_assoc]
  rw [this]; exact base_C5

theorem base_BOWTIE_gfn : ∀ s, HasCircuitSize 5 (gfn [] Eb_BOWTIE) s → 8 ≤ s := by
  have : gfn [] Eb_BOWTIE = f_BOWTIE := by funext x; simp [gfn, Eb_BOWTIE, f_BOWTIE, Bool.or_assoc]
  rw [this]; exact base_BOWTIE

theorem base_TwoK3_gfn : ∀ s, HasCircuitSize 6 (gfn [] Eb_TwoK3) s → 9 ≤ s := by
  have : gfn [] Eb_TwoK3 = f_TwoK3 := by funext x; simp [gfn, Eb_TwoK3, f_TwoK3, Bool.or_assoc]
  rw [this]; exact base_TwoK3

theorem base_K3C5_gfn : ∀ s, HasCircuitSize 6 (gfn [] Eb_K3C5) s → 9 ≤ s := by
  have : gfn [] Eb_K3C5 = f_K3C5 := by funext x; simp [gfn, Eb_K3C5, f_K3C5, Bool.or_assoc]
  rw [this]; exact base_K3C5

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

theorem conj_2 : ∀ t : ℕ, HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) t → 4 ≤ t := by
  have heq : (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) = gfn (n := 3) [] [(0, 1), (0, 2), (1, 2)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 3 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn

theorem conj_14 : ∀ t : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) t → 7 ≤ t := by
  have heq : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) = gfn (n := 5) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (p := (4 : Fin 5)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 5)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 5 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 5)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 5 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))

theorem conj_15 : ∀ t : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) t → 7 ≤ t := by
  have heq : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) = gfn (n := 5) [] [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_base (E := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)]) (Eb := Eb_C5) (fun i : Fin 5 => match i.val with | 0 => (0 : Fin 5) | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (3 : Fin 5) | 4 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base_C5_gfn

theorem conj_16 : ∀ t : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) t → 8 ≤ t := by
  have heq : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) = gfn (n := 5) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (Eb := Eb_BOWTIE) (fun i : Fin 5 => match i.val with | 0 => (0 : Fin 5) | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (3 : Fin 5) | 4 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base_BOWTIE_gfn

theorem conj_31 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) t → 8 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5)]) (p := (4 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (p := (5 : Fin 6)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)))

theorem conj_33 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) t → 8 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5)]) (p := (4 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (p := (5 : Fin 6)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)))

theorem conj_34 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) t → 8 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)]) (p := (4 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (p := (5 : Fin 6)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)))

theorem conj_35 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) t → 8 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)]) (p := (5 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (p := (4 : Fin 6)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)))

theorem conj_36 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) t → 8 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 4), (2, 5), (4, 5)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 4), (2, 5), (4, 5)]) (Eb := Eb_C5) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 5) | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (0 : Fin 5) | 4 => (3 : Fin 5) | 5 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base_C5_gfn)

theorem conj_37 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) t → 9 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_base (E := [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)]) (Eb := Eb_TwoK3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 6) | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 5 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base_TwoK3_gfn

theorem conj_39 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) t → 9 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)]) (p := (5 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (Eb := Eb_BOWTIE) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 5) | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (3 : Fin 5) | 4 => (4 : Fin 5) | 5 => (0 : Fin 5) | _ => (0 : Fin 5)) (by decide) base_BOWTIE_gfn)

theorem conj_40 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) t → 9 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) (p := (5 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (Eb := Eb_BOWTIE) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 5) | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (3 : Fin 5) | 4 => (4 : Fin 5) | 5 => (0 : Fin 5) | _ => (0 : Fin 5)) (by decide) base_BOWTIE_gfn)

theorem conj_41 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) t → 9 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) (Eb := Eb_K3C5) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 6) | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 5 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base_K3C5_gfn



namespace Reduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem base2 : ∀ s, HasCircuitSize 3 (gfn [] [(0, 1), (0, 2), (1, 2)]) s → 4 ≤ s := by
  have heq : (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) = gfn (n := 3) [] [(0, 1), (0, 2), (1, 2)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_2

theorem base14 : ∀ s, HasCircuitSize 5 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) s → 7 ≤ s := by
  have heq : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) = gfn (n := 5) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_14

theorem base15 : ∀ s, HasCircuitSize 5 (gfn [] [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)]) s → 7 ≤ s := by
  have heq : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) = gfn (n := 5) [] [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_15

theorem base16 : ∀ s, HasCircuitSize 5 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) s → 8 ≤ s := by
  have heq : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) = gfn (n := 5) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_16

theorem base31 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5)]) s → 8 ≤ s := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_31

theorem base33 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5)]) s → 8 ≤ s := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_33

theorem base34 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)]) s → 8 ≤ s := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_34

theorem base35 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)]) s → 8 ≤ s := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_35

theorem base36 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)]) s → 8 ≤ s := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_36

theorem base37 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)]) s → 9 ≤ s := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_37

theorem base39 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)]) s → 9 ≤ s := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_39

theorem base40 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) s → 9 ≤ s := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_40

theorem base41 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) s → 9 ≤ s := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_41

theorem node1 : ∀ s, HasCircuitSize 7 (gfn [6] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) s → 9 ≤ s := by
  exact gfn_fix0 (A := [6]) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (3 : Fin 5) | 4 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base16)

theorem node2 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4), (5, 6)]) s → 10 ≤ s := by
  exact gfn_fix1 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4), (5, 6)]) (p := (5 : Fin 7)) (A' := [6]) (E' := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) node1

theorem node3 : ∀ s, HasCircuitSize 7 (gfn [3] [(0, 1), (0, 2), (0, 4), (1, 2), (4, 6)]) s → 8 ≤ s := by
  exact gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (0, 4), (1, 2), (4, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 4), (1, 2), (4, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 4), (1, 2), (4, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 4 => (3 : Fin 5) | 6 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base14)

theorem node4 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (4, 6)]) s → 10 ≤ s := by
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (4, 6)]) (p := (5 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (4, 6)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (0, 4), (1, 2), (4, 6)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (4, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (4 : Fin 6) | 4 => (3 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base31) node3

theorem node5 : ∀ s, HasCircuitSize 7 (gfn [3] [(0, 1), (0, 2), (1, 2), (1, 4), (4, 6)]) s → 8 ≤ s := by
  exact gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2), (1, 4), (4, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (1, 4), (4, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2), (1, 4), (4, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (fun i : Fin 7 => match i.val with | 0 => (1 : Fin 5) | 2 => (2 : Fin 5) | 4 => (3 : Fin 5) | 6 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base14)

theorem node6 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 6)]) s → 10 ≤ s := by
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 6)]) (p := (5 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (4, 6)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2), (1, 4), (4, 6)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (4, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5)]) (fun i : Fin 7 => match i.val with | 0 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (4 : Fin 6) | 4 => (3 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base33) node5

theorem node7 : ∀ s, HasCircuitSize 7 (gfn [4] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) s → 8 ≤ s := by
  exact gfn_fix0 (A := [4]) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (3 : Fin 5) | 5 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base14)

theorem node8 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 6)]) s → 10 ≤ s := by
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 6)]) (p := (6 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)]) (A1 := [4]) (E1 := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 5 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base34) node7

theorem node9 : ∀ s, HasCircuitSize 7 (gfn [5] [(0, 1), (0, 2), (1, 2)]) s → 5 ≤ s := by
  exact gfn_fix0 (A := [5]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := [(0, 1), (0, 2), (1, 2)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | _ => (0 : Fin 3)) (by decide) base2)

theorem node10 : ∀ s, HasCircuitSize 7 (gfn [5] [(0, 1), (0, 2), (0, 3), (1, 2)]) s → 6 ≤ s := by
  exact gfn_fix0 (A := [5]) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 7)) (A' := [5]) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) node9

theorem node11 : ∀ s, HasCircuitSize 7 (gfn [5, 3] [(0, 1), (0, 2), (1, 2)]) s → 6 ≤ s := by
  exact gfn_fix0 (A := [5, 3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 7)) (A' := [5]) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) node9

theorem node12 : ∀ s, HasCircuitSize 7 (gfn [5] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) s → 8 ≤ s := by
  exact gfn_branch2 (A := [5]) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (p := (4 : Fin 7)) (A0 := [5]) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [5, 3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) node10 node11

theorem node13 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5), (5, 6)]) s → 10 ≤ s := by
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5), (5, 6)]) (p := (6 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)]) (A1 := [5]) (E1 := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 5 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base35) node12

theorem node14 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (4, 5), (4, 6), (5, 6)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (4, 5), (4, 6), (5, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (4, 5), (4, 6), (5, 6)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2), (4, 5), (4, 6), (5, 6)]) (Eb := [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 4 => (3 : Fin 6) | 5 => (4 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base37)

theorem node15 : ∀ s, HasCircuitSize 7 (gfn [3] [(0, 1), (0, 2), (1, 4), (2, 5), (4, 5)]) s → 8 ≤ s := by
  exact gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 4), (2, 5), (4, 5)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 4), (2, 5), (4, 5)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 4), (2, 5), (4, 5)]) (Eb := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 4 => (3 : Fin 5) | 5 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base15)

theorem node16 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6), (4, 5)]) s → 10 ≤ s := by
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6), (4, 5)]) (p := (6 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 4), (2, 5), (4, 5)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 5 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base36) node15

theorem node18 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (3, 4)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (3, 4)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (1, 2), (3, 4)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (1, 2), (3, 4)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base39)

theorem node19 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 6), (3, 4)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 6), (3, 4)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 6), (3, 4)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 6), (3, 4)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base40)

theorem node20 : ∀ s, HasCircuitSize 7 (gfn [5] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) s → 9 ≤ s := by
  exact gfn_fix0 (A := [5]) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (3 : Fin 5) | 4 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base16)

theorem node21 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4), (5, 6)]) s → 11 ≤ s := by
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4), (5, 6)]) (p := (6 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)]) (A1 := [5]) (E1 := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 5 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base39) node20

theorem node22 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 6), (3, 4)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 6), (3, 4)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 6), (3, 4)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 6), (3, 4)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base40)

theorem node24 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (3, 6)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (3, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4), (3, 6)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4), (3, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (3 : Fin 6) | 2 => (4 : Fin 6) | 3 => (1 : Fin 6) | 4 => (2 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base40)

theorem node25 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (5, 6)]) s → 11 ≤ s := by
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (5, 6)]) (p := (6 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) (A1 := [5]) (E1 := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 5 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base40) node20

theorem node26 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 6), (5, 6)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 6), (5, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 5), (3, 6), (5, 6)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 5), (3, 6), (5, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 5 => (4 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base41)

theorem node34 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5), (5, 6)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5), (5, 6)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 5 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base41)

theorem shard01 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node2

theorem shard02 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (4, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node4

theorem shard03 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node6

theorem shard04 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node8

theorem shard05 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node13

theorem shard06 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (4, 5), (4, 6), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node14

theorem shard07 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6), (4, 5)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node16

theorem shard09 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (3, 4)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node18

theorem shard10 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 6), (3, 4)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node19

theorem shard11 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) t → 11 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node21

theorem shard12 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 6), (3, 4)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node22

theorem shard14 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (3, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node24

theorem shard15 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) t → 11 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node25

theorem shard16 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 6), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node26

theorem shard22 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node34

end Reduction

namespace Reduction
open PEqualNP.MetaComplexity 

theorem row17_of_row0 (base : ∀ s, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) s → 10 ≤ s) :
    ∀ s, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) s → 11 ≤ s := by
  have base' : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)]) s → 10 ≤ s := by
    have he : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) = gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)] := by
      funext x
      simp [gfn, Bool.or_assoc]
    rw [← he]
    exact base
  have child : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (3, 6), (5, 6)]) s → 10 ≤ s :=
    gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (3, 6), (5, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)])
      (fun i : Fin 7 => match i.val with
        | 1 => (1 : Fin 6) | 2 => 2 | 3 => 3 | 5 => 4 | 6 => 5 | _ => 0) (by decide) base'
  have he : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) = gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (3, 6), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [he]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (3, 6), (5, 6)]) (p := (4 : Fin 7))
    (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (3, 6), (5, 6)]) (k := 10) (by decide) (by decide)
    (by decide) (by decide) child

theorem row21_of_row0 (base : ∀ s, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) s → 10 ≤ s) :
    ∀ s, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) s → 11 ≤ s := by
  have base' : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)]) s → 10 ≤ s := by
    have he : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) = gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)] := by
      funext x
      simp [gfn, Bool.or_assoc]
    rw [← he]
    exact base
  have child : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (3, 6), (5, 6)]) s → 10 ≤ s :=
    gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (3, 6), (5, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)])
      (fun i : Fin 7 => match i.val with
        | 1 => (1 : Fin 6) | 2 => 2 | 3 => 3 | 5 => 4 | 6 => 5 | _ => 0) (by decide) base'
  have he : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) = gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [he]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (5, 6)]) (p := (4 : Fin 7))
    (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (3, 6), (5, 6)]) (k := 10) (by decide) (by decide)
    (by decide) (by decide) child

end Reduction

theorem proveAtCap (n k cap : ℕ) (f : BFn n) (rows xs : List ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (hlen : rows.length = k + k)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun a => encL a rows) = xs)
    (hgoal : encL f rows = goal k)
    (hprop : ∀ zs ∈ xs.sublists, zs ≠ xs → (cov k zs &&& lo k) ≠ lo k)
    (bad : ¬ NatRun (mask k) (goal k) cap xs) :
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
      exact bad hcap
  · exact hprop _ (List.mem_sublists.2 hsub') he (required hr)


def covDelta (k : Nat) (up : Bool) (w : Nat) : Nat :=
  if up then diffUp k w else diff k w

def covFold (k : Nat) (up : Bool) (ws : List Nat) : Nat :=
  if up then covUp k ws else cov k ws

theorem covFold_cons (k : Nat) (up : Bool) (a : Nat) (r : List Nat) :
    covFold k up (a::r) = covDelta k up a ||| covFold k up r := by
  cases up <;> rfl

def coveredNew (k : Nat) (up : Bool) (a rest : Nat) : Bool :=
  ((covDelta k up a ||| rest) &&& lo k) == lo k

theorem covers_cons_opt (k s w : Nat) (r : List Nat) :
    covers k s (w :: r) =
      coveredNew k (r.length + 1 == s+1) w (covFold k (r.length+1 == s+1) r) := by
  by_cases hb : r.length = s <;>
    simp [covers, covUp, cov, coveredNew, covDelta, covFold, hb]

def nextCovered (k s : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  let slack := s+2-ws.length
  let m := mask k
  ws.any fun a =>
    let ra := ws.erase a
    let la := ra.length
    let ua := (la+1 == s+1)
    let ub := (la+1+1 == s+1)
    let ca := covFold k ua ra
    let cb := covDelta k ub a ||| covFold k ub ra
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      (coveredNew k ua w ca && f (tagU ws a neg false) (w :: ra)) ||
        (slack ≥ 2 && (coveredNew k ub w cb && f (tagU ws a neg true) (w :: a :: ra))))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        let l := r.length
        let u0 := (l+1 == s+1)
        let u1 := (l+1+1 == s+1)
        let u2 := (l+1+1+1 == s+1)
        let c0 := covFold k u0 r
        let c1 := covFold k u1 r
        let c1a := covDelta k u1 a ||| c1
        let c1b := covDelta k u1 b ||| c1
        let c2ab := covDelta k u2 a ||| (covDelta k u2 b ||| covFold k u2 r)
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          (coveredNew k u0 w c0 && f (tagB ws a b conj false false) (w :: r)) ||
          (slack ≥ 1 &&
            ((coveredNew k u1 w c1a && f (tagB ws a b conj true false) (w :: a :: r)) ||
             (coveredNew k u1 w c1b && f (tagB ws a b conj false true) (w :: b :: r)))) ||
          (slack ≥ 2 &&
            (coveredNew k u2 w c2ab && f (tagB ws a b conj true true) (w :: a :: b :: r))))

theorem nextCovered_eq (k s : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) :
    nextCovered k s ws f =
      next (mask k) (s+2-ws.length) ws (fun t zs => covers k s zs && f t zs) := by
  unfold nextCovered next
  simp only [covers_cons_opt, List.length_cons, covFold_cons]

def maskCount (k : Nat) (up : Bool) (i : Nat) (ws : List Nat) : Nat :=
  (ws.map (fun w => ((covDelta k up w).testBit i).toNat)).sum

def coverCount (k : Nat) (up : Bool) : List Nat → Nat × Nat × Nat
  | [] => (0,0,0)
  | a :: r =>
    let v := covDelta k up a
    let z := coverCount k up r
    (v ||| z.1, z.2.1 ||| (z.1 &&& v), z.2.2 ||| (z.2.1 &&& v))

theorem coverCount_bits (k : Nat) (up : Bool) (i : Nat) (ws : List Nat) :
    (coverCount k up ws).1.testBit i = decide (1 ≤ maskCount k up i ws) ∧
    (coverCount k up ws).2.1.testBit i = decide (2 ≤ maskCount k up i ws) ∧
    (coverCount k up ws).2.2.testBit i = decide (3 ≤ maskCount k up i ws) := by
  induction ws with
  | nil => simp [coverCount,maskCount]
  | cons a r ih =>
    have e : maskCount k up i (a::r) =
        ((covDelta k up a).testBit i).toNat + maskCount k up i r := by simp [maskCount]
    simp only [coverCount, Nat.testBit_or, Nat.testBit_and, ih.1, ih.2.1, ih.2.2, e]
    generalize (covDelta k up a).testBit i = b
    generalize maskCount k up i r = n
    cases b <;> refine ⟨?_,?_,?_⟩ <;> apply Bool.eq_iff_iff.2 <;> simp <;> omega

theorem covFold_matches (k : Nat) (up : Bool) (ws : List Nat) :
    (coverCount k up ws).1 = covFold k up ws := by
  induction ws with
  | nil => cases up <;> rfl
  | cons a r ih => simp only [coverCount,covFold_cons,ih]

theorem covFold_bits (k : Nat) (up : Bool) (i : Nat) (ws : List Nat) :
    (covFold k up ws).testBit i = decide (1 ≤ maskCount k up i ws) := by
  rw [←covFold_matches k up ws]
  exact (coverCount_bits k up i ws).1

def coverHoles (k : Nat) (up : Bool) (ws : List Nat) : Nat × Nat × Nat :=
  let x := coverCount k up ws
  let l := lo k
  (l ^^^ (l &&& x.1),l ^^^ (l &&& x.2.1),l ^^^ (l &&& x.2.2))

def missing2 (z : Nat × Nat × Nat) (a b : Nat) : Nat :=
  z.1 ||| (z.2.1 &&& (a ||| b)) ||| (z.2.2 &&& a &&& b)

def todoMask (k : Nat) (up : Bool) (r : List Nat) : Nat :=
  lo k ^^^ (lo k &&& covFold k up r)

theorem maskRemoveBits (l a b : Bool) (n : Nat) :
    (((Bool.xor l (l && decide (1 ≤ a.toNat+b.toNat+n))) ||
      ((Bool.xor l (l && decide (2 ≤ a.toNat+b.toNat+n))) && (a || b)) ||
      ((Bool.xor l (l && decide (3 ≤ a.toNat+b.toNat+n))) && a && b)) =
      (Bool.xor l (l && decide (1 ≤ n)))) := by
  cases l <;> cases a <;> cases b <;>
    first | rfl | (apply Bool.eq_iff_iff.2; simp <;> omega)

theorem missing2_bits (k : Nat) (up : Bool) (ws r : List Nat) (a b : Nat)
    (h : ∀ i, maskCount k up i ws =
      (a.testBit i).toNat+(b.testBit i).toNat+maskCount k up i r) :
    missing2 (coverHoles k up ws) a b = todoMask k up r := by
  apply Nat.eq_of_testBit_eq
  intro i
  obtain ⟨h1,h2,h3⟩ := coverCount_bits k up i ws
  simpa only [missing2,coverHoles,todoMask,Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,
    h1,h2,h3,h i,covFold_bits] using
    maskRemoveBits ((lo k).testBit i) (a.testBit i) (b.testBit i) (maskCount k up i r)

theorem missing0_eq (k : Nat) (up : Bool) {ws r : List Nat} (p : ws.Perm r) :
    missing2 (coverHoles k up ws) 0 0 = todoMask k up r := by
  apply missing2_bits; intro i
  simpa [maskCount] using (p.map (fun w => ((covDelta k up w).testBit i).toNat)).sum_eq

theorem missing1_eq (k : Nat) (up : Bool) {ws r : List Nat} (a : Nat) (p : ws.Perm (a::r)) :
    missing2 (coverHoles k up ws) (covDelta k up a) 0 = todoMask k up r := by
  apply missing2_bits; intro i
  simpa [maskCount] using (p.map (fun w => ((covDelta k up w).testBit i).toNat)).sum_eq

theorem missingAB_eq (k : Nat) (up : Bool) {ws r : List Nat} (a b : Nat) (p : ws.Perm (a::b::r)) :
    missing2 (coverHoles k up ws) (covDelta k up a) (covDelta k up b) = todoMask k up r := by
  apply missing2_bits; intro i
  simpa [maskCount,Nat.add_assoc] using (p.map (fun w => ((covDelta k up w).testBit i).toNat)).sum_eq

def passesMissing (k : Nat) (up : Bool) (w z : Nat) : Bool := (covDelta k up w &&& z) == z

theorem covers_missing (k : Nat) (up : Bool) (w : Nat) (r : List Nat) :
    passesMissing k up w (todoMask k up r) = coveredNew k up w (covFold k up r) := by
  unfold passesMissing coveredNew todoMask
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq]
  constructor <;> intro h <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    have e := congrArg (fun t : Nat => t.testBit i) h <;>
    simp only [Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor] at e ⊢ <;>
    cases h₁ : (lo k).testBit i <;> cases h₂ : (covFold k up r).testBit i <;>
    cases h₃ : (covDelta k up w).testBit i <;> simp_all
theorem anyAgree {α : Type} (xs : List α) (f g : α → Bool)
    (h : ∀ x ∈ xs, f x = g x) : xs.any f = xs.any g := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨x,hx,hh⟩
    exact ⟨x,hx,(h x hx).symm.trans hh⟩
  · rintro ⟨x,hx,hh⟩
    exact ⟨x,hx,(h x hx).trans hh⟩

def nextTallied (k s : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  let n := ws.length
  let slack := s+2-n
  let m := mask k
  let u0 := (n-1 == s+1)
  let u1 := (n == s+1)
  let u2 := (n+1 == s+1)
  let z0 := coverHoles k u0 ws
  let z1 := coverHoles k u1 ws
  let z2 := coverHoles k u2 ws
  let h2 := missing2 z2 0 0
  ws.any fun a =>
    let ra := ws.erase a
    let ha := missing2 z1 (covDelta k u1 a) 0
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      (passesMissing k u1 w ha && f (tagU ws a neg false) (w :: ra)) ||
        (slack ≥ 2 && (passesMissing k u2 w h2 && f (tagU ws a neg true) (w :: a :: ra))))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        let hb := missing2 z1 (covDelta k u1 b) 0
        let hab := missing2 z0 (covDelta k u0 a) (covDelta k u0 b)
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          (passesMissing k u0 w hab && f (tagB ws a b conj false false) (w :: r)) ||
          (slack ≥ 1 &&
            ((passesMissing k u1 w hb && f (tagB ws a b conj true false) (w :: a :: r)) ||
             (passesMissing k u1 w ha && f (tagB ws a b conj false true) (w :: b :: r)))) ||
          (slack ≥ 2 &&
            (passesMissing k u2 w h2 && f (tagB ws a b conj true true) (w :: a :: b :: r))))

theorem nextTallied_eq (k s : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) :
    nextTallied k s ws f = nextCovered k s ws f := by
  unfold nextTallied nextCovered
  refine anyAgree _ _ _ ?_
  intro a ha
  have p := List.perm_cons_erase ha
  have H0 (up : Bool) := missing0_eq k up p
  have H1 (up : Bool) := missing1_eq k up a p
  have ln : ws.length = (ws.erase a).length+1 := by simpa using p.length_eq
  apply congrArg₂ (· || ·)
  · simp only [H0,H1,covers_missing,covFold_cons,ln]
  · refine anyAgree _ _ _ ?_
    intro b hb
    have q := List.perm_cons_erase hb
    have p2 := p.trans (List.Perm.cons a q)
    have p3 : ws.Perm (b::a::((ws.erase a).erase b)) := p2.trans (.swap _ _ _)
    have both (up : Bool) := missingAB_eq k up a b p2
    have noA (up : Bool) := missing1_eq k up a p2
    have noB (up : Bool) := missing1_eq k up b p3
    have none (up : Bool) := missing0_eq k up p2
    have ln2 : ws.length = ((ws.erase a).erase b).length+1+1 := by simpa using p2.length_eq
    simp only [both,noA,noB,none,covers_missing,covFold_cons,ln2,Nat.add_sub_cancel]

def keepRunTag (t : Nat) : Bool := t == 0 || decide (48 ≤ t) || t % 4 != 0

theorem keepRunTag_zero : keepRunTag 0 = true := by decide

theorem keepRunTag_neg (ws : List Nat) (a : Nat) (save : Bool) :
    keepRunTag (tagU ws a true save) = true := by
  cases save <;> simp [keepRunTag,tagU,Bool.toNat,Nat.add_mod,Nat.mul_mod]

theorem keepRunTag_save (ws : List Nat) (a : Nat) (neg : Bool) :
    keepRunTag (tagU ws a neg true) = true := by
  cases neg <;> simp [keepRunTag,tagU,Bool.toNat,Nat.add_mod,Nat.mul_mod]

theorem keepRunTag_two (ws : List Nat) (a b : Nat) (q ka kb : Bool) :
    keepRunTag (tagB ws a b q ka kb) = true := by
  have ht : 48 ≤ tagB ws a b q ka kb := by dsimp [tagB]; omega
  simp [keepRunTag,ht]
theorem nextKeepOne {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws (fun t ys => keepRunTag t && f t ys) = true := by
  by_cases idle : neg = false ∧ save = false
  · obtain ⟨rfl,rfl⟩ := idle
    have onws : NatRun (mask k) (goal k) s ws := Run.perm p (by simpa [kept] using h)
    cases ws with
    | nil => have hl := p.length_eq; simp at hl
    | cons z zs =>
      have hl := run_len onws
      have sl : 1 ≤ s+2-(z::zs).length := by omega
      apply List.any_eq_true.2 ⟨z, by simp, ?_⟩
      rw [Bool.or_eq_true]; left
      rw [Bool.and_eq_true]; refine ⟨decide_eq_true sl,?_⟩
      apply List.any_eq_true.2 ⟨false, by simp, ?_⟩
      rw [Bool.or_eq_true]; left
      simpa [tagU,keepRunTag] using hf 0 (z::zs) onws
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
  | false =>
    have hn : neg = true := by cases neg <;> simp_all
    subst neg
    simp [kept] at ht
    simp [ht, keepRunTag_neg]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht, hsl2, keepRunTag_save]

theorem nextKeepSorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws (fun t ys => keepRunTag t && f t ys) = true := by
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
    simp only [ht, keepRunTag_two, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem nextKeepTwo {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws (fun t ys => keepRunTag t && f t ys) = true := by
  rcases le_total a b with hab | hba
  · exact nextKeepSorted hab p h f hf
  · apply nextKeepSorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem nextKeepComplete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs (fun t ys => keepRunTag t && f t ys) = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact nextKeepOne p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact nextKeepTwo p h f hf

theorem uniqueAny (xs : List Nat) (f : Nat → Bool) : xs.eraseDups.any f = xs.any f := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true,List.mem_eraseDups]

def nextDistinct (k s : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  let n := ws.length
  let slack := s+2-n
  let m := mask k
  let u0 := (n-1 == s+1)
  let u1 := (n == s+1)
  let u2 := (n+1 == s+1)
  let z0 := coverHoles k u0 ws
  let z1 := coverHoles k u1 ws
  let z2 := coverHoles k u2 ws
  let h2 := missing2 z2 0 0
  ws.eraseDups.any fun a =>
    let ra := ws.erase a
    let ha := missing2 z1 (covDelta k u1 a) 0
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      (passesMissing k u1 w ha && f (tagU ws a neg false) (w :: ra)) ||
        (slack ≥ 2 && (passesMissing k u2 w h2 && f (tagU ws a neg true) (w :: a :: ra))))) ||
    ra.eraseDups.any fun b =>
      a ≤ b && (let r := ra.erase b
        let hb := missing2 z1 (covDelta k u1 b) 0
        let hab := missing2 z0 (covDelta k u0 a) (covDelta k u0 b)
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          (passesMissing k u0 w hab && f (tagB ws a b conj false false) (w :: r)) ||
          (slack ≥ 1 &&
            ((passesMissing k u1 w hb && f (tagB ws a b conj true false) (w :: a :: r)) ||
             (passesMissing k u1 w ha && f (tagB ws a b conj false true) (w :: b :: r)))) ||
          (slack ≥ 2 &&
            (passesMissing k u2 w h2 && f (tagB ws a b conj true true) (w :: a :: b :: r))))

theorem nextDistinct_eq (k s : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) :
    nextDistinct k s ws f = nextTallied k s ws f := by
  unfold nextDistinct nextTallied
  simp only [uniqueAny]

def nextKept (k s : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  nextDistinct k s ws (fun t ys => keepRunTag t && f t ys)

theorem nextKept_complete {k s ws} (h : NatRun (mask k) (goal k) (s+1) ws)
    (f : Nat → List Nat → Bool)
    (hf : ∀ t ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    nextKept k s ws f = true := by
  rw [nextKept,nextDistinct_eq,nextTallied_eq,nextCovered_eq]
  have hbase := nextKeepComplete h s rfl ws (List.Perm.refl ws)
    (fun t ys => covers k s ys && f t ys) (fun t ys hy => by simp [covers_ok hy, hf t ys hy])
  convert hbase using 2
  funext t ys
  cases covers k s ys <;> cases keepRunTag t <;> simp

def nextDirect (k s : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  let n := ws.length
  let slack := s+2-n
  let m := mask k
  let u0 := (n-1 == s+1)
  let u1 := (n == s+1)
  let u2 := (n+1 == s+1)
  let z0 := coverHoles k u0 ws
  let z1 := coverHoles k u1 ws
  let z2 := coverHoles k u2 ws
  let h2 := missing2 z2 0 0
  ws.eraseDups.any fun a =>
    let ra := ws.erase a
    let ha := missing2 z1 (covDelta k u1 a) 0
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      (passesMissing k u1 w ha && ((neg || keepRunTag (tagU ws a false false)) && f (tagU ws a neg false) (w :: ra))) ||
        (slack ≥ 2 && (passesMissing k u2 w h2 && f (tagU ws a neg true) (w :: a :: ra))))) ||
    ra.eraseDups.any fun b =>
      a ≤ b && (let r := ra.erase b
        let hb := missing2 z1 (covDelta k u1 b) 0
        let hab := missing2 z0 (covDelta k u0 a) (covDelta k u0 b)
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          (passesMissing k u0 w hab && f (tagB ws a b conj false false) (w :: r)) ||
          (slack ≥ 1 &&
            ((passesMissing k u1 w hb && f (tagB ws a b conj true false) (w :: a :: r)) ||
             (passesMissing k u1 w ha && f (tagB ws a b conj false true) (w :: b :: r)))) ||
          (slack ≥ 2 &&
            (passesMissing k u2 w h2 && f (tagB ws a b conj true true) (w :: a :: b :: r))))

theorem nextDirect_eq (k s : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) :
    nextDirect k s ws f = nextKept k s ws f := by
  unfold nextDirect nextKept nextDistinct
  simp only [List.any_cons,List.any_nil,keepRunTag_neg,keepRunTag_save,keepRunTag_two,
    Bool.false_or,Bool.true_or,Bool.true_and]

def checkD (k : Nat) (scs : List Nat) : Nat → List Nat → Bool
  | 0, ws => !(ws == [goal k])
  | s+1, ws => !(nextDirect k s ws (fun _ zs =>
      !(scr k s scs zs) && !(checkD k scs s zs)))

theorem checkD_sound {k s ws scs} (ok : checkD k scs s ws = true) :
    ¬NatRun (mask k) (goal k) s ws := by
  intro h
  induction s generalizing ws with
  | zero => simp [checkD, zero_done h rfl] at ok
  | succ s ih =>
    let F (_ : Nat) (zs : List Nat) : Bool := !(scr k s scs zs) && !(checkD k scs s zs)
    have all : ∀ t ys, NatRun (mask k) (goal k) s ys → F t ys = true := by
      intro t ys hy
      have bad : checkD k scs s ys = false := by
        cases he : checkD k scs s ys
        · rfl
        · exact False.elim (ih he hy)
      simp [F, covers_ok hy, scr_no scs hy, bad]
    have hit := nextKept_complete h F all
    rw [checkD,nextDirect_eq] at ok
    rw [hit] at ok
    contradiction

def insertWord (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: rest => if a ≤ b then a :: b :: rest else b :: insertWord a rest

def sortWords : List Nat → List Nat
  | [] => []
  | a :: rest => insertWord a (sortWords rest)

def cpBoard (m : Nat) (xs : List Nat) : Nat → Nat → List Nat
  | 0, _ => sortWords xs
  | d+1, c => sortWords (mv m (c % 4096) (cpBoard m xs d (c / 4096)))

def checkpointHit (count : Nat → Nat) (board : Nat → Nat → List Nat)
    (lookup : Nat → List Nat → Option Nat) (s : Nat) (ws : List Nat) : Bool :=
  match lookup s ws with
  | none => false
  | some i => decide (i < count s) && ws.isPerm (board s i)

def checkpointCheck (k : Nat) (scs : List Nat) (count : Nat → Nat)
    (board : Nat → Nat → List Nat) (lookup : Nat → List Nat → Option Nat) : Nat → List Nat → Bool
  | 0, ws => !(ws == [goal k])
  | s+1, ws => !(nextDirect k s ws (fun _ zs =>
      !(scr k s scs zs) && !(checkpointHit count board lookup s zs) &&
        !(checkpointCheck k scs count board lookup s zs)))

theorem checkpointCheck_sound {k scs count board lookup}
    (closed : ∀ s i, i < count s → checkpointCheck k scs count board lookup s (board s i) = true)
    {s ws} (ok : checkpointCheck k scs count board lookup s ws = true) :
    ¬NatRun (mask k) (goal k) s ws := by
  intro h
  induction s generalizing ws with
  | zero => simp [checkpointCheck, zero_done h rfl] at ok
  | succ s ih =>
    let F (_ : Nat) (zs : List Nat) : Bool := !(scr k s scs zs) && !(checkpointHit count board lookup s zs) && !(checkpointCheck k scs count board lookup s zs)
    have all : ∀ t ys, NatRun (mask k) (goal k) s ys → F t ys = true := by
      intro t ys hy
      have nohit : checkpointHit count board lookup s ys = false := by
        cases e : lookup s ys with
        | none => simp [checkpointHit,e]
        | some i =>
          cases he : checkpointHit count board lookup s ys with
          | false => rfl
          | true =>
            have hx : (decide (i < count s) && ys.isPerm (board s i)) = true := by
              simpa only [checkpointHit,e] using he
            simp only [Bool.and_eq_true] at hx
            obtain ⟨hi,hp⟩ := hx
            exact False.elim (ih (closed s i (of_decide_eq_true hi)) (Run.perm (List.isPerm_iff.1 hp) hy))
      have bad : checkpointCheck k scs count board lookup s ys = false := by
        cases he : checkpointCheck k scs count board lookup s ys
        · rfl
        · exact False.elim (ih he hy)
      simp [F,covers_ok hy,scr_no scs hy,nohit,bad]
    have hit := nextKept_complete h F all
    rw [checkpointCheck,nextDirect_eq] at ok
    rw [hit] at ok
    contradiction

def pickRows (r : List Nat) (w : Nat) : Nat :=
  match r with
  | [] => 0
  | i :: is => Nat.bit (w.testBit i) (pickRows is w)

theorem pickRows_bit (w : Nat) : ∀ (r : List Nat) (t : Nat),
    (pickRows r w).testBit t = (r.map (fun i => w.testBit i)).getD t false
  | [], t => by simp [pickRows]
  | i :: is, 0 => by simp [pickRows,Nat.testBit_bit_zero]
  | i :: is, t+1 => by simp [pickRows,Nat.testBit_bit_succ,pickRows_bit w is t]

theorem pickRows_xor (r : List Nat) (a b : Nat) :
    pickRows r (a ^^^ b) = pickRows r a ^^^ pickRows r b := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_xor, pickRows_bit, pickRows_bit, pickRows_bit]
  by_cases h : t < r.length
  · simp [h,Nat.testBit_xor]
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem pickRows_and (r : List Nat) (a b : Nat) :
    pickRows r (a &&& b) = pickRows r a &&& pickRows r b := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_and, pickRows_bit, pickRows_bit, pickRows_bit]
  by_cases h : t < r.length
  · simp [h,Nat.testBit_and]
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem pickRows_or (r : List Nat) (a b : Nat) :
    pickRows r (a ||| b) = pickRows r a ||| pickRows r b := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_or, pickRows_bit, pickRows_bit, pickRows_bit]
  by_cases h : t < r.length
  · simp [h,Nat.testBit_or]
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    rfl


theorem transport {m y s : Nat} {ws : List Nat} (h : NatRun m y s ws) (r : List Nat) :
    NatRun (pickRows r m) (pickRows r y) s (ws.map (pickRows r)) := by
  exact Run.map (pickRows r) (fun a => pickRows_xor r a m)
    (pickRows_and r) (pickRows_or r) h


def orbitMix (x : Nat) : Nat :=
  let x := ((x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9) % 0x10000000000000000
  let x := ((x ^^^ (x >>> 27)) * 0x94d049bb133111eb) % 0x10000000000000000
  x ^^^ (x >>> 31)

def orbitLookup (tab : Nat → Nat) (seed m h : Nat) : Nat :=
  let v := h + 3*seed
  tab (orbitMix (v+1) % m) ^^^ tab (m + orbitMix (v+2) % m) ^^^ tab (2*m + orbitMix (v+3) % m)

def orbitLabel (p v : Nat) : Nat :=
  (((v >>> (fld p 3 0)) &&& 1) <<< 0) ||| (((v >>> (fld p 3 1)) &&& 1) <<< 1) ||| (((v >>> (fld p 3 2)) &&& 1) <<< 2) ||| (((v >>> (fld p 3 3)) &&& 1) <<< 3) ||| (((v >>> (fld p 3 4)) &&& 1) <<< 4) ||| (((v >>> (fld p 3 5)) &&& 1) <<< 5) ||| (((v >>> (fld p 3 6)) &&& 1) <<< 6)

def rowOrient (k : Nat) (sel : List Nat → List Nat) (ys : List Nat) : List Nat :=
  let r := sel ys
  if pickRows r (mask k) = mask k ∧ pickRows r (goal k) = goal k then ys.map (pickRows r) else ys

theorem ori_ok {k u ys} (sel : List Nat → List Nat) (h : NatRun (mask k) (goal k) u ys) :
    NatRun (mask k) (goal k) u (rowOrient k sel ys) := by
  unfold rowOrient
  dsimp only
  split
  next e =>
    have tr := transport h (sel ys)
    rw [e.1, e.2] at tr
    exact tr
  next => exact h
def cutN (s n u : Nat) := if u = s then n else 0

def cutB (s : Nat) (xs : List Nat) (board : Nat → List Nat) (u i : Nat) :=
  if u = s then board i else xs

theorem cut_root {k s n : Nat} {xs pool : List Nat}
    {board : Nat → List Nat} {idx : List Nat → Nat}
    (cover : bar k (cutB s xs board) (cutN s n) (fun _ => idx) id pool (s+1) 0 = true)
    (dead : ∀ i, i < n → ¬NatRun (mask k) (goal k) s (board i)) :
    ¬NatRun (mask k) (goal k) (s+1) xs := by
  intro h
  have hr : NatRun (mask k) (goal k) (s+1) (cutB s xs board (s+1) 0) := by
    simpa [cutB] using h
  obtain ⟨q, _, j, hj, hq⟩ := bar_sound cover (fun h => h) hr
  by_cases e : q = s
  · subst q
    exact dead j (by simpa [cutN] using hj) (by simpa [cutB] using hq)
  · simp [cutN, e] at hj
theorem symCutRoot {k s n : Nat} {xs pool : List Nat}
    {board : Nat → List Nat} {idx : List Nat → Nat}
    {ori : List Nat → List Nat}
    (perm : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (cover : bar k (cutB s xs board) (cutN s n) (fun _ => idx) ori pool (s+1) 0 = true)
    (dead : ∀ i, i < n → ¬NatRun (mask k) (goal k) s (board i)) :
    ¬NatRun (mask k) (goal k) (s+1) xs := by
  intro h
  have hr : NatRun (mask k) (goal k) (s+1) (cutB s xs board (s+1) 0) := by
    simpa [cutB] using h
  obtain ⟨q, _, j, hj, hq⟩ := bar_sound cover perm hr
  by_cases e : q = s
  · subst q
    exact dead j (by simpa [cutN] using hj) (by simpa [cutB] using hq)
  · simp [cutN, e] at hj

namespace Row0
def vals : List ℕ := [1,1,1,2,2,4,4,8,8,8,10,10,10,10,10,10,10,10,10,10,10,12,12,12,12,12,12,12,12,12,12,12,16,16,17,17,17,17,17,17,17,17,17,17,17,18,18,18,18,18,18,18,18,18,18,18,20,20,20,20,20,20,20,20,20,20,20,32,32,33,33,33,33,33,33,33,33,33,33,33,34,34,34,34,34,34,34,34,34,34,34,36,36,36,36,36,36,36,36,36,36,36,3,5,9,3,6,5,6,9,24,40,3,5,6,9,11,14,24,26,40,42,48,3,5,6,9,13,14,24,28,40,44,48,24,48,3,5,6,9,19,21,24,25,40,48,49,3,5,6,9,19,22,24,26,40,48,50,3,5,6,9,21,22,24,28,40,48,52,40,48,3,5,6,9,24,35,37,40,41,48,49,3,5,6,9,24,35,38,40,42,48,50,3,5,6,9,24,37,38,40,44,48,52]
def inputs : List ℕ := [0x560aeb5806c0dcbb00d81b2bc00000ffe000001ffc00000007,0x8b5941280965a815012ab5164007ff000000ffe000001ffc18,0xacc1182312d81302615b0261cbff8000007ff000000ffe00060,0x330660cc2720e41c85fc3f8e1000000000000000000ffffff80,0xc21843085bc3786f0e604c0400000000007ffffffff00000000,0xfc1f83f07c0380700b80700803ffffffff80000000000000000]
def scs : List ℕ := [0x1141516c6f19c68,0xe02d088671986a,0x1402d0286f1b87a,0x88151147a1a06e,0xe0220b46a19867,0x1404516c6a19c66,0x1140a1406f19868,0x880a0e06e19c68,0x1140a0887a1b86f,0x1140a054681a866,0x880a0b46e19868]
def target : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def rho (ys : List Nat) : List Nat :=
  let a := fld 0xc2442484a9320293200f4a0006d822688000 3 (bsr 0xf7831134f4fedb03ef42530ceeb6ca99dd448942d75a4f37d12435e6ceeaee09cdfdf8d5c84b49c4c0a8f783b5e46551b359a4deb279c2a1b0edf685b0147856aee40560ae8440cba181a3399de14f0f9b4f693095865b2993b4971e9375f304880f16b08715b59f73aa60ef6f5f01b26e5e2e6b6decb162639a36156375fee9527a8cb85157812a493de4eb4577ef263b056ff32e79e25f2c0f0be325862c5321a9d46920ee1b271e6cd2651774472c1683bb1211c516140dd37f0e0aa5544e073f6720 32 (hk ys) 6 0 49)
  if a=0 || 6<a then [] else
    let c := fld 0x6444af142c791163d2b28695a2358ca000000 21 a
    vals.map (fun v => fld 0xa8009d927a000000840079b36f00bcb15bb05045430000008200778f6e00988d388c2d222000757f15740a6807006a670566030000 8 (orbitLabel c v))
def B (i : Nat) := mv (mask 102) (fld 0xe21e30e41105505f41503f31f30000f10400e40401f21103e10 12 i) inputs
def I (ys : List Nat) := bsr 0xf7831134ef42530cd12435e6ae8440cba181a339880f16b08715b59f639a36156375fee9527a8cb85157812a2c0f0be31683bb1211c516140dd37f0e0aa5544e073f6720 32 (hk ys) 5 0 17
def test (i : Nat) := checkD 102 scs 8 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 102 (cutB 8 inputs B) (cutN 8 17) (fun _ => I) (rowOrient 102 rho) scs 9 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 4 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z4 : span test 4 4 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z8 : span test 4 8 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z12 : span test 2 12 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z14 : span test 3 14 = true := by decide +kernel
lemma regionOK : span test 17 0 = true := by with_reducible exact (sj (sj z0 z4) (sj z8 (sj z12 z14)))
theorem finChk : ¬NatRun (mask 102) (goal 102) 9 inputs :=
  symCutRoot (ori_ok rho) roof (fun i hi => checkD_sound (spOK regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 6 target t → 10 ≤ t := by
  refine proveAtCap 6 102 9 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row0

namespace Row8
def vals : List ℕ := [1,1,2,2,4,4,6,6,6,8,8,9,9,9,12,12,12,12,16,16,17,17,17,18,18,18,18,24,24,24,24,25,25,25,25,25,25,25,25,25,25,25,32,32,33,33,33,33,34,34,34,36,36,36,36,38,38,38,38,38,38,38,38,38,38,38,48,48,48,49,49,49,49,49,49,49,49,49,49,49,50,50,50,50,50,50,50,50,50,50,50,64,64,65,65,65,65,66,66,66,66,68,68,68,70,70,70,70,70,70,70,70,70,70,70,72,72,72,73,73,73,73,73,73,73,73,73,73,73,76,76,76,76,76,76,76,76,76,76,76,3,5,3,10,5,20,7,14,22,10,40,11,13,41,13,14,28,44,20,80,19,21,81,19,22,26,82,26,28,56,88,3,5,10,20,27,29,40,57,80,89,96,40,96,35,37,41,97,35,42,98,37,44,52,100,3,5,10,20,39,40,46,54,80,96,102,52,56,112,3,5,10,20,40,51,53,57,80,96,113,3,5,10,20,40,51,54,58,80,96,114,80,96,67,69,81,97,67,74,82,98,69,84,100,3,5,10,20,40,71,78,80,86,96,102,74,88,104,3,5,10,20,40,75,77,80,89,96,105,3,5,10,20,40,77,78,80,92,96,108]
def inputs : List ℕ := [0x4758c02323e0239c600989f15980f07857001ffc00001e000ffe00000f3ff80703803,0x8a094d651e24e504a26a87100a8f908bcd0000007ff1e07ff0003ff870000078001cc,0xad412856ae0404a09466d7820151127d1f2ffe0007ffe000000003fff800000003c1f0,0xae95d385404009412883212457a7a03fe88ffffff8000000000000000003fff803fe00,0x310621188488de8bd1cc42001dc7ffd01200000000000007fffffc000003fffffc0000,0xc218426109116f0de1f787ffe60200224000000000000007fffffffffffc0000000000,0xfc1f83fe0ffff00e01380448b8044480000ffffffffffff80000000000000000000000]
def scs : List ℕ := [0x1d8682048f2348c,0x1d84507c9f258b5,0x1a0500dcb52449f,0xdc1f114962308f,0xdc1f140912308d,0x1d8371a0b523c96,0x1a01f1d89f23491]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def rho (ys : List Nat) : List Nat :=
  let a := fld 0x390316102385a747615795325321322065498800498870526050420542332101 4 (bsr 0xffb93cdefabd6fedf7423f9ff582b9f1f3eea8d9f1d7b75be9e8d5bae5792811e114fcb2df5d4d4adc65c784da702df4d622589bcfb96cf1cec4936bca9679c0c7c1e596c27abfbebd935c50b84dff99b6afeed9b5124aadb06b5123abf9511da91b880da8bfc72fa3016442a219af959d6d03769cd84ac39b5f3f3a969bfb69910afed88cf5763a8579a19a804750dd7e6767d87d7567f679c1958678a4f16178a3812770f9676d6a3fff10689e704a676cd73d647d8899587d0c395843e1385545aa6351ec39f451744c1d4a197648498a981d3dcd5e1a391e942f367f10d32e65260a29ce9e4826bdf0a919042b95183e48a70fd8f69e0644477e063cd20e 32 (hk ys) 7 0 64)
  if a=0 || 10<a then [] else
    let c := fld 0x463d66543243566d2a60c5852ee70a058ab4421cea831aebc60400000 21 a
    vals.map (fun v => fld 0x399b6d00000001170000219010033400c2002f976b50000001150000168aa003f000f200299449f003ea108183bb8ec737c9a1d46574984ba5b0000000000038d64a900329aec16b1408a4200324009d002f53296638dd72335c0c0582a00001609c57a943e1b0025142915005c28120024d300e4ba3c1609490191a04460080000 9 (orbitLabel c v))
def B (i : Nat) := mv (mask 140) (fld 0xe10f41506e54000400f40f10106e41 12 i) inputs
def I (ys : List Nat) := bsr 0xf7423f9fe5792811969bfb6979c1958678a4f161647d889951ec39f44a197648391e942f0644477e 32 (hk ys) 4 0 10
def test (i : Nat) := checkD 140 scs 8 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 140 (cutB 8 inputs B) (cutN 8 10) (fun _ => I) (rowOrient 140 rho) scs 9 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 2 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z2 : span test 3 2 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z5 : span test 2 5 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z7 : span test 3 7 = true := by decide +kernel
lemma regionOK : span test 10 0 = true := by with_reducible exact (sj (sj z0 z2) (sj z5 z7))
theorem finChk : ¬NatRun (mask 140) (goal 140) 9 inputs :=
  symCutRoot (ori_ok rho) roof (fun i hi => checkD_sound (spOK regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 10 ≤ t := by
  refine proveAtCap 7 140 9 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row8

namespace Fixed40

def raw : List Nat := [0x9b24d97cd883b485b53e0000001ffc000000000f, 0x1454a2a862d76517352e200000000003ff83ff870, 0x3861c30c8338463826345ff8ffc6001c001c00180, 0x2289d471142188bdb8c08000fff80000001fffe00, 0x3b0f1842183df0e1c0811fff0000001fffe000000, 0x3c0fe07fe046000600081fffffffffe0000000000]

def pool : List Nat := [0x11c2a0e85b14c54, 0xe80b0a85214456, 0xa80b06c5b14453, 0xa81b11c5715051, 0x11c2a06c5415852, 0x11c0b0a85414c5b, 0xe82a02c5315852, 0xa80b0e85315851, 0xe82a06c5b14853]

def N : Nat → Nat
  | 4 => 1
  | 5 => 39
  | 6 => 215
  | 7 => 396
  | 8 => 212
  | 9 => 10
  | _ => 0

def S9 : Nat → List Nat
  | 0 => 0x0 :: raw
  | 1 => 0x0 :: 0x0 :: raw
  | 2 => 0x0 :: 0x3ffffffffffffffffffffffffffffffffffffffff :: raw
  | 3 => 0x3ffffffffffffffffffffffffffffffffffffffff :: raw
  | 4 => 0x0 :: 0x9b24d97cd883b485b53e0000001ffc000000000f :: raw
  | 5 => 0x0 :: 0x1454a2a862d76517352e200000000003ff83ff870 :: raw
  | 6 => 0x0 :: 0x3861c30c8338463826345ff8ffc6001c001c00180 :: raw
  | 7 => 0x0 :: 0x2289d471142188bdb8c08000fff80000001fffe00 :: raw
  | 8 => 0x0 :: 0x3b0f1842183df0e1c0811fff0000001fffe000000 :: raw
  | _ => 0x0 :: 0x3c0fe07fe046000600081fffffffffe0000000000 :: raw

def S8 (i : Nat) := let c := fld 0x5065b50010311030e52010611056b708b7001017f3241070b3055073e513f6576734b704b4091049103910556715772350277723e54710335059b104104210795017b100e423504510600002b403f320e643f210500610265070e4151027102150721045b6057740e633f5436620b60867371062b703f64777487723f424b3035010f650e543f530e51277431017b60076181024f64050211073e625107376351053f5205040f3005055b4026730503010245073105877411040f21467304003e639102277281030f543f418b103f513e210b40477106620b200f604f53810531020f642b500f534b500f4231043f6105012b303f343f310f108f4221023e3407634f6375074b6061064774410601050f523e533e310e610f4121063e650b103e6167722b60177235033f6241050f51667385070b5041030e213e3235060f3116733f6371070104110621030f2021055b706b50510401000e620f400f340f6131063e5211020f3261077104677131034b105b100e346b100e310e5381077b704f4561050e6517742b206b6091060f500f6237610310210061030e323e423e4125070f633e648104 16 i; mv (mask 81) (c % 4096) (S9 (c / 4096))

def S7 (i : Nat) := let c := fld 0x493700ab31231030630416370623035d76249372631041c105d1b31d3b02441043b23235b500a500373401c663c7100ceb218d1040b10095714493218a3013b304bd30343100c537023b407a313cab610e21023106ceb3186102907749c702aa270c63304c10315221073721c66033350c7b608b1002022158b62ca103c770295270c710612221063608d66035b709d105c770490371002219c1030635068760531019136049360363709137049350b930468b0304310cb302333049db404f372913057b7625eb43c33045b3710d3017b7604b774113608bb31ca76309f304c6637a2325b27082207c76046b350273603c2061c104583704c7628d105ceb20ca10230b01203721c1067c2708d1064a370bd35027303c72105c3028460409503863706b3606810120207ab36091321d11017a230543709d740cea300e2528f370d3b6053b02537159d340c5360b93058f340791054cb5191303a6303c33509d3038b60389381d1b4127350c770317321d1103a6350863046b370ca662c77605e714845002a37253100c53509c500cb202a6340cab41ca301ceb01d1762123729c1052a252ad370043606a103c1210c7103ca104c77620a603d11058bb02173709c1009d7508d1037b104307626e2608b5006a762ce10328102ce1060e7739c70342b73043706376376270d1663c736039602bb370ca6603910348100c41004c10549340ceb40b73219d100b93210e3720910106370ca10109750aa24036304a73301735068b529db033b3020e7235e27039762d1b013e1009d703ac372cab0109e1068105603712710297b423970232102862204c301c76036b3404b2073a330ca105173729130439703b9370563427f3029b3021410063762a1773ce30135b407bb21173607a30268b02683025c1029c605a63106af323b330ceb513635044760ac22137350841054230309e317d350d110436360637600a10056380d1106c1370b9360c7104762407e370091039d10178b4228104d1660c75068d7639b3507976409f107d3049327079103c1b601937037360ce105453609910068b32ce101687409c1046c206d130139705cf303933714cb2179762095019d7600e202683037e2100030167762507048d102ac2075b302273043f2708f3504cb31cab2123b20535009b3040e3021734001360827742737039105536044f30130b3135a3037370153017966368750803701c762cb10035b60cb272a6360c534043321483038f360a63700722123a30cab31472601c10368b1204350841014cb01687034223284715483218d662c630286350681001330304340ca106c760213382883709210084100d1b214f221c7a607bb01753508a2212310502102863605e30368340 20 i; mv (mask 81) (c % 4096) (S8 (c / 4096))

def S6 (i : Nat) := let c := fld 0x554c0c8a6c3673032718a00cc0c4a606123724b9a8d00c06346089d1024c9814c8c0d10680263212a881a7cc813868073302b59b0c08c85124406d751265a1474d4110606b87516718111040a04608f93315f1b12ccc85d2208ff105633018004026c60600b12981a04a48113a20858361a3981bfc40c982010a100265892d6c86286071d3607e982484c09b4200892328798a108c0c606a0693027a181c08c0c1e6807b203229303f8c0a98628822421e98143cd4696604ae320748809d081512624e910357181c04c401a604ac350c3981ac0d4a946065a34297982e20c857a604b81031d9b121c4110e202323031b1823f8c0cd86829d753c21b0c20401fc6804c302aa1a013040c1e660fa2064688221ccc0016044a251468813748c94e404ff104271b0858d02646a02f314260829a0c82e866297361bb181805c4dfe202fb1020d181a368820a606583145d189ab4c95106a11d3409c930c04d82102092b30374882955d4602660153202c1a8a20d825c6c0012607e9819908c1d20011d30374ba903cc863a2043c364c4181b70d01e8680db3024d182b0cd010e200d930357121610d453aea22030386181ba5942842009c36046d883e8d8a986c27036164181b7cd84fa606d731485981988d0246404cd3244a903178c0e026a014102809a0370c0899604b87506f910c58d04002091331326082130406f6606f6102019901544092aec63126163981b34c101e6c4ef302489a0374c0aba6040f35038110be8885d22050f3617f880098402b06a109303 21 i; mv (mask 81) (c % 4096) (S7 (c / 4096))

def S5 (i : Nat) := let c := fld 0xcf303643037f30332330603037a3303b3034a313c23126d21074103741027b321c93134a351af302d2320ca340c9341cd3218e3039b3307410174100473036e10325302883037a302ba3033f321c935198302423215c303633037b3037d331b2302 20 i; mv (mask 81) (c % 4096) (S6 (c / 4096))

def S4 (i : Nat) := let c := fld 0x2321 14 i; mv (mask 81) (c % 4096) (S5 (c / 4096))

def S : Nat → Nat → List Nat
  | 4 => S4
  | 5 => S5
  | 6 => S6
  | 7 => S7
  | 8 => S8
  | 9 => S9
  | _ => fun _ => []

def I : Nat → List Nat → Nat
  | 5, z => let h := hk z; (h / 23 + fld 0x1d67b01e11cce00800028c2108046 5 (h % 23)) % 39
  | 6, z => let h := hk z; (h / 74 + fld 0x181f04286d0a00a0840307086a00232700155d06000c0201000d2300005f10131e00010003181a060c27120628055c002b22120116002b1d08020200060e00000901170e760909120000 8 (h % 74)) % 215
  | 7, z => let h := hk z; (h / 144 + fld 0x17ce000145281e440141c51db2d00338540402a0c007a2b008a24d70818027b0f8ae640000898008600075462b2b88c0000058081e160e95422210281ca26500830467407950000202024000d0100858031aac46418121000806010146c030000800020f8000013058cc000a0181c2a5108800140c040441c030200c000b000240a17030000203020580804010343625020700e1d000000000010100400018241c01 9 (h % 144)) % 396
  | 8, z => let h := hk z; (h / 85 + fld 0x23173870003ece3802028b254242880a23f0f1a545927c012093d2800668181030004103201810f4808100001484d0018584244c18206940860604505040058008142040000000100c686 7 (h % 85)) % 212
  | 9, z => let h := hk z; (h / 1 + fld 0x0 1 (h % 1)) % 10
  | _, _ => 0

def chk := bar 81 S N I id pool

theorem h0 : span (chk 0) 0 0 = true := rfl

theorem h1 : span (chk 1) 0 0 = true := rfl

theorem h2 : span (chk 2) 0 0 = true := rfl

theorem h3 : span (chk 3) 0 0 = true := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
theorem h4 : span (chk 4) 1 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
theorem h5 : span (chk 5) 39 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
theorem h6 : span (chk 6) 215 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
theorem h7 : span (chk 7) 396 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
theorem h8 : span (chk 8) 212 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
theorem h9 : span (chk 9) 10 0 = true := by decide +kernel

theorem allChecks : ∀ s ≤ 9, ∀ i < N s, bar 81 S N I id pool s i = true := by
  intro s hs
  interval_cases s
  · exact fun i hi => spOK h0 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h1 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h2 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h3 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h4 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h5 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h6 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h7 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h8 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h9 i (Nat.zero_le i) hi

theorem dead (i : Nat) (hi : i < 10) : ¬NatRun (mask 81) (goal 81) 9 (S9 i) :=
  bar_all (fun h => h) allChecks 9 le_rfl i hi
end Fixed40

namespace Fixed41

def raw : List Nat := [0x560aeb5815933ac206d4f000003ff80001ffc000007, 0xab5d41a82aa40d54bd4b9001ffc00000000001ffc38, 0xacc118231330e118e098d2ffe000001ff8e000e000c0, 0x310620c437470620eee304000000001fff0000ffff00, 0xc21843085b87fbc3130020000000001fffffff000000, 0xfc1f83f07c049c029c0200ffffffffe0000000000000]

def pool : List Nat := [0x108371345c16458, 0xdc0a0686c16861, 0x1082b028611746c, 0x134420685d1645c, 0xac1a0285c16059]

def N : Nat → Nat
  | 5 => 2
  | 6 => 69
  | 7 => 218
  | 8 => 180
  | 9 => 10
  | _ => 0

def S9 : Nat → List Nat
  | 0 => 0x0 :: raw
  | 1 => 0x0 :: 0x0 :: raw
  | 2 => 0x0 :: 0xffffffffffffffffffffffffffffffffffffffffffff :: raw
  | 3 => 0xffffffffffffffffffffffffffffffffffffffffffff :: raw
  | 4 => 0x0 :: 0x560aeb5815933ac206d4f000003ff80001ffc000007 :: raw
  | 5 => 0x0 :: 0xab5d41a82aa40d54bd4b9001ffc00000000001ffc38 :: raw
  | 6 => 0x0 :: 0xacc118231330e118e098d2ffe000001ff8e000e000c0 :: raw
  | 7 => 0x0 :: 0x310620c437470620eee304000000001fff0000ffff00 :: raw
  | 8 => 0x0 :: 0xc21843085b87fbc3130020000000001fffffff000000 :: raw
  | _ => 0x0 :: 0xfc1f83f07c049c029c0200ffffffffe0000000000000 :: raw

def S8 (i : Nat) := let c := fld 0x502050151063501010321023e547b70710621073e533e323e612b303f5301020f214b4061033105010511076b604107210451053e410e310e3281073f3201002b40710711020e610e533f2135063e313f6561050f204f740e4171026b70610681024b300e653f410f5305060f303f3181035f725b6005035b500f520f320f6591020f414f733f610b10000035053e6435024b106b500f610b503e620b403e523f515b703f520e5241063f540e640f512100210331023f4241040e620f31610281040f5411040b60510771030f424103310621057104110321063e6331018b103e340f503e213f62350451045102610791045f743e51050401063f635b109e432b202b60410505009103110501048b70010181050e340e517b60110605050f630b2031035b402b506b1004003f340f103e422b7035030e639b109f430f624b600e2191054b500f400b300f3491069f320e423f6403107b109e423e654b700f6431040e549f420f60 16 i; mv (mask 88) (c % 4096) (S9 (c / 4096))

def S7 (i : Nat) := let c := fld 0x37b019fb0168206b122198340493010910209f54b1301091047020624b436035013350413509935009f53a83706435009f2009f4385624582304510521b70873408c360833016f102a92302db414510309e549737041360133607e3026037006305a4b6109e5021202603605d304a83506f1049fb414137009501a410171208a410237b610630409500a41046436029360643407e212603405910609e310910509502451022130279242073506c36009e105d3705d3052d1027e20298350090006c3704b10545610a410509f5198303451049735009e51793029936021242a830455b736f105a4103af105792025910509f422d1018f306383028130609e53873500e30309f40afb018c37045614031055910309e5216303a4b0198360031042d1048e637af1022d10506306343705e2701123245000afb316f1036d32137b41133705430109f52873708c34011202023600c250402071520743230413400940519321a3240813044e2217522145616a4b5181307a41061130222105ab3018736034305993704b1065d36099340123010630709f10a836064370091018e2404336037101073602db313710298321371056f10698b732db517063409f5054221091034510609e40091004561209e4312221591044e3018c3219736098370ad3609230181305212106c30597304a9310133403b3010d3016c30411210a83214b104406348c35037b315227037106a9306a4b316e1039f10237104afb51095042db01 20 i; mv (mask 88) (c % 4096) (S8 (c / 4096))

def S6 (i : Nat) := let c := fld 0xb83033e230351033c30319251342305930313303cf2300430291303c72306c220351057a2203f3034830310230672201d331d31019a104d5b63622309a1019335087330b32305163415303a1230422208731039230873603d2201c30387321b43031cb6387350c030387340093033a2610d220483029f230a03030e313543505123058231346361e241d532173303ad2306d2208eb6321350d12313510177303261018c2304a303cb2308d102 20 i; mv (mask 88) (c % 4096) (S7 (c / 4096))

def S5 (i : Nat) := let c := fld 0x58c0aa321 18 i; mv (mask 88) (c % 4096) (S6 (c / 4096))

def S : Nat → Nat → List Nat
  | 5 => S5
  | 6 => S6
  | 7 => S7
  | 8 => S8
  | 9 => S9
  | _ => fun _ => []

def I : Nat → List Nat → Nat
  | 5, z => let h := hk z; (h / 1 + fld 0x0 1 (h % 1)) % 2
  | 6, z => let h := hk z; (h / 36 + fld 0x1271880b008164a0c040524f0531050cc0110030c00800010000c3 6 (h % 36)) % 69
  | 7, z => let h := hk z; (h / 82 + fld 0x50033781507000700070149000035c100941100030300140069881b0006002e44022e13621f02074a560115020d041c01000335160310110b011a12040b110b011b281c00050e000c110c030a0003002000 8 (h % 82)) % 218
  | 8, z => let h := hk z; (h / 68 + fld 0x2304041f19030f008e3828032501820f3d0737020f0100010402140014500009335f060a0a05030101081b000000070631021200000002000d370a25001409030437080b 8 (h % 68)) % 180
  | 9, z => let h := hk z; (h / 1 + fld 0x0 1 (h % 1)) % 10
  | _, _ => 0

def chk := bar 88 S N I id pool

theorem h0 : span (chk 0) 0 0 = true := rfl

theorem h1 : span (chk 1) 0 0 = true := rfl

theorem h2 : span (chk 2) 0 0 = true := rfl

theorem h3 : span (chk 3) 0 0 = true := rfl

theorem h4 : span (chk 4) 0 0 = true := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
theorem h5 : span (chk 5) 2 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
theorem h6 : span (chk 6) 69 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
theorem h7 : span (chk 7) 218 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
theorem h8 : span (chk 8) 180 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
theorem h9 : span (chk 9) 10 0 = true := by decide +kernel

theorem allChecks : ∀ s ≤ 9, ∀ i < N s, bar 88 S N I id pool s i = true := by
  intro s hs
  interval_cases s
  · exact fun i hi => spOK h0 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h1 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h2 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h3 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h4 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h5 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h6 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h7 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h8 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h9 i (Nat.zero_le i) hi

theorem dead (i : Nat) (hi : i < 10) : ¬NatRun (mask 88) (goal 88) 9 (S9 i) :=
  bar_all (fun h => h) allChecks 9 le_rfl i hi
end Fixed41

def projOk (k l : Nat) (r ws zs : List Nat) : Bool :=
  ((pickRows r (mask k) == mask l) && (pickRows r (goal k) == goal l)) && (ws.map (pickRows r)).isPerm zs

theorem projOk_dead {k l s : Nat} {r ws zs : List Nat}
    (ok : projOk k l r ws zs = true) (dead : ¬NatRun (mask l) (goal l) s zs) : ¬NatRun (mask k) (goal k) s ws := by
  intro h
  simp only [projOk, Bool.and_eq_true, beq_iff_eq] at ok
  have q := transport h r
  rw [ok.1.1, ok.1.2] at q
  exact dead (Run.perm (List.isPerm_iff.mp ok.2) q)

namespace Row13
def vals : List ℕ := [1,1,1,1,2,2,2,4,4,4,8,8,10,10,10,10,12,12,12,12,16,16,18,18,18,18,20,20,20,20,32,33,33,33,33,36,36,36,40,40,40,44,44,44,44,44,44,44,44,44,44,44,44,48,48,48,52,52,52,52,52,52,52,52,52,52,52,52,64,65,65,65,65,66,66,66,72,72,72,74,74,74,74,74,74,74,74,74,74,74,74,80,80,80,82,82,82,82,82,82,82,82,82,82,82,82,96,96,97,97,97,97,97,97,97,97,97,97,97,97,104,104,104,104,104,104,104,104,104,104,104,104,112,112,112,112,112,112,112,112,112,112,112,112,3,5,9,17,3,6,34,5,6,68,9,24,11,14,26,42,13,14,28,76,17,24,19,22,26,50,21,22,28,84,34,35,37,41,49,37,38,100,41,42,56,3,5,6,9,17,24,34,45,46,60,68,108,49,50,56,3,5,6,9,17,24,34,53,54,60,68,116,68,67,69,73,81,67,70,98,73,76,88,3,5,6,9,17,24,34,68,75,78,90,106,81,84,88,3,5,6,9,17,24,34,68,83,86,90,114,98,100,3,5,6,9,17,24,34,68,99,101,105,113,3,5,6,9,17,24,34,68,105,106,108,120,3,5,6,9,17,24,34,68,113,114,116,120]
def inputs : List ℕ := [0x11b11bf1b046c88d93e09b21364f8451149f000000fff000000001e0000000078000000f,0x2452451457d147a28e2145428a90cbc2f1710000000003ffc7ff8e000000000003c0f070,0x4864862868a19143245f861f0c393c8f23a20000000000000000000fff1ffe383c0f0380,0x828f2842810a27947082289751c2112ffc04000fff00000007fff000001fffc0000ffc00,0xf308308303cc3a18410bb0e461043ff44808fff0000003fff800000fffe000003ff00000,0xf40f40f40e100420080bc0f781ffc2008040fffffffffc000000000fffffffffc0000000,0xf80f80f80fe03fc07ffc0018002020080200fffffffffffffffffff00000000000000000]
def scs : List ℕ := [0x210781b0932489b,0x13c291e09925895,0x1b0290e09b24c92,0x1b05e13c9b24093,0x1b0291e09924891,0x1b04f1e09624890,0x1b0381789325491,0x1b04f1789b24c92,0x1b04f0a49524490,0x13c382109925895,0x1b0290e09b24492,0x1b0380a49b24893,0x13c291b09924095,0x1b05e0e09624c90,0x1b04f0e09325496,0x1b05e0e09524490,0x1b02913c9924091,0x1b0292109924c91,0x13c291b09124099]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)
def rho (ys : List Nat) : List Nat :=
  let a := fld 0x410491615c4c61879001472004085200024 2 (bsr 0xfec2e0a6fb828f20f957e4b6f6775b50edc75f20e7e8002fe55b79a3e248fac0df9b3e41df6c305dddc57c74dd7e3b8edaf1b502da6af460da0097e5d6c6b9f9d5c5105dd4b15d83ca77149ac7fabf8bc0994494c0922f4db8ca5e19b6c3adebaaa547aca9085f8fa2f2d5f2a2ab883a9e7733ac93cc3e9d8eb19e27872f76d9864f32ce8336ba717daa46ee7d3c8db47c7b514477b25c0b6f26116f6ec645866c998ae35d1ff5f951f0f60450c3b84d4a810e8a4a0dd619457e3ffc37bc66913786270730541d362cd540902ca29bed2a16156129bdc33d28c110b624a8a85720c1af3b205f4dd61f43052f17fff0a9171e26bd140972810e591ac00e13c6420dabd1680b1f4adc08bd97d908ab4b81083f91b402a08c45 32 (hk ys) 7 0 70)
  if a=0 || 3<a then [] else
    let c := fld 0xb9c286ae222e8ca000000 21 a
    vals.map (fun v => fld 0x1130000000d3003e60e840000000c4003aa0c78000020ab58236cd86a000000000003a400de003dc00ad7b179b05b003a000a37393dae4c00369ac996a9248a440000000c20000000b8003419e38002a564350030580290027d6226002d1602357a583e1e0000000a200278009b0029d541a5305926140027540104e031240a002552207480100000 9 (orbitLabel c v))
def B (i : Nat) := mv (mask 144) (fld 0xf65e53f43000102f10e43e21e31f53100403e30f30400e10760f50504e51e61500e65106506104405f51f21401f31e50761f61651502 12 i) inputs
def I (ys : List Nat) := bsr 0xfb828f20f957e4b6edc75f20e7e8002fe248fac0ddc57c74da0097e5c7fabf8bc0922f4db6c3adeba2f2d5f293cc3e9d7daa46ee7d3c8db47c7b514477b25c0b6f26116f5d1ff5f94a810e8a457e3ffc37bc66913786270730541d362ca29bed2a16156129bdc33d24a8a8571f43052f171e26bd140972810e591ac00e13c6420dabd1680b1f4adc08bd97d902a08c45 32 (hk ys) 6 0 36
def cls (i : Nat) := fld 0xa300b0000004812001e003c0c10184181910440c01960 5 i
def sel (c : Nat) : List Nat :=
  let t := if (c-1)/10 = 0 then 0x184d067a5936934925522905c2a564c260b012c9b49a492a91482e13eb15a2c164b1582bd2c9b49a492a914825944a7552a52c9e4da9d4c934925522904da4d449d5027d2c9e4da4d3a9c4925522904da492a914b25520934924520381c0e070381c0e070381c0d46a35148a45229148a45229148a44c261308c461f0f87c3e1f0f87c3e1f0f87c3c1a0d0682c160b0582c160b0582c160b050281008040180c06030180c06030180c060281407038100804000000000 else 0x1d2f77b26536934925520916f2b5b0e97439d329b49a492a9048b7946d76d355b0d76ab59329b49a492a9048a653ca7532b532a24da9d54934925520914da4d3c9d4e28d32a24da4d3aa04925520914da492a904ca55229349241225e2f178bc5e2f178bc5e2f16cb65b2793c9e4f2793c9e4f2793c984c261249245229148a45229148a452291488160b058341a0d068341a0d068341a0d050280c0603020100804020100804020100802814040201c0e07000000000
  (List.range 162).map (fld t 9)
def dst (i : Nat) := (cls i - 1) % 10
set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem projOK : ∀ i : Fin 36, cls i = 0 ∨ projOk 144 81 (sel (cls i)) (B i) (Fixed40.S9 (dst i)) = true := by decide +kernel
def test (i : Nat) := if cls i = 0 then checkD 144 scs 9 (B i) else true

theorem test_sound (i : Nat) (hbound : i < 36) (hi : test i = true) : ¬NatRun (mask 144) (goal 144) 9 (B i) := by
  by_cases hc : cls i = 0
  · exact checkD_sound (by simpa [test, hc] using hi)
  · exact projOk_dead ((projOK ⟨i, hbound⟩).resolve_left hc) (Fixed40.dead _ (Nat.mod_lt _ (by decide)))

set_option maxRecDepth 10000 in
lemma roof : bar 144 (cutB 9 inputs B) (cutN 9 36) (fun _ => I) (rowOrient 144 rho) scs 10 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 4 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z4 : span test 2 4 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z6 : span test 3 6 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z9 : span test 4 9 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z13 : span test 2 13 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z15 : span test 3 15 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z18 : span test 4 18 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z22 : span test 2 22 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z24 : span test 3 24 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z27 : span test 4 27 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z31 : span test 2 31 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z33 : span test 3 33 = true := by decide +kernel
lemma regionOK : span test 36 0 = true := by with_reducible exact (sj (sj (sj z0 (sj z4 z6)) (sj z9 (sj z13 z15))) (sj (sj z18 (sj z22 z24)) (sj z27 (sj z31 z33))))
theorem finChk : ¬NatRun (mask 144) (goal 144) 10 inputs :=
  symCutRoot (ori_ok rho) roof (fun i hi => test_sound i hi (spOK regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 144 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row13

namespace Row18
def vals : List ℕ := [1,1,1,1,2,2,4,4,8,8,10,10,10,12,12,12,16,16,18,18,18,20,20,20,24,24,24,26,26,26,26,26,26,26,26,26,26,26,26,28,28,28,28,28,28,28,28,28,28,28,28,32,32,33,33,33,33,33,33,33,33,33,33,33,33,33,34,34,34,34,36,36,36,36,48,48,48,50,50,50,50,50,50,50,50,50,50,50,50,52,52,52,52,52,52,52,52,52,52,52,52,64,64,65,65,65,65,65,65,65,65,65,65,65,65,65,66,66,66,66,68,68,68,68,72,72,72,74,74,74,74,74,74,74,74,74,74,74,74,76,76,76,76,76,76,76,76,76,76,76,76,3,5,9,17,3,6,5,6,9,40,11,14,42,13,14,44,17,80,19,22,82,21,22,84,25,56,88,3,5,6,9,17,27,30,40,58,80,90,96,3,5,6,9,17,29,30,40,60,80,92,96,40,96,3,5,6,9,17,35,37,40,41,49,80,96,97,35,38,42,98,37,38,44,100,49,56,112,3,5,6,9,17,40,51,54,58,80,96,114,3,5,6,9,17,40,53,54,60,80,96,116,80,96,3,5,6,9,17,40,67,69,73,80,81,96,97,67,70,82,98,69,70,84,100,73,88,104,3,5,6,9,17,40,75,78,80,90,96,106,3,5,6,9,17,40,77,78,80,92,96,108]
def inputs : List ℕ := [0x16c16c88d76c05b05b22337b00ec0ec9292af800000000fff8000000003ffe000000000000f,0x216b141781140859c505e02501155942e2e588007ff80f0000001ffe03c0000007ff81c1c30,0x2b182187902189c60861e404615981187474717ff8000f00001ffe0003c00007ff8000e0e0c0,0x2ba2ba38004a012812848818857a17a3807f827ffffff0000000000000000007ffffff00ff00,0xc40c41221841bd0bd0e006101dc1dc3ff80040000000000001ffffffc000007ffffffff0000,0x3083082446082de0de0fffbe0e6026010049000000000000001ffffffffffff8000000000000,0x3f03f03ffff03e00e00911c00b8038024900007fffffffffffe0000000000000000000000000]
def scs : List ℕ := [0x1fc4d06ca8280bd,0x134351649c26097,0x22c671fc9927098,0x19c590d4bd268a8,0x22c7f19c9825c9c,0xd41b134a026899,0xd41b22ca82609a,0xd41b1fca82649a,0xd41b134a025c99,0x1342719cbd264a0,0xd4271349c25c98]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def rho (ys : List Nat) : List Nat :=
  let a := fld 0x18822492803840868420032830708899 2 (bsr 0xf9795bfaf7ca5b71f5bf7ce0f163380ced9c28c1e94ccfbde058865fdaf380a7d840bc00d79982c3ce89ad8ece82c438c6ce523bc0fd0ac4bd0fed01bcfab1a9b69b83adb23ed016b0fb3666b0c1e62daba738b6aaca9698a9ebec5fa9dd629ca52443c2a48ba7fa9fdf667098e2a61e8d02265289ba790489afb26b8568c2c484c9e6908295090c81d5c9697a18dad2737193a4695708f968cc8bed60e0a5a660ab18a1608a3ff95f41c7865eb654ca5a25f2da5910af6d54d59f9047ca584e451e2fcb421dd2bf40e1f9033e3a2c25384bcb65321a3b972dbc0bf7272886371db835851c6fbd121be8f6051aa9a0ae18a9b674148b0d770b63a955055a7878 32 (hk ys) 7 0 64)
  if a=0 || 3<a then [] else
    let c := fld 0xb9c285ce22358ca000000 21 a
    vals.map (fun v => fld 0xfb003bc00e300000012d0048401150000000e000371b0bd0000000c8002f000b10000000ae002ae10a800476508b8e1fe0c7c004320a78821d0ce650000000c6002e800b0003adec5975135aa4a0000000a60028da8a000369a446689086a33002e186275b86d5e18002a9581554849341000289480d5082932080027130064b8100000 9 (orbitLabel c v))
def B (i : Nat) := mv (mask 151) (fld 0xf10f40106f21506102f50e64404f41e40502f53e65e51401e54500f51100e41e21503103405e50f54e34e10400f34000f65 12 i) inputs
def I (ys : List Nat) := bsr 0xf9795bfaf163380ce94ccfbde058865fd840bc00ce82c438bd0fed01b23ed016b0fb3666b0c1e62daba738b6a9dd629ca48ba7fa9fdf667098e2a61e89ba79048295090c7a18dad2737193a468cc8bed60e0a5a660ab18a1608a3ff95f41c7865a25f2da47ca584e451e2fcb40e1f9033e3a2c252dbc0bf7272886371c6fbd121aa9a0ae 32 (hk ys) 6 0 33
def test (i : Nat) := checkD 151 scs 9 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 151 (cutB 9 inputs B) (cutN 9 33) (fun _ => I) (rowOrient 151 rho) scs 10 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 4 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z4 : span test 4 4 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z8 : span test 4 8 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z12 : span test 4 12 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z16 : span test 4 16 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z20 : span test 4 20 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z24 : span test 4 24 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z28 : span test 2 28 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z30 : span test 3 30 = true := by decide +kernel
lemma regionOK : span test 33 0 = true := by with_reducible exact (sj (sj (sj z0 z4) (sj z8 z12)) (sj (sj z16 z20) (sj z24 (sj z28 z30))))
theorem finChk : ¬NatRun (mask 151) (goal 151) 10 inputs :=
  symCutRoot (ori_ok rho) roof (fun i hi => checkD_sound (spOK regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 151 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row18

namespace Row19
def vals : List ℕ := [1,1,1,2,2,2,4,4,4,8,8,10,10,10,10,12,12,12,12,16,16,17,17,17,17,20,20,20,20,24,24,24,28,28,28,28,28,28,28,28,28,28,28,28,32,33,33,33,34,34,34,40,40,40,42,42,42,42,42,42,42,42,42,42,42,42,48,48,48,49,49,49,49,49,49,49,49,49,49,49,49,56,56,56,56,56,56,56,56,56,56,56,56,64,64,65,65,65,65,66,66,66,66,68,68,68,68,68,68,68,68,68,68,68,68,68,96,96,96,97,97,97,97,97,97,97,97,97,97,97,97,98,98,98,98,98,98,98,98,98,98,98,98,3,5,9,3,6,18,5,6,36,9,72,11,14,26,74,13,14,44,76,18,80,19,21,25,81,21,22,52,84,25,26,88,3,5,6,9,18,29,30,36,60,72,80,92,36,35,37,41,35,38,50,41,44,104,3,5,6,9,18,36,43,46,58,72,80,106,50,52,112,3,5,6,9,18,36,51,53,57,72,80,113,3,5,6,9,18,36,57,58,60,72,80,120,72,80,67,69,73,81,67,70,74,82,3,5,6,9,18,36,69,70,72,76,80,84,100,100,104,112,3,5,6,9,18,36,72,80,99,101,105,113,3,5,6,9,18,36,72,80,99,102,106,114]
def inputs : List ℕ := [0x42fc2c012c7c04b9cb00964f01591f045278007ff8000078001ffe00000e00001e00007,0x3c544540257c409505533aa3902aa214bc5cfff80000007800000003ffc7000000007838,0x898898eb98881260a6414c92cf30f23c8e90000000fff800000000000000fff1e0781c0,0x11211210c2111bc83081791c45b47043ff020000000000001ffe0003fff80fffe007fe00,0x2242242304222dd0dd0ea20206b87ffc10100000000000001ffffffc00000ffffff80000,0x3c83c83c080009e09e0f3c1ff8c0040100807ffffff000001ffffffffffff00000000000,0x3f03f03ff03ffe00e009c0100700488a22007fffffffffffe00000000000000000000000]
def scs : List ℕ := [0x114201449724490,0x20c451dca323c94,0x19c51114a324499,0x1dc6720c9723c90,0xd8201449725093,0x1142019c9924091,0x19c200d899250a3,0x1142020c9323c90,0x20c770809124c8f,0x19c4520c9323c90,0x20c45144942448f,0xd8201dc9023c93,0x1dc5120c9923c91]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)
def rho (ys : List Nat) : List Nat :=
  match fld 0x1858e48be88228500 1 (bsr 0xfdbf7bcafd7239e7f853cf8ff3a47eecf2c4f171edab805febd25c57e58a7b05e35ef914e00aade0ddc13479d7cb6f94d53813b8c9252652c2cc5fa4be370bdcbdb2c8f6b93c43e1b7eabc0db6563989b15059b2a9b60f5da23bcf419ac580ca93dd0d12904f2e208adf4a6384253f6e800f32447d71db547cc8d5d77bf9a0a5773ee0a57043f3476cf6ceca6c82649a6b3bcedc698c41da60635b1960205ccd5950015f589d670856a171b94dee9f4b4ddc56254c70b91b4671850b464185543ff014f93a510d9537f90bb23700a0a2330c54be3019fac72b5f3ac726b4de2c2131f5dd1bec420c174d6aa716b4fe39157bf054115fec560c01d95d0342b8480316ee6001b5a6cf00d1b3c6 32 (hk ys) 7 0 67) with
  | 1 => vals.map (fun r => fld 0xeb00000000000441a0c40000000000037e3ad30043e3702871dd06740000000ba0000000ae0000000a1003c13a990000000ab0029deaa3003bde6677717cc65d0000000b7003719a510000198a065af86c330036c00aa6d1158242002f580975e0b4602c002d16a2000299381d00279360f4d2441609002955219520552813002412606478000600 9 r)
  | _ => []
def B (i : Nat) := mv (mask 143) (fld 0x406f40e30104505106e43e40e60f20506f43e10403101f30f52e65e20e50e32f53e62f62f10502750504102f65f50402400000501f32652405e63f60e53f63105e52 12 i) inputs
def I (ys : List Nat) := bsr 0xfdbf7bcafd7239e7f2c4f171edab805febd25c57e58a7b05e00aade0d53813b8c9252652c2cc5fa4b7eabc0db6563989a9b60f5da23bcf4193dd0d12904f2e208adf4a63800f32446cf6ceca6b3bcedc698c41da60635b195950015f589d670856a171b94dee9f4b4ddc56254671850b464185543ff014f937f90bb2330c54be3019fac72b5f3ac726b4de2c1bec420c16b4fe39157bf054115fec560c01d95d0342b8480316ee6001b5a6cf00d1b3c6 32 (hk ys) 6 0 44
def cls (i : Nat) := fld 0xa0003000000008007202080000000a57510012002042 4 i
def sel (c : Nat) : List Nat :=
  let t := 0x55a8d429979bbd289149a411ef551a7532f37725122934823d4ea378265deee4a245269047a8d32ba51a656ab44a245269047ab938a655aa54aa751a654ca55225122934823d469450a6d3ca34ea6538944da6922934823d329149a41289347a45208f3399cce673399cce673399cce633198cc6633198cc6633198cbe5f2f97cbe5f2f97cbe5f2f974ba20100804020100804020100743a1d0c86432150a8542a150a8542a150a85426130783c1e0b0582c160b0582c160b0582c1209030180603018000000
  (List.range 176).map (fld t 9)
def dst (i : Nat) := (cls i - 1) % 10
set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem projOK : ∀ i : Fin 44, cls i = 0 ∨ projOk 143 88 (sel (cls i)) (B i) (Fixed41.S9 (dst i)) = true := by decide +kernel
def test (i : Nat) := if cls i = 0 then checkD 143 scs 9 (B i) else true

theorem test_sound (i : Nat) (hbound : i < 44) (hi : test i = true) : ¬NatRun (mask 143) (goal 143) 9 (B i) := by
  by_cases hc : cls i = 0
  · exact checkD_sound (by simpa [test, hc] using hi)
  · exact projOk_dead ((projOK ⟨i, hbound⟩).resolve_left hc) (Fixed41.dead _ (Nat.mod_lt _ (by decide)))

set_option maxRecDepth 10000 in
lemma roof : bar 143 (cutB 9 inputs B) (cutN 9 44) (fun _ => I) (rowOrient 143 rho) scs 10 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 2 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z2 : span test 3 2 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z5 : span test 3 5 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z8 : span test 3 8 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z11 : span test 2 11 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z13 : span test 3 13 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z16 : span test 3 16 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z19 : span test 3 19 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z22 : span test 2 22 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z24 : span test 3 24 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z27 : span test 3 27 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z30 : span test 3 30 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z33 : span test 2 33 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z35 : span test 3 35 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z38 : span test 3 38 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z41 : span test 3 41 = true := by decide +kernel
lemma regionOK : span test 44 0 = true := by with_reducible exact (sj (sj (sj (sj z0 z2) (sj z5 z8)) (sj (sj z11 z13) (sj z16 z19))) (sj (sj (sj z22 z24) (sj z27 z30)) (sj (sj z33 z35) (sj z38 z41))))
theorem finChk : ¬NatRun (mask 143) (goal 143) 10 inputs :=
  symCutRoot (ori_ok rho) roof (fun i hi => test_sound i hi (spOK regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 143 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row19

namespace Row20
def vals : List ℕ := [1,1,1,2,2,2,4,4,8,8,8,10,10,10,10,10,10,10,10,10,10,10,10,10,12,12,12,12,16,16,17,17,17,17,20,20,20,24,24,24,24,28,28,28,28,28,28,28,28,28,28,28,28,32,32,33,33,33,33,34,34,34,34,36,36,36,36,64,65,65,65,66,66,66,66,68,68,68,80,80,80,81,81,81,81,81,81,81,81,81,81,81,81,84,84,84,84,84,84,84,84,84,84,84,84,96,96,97,97,97,97,97,97,97,97,97,97,97,97,98,98,98,98,98,98,98,98,98,98,98,98,100,100,100,100,100,100,100,100,100,100,100,100,3,5,9,3,6,18,5,6,9,40,72,3,5,6,9,11,14,18,26,40,42,48,72,74,13,14,44,76,18,48,19,21,25,49,21,22,52,25,26,56,88,3,5,6,9,18,29,30,40,48,60,72,92,40,48,35,37,41,49,35,38,42,50,37,38,44,52,72,67,69,73,67,70,74,82,69,70,76,82,88,112,3,5,6,9,18,40,48,72,83,85,89,113,3,5,6,9,18,40,48,72,85,86,92,116,104,112,3,5,6,9,18,40,48,72,99,101,105,113,3,5,6,9,18,40,48,72,99,102,106,114,3,5,6,9,18,40,48,72,101,102,108,116]
def inputs : List ℕ := [0x42c42fc2c10bf0b047847c02b13e0806ca78000007ff8001ffe007007800003c0000007,0x857c544542151152bc8bc405524294bd45c8007ff800000000007807800000000fff838,0x3c18818818f062061c93c88a660e478098697ff8000001ffe0003807801ffe1c0f0000c0,0x12a12a12a14a84a85125111ee8f087eee38200000000000000000000001fffe00fffff00,0x2142142142f50f50e202222b70fff81300100000000001ffffffc000001ffffff0000000,0x3d83d83d838608608003fff38049121c01007ffffffffe0000000007ffe0000000000000,0x3e03e03e03f80f80fffc000c0080046002007ffffffffffffffffff80000000000000000]
def scs : List ℕ := [0x20c771ac9023c93,0x20c291749929098,0x1dc5102c98250a4,0x1ac0b1dc9923c91,0x1442902c9323c90,0x1ac2920c9824091,0x1dc51174942408f,0x1442902c9124c90,0xa40b20ca424c94,0x1440b0a4942448f,0x1ac0b144a424498,0x1dc6b20c9924c8f,0x144291749925091,0x1440b0a49124c8f,0x1ac0b1749924091,0x1dc5d1aca423c94]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)
def rho (ys : List Nat) : List Nat :=
  match fld 0x0 1 (bsr 0xfbbb207cf846ca6cf61c44aef1b63f6af06788f3f031bf29ea55c7ace5f9f36fe3a88167de74b108dd3a27eddaffd105ca576bb2c7982f8ac6d913dec5966451bcfa0acbbab7b327b8baf593b418853ab15943afb131d659afe29894ab31c543a11482539fd1d2c69f49cf7d97512cf58f527ac58e3190de8d86beca8d5482e48ca23b4f8b6d44ce89a6f67187ca36b980bc0f9a78c2eb90788cce96776f78a472a0de69722a42c06ac9398c65216b4b61e17a56612940e660131ae153f09545530585d250c39e5b470a563941568e913dd4164a3b6dbc71359a118e2aff0cd01f724bbd1d0730f518edb4be17f81bf2170a89d51628de5813a908c611d1e6300c8d7ce50bbe84ff033eea7e 32 (hk ys) 7 0 67) with
  | _ => []
def B (i : Nat) := mv (mask 143) (fld 0xf43404f53e21e40102401106e30f50105e31f24402e63406100403101104e62f60e60e61663000505e52500f54503f61f63760e51e24e50e10e41f64103400f51e20405f31f62f52e65f65f20e53e64f41e43765f40f23e23502f10f21f30e54504506501 12 i) inputs
def I (ys : List Nat) := bsr 0xfbbb207cf846ca6cf61c44aef1b63f6af06788f3f031bf29ea55c7ace5f9f36fe3a88167de74b108dd3a27eddaffd105ca576bb2c7982f8ac6d913dec5966451bcfa0acbbab7b327b8baf593b418853ab15943afb131d659afe29894ab31c543a11482539fd1d2c69f49cf7d97512cf58f527ac58e3190de8d86beca8d5482e48ca23b4f8b6d44ce89a6f67187ca36b980bc0f9a78c2eb90788cce96776f78a472a0de69722a42c06ac9398c65216b4b61e17a56612940e660131ae153f09545530585d250c39e5b470a563941568e913dd4164a3b6dbc71359a118e2aff0cd01f724bbd1d0730f518edb4be17f81bf2170a89d51628de5813a908c611d1e6300c8d7ce50bbe84ff033eea7e 32 (hk ys) 7 0 67
def cls (i : Nat) := fld 0x9000064000007220800252c11000006800000090500a0702a00200000000000030 4 i
def sel (c : Nat) : List Nat :=
  let t := if (c-1)/10 = 0 then 0x59a91529865b1d289149a411ecd5228d30cb6325122934823d60a4642618ec64a245269047a9130c1522617cbd4a245269047ad942af59ac95cb0522615eae56a5122934823d489454a7d4ea451a6142944fa7922934823d309149a41289347a45208f1f8fc7e3f1f8fc7e3f1f8fc7e3b1d8ec763b1d8ec763b1d8ec6e371b8dc6e371b8dc6e371b8d46a29148a45229148a45229148944a2511088441e0f0783c1e0f0783c1e0f078381c0c060300b0582c160b0582c160b0582c1008030180603018000000 else 0x54a6166a463b2d22944824d1ec84c2c148c763245289049a3d469866a9196c648a51209347a6148c14c2917abe48a51209347ad95ea154a9d3ea34c291429f4f245289049a3d309159ab96498582915e91572b5289049a3d48944824d229047a51268f1f8fc7e3f1f8fc7e3f1f8fc7e371b8dc6e371b8dc6e371b8dc763b1d8ec763b1d8ec763b1d8d46a29148a45229148a45229148944a250c060300b0582c160b0582c160b0582c100811088441e0f0783c1e0f0783c1e0f078381c0301800000000c0603
  (List.range 176).map (fld t 9)
def dst (i : Nat) := (cls i - 1) % 10
set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem projOK : ∀ i : Fin 67, cls i = 0 ∨ projOk 143 88 (sel (cls i)) (B i) (Fixed41.S9 (dst i)) = true := by decide +kernel
def test (i : Nat) := if cls i = 0 then checkD 143 scs 9 (B i) else true

theorem test_sound (i : Nat) (hbound : i < 67) (hi : test i = true) : ¬NatRun (mask 143) (goal 143) 9 (B i) := by
  by_cases hc : cls i = 0
  · exact checkD_sound (by simpa [test, hc] using hi)
  · exact projOk_dead ((projOK ⟨i, hbound⟩).resolve_left hc) (Fixed41.dead _ (Nat.mod_lt _ (by decide)))

set_option maxRecDepth 10000 in
lemma roof : bar 143 (cutB 9 inputs B) (cutN 9 67) (fun _ => I) (rowOrient 143 rho) scs 10 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 4 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z4 : span test 4 4 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z8 : span test 4 8 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z12 : span test 4 12 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z16 : span test 4 16 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z20 : span test 4 20 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z24 : span test 4 24 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z28 : span test 2 28 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z30 : span test 3 30 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z33 : span test 4 33 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z37 : span test 4 37 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z41 : span test 4 41 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z45 : span test 2 45 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z47 : span test 3 47 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z50 : span test 4 50 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z54 : span test 4 54 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z58 : span test 4 58 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z62 : span test 2 62 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z64 : span test 3 64 = true := by decide +kernel
lemma regionOK : span test 67 0 = true := by with_reducible exact (sj (sj (sj (sj z0 z4) (sj z8 z12)) (sj (sj z16 z20) (sj z24 (sj z28 z30)))) (sj (sj (sj z33 z37) (sj z41 (sj z45 z47))) (sj (sj z50 z54) (sj z58 (sj z62 z64)))))
theorem finChk : ¬NatRun (mask 143) (goal 143) 10 inputs :=
  symCutRoot (ori_ok rho) roof (fun i hi => test_sound i hi (spOK regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 143 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row20

namespace Row23
def vals : List ℕ := [1,1,1,2,2,2,4,4,8,8,10,10,10,10,12,12,12,16,16,17,17,17,17,20,20,20,24,24,24,24,28,28,28,28,28,28,28,28,28,28,28,28,32,32,33,33,33,33,34,34,34,34,34,34,34,34,34,34,34,34,34,36,36,36,36,48,48,48,49,49,49,49,49,49,49,49,49,49,49,49,52,52,52,52,52,52,52,52,52,52,52,52,64,64,65,65,65,65,65,65,65,65,65,65,65,65,65,66,66,66,66,68,68,68,68,72,72,72,74,74,74,74,74,74,74,74,74,74,74,74,76,76,76,76,76,76,76,76,76,76,76,76,3,5,9,3,6,18,5,6,9,40,11,14,26,42,13,14,44,18,80,19,21,25,81,21,22,84,25,26,56,88,3,5,6,9,18,29,30,40,60,80,92,96,40,96,35,37,41,97,3,5,6,9,18,35,38,40,42,50,80,96,98,37,38,44,100,50,56,112,3,5,6,9,18,40,51,53,57,80,96,113,3,5,6,9,18,40,53,54,60,80,96,116,80,96,3,5,6,9,18,40,67,69,73,80,81,96,97,67,70,82,98,69,70,84,100,73,88,104,3,5,6,9,18,40,75,78,80,90,96,106,3,5,6,9,18,40,77,78,80,92,96,108]
def inputs : List ℕ := [0x4b04b2235cb012e72c080afc02b13e1153c000000007ffc000fff00000f00000780007,0x95ad505e055025415494dd44055242af2e4003ffc07800000000001fff000000003c38,0xac60861e408627182187811885660e47234bffc000780000fff0001e00003ffc381c0c0,0xae8ae8e0012804a04a12062115e8f087fc13ffffff8000000000000000003fffc01ff00,0x3103104886106f42f43818400770fff84080000000000000ffffffe000003fffffe0000,0xc20c20911820b783783fef83f98040048800000000000000ffffffffffffc0000000000,0xfc0fc0ffffc0f803802470022e0089100003ffffffffffff00000000000000000000000]
def scs : List ℕ := [0x1101e1409723c90,0x1d81e208a024893,0x1d844178b724097,0x140440c0922388f,0x1d85e2089223c8e,0x17830078a025cb7,0x11030078932408e,0x1d8501788f23892,0x1d850178a023893]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def rho (ys : List Nat) : List Nat :=
  match fld 0xc07d61251b0941ae 1 (bsr 0xfad57cb8f9047f6df75acffbed7be9d0ebdd4332e951c2f7e84a982be66bcd2cda83b6a2d9681db1d39d99dccd0b5820cd09d6d8ca5d2c92c3b0b69ec223ee35bf567c23bd81d0b9bb13f5dcb6d82285adc7586cada8c338ac8cb5c4ac7e0d38a2be6553a0b125729d83592a98f245569756d55b95268ac49377e3d79164dcb68d3232e286f93574830329a581d920eb7a1f058178c8f10a7482b68d6968e6a668f7a89367b8c7d6675a0ee560fd95995accbdfd5a3906515885c981534d0c244f485e064ebbd8de4ce777da486b43f04010b6873d5df0733d31516f3699612b2f5a17b02cee13cf22802718116347de1041c9290b589ae80b0d049403c2b6a1 32 (hk ys) 7 0 64) with
  | 1 => vals.map (fun r => fld 0x11b000021f030000000e90037400d10000000ce002f594b70000000b40036800aa00000009e002f1369700365ca506c1118e41002ed883d5d0b0602a0000000b6000021aab0045a1682853d0ec730000000a700291f6a0003cdf46f79178d65c002c5641e0028d341a00271320e4c2401408002894c175084d26110023d2406470000600 9 r)
  | _ => []
def B (i : Nat) := mv (mask 142) (fld 0xe64e51e52f34e54e40e20404f65f40f20402503e50e65506f41102f52f53106e34e41f10f32101501103f50405f54f51000e10e24400502 12 i) inputs
def I (ys : List Nat) := bsr 0xf75acffbed7be9d0ebdd4332e951c2f7e84a982be66bcd2cda83b6a2c3b0b69ebf567c23b6d82285adc7586cada8c338ac8cb5c4a2be6553a0b1257298f245569756d55b9377e3d78d3232e286f93574830329a578c8f10a68f7a89367b8c7d6675a0ee560fd95995a3906515885c9814f485e064ce777da486b43f04010b6873d5df0733d31516f2cee13cf116347de03c2b6a1 32 (hk ys) 6 0 37
def test (i : Nat) := checkD 142 scs 9 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 142 (cutB 9 inputs B) (cutN 9 37) (fun _ => I) (rowOrient 142 rho) scs 10 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 4 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z4 : span test 2 4 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z6 : span test 3 6 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z9 : span test 4 9 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z13 : span test 2 13 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z15 : span test 3 15 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z18 : span test 4 18 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z22 : span test 2 22 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z24 : span test 3 24 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z27 : span test 2 27 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z29 : span test 3 29 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z32 : span test 2 32 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z34 : span test 3 34 = true := by decide +kernel
lemma regionOK : span test 37 0 = true := by with_reducible exact (sj (sj (sj z0 (sj z4 z6)) (sj z9 (sj z13 z15))) (sj (sj z18 (sj z22 z24)) (sj (sj z27 z29) (sj z32 z34))))
theorem finChk : ¬NatRun (mask 142) (goal 142) 10 inputs :=
  symCutRoot (ori_ok rho) roof (fun i hi => checkD_sound (spOK regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 142 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row23

namespace Row24
def vals : List ℕ := [1,1,1,2,2,4,4,8,8,10,10,10,12,12,12,16,16,16,17,17,17,17,17,17,17,17,17,17,17,17,17,18,18,18,18,18,18,18,18,18,18,18,18,18,20,20,20,20,20,20,20,20,20,20,20,20,20,32,32,33,33,33,33,33,33,33,33,33,33,33,33,33,34,34,34,34,36,36,36,36,40,40,40,42,42,42,42,42,42,42,42,42,42,42,42,44,44,44,44,44,44,44,44,44,44,44,44,64,64,65,65,65,65,65,65,65,65,65,65,65,65,65,66,66,66,66,68,68,68,68,72,72,72,74,74,74,74,74,74,74,74,74,74,74,74,76,76,76,76,76,76,76,76,76,76,76,76,3,5,9,3,6,5,6,9,24,11,14,26,13,14,28,24,48,80,3,5,6,9,19,21,24,25,48,49,80,81,96,3,5,6,9,19,22,24,26,48,50,80,82,96,3,5,6,9,21,22,24,28,48,52,80,84,96,48,96,3,5,6,9,24,35,37,41,48,49,80,96,97,35,38,50,98,37,38,52,100,41,56,104,3,5,6,9,24,43,46,48,58,80,96,106,3,5,6,9,24,45,46,48,60,80,96,108,80,96,3,5,6,9,24,48,67,69,73,80,81,96,97,67,70,82,98,69,70,84,100,73,88,104,3,5,6,9,24,48,75,78,80,90,96,106,3,5,6,9,24,48,77,78,80,92,96,108]
def inputs : List ℕ := [0x12c12c88d72c02b02b2232eb003601b55d8255e000000003ffe000000000fff80000007ffc0007,0x216b1417811404596505e025004aab500a85cb2001ffe03c0000007ff80f0000000fff80000e18,0x2b182187902189660461e4046156c0260130e8e5ffe0003c00007ff8000f00001fff00000007060,0x2b62b63800460978978e0009801900c80641ff09ffffffc000007ffffff00000000000000007f80,0xcc0cc12218c13903904887105fe0ff07f8792000000000000000000000000001ffffffffff8000,0x3083082446082de0de0fffbe0e601300980200000000000000007fffffffffffe00000000000000,0x3f03f03ffff03e00e00911c00b801c00e0040001ffffffffffff800000000000000000000000000]
def scs : List ℕ := [0x2141f14cbb2b4ae,0xb01f0489e274a1,0x244120b0a52789f,0x2146d2449f2849d,0xec121b4bb2b8ad,0x2143b07cae2b4bb,0x14c1207ca52749f,0xb01214c9f2849e]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def rho (ys : List Nat) : List Nat :=
  let a := fld 0xe465b8084d80806c001965881811001861a653052400291 3 (bsr 0xfd73216afd2ae6a0f4b4ebf0eebc10b5ee8dd76ee615bbb3e2771267dcc8cd84db1f5491d9204e97d82f7fc1d3bc4e42d26d8defcf757ea1c77a1116c3428d89bce7a9e1ba26b6e3b8ed470bb1f21bebb0f1248fa9f68c8ea820a7a09e1133ea9d7fb3f59821dd2d94b96e8c92b118818f112e658a3c63418944838f7e976dac7e6e118f7d3edc677c2f6c1276c035e76b7510e56625fa5465e342a66579cdbd600390ec5b81fc0d5b728fb5522d3c26518f9a784cc737e84a3af73d41b01e383b19fbcd39e2c65133c0b0563136606d2d6bcfc22d5bc1062870c4e623ac96e32281415921d63bcd20a119321663282a1523e67c14e5b5370c33c12b07c33d73 32 (hk ys) 7 0 64)
  if a=0 || 4<a then [] else
    let c := fld 0x174650283d6221dd358ca000000 21 a
    vals.map (fun v => fld 0x107003ec00ef0000000ec003a1c8bb000000137004ac01200000000d40031d74ae004a6689194216248200462227e881e8da6b000000104003e000ee0000000d20031570ad003da025f7a94dbe5000399bc4c6e92076390000000ab002a16ca500305682c5987c240f0029d520c530253e07002853c054e80c0000 9 (orbitLabel c v))
def B (i : Nat) := mv (mask 157) (fld 0xe40f51000106f30e51400503f31e50e31506f21e21e30403f40504f41104401f10e10103 12 i) inputs
def I (ys : List Nat) := bsr 0xfd73216ad9204e97d3bc4e42c3428d89bce7a9e1b8ed470bb1f21beba820a7a09e1133ea9d7fb3f59821dd2d7e976dac7d3edc6776c035e76b7510e56579cdbd600390ec5b81fc0d522d3c264cc737e82d6bcfc221d63bcd20a119321663282a 32 (hk ys) 5 0 24
def test (i : Nat) := checkD 157 scs 9 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 157 (cutB 9 inputs B) (cutN 9 24) (fun _ => I) (rowOrient 157 rho) scs 10 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 3 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z3 : span test 3 3 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z6 : span test 3 6 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z9 : span test 3 9 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z12 : span test 3 12 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z15 : span test 3 15 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z18 : span test 3 18 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z21 : span test 3 21 = true := by decide +kernel
lemma regionOK : span test 24 0 = true := by with_reducible exact (sj (sj (sj z0 z3) (sj z6 z9)) (sj (sj z12 z15) (sj z18 z21)))
theorem finChk : ¬NatRun (mask 157) (goal 157) 10 inputs :=
  symCutRoot (ori_ok rho) roof (fun i hi => checkD_sound (spOK regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 157 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row24

namespace Row25
def vals : List ℕ := [1,1,1,2,2,4,4,6,6,6,8,8,10,10,10,12,12,12,14,14,14,14,14,14,14,14,14,14,14,14,16,16,16,17,17,17,17,17,17,17,17,17,17,17,17,17,20,20,20,20,24,24,24,24,28,28,28,28,28,28,28,28,28,28,28,28,32,32,33,33,33,33,34,34,34,40,40,40,40,42,42,42,42,42,42,42,42,42,42,42,42,64,64,65,65,65,65,66,66,66,68,68,68,68,70,70,70,70,70,70,70,70,70,70,70,70,96,96,96,97,97,97,97,97,97,97,97,97,97,97,97,98,98,98,98,98,98,98,98,98,98,98,98,3,5,9,3,18,5,36,7,22,38,9,72,11,26,74,13,44,76,3,5,9,15,18,30,36,46,48,72,78,80,18,48,80,3,5,9,18,19,21,25,36,48,49,72,80,81,21,22,52,84,25,26,56,88,3,5,9,18,29,30,36,48,60,72,80,92,36,48,35,37,41,49,35,38,50,41,44,56,104,3,5,9,18,36,43,46,48,58,72,80,106,72,80,67,69,73,81,67,74,82,69,76,84,100,3,5,9,18,36,48,71,72,78,80,86,102,100,104,112,3,5,9,18,36,48,72,80,99,101,105,113,3,5,9,18,36,48,72,80,99,102,106,114]
def inputs : List ℕ := [0x41fc1c02389f009c4f802e23277001e4a578007ff800001e00000f000003ffe00000007,0x3c244246a487125a438805244019297239ccfff8000fff0e07ff8700000000003ffc7398,0x848848ea978201489132e41e0a209d5c1f10000000ffff000000003ffc3c0003fff83e0,0x11111110c21246d93c21669e04440d59fe0200000000000007fff803fffc00003ffffc00,0x22a22a23142489621245b71ffb78f260108800000000000000000003ffffffffc0000000,0x3cc3cc3c1840027c3ffe38088380438081207ffffff0000007fffffc0000000000000000,0x3f03f03fe07fff802001c0111c009c0124007ffffffffffff80000000000000000000000]
def scs : List ℕ := [0x13c360489524ca9,0x1dc4f20c9a23c91,0x1dc36084a924095,0x1a0210489a24cac,0x1a0211dcac23c93,0x1dc36084ac2449a,0x841213c9523c90,0x84120d8932408f,0x13c211a0ac254a9,0x84121a09a24091,0x1a0360489a24cac,0x1a02120c9524c90,0x1dc680d8932448f]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)
def rho (ys : List Nat) : List Nat :=
  let a := fld 0x4ca5c03880c243322ed706239220fea4 2 (bsr 0xffc6f9c4ff41e8e2fbd0a54cf606c261f4a30a53f2969921e92c093ee7041e37e63d7411dd2668d5c6cca5b0c5f20b3dc424d732c0987827bea7d536bb5677f8bada98a2b9008580b21ff34eaa85e630a31945aa9f9ee1e99c41684c9ad428319876483e95deaa86951f47a69483de0593dbbcc29172253d8dac909b8a1809cf89cba2718924bbb385d02f51856e310484ff0c0179f3338c79431fc0766724c1743f5c48724dcc286b654a0c68d3a29c65efabe465ccde23622f2961561473d54fd401c84c7e3d33494994ac4328b7fa424e10483052afba2624c49e25a41b5a1f1ec26f180438f81538f044106645730dc8155e0ba567900812b114000423c2 32 (hk ys) 7 0 64)
  if a=0 || 3<a then [] else
    let c := fld 0xba2643435313171800000 21 a
    vals.map (fun v => fld 0x4762305000000000003a620dd0040a1ef68720cee740000000d00000000c40040400c0003c978ac002ac00a000275dc9a7e9a1da6476184ba5b0000000cd0039800c30000000bf0036572a9002a0009f7193daa4b00261a895699208842002999236002716c320025d6a2e5a24c421e520493c0f4d831220a4b01d20054780c0000 9 (orbitLabel c v))
def B (i : Nat) := mv (mask 143) (fld 0x504000e40e20e10e52f10f53104f20506400106e32101f32e62f40e43402401f12e12f42f52501 12 i) inputs
def I (ys : List Nat) := bsr 0xff41e8e2f606c261dd2668d5c6cca5b0c5f20b3dc424d732bb5677f8b9008580b21ff34eaa85e6309f9ee1e99c41684c95deaa86951f47a693dbbcc28dac909b89cba271743f5c48724dcc2865efabe4622f2961494994ac424e10482624c49e25a41b5a000423c2 32 (hk ys) 5 0 26
def test (i : Nat) := checkD 143 scs 9 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 143 (cutB 9 inputs B) (cutN 9 26) (fun _ => I) (rowOrient 143 rho) scs 10 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 3 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z3 : span test 3 3 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z6 : span test 3 6 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z9 : span test 4 9 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z13 : span test 3 13 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z16 : span test 3 16 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z19 : span test 3 19 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z22 : span test 4 22 = true := by decide +kernel
lemma regionOK : span test 26 0 = true := by with_reducible exact (sj (sj (sj z0 z3) (sj z6 z9)) (sj (sj z13 z16) (sj z19 z22)))
theorem finChk : ¬NatRun (mask 143) (goal 143) 10 inputs :=
  symCutRoot (ori_ok rho) roof (fun i hi => checkD_sound (spOK regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 143 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row25

def prefixGates (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x100f50100f40100f31100f20100f10100e62100e61100e54100e52100e50100e40100e31100e30100e21100e20100501100500100401100103100102100101100100006f54006f53006f52006f51006f50006f43006f42006f41006f40006f32006f31006f30006f21006f20006f10006e54006e53006e52006e51006e50006e43006e42006e41006e40006e32006e31006e30006e21006e20006e10006505006504006503006502006501006500006405006404006403006402006401006400006105006104006103006102006101006100000f65000f63000f62000f61000f60000f54000f53000f52000f51000f50000f43000f42000f41000f40000f32000f31000f30000f21000f20000f10000e65000e64000e63000e62000e61000e60000e54000e53000e52000e51000e50000e43000e42000e41000e40000e32000e31000e30000e21000e20000e10000505000504000503000502000501000500000403000402000401000400000105000104000103000102000101000100000000
    | 1 => 0x106505106504106502106501106106106105106104106103106102106101106100106006105f64105f61105f50105f40105f32105f21105f10105e64105e63105e62105e60105e54105e51105e43105e42105e41105e40105e30105e21105e20105e10105502105500105402105105105103105102105101104f64104f62104f60104f54104f53104f52104f50104f43104f40104f32104f20104e64104e63104e62104e54104e53104e51104e43104e42104e41104e40104e32104e30104e20104e10104400104104104103104102104101104100103f52103f42103f21103f20103e52103e51103e42103e32103e30103e20103e10103401103102103101102f61102f60102f41102f30102f20102f10102e65102e60102e54102e53102e52102e51102e50102e42102e41102e31102e21102e20102e10102504102400102103102101102100101f50101f40101f21101f20101f10101e54101e52101e51101e50101e43101e41101e32101e20101e10101500101103101100100f61100f60
    | 2 => 0x505f10505e72505e51505e30505e20505e10505b74505a74505764505762505760505662505661505503505501505500505106505105504f21504f20504f10504e72504e10504b74504b64504a73504a64504a63504752504750504651504642504504504500504102503f10503e52503b64503a54503742503642503640503632503630503101502f71502f51502f21502f10502e51502e41502e31502e30502e10502b32502a76502a42502721502720502665502621502620502501502500502400501f20501e30501e10501b31501a31501710501610501500500e32500b30500b20500b10500a50500a30500a20500a10500761500661406775406773406772406770406675406673406672406671406670405e75405101403e41403102402e30401f20401100400f54400f43400e70400e50106f63106f62106f61106f53106f43106f42106f41106f32106f21106f10106e65106e62106e60106e53106e51106e43106e42106e41106e40106e31106e30106e21106e20106e10106506
    | 3 => 0xe21b40e21b10e21a70e21a50e21a40e21a10e21501e21360e21102e21101e20f70e20f60e20f50e20f40e20f21e20f20e20e50e20e40e20e21e20e20e20b70e20b60e20b50e20b40e20b20e20a70e20770e20760e20750e20740e20731e20720e20501e20500e20401e20370e20360e20350e20340e20331e20320e20101e20100e10f70e10f60e10f50e10f40e10f30e10e70e10e64e10e60e10e50e10e40e10e30e10b70e10b60e10b50e10b40e10b30e10a70e10a60e10a50e10a30e10770e10760e10750e10740e10730e10501e10500e10401e10370e10360e10350e10340e10330e10321e10103e10101e10100506f72506f64506f62506f61506f53506f43506f42506f32506f31506f21506e76506e65506e64506e63506e61506e60506e53506e51506e43506e42506e41506e31506e21506e20506b20506b10506a10506776506773506772506771506676506673506671506506506504506502506501506106506105506104506101506007505f75505f74505f72505f41505f21
    | 4 => 0xe41331e41310e41102e41101e40e41e40e31e40e21e40e20e40b20e40a70e40a60e40501e40370e40351e40101e32f71e32f61e32f51e32f50e32f21e32f10e32e70e32e60e32e52e32e51e32e50e32e43e32e31e32e21e32e10e32b70e32b62e32b50e32b10e32a52e32a10e32621e32620e32102e32101e32100e31f70e31f61e31f60e31f51e31f50e31f32e31f31e31f30e31f20e31f10e31e71e31e70e31e61e31e60e31e51e31e42e31e40e31e31e31e30e31e20e31e10e31b74e31b61e31b31e31b10e31a71e31a61e31771e31761e31751e31743e31742e31731e31710e31640e31620e31501e31500e31402e31400e31371e31361e31351e31331e31310e31102e31101e31100e30f60e30f31e30f30e30f21e30f20e30e70e30e60e30e50e30e41e30e31e30e30e30e21e30e20e30b70e30b60e30b50e30b30e30b20e30a70e30a60e30a50e30770e30760e30750e30730e30720e30501e30500e30370e30360e30350e30341e30330e30320e30101e30100e21e41e21e10e21b60
    | 5 => 0xe51e42e51e40e51e21e51e10e51b70e51b50e51b30e51a70e51a10e51770e51750e51740e51730e51710e51502e51500e51370e51350e51340e51330e51310e51102e51101e50f70e50f31e50e70e50e65e50e51e50b70e50b40e50b30e50b20e50501e50361e50101e50100e43f51e43e41e43e40e43e31e43e30e43e10e43b63e43a73e43a63e43754e43632e43631e43630e43503e43332e43103e43102e43100e42f62e42f61e42f60e42f43e42f41e42f40e42f31e42f30e42f21e42f20e42f10e42e62e42e61e42e60e42e43e42e42e42e41e42e40e42e30e42e21e42e20e42e10e42b62e42b53e42b21e42b20e42a62e42772e42751e42742e42721e42720e42630e42621e42620e42502e42501e42500e42403e42402e42372e42342e42321e42320e42102e42101e41f61e41f60e41f42e41f32e41f30e41e71e41e42e41e41e41e40e41e30e41e10e41b61e41b41e41b31e41b10e41a71e41771e41761e41741e41731e41610e41502e41501e41402e41401e41371e41361e41341
    | 6 => 0xe65104e65102e65101e65100e64e62e64e51e64631e64630e63e30e63632e63631e63630e63503e63400e63102e62f71e62f43e62f40e62f31e62f21e62f20e62f10e62e61e62e42e62e40e62e31e62e30e62e21e62e20e62e10e62b42e62b20e62762e62752e62731e62720e62630e62620e62503e62502e62500e62400e62362e62352e62320e62103e62102e61f50e61e61e61e51e61610e61401e60f31e60f21e60e41e60e40e60e31e60e30e60e21e60e20e60b60e60b40e60b30e60b20e60750e60501e60500e60350e60101e60100e54f54e54e61e54b73e54651e54632e54631e54630e54403e54102e53f70e53e40e53a30e53a10e53632e53631e53630e52f53e52f52e52f51e52f50e52f43e52f42e52f31e52f21e52f10e52e62e52e53e52e52e52e51e52e50e52e43e52e32e52e31e52e21e52e20e52e10e52b50e52b20e52b10e52a20e52a10e52740e52501e52500e52402e52401e52363e52340e52102e52101e52100e51f71e51f70e51f32e51f21e51f10e51e70e51e51
    | 7 => 0xf31504f31500f31400f31231f31104f31102f31101f30f61f30f20f30f10f30e73f30b10f30a64f30a54f30a30f30731f30642f30641f30630f30500f30230f30104f30102f30100f21f70f21f60f21f50f21f43f21f40f21f20f21f10f21e70f21e63f21e60f21e53f21e43f21e40f21a73f21a63f21a53f21a52f21a43f21a41f21a21f21730f21720f21710f21630f21621f21500f21221f21103f21101f21100f20f60f20f31f20f10f20e20f20b72f20b63f20b62f20b53f20b43f20a53f20a43f20a20f20631f20620f20502f20500f20253f20103f20102f20101f10f50f10e60f10e52f10e32f10e20f10e10f10b72f10b51f10b50f10b32f10b31f10a72f10a62f10a52f10a42f10a32f10a10f10642f10610f10500f10242f10210f10102f10101f10100e65f64e65f62e65f51e65f50e65f43e65f31e65f30e65f10e65e61e65e53e65e42e65e32e65e31e65e30e65e10e65b54e65b52e65b50e65774e65770e65661e65653e65650e65505e65500e65400e65376e65350e65105
    | 8 => 0xf50b70f50b10f50a50f50662f50661f50104f50103f50100f43f62f43f61f43f60f43f32f43f21f43e61f43e60f43e20f43e10f43b75f43a65f43752f43751f43750f43742f43741f43740f43732f43731f43651f43650f43642f43631f43630f43500f43400f43243f43102f43100f42f31f42f20f42e60f42e30f42e10f42b65f42b62f42a65f42751f42750f42740f42721f42651f42650f42642f42641f42500f42242f42102f42101f41f21f41e31f41e20f41b65f41b21f41a65f41750f41740f41710f41650f41641f41400f41104f41100f40f72f40f30f40f20f40f10f40b75f40b20f40b10f40743f40741f40651f40500f40105f40103f32f70f32f30f32f21f32f10f32e71f32b54f32b52f32a74f32a54f32a52f32751f32741f32740f32730f32721f32720f32640f32632f32631f32620f32501f32500f32232f32104f32102f32101f31f21f31f10f31e50f31e42f31e41f31e40f31e10f31b54f31a54f31a31f31750f31740f31730f31710f31650f31642f31640f31631
    | 9 => 0xf65e10f65770f65265f64f53f64f50f64f30f64e51f64b54f64743f64741f64104f63e41f63e21f63771f63770f63732f62f60f62f21f62e62f62e30f62e10f62b52f62a62f62770f62760f62662f62400f62104f61f60f61e71f61b21f61770f61760f61400f60f71f60f50f60f42f60f32f60f20f60f10f60e73f60e42f60e10f60b50f60b20f60a72f60673f60672f60671f60660f60272f60107f54f21f54b74f54760f54751f54750f54401f54102f53f41f53f21f53e71f53e40f53e21f53e20f53b43f53a53f53762f53761f53760f53752f53751f53750f53732f53731f53661f53630f53500f53400f53102f53101f52f41f52f32f52f31f52f30f52f21f52f20f52e75f52e41f52e31f52e30f52a76f52761f52760f52750f52721f52661f52652f52651f52501f52401f52276f52252f52102f52100f51f31f51f30f51f21f51e75f51e40f51e31f51e30f51e20f51b71f51760f51753f51750f51664f51400f51264f51104f51101f50f43f50f41f50f20f50f10f50e42f50e30
    | 10 => 0xf65e31
    | _ => 0
  fld packed 24 (i % 128)
def thirdGate (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x731730721720710676675674673672671670665664663662661660654653652651650643642641640632631630621620610507506505504503502501500406405404403402401400387386384383382381380376375374373372371370365364363362361360354353352351350343342341340332331330321320310287286284283282281280276275274273272271270265264263262261260254253252251250243242241240232231230221220210108107106105104103102101100000
    | 1 => 0xf65f64f63f62f61f60f54f53f52f51f50f43f42f41f40f32f31f30f21f20f10e76e65e64e63e62e61e60e54e53e52e51e50e43e42e41e40e32e31e30e21e20e10b86b85b84b81b76b75b74b73b72b71b70b65b64b63b62b61b60b54b53b52b51b50b43b42b41b40b32b31b30b21b20b10a86a82a76a75a74a73a72a71a70a65a64a63a62a61a60a54a53a52a51a50a43a42a41a40a32a31a30a21a20a10776775774773772771770765764763762761760754753752751750743742741740732
    | 2 => 0xf75f74f72f71f70
    | _ => 0
  fld packed 12 (i % 128)
def fourthGate (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xa60a54a53a52a51a50a43a42a41a40a32a31a30a21a20a10775765764763762761760754753752751750743742741740732731730721720710665664662660654652651650642640632631630621620505504503500405404403402401400387376375374373372371370365364363362361360354353352351350343342341340332331330321320310276275274273272271270265264263262261260254253252251250243242241240232231230221220210106105104103102101100000
    | 1 => 0xf62f54f53f52f51f50f43f42f41f32f31f30f21f20f10e54e53e52e51e43e42e41e32e31e30e21e20e10b76b74b73b72b65b64b63b62b61b60b54b53b52b51b50b43b42b41b40b32b31b30b21b20b10a75a73a65a64a63a62a61
    | _ => 0
  fld packed 12 (i % 128)

namespace Row26
def vals : List ℕ := [1,1,1,1,1,1,1,1,1,2,2,4,4,8,8,10,10,10,12,12,12,16,16,18,18,18,20,20,20,32,32,34,34,34,36,36,36,40,40,40,42,42,42,42,42,42,42,42,42,42,42,42,42,44,44,44,44,44,44,44,44,44,44,44,44,44,48,48,48,50,50,50,50,50,50,50,50,50,50,50,50,50,52,52,52,52,52,52,52,52,52,52,52,52,52,64,64,66,66,66,68,68,68,72,72,72,74,74,74,74,74,74,74,74,74,74,74,74,74,76,76,76,76,76,76,76,76,76,76,76,76,76,80,80,80,82,82,82,82,82,82,82,82,82,82,82,82,82,84,84,84,84,84,84,84,84,84,84,84,84,84,3,5,6,9,17,24,33,65,96,3,6,5,6,9,24,11,14,26,13,14,28,17,24,19,22,26,21,22,28,33,96,35,38,98,37,38,100,41,56,104,3,5,6,9,17,24,33,43,46,58,65,96,106,3,5,6,9,17,24,33,45,46,60,65,96,108,49,56,112,3,5,6,9,17,24,33,51,54,58,65,96,114,3,5,6,9,17,24,33,53,54,60,65,96,116,65,96,67,70,98,69,70,100,73,88,104,3,5,6,9,17,24,33,65,75,78,90,96,106,3,5,6,9,17,24,33,65,77,78,92,96,108,81,88,112,3,5,6,9,17,24,33,65,83,86,90,96,114,3,5,6,9,17,24,33,65,85,86,92,96,116]
def inputs : List ℕ := [0x3b61db21db0ed92526d936c936c9b649494955b600000000000000000000000000000000000001ff,0x40b7050205b8285c082ce14041670a1717172c0a000fff80007ffc0e0003ffe0001fff0383838600,0x2e0c20617061030e89c304184e1820c3a3a3a380dfff0000fff8000707ffc0003ffe0001c1c1c1800,0x8504285728b9470011408a14ea2751c024bfc0500000000fffffff8000000003ffffffe0001fe000,0x2e61730e4302182009d84ec388c0460803fe48061fffffff0000000007ffffffc000000001fe00000,0x30818409840c20492de06f03ef03781ffc000028000000000000000007fffffffffffffffe0000000,0x3f01f80ff80fc07ffe00700270038012480000301ffffffffffffffff800000000000000000000000]
def scs : List ℕ := [0x1a8000a0a929ca8,0x1dc00250a6294a4,0xd428000a2284a3,0x114000a0a6290a5,0x11400250a9288a7,0x1a828000a829ca9,0x21c6a000a5290a6,0x1dc00148a6288a4,0x1a8001dca828ca1,0xd40021ca528ca2,0x25000148a9294a8,0xa00021ca9284a7,0xd4000a0a728ca2,0x250000a0a9298a5,0x1dc0021ca8298a4,0xa000250a728ca1]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
def recipe7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x6169030916a5127311c6871e2335a1e1c02c763a15a1e81b151d24f101e21b286b03a075da2a5f1c05006020fa266a8fba6169b52c2224a9e16a4fa71822a5f1cba72f6d83a092eba15f168502803029303c9869318a27393f4013b39a417f3d9b53f74bfc41169b5246c9b5021984c0b3d9c617028353a720f48a5a9b5035b3a126379c9051731133313fc030905b07053ca5f089c6051f85809183f4901e23e2c5fa2a5c5da2a3d73ba03616b1d5e603a1311aab9070905b915b3a1285b3f42a32850741984c32182b92a06bd22f3c83637711b525083fe2e3f0ae89093a3073ebfc62093a33a3f850184599001199b1244dca3702123ea31822a02183f4054022a10073e1065cba107171b102168502b5623e781e012310ba4ea0169b5375500e471822a01169c696168503e744994e42ba0061f858052104c115d05b0e2ebfc5a4d9b5290428c911685007218503a6c806001c825a8169b59907420306e3fc701823e335b190357003a264f84c2b50a3e241984c101abb22c16a4f07313fc380201f0517108076122a041e1c026763a1296b8f53000858741e04c9a1d3d73665a3536541c5901aa3b4e2123e041fb13243e01764181b10518a280640ba0
    | 1 => 0x3670a2a0f79002101ca4d255f8120418850061840113083f65663bd2044ba2a04093a30103a0715760f49b60235021e04c42169b5071885030402331e020812840a27074ba2a071990327524198b08235815c22a5c5cba10d420160f5e85d0c181d1351e2b49818a282a16a515c00a2a266e8f50d292de282d1b8a61822a4e1b81430763a1263f1bd941a850071cb082e313fc231aa320b5c3f4346f83a50183f4246c9b8022104c2b562353a7203a334c1852c6022e071b9b1244d046a3169b50701ba0431822a393282b020a3f4244f3d2931822a9b603a10e02829105b00b012182090071c6075b3a19e422350741ba14e1dc226b0905b0c5e05b0f249d18a3d9b58a183a39818a27240404c06073f424199bb2b6e0f407183f4741b84c050739d04433fc070741d10213b0713d9b5093d9c506020f412789da27313fc2801050264284c041cba7961ba3e4b183f4041685003010f5911ba3e92218500d013d36a4d9b8071c050334d04c3945401245d84c2c4585007168500c043b608488201f0084c3b4f85b126005b2f5ba3336708f525212b4276523e024ba2a836122a0e42235362631f611e2332716850240307510759b8061b84c1c43030344f3a3
    | 2 => 0xe5c046296b9b50f1e1d1bb1a2352e6c1b83670a2e27622357a5a9b531212b4333f23314631c510759b53d2c85b272123e26451bd101a21b8c5da2a07093a32b31bf404169b0643e3a0151ca4f063d9b52a4b8583950a272355a28392121b24621bd5f4d9b8071823e5f1c23b02074200406c050c80420061784c421822a2a3f04c0217a334b5bba1367083a3416a4a031e0200c5d85b74181c0271823e026222a6507420316e9b894413fc36253190d01bd36c0b827393285f07018f5263f1c08a1e3a30f5e91094023fc06023fc8a5b3a1241e1bb2c1ea502407420273e4010317a334a1822a02169b52a3f1b12b21a4d103f3a308010273f74ba1980122a66313fc357022a9d40405387183a294d3ca2a313fc125d85b07028f40b3e05d611a3a7273dbff6a5b3a12a5b3a7144f3d206181c02656872360185b164102c2c5fbd2286b0f404182332716a31871ba331e7da722f5cba707071c624249bb244f05d04218502b4d235275304c031984c2700a3e1b00a3e3e1e9a5021ba2707179bd0702003266a8f41c7fb8271183a32d4f9c5393105d2348985b81822a0a3e05d30483072b4523e33429c02a16a4f3a5ba3339429b133370338a1685003179c0
    | 3 => 0x763d9b5101ea1b060ac05354f85b266a8f5071e1c05e1ea3b2300a3e83603a10b16a4f256b03aac1822a985b22a24211bd044d405b3169b56562ba1334084c333f04c030605d266eba09018850353d1857a3f22a241b9bb317b22a3653b13251e31f041a8500c183a304463a1323c98624039c1020741d90433fc6b093a304212274c169c6061a235334eba6313c98605021b8891d019063d9b80b5a9c607020f502181bd070222e06313fc3a3a9858c1822a2c6c8f5393f04c2e62235333285f011822a051784c30182b9941aa3b026022e2a3105d126301c0900b9d5e0739d240741d8c18a27361aa31943f22a261c1cb06169b50c2c3a003433fc0717a33971283024652338803bfc335a8502851050070605d284d3ca05023fc941ea3b021822a1c1aa32103e9c0995cba1870605d28700f4065a9b51803c3a5c6222a345bba76531ba00e5e235b8169b5240084c39531bd2a6b03a2408be4040741d143e05d4b169b5041804c197806a881ba3e021b84c021784c071984c0b3f05f1060c19282523207193a68f2122790168505d313fc042123e071ba272852419264f9bd2f182b98e5b3a123010505f1e233ac169b5941a235032104c24181bdb11822a
    | 4 => 0xa01822a051740c2d3880d266ebfc902123e065b3a12c5185d07613fc2b3d8502a488200c1e3a39a1dc220c179bb050905b1042ba32f6cba0a91822a1f211ba4d1a85006183f4134202d9416850031e8502c6c8f4050ac053018ab9051e3a30c3d9c6245b3a4326f3a0105bb9d326ea2a156401e394504c1c01050901823e0f18c28041a23e365a858333105d30588343616a3105022de05074200c3d9b80a18a4f061685005010f504179bd890905b355b233036022e935da2a267286b38748052c43050056122e991e850871984c070222a053d9b802211bd03169c6835fa2a365423f2b5a850041f85819448322618ab966403a105313fc04179015562ba107169c6286b1b52b1ea503a4585018199bb244d9b5912101b2e5385006021b5071f858041e04c2418233061822a070283a105fba6071e1033b7283a256c0f54e1784c2f18ab9275084c071e04c0c1e1d1062132b2b5323e26509bd2c19a4a061aa3b1124332241e1bd26561bd063f22a245b3a126429bd396b03a2470a2a255185d2c24a4a701e23e991a8509a5f22a882123e5a1984c0121014042104cb51822a060905b3565a275a1804c2d603d6265182b43169b5ae1822a9007420901a3a7
    | 5 => 0x617bd0100d3f607033a0991aa3b244dbcc87074202f6c8f55642ca383613fc741e3a339199cd031a8501f7b802304f85b316eba0481822a246c8f5961e23e3a4f3a52c76a2a963d9b5611dc22411822a2b5b3a15b21012071e8509421850055b3a1944d9b5393e22754011b52e311080e1ca4d9d4f3d2993ebfc9018a3b345ba3306071c60406bd22b4e8762b6c1b804183f413770f5743d9b807033fc2502130041984c8d168501c00a3e0706bd20d5e85d0621850056c3fc06179bd063e3a002169b007008f50219a27071b84c7a3d9b50b40405316ebfc905cba11d7d8f435700f42c488500e3d85025520125f0905b991a23544169b502013a02a3e3a0266a83a5d16850281eb19955e3a13342a33046122e3b801c5711b9b10a6041d244d9c6654d9b8106005d19788f4064ba2a274e80b3a6e0f410758f5394523e336d8f510311c6735a9b57a053ca4e3d9b82c3f8508e082353c801c5244d9b8133f05f0003a075a1e04c32192b9103e9bd8d3f22a24211d1274b8462e3105d2e4084c2e3f04c085b39d3e1618d2453850265b0190817322741b9c09e1ca4f284f3a32d4f05d0c6005b2c403a1316323b241e1c0071e81b9062235991a23e556222a
    | 6 => 0x7030f5055fa2a106182b3c730f531519c56a07420070d9170c5d84c741804cad169b501211b10617a33001d0196b1d019071a850715b3a10106c05071e401264084c00020032e5a8503a6c8f52b2524d220084c263f04c031a23e01168502f5b3a7944d9b8241ba33002101445169b54d1aa3b4f5e3a1366605022460355c07420ab169b5237a8f5071e23e942123e2765235aa1822a2c6cba025508582f16b1d2f5b233286c8f5105b1850319a2766093a3061984c07030f42b1a24d271e23e1901050701685033008765d5da2a0c3d9b500210121a5f22829524195f313fc275323eb61822a5a1b84c106c1b5383d1852842a27241e1d1393f1bd0a66bfa052185007013a005179bd5a07420306e03a8e188502b4823e033d9b546169b55e5b3a15c013a106093a3361f31d441822a245685005199b12e4b84626531bd951d019031784c101ea4e3a1e24a2a70bfc061823e255701959674312f4f3a3620905bb7169b50c1bba3880905b0c0105b99071c67208235901a850106041924199ba2b3f23e9e4f3d2275d85b3551a3f870ac05235f9912c4f05d8f5b22a784022a334d850244f1c51763bd2041c419394b8462d603a7394284c023e3a007181bd
    | 7 => 0x264504c040122a903f22a17063cea41822a256e9b5071fb136a0741d47169b5072104c06018f4991685097082351b1aa32945cba1963f22a2a6a8f5266ea2a07413fc0702a2e326ebfc87071c62003ce4742104c33652353a43050316ea2a230084c071a23e051822a395a8500221850361eb1c5f093a3264804c3670bfc3b463a42c6041d21011b00c6285b041cb072f62bcc985da2a2633a3e102121b20011b09b6122a451822a3665a3e103e84c9407420064022a295b3f42a4b8460731ba0266a8f63a5b2330c18bc7286e0f4281ea3b701ba3e275a85002188500f3d9c6901a2355d1b81424041e6062104c254eba6775b22a3e7403a3f58ca3155d05b051984c051804c095bba43b518162f331c6106c1b803074200663bfc2c6c9b82d4f1c5073d9b5041784c01169b5064d9b5285b2334e5da2a0f5f1c5240202005179c08d1823e0b5c85b2806a4f071784c033d9b8347d3a15a5b22a326f3a1076122e741bba3001b814246e0f4256c1b52e6c1b505093a3367da2a3543ba19417a3307063cc90413fc951a9080621213615b3a18f1822a0e5e05bb71822a015b3a107023fc056222a901a23e3162233074d9b8881d019610741d763f22a965a9b5
    | _ => 0
  let q := fld packed 28 (i % 128)
  (prefixGates (q &&& 2047) <<< 24) ||| (thirdGate ((q >>> 11) &&& 511) <<< 12) ||| fourthGate (q >>> 20)
def finger7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xe248d9d5c8881d67e080e70d4ba09e4009769207f9ea1c6e62626c032ca75c95c2c2f027b3afbf977acdbd4ab824cde99d2fec875346804331c393bf74b48145b6ed9704e936ea542255b345a29eea716c6a5ada964223acc11a3191663e315b803f64db826ff6c6305f92ac33e1d170ed2f229e0b2d6bb49fad843eabd4b306
    | 1 => 0x87c0f34f2e2c8d4b81607ace95f2241225474d651ae720e13eca52cb8cc685cb52ba9920820437bf0e0e7ac3a1275790837b6274404c5d89a71c61440440e3e22d5afb60a544158a2c13d0727949986527bbce8e0726f6b5e0ac5ed427aa0fcd043dfad612680ba7129d0ee6215997fe61fbdd999b1d5af8fef612b9c47e1102
    | 2 => 0x59da1e22172e7f14a42a50d73561d3533065af6e942110a9d0d27b9695ba5c5c47edd8a4afae892c6cda6ac6e40794448c89f466880332703ec97812f5df98bdf3165744a698649daa0d3f407f089268013fda0abd347889da209f96197318654da39695fba97665777e393f94026ec38873a7af8e97d58ab674eb7fb17a1ffa
    | 3 => 0x56945944fb43417ecf9eaeac37cbf1e8394f0e61485987928522838f9bf0d8f652f7522796ae8e3868fce50d4322903ff5df561baa35fd906685109b52a0d24335c4fb4f0c5a0bd3f881fb2f147166a306bed519d4a2877306bd0eb2df1ef50586a70d135eb757bdc682f27adc25255f322ff05399dd6cb45ed4f72e57748f74
    | 4 => 0xeafa75977e11fa89b13390b703f3c64dedd01a3ba0262f4be57bf93e97e949f2054a7303174357938c110b0c2ec8fa3571f882ba27a1dee4a87629ca97cc8364bcc3c177ee2f83880f67bf99b7bbc4a125c8a7f585d88146465ae312ac01d9f748f351be479b2dfa8482632b25dc0f8f0b224a314693c86782f00495db6754ce
    | 5 => 0x5409a25abe4b4008f29b9ede56c590761f364a70dd785b626832cb9d8efdb437c289dda624aa2546b1c7f239bec0e9201d0925a12f18d5c8a46c697155aeb7851768425460a18bb97c04a761625636f19326d1bd510879c9428a619117a43843eb43ebc17c429019e9a83a1ae9dd9cfdde79fb52f4e624a18b90272a829cb3a2
    | 6 => 0x1c0f9df378ee5acd8c80f60e0a29e1b121c539a5e8c4fec4f888fe6fcfb3dffa674e1df673730bda755f5e52d9e4bd47078b69908583067d9c04c9411f9e3beac28f207b8f74c8e8ce2fbca439454812f6cb0a4379b60b7ee477f569c0557208ce949863da0220346de7bf5f374195595c3426e73c4c16ef17a9e115acd8ef77
    | 7 => 0x9608ebcfce3b218b9fa7fb2b6634a0c9b1bbacc32277a8c8538fb2c68bee6ca529723482d644a79b73af2c3351395e7ac59a60c6e207d87f4170adab67ef2a4ef551998b4327ec60e21edbfc74d4ed66d35238f9df8a0dc4e1ad3a9ff075bec3f1be811f612bdd5c21bf076fbf36292a216984b7e7801763200933c19009da4b
    | _ => 0
  fld packed 8 (i % 128)
def recipe8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x5d8170405d301c538834043fb4b846040585f8580282018a270300e280f54123e2a03a4000f6107c0405b279ad3a1863a9855d84c4022a3e1c51b31a6d8f52d9b3633ca0ba4e01baf3e01668034011b54b0252e8032190c6d0f4402272104c4b9037b8f54a100400240b4107d0f4609343482e5601352419440194f1c51ca1b0302903ba13e9c50302f0280d6c0f47f83a541c54700d179d06d0f54d8501d40e6723754bd678005759b56c8f544825311c63a1961899801a331ca4d568700c9ac0081c779b55b84c720f403022020f57d8016f80266bfa6281b019c05c8503582c748f4533a637046038f5290036510f009b11c8255e827608151a9ed663c33385f109bb17a3353850169b5042f81bb246007167238222310380843b083180f519111cb076a11c030164d9b1023072523123316328502331f728f54185025232
    | 1 => 0x4eb122906c712072c827019c248185298f4179ba0411d5c85b5d23f5f8136b1b85ca272e005011b13f8231618d032763f80f59046799b5609c52d8f5053183d850018402331c3a99768455011c6261a61b8201e81b031165e05b280f4233223482f01817400230b91e3900b043d91e8766c1b503133011b822b244e3ca5b1900407f6991b7ba2a790026105d043a7291b55c04c242e5790f43e01b470ff6442061c19040461da515e934769b8259ad0205d778057a0066c8f42c86b29805042284305044829030353f0200f9a5288f54d80c1b91a5f1492d0f52e9b5758f41b8125f1c518a2864c2632c00013a55a8580530f2a0f47d06a581597fb8218bc75c23e0bbb137833169c617a4203a2a4d04c218207f0f5771b5059a6402281f858279ac199bb7da72044055323e2980664c3a1822a028586b1b5458467c3a156011
    | 2 => 0x599c6e03a1b136630221b9a90084c5d85b51828041e61f31d3b0392e0f6674226791b6eba07b0f45a8466787e2698d4d00b67bc24e00d7603a0112d2d883680106481f4685867819029c06a83a710053e9bd4f84c2b00576ba00306e1d24f031c328a2a03b11269a8073f45f9867d0f5271ac0287a2b1b865870028374a023560580739d1e31f4d4016323c4fc1d18b177ba2e0bc113a8396ebfc030314cb9d3f3f40223c041085c0201d25142812360175ebd263bd3291b84187e50986380332d8f6202b9630163c83806bd24000e6f8f53f80e2e0f57a00348850008f56323f040ae1d243189026123f2a0f5044201ab19798010402e043d01b3b2028353d8213100e748027d8f425a4225250043b66301c5ebc9191cd50813013f41e3274d3ca0340d763a13f85022b23103fe61bd5044010280925a4a7e8021a3f6771b8
    | 3 => 0x620462883a6385d029fd1784c23cdb038307d8027c1b37aa094b858789da6e8f5028160383163bf009c11173223e0173f1b1401c6040ff5480e7d8f503075028155e9c5379c9023fc040161b9b92e83a7b0f55d05b2c3a03f902040505b06f01c1d37116018811a24f6a8f53a0fc2524d083e14dbf45ba333e9c06187d2e8321a8506402a7b9b53e9013a185029b36d8f427ca8631c564ab2740f55282b22bce16b1a2a83a42016421fb0432b292de0330700a271fa83420500108064aaf53017028217c804520128005d63827021c20440a028316401e60822319c6039087f8f4259a6643d62903a31bf404400169b0252300441d5b9bd661102d8026f83a5480f1c428020074b985013a0039b506c05043a30381e0281c390ff183fe5304c3d185630194d3d25880f22b297f9b34dca373805561c17583a7e00002b14730f4
    | 4 => 0x2330c67c26000f529ba05cba37f002570891518d1a2350300b2737b7c0f5038124c18557ad35f86f5601c65017313fc6219156872041c56380e1aa314f05d5502a6ea2a6c80220c841aa3242235173b40185b043cc028415cba50380a038271fb137020700858781b86000c2a0fa3a19004041249b9492335bb9e4a986249d11ca4f0180c01001028f575ba017a430184c5a9b57e9d8029c15e3a53085d028336482f1a23e024997f0045181607bc714b0e2f9161b9d0038587b9b8301107b8f4489865d1c5029c4710000340b0b1d12a0fb1eb1c2d3fc5005d4223e0412e17b1617ba731ba0023154c05806bce58834041b118322243325ebbb021c62081f1ca4e6c9b86101918c2815ae80404077bfc211ac2118d041c66100e510155b9c03d9b54f3d2083fe3ea335781f700f439031251cb7f8f55b0190325d438300699c
    | 5 => 0x45850298f5760f5610254e86f6c0054ebd067bb5770f479ba037846403f43385b63819131a26b3a11685003ce43780d199ba1c40c02829202a209410680306f004613ab3f05f500275f024039176b03a1d81a768f53d9c50281b0285f61815708f5028797a8f440010089c6508580200c5f81b728f4091d1783fc0303053046720f5202b4758f54c192661350383a1e1ad0300a778f52c8f425a4351a3f780030bbb21aa3b2330d6b8f550a27788f405199032d446810038093f22a6c3fc6847a44a5d5f07c2332162185532127286b2c85b1dbdc6600d31931293fc028710905b6cba04001a4223b249d05e3a36e80221ba222b286141d7f4995e91003a076382903985179bb4e05b2c1b5181b1028f63813544832684874dba3030142e0f47a030451385318548820074203c035042356d83a1d25022b263e05d6091003829
    | 6 => 0x38f4043d31dc223105d6402b0404c760fb798f5370331ca505a9946b0fb1d0191d24203bfc29a2a16a4f01027179bd020036791321850644306d3fc04024021303285f233df01bca57087210144481a519c5030346681f3200e044196782c290f5043c12803a73002450465a9925c902021340223d188505b80c02c26561fc3d8fc293a116b0f773fc6180e4084c2798a6c0065440221012173193f04c4f9c00407620bf84102c353f46a8f45ebb72b0fa7703a034112e8f55c80c5485d03b141cb085182646b134e92f023080382c7a83a019e1021b03241d043ca648290b3c73980b5f3d2043084f85b4400f313d2039b0770f52d85f7806a66827658312b8f55b3a11049b2619c7c03a0439d5182b1fb1e6b0f501836183f40105066908728010741d578270449e45876018312798d61825211b1042335a9850302c02405
    | 7 => 0x3880d5e85d7b80216b27720fa5e85b4d9c66500b783a002138039c102020020813e84c610900382d1984c7780201a14748f50413879a2a1804c4d9b867b15038b423318020135c10f08c292123e700f55500e6b0fa179c060bc5041740428c4504c63858639c55b0585a9b02cba33c83674499038076e9b82031f093a34822704110788f528802043d62b83a6281870a2e01ba5038171d22f0431260be96d1b37a0040340c03c6e03c3a628fc0392e4f3a5019bd2524e6401503032319c5748054804c77a2e683c458c8e2634c171af18a51023a058cca4b1852ea2a7bbfc3cc8e02b1109c290281967bea191cb03ba0481860b411044a3798035b39d043111b814038153d9b039a4164c2c5b3a7474812d0013a100513f4020313c037491854680c16a311d2472331e4303001ba30315a0284c7e0f45f8206182b5c39d5f05d
    | _ => 0
  let q := fld packed 20 (i % 128)
  (prefixGates (q &&& 2047) <<< 12) ||| thirdGate (q >>> 11)
def finger8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x70b1d7c555844c03cb80d0155945e41953891fafbfea4eaa3a62263c52ce3895ef3ff01d5aafefccfd137b6712d9ae209b2122b053e416380fa47fb88b92f61da1b04fc727c1e24e55f2637f72ae499136be5a4b2cc02538da89123fee3e48068c3f96282b3a9227305992bdf89fc853e8d645cb0b27fd9e92cb074c9c2eaf31
    | 1 => 0x7eb24ca81620d0ab3c68ae15138d2865edb76ccbbc16d3daeebdf6a26152a0556dba188a42f28f1df722c368a148ce9074544568c176af3a6046057dbdb88b52134437ad220bac363ea20845aaf24ca0fd9f0d0ac13267b6dfac28d41cae74fc044b2e53a1b1842c269d98e660590d33f9acdd84b80747039a4e12681839e1de
    | 2 => 0xa1e8d226e2256a15df5b55ea4e0fbaeaf129480e73577176096d0671d03bb9bad9391cea4d3c44677aeb6a07c15d1824124f2437f1c62f6a21901db230d8f9b2f21ecc20d212fdbc52412ed2d40bbaacd13f8e55f7bbf176daa0cac1192b6f5b8feea060aa2e31357bab3d2bfa09055f6063336b22d4f9ba1414d2eca8eefc2e
    | 3 => 0xbc6e2194fbebf6c50fe79d5a3476102475906fc08981a82f3b0d4a659b5c53de1e640b1def54f13a318e1df60e0d77e1d49f081bb00ac7b6663483c96557b3bd22e25ec2214c8a4810f15bf7e812120636a9f819876e84655af477f2e77f79055af6cf669e7b4f12dafbf27adc6544da23e3d9dac9b2c241163db5134fe4f5c0
    | 4 => 0x7e847508d6717f08b15ac589b67bd49ff40c1ab03fcb5d2104d9dc17e78589ed8374ef6e5f2f57faad86fd0f67d34e8647bff6f4b1a1de12c5fe299c449033f27bc3c1f1c4964b93416007c1d45e02c267349a62cc30eb9b0184e312e78afc614c8d6feda39b306004ada5ddae977b87acc2ca314d70cf9c04802790ba31d095
    | 5 => 0x1b8050d33f8e97f5195f14369ff8fdba1f191861bf5fc721bb70b77eb85dc38d65e684398a3681249d71f23ad0ed1d7536c154e4b08af769a4dceb0ab66c085762687452bf9026d734e4a7ad26e7b5659e307298fba9b2abf88a1d8d423e7a4ab6753d763042fb56034d2a1a0fb91b2d6112a201886df6a145875ec56c3152d1
    | 6 => 0x1c2e9d956fe389d7bb7ff5220a93e12af83339a57ac495371f2609e0124fdf70310c4499b96b07a371275796ae9b1447c9d5cf47ac6270765905305e1fc01a7043a1be34c30d1172fd79eb9ded4540e999ccfe9d0509981763657fd9b097c0deebf4217573407b34d31363b97953d9f25ce102b93c613936e13763150118e8fc
    | 7 => 0xd42d9d0a9ecad829d2e23ca9b59a50e8b1b82b11c68172c8864484174bce6cf54bae34852809b6478b1098a8e0bef16d169adc3123e8b5549cd08918b854c01990204d531348ac3cd92daa8b7c56597378ca08badf5e5823716781b7181775c38672e94ece65dd05a29358414c40129e027cf5ba25caa722934a01e4666cf090
    | _ => 0
  fld packed 8 (i % 128)
def count (s : Nat) : Nat := if s = 7 ∨ s = 8 then 1024 else 0

def board : Nat → Nat → List Nat
  | 7, i => cpBoard (mask 161) inputs 4 (recipe7 i)
  | 8, i => cpBoard (mask 161) inputs 3 (recipe8 i)
  | _, _ => []
def atFinger (table : Nat → Nat) (ws : List Nat) : Option Nat :=
  let h := hk ws
  let i := h % 1024
  if table i == h / 1024 % 254 + 1 then some i else none

def lookup : Nat → List Nat → Option Nat
  | 7, ws => atFinger finger7 ws
  | 8, ws => atFinger finger8 ws
  | _, _ => none
def ck := checkpointCheck 161 scs count board lookup
def pan (s i : Nat) := ck s (board s i)
set_option maxHeartbeats 50000000 in
lemma block7_0 : span (pan 7) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_64 : span (pan 7) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_128 : span (pan 7) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_192 : span (pan 7) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_256 : span (pan 7) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_320 : span (pan 7) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_384 : span (pan 7) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_448 : span (pan 7) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_512 : span (pan 7) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_576 : span (pan 7) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_640 : span (pan 7) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_704 : span (pan 7) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_768 : span (pan 7) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_832 : span (pan 7) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_896 : span (pan 7) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_960 : span (pan 7) 64 960 = true := by decide +kernel
lemma good7 : span (pan 7) 1024 0 = true := by with_reducible exact (sj (sj (sj (sj block7_0 block7_64) (sj block7_128 block7_192)) (sj (sj block7_256 block7_320) (sj block7_384 block7_448))) (sj (sj (sj block7_512 block7_576) (sj block7_640 block7_704)) (sj (sj block7_768 block7_832) (sj block7_896 block7_960))))
set_option maxHeartbeats 50000000 in
lemma block8_0 : span (pan 8) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_64 : span (pan 8) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_128 : span (pan 8) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_192 : span (pan 8) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_256 : span (pan 8) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_320 : span (pan 8) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_384 : span (pan 8) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_448 : span (pan 8) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_512 : span (pan 8) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_576 : span (pan 8) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_640 : span (pan 8) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_704 : span (pan 8) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_768 : span (pan 8) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_832 : span (pan 8) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_896 : span (pan 8) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_960 : span (pan 8) 64 960 = true := by decide +kernel
lemma good8 : span (pan 8) 1024 0 = true := by with_reducible exact (sj (sj (sj (sj block8_0 block8_64) (sj block8_128 block8_192)) (sj (sj block8_256 block8_320) (sj block8_384 block8_448))) (sj (sj (sj block8_512 block8_576) (sj block8_640 block8_704)) (sj (sj block8_768 block8_832) (sj block8_896 block8_960))))
theorem closed : ∀ s i, i < count s → ck s (board s i) = true := by
  intro s i hi
  by_cases h7 : s=7
  · subst s
    exact spOK good7 i (Nat.zero_le _) hi
  by_cases h8 : s=8
  · subst s
    exact spOK good8 i (Nat.zero_le _) hi
  simp [count,h7,h8] at hi
def rho (ys : List Nat) : List Nat :=
  let a := fld 0x241e8700452bd4d5b9ac0800b194030a0023292721100198a01150119c0510843008c02906010001 5 (bsr 0xfd356f1ef6e89598f389cc02eaec9a74e968fdc8e90a70ade6a94e04ddfbeb78daa3d3cbcbc8cd82c8b110a9c6f26311c33ddce8bfca6579bf2fb6e0b9aafae4b6d3eddfb24e7b36ac56727da3255ffe9836ca2f96b10df38a5599d588a3c458878fa7a584ef97717cee56ca798bb9e87940e06777fadc0165e3f9c265b85c2d641ccac75cf1d879583f712c580c731957b07efd558e792a558b6be055809c225499bbec4f0e61214d99dc424ca69a8549936523398838913613983b346e7c9331cf2ecc2c7b9ebc298b49532544fb592448e2d92085ee49187beddf17882ede12009c670f4f26fe0cdf66f30a1bc6c4092451960379507400e99527007e3081 32 (hk ys) 7 0 64)
  if a=0 || 16<a then [] else
    let c := fld 0x1ab850711d4237462e45c08dce0735284656a2e71108eae070ad45d1a2352a31ac6508d1b815ac623b91000000 21 a
    vals.map (fun v => fld 0xff003c800e50000000e20035400c80000000c50030800a9000000122004540109004c67a949821e4a84004524077899aa10670040e0a6481185505f0000000df0034800c7003b9f45276915c64200345ba35680a18c250030586226007d4e1d0000000b5002c800a6002e5761a5c05d4a15002c566125803d480d0028d440b508240000 9 (orbitLabel c v))
def B (i : Nat) := mv (mask 161) (fld 0x401506000e10f10500106e21e53f31f21400100 12 i) inputs
def I (ys : List Nat) := bsr 0xe90a70adb24e7b36ac56727d8a5599d57cee56ca580c731955809c223613983b2448e2d917882ede0a1bc6c40379507400e99527 32 (hk ys) 4 0 13
set_option maxRecDepth 10000 in
lemma roof : bar 161 (cutB 10 inputs B) (cutN 10 13) (fun _ => I) (rowOrient 161 rho) scs 11 0 = true := by decide +kernel
def nextRecipe (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0x8a408e40ba30be306e2082217a218a21910286219730977095001a207e2195029f649f319f549f342e139f309403910395033e139f419f4094049e548e219f2056135e131e209e3195076e219e4194003a603e600e534321472145004f7640004f2645034f214f634f614f644f6044062e644e7641054505410245023e624f134f104e614e714f434f4044044e544e644f301e644e63450741074e134e434e1444004a404e404e605a605e609e604a304e307a0156037e015e03be10b6109e30
    | 1 => 0xc4033401cf42c4048402c40076027e0222215724262157705000550355005f645f542e213e415f405f4354045e545f135f035f105400bb204b30100015001f321f421f2014021e32140026032e0305060106b710b712b717b713bf10bf12bf17bf13b500650075076501bf736f62bf726f61bf706f60b40764066000be17b617250721076105b5066505b507650661063507310785076f21bf306f20b403640255075107bf206f1015071107b4006400ba20be206e10ba70be706e6036033e03
    | 2 => 0x7b0100000f0104000f210f317b218b31530304010e010e215b033b423723272393305370937077014100910001003b6077027f0105007f027400510081003100bb7027034b602704200025032f032f542f0424009b302100250037033f7630003f643f6035033f6135003f543f403f422f413f0334005b403a403e409b4026042e041b207f218f6485008f308f318f548f342f138f403f138f418400570382308a3086308e30bb304b4026017402cf64cf32cf54cf342401
    | _ => 0
  fld v 16 (i % 96)
def C (i : Nat) :=
  let d := nextRecipe i
  mv (mask 161) (d % 4096) (B (d/4096))
def nextCodes (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0x773d179d18f90f93f76f0001875269516500004ee11fb16cacd12faf7488519540000d9042645530f342cdd3b4176c6b5b9d536ce2f21e15a992832871307def054d00005c7004379e3407225d0a509b0e8ce3390dd566e3e30f7052000059d44b5f114288dff48e55ccd87a9418000ccfd39f4d0c195a541ebad837f18c24000059dd6a6269a3dc4a9495a4edc4470e47960412c00037cffcb083400068b8000f32ad3900f10f4
    | 1 => 0x3b4d29c5f556f3301643f44dd992cf9ff08347c32fb8e534a4618000afcc000a0a401a493524ff5d1d4be08c000009d0fc1f8400027c9c95fec93c3e06edcba74456324ad1dcc33e40c14e702900016344eac00010c400066073ab0002403b39967a2bd80000423d207601ae47f3dc106acc000706000073618365db842b5e760be3d747dedde9e7a0000400000000050e85dfea8800015c4000c9100001df2225c897e670410000
    | 2 => 0xa7fc000bfeffda0003fdd512864923d000087ec6600a98000de588dc3afd6e1f8be643df067989e680000cc796242a3641e3ff55d597495dbfec000d63c0000000000df8844a72adb1b0b159f422d2bee12f6d3100000006076f615a6d3dd44d96144bedf9f0001b84383000000000009624a34218c000dc70000cad1a410000000f4de56216a65f440acd5150f429dc6026787ee0000a45e8c200c51f48c146fb6a116ba51e2d5b
    | 3 => 0xf7b014915d80008e8be46a7f23d9ad1adfe2c6a2ef5a44000a76525b6c3d30203c2c37c97c0004b200000001446220400080b2c5b5d08000d5eb53fd94800000522d9eae33af58ac46d0001ab6018134590b4000347efc359952575ec18cb5906eeb3f9fa4c4370a29b9a000000000000b8fa5c5bfc0006d78058da70000a7fb38700006c7739c0002f5ffea53ed3f45a5cdd908785db267c06c0db4f340000000cf00adf2d038e6
    | 4 => 0xb1c864000038bd11a000040800003d55c5dd39bf29c3edae61d8c000a616214ce6d0df00015cd54e631c7c941fe009937c1790000c28e762433c0001bb05cfa6049957c454a30c0b086000311c037800060a92067a141ae372dc2100011d3b416bfe14d682b5fd8997192b58f542d959b35bc0040fe72f4e25f60f31400060c76e025880004c7c0989fab09d29e03c3d404315bdec000a4535d03c2a1e10001e832b38ad40000102
    | 5 => 0x3ee0000b7a3c194aa7e9c25c1423bb2e868b00ffae00011613c85b66bbe80005077d8300000008aa13b981bcd170000000d6fa68247845597e0c0002084b63e698000022f6c5b0e722e959d20d701e48a00000008e200001db8000473893300000000000000ce95f22000000000000170000000bf745a4e2cd6e26bd178f5ba7bfc4fff58014980004e85f4012216399cc1d1105600003987e257c740000000ce1b6fde92abcf983
    | 6 => 0x2997760001a3e1622b08df0528a4c6c6f1e8726f15b79bdf0003b01000168100012de000291f4d32d9d00023eb972a5850001aa404a800023aeca050fc00026c4a0713942d4000165628a455affa81a72fdd78059584d6fe3b9b949d00001c40238c818000986b2318235b450000cdf00001415aeb5d03458c058ede78e000088e02185adaa69231eba3a8e0002071ace4d2763ff965eb5de49623e4c30000000be91ea6b378049
    | 7 => 0x3106217cf1f4f0c0004047c9243b80590001e450000000345b6e6b876f184b1e314c9bb7160001a864b6c25d2dff4d990b209b00009c8053a80f5a8c000f823bc80000967695457c0002c980001b1649f8000b128000ce13f03000122098fd7c67d1564e8c18000e159c6026b8000a4811ed3e61dd8291f2a111c9ba95d1d8b6000082c5f4827b5350a1a000304c0002cc3169dd2d3c78000d6563a56e5265259fc97eceeb69a
    | 8 => 0x9fd0d372bf5baa035d79f000250f0000000419a3982a4ea9a3e62882e8b40000000000000162ed995455000091b4cec5e1727f502355c0a5820965e675be63cb9174c000093200037ab3a79fa23eeb8fea15c5b3bec950e5e38597453eaf2f1a2ae38c68000e0b34292f159d2df650bc0000b2e0002867b03c48a3924000187800ea0eef495e77a3fffc3afc0000250000016f39f7015261b3c7d1820d6e53cd1f90977c7d154000
    | 9 => 0x2c9f9a30c4c00058b414c13417db84bd3b526c90982ad95f2631a1382a6c46a2988e2b0745147000033c00039a2d550000f64eb3dfa7e9490b1889a11f00008ae40003ce671978c16d800000002d22f1c3612ca15a294ee3bc946f4bac00000017998ced4df6e9bd392fc410f00027880001d3c00003541783a6b4b34feb747c9657df14deb332cae0000000000000095300000002823996d7030001c7b000000000027d76714000
    | 10 => 0x52000000002f4fc26fac012f55c0527c000df2c00038b00002794b4b15736a5042c000359800026952a00000861928248cfc8156c7db000000025dd00000000001ab89014ad15a52cf17b3800038fdc59e0c95060000000ea580002170000cf85872dcfd826032d37c2623cd46f4c000af8c7ddc119bafb0d32574bd92882a0c00080a71b5a37001023604d7265561400000000001e370f4c0006b6c00049183f852c858caca253e
    | 11 => 0x5ac0c7071b84a90ec34e316d13a820a9ceba8be1ac5a380008f3c0007ecdc02d86196700000003ed04f80003144fb7cbae0000000d68df2c520c0000c97ff7000131700000000000446ca18000491fc3347d00009dd038f1ef0d890003d7ef7d3724b3780000003f82c18cd88a7055bb108f731e2c40009fe0000fb67589a9dc0a0c47c0733498000b18865c00000006ecf3f3272dbc3000305a48b360d03280001213a8acff0000
    | 12 => 0x3bed777a06c000f55800052044b409536285b7f783b298000969d2d10002c8a0000b9c61e0000d4b000014af51cc3bc94300000005e84839895c00000008ee0000f5e0000000026c185f3ec66c00014904936f560001d9b181f27f045620b5433192e232c0582b8000dcb000049f8ef401baeb6a530000ec0028c48397e5e86eee255041177ef463c6d2c00014a8216313800069a430494e19e7d43c00021701e2f16a8064a8eb6d
    | 13 => 0x7e3d71978221945c12d370001ee82d04c21dc58000024ef3536b4e3553a400000022f559380004a4940c313e2d94e529a200010eb
    | _ => 0
  fld v 14 (i % 96)
def action2 (ys : List Nat) := orbitLookup nextCodes 0 426 (hk ys)
def rho2 (ys : List Nat) : List Nat :=
  let a := action2 ys/284
  if a=0 then [] else
    let c := fld 0x29cb822e5c0a8ee08c77070ab84655c1c46e11a37029cd422e6a0a8f508c7a870ad44656a1c47511a3a82ae70237380ad5c08eae0b8a706a5382e45c1aa2e02ae8c237460ad6308eb18b8a8c6a5462e4631aa31872e28477141cd4a11ea50b9c286ae142e8ca1ac65072e44477221cd5111ea88b9c446ae222e8d11ac688 21 a
    vals.map (fun v => fld 0x141004d001270000001240045c010a00000010700410014000000013f004c80126004fa7aa09824e4a86004864083899da10690041a0a668118e78600000000fc003bc00e4003edf45e76945c64400379ba41680d18c2700311862460086761e0000000bd002e8013a002f1761c5c0667216002d1661458046700e004de6c0c9a8281000 9 (orbitLabel c v))
def J (ys : List Nat) := action2 ys % 284
def r2 (i : Nat) := bar 161 (cutB 9 (B i) C) (cutN 9 284) (fun _ => J) (rowOrient 161 rho2) [] 10 0
set_option maxRecDepth 10000 in
lemma roofPart0 : span r2 1 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart1 : span r2 1 1 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart2 : span r2 1 2 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart3 : span r2 1 3 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart4 : span r2 1 4 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart5 : span r2 1 5 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart6 : span r2 1 6 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart7 : span r2 1 7 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart8 : span r2 1 8 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart9 : span r2 1 9 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart10 : span r2 1 10 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart11 : span r2 1 11 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart12 : span r2 1 12 = true := by decide +kernel
lemma secondRoofOK : span r2 13 0 = true := by with_reducible exact (sj (sj (sj roofPart0 (sj roofPart1 roofPart2)) (sj roofPart3 (sj roofPart4 roofPart5))) (sj (sj roofPart6 (sj roofPart7 roofPart8)) (sj (sj roofPart9 roofPart10) (sj roofPart11 roofPart12))))
def t2 (i : Nat) := ck 9 (C i)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart0 : span t2 63 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart63 : span t2 26 63 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart89 : span t2 26 89 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart115 : span t2 36 115 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart151 : span t2 31 151 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart182 : span t2 22 182 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart204 : span t2 19 204 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart223 : span t2 42 223 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart265 : span t2 7 265 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart272 : span t2 7 272 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart279 : span t2 5 279 = true := by decide +kernel
lemma secondTestOK : span t2 284 0 = true := by with_reducible exact (sj (sj (sj leafPart0 leafPart63) (sj leafPart89 (sj leafPart115 leafPart151))) (sj (sj leafPart182 (sj leafPart204 leafPart223)) (sj leafPart265 (sj leafPart272 leafPart279))))
lemma upperDead (i : Nat) (hi : i < 13) : ¬NatRun (mask 161) (goal 161) 10 (B i) :=
  symCutRoot (ori_ok rho2) (spOK secondRoofOK i (Nat.zero_le _) hi)
    (fun j hj => checkpointCheck_sound closed (spOK secondTestOK j (Nat.zero_le _) hj))
theorem finChk : ¬NatRun (mask 161) (goal 161) 11 inputs :=
  symCutRoot (ori_ok rho) roof upperDead

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 12 ≤ t := by
  refine proveAtCap 7 161 11 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row26

namespace Row27
def vals : List ℕ := [1,1,1,1,2,2,2,2,4,4,8,8,10,10,10,10,10,10,10,10,10,10,10,10,10,10,12,12,12,16,16,18,18,18,18,18,18,18,18,18,18,18,18,18,18,20,20,20,32,32,33,33,33,33,33,33,33,33,33,33,33,33,33,33,36,36,36,40,40,40,40,44,44,44,44,44,44,44,44,44,44,44,44,44,48,48,48,48,52,52,52,52,52,52,52,52,52,52,52,52,52,64,64,65,65,65,65,65,65,65,65,65,65,65,65,65,65,68,68,68,72,72,72,72,76,76,76,76,76,76,76,76,76,76,76,76,76,80,80,80,80,84,84,84,84,84,84,84,84,84,84,84,84,84,3,5,9,17,3,6,34,66,5,6,9,24,3,5,6,9,11,14,17,24,26,34,42,66,74,96,13,14,28,17,24,3,5,6,9,17,19,22,24,26,34,50,66,82,96,21,22,28,34,96,3,5,6,9,17,24,34,35,37,41,49,66,96,97,37,38,100,41,42,56,104,3,5,6,9,17,24,34,45,46,60,66,96,108,49,50,56,112,3,5,6,9,17,24,34,53,54,60,66,96,116,66,96,3,5,6,9,17,24,34,66,67,69,73,81,96,97,69,70,100,73,74,88,104,3,5,6,9,17,24,34,66,77,78,92,96,108,81,82,88,112,3,5,6,9,17,24,34,66,85,86,92,96,116]
def inputs : List ℕ := [0x8d8846c4de36026c41362679b080769016d47c000000001fff8000000000fffc00000000000f,0x16290b149038a95148a8a488c553eca27cd4bc4000000000000000000000000001fff83fff0f0,0xb8305c183840c4e18270c1c1063808c70098c8bffe1fff0e0001fff0fff870000e0001c000300,0x21425ca3c085008a12751e022820311756e30100001ffff000000000ffff8000000001ffffc00,0xb98790c1010604ec3c460804303abe1c0702023fffe000000001ffff000000000ffffe0000000,0xc2046102260816f03f781ff7c0c4c00098001000000000000001fffffffffffff000000000000,0xfc07fe03fff01f002380113800870000e000203ffffffffffffe0000000000000000000000000]
def scs : List ℕ := [0x1f067234a52749c,0x19c1f0c8b3280a1,0x1603207c9f2689b,0x7c0c19c9d270a5,0x19c0c1f09f26c9a,0x2345807ca1280b3,0xc80c11ca02709a,0x11c0c19c9b2689f,0x23432030a52689d,0x19c0c1f0a12709a,0xc81f234b327ca0,0xc81f11ca526c9d,0x19c0c11cb327ca1]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)
def recipe7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x619858061a04f4e18211a21a29e0308a152a1e225256ea08062088d2b5b054153f9e5281e1ed06074057b199d6513e1d7396d8f414758f4b1182052b652aa2b172c5106005d2c6e9dc240a44a03211e31a62a152d4fcb68e17054346f8fa0622054285204d2f31a0836443b926518602c0b4460732c49045b1da29362b0072104f041820d4e1820d041a433264d847180c937031ba0d7016a9c5b1704d5b4f9d725730f4041a29e04211d6373d1859f63c1e5d16a9c123e054071815625518604b19a041f61049071704d2b17a442551c1e2c6c83b8361208b3182052b5b3a42a24a22254fc522873882781984d2b3f20d266ea05394084d745c3b91e3d9b02e7029e265c2a92c25aba271704f625cbb904010f505211d6041f23404019d7935c20507022088921ab14d5d3b931172be884f9d7991b84f011984c2d390670b1698a14603d12b42a0d2b1a21c24308512b5320d72170543b6e9b8286c8f52c4f3cb03010f51a012033a720f4100185c0f6005d05021d7061a29e266e8f405010f50918404b908c423a3e2b03a3305e316e8f5306aa9e051b84d6b0905b2a3f04c631f2ae071a37d2b6c0f4625c3b90308c4239348632c6c8f5346c83b2a4d04c
    | 1 => 0x3a412b0153f9e05d1704f244ec1e836120a991abe3071b84c2771205040183b1b5fae3051cab0245b054022104f991b3e30518205334b9853533a11250b47307000f52a540542e3105d39429d6075d3b903013eb100285b177b0f6660905b3b430547c5c205240841e304f85b2419a465b1b9e2071caaa283304901008f525093fd2454054350b4462b1a2b15f0946c066dc4904018f52e748f57a3f205275fa0d8b21ab02c48a9c0e1cc36041d054326f3a1021e04d061d054103e1d7143e85c1c0084f0e1caaa070bbd31b172c7021804c1461c1c9a0b4732b1a2b0100085c7819bd0ba0b3d2396c0f505020f50221a9c6121ab12e6b0f5040905b356e8f4050905b253f01c06028f53332860041a04f2b17a491e0084d8c0bbbc3b0b2222b012b0324f2ab074f9da165ebd25a00aa0153e1c52b0eac20409452346f83b763f2056a08c42071aaad01000f52d5cc33031a04f051985806020f5051b84f2a5c20d3149054156085b250946c060905b336b0f52e3f04c0731a08136005d2b172a42e4d04c326c29e3f74a082b5b8543f74aa0481a29e35518513074a9e276a8f52c1093e3b072c32a3f1d62f5c3c0411820589094668b0bbbc29773b92f19a34
    | 2 => 0x41b84d042104f30412b1395aab0983e85c31462ac3a45ab0270084f061b84d062104f10791d95e5b3a12551c142c6c29e39509d6031e04d3f749d7051e04d3a4f3cb121fac0af1a29eac1820532519e82a6b0f503008f53b40a342e34c4c3e1eb91021e04f5b0946c2e328602b6c1da2b4804f2c403a12e0995b306c29e150dc36345a4850501b0a3f21383230084d491caaa2e4d3d2890946c07184042b1eab1995f2ad781704daf182052f7629e393e04d061a2b15106bd2041804c0119858491cab1061804c115cc422b172c829523d65b1e1e5942120f14788f50e1abf71518a7a2a16ab0330184d334084c3e1f383054ec5039429bd880946c392121c2b1eab02a5304c350b2222a6d8f5394084c331e1372c4f1e72c5cc423a00854336c0f50b3e85c4c5c20506022a12f74a0807010f52e5304d070b45006094422b18a1b6366c20357003b0618aa9031820530213839d5f3d2075a9b515172253a412b13942a0d054f9d93f1718b2d6d03d05211e20c5d9d6043e1d7276c1d739409d63e1eb9204182052a7403b2d5205c0218205070b85c501d2ac3f74a9f031aa9c345b85407021d763184042e730f43c46aa9761caaa256c0f5051aa9c2c3f815
    | 3 => 0xb5c40428521e330748f5256b1b5256e8f5631a2b12e4b905370205c021e04c396d8f527521e7396b0f50f3d8fc2c5cbb9330cbfd021804f346f8f4041e04f2808c42421a29e2a3105d3f589ea070183b022104c053e1da317aa0a0708c422a56056072104c31212b6070283b2b179080f40a152f5aab03e1f38f071d0543045ab0051704f156d9da6b4f9d7031704f25171df2a0285815182253533a0f021b84f316e8f42c018542b4504f2b62ab02f213832b5baad5b1e1e007028f53b5c2a9254fc2007018f51e199ba2c5c3b93533bed041704f2a0284d0f5c88e3151a1674181d62d6d29e890905b336a8f5061704f276c0f5394284c9c51bd15a1b9bd0f603d25d1804f07094520118203306e4492532860250b4743a3321507020f5396a8f5461820507030f53117ac6200084d106085c316ea0a804129e153f84d2b3e04f6b5c3b906222ad3b6e8f433051a60c00c1d021984d020083b2e6c0f5227d8f52c6e8f5041a854061d1085d1b84f071b37d052104f356e9b5031b84d031b885501caaa0719858071a04f294f85b19649e90602449145e85c3151860286b0f62c3b185941ba0d141abf707074053b5c3c0501cab12b17a46071a0b0670bbbc
    | 4 => 0x31748f53018ab7041e04c8d3e1d9041804f10411e9021a20f02011d9256b0f5031b84f1019a23031a854042104c051a8542b1821c07008f588091e9061f88c15313d2070303d062104c0701b0a750a2aa3543ba12f08c42050bbbc071e04d32172c610249f3061a20d65199d632518602f172c62b2121b041b84f2b3f04f3251c1e271e21c3930854071804cb418205050220a061b84f491d0542408c426032c49a81a29e254fcb69d5f3d15f0905b2b5f85c3e7403b1b00a042f6c83b3b212b42c028548b0b85c890b1e92b17054246c8f50208a15031984d011b84d051984db41a29e2b4284f271e20d051a211781e1e5245b3a1031a2112b7403b266a8f4246c83b075e29e880b4502d558630718aa9334284d3f74bb92c6e9d93118490245b2ad05794490f5b04f022104d060230a285205c3b418543541ba42c3dc33031b886ab18205367083b8a1704f050083d0419a042e500b2250945243182059d4fc208a0b85c011e04d051d054266e8f53f748f55b211e2356e8f53f58cb3ba1a29e044f9d7317b208303e2c804211e013182bf011804c074f9d9316bba18719a342f17ac08e5b1da7f19a15315f2d14218205031e085061820533301c5070203b
    | 5 => 0x311d2ba31460543334863894f9d72c5d2a905199d6365205c286b1b8286b0f4071bb11295dbd1025c3b98708c422419a340217854191b9df0517854275304c3151bd1051f054011984d305b0542b21ab16b0946c25348632c1f2ae3018abc26518514e1804f035c2052a34863387183b2c5caa93034ab1451a29e781b84d334084d6508a15021984c041785425348546609452041f0542431a082c430542b21ab03f74ba1256e8f43b3384f2a329e93c0ba23071704f07220544d1aa9c032104d210084c394504f6c0b85c4e1b84f942104f07010ab8809452281e9ed367d05d396a8f4b81a29e15761b504170541a1720c870740406170543f74beb394d04c3050aaa042104d1531c1c2c0ea7a317b205271ba0d2258c8e2f5e2b09d172c5062104d2c38047070083b2e4084c611a2b1630b1e93125aba041d1082a5b04f05020f42a6a8f5334e9850f5a9852a5084c3a5b854331b9ca0702449393e04f2a083e1055bba12c19a461243aaa045bba12d4f4125b1b84d5b4f9da070b3d2237b0f5041a20d24728f5501d0541c012b0611a2b0156d9d9070283d052104c31418543a5b054032104c89091e9011704f2a5485d07030f424700f5441a29e2716a9c
    | 6 => 0x11840463178549619a15ac1a29e2e3e04f7b4129e6531a08100105c012104d1b66a182262192070bbbc071a20d2301854022120f355d2a96932c49781caaa285bba70701082071b84f2349185271820f34412b063170542633a11304f2b00e4005e1d7e0f431172c40419bd90421ab1316e8f6513e1d9041f2ae061984c9b612050119a0402000f539213831440863275604f353384f051704d871984c021704f031704d0532c493b4f85b33308513543054240404c190084f0b5da150421ab0216682a0718203324fc2040753d25b1984d1f0084c3408a150621ab0345bba125540542b4820d15760f52551be62a700f51507bc76017054041704d103e1da394284f061704d395abee9119a15105b939070083d105b8fc394e84d255304d98184041f009d60c1744a2e6a8f55e08a15333105d333f04c071e0af283305e5b211e0165f05c2d71c492c5185d2b5aa9c011b84f323c0372800854154004906022088c0b85c0c1813d670b85c2724a0b02199d657633d13f58ab3072104d74011da31492ac1a7b0f4303e054031a43378211e2333e04f031c29c900b3d2941704f055cbb928211ed031a29e0408a15880905b051a29e285dbd1305b854276d8f5
    | 7 => 0x276c1d9050b85c160b3c7276e03b3d5880f011704d0a5cbcb1a7a0032a6b1b8271ba0b3f74a05021a20d2e313d1151093e3b1eabf3954054333e04d3a31bf1286b0ab360185b2a5304d996141d395304d913f2050702c49115d05b315185d10603d30c00c6c305cbb93a6c83b0319a0404000f510758f5167803d320381a2a17225b90945205443b905193c0151fac0256dc49357d05d286b0fa3017aba346c8f51418bc7041caaa3d73882890b3d2061caaa363d1850f603e607170542e083e21a7b03b25094662a708f52b6c0f5333f04f0d5e85d275304f941804f6a0740430182bf2e4e84d244f3cb28521e08a2120d63172d128728f52c5c2a9265c3b90c3f85e286b0fb0c2da9e335604d2b6c03d1c018543074c492704054021a29e360ba2305222343d3c0372a6fa050702a0583612051b25aa5334284f306e082051e211941b84f021e1e5880b3d26b01bb90431a08b71a29e5f16a9c881b84d156d9d72532c492a32c49334e84d236385d5a1804c78199e00c5e05b1a65091105f84d256c1b8355cbb9394284d3048ab12f6d8f415329e9071e04c07032051131c6c254f9d7255185d14789d90700882275d85b393105d271e20b231d2c824709da
    | _ => 0
  let q := fld packed 28 (i % 128)
  (prefixGates (q &&& 2047) <<< 24) ||| (thirdGate ((q >>> 11) &&& 511) <<< 12) ||| fourthGate (q >>> 20)
def finger7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x25698f89bcf4070d3d36c7596fb28e0c7437c12f475d8979ea77f90aa56350eb27065aad0495ff64fa38f29f3ca20318167db1495309004066dc5f8539d862e9248c56ae4144ca2248116e0264ae9476446c7f93b283e97a73a06b13fadd5b64c98fbc0f295ba378b02c93c3aaf1fa3bf01c26bdeb0f52cd11683a75a97fda5
    | 1 => 0x457d18adf1f432ec8270ecfc5634d746a8ce97372cbdacf2a078d4edca21de0dfc2e5bf5112426e9a00870243c8402c15a5d732775d54c8193d719b029da6d70d5efc5f3826f9834ee0d550fc56335547924b644e3329b2b66fc05d970076857b73cb91697327790d196bc3348fd7cc8ad5142d27b442360fc47af7b01b2df8b
    | 2 => 0x3160a66e39efb7384b7a7ccd4e6344acb88543503e6e242001deb087ad82c1ccfba7ca2c97f21891a9c437c9bd5db08a5c876c04dfbc480dd44d81e474e98d8c8296e84de96a864fbae1dc917ae9a56d9cd61ed7b22994269dc5c591442b5de62b36d0b8bfd157475b39db8e40bdb613b16e3c9fa16beac308aa28df36ae06ea
    | 3 => 0x66d5191477ce1b1708c6eb96dbaaa2f98cb7a00e8b30bfa690342c71f966d949ac55b9ec9e9d1efac6eea27416c4c1ab541fdd611e84fda7ad7ce32c49a61e5d654a6179636ab2cd1fe0d28dc528a911753219f94ab7bda41eada7e4d1a001abbbaf9035bec82e3e9db3b410aebe8579cd7bca108d7a1115d2f5ecc9ccddbdb3
    | 4 => 0x3cb5147e059ff8c5424b1ddeb0b7e292ea89abe3ca8fb76d1442c0050d97e8429dafcea0aa910e4d914fe8844d634bebc72cd6737ccbe780465f110f8d36910fb26bd7e80d0913a6a806d1a553d4c1ecbef710258127383e38417748e7746db41165b0d5cb7f91e1f1e2fc3c665225c27307281e94b1de88f96ee69781504c15
    | 5 => 0x8d9336868146787d61c7cb950cc3099ae08ca82b1bccfbb2794627603d088a5e076e4db84bebcd8c4f34d58eda7f951edea577dab1d2ae4778c60822d56dc15870ca48122c192a1acbc43160c76eecc9b4554bad21d95c0ed9d9379a3efbb57663b1870af04e960677d14a217847a617452be0871f061fe52f68a9c639f3b29e
    | 6 => 0x7e72c459784e7003910425d110121ef534b9beba5fe8a8a4f4de3ad97c5eb3fce7da47f1b2bdf9349a8b4d2fa3c758defc2e4e11b14080536286e1d085619af8e440749ef98987db168ff3a1953b2d436690bdb89f07d4ab2f5bb62058a8a15d306cc3eb8181cc8090a9e53660498fb70371956166a40bdfddaa97bec28b4a77
    | 7 => 0x1f0f25db593d2982cafe27fd714c327d6b9d211557e84a750d9b62423db26bc9071d861f4b071b66d3ceb74eb5d4919c6e1fb44351a15fcac54ca01d98f0c50a6893dd7fc777e8eaecc1143b35922054991e99cbda28c71771e66f65905058dc1e2985c9a92d3c619d663f76c1df5af8c1b88faca38d15d74e423792d5e99c73
    | _ => 0
  fld packed 8 (i % 128)
def recipe8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x28566f3a14f908038564b98564c6611cad112a51a2b07a8f7521e24f25805199633be609e700add2e0f5623d1039b5022a1603bc042b0314127b1d94e9851bb1f6ebeb5129c18aa95d9d63186009bf7042a862847330604c19034c4c040fe2ab0a2abeb51bd101c47748f5533a6708f53e85c6b83b6d83d024511a3f65495353c4e490540184c1e9ec172a450856039d70405d2c2081aa9c1aaa5202b75e3a35f05c518510420d4f9d97d0f417ac5211e22a29f4918533a0f280f401c12182051bb1d0204d02a150304d540545325a5e20f019e86088e3b036044861fac61720b0241e0244245847523bf2d8f72e44c1f4cb0425a759b563bd3020630183b4f2150284d779dc6d0f5423ee6a8f5429141b9e01c2222c1d9311c62c9d91d05412adf53309674731eabf7908244ab01a10429a9f6e8f4018511aaa62e9da17ac4
    | 1 => 0x53847202b43f20543054040671793c044533706774beb40858409e016ab0528604284d728f54e00d290f55320d038f5758f4043a36f1d95b04d760ab03b355d87b6b8f542049042d37f0f40390870aa12ea086b0f7040910083b02bd00104d0432a531e261060343a70284c043b80105b2b03b50b100408e42442024491ea1c0e459034430184f0b3d2020806f03b2d29f01bed4e84c2a0fa04108199e0789da640601bb1b2104f03adc3e1e94b1851b84d641e95f05d1ca1b024a2758f66ca08023eb432c767029332165429c7703d2e0f9039172d29e028400bbb14820f008581e88a040ff6c0f47d8f4008f55e85b7483b4c185024127b208030561d2ae1c1ee758f52b0f51e04d0405c042aa0185b051a2718f540a046c0f56e03b50a045d84c7403b809851804c5f2ac02260042b1452e0028545ebbe621e061c225304c
    | 2 => 0x21da202b829bb902bed633d23f04c3204918203629e70cc560e1f32293e1fac15c40451c427b0f635c426c9b52fab033bed2b8f5789d901bbc1984d64c6c4a18503063770f4041bd5b185024071bb271a2115205c6ea0a040850408c5084f0285b3385b60ae1131a117b160239f172c30a42a740ab0284f0ba2328a05211e020ac55f8115185d181a6541532903b778f502aab638602ea9e0105e3f85e1e4892a0f504215044124b98740863689a679a05251ca1c2a518a1d7f9d94e8af3f84d211bd1ca1e0e3c844854519c5019e306bd2222c8329e96204d0383b524660404d2883b5f9e2632ac1f08b02275041e85d2a95e2e0044af262b84c8473d4da53091202be1b0b15d05b613415e85c02bd25ec1203858011d66e082613d21b9de770f5021385613224a225caa9040600cc5724b831a95c204901704f7d0f90241f
    | 3 => 0x29aa0040c00441b3110b1705458c8e0285e37047608b51fac46d2052104d0913d4818560a167c29e021ea0cc581e222531e05880f66ae13305e011b83344247847040513341d5f412041155c2a945ac7041050404c5882c03c49042d27003b440545fadc02bd348116252e64fc1c25ac5012081d1081aa9d4dbd1540512d0f54f85b4c85d030f41f2c70429c093f62c0f53e2c82c8f50220519c160129c6204f17ac221ae75bba15d85b041221804f349073384f0404008416360635d8584eba6029d6202c3028421e9ed5e04f2104c0bbb2038f46308e7a9dc61860031b25d9850bbbc1a20d700f56ea052f9075205d38047011d9740f44084d021d61a8544f88e0449e3f208560582aa055aab0019da04054293eb288f503beb4f1e704056219a00b41c09466492ad5320f202bf0185434049521e05c85b781d95c84741957
    | 4 => 0x730f5789d7790f5172234004952c1d031e26c1d91704d768f51d2a6023be021b80084262185010f44c1923e04f6b0f4038f95208f0390b1eb1c678910405b2e8f55e2b05f0516141d1a2267c03b0946c58a180404f6c03d35897748f41d2a4600470430929b0a430925c04c4e84d3c1855e3bc2883d5b1d556103222c71a43323b7d0410b468474286711a0c0084f4f9d51a29e173a71020b42051199d6212046d03d1a20f4b9036fa082a2084185438a185f9e0179016d8f46c8f574a050240570a052b83d44908621904804f2aaa07a9d708a15011dc412114804d222ac030b7770f93d18531c05040585c205083de139ba7b0f5044047c83b5d90f5c3b90413802c49178547783d172c61f054348540104f6c0820cbfd1fa682d41e042d151860033bc32c1c0441f2c83b68113024662a03d7a1d75f85c4d9392a83b028f7
    | 5 => 0xe4a92449c3c0372a0fb301177f83b04462041ea189021ca1c6bba16f8fb182bb0bc83423ae4608002a11499860085618ab47f8f51cab01a20b6d9d75c0560c3db3605c773b90441c1b9f1779da45856460476800b1618d31bf104043799b5388670229f6b1b50405e3b8364d1857a8f551958531854310670aa03f9e323c3803a05760f544bc001b1107bc7492ac0343431a085506063c202a8ab041e33b18564c1f48117039090229e039035a1ac0404249aa95b854189df1d2a5460546141c4fa165b8473e04d5a858308514504c64c527a0f52aa9f4d04c18a1a630540446619a15040ae1984c041390699d5b05421ab10410902c4d2120d6404f749d94504f211ae7a4493184930854040863a1851d2bb781d76cbeb32c492983d02ba71f26d1d2b401a5a1d2ac21ab0293a1613d37b83b41091038fa3a0fd022186a8f7
    | 6 => 0x5f8584229f043f15d9921ba0d62bed0bc590908e6d9da0ebc6788f40915b7683b0084d029e031a035b04f3e88f1c22518ab803a0840a1503aa01b9b94229e051ac1fac30841e6005d7903b02ab06c1dc5ebd30381a350634187447884798f5010f57183b6b0f55d84d631e702b1125ac225ac0019d764863672e27983b028f603b11043f90386b74a9f58c7d7029f58ab301b2a3e1d96e9b51ea1a40c337303d49822701da0b85c7803d31a0458cb3172ad780f50285d2120f3f01c02a0d571086105d020f67029e4ec50030f6043c07b8f53f04f558630225a301082e83d7f03b0084c709dc012dc53ab1113ba63c1c22abe000f57c8f53e84c4f2b001c86549117c0f5041071e2237b03b1d2bf68260033be48985608511caaa7883b4284f383f91d2b85304f61205192b444bd816bce0205c4f1561b9e2043bc1cab13da9c
    | 7 => 0x249f43e2ad0fcb179beb013eb042a96c83b018f57a0033da045baad6385c02452672c5171f16a8f61e9ee022a97e0f42a03b2e0f40a19b01185280f50332a03a9f09452172c417aa30eac20420419b25020f50905b381ea030f5549147fc495b2ad51bcb4d1d63b9866c9da6ca0a709b50519b6682a5c9e301891710f52f8fc5ebd102b2a03a9e4685803b2a172a3198581a04f5f3d16e8f51d2c72e0f6523a633c426f8f532c50813ab54cb653a9c5d856043ee029e92a8f51fac21fac0039121a0b01ca2039486203f8749d75809151c1c22054199a70408b0444c3c98644aac321580fca5612080221418ab57383d6220d5f81b5485d0b222043a7251ef4d1930432c44aa91d2c95c1854084c2d0f4091e918abf7783b6d8f56105c0184d7083b45138021e05485c5e854560565c04f7720818404021fa27b8f53191468b8
    | _ => 0
  let q := fld packed 20 (i % 128)
  (prefixGates (q &&& 2047) <<< 12) ||| thirdGate (q >>> 11)
def finger8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x1edb3b36faf1f002d3631027d2357bf85e5b6b767161f390cc0c60d5aa29cc2b75d25111b92d8bdf4738b5e2aa6a88bb6285b8a29a674365066de2d6536b6ad9a1969b6ad4604c8938c797232604295d02469eb380ef9896500623e7452cabf8ea8e9697a995c9ac05f9f7d6916ef8c101aac2aa712a8037b4163bb2bf6f98a3
    | 1 => 0x742f183cf7ccd12aeb8c9cfc753eb511ded4970d484e5420f949c6de343c9f1a37c776f5b20ebd4bc6aa71af53cf284ccb5d2ceb40ba4cf413d424e50b65f43646d9c529ded8981c120ef93f50638c49b19191b5ba5af810505405cf3ae768d7129c46a5703217c44296bd94b0df82ef2d398e8846a023a0c4db23c35faad8e8
    | 2 => 0x31821455398e2c38b2ed35ca5cda9b043e84552b5abe5420be522fe6d4197214fb0c84cc499d5f759166734bc223ddc6dc076c169d035be143d7a05477ab41ee04ecb495180753c4c9566188c3e963a7a7decbd7b84dd426dd3d6fe1d62b1c94e368c99b57a1489d5b9d97ab05555d9d1a61911c02371e67257b137bbaae6d3c
    | 3 => 0x6f2c9033776adc595b733e968d6f0f1c6dd98a6b1df7b2a6738a252a1fed4cadf00422ec4447375c3841d3f647c4c1ab8dbb4f6501848ce3cd0fd9f6499ca05c19c86181646a6ffe895f6394f6fbd67903ea19a44a5be690a14fa7e4df6d0513b8af3dc6a7c899f89d20ecbbae54167ecd5dad0e8d7aaa5b1b138032fbac669d
    | 4 => 0xade1407564eb31942b76838b0d9a7926770c6e344434fe9ee6c1c139d9217426857dcaeaeaf6b6576029661d982199914dcd67309ace0a9c0af110f113f91c0c36bfe4b9387a503a8f687f801edf1f61c8508928127ed3e38c881dfd5d46d3bd2dc491b5c7f91e1f130053c4728347456d2c044b218cddc6b829b573ef49c15
    | 5 => 0xb4cfd23b2610d3fe619738a905c4d7ea204bfce2adccf6f563409a71d577049464c794bbdee17e8ce448230fbcdb0f9107eebeda908926a5f59408bd6b3768df14ef1412efc80ccab0be64f978f646e63a10e4e7813119287af0379b3e7d013463d82c0a866ade87e5c148e61156cee645e8fedf35f01fe5181c3b6f3966f5b5
    | 6 => 0xb72161878f01703bc1a799987658193c1efc6375f2bf232f4590ed94d5dcd58b74d43322f0ff91f12679f3002d758b8209e7f4a92a83dec328621d0fbad4ea3e70c74eff99287f8528fc90918ae2db44a4536cc2aa6790e073c9ed58dcce206176cee1da0062d0f0c8cf3210c33cac2034bf3e688920b5e92f684aa4bed4af6
    | 7 => 0xfd7b0c453186b8820669c05f49ef99c18c4508391b44675e7f1d6228663152d8071d911f6e0446515cd4b0df7dd84a71e41221172da1cd45ea4ca0552913833e5e8299afefe82cdc1ca8e7be3592c6ec0b8a5724da5a7161da06700d907cef419f9dc2418f10eae7d9cfbba922df4a9e21c6a11e73fc90113bdde4922fa46ba5
    | _ => 0
  fld packed 8 (i % 128)
def count (s : Nat) : Nat := if s = 7 ∨ s = 8 then 1024 else 0

def board : Nat → Nat → List Nat
  | 7, i => cpBoard (mask 154) inputs 4 (recipe7 i)
  | 8, i => cpBoard (mask 154) inputs 3 (recipe8 i)
  | _, _ => []
def atFinger (table : Nat → Nat) (ws : List Nat) : Option Nat :=
  let h := hk ws
  let i := h % 1024
  if table i == h / 1024 % 254 + 1 then some i else none

def lookup : Nat → List Nat → Option Nat
  | 7, ws => atFinger finger7 ws
  | 8, ws => atFinger finger8 ws
  | _, _ => none
def ck := checkpointCheck 154 scs count board lookup
def pan (s i : Nat) := ck s (board s i)
set_option maxHeartbeats 50000000 in
lemma block7_0 : span (pan 7) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_64 : span (pan 7) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_128 : span (pan 7) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_192 : span (pan 7) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_256 : span (pan 7) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_320 : span (pan 7) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_384 : span (pan 7) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_448 : span (pan 7) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_512 : span (pan 7) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_576 : span (pan 7) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_640 : span (pan 7) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_704 : span (pan 7) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_768 : span (pan 7) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_832 : span (pan 7) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_896 : span (pan 7) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_960 : span (pan 7) 64 960 = true := by decide +kernel
lemma good7 : span (pan 7) 1024 0 = true := by with_reducible exact (sj (sj (sj (sj block7_0 block7_64) (sj block7_128 block7_192)) (sj (sj block7_256 block7_320) (sj block7_384 block7_448))) (sj (sj (sj block7_512 block7_576) (sj block7_640 block7_704)) (sj (sj block7_768 block7_832) (sj block7_896 block7_960))))
set_option maxHeartbeats 50000000 in
lemma block8_0 : span (pan 8) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_64 : span (pan 8) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_128 : span (pan 8) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_192 : span (pan 8) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_256 : span (pan 8) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_320 : span (pan 8) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_384 : span (pan 8) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_448 : span (pan 8) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_512 : span (pan 8) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_576 : span (pan 8) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_640 : span (pan 8) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_704 : span (pan 8) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_768 : span (pan 8) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_832 : span (pan 8) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_896 : span (pan 8) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_960 : span (pan 8) 64 960 = true := by decide +kernel
lemma good8 : span (pan 8) 1024 0 = true := by with_reducible exact (sj (sj (sj (sj block8_0 block8_64) (sj block8_128 block8_192)) (sj (sj block8_256 block8_320) (sj block8_384 block8_448))) (sj (sj (sj block8_512 block8_576) (sj block8_640 block8_704)) (sj (sj block8_768 block8_832) (sj block8_896 block8_960))))
theorem closed : ∀ s i, i < count s → ck s (board s i) = true := by
  intro s i hi
  by_cases h7 : s=7
  · subst s
    exact spOK good7 i (Nat.zero_le _) hi
  by_cases h8 : s=8
  · subst s
    exact spOK good8 i (Nat.zero_le _) hi
  simp [count,h7,h8] at hi
def rho (ys : List Nat) : List Nat :=
  let a := fld 0xa1c3269301086009430000c2b222cc10001411c7140c2088 3 (bsr 0xfc4b4dc4f92dd3dff61fed3ff211aca1e747446fe5011aebe0c65e1ee0bec9a5dd5f2d6bd98f9235d6b3f50ed4374c98d2d8af1ecfd00ed3cd66fd69c8b4a9cdc5c11f1dbe262fe8bd9611c6ba26cfbeb6dee1a3ab7077f8a746b738a4ed92aba25f850ca21c1a76a06890169d0dc8ed9bfe408f9a3d9b8f93f46c539100bc9787315ce181ddfa1c7a807146735658f171e68e7f6606a67d62f503dc626c705560bc372c5e96bbfb5d5c0b5a5c2e1b595bf34bc35b35d66658b7e884572aefb653f30f574f30a7ce4e426725445164e537c9eea53440a5903382a54727ac431823b384ef1e3d14911c63350c17d8839c13487c1407fc126d07c8c95c072bcecb 32 (hk ys) 7 0 64)
  if a=0 || 6<a then [] else
    let c := fld 0x5ce2223b9031ea81d5c4439aa06e8d1000000 21 a
    vals.map (fun v => fld 0xfe0000000f10000000ed0000000e00000000dc00001b2b3000000120000000114004c25e8d0031618890047e3c7c002ca167800442147584a84ce650000000ea0000000df003e9f2580030dac54003a5d047002c1aa430036da84069a8064300000000b6002b800a5002fd8e2d5f07d3a1d002ad681a55031380a0027d36084d0100000 9 (orbitLabel c v))
def B (i : Nat) := mv (mask 154) (fld 0x102f10000502400501e50f23402f31e23106e20e53f53f43101e43506e30403f20e10f30 12 i) inputs
def I (ys : List Nat) := bsr 0xf92dd3dfd4374c98d2d8af1ec8b4a9cdbe262fe8bd9611c6ba26cfbea746b738a25f850ca21c1a76a06890169d0dc8ed9bfe408f93f46c5360bc372c5d5c0b5a5c2e1b595bf34bc35b35d66653f30f5723b384ef1c63350c13487c14072bcecb 32 (hk ys) 5 0 24
set_option maxRecDepth 10000 in
lemma roof : bar 154 (cutB 10 inputs B) (cutN 10 24) (fun _ => I) (rowOrient 154 rho) scs 11 0 = true := by decide +kernel
def nextRecipe (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0xf322900154a0de605728378109480de035f201390222031b213f28c5c862a011f738fb947dd63ee31f748fb84501e20011f248a80c540d3c471f238f90c7c823ce51f434731c398c5cc31f407f31479d23c4911048a824441a2a0d11028a813b98c1cc31f501f311b98e3ceade638f98c7cc228071e738f21c7c417cc31e712f39339863c464e610f30ab88e3ca714008f381a980dcc0ae605d302f9823c804a6027302b8c23ca11e3033021b81034804e300f204a80434612e01a30853840dc06be302f08158409ca01e30
    | 1 => 0x2732104108a084105228293c8c1c423e022529139489c844f3127981100c9c864f102728939048a0e4107273191000b4805e4067180180c1c0611020b9085cc02ee015000800054083ec81f540f9a07cc43e60140308818540c3e840e310fa0050103ca81e340f9087c403c62150708838790428000a6007301f94d4ea0962152802bdd874c0af265282278855ec8af634730abd955ec0a40657a88b9915ea0a405573b2b995420aa5055081294095e280e621f301b9855ce2ae5157a1abcc14806ae635729979d5420e4e62
    | 2 => 0x6281b0414aa0cc5052a83b1419820c5f5367a10141c020e5f5067a00d41c620e5e653083979159c685f32679097cc19e40540362011790d9c645f2067881500988025e42588395000a2025a302f1833881d4c0ee602d38179c19cc14604bf01d3810b4a05e50672016880bc40ce10a3015f8069c04e6037701da902dc8096034f0190404144241032398104080c42474023a811dc08a004f761b0113d949ec84501228193d888a044f6327b093d80880c4e7627a993d0c9ea24f5227a813d50880a4f42172093d0088084e54
    | 3 => 0x15109f8856e60bb621310add416ee0bf7658002fd896a00b5015a81a794d7ec6bf615fb02d0197cecbf234729afc905c42bf205f312c4096a04bf430720afd007c846e535f122fcc57e60b4035b11af88d7e20b400288130404a20671062b8815c4cae2e57152b8915c50be205f132f8b97c54be245f142a8014000bee8cf632a8131404aa06c5022fbaa441cbee6cf622fb933d84bee0cf602a03b101980005e172b0b97d0d9e645f40679817d95020e5f45679a0941c420e5404620197850ac285e7467319441182065504
    | 4 => 0x6faa37c91bea68e516fa937d41a80adf21171237c81bca4de62688135409be28df04072137c0c7c806e516a001a940dca0de509d904bc493e876500b79823d0e1e862f317f995840e9e656f40778983cc47e646f436fa1d9001766091004a80588c2d4616630b71816cc096611b3013018b80e0c090e04430223810b640ab303a00cfdd80c033f639a804900928073f629fb04d01a7ced3f324201c100c4802f4029f31cc40e6a06e40302008d008c806d4039f904d00a68007e0193014b8090c068e038301c380c4442b101
    | 5 => 0x7aa03d081e8204040082014101e060f23020019c0c04a00a500328039417680d703052003900b6a01b408da80fdd80c043f651fb20d4086a063f601fb18fd88680c3f531fa18fd487ea03f541a028fd004808340418820d4107e0604021a00498125c08632133a819c90ce42672533b81bdd874a06f65328199410dec26f6032801bd90dec66406373b1bd50de426f5137a80b950c80a610532829bc50de080e5237818f940c8002604170236c85ae42df761d2037d95bec4d5036a8227945bec0d5006fb237d8da80cde76
    | 6 => 0x7a81a5015080aff0412013d0010c0a8e059301cb80d2c0c9e064b02a781514c08e6085304398054c02e60a38251c0a8e2151029081a4415020b0102108153c41e20125034a82a14160a0425027a805fc0e9e097f01a78150406880021001280404020a008100428001c0ddeec370377b2bbd91dec0e5037280a7c51dec6e50077a83bd45de80ef41478a3bd51de842f43720238411ca08ef03720019c11ae08ea5077283a901dc800f76000003d941ec8050107b00140c1ec40f63028003d841ea60f4307a003d401ea20f52
    | 7 => 0x50800440082011b700100a2d812e0b2703588002d824e0d270293824bc04ea012f0392814bc1a5e052f04920027dd876c09f064f9327c153e0695044a001ad81b6c161006880184000200bb60708016dc096c12606970321c11d68027032da002d010e0a0b5047bb0ed411ec08503428223d851e088f054781a100096a0db5055b043dd876810f6587b043d8a0a0705044fa8c3c121e070f5047a8c3d4a08006b508528439405eec200017b00bd884a02250317b20bc0c5e462f0417aa0bc9048004b400d982ad4236802602
    | 8 => 0x710105a898c0cd6072b013fb29c000fea47f023a809fc14fe027f033a001fd4e56c27f513a029f814fccb2b313fa19fc8c420674023f011f948e20475027080bad44c608010318819f80cc2086b043f11c9c4ad664e713599810cc1d6840b420391c2d8a16a46350139189c908680133051a821c8c86a0b3504b9325c8cc6e0437059b804dc0b6211100
    | _ => 0
  fld v 17 (i % 96)
def C (i : Nat) :=
  let d := nextRecipe i
  mv (mask 154) (d % 4096) (B (d/4096))
def nextCodes (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0x5355e2edb00008db4409150dc5102390951c000ebdf78d0d931755a2cce0f48a0511b1afa20000b1d11080008cc80e9cbc27a74250134800001faa87aeedd922117fa32e1ce8f1f08ea7f4000f6af28ec6674cd733a2c708000d9dc189f9c000efa1b58caa5560006c63108000000936dae8b5be21989f4b8a20bd508c80013f85f70e179b8000000b9812f0001ba441308e54383557d59d300007c3
    | 1 => 0xd0ea5979d207c0007d605da7923fc66e40013afa1d6f44001bbc9de80017b539ac268f50869c188bbbfd387220900074b38b2a82976011f9f89c91880003e0a3e5bdb000000164a78d52f00004b1259af0e16546c00053f4001a91326e3537e37a00007d9000020bda109a406a2b903780010235f300066589a524907a9d75004f890961b10000000f3eb5b0000373000219d29174168b99bc108000
    | 2 => 0x8dfeaed4da7aee13253ae8c0000441d9985256d107000000000072926f8b7a00000026b26e56921358002b50387103a2c8000120ee562e2ef266687d16595984fbdc70001f300005c40f5c7811690005aec4a0000f34fa721ffa9200027cb013092e3400000009be110840b8c8050335ff598866f11b82845734000720614db121df75700037ec000d6c60b0001247435b74c12e6340000001d2737e
    | 3 => 0x3ccc7513d187ed6a0218afcf7626b02bc00310ce8d80014cb77427c3f562280006c060266de0503d986a67d300061112764ce0000ddc0010b10ff000000143feeb27efcba2a037dd920000d210c9dcbd99d35f58e8468c781a9c47360572732aa7f8df8001af2f498001272f330007fd01d90bed4f316fba2725000129074403302c80038bd9a3000236a121281c24a9a58a0e29263c78e2bc946
    | 4 => 0xf70b9171a1cb100000023033937d6014800199c7f58000001e438b5d9c436e38aa9b6e642be00000052bd6bdab900000010873b649880000010694b06bfc001aa5219d7fbdc21910001ce771a19cfbe0db71101d80000001830c6800035d4000376dca59e019d930a9dd2dd936000411000024735100004cd2f0fcb000543800115d0870000000558de7e2f40017767e2e21896eaa100045e63d2000
    | 5 => 0x3bef0a80017dd3891434fc000096d29d3d500009268002889aa8000545e7fc00000016e1f421da17e0634ebf023da2093ec8a4db46b4efc0004c7f7c8e18148d4fcac5ce78785e9ad880003f000000000025e600012f93223031524a992ec5eeda4650c103f55aab00006a400006072b41e0dba0dee4e712c0012c21a07c0dc42c546638948b356ce0f3c96020679200004908c8259c08d7fc4e2000
    | 6 => 0xf850a4eb2a0000000003100000f3b2929b90000b6dc968001acd0001ece18121e000771d9974d4a0a80031f928065460a0500ca4b2338385a42030587f29cca8bc2c52cfc00009afd112b239b422e5535200000000007378001f2b0001b2400053b4873c06e0cb11253871051501ae596ea8000cf03ab6b61aa30dc4c58e5d37802b2cb81112fa0000003541c56cab0000001286ce0d705da38e1fb7
    | 7 => 0xbc60a7c02297d0001c86f5e71ec00dba572e5d756b43276ffe9300000001e17640000b649a4391000000000000000044901299b04e081ee1fcea3155823c000898523f42d5eaf125f4e0eaa8f398e4bcaa3c46000cfbbd791bd0467670001f68cc326114740006006ddb4f35450863a07d640000009ca84b4c5bca40d501fccf56122eaec54000fdf30748739f84ac67600022560d864d2fbfe6b0e8
    | 8 => 0x6d608cbc918f57ba0000aaa0004e8800000050a61360840012bedc3800287a9e11260000e79c93f1754e100c41ac14912823e669ca0bda8001605b670000000000000566bbae00005f56c4304add000689c0019160005094000000e018a4e79e0594540003fdf092d748003bc596c00000023d400090c0c46a019d15153c7c9c6ef58a8694e8609919da291e2739810f1cb841fbbe4000620b4661ab
    | 9 => 0x86b87449f8b510002420e56000b5000012d8682a19c8300c2399f7ee97273738f00000028876981cb63c8001475cb40ab21e60000001ec7d1d4a40000002667b2e6da8fa57da89fcc683d5651f0f000000271600077096d78c425726100000017930005b0400006f8bc0001dae872703a428db01210003f9531f1b900001498ce0e58198e4834fbad52d00030fc00031883302f61262c92b7c00121d
    | 10 => 0x228003a61fca7f4244c00061d1766a4f965b530000003bf3268c4433fc000563a2c424000089ab289a28aadd2900057d08900002fdbf76ac412b000000049c5810003e455e7a78d13e419b280009163584000ab54777d82632996dbd0001b77996aa13b2d5100000000002248f003795ce4000571089a8540ca3f0612800101eac60002c883d353ac36ac9cbf2374f780003ce8ba762e08b4f1f2f2
    | 11 => 0x250001a6285d2d247f8c802fd82e1103cf045fe381930000d1600018ceaf5885c6c0c984061c762e3c9bf85a9b4c780005fe0005c0593d1b438dd1d36d075d068b486f953c0000ad11e38001d2ce3fc311dbc3ad0000413c149f10d44738db782ba468b172b7b53aac8b141095595ec8003abfa8770b0dc627400000047700004913a12fd4000a9926dde0c00184600061a89a23bc532b9e8b64d2e
    | 12 => 0xcad09235c812106789a4000f619e3cc21708dd295dcac4001773bea13fbb990945150000b08000b700c2e3ad21b7760abc86822e7930002c03b0da7ca56a76b673022f7716840cf518c6d07f604c1088c800000800a3f2dca9412008f024b0220a59a2095495e005000429c000000a2a0003610c900000399bebe104e7b503a5751367d3f8404e000b8826d455a000171476cf72d45a388c2f48513c
    | 13 => 0xc4fed483ff591000000189021f31339d853466314b000126370f2042157656ca300033920ce8df77d18d4d8555959d8003bb823201288ec964000477b9cb1965cfcd2cb300013cd0002095400e1daba0002edb9e8227b6c9fe40002e1800093192388046f6533fe70000002c0039f200a79d2db38f0001f7521c000000249253f9fa5e120f05913e3000363c00166a000059a7548eb07854bdfd2000
    | 14 => 0x395c000ce500025b8d60000061b2f48b18bcbba4f13f55c4d00066a0fba2a0880c62e730ff47fe4d2e4807a9952baa4e240008d99d8da9d9d7f6b8aca1f600000008acb46000cddb6fc001787a7bb2cf6be0002360bfded3d2600064bd59bb290005cb45490ececac5b1d99aee00003a0001d440005b731830c10005728000deb7e6e7f80006dd0002ee5083eb3c5bbcbc00119e2a9000096c000
    | 15 => 0xcd63fb53e32880001a9d3571de0d28b336ca000af61d7d68000031f068232c000e40333b9d1e823409dde94e0005f10000001dd10a58001fc74bf595000096e233c3a07c7f64ca4a393ba800000077c5f940000000004a351a837e8cd00d70e50760eaa6d000187700061790d2b6b4e7000100610e0000000d1c00013b9b91e0400021600020a80000c744bc846d3648c00029abaf8a1c00030aae48
    | 16 => 0xa87d7e05dbc4800043287afd878ac080c0019b428ff1ed82400001a8000001194b5cacf1dbeece7f600030ee06d4300001beb10d36ed15400003144402de047eb6e9e8ec0987897eaf849beb41a600000023982ed0003b4c0fb88a37ede877dabc170ca099f45c12000337c001c76e05b832b6c7558fb80000000000003157a48230c360eb61c322441a94e87a928654dbcbf4e299b9db345c001357
    | 17 => 0x9b94300000000002170cadf784bd51f77b684da3f8001ff54ddbf6e63400000024a5f21b70b020007d98000e198c78f6e16b1220006ab8729b997b900035d90b1c8d086f7a600000057a1467d2c08682c1efb46f05b03503463720391ccdc741612df92102be31447821c9b31f2defa9b5800156bd7d8000562e690000001e3211c70c87e80000000000001dcb79e8378002d680f201db310000d5c
    | 18 => 0x700cb5c000a5466298decb002a7c777dbc4058100039cd9cc00022ca9accda0f900002b00f12cb0001da413c2564f7425b55200079900026759870002b37938fb504adf443a76570006234c4073598857860161de0003eff3296fa0005c6c471111972fdd40008be04b1966980ebb3643eb881c000bdaa11596e0006268f740000003711fcda3a0000000003d9d3a2dce21d914f73003c5ed09092b9
    | 19 => 0x7e5837002b7fd67aab67ce1000199fb22000ab48420ef0bc400000000f40009a640987b45243c0b6c9655d4d1b39d30d75c4da1a21d00001cd0dd80010600001d8c50b6ea727032d040001a79a565ed41a6fc50bff4314b618d382ab041ea3cd3529851281cc10007bec00143d0004459222237b442db46e800002f11d2b17c7200000017b00009cecd55a80ea3c1459d8000f8682fb7dd367b1d
    | 20 => 0x4351810ce253faa40002c60d66000362fb033de0006e0358a70a1a2800262bb0cd66300e0f20000005e30a8e42326e0bf96ba9240003a20000089b9b6d5e25a45815897e46d510f2db8002f630f00005895dbc7952cf5c059d9cf2b77e25e182000ee3bcbcf0a44d00014f3cb380055ddfe6bc6ef5ac53450000000a96ef8fe98000d1406e547e2bd29300029b94f40002c0394e0000004af4aa91cf
    | 21 => 0x846015f335ab40005d4c43551f0003b3d128aea34f177800027602e843171293f00036e66ca1650002f0ea3e7b2dc6a7b800015be232a90000000f488cba2052094678dec4ee00079812d8000000fc198ba7ea314b1c0814000389fd590af4b89911398000925bb1e18d02d653b0a7360002aeca3d024417b583c161724ba59052285ccc8d20b2f4308415d1c0dd8d00037a40011434ed00008acf21
    | 22 => 0x10d8000000888d149bcc00023b74e000029c0003c500023e7fec0002bfa5574db0964add7f231b45bc7961600000c65c87608f5d038813415466388d8002c11e7e00072a649801bbe38001c4000012c0a380000005e625390ee532898366f6160006f81e21c14849cbca042973a50a3680000009fabbc7c5c0000007e29699f5a4234e583c400066dea1a75bc5e3adaef8000000000d6ab81df2f89e
    | _ => 0
  fld v 13 (i % 96)
def action2 (ys : List Nat) := orbitLookup nextCodes 0 736 (hk ys)
def rho2 (ys : List Nat) : List Nat :=
  let a := action2 ys/833
  if a=0 then [] else
    let c := fld 0x72e40c77205cd5031ea81b9c446ae222e8d11ac688 21 a
    vals.map (fun v => fld 0x133000000126000000122000000115000000111000021d32000000131000000125004c25e9900492468c0047e3c880044e247b004421e7784cb8e8660000000fb0000000f0003e9f264003bddc57003a5d05300379ba460036db44269cb47e310000000c900304012c003218e2f5f0b2561e002d5681c55066540b004a650099381c0600 9 (orbitLabel c v))
def J (ys : List Nat) := action2 ys % 833
def r2 (i : Nat) := bar 154 (cutB 9 (B i) C) (cutN 9 833) (fun _ => J) (rowOrient 154 rho2) [] 10 0
set_option maxRecDepth 10000 in
lemma roofPart0 : span r2 1 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart1 : span r2 1 1 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart2 : span r2 1 2 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart3 : span r2 1 3 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart4 : span r2 1 4 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart5 : span r2 1 5 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart6 : span r2 1 6 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart7 : span r2 1 7 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart8 : span r2 1 8 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart9 : span r2 1 9 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart10 : span r2 1 10 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart11 : span r2 1 11 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart12 : span r2 1 12 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart13 : span r2 1 13 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart14 : span r2 1 14 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart15 : span r2 1 15 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart16 : span r2 1 16 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart17 : span r2 1 17 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart18 : span r2 1 18 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart19 : span r2 1 19 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart20 : span r2 1 20 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart21 : span r2 1 21 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart22 : span r2 1 22 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart23 : span r2 1 23 = true := by decide +kernel
lemma secondRoofOK : span r2 24 0 = true := by with_reducible exact (sj (sj (sj (sj roofPart0 (sj roofPart1 roofPart2)) (sj roofPart3 (sj roofPart4 roofPart5))) (sj (sj roofPart6 (sj roofPart7 roofPart8)) (sj roofPart9 (sj roofPart10 roofPart11)))) (sj (sj (sj roofPart12 (sj roofPart13 roofPart14)) (sj roofPart15 (sj roofPart16 roofPart17))) (sj (sj roofPart18 (sj roofPart19 roofPart20)) (sj roofPart21 (sj roofPart22 roofPart23)))))
def t2 (i : Nat) := ck 9 (C i)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart0 : span t2 83 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart83 : span t2 77 83 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart160 : span t2 28 160 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart188 : span t2 38 188 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart226 : span t2 37 226 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart263 : span t2 44 263 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart307 : span t2 40 307 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart347 : span t2 31 347 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart378 : span t2 10 378 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart388 : span t2 45 388 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart433 : span t2 25 433 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart458 : span t2 65 458 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart523 : span t2 34 523 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart557 : span t2 15 557 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart572 : span t2 72 572 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart644 : span t2 65 644 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart709 : span t2 50 709 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart759 : span t2 17 759 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart776 : span t2 10 776 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart786 : span t2 13 786 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart799 : span t2 25 799 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart824 : span t2 9 824 = true := by decide +kernel
lemma secondTestOK : span t2 833 0 = true := by with_reducible exact (sj (sj (sj (sj leafPart0 leafPart83) (sj leafPart160 (sj leafPart188 leafPart226))) (sj (sj leafPart263 (sj leafPart307 leafPart347)) (sj leafPart378 (sj leafPart388 leafPart433)))) (sj (sj (sj leafPart458 leafPart523) (sj leafPart557 (sj leafPart572 leafPart644))) (sj (sj leafPart709 (sj leafPart759 leafPart776)) (sj leafPart786 (sj leafPart799 leafPart824)))))
lemma upperDead (i : Nat) (hi : i < 24) : ¬NatRun (mask 154) (goal 154) 10 (B i) :=
  symCutRoot (ori_ok rho2) (spOK secondRoofOK i (Nat.zero_le _) hi)
    (fun j hj => checkpointCheck_sound closed (spOK secondTestOK j (Nat.zero_le _) hj))
theorem finChk : ¬NatRun (mask 154) (goal 154) 11 inputs :=
  symCutRoot (ori_ok rho) roof upperDead

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 12 ≤ t := by
  refine proveAtCap 7 154 11 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row27

namespace Row28
def vals : List ℕ := [1,1,1,1,2,2,2,4,4,8,8,8,10,10,10,10,10,10,10,10,10,10,10,10,10,10,12,12,12,12,16,16,18,18,18,18,20,20,20,32,32,33,33,33,33,33,33,33,33,33,33,33,33,33,33,36,36,36,40,40,40,40,44,44,44,44,44,44,44,44,44,44,44,44,44,48,48,48,48,52,52,52,52,52,52,52,52,52,52,52,52,52,64,64,65,65,65,65,65,65,65,65,65,65,65,65,65,65,66,66,66,66,68,68,68,68,80,80,80,82,82,82,82,82,82,82,82,82,82,82,82,82,84,84,84,84,84,84,84,84,84,84,84,84,84,3,5,9,17,3,6,34,5,6,9,24,72,3,5,6,9,11,14,17,24,26,34,42,72,74,96,13,14,28,76,17,24,19,22,26,50,21,22,28,34,96,3,5,6,9,17,24,34,35,37,41,49,72,96,97,37,38,100,41,42,56,104,3,5,6,9,17,24,34,45,46,60,72,96,108,49,50,56,112,3,5,6,9,17,24,34,53,54,60,72,96,116,72,96,3,5,6,9,17,24,34,67,69,72,73,81,96,97,67,70,74,98,69,70,76,100,81,88,112,3,5,6,9,17,24,34,72,83,86,90,96,114,3,5,6,9,17,24,34,72,85,86,92,96,116]
def inputs : List ℕ := [0x23611b2236cd809b104d899e6c22880b653e000000000fffc0000000007ffe000000000f,0x48b74505e062814520a29203155e12e6a2e2000fff80f000000000000000000f03fff070,0x2e0c2061e4083138609c3070418e47804c345fff0000f00000fff87ffc38000703c000180,0x9504a848831426284bd47828a0897bb71c08000000000000000007fffc0000003ffffe00,0x2e61730e0041813b0f1182010c0ffa0380811fffffff000000ffff8000000007fc0000000,0x30818409118205bc0fde07fdf031004c000800000000000000fffffffffffff8000000000,0x3f01f80ffffc07c008e0044e0020047001001fffffffffffff00000000000000000000000]
def scs : List ℕ := [0x13c290f89b24c94,0x210771789224496,0x1dc290309c25caa,0x1780c1dc9b25093,0x1780c0a4aa24c9c,0x1dc5e2109624891,0x1783e0309624492,0x13c0c1789c2509b,0xa40c178aa24497,0x1dc0c0a49424c9b,0xf80c0a49724896,0x1783e1dc9b24493,0x1783e13caa26c93,0xa40c13c9b25093,0x1dc29210aa25897,0x1783e13caa26c9c]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)
def recipe7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x2802bfc2a5b04f393786584198572f124fc2b5f9282b3d85007074050701aeb2c43050335604e275d85b256e8f52281cba2f58865a61822a612185336590573533a0f0321850995f22b3e611287a3f2052456850061a04f8c1c2293a3305e910f4fe2f728f52b6037f07008b935592f62a708f5061d928395304e2b60389271e20d234606511424781d040675c0739d395085621674c71a62a1502010f5061b84f2d39067296b8f5271ba0e2f543cf8419af22f08a151343065051804c2b17a463e0238d32523d6022104c27508563b338622b6b205240404f03198572916a0226320552f1a300901e850245b3a12c6e8f52343865273e04f070203a304f85b84168572f5ba343c56be103008f5071c050255604f040145d03000f5b11820590168508a1ba0e0a5c85b1863c1d3e60b7f071804c2d5f928021a04f061c050240404c3f749b42b700f426543cf2a5304c346f8f4186385f396a8f5865f4ba061804c361b38c1a63864316e8f7071984c3235bf2395084c2b4804f031e20d991a38b256b0f5045bba13e1f3946b0905b051e1fa395304c2831bf1387183a070283a0c2c206051d85522664a084210572e6b03ab31822a393f05707031b62f3a92c
    | 1 => 0x2e700f52801050051985800000f503168500e1da523b6e9b8256d8f5836120a02168570719a151a7b208041b84f2a53853030103c3942a0e031a2292b3f04f326f205050220507183f4031a850051904e2d7403a9912c9d021e04c333e04f2a3d857237c03e1c65065190d141061e850301890b2d60928890905b3942a0407198582b7403c2e3f04f2c6c9b82431a083151af925560582b5323e295785a051820d271823e2e3d857070103c061985824700f5071904e395084f256d83a296f03a04018f53f74bcd041c0502e4d04635320552716850040103c2241c9865198572d5fb89141bb03336a8f5041804c2347067061904e041f2342a6da2a31710f4052104c071820d2c6c83e395385031388482a104828731a06227e2eb935c205051a2113a7003c0418a2715760f53d2c85b061e04c4e2121007018f5135a9850701aee236084807028b93e7403c3334864041e20e3d5f38b2a5085634430508a16850040740505018f50216a043058aea051a04f070d4b5295e41d030a405b2182051542062361ab8b30124fb254d04f2a172252e5a850314812825508562c432360219858062104c07208780401bcd2f39cf70702c5d396d83a2b18a1b285b3f4
    | 2 => 0x2e53850334b98506198578a1e23e263384f9812c98395385307000f52a5485d071b857237b8f528700f43f748f5031a20d5a1bbd00b3f3f4254d056a91822a135e85d2d01aca266c806244d046061b85704172e90602b0a0701bfc123f85e0c5e05b020103c02218502e6249a31519c53d5f37c110205a943f208031822a941704f2716a542c5f928031ba0d2c45a39051e04c1b614f72d16a5227560568819a15441822a071ba0e15424405f1c05002602ef3a3f8502f6b83a411822a071685722444a32b42a3e155d05b2e5304e071b2ca1c43aef2a4b8462c1f248115d05b0321853051aa395d1ba3e0219857282523203018f53a6c8f5021885061013a12c2524f0f5b04f2e4d04c230e4aa050203c2e124fc2a70a2a690a43f071f877051822a33590673f7483c236385d2f74a2a042104c255325a395325b02000f50317204156085b3734c7719758f42f19b00461822a3063388062132b072104f04212e9316ea09031a20e3055aeb126105e930f4fe387183c871984c2a700f52b5fb892a40857031e850286c8f5660905b04183f41a014d40301aeb2c4f0ad2f124dc3162a1523478463612b062b4820e15031280431a08021ba0e2e749b5272123e
    | 3 => 0xa3e05dac1822a4c5c2051c01050941b84f396a8f42c48850231f94e210a18c0116850326f3cd2d7403c171720b276c0f53039cf7343f8500723b7c0c5d85b4b183f40218205275db7c326f03e2f5b47e245304e256c1b52e378657a19a152a6fa2a2f5bba107030f53b6e8f5275a85023030671b65065346c8f5070a4052e6c03c07010946c1cb89270084f05218502e300484e1b84f2d6d03c254b8466619858620905b296f03c2700a3e0508a15246c8f543182052e3f04c2c3f850025c2053f58ad5254ea2727560579619a151c650572a50858274b846326f3eb3a37868316ea0504010f53f1c39c2c6c8f5031a23e255605607199b12d611283512cf92f74bcd1831118302caed0e5dbca2a02858052104fa01822a300913d2343c7e11031282f748f524104c42c1e2451f0084c0518850306249a05182ea9612867271e23e2b03050041985807010f594104c3260913d220106731738f53e01128b41822a05000f53541a343a720fa0318a284a1822a1c652f205010f52244067301f398253484a2a7403c07198572f1a10a3459067181fcac353384f285b3a103210576c1a38b35024480718850334284f031e0980301bfc062104f4e1e20e2d24b84
    | 4 => 0x367083a2a709b62c380693533a0e051e850010083a5d1704f2d01acb266a83a06020f53334862316ebeb062120e275304f2757859377103c377403a0b03128661b8572633a0e05168503f030a42b17a422d0ecd41931c7e07230cb32521c68c1ba273039cf52e748f52451050275fa0e3262c9a3616b041c02afb255304f39700f5116105e071e85006073f4071823e371815e041a8503c020cb9355aeb304e04802008f52a3f04c07171b10321ad012408629912867071b2cb2d1aad80716850377403c1c444a2071aa362f7483e2b3e04f0317a29072104c2d7403e6616857394b846661baf262602ef06168502732c6702218530e1d437071a8501544065916249a03010f5051cb8a3f74bfc1644865871e04c5f0905b305889caf1822aba1822a393d85727212102e3e04f310ba4e071c1280c3e9ff061a8500519857051f2343e601280401aef36614ab1a6305b92210579208a151b460657419a15021804f3a45850373c1859612c9d2b6c1b62a0304c3274bcd0517a34266a8f76a31a0807028f52c609282a5084c2302867031820504000f506018f4395a850393f04f3062c9a2c48a3697128671864c6a06028f5394d04f2e3105d011820339429b1
    | 5 => 0x3258c7e3f58865041804f24378682e7483e9712c9d06204a43524b043f031282f31a06013a12c05210572243aea07028f49a12867073f205030103a2753853041e850901b38b394523e2d01128031c05018181bb901ba3e2431a0602211bd2b4284f12412350702a2a2346af4220084c255084f071b9280416850334284c2404057985c85b3e5f928317b20a0f21222231bb9b272120d1540864a11822a35592f25f21850050bcb764181b1031984c393f04c0218057290105a2346857334d04f2346af5356e8f532748f54118205070a43f357303e2f1a2e4051aa3b040103a281c236271704f93183f425348642b0ecd42a3f0572f3305e2e3485f2f31bf16531a08394504f326f22b935c22a3162c9a9a1c928315dc7e61182ea335a850336d8f504018f42c45a360521853227daee27700f52b6c03c326f0f505020f5361bb04313f0552d718f5300f2fb2450858354110a336c0f52c45850367083c8a1704f6e124b931578598d3d9b42d5586210758f5451822a1b612195e1e850041aa3b394d0562b4520e1a2ca2a8d0ecd42b5a8507619a15051804f5a1b84c05602ef07124f23b5185b66198570501206051a85007020f5377120a0516b122e58868
    | 6 => 0x25532cf2d7422a271ba3e01168573258c7d360185b2f6d8f5316e8f52d6d03e276223e5f1e8501c43aeb100285b330204f2d6012803013eb6c37c7e2b4523e333f04c226605b042105790188502a3105d2a56056880905b22664005f168508301aeb361b38b7841b81020103a396b03a377103e2c6ca092c730f5334084c9812c9d393e04f32481282b50a3e04182057e1c1283b1636902013eb2f74aec2d1d15f0712c9d3d73a0603211b105212103533bed01008f5032104c3202055633fa2d5a211bf04211be333484a0321a7d186405e256c0f525040530518057325584a24538532a6b0f5071d928326f0936c10482276d83a316e9b73e619283058868256b03a0618205050905b8301aef5117463030905b051d9283559441237c83a8d19a153e613ec031a04f2a4d04c2a030570518205942132a336d83a2753850356d0f501000f523491852a6d83a3a51050275304c071b05a071d85507218502e6a8f5071e04f30748f53f74c5d256d9b6230084c8f1eb965d1b84f3151a16070905b031b84f2b6c03e060283e2f104e2011b9b103211bf051832a5a1984c071a23e0e408640702a063074bcd060905b3d800621a7b20622674b53559057361a38c
    | 7 => 0x333105d365005d2b6c0f50c3f85e0316857394284fac182053a4305061212ea23010501024b0337710f431748f526763a1021822a35700f4133ea003765ca02a17223353f90a031e04c7a3f22a3018ab80d03128031904e275604c2a5304e4e1804f2e6c0f58a5a9b5051704f2c7083c2c604fd394504c2a5604e151e225393485f2302c9d2269475103e0482e6b03e065b3a1021804c286b0f42a7403a350b2223202128b81822a2337cb96621057a51820571183f4181fc96763f2052f3f8500724128690ac8b92212f324538502b6012803183f41901050071dacc0421210071704f2b6c1b7295785904008f52f6c8f5346f83c377103a2e56057317b206361a38b1c43aed224592c0418057061704f304812802212e9271820d2a0304f2b4d20d276a8f5276d8f5295a84e041e04f053d9b5190084f36018772a5fb89343305e900ecd402183f49a12c9d2a6a8f507008f5335084f3759066227903a394e84e3e7403a3512b063d5eb7e071b84cb5182050501beb333f04f2e01bcd05008f52b7283c3e609283018abd2d7422d9812867136005d2b1bb00063d9b435732ef1b5fae3840d4b5073d9b5061b84c3d5db8b051c9288f16a042f37868286b0f6
    | _ => 0
  let q := fld packed 28 (i % 128)
  (prefixGates (q &&& 2047) <<< 24) ||| (thirdGate ((q >>> 11) &&& 511) <<< 12) ||| fourthGate (q >>> 20)
def finger7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xa7cc478a1cedac575879fc3567e2cf3ff6958951170f5fc235fc1be4cd92ea0a5e56f8bc846bee96e20b2ce226309a80dfb6a676c3a525e5fee9fd720c1ed85a8cc85780e5ae3745f54d6f2c89f05d3b7d6761e105a7228aaf010ee8b91c9c11689a4409a6dd78add8fe16b0850c2a25636a2ec4feb1462894e64806ca0c845a
    | 1 => 0x3d6d3609dff3bf87b9ca8b1732f4fcc0b56fc6d7f2c35ac4d08f0f7eec282a119472afef1bdb6a8ab54289fe1111eb59e137253d794756576c10994547fd9c47b15de8a8d35baf3aa21ef242e84b8be16dd08a1760744bc4ad3cf572ba206b80e39b87894b7258403c3459f542437f219a87f39325e21d051f6e0b235119a642
    | 2 => 0x9463da143ee59c40afa4444f3eade0ebd8d4170e0c8181f1180ca760182378fb0c03521590ab2e7cfc2249ec8ad5e29578ced7f3b0ee070d93aa5112c92a21c66e5a809415adb523043860f9a324fbea1ec2296498e0721f11eae9e7019b2d8f7f1c333f1349f202ba97d8d62ef98d3ab890f0776c0d13e1697c5543111ac1b
    | 3 => 0xcfc6f9118c0321f396102693da1c1903ab0b200e6060f7c4350d29c2149f6c0d1f8f5f890dbebd54b365b92373878227cd606972b1f110bae1eedd9acbc1ec0a6388364d257551397111f60345f037a8e0228465bc3d5f851ae2d19d72456b5aeae9219a1ddfddfc47b6b687263761101ff45ac53910e8b11e6a42359d386cc6
    | 4 => 0x7542184e37caf93f26bd229b4d094b78a6c668584138bf26b09057fb0a9813f1e6fa744672c21ce4ca7327d59f0c25de30149378e0a2268ed5ae3f742fefbf4eea845942a1956a0a7e24890b39495c3d1619bb8ebf71592294281d1351c20c4d77cd92c3c133dc1940b8961d3b8d9e75c21efbe2463d72dcc5953bba5c3ef9cb
    | 5 => 0xf954f7d7720cc064a370d44c247a42b8fb9b3a1a93c4a8188c7afca7b3fed6c3895544cc99f2847971d5ec20b2ba345806900947567dddb3611de65221fd8dfcb49639bd64f960c385114a5180a4788b32bf954849c8129eb6abbc399aaf6fba53f2a32898d5525be0949ebc72f9225a17ebadbdf48d5272cc8b9cb9a1de9e7a
    | 6 => 0xe2087227ea7340485bf4b60887357b672505ad284da4cd3af422c0c21bf1fe81a438b9fbce7921d6703a3276fce5dee4c5247b54b9c752c6056f72cf2321788795eada23e008290b3d51556cbd7ce4f677bab01ecff729713d6f1e94ad99e39c206c6a49ebaf5b996b233a308651cc629763359ae1bc6a90b1c36d95da099e26
    | 7 => 0xc4cf59999aac1706424cfd0522e4bcfdfdce6d7d5fd7b452324f7b7e566ef9c0e9245779b558ade9c4cd73c10b53f8cb9f9b6c247ef5d60604108bb999c88627de3a998732ca0c1d365947a07bfa5d8eab1c1acc5cbecf944caff89fa5aab11a6afc2ce88199a084a86caa077a86444767fc989e9b47b0c8c179c6e236fd3387
    | _ => 0
  fld packed 8 (i % 128)
def recipe8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x491856d03a4523e55aed7f83c432eb1a2355f04a7b83c1aa394d05603beb033f113d00712056204f4785a1fb8803cfe42236290f53184a6ea2d030ae43c9716a510ba4e20ad64b98550a3e0209c444a26385d7403a1c2245004a40864019c76ea2a424b56d20a37cb0179bb6785f022055a846018571904e40aea028994123e6e83a0ac8b5c8537a2827c83c36062040ae0323a2983e6d3fc460657b8f56d0f540857033876405959068024b512ca11820d5b84c6406255aeb67064788f52715227b856aa057e8f5018f50305d5f22a0409954a04590c712b06700f54d04c4285724aff244b20423a0404a0438701a276f83a0d4b52104c27b93031b464c213806550858039b52b2ef02c001a21102a3b7faec40858040480243d7f0f5043887103c22141770f547048204a52903c543a7590651c2227d8f5212f36192826330
    | 1 => 0x1b8570404f3104a000f501a2a52c5b5e05b0ac3e62b8816aea2a03a1aa52022086b03a620465d85732a171a20e4a1281ca1c66c0801bfc02bcd54400509b14b8461e20d03b112803a298f4348624eaf41b3394284c5bba11fb8e3f04a6a8f4298f502af40185802cbd788f43cb3710941549090519e1baf26e0f5508461685703bcd5e20e32c5c530461b2ca6da2c0186522b04104a61822a01a11030570209925a467203c1e04c588623f85e5bba7044a26c0f4280f5740f53d06763bd35f4ba5304e7a8f47b0f4043a5708f57fa05470670184f020f64120e16a976784a0383c59048040570305e7883a7d83e4ea0427b94448655649f1ea395c22a030644804f6ea826485f02beb7003c5647c668d3038570bc6820b90043350cc71560576605b2b03c680d120b8e5a857031b80405e4a9853105d74a056c0f5664a134c78
    | 2 => 0x29b15d85b732eb0699f17a341ca1f31be8038f55e21003aee128677703e241280304344c057e85b6504f6806965c7e45856790f57403c718f568068378487183c0a405074044084c03334530994b903204801a20b2b0f55c04f7803a6d03e0205b6e83c6f9b464b88040435884a17a460221057bf3030405f2294022c6804821a36648645c23e720f42522003058632f6430655796437867202b9590661a37c038bb500a6390651f2796c03c0183c2185074beb4d1950105308a152983a02857610595304f5295d4822743a34414785f84c6204e78a0604312378680408661850040582b0bb3f20625a9602b8b0304f181a67d03c5a8585d85634c05478482b1b77983a3f84a01227208a25a9b52104f538507a03e030f818850041736a83a0409f3305e7f9b538069261a67a03c18a1b2a83a2903e5b04f2e83c588653e227
    | 3 => 0x14d43e048390a9031bd612085084c1aa3b6304861a3e2b03e57c415f84f2224a1804f23b2f7d0f558cb9073f40204c25301041bc008572d0f51eb8f04062630a50405a488535323e038f47e0f54804c1718b0ecd41e8505abee1ca210285317300182030084c5ea3b540482e8f5020ac15b0559067193313f0571db3816850600507803e1aa36081696109931bf1034b42524d0f2fb1f09f48a390448b2c03a02c61732ed02b121a85016af03f85a0285858ae966af9440657b03c300484e9016b0f4038ac7783e040b30186646af4730f50332b513ee63b880432a022cf4eadd204ae4e9853fa2702a34018f43f2f25d0482a8b94005e348645e85d028f55e8507a8f54206246857449c83f059124b90284f02a7d720f54fc001eb94038d00247b1f234778f50432b3d850480572b20a430501cb9a0340546cd45e3a3761b4
    | 4 => 0x5f05a448551da515784a038fa7e03e5084f012e9179f66743f740ac3384f4f85b212f444ca00409a53a155b05665853780f502a2a6105e040987903a7803c7f8f5388691014d4e9431b9283f2e9770f4800626848d0084f03098210575886837865742096f0f542a3e023fc3f0556405e0305f0084e280f46d83a4c1b10a43f20b8f042f374a2b03a2a470595405b1e9ca388671a20d6686812cf956ad0468674eb080e49479aeb748f52983c028f74123503bfc211be0223b034630349d0f94b760f40286539cea19b023e84c191f9212f2758f556056713fc0285f20ad95484a710f54504f3b985358627e83e7349a7983c682906384a0ba236d8f421a3a5f38c044635685001938014040204e2c03c5c057218535285e04065128d26d8f52437f53ad02123e2120e010502521c0405f2049511a0c58cb35584a2a03c7183a
    | 5 => 0x1f27b0f4fe6c8f40599c020553910a3ccd456a3a243806c03a042cf0185002ba4038f97c0f55f858530980410a0222d468d1042345005d558620184c601286b8f52c0f51a20f5623e0392c1a21c4820d5604f2b8f50222a1e1be1eb957b83a23b8b558641a1ca2521b7483e684c92a8f51d24c65065760f548128019b503893172ea6c8f5450463e04f350642a83c1d928032ef0305b0305948b8616a565304c6a8f51820503210288f55489a478462521a2214f650577c03e21210562e90412829205492341639b18a971e23e5505e03cb306bce5585f4d046180576f8f5122fb0283e134ff370693704604059042101fb8f1e04f1aa3a4c2dd5c2056404f03b8667c630225b0905b2cbeb273993fa2d7303c5485d2521f6204c1419c1a23e6c9b733a113d9b67d03e03403458486b0f535200700f43f22a41a346f83c7b0f5
    | 6 => 0x5085660853429bd418501b2015c0562038f5d84c028461f3904022d573ef554975885f474a1609456084802b08398d52a83e6305d5f22b4e84e4404a5b3a11d4fa4022a738f566c5c7703c6218521227200c87e03c0304c1e1bd3d166030410285e50a043385e0205746234022f5509853f8597aa2a7a20a28a05332166f206023eb39cf604045212f044ca2778f4481854b1285b3a71704f040506746b56058164a6380662e0f57c03c0404c212047a0f50404102a0927b8e5084e038674b90d6c1b47d83c603ed5f37e0384c438530205d01beb03af71fbe64e8c3022f25949d04204703eb008f50fcc0038bd589443f05a3a18503c5d6d0b91b84c03a091c9280222850408758f47383e3f2086c80603ba166c9d5f8574205a043712a0f56205b773eb7983e63c050846767498438654384a7f83e0205902bed1f3882903a
    | 7 => 0x710f41f2f11a04f074057a03a2120f3d85721a390233404333241512010b1d1287283e680655e85b0289c01c05340cc5e211019b71e2225f85661a3563057458460204031a061b84f20b9762388163697aa051014c41c78518480085861c48398467d0f4638550285046057040bf7483c0286425284378690284c43aef29bfc028416e3eb390681c23603cfd02211204ab680665e0530a45f674680f94a5ca275604c4043943ae90203a1c0504f22941a3b632f2028567a83c1a21b628504104f1cb7f7603a0204f4185e482e9038aa1804c2d8f5191fe02209592f41f397462f2578592b20550b2c6385f4e8581984c0383a3ccf85f9281249709c1123b7c2c8f51e921039b651a3f768f51e20e104a77703a5105023b8c6285334c616349a738931bb20028682a8f46e8f55b05833afa031b61dc451ca1e2b282029384820f
    | _ => 0
  let q := fld packed 20 (i % 128)
  (prefixGates (q &&& 2047) <<< 12) ||| thirdGate (q >>> 11)
def finger8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xd6d268ade0aac843e79271936ecc34c01959a6d55902fccbc7ef9bd33f9eb90382fbbf842763936c0345fb5fd853f807535e351c39cead798b19ecc1fae8a6af197e04e30ae3789e34d7559e62572cc7df6611ab89ac29878ced90583b17a8a2f9a44a9a6c2c56ed88e5db01f15548a318c7dfec0e35a48812789aa500c9dea
    | 1 => 0x3da24109dfaac08751ca079d3214f264b66f5bdc14c35adc64bd0ffee314b9bba9fbaf6ba0f00bcba4ba0b45a1cf24592e76253d712e285492408a7047e27238b9e2e825f8b16dce6cd7c712dfb5e41648fd98e08c48d266663ce655bdea286c8447bd894be93dc0933401893a737f842d6d20722fb72d881fa04b9ca1e5e5bc
    | 2 => 0x975769b043187ac449fa447af3e3d8611188ce3b23fc829b8940ca762a3c5a7c8632b76aa9ba562095d6c6af47488a460e8c687fa15b7edfd70aad0bf1af35021653dd50dc5adbd90e8a86c0753d89d2e6759afe356c74bc4967bc09f4b6c8bd4633381731619ae503bb7d8d5fbe5e17ab3093beba8fae2f5333b72f59ecf0b8
    | 3 => 0x8fd902048c0221c3c7910969161c66bbd60b8e899949e476de9d3f15209f4853f08f5f1cd70b8454a523f576346df42731406945bbf13f92c094a09a026d6a7141a8924d6549da6686aa79f0c92419db32b91e4d984b16483d2c10bf29bf6b4dd8913eb62bdf4fc80ac3befd26c0ad6c72291b8b39207dcc036799ef66ec3129
    | 4 => 0xb1af54517922c5e32624d94996cbcfa2b2f9a06441da4b30787d6f16d4989992d511df67726817c2c6f927b5e78c32333e1e93f9ec2c268a365c9874059449171499f3869145e10a2ab7909be208a2b821b88b8ede02c6f68b3eaad00c0d548ab653d7727e33f1732b356c645beceedb871e66cd3a3d728fdfdbca13445cd430
    | 5 => 0x1e543983e2e25b81a3d28214e17a40343dfe3adb08fa7abde4ece3a78d3a9e57841244cc3c5484033d6e60a05e7119638a90e0476d4d0163421d4db882041dbd1896aa3e91ead72724b14ac4456f1dc3aabf7a5742028b9ecfdcbc946981678d39f2a3cb981cd92a52941fe77236b41d41e8ad4e9f8d952f037a6c257ced6443
    | 6 => 0x85121082eefefe1eeacbb6d7597b4b25017d623852a4da25f44ec0beeace7181a443eefb2016492fd10f9f450c29a35871ccd9be621db22c220a4cf6232c702faad239cdd30502f9cc045e4710aac5ab14ef35cecf989f8c2b2f48eaade379e53b3e6a78ebaf5b6a0c3c2b309f51b44f2af11b3c353cfa901ef3b15525259eaf
    | 7 => 0x9523599983acb306d744100522e9dc43e76d7bb35fa6d7c39e57e17e56a65d55e2995074b2578930d54a7cad5dda2530f19b5f198092d606b2129ed95ce2c5f393ae6987323f56baaa0f2bb4be35c45c95a782ccf1becf1a7298bcd14755ec1a6af119e81199ca34a87c1d07bac79847861a98a4ec1ad6d65a0ec66e3787978a
    | _ => 0
  fld packed 8 (i % 128)
def count (s : Nat) : Nat := if s = 7 ∨ s = 8 then 1024 else 0

def board : Nat → Nat → List Nat
  | 7, i => cpBoard (mask 145) inputs 4 (recipe7 i)
  | 8, i => cpBoard (mask 145) inputs 3 (recipe8 i)
  | _, _ => []
def atFinger (table : Nat → Nat) (ws : List Nat) : Option Nat :=
  let h := hk ws
  let i := h % 1024
  if table i == h / 1024 % 254 + 1 then some i else none

def lookup : Nat → List Nat → Option Nat
  | 7, ws => atFinger finger7 ws
  | 8, ws => atFinger finger8 ws
  | _, _ => none
def ck := checkpointCheck 145 scs count board lookup
def pan (s i : Nat) := ck s (board s i)
set_option maxHeartbeats 50000000 in
lemma block7_0 : span (pan 7) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_64 : span (pan 7) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_128 : span (pan 7) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_192 : span (pan 7) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_256 : span (pan 7) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_320 : span (pan 7) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_384 : span (pan 7) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_448 : span (pan 7) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_512 : span (pan 7) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_576 : span (pan 7) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_640 : span (pan 7) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_704 : span (pan 7) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_768 : span (pan 7) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_832 : span (pan 7) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_896 : span (pan 7) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_960 : span (pan 7) 64 960 = true := by decide +kernel
lemma good7 : span (pan 7) 1024 0 = true := by with_reducible exact (sj (sj (sj (sj block7_0 block7_64) (sj block7_128 block7_192)) (sj (sj block7_256 block7_320) (sj block7_384 block7_448))) (sj (sj (sj block7_512 block7_576) (sj block7_640 block7_704)) (sj (sj block7_768 block7_832) (sj block7_896 block7_960))))
set_option maxHeartbeats 50000000 in
lemma block8_0 : span (pan 8) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_64 : span (pan 8) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_128 : span (pan 8) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_192 : span (pan 8) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_256 : span (pan 8) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_320 : span (pan 8) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_384 : span (pan 8) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_448 : span (pan 8) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_512 : span (pan 8) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_576 : span (pan 8) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_640 : span (pan 8) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_704 : span (pan 8) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_768 : span (pan 8) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_832 : span (pan 8) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_896 : span (pan 8) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_960 : span (pan 8) 64 960 = true := by decide +kernel
lemma good8 : span (pan 8) 1024 0 = true := by with_reducible exact (sj (sj (sj (sj block8_0 block8_64) (sj block8_128 block8_192)) (sj (sj block8_256 block8_320) (sj block8_384 block8_448))) (sj (sj (sj block8_512 block8_576) (sj block8_640 block8_704)) (sj (sj block8_768 block8_832) (sj block8_896 block8_960))))
theorem closed : ∀ s i, i < count s → ck s (board s i) = true := by
  intro s i hi
  by_cases h7 : s=7
  · subst s
    exact spOK good7 i (Nat.zero_le _) hi
  by_cases h8 : s=8
  · subst s
    exact spOK good8 i (Nat.zero_le _) hi
  simp [count,h7,h8] at hi
def rho (ys : List Nat) : List Nat :=
  match fld 0x66751402adaa695 1 (bsr 0xfc42f9d4f983b625f65fdd8aef12a16bec0068fceb7ae66ce7927403e2dfa6bce2db16bfe26ffb0ddcca50b6dbb0c082d44e0266cc4ddd90c85b11f0c1dfed25bf892aa7be90fde1b9bc5323b8bf2ae5b840280ab5d8ee2bb3adf8d9ab918a6c97bbd4b794566034940775d48b1dbc4189fbe569857f9ccf8332a657802623957e18e57872440c2866b42c306577bede64e28e865fb708ae5f5ac764582d6f9955b81b3d559524404b5745984233e06b3e995e0c3ca6bef13b7161ac39b75ee63691856b3404dacb3142e40e3053a2802852bf39263f2b591ea98f881e2ab19a1d566ad01839463c149a43ab0b8e4e0d0b26fed30646ede901f9f82f01eef95d 32 (hk ys) 7 0 64) with
  | 1 => vals.map (fun r => fld 0xec0036c00ca0000001140000001000000000df003398eaa0000000e80035c00c900361ce4f6b0f984370000000b40029d829700335884b618e852270000001110000000fe0047e3a84002b9ee700044a2077002a5ec6c00419f4747ca70bc5c0000000b2002880096002b56a245586924070029562205083122040026d281e498240000 9 r)
  | _ => []
def B (i : Nat) := mv (mask 145) (fld 0xf54e52f21f41000401e10e20f65e50100f20f10402400506f53e54e41e42f31106e51500e53503f50f52e31e21f51f42104e65504405103 12 i) inputs
def I (ys : List Nat) := bsr 0xfc42f9d4f983b625f65fdd8aef12a16bec0068fce2dfa6bce2db16bfdbb0c082d44e0266bf892aa7b9bc5323b840280ab5d8ee2bb3adf8d997bbd4b7940775d48b1dbc4189fbe569857f9ccf8332a657802623957e18e57872440c286577bede5fb708ae582d6f994b5745983ca6bef139b75ee63404dacb3053a2802852bf391e2ab19a1839463c149a43ab0b26fed301f9f82f 32 (hk ys) 6 0 37
set_option maxRecDepth 10000 in
lemma roof : bar 145 (cutB 10 inputs B) (cutN 10 37) (fun _ => I) (rowOrient 145 rho) scs 11 0 = true := by decide +kernel
def nextRecipe (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0x33d90cf5433d8c5e6533d80c40633d4ccf5031014ce76339d4ce6533898ce2530414c505139502e6530408c50233c50cf1333c40ce7133984ce5133d0ccf40310107e64339d0ce6433cc0c4033398cce53339ccc5073041cce243384cce4323988ce2331000ca604f818ce60329423e05339407a608f8107e603b90136034f80dbe606e9023e0377981be400d8183e06339c08a603b9408e60339007a401f9008e40328c1be50338c1da4077900ea303b8c1ee606f8c08a307b9008e3036804ba010a840de012f80426100b8407e03778c15e1055841ee30
    | 1 => 0x6d401bf736fdc9bf766fdd5bf716fdd1bf706d01c16026fc989e2337985b5035388cbe621b88cae21078083e136fd95bf456fd8dbf436fd845e636fd81b40667985bf405f989be766f9d11e634f88dbe246c411b504139442e626c409b5024398dbf516fd41b4056f9d5be656f9158e616fcc1b4031f98d2e635b981be616f905be71579c8fe613b88dbe516f8c48e636d00036030f80dbe703040cc10432c84ba6131d40c72131400cf7433dc8cf7633dc4cf7333dd4cf703101c160533c989e253140cc50433c84be611b894ae25078143e1633d84cf51
    | 2 => 0x7bd49ef327bd445e437bd41e405678c5ef305f8c9ee757b9cd1e434f90dee637840de503138842e3278419e5064384def417bd01e4047b9d1ee547b8d18e217bc807e134b84d6e207b945de31578c8fe213b84dee4179000ee703a9813e044b980ee60198146e052040c8321204088721214008f76200008f6523d90850323d8885021b9448f6323d801e530f9908f5123d045e5423d0c8f40210108e54239948e64139082e5323c848f1323c407e41239448f302100c8e432141c8107239848e13210012e507b9c12e037b940da612a885b10303944a621
    | 3 => 0x39010ee763b9d0ee643b898ee2438410e504139482e6338408e5023bd44ef533bd40e4053b9d4ee653b914ef133bc407e613b984ef303900cee633b90ce5073841ce400569c15e703f981c500704015a6057980fe50569415e503f9015a2057880fe10098084e010b80906034380d8a406390146035380ca6052b8142a40138c02e40569015e403f8c066031b80cda2162885e102618840e2179d01e73079d41e76079dc1e5007bdc9ce437bdd5ef747bdc5ef737bdc1e4075a881ef652790cde21794094e432f8c86e132b8c5ef60078c83e437bd51ef34
    | 4 => 0x3d40c45061041825070841d55073d418f1064141cff4257d48ff4157d40ff4055014f40457994fe5457914fe3457cc8ff2157cc0ff205500cf4021d41c71074941cfe5257c80ff1055008f40157988fe5157908fe3155000f4000980c4e020b80d5a30578c0fe202980cae03518114e04629818e60429810e603840ce730384046a2103948e75039d00e76039c94662139dc0ef713bdc8ef7039400ef763bdd4ef733bdd0e4070580cef2627890de6239404ef252f98c6e212b88c1e030d8503e143bd94ef453bd84ef603bd04ef403bd8c5e6439018ef43
    | 5 => 0x5b8c1de5175001ce037180dde704580d1e03779409100254024100914002605138102e0554408f1015440cf10201418010655c41571355c5d571655c55571255c515f1057c4d5f1757c595f1557c495f1455400f50057dd8ff652541c91073541cd1075540cf5025141cff642d41cb1071941c61072941ca10757dc0ff600541c11073c00035020c4095f653fd515f453fcd15f603fd415f403fcc15f633fd495f433fcc95f623fd4455071441d54063d0155f423fcc554043d00d5e16558595e145585115073f94d35073f9955e743f98d51043c40d5504
    | 6 => 0x2900414020d00d6f525bcc854035bcc164034500d34035b98c44010900904035bc8164021d00d2403590000e012d808be021580c5e038580e1e039180e4e038980e2e032580c9e0364884da3166885d10375cc00e3175d00961365885d75075d81d77077dcdce5377dd5df7477dc5df7277dc1d4075a8c1df652784dd500378c5d5035394cbe421b90cae4177d801e420f94ddf5477c91df5377c8ddf511784ddf50750159e215f809de75779c91e134f94dde6274409d502138c42e424390ddf4177d01d40477951de24638c5df307500c76231f88d2e43
    | 7 => 0x1d0147f231fc807e751f9c87e521f9947e621c4087502138c82e431fd047f401fd0c74041f9507f131fc0c7f101d00121014ac840e4249c8527704bdc52f764bdc92f754bdcd2f744bdc12407480012f6227990de524940125014bd94be531b9852f602b98c1e630f9d12f254bd152f214bd052f23178912f204bd0d2f40490112e724b9d11e244b9892e644841125040984c2e13439452f504bd4d24054b8952e454bc4d2f034bc407e51490012e701f9c07a50478107e504b9015b203acc08b3032cc004015bdd8a6015bd9494033540144032d0086403
    | 8 => 0x1009ff7071011ff757fdd1ff727fdcdf40719805ff6525010d4027d40144042d00c64012900c14030d011ff547fcd1ff507fcc1ff5215011f4056500d74037f9d5fe734501134047f98df1037d40c44020900d04017fd09f40461009f40003808b6032f80cd60237808960427811ce047181246049381196036780c56041781073211c4047b21038c877401dc9077211585077501dd8077701fdc47f761fdd47f741fdcc7f721fdc074071c0007f651fd8875031d40075011fd9075041b9047f601fd8c1e430f9507f541fc907f511fc847f53178507f50
    | 9 => 0x43d045f5443d0d0404439510e65439904f420bd4d0f03410007b404ad40a100294010a4043900610019401db4056d40eb507ad01bb50858161e059181a4e06658119e04898122e04258149e0503c858f7063dc98f7663dd58f7463dc58f736101d6b2063d949f4337c85850253d0d850063d80bf321bc4caf3107cc83f4363d518f3463d418f5263cc18f3263d445f43610158f315fcc98e75639cd1f434fd0d8e636040d850313c842f3263d010f1363d05840076cc0770349c0d4100514018a50639418230628c18630638c18a70639c15b306ecc0cb40
    | 10 => 0x114104f5213d444f5004418310709c544f3409c4c4f3209c4827140bc402f700bd002f730bdd82f710bdd42f720bdd02407080002f610bd9025020940c2f65094142f630bd882f60054182e760bc542f450bc4c2f430bc482f14094004f310bd084403090102a710b9c44e630b9d026140b8502a610b9844e530b9904f040bc144f020bc0c4f010bc0841031140c25040840424001440055008840225008440215000a9c04e600b9c02a60139402e6041c0c31000d4010f76400010f6527d510f6037d090f622fc4c6f512bd4d050007d4c3f6443d010f51
    | 11 => 0x1b898ae26078183e174fc593f564fc513f544fc4c5e624fc413f534fd4134054f9d51e624fc193f044fc0d34004f9c19a60679809a21258863f74738563f768fdd63f738fdc63f708d01c16048fc989e213798e350453894be641b890ae24078103e158fd963f15879922e628fd8c5e618fd823406679897e608f9da3e71479863f058fc123f034f89634000d8143e058f9c11a60479813e508f98231008d40131004d400270509c0c270244401150064401950009c404f6013cc04f6213d942b7113d904f6113d8c4406100002b6113d4c4501114084f54
    | 12 => 0xd0157f545fc117f535fc0d7f521500574055fc097400858121e04869c21e708a9c22e70898162e05258189e06669c19e7073815c605918164e0514884562147dd9100047d889e6147d80de5347d94be541b990ae64079903e7547c911f1447c105e2147c4d1f0347c4114003580cde034dc1a3705518194e06518154e052d814be052d810be044dc123704198106e04198186e064dc0e370329818ae0629810ae04869821e608a9822e60169805e604dd413b214dc853f744fdc93f714fdd93f734fdd53f704d01c16064fc849e263799535044fc98be65
    | 13 => 0x894054f542fd0c6f412bd0c1f430fd522f048bd522f248bc161f418bc0e24003ad01170415c0c5f76140005f6017d885f611540c5f65154145f6417d8c1f640fdd45f0417c905f1417c0c54001ed41db507ad423b606ed80cb6067dcd9f7667dd59f7467dc19f7167dc994075acc19f6567d809f1337cc5950353d4cbf421bd0caf4107d083f5367c119f5467c919f5367c0d9f2367d419f5117c4d940045c0d9a5067941eb304ad013b5022d01bb4032d417f735fdd97f755fdd17f725fdc17407158057f6525004d4035d40d44052d0106404290101404
    | 14 => 0x294146f2329001db600dc0d01002a9c0ae700ad815b707ad808b6007dcc1f7007dd81f7507dc81f740501c100007c181f0405408150307c14150507c0c1f0205000b6062f818d6063781833210dc8437270dc8c3f21069c03f170fc543f050d40c3f160d4183f140fc103f130fc0c1e700d0010b4062d415b6056d00570487dc21f7173dd21f7287dd61f7387dd214077ed421f6087d889f6437d4a150153d90bf531bd84af6307d8c3f7487c161f4587c0e1f0485000eb6062cc22f708bdc5cf548bdd62f748bdce2f728901d77038bd962f6027c50df32
    | 15 => 0x35c18df0137c0cdf7634000df652540cdf0237c18d40048400a7051c4014f0653c154f7053dd14f7253dd94f7505c154f2627c954f0437d914f03510018100529c14e70519c1427019c0cb7022dc0cb7062fc04bf702fdccbf762fdd4bf7401400bf052fd94bf0425414b5022d40cbf612fc08bf032fc18b4002e9c0be701bdc06f711bdc86f761bdd46f7405c0c6f061bc986f041bc906f051940c65011bc946f031941464000dc107b604ad806a701b9c0af702bdccaf722bdd8af752bdc4af7405c08af062bc98af0427c8ca5012bc14a5032bc94af03
    | 16 => 0x30d424b710cc1c3b0786dca1b6238d82172316dc8572415c8c735074d41e35051c98972519c90736029c98972329c94672374d81e36071c90e3701cdc1d37078dc123700ac40c1006c400810078400970535c0cab702edc02b700ad022b7026dc06b7073c0dcf0573c11c40006dc0eb70384007b7076dc1eb704edc23b7032dc12b706edc0010029c18b70516d80670693c1a4f7073c5e4f7505c1a4f0393c164f049100097032dc10670427c149f7027dc89f7627dc4170427c189f2627c0c9f04250011b600dc164a70939c09a70279c1d10019c14d702
    | 17 => 0x28404330304409ae050c40c3b036bd05af211440cdb315c40911036b80931036b948410108409010336c84ab3162cc4730369005ae011c40c7b034840ce330004098b5262cc9d33052dc433062ec040f6003d880f6503d90bb7103d840f6301018000003c100f5403c0c0f530140405022ed840f0103c080f05010000e6003d480f51010140e050ec180e652ed44bb4103d080f3203d040f43010100f310100c0e640398c0e43038100e03039500e530040c050300410050442d88b71342d0873402dc49072374d00e35078d00971438d01972378cc13350
    | 18 => 0x404db016bc09af6568001af542440daf016bc14d1015040cb1021840cab71
    | _ => 0
  fld v 18 (i % 96)
def C (i : Nat) :=
  let d := nextRecipe i
  mv (mask 145) (d % 4096) (B (d/4096))
def nextCodes (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0xd716070006c00000fc6b10000005de000aabd8640882b79dc66b88e6e1cf8093f9b34000b3037525fde70009e52cb29c6770d72a6000e93bde37a7d10003f5baf707b111436610003d0483385c1409fc3cf5209bb1400086cd9afb838e30951631b2657705c500000000000097d3f1c823cdf416150007eec030003066fc6140008a8df13517614353800002559cb8b1
    | 1 => 0xec400058a5d97990000003db000a234fd0009f51e118a90a0005bf35800037e191a38cf5d1ffbfd780009533c29fd1d389688f00055d7399cc70bbf980746805bf224395f21494dde2002e4209120000009fee5a12ba9723d3e6062993d5db4dbc5000ad80000000b33b62920007b9025000000e10844902561ef554010aa5d000819a3fc021ea8a5a21866000362d11
    | 2 => 0x9856a3c2bece4c887a46dedf2dfa3eb7000077a9eeb24d8b28071518fc9a9f300030e60bd8368075fe019a1aa934d0008710aa50f00011800096a8bd802000d2e00047993db8f043000000bbc1da0002950000004c7000000be3000271c34c8f000ad2f0ab058ecc14000a5c2a91c244e9e83fc9a200075b1470007c5e81435000cbb000e46000483000b9c0006b587f
    | 3 => 0x9bd3cb0008d445491c0ea7adc9eb8f8b1b992df303e530001191e74d9251d79000d3900039f325bcb11d0006f100055d052fe600012176e55630a593912e53000ced16f000823d603a151345739000088658eae8d8fecf6a0a91a25e0a42555434b1d25b2ad5259bff5877b1cd46e8a327b53862a7907aef745cb83321c100064556c8678804b8dc5448538cf34be2fc
    | 4 => 0xeb60002a252bf72b392b2ec110c00007a5e9bd1783000000c16079000ff7256bdcc0292842cbdeac300077f000cec0000a1a4a93b24df9dda5916232439000d16caf2e023d104d1fd545da924000d02d184f7a206c9a716a48f0000b75ac840a4187fa000f7046a4c05dea0338cac8de800071096d4fc17567c02e9afbe0c785f48de000dc0cc8d09477731953000
    | 5 => 0xa4a000000de3081dac566228561fd9000000b5ff0acd04c8363ddc33e82cc4c349fce3cee521134be694df388f2787ee000a73079d81d98537030a6d42849851e04bc99224000dc12c53e4e731a1d95857a8a05a0002e847cb8cd52398d9aaa5a63bffef10000a30000005f708075f000222000e1c5a5e36db2551300cd95ab1a320e8dc6adb576f3b869b00ab3b3000
    | 6 => 0xc400000004f000059c40e0000000000006c100054292dc69d7cd81037c2e001f5913f88a1d53250009393810000004f2000b4ab5e16544417781a323000e330c254666f5bc649748c99000f5eb86000030cdd68f000266e84aa8eda2aa000801dfe000b11906000dee9fd5642c0bc0830030fc8d8f29d3b73b42d0d94a43d0c6267bd0004a5e6262de37e679834b00cb
    | 7 => 0x6b6e1700020203c0004384db4fc00002ec0b2e18d20002a20000000988a0a7eb9b438890360c51fcc49a1e94e00003a7dfd6c330a7d433100250837f0004f3e180f81be71baef6220009b10005dd7ef0001370006a67a649fb072b079d13f9248bb5cfc17dba31a0006601fd000ce900050e0623203be93c00000087b646000b4dd6d54da55a3700054a000e42168f70
    | 8 => 0xd0bcb02a29dfb1d0002c3aade8d7f3f82a4ed2a0ac000fe53ff5760001a63f31ef72e77229a16500000022de9135edcd42b3325f30cd9b270adcb00000000000000b00014dae0173f1f5b27c60009db000c12fe300042624a900a9eeb65d4c2be83b02425d6671aa62f8210879a8d744650ef0e617df52c67adbc87a97f5635103b10000c90d4157447a4c74927f11d4
    | 9 => 0x243ed7dcd000e19cfb94f5ca3699d2d865e978a33900091e3d35690043e800009cbd70898842e59370000900008aae8d72a98efb6002ade00017c00060da067240000000f7766000e50000000165f1aedd8795190004056747be1052180007fe7eb4292eea0c015f4f0ba517000739d3f0fb000000000b36ca692eae0b8cc07b2700012a5612f2571b821fe6c2e54daa
    | 10 => 0x81a0000003e7c044b25ea7f45ec5faebe42cd7b0962082127b842c43b000549455000c57383000543146845439fe8eb0fbc0ab3580005adc5c00008a5b0056000ad1e02ee611206d44d85b92337a069000422f838d3315374dab7480003705bd5a45245d1e61dd7cd99961fae9b6bca486cd51d8e0795000b0c0002d386c2ba0002287378171aea086d2b12b5711789f
    | 11 => 0xdb45876eb2987464fc1d910a3fd8e828a226c254994100005fe0d92b9000cd69b769da84db8795000af0a555462688af4a800069309286c5a694b000722de0c19778737829dbd3a4548d242f00005d0bd63df50f000ec433800048295e00076a53501200033f0001ce6edaddfe7095000655000000b8d14f1bd8fa73db4e230a3736f000d186d7da6e91dff3fe10e
    | 12 => 0x99086e18afe441000000cb61ac399c26e86000316c866a234e000b0a11c2943a0d034d20434c7f193588a90006566f7ae31e24eb000000714af7000221a63000262af50c263beec0d40000e91cf63b6245c00c800085daea13f2d3bd3a350c70acbe5725b1ee5c53fd9297ed12b75f7a02300000047c99640e4a2000cd4b627ad9deaa934b6ec21e000fe4000f437cb
    | 13 => 0x542e86fc6706b67fe966eb9b7d338fd7d8520f733ec25c42fad000667e2b0d800007f3eb986f9b7b7f99000b2d6c418600030f000bea63920372cb339ee26f9510b30da978ebd41d00000024b4deccc5ed000000f51a9f4f9502872f230004de78131cdd8d7a3090008150c9000a6c712563cf0f487db85607300008d7d2c1ea6f00044a2200003de072587c5a13f03c
    | 14 => 0x1b2000000a287e90004d9150000b2524a8dd7ef4750f56fb1083045144fe00077550973db4b8ab000101116575efb94267887056c4738b8b7364bb5309c52b4df344000252fde3ab96b453df6000aa059d2236d676166283c807164520000fb1000dd130fd6a200557fcd0000009f7281000adc000a7e00096500044f000af45b4a4b5c8f3de990000000006be59784f
    | 15 => 0x8f4b65aa25c2af50c1d0453efae60a94451eed030b5eae790000001998e460f082783000612000814f629d3000840951de6000d3f0000003c57f82f30000000002d4ec90390005900000b13fb8860005fcc7d83e4f1fef300a9c89d5831364176745de45f92b1b18146c5c99b5d254000000000fc9dd90008467d16ed0d477c209ea3000c79cbbb1ed9b81f61c0004a5
    | 16 => 0x6fd7bd7d8714cf1496efecdf55f000000000a300f62505ec38b0bd0002c130bbf9ace0b73790007cc000f2cd5c14500024bb870002cd31c8f26ba8749976cc39bb68eeb000701cb1526f98f10000735653873724000afa0008c1c22fd360af941d66fd852bc527f3e8000feb6755fc000fd3f56000e6247da9fb7f00055b0df23fd70dfd5bccbabde000f1165769a0b7
    | 17 => 0xf809d039060fd317b8050005cfb4100079a000a96e2a9e93b30b6b86f2c064df66a78209e0d7ffa3bff20eac049c4f4b66000d3fb3ec5d529cdd9b500051f38e000f42fb04dd3bfcfb9748afcc3314e1f96800000015123f674000997a2576b5487358df3cd0000000be000754bd9000e56e1061ee524283f305991bbca94b8051093da6e7faf0001943cc9d7000b1e
    | 18 => 0x689fad5f2a88659000aaae3c8051267dd0000000000000abffb6ea277000000000000526265000d7600026400071fb73d479b5e7359b4d80003e0455865a354d7692b1d134b0cf17000c13206b6a751000c3a000497000e334565dc05b85600047b000512c49707845a027ff0002a5188fa0000a113558ad3a4b75000da13f300700096ff49032120eed000e60be9000
    | 19 => 0x1e9000000000457614214dfb00000000000039e00001407d4da4e8b512ba42c000dbc14041808d6f29cdf19000a792ff30883f1ea0ec4c6000212fd98c70cd2f374b50439500926fb4a0004d4000e38073b8a5630920b50005911dea74583fae000cc6d94000f5ecb5bd8c7cbd80001500000004e659988e000d76000b7b760a56c683c3000dc4000eb86511a5118b34
    | 20 => 0x65bc822b2000f2d0006d2d260002aa000d732f76e5610000ec90f512000045c0c16e8f6060600ba0f00000035e9e3bb8658158000d107e268bb7f0000000006c3965620bb93e9a922fd000a9309f00000012b57500000028dc200005a02c80004296106cf00004edb7fce8479cfc74839000520d7a3b25a94c3f5950127c8389c7000f8c51dbe92c91710007d37c1bf7
    | 21 => 0xaf2df860c524ded0005b60002db67d0000fc19de9e0f5d3ef7f5b08d54b2141917dc600095b18b1f5aadb412716a1000b7eb050000000004bb000345000000321000cc16b5105000000298a6b000000dbd3aa3887704368b5ed10003b500029fa0b1c30eb1c0000af86f3913a0729600037f000ee58900000006fa00057f3ebe3f14df02fa9f24befdb39bf317
    | 22 => 0xfd36c14a2319ad80000000000004fc0009b45dd00017faef000000fee000c3f2c12a40001ea426bc41a824e4990003980000009df0002e45640006ed9fb000000000534000086685113b453113874d46ec000000101e3c0001d20001ab0004657923bdad400014b000ce871f000000b8600075500015c017cc205f0006cc62ca2900045513eac7cfb305230918dbf000
    | 23 => 0xc89c65c335aa19500000079d6e880e00077b000000b640008613ab236584e6c0006ec9cf8e124c3a63ebce90000930e4f3a6a27b0fc9b165bdb25000ba400052d00000043fbe42771358436f28ce00000039e239aad70aa47caf00097ffca662639000000c12b1797b0006ff000a044a700000000000052e47cc4800095a0002f9d9a000f8e0000003f1f9fab50007e3
    | 24 => 0x209b9f09a024dc79500000000000009ff28e372a6e418703039b0c212000e4800070cf54dbd6e1000921000a3db8757b000bc27d06a6b86f16000000151b6f338eb8311e2843413d0000000bfdbb000000874000000e176de0b450a00045f4c944dd3773b000982fd6000000bcfd6ef89502956f7234c000000c52f479db00026f05b0000009791fe81ec125d22c71ca
    | 25 => 0x74e005ea074951746302d8250003fdd0d48acf69b06cb5b5982f484ead6f27a00028a45de2d000000e1f97d000dd4000b8815dca5083a486d05dcab70eeb529c03e9000d3500000000053510e0ee7d549377298cbac80e0b8b4f000438f4f6d6f89d8c1db000576170c843edb5e000e8a08a0000005f70002440009b94ff1348a8e4ddf33b34b964fd384bc73d89a3cd
    | 26 => 0x948ce093a4f83dd0000002ae3576e9ac50006724310000005d30575b7d85ba0495b9b00057827d00038c221a3efd63ff87175c578c0d161a1500041f0000000000000007bd000422fbb000d29db75c77331ab298000000c580e3d57b24000c589fbbc8487063d70331bbd76382b000fc5b1a000000d2e0000001e4db56ce475a16000000000c131b893f21f23a9bb43e
    | 27 => 0xb0752e292b9b75b06338d5260002bc3f8c1e00098cd73000f2c051e970bc63f46e619b4d0006b2be90000005941a480d993046186000d186f803c421699d9b000000c7eb8800012918c000d9d00045bb3f00000067151235b000c879ae9e200000002ece10003c5569000202000ab0c6bdff00010b061e44000fea000effc8b000975c500000003b7612e52000dbc000
    | 28 => 0x7559dece6230c9a1a70dd000bb14b301221a1385b1675bae59a826a1e4a870551221f7bccc869b00000089a1cef9cdbf7a8338afe7f710132982b8d60005625b624f000508cd700032b95aa7a1a8000fdb8b000052324100003781500012fadc657c17378fad000d37f750000004b6000cc317d6a3653000c80000d60daa567000aef9e75591b92bf00025630166733c
    | 29 => 0x46138f2074e12da93adb0000ca658a77e6e305f9200007090008e70007d03b89f0dbc5d3b90c66d98daf6d1c1a00000a7c0e1f000e7dc969fc000682cf14e6feb419629cb4000000cacddffab9a6ed40008a4726000870179000c654440000004f190e000c3535d0d7000cd815100040cd8323ec47387000d903602a038500003beeac0a00062d7bf3730f2000e4a335
    | 30 => 0x66867000075b000000356a5b24e0008600000006bf9a6f7fa7db146603adaa8000000e7bd59c79000000bc1db1e432d2dc835225311f294419ca16b0000dc89d31c1f73101223000262000b290fd3780b0fa8cd8a0e0003d630c668d2c0001bc1e00000004fa42d4300005e3e3071f0004a10969f02f0115ef673d000dbb3ae0006508021940000951e08eb06d4aa15a
    | 31 => 0x7b4f32131310658c242e91e2b2102ce630005e30002f7744000ddd903de9658ffdeea9d50c0000000b1569f1db0005b0c76afcd1a431efebefa6ebf9000fa4000e81c9eee1000613faa0d800088a9077ae0b3000000e6ade3d660000001928fb44b000b9de269ecca0bbe0000a34c384d364d26197333eedd329ffc71695dbd984e13116a4053def08d1c8a278e70757
    | 32 => 0xe55d372719303ce007fadb2b7db098519af91731098602781e5a1a7ef0c70003af3b647750acfd9db
    | _ => 0
  fld v 12 (i % 96)
def action2 (ys : List Nat) := orbitLookup nextCodes 0 1033 (hk ys)
def rho2 (ys : List Nat) : List Nat :=
  let a := action2 ys/1742
  if a=0 then [] else
    let c := fld 0x2e4631ac688 21 a
    vals.map (fun v => fld 0x1210045001070000000db0000000ce00000010400401f92000000011f0044801060047a3a908820e0a76000000103003fdf31c0040a02737e9bcd65d0000000e90000000de003a1ce5b00375b84e0035dac4a00331963d00325903960c6c6c280000000b7002cc011a002d96a265888e321f002b1561d50866300b0045e2c088a8180600 9 (orbitLabel c v))
def J (ys : List Nat) := action2 ys % 1742
def r2 (i : Nat) := bar 145 (cutB 9 (B i) C) (cutN 9 1742) (fun _ => J) (rowOrient 145 rho2) [] 10 0
set_option maxRecDepth 10000 in
lemma roofPart0 : span r2 1 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart1 : span r2 1 1 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart2 : span r2 1 2 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart3 : span r2 1 3 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart4 : span r2 1 4 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart5 : span r2 1 5 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart6 : span r2 1 6 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart7 : span r2 1 7 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart8 : span r2 1 8 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart9 : span r2 1 9 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart10 : span r2 1 10 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart11 : span r2 1 11 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart12 : span r2 1 12 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart13 : span r2 1 13 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart14 : span r2 1 14 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart15 : span r2 1 15 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart16 : span r2 1 16 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart17 : span r2 1 17 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart18 : span r2 1 18 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart19 : span r2 1 19 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart20 : span r2 1 20 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart21 : span r2 1 21 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart22 : span r2 1 22 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart23 : span r2 1 23 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart24 : span r2 1 24 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart25 : span r2 1 25 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart26 : span r2 1 26 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart27 : span r2 1 27 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart28 : span r2 1 28 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart29 : span r2 1 29 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart30 : span r2 1 30 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart31 : span r2 1 31 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart32 : span r2 1 32 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart33 : span r2 1 33 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart34 : span r2 1 34 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart35 : span r2 1 35 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart36 : span r2 1 36 = true := by decide +kernel
lemma secondRoofOK : span r2 37 0 = true := by with_reducible exact (sj (sj (sj (sj (sj roofPart0 roofPart1) (sj roofPart2 roofPart3)) (sj (sj roofPart4 roofPart5) (sj roofPart6 (sj roofPart7 roofPart8)))) (sj (sj (sj roofPart9 roofPart10) (sj roofPart11 roofPart12)) (sj (sj roofPart13 roofPart14) (sj roofPart15 (sj roofPart16 roofPart17))))) (sj (sj (sj (sj roofPart18 roofPart19) (sj roofPart20 roofPart21)) (sj (sj roofPart22 roofPart23) (sj roofPart24 (sj roofPart25 roofPart26)))) (sj (sj (sj roofPart27 roofPart28) (sj roofPart29 (sj roofPart30 roofPart31))) (sj (sj roofPart32 roofPart33) (sj roofPart34 (sj roofPart35 roofPart36))))))
def t2 (i : Nat) := ck 9 (C i)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart0 : span t2 37 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart37 : span t2 82 37 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart119 : span t2 84 119 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart203 : span t2 55 203 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart258 : span t2 55 258 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart313 : span t2 22 313 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart335 : span t2 36 335 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart371 : span t2 44 371 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart415 : span t2 14 415 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart429 : span t2 31 429 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart460 : span t2 29 460 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart489 : span t2 43 489 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart532 : span t2 37 532 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart569 : span t2 38 569 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart607 : span t2 26 607 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart633 : span t2 10 633 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart643 : span t2 43 643 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart686 : span t2 71 686 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart757 : span t2 41 757 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart798 : span t2 12 798 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart810 : span t2 60 810 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart870 : span t2 15 870 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart885 : span t2 57 885 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart942 : span t2 45 942 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart987 : span t2 63 987 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1050 : span t2 28 1050 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1078 : span t2 100 1078 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1178 : span t2 53 1178 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1231 : span t2 78 1231 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1309 : span t2 79 1309 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1388 : span t2 20 1388 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1408 : span t2 70 1408 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1478 : span t2 29 1478 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1507 : span t2 36 1507 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1543 : span t2 46 1543 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1589 : span t2 16 1589 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1605 : span t2 11 1605 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1616 : span t2 12 1616 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1628 : span t2 8 1628 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1636 : span t2 12 1636 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1648 : span t2 22 1648 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1670 : span t2 24 1670 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1694 : span t2 8 1694 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1702 : span t2 18 1702 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1720 : span t2 15 1720 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1735 : span t2 7 1735 = true := by decide +kernel
lemma secondTestOK : span t2 1742 0 = true := by with_reducible exact (sj (sj (sj (sj (sj leafPart0 leafPart37) (sj leafPart119 (sj leafPart203 leafPart258))) (sj (sj leafPart313 (sj leafPart335 leafPart371)) (sj leafPart415 (sj leafPart429 leafPart460)))) (sj (sj (sj leafPart489 (sj leafPart532 leafPart569)) (sj leafPart607 (sj leafPart633 leafPart643))) (sj (sj leafPart686 (sj leafPart757 leafPart798)) (sj leafPart810 (sj leafPart870 leafPart885))))) (sj (sj (sj (sj leafPart942 leafPart987) (sj leafPart1050 (sj leafPart1078 leafPart1178))) (sj (sj leafPart1231 (sj leafPart1309 leafPart1388)) (sj leafPart1408 (sj leafPart1478 leafPart1507)))) (sj (sj (sj leafPart1543 (sj leafPart1589 leafPart1605)) (sj leafPart1616 (sj leafPart1628 leafPart1636))) (sj (sj leafPart1648 (sj leafPart1670 leafPart1694)) (sj leafPart1702 (sj leafPart1720 leafPart1735))))))
lemma upperDead (i : Nat) (hi : i < 37) : ¬NatRun (mask 145) (goal 145) 10 (B i) :=
  symCutRoot (ori_ok rho2) (spOK secondRoofOK i (Nat.zero_le _) hi)
    (fun j hj => checkpointCheck_sound closed (spOK secondTestOK j (Nat.zero_le _) hj))
theorem finChk : ¬NatRun (mask 145) (goal 145) 11 inputs :=
  symCutRoot (ori_ok rho) roof upperDead

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 12 ≤ t := by
  refine proveAtCap 7 145 11 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row28

namespace Row29
def vals : List ℕ := [1,1,1,2,2,2,4,4,4,8,8,10,10,10,10,12,12,12,12,16,16,17,17,17,17,20,20,20,20,24,24,24,28,28,28,28,28,28,28,28,28,28,28,28,28,32,32,33,33,33,33,34,34,34,34,40,40,40,42,42,42,42,42,42,42,42,42,42,42,42,42,48,48,48,49,49,49,49,49,49,49,49,49,49,49,49,49,56,56,56,56,56,56,56,56,56,56,56,56,56,64,64,64,65,65,65,65,65,65,65,65,65,65,65,65,65,65,66,66,66,66,66,66,66,66,66,66,66,66,66,66,68,68,68,68,68,68,68,68,68,68,68,68,68,68,3,5,9,3,6,18,5,6,36,9,72,11,14,26,74,13,14,44,76,18,80,19,21,25,81,21,22,52,84,25,26,88,3,5,6,9,18,29,30,36,60,72,80,92,96,36,96,35,37,41,97,35,38,50,98,41,44,104,3,5,6,9,18,36,43,46,58,72,80,96,106,50,52,112,3,5,6,9,18,36,51,53,57,72,80,96,113,3,5,6,9,18,36,57,58,60,72,80,96,120,72,80,96,3,5,6,9,18,36,67,69,72,73,80,81,96,97,3,5,6,9,18,36,67,70,72,74,80,82,96,98,3,5,6,9,18,36,69,70,72,76,80,84,96,100]
def inputs : List ℕ := [0x4b012eacb004b8e5802591f005647c1149e0000001fff80007ffc000007800001e00007,0x95ab54055009502a98ea8f100aa8852f1720007ffe000000000007ffc78000000007838,0x2ae602980a60126053205322253cc3c8f23a5fff8000000000000000000001fff1e0781c0,0x3080c2030833c818409e470416d1c10ffc0800000000000fff80007fff801fffe007fe00,0xc103040c1055d0ae872880401ae1fff0404000000000000fffffff8000001ffffff80000,0x3020c08302099e0cf07cf07ffe3001004020000000000000fffffffffffffe00000000000,0x3fc0ff03fc0fe00f004f00488bc0122288801fffffffffff0000000000000000000000000]
def scs : List ℕ := [0x1d46720c9524891,0x1d4570e8bd258a5,0x1282015c9924c92,0x19c20128a524c9b,0x20c3a1d4bd25499,0x1d44a19ca524496,0x20c3a1289925895,0x19c20128bd24c9b,0x19c4a080a5264bd,0x1283a15c9624c91,0x128200e89524492,0x20c3a19c9224495,0x15c3a20ca525496]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
def recipe7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x3640b5b051784c36579e41f6605b2d24a623557163253484a36709b604173a81b7b3a027700f5330284c19651e31e199de41169b66210ce73660c24021b9d624199ba2e5604d35700f4295185b2c6c86a2b6c0f423571b00516b602e0384da6169b6365784d0a0113b0e5d826121bc3b075d1dc5e00ccd2f6d83f335604d245f9bd2e6f83f07180bf061b051061b9bd1e0084d0602ba031399c939329c72a00b7f24181c002179c01d211de2d4f9e7340092624621be073f20907183a333329c70b5c85b26731dc011e04d050a452334084c0443ccd031b84c2d1ea66051704d03018f5263f04c1000c66220084f2a6b1b6266c8022519a7924560513e5584a12613d16006bd1394504d351e36307011b52d719b52857c1a02169b0381a1713003126395084d306e03e334e84c0d1abe3871984c2873c1504173760619257364435b270412980211d62706bce2a029d62c5705d326f0bc02169c7205c4e037334d12e6a8f505019b6071b0512d5000e030183f334b9853657b4226451be06170c005010f504179bf2a744152a53124301735b2c730f504011dc3b5185b931704d37549e8240084c031e04c3301ba3021b84d39451e32a5f85b2f01126230084c
    | 1 => 0x1b0e172733d9b62e039e52a5093036111f5071e1be2e7483e07609da07180df2b5b4d0316e83e03019b8263f1c0327483e981f35d713d9b623008172e5ab6007173bc5a03ba012799b5022104c3019cd7276c1da0702a092a5604c62541da0d2906a33181ef295fb5b033f20906029da2532a17061704d811e1e3071784c30223952e560510843017274601c28700f40717b5e3e3984b8f5d1dc07011db022104d2e3e04d335916e394284ca2169b63754a8f042104c8f1f35d88171e3261e1ca1f4a1292b6c0ba191925719199f5011b84c241b9d0051804c2a02132396ca09035b4cd0718374293604a275604c03211bf33181ee5d1e04f5a1804c0517926335604f2f18a67042104d07033a02a249ca8910ce7333185c306e1f88f1735d391e1cf20009d6346f83f24249d29817418031b9bd051e2a706211be19634f0263f1bd070a45229144ef2c718f5021984c8700ccd071704d255607313613d105009b69717b5e06180bf030083f0b18bc728013a82a06bd1031bb5a394504c041c8ea15174bf2d1826a06183a329008515a1e1be220084c22618ce3d1dc93051fbd9011e04c07018ba05021dc8c171e5031e35a5b211e40445b532d6d0f52e4084c
    | 2 => 0x6f5841e26730f50401a0901211d680011da44169b6072104d0517126240404d2d21a692b3c1858c173bc335084d2f5bb52395304d24040bf0f6005b393e1e3031784c39199cf1f6744f30541da20574e1254e89604179bd931b84d061804c06404cd334284c2d6d4cd394c05107028f52c404cd300b17e04541da601bb7f297103f2c143e7245d9c02e301c534530965b1704d051e04f226725f2d4f1e71f171f50f60340146305d3e7403f356e83e5f541da2c71c1532749b68c1b84d24040e0071bba8871b84c8f1f126266a8f50501ba00f601e707179bd021e04d256d8f52f5b92624211d229212705e5b4cd8b5bccd1f660ce396c8f52600a57070303e2e6a8f439429bd021704d2e6c8f5256c1b82938a1904169b6031704d05179c01461060191ab582901051316e83f8e1712605181bd275604f891735b071804c07404cd0d5e85d27561bd24181be02179bea5169b6041e04d03013a0061784c2d718f42d71a0924651bdb6169b62b580602a561d607179262f4dba32c731db271e1ca35733a032399c90702b53051b84d19171df126105d345bb5e03173bc334f85b30571d6256b0f530733a022171de0701ba0396c9da207f03e0708c3e065e353
    | 3 => 0x5169b60410ce0051925924651bf286e0f5264804c3d008ec2a6b0f404183d9270289d29574e72a3f04c071f126334d04c0319257b3169b689199d63074ba0071c92604193a8395084f051984d041b051276d8f502011b63a1736f061b35b2524a1a31738f53a4dba307008db8d3d9b62b6c0da27738f52d579e3061c3600717126913d9b602169d61f660ef0f00c662e249ca220c184af169b62a4d04c05179be06179c02873a09314235b05000f507031da34433602a6f8f50406bd1206704a050183e05179bf1b6305b2e748f503019b62e4e84d04170c006198c0050241506169b624211bd291735b03010f587211bf276f83f051103604199d6981f126933e1da277383f071f35e071e04f051735b0f5f85b04181bd2c16b682550924871b9bd2e313d1264084c6906bd13302af73670ba0246d3a03258060071b35b156102a226782f393dccc1f3dcd306028f5126005b3657ba69960c1e041b84c391b9cf061ba5c35573d188171e50e5a9c705011b6051f126061fb5b2d718f55f109292c731b69e6085d366f03e276a8f56617142241b9ba07181bd37580602f6d9b846169b6263f1bf5e104d3231b9ba162a2cd021e04c06179bd25573d10702415
    | 4 => 0x1e6585d811704d2c018e5246e209353b1292a56259200084c04008f5255604d27739dc2e749b8355705d275304c071092924044ce2a5604d02211be07181bf931e1e306000f507104d3071d37f305705d061c81807029db052104d2e74ba02e6b0f533309262453ce135730f5266a8f42e5304c07023a0071ba04051c0c3363404a055b1dc1f5d1d50119c3e255705d30730f502169b607018f5244f36030541dc04211be2d1a2673174ba05f10ce72066bd32b5fbd1721c3601f6704a2b5802a061e04d1361c1f03009b6072104c25730f505173521f49ce0201cb70061cb5d621735b393f04c06029dc23640602a5806004183a382169c7011804c5c00ccd061b84d2e6c9db932104d37028c9266a8fb21011b02a309262a561bf245d9be241b84c07000f5070183f227f0f52773ccd24009261a53b51290185107179bf30213642e038c13543926075b4cd051810526239ce345b35d255084f336c0f50617126264e9be2a6d8f58c2104d3a7003f221b9ba04211bf051092924040df07199e307104e18e199d60e19c3e2d5784d2c51926195c219345b126070083e071cb7f1a01926256c1b6985d1da2f5b12694169c707030f5393484a1f6606004023a0
    | 5 => 0x1f66860061c0c3065b1dc394284d2a6a8f5285dbd106194e9275312403179be2c5185b246e0f526451bd127ab0b07181d60408c3e2d57bd02e0384f42169b62857b42015a9b63950b2e06181be8217418300736d391726a330cc5e041e1be6a08c3e3d60be7070203e244c0511f7d0f522471c96b1f35e24211be25731dcaa169b649169b6031984d317483e333f04c07008f5363e35b1e6505c06211e3295f851261e9ca051e04d264284c0824919071a0732c3584a2010ce3256d9b6045a9b62a008c3041784c011e04f2d1f267336d8f50a17c17194026166109292a722093a6e3a00400ccd2d710032c733a021019d58560c1e071c0c329571d6041984c03179bf363b92918019265b1b84d06109292a6b0f50518142031bbd004011da261e1cf05541dc2d111f51f7d1da07029b7070083f355c35b04019b81f664662556051031f4d0125f85b06179be104084b031735a05023a02a54126387183e04194e92a5084d8c1725c245b4cd50169c7a8169b618008173003147241b9bd071984c001c818871e1be394e84d264504c1b01926031b84d0219b4d8810929031f126061984d2e3105d255604f063e1dab8169b6126135d05199e5395325c207d8f5
    | 6 => 0x26481be33330606610ce724249d3ac169b6041b9d62d6c9dc812104d2a3105d2e0304d071e04c81192573356051032104c241e1be36738f52957c1a04010f507541da805b1dc2a5304d2c7083f9341ccd021ba5c981a926334284d05212a7031e25c615b4cd1f199ba67633552b718f5881e1e32e4e84c251b9df055a9b5011984d032104d66541dc9a5ebd127040d52b5b3a88d3f209243d8151f4a929071a3600702c1504020f506541dc394084d061b8c0355d35b8810ce7396a8f52d149f50e5d90f2c5205d305d35b051a9265a1b84c26481bf206605b71183a304169b0245607378031dc7a3d9b6334e84d2a5092436739da30748f50401ccd1e1b9ba2d6d3a026429bd6d20424071e04d396b0f5351ab7005213d0265cb5b8c06bd13754b6105019dc254301731710f4306e1dc3a173592f6d83e882104d07208e83332860031984c051b84c24561d606199e5286e3a00419261297383e062104c063d9b629541da235333a39409e3051e04c05008f51c019261f7d2732e3f04c02212f735381c9041804c391e1cd2e749b712791dc051ab5f300392607018bc011b84d45169b62a0a17a2f00926070103e062104d21014f526531be885a9b66a17126
    | 7 => 0x310929201b9ba172cccd230084d2b01126030083e811bbd02e5604c3e7403e061ab5d89109293771415393f1d6945d1dc061b84c051834d2e0384c05020f58c1704d336b83e041cb5d296505129738f504021dc3258a18217f83f6d19c2423579b0041f12629771da041baf703199e40706bd1336a8f50117138255084d811b84d305584a0619c3e3541926012104d3d57c66073e3a02f74ba0261e9cc2f19a793516b642e4bb3b061bb4d2b5b35d30419263204089071935207211be2a71c15393f1be05211bf0417126334e05b031e04d02013a02b5bccd26561beb0169b6075a9b5351f35730144d953173522b5b126051b0516402209334084d8c171e3071ab5d5b1e1e36210929254e84d2d2526a071b84c394084c03169b607020f506541da24181d42000c7f5a1b9bd3950a5c2f7483e396a8f439409d6011984c875b4cd071a92666541da336c1b60f0144f161d123041e04f0e3d9c7336b0f5021784c035d1dc0719c3e2c6e8f5051fb5b020103e6641ccd81199e5387183f061f1261f499291f7d1b8b2169b603192592010cdd051c9260641ccd061725c031735d07031b6393f1bf5c1bba81e00929071741802181d6241c818031804c2d3c185
    | _ => 0
  let q := fld packed 28 (i % 128)
  (prefixGates (q &&& 2047) <<< 24) ||| (thirdGate ((q >>> 11) &&& 511) <<< 12) ||| fourthGate (q >>> 20)
def finger7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xee4839a3a423b5f81b1229d27f2576af6d2e3ad7f4163d3216cd7747152eca635f5d2ee0cbf269aab84a610ac6cd3917c2aa99b36a1e259f30c5163f80ef55b23627f59961c594cb11c94e05d03e608f8ae6a6b8faf43c48d72215823b99eaa4cffa1d8de6880aefcd4f3185d6cdde1d1dc79e4df3ac5ee7238fac5e9a6cbed2
    | 1 => 0xaf6494f23207e0ba7136e15a4bae2cb42b2b61bd7deb26be7974aaa4e5f77181c0ba43954bfa9434048b192d06e23af9ac7c4cf13febcce5bdd1c167280bac893822b954b3210abccf9fcfe8ae73da3945464591afd85d0816c5573e63f7d2dc880130e280ec24c5012fd0404c8038e4d5b56ddd6fa40b07fc05394965fc919f
    | 2 => 0xc0be80c12235e41931763a17031ee7a1f4559e7a779a670d6d5a11e7a75a57791bf928ebc1ba2a8f480319188937c5f8a417a82c65184c7ab01037b7eaaca4a42dd3cfcc100689949229c33690e7f06c0a6e54a170201722c2d5562e936b9472cfacb7500884ecb77ab61ecc2c8d2e327766c80524f411f4a1a4d8fc224f5630
    | 3 => 0xbd6968f46d5b83f8ed80c00f5fec955bf739d3da0ff26f58adb07ba9345271b0f2daf78c64a7e70e33d9c419e87e746ccf19186c50653e9b67e1cdb58b780d880460e98b7673c045c058f3cc66781c2e115dc77b4eda8aa5a93ec06c6cfd0a342ca0af4e98a44971385f12e884cccc4aa7f6d0a26d5cba30468153a8e4674ecd
    | 4 => 0xb3651f5423ba2df657f7f38191fc446a6c753921af56f7e05836419d0fd5fd53185b458294e9982788750bcd5944726914fd0bae0bb46cd8232d1d0686e01e12d21e4fee4e82d7d5adb871debb6e9bcb9383a266e692709dee4fb47c0c6cfac59d8128081f82f59c105c12afa7d81539f7629345fd587b954259734c7f59f30e
    | 5 => 0xba17efba1f1f6df81d6e546d7820bacaf79ef76e079024af8daa6d99133f459cb69dc823aaac4af41745ad51d34ed3f8b446082845237660fbe51ea3533cb993d88e6f7ba6985e413ebd7861fdb7e1631c264dcc7d35986095a6a45b8a14cf11be16333520e1ba168be50888b97dc7cf1b56aa06329c66fab3b81aadc711b9af
    | 6 => 0xda79ea57a6d70db90cc485cef393c3f746d7c16ea630f5490d7ec8d87b61f8a1316bdc5ac08ad6e44dba6c2657a801ddd2fcddcacb2c4daca7405d4d7acb8e33e5717171bb900cc7a0bdcb944523da54d119fba5a075e49efcd6433c864f3619421a284766e5259538feaedc77f325bc3eec8356bba67e91cbde373e63a62237
    | 7 => 0xb6ac3cd233bc79209de7a8f2ddbda06639e51b94bd0715fa0b1e86f6c31bdc29fc27930761e28443043d84771c832b9e39ccb926139c4d9b5eca234e59f5a443a54847514aa18cc0b22ede7d4190e543682c7cc40c640eed9099fca6aa5a872be3ccdce5f062c91527409a94e1d2f2c2e92d6114965a53fe3d297d7929818273
    | _ => 0
  fld packed 8 (i % 128)
def recipe8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x470d102ba0788015b1260341a1d123043a87a2090412a4d18546ce1030d78205d033cc034240405b03051041382a8bc7fba00441e0519d2d05c71ba0028be0a16b03b5e041266184a2a0f5249b97183e4b9911f36c1c0e32e9792b8f55785d5c219034156102a67c403d81573209041be481bd301c5040ae134eb749b55632e252212d9b8739db249dd06bd167a5f66c1e5f3411e1bd45b60761dc5a81d54c2301b2d5f04d6441f2eba05084c4704b2a83f19bfd5785c040ea7dba0211e46c9dc4e8962297b2113c288ba5604c6085b328600435f651be01a1766926021c95b04d540ca028b6040c01f3575f0512d8ba67ba8769b8388314935c640601b84c0335d03c15020f5033a803c18681751da623904b0dc350293857ba61e26e5f1e31a926761b5573d1790f56c0f4169b0031267083e461294104f19bad5f84f0b16d
    | 1 => 0x179d0039650404f471785a851211b9039e30192662ba30337602126531be7d83e4504f7a0f57f83e0404d761b75205d783a00285d011b8013d12883e62051451bd03aa72217f043be5185b5093a5705d2121d758f5012190184c5f1e503a573f0604bb3b33a5f798db53012040e2038f3040517a80167454211be0f93f730f5708f55a9d6199a8448d21cb6e6e03f659243eb5203bd86184b034e6041242e83e1f358249f0760f44284c5802a6d9b80284c219cd0335a41b520243e67c2503138769b7043bd0385b028dc64c3a1fbb34635d1a21c1a19a179ba6d0bc0136001ce1042a703926740bc7f03e43b5d7883e650515b33b3e926731da0205d7c83f46126520ca179d27e0025ebb6561bd211bf7d0f40304d030ae0435143926020863a92938a191033d679621836a7903f02b74033be043d800896219ca1b0514504c
    | 2 => 0x3298f1792660bd15705b7a83e6482d01bbe3a92a670603f9e3030604384a509851ba6e4444f508e908c3e029c0749b64f3606c0f56704b6704a6837f4084a034d1381eb0b96a1e1be1fa937e3a00383e7983e61860703a0034e00325c03b5a438886b0f502124743a002a09043761936a030d15c84d6782c238ec6d9b7561e348341039635d1da02a046bba0038ce290f41784c1fb6300851420517f03f0ac3e36a18043bc0384f541d56d0f502bd267c5258060038db022a7481bf1b270731b5029b0589c81c223720f5261aa661e75504a758fa5632d2b03e033d34284d2f4d20409922b651da63429bd7cba001b523185c280f410c82033a0029c7022101fb655c35b04142114ee0435a01af7043aa038514eba6791db03c245084d6305b4dccf1ac736f8f45f1c5241831704d7a03e023be550604e8d14225e0392403968
    | 3 => 0x299da573d81f36f01b3b0b44f179c00084c65ba3758f4039da2b0f51bc3b03b553ea161e9ee430175d05b191ca03b54400726685d6716702415041e85f84c611110292a2c3a06f03f559797c83e1bb725c04f029c90200b02bda03b537a03f031d65005d6a8fa021327c35301124040607c0f450851031b003ce7028f54200f0084f4184b6d0f459950043402b03f03bd36105d508c01f16c668ee619e84e8bf7d8f56b1b5560517f8f5528606ba090425c718f5633552b35467c8c288f5561be7c209518ca02b4d03bd65f35b6e8f503147179bd040ef189ed01bed3f84d728ba6484a1da45149f57983f413740303e418f003203579e7021b6778f55a98e041d6031e466060339e802b5503b760204f0b97b7b83e039b03984b6804b74002019c06e2096617649926028ca2e8f52883f6605b7403e5604d2dc154284a0204d
    | 4 => 0x6141f5cb5b33976029292e03e5c189019e80b16a6f0f52534b02cd31f35d721b76d83e7c8f50304c7d9b85f0ee719b8030f56305d03bd11cb5d02b9f2d3a00435b0289d1b84d759b63e9c53e84c5a9854504d021382900363a162b1b55cba3588d47b8f51735d1c926010ed788db6085d731b65d84d203dd5c04c2133e788f50cc5e5804a0286d0381a5b051639e82dba01d180171266685c7a8f54d3d2798f5043a9029be03374780f52b4cd3105d57bbc530e35a9895b124298f5029b56b8f53b929018c03f04c4604b083e2169b6038f54184a7e83e451e316a6c4e84d7c0f5019bf6d8f4458181f35e1a34619362191cd719b5644181e04f03353034e84504b5d1dc01bac731b70104f02ccd038604a0d6770fb509881c34921a1a6b1b803bd01eb606b83f1793c4f1e72983f19c281c3606e0f50383f0104d779b54ace0
    | 5 => 0x249d0040e566860211e31984c61418029d51fb626204f2e353168187d04b5916e73b537e8f5309260408931114040424ebbd2d03e2242b508e000a591da6b18b620304006bce4b9894ac2426bf510929039290305c6b1b60a17c03b74028125d92402c1463c66031bd034d0104d36784a1925f2a095029db2a03e0404c0b4354d1d622cc31da6c32c1e573be023a0083e042479040dc7c1dc7283e239ce043d9031542121b018f522b643b92a513a357c1a040c52c83e7ab0b5804b721b63e1da034cd7e0f50416f04ced1e16b5405b2906a07be1034f52a83e5c185580c9740f56504c0a3fd6a8f40305d6b1b76e8db5304f579e33c036208c946b5b481d6183ce4e05b5f05d78002000f5031555c85b039b51c818134ec03042179bf6504d019da009245b4cd563a90312a4e84c5b1eb2ecd26d1b7028e9489247003e684bc
    | 6 => 0x679c72c8f5733a00385c021b01f267571d6541dc03418680d1039b73684a03cd01fb567f83f2a8f55304c0103e0384a17a620409604031768f50113b6e83f1e1e36c9da579e87ec150334d508c23e1260204c03a5f544df02ce9681c8019dc0205c211f2039d5290f52c83f2c0f5490216c8022a2cd0203e02cbc02203588e80287b5b4d02104c1da647d0f52e0f54b905028ba3d9b6040401e1ba6505c0385d008f53484a551c70405c4496565bd14d04c6504f6a8f55b0ae2236d041bd6005b2104d34a18418cf0185b4818803842023742c03f1f36d5485d560731da656e83e2b1dc73c154cbd2028bc1f36b031c0031292a03f1c96b7483e7883f7383f543d81736d029b7028012d0f4530c3034d3459293e9c04d0df73b550384c7b9b84b9850184f03c3e199d660bd22b0f4042f7038ba5604f4eaf766361719b70405d
    | 7 => 0x34e92b80145cd31c2255d103481855000e7d1b8238cc641c7169c75c1242491f028ae031b62126f66b5f0203f3384a4804c6d3a0192611ac24748f5563d63e9be249192a354788f41e20c19a1d389eb7183f1e04c144d86f83f5084f03bed02040038ca211d6579e45841e251ed7b0f53a1854818971003769b5544d30335f4533b03b413e04d5bb5d65bd201a5c571c50084d019db5f05c7b3a0012090434d5904b039c00081702bd0144d602c1518b453e85c2d0f55b926720f45005c3343e03a12280f5211bd0519a56204044bc5e9264601c6f8f502a5c1c3486f415764cd760f5028600b180181a63b1290402d7f0f5022094084c4484a013a057bf15241a040ca649c72d8f53acd3651e4208e86e3a00cc3b3384b1b9de571292e4cd011c726b6541210728f5038405f8517a0ba038da041605c33b14cd57d27301c4f
    | _ => 0
  let q := fld packed 20 (i % 128)
  (prefixGates (q &&& 2047) <<< 12) ||| thirdGate (q >>> 11)
def finger8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x1f48e0c59ed3275f5e5951e44b6b973af1396e50dff2b4fa89664f274d18d62c29392e3f8fd591aa8b725ec7f8560a3fb9229abe4feecd9fc14c0d3fbe80826ca8939421816631fc8a424a055ba8eef6d409a691203a9b887fad285e8b8859e07cabc5df9d885cefcddaac0a719afcea68f62a4d7c1153b923d8bc8dca6c3465
    | 1 => 0x233428fea9cfca523a2e308a74c65f34788450ac4deb0827f25140512dc7214b1ad82fd7ae647fe6bc08ed41cc3e303aac50c7ab8ec5fe75ce4133699f0bf5054bca9d9a4a67df2af39dddf6f0a67bf3e2685742097d35b8509f85e0e0c9b89357feca5e52b8beb8c6ce2a204c622bf8b0364da0eb457ad851a8deaef659913a
    | 2 => 0x7dbe5b8b1e5534ec2f118e261a9aae2df4058a1bc653b84782afe4a5a789f279272c3434f9f9331afc6a197b6037cb69a46279e63f18b8d2a974374f068d6ca4cbd8e18edeadec86928e5ee4de172af2959c3019a2aba5dcaff18f11a3b1ddb91b524d50aa2f875ddf0842c7e9f792329f273887907881f9a136be3aaa58b018
    | 3 => 0x67a6eadd6d5b068a8ffd924f5fa57f3fcb66d36c2fd66f09975fd6c2b766361223c9559b64e912e2d079f176db731e1f251925b9da2aae9aade442268648def561311d21bfca48cbc0018f1488f13bcdfb2a38b84ef4b3887a98c102aef3e3343dd4714efa34570a3eec12362f4dd064e43cc7fd9a99f89ef22f1b9ae0b32781
    | 4 => 0x9dafd6e2382122a14132181b64eae2b8744ef214365f7a6c33ce19d5976de31f79d37b0a99149bf8875b1829548a97af20b141489132fe3cc5974064a0db9136560f27d2a829f414a3ace30ca9ce90ad837a266142290d1e6f3f642de6cfcd039e2b2081f63269c34e6a5af96ade0ae53e43e9dfde301d8e9a7739a7ff71334
    | 5 => 0x1aaebcba1f23dc87f50e5415360e114be9336202a707d0c23318c26178be8d9cb97599d3fade5b6e2d42ab51dd4e6ff83b78c3c77362928ffbf78a7b10f3af8aa71a6f42426f51537c31d216fdb7c3891e4f05b527f60867413bb870bd973961e7733835d316aaa32b1d08bd4c7dc71e1556af06c49c1cdce462dbfd765e536a
    | 6 => 0xf06bf57dca6dbbb9a3018591b31ee5f50ad743e178608621507ed4e7b71b2aad81b6be9a6d8a57882b0484d2b1f4b7ddaf7f2876982ca05b10b1f04d11250e9fe5534cc2af8d39701ad87d8f1823d37e95bd1d4aebf32cd268f1cc10edf81c517429b41d7129228438fec950292a06520733e35f86317eeb556837e1bcd5eae4
    | 7 => 0xa0b13f7ca0aad8819d2fb3201fefa0ba80e5e03e0e07150a3b5feff1d08e382b6427935bf2e218f204bb873502dec3819d35d0ee39b20233a6b6c94e7864c4682359f548b9a140e6947ecb29c70daf4353c0fc144dd3ac6e4945645bb91e98b0cacc315df028c039352a4d8ee1f50f3762f1a6550fc9e2c89df245403aae9962
    | _ => 0
  fld packed 8 (i % 128)
def count (s : Nat) : Nat := if s = 7 ∨ s = 8 then 1024 else 0

def board : Nat → Nat → List Nat
  | 7, i => cpBoard (mask 145) inputs 4 (recipe7 i)
  | 8, i => cpBoard (mask 145) inputs 3 (recipe8 i)
  | _, _ => []
def atFinger (table : Nat → Nat) (ws : List Nat) : Option Nat :=
  let h := hk ws
  let i := h % 1024
  if table i == h / 1024 % 254 + 1 then some i else none

def lookup : Nat → List Nat → Option Nat
  | 7, ws => atFinger finger7 ws
  | 8, ws => atFinger finger8 ws
  | _, _ => none
def ck := checkpointCheck 145 scs count board lookup
def pan (s i : Nat) := ck s (board s i)
set_option maxHeartbeats 50000000 in
lemma block7_0 : span (pan 7) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_64 : span (pan 7) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_128 : span (pan 7) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_192 : span (pan 7) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_256 : span (pan 7) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_320 : span (pan 7) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_384 : span (pan 7) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_448 : span (pan 7) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_512 : span (pan 7) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_576 : span (pan 7) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_640 : span (pan 7) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_704 : span (pan 7) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_768 : span (pan 7) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_832 : span (pan 7) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_896 : span (pan 7) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_960 : span (pan 7) 64 960 = true := by decide +kernel
lemma good7 : span (pan 7) 1024 0 = true := by with_reducible exact (sj (sj (sj (sj block7_0 block7_64) (sj block7_128 block7_192)) (sj (sj block7_256 block7_320) (sj block7_384 block7_448))) (sj (sj (sj block7_512 block7_576) (sj block7_640 block7_704)) (sj (sj block7_768 block7_832) (sj block7_896 block7_960))))
set_option maxHeartbeats 50000000 in
lemma block8_0 : span (pan 8) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_64 : span (pan 8) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_128 : span (pan 8) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_192 : span (pan 8) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_256 : span (pan 8) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_320 : span (pan 8) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_384 : span (pan 8) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_448 : span (pan 8) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_512 : span (pan 8) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_576 : span (pan 8) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_640 : span (pan 8) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_704 : span (pan 8) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_768 : span (pan 8) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_832 : span (pan 8) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_896 : span (pan 8) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_960 : span (pan 8) 64 960 = true := by decide +kernel
lemma good8 : span (pan 8) 1024 0 = true := by with_reducible exact (sj (sj (sj (sj block8_0 block8_64) (sj block8_128 block8_192)) (sj (sj block8_256 block8_320) (sj block8_384 block8_448))) (sj (sj (sj block8_512 block8_576) (sj block8_640 block8_704)) (sj (sj block8_768 block8_832) (sj block8_896 block8_960))))
theorem closed : ∀ s i, i < count s → ck s (board s i) = true := by
  intro s i hi
  by_cases h7 : s=7
  · subst s
    exact spOK good7 i (Nat.zero_le _) hi
  by_cases h8 : s=8
  · subst s
    exact spOK good8 i (Nat.zero_le _) hi
  simp [count,h7,h8] at hi
def rho (ys : List Nat) : List Nat :=
  let a := fld 0xa642008424c080416a3045606004d40410d260b00b68b011 3 (bsr 0xfb1e0242e5fbb754e4578a26dedbcf48db58da58d6f67d87d01a17a5cdcb4769cc699b04ca2bb017c75a8d58c7065f89c36964cdc06437d3bf7ea796bedd3a3cba2a6b7eb9d5cf37b9c19f56b87ddabdb8150e95b297db70afe0a9b8ad3abd9bab3198cca40fb604a33e10cda11498099ff1daf193c305ad9196233f82cdc3487bce97e879c9fd3b70d90a6c6b5bd747656919bf65250aa663039633607708f15e4112b15b37383a589afe2c5230a7b74ec3fbb14c26dc6242d98db4401a06353937667136708df531b323aa2e2779bc2b6cd9ce2a222d6b29b832402845105b238b879f1e7ebf48129b800a0eda5e770ccd94de0b2fc92f07ad7b9b06fa3e4d 32 (hk ys) 7 0 64)
  if a=0 || 5<a then [] else
    let c := fld 0x33b023a3a42ce5056ae2074aca000000 21 a
    vals.map (fun v => fld 0xf400000000000001ceda0000000000035c00ca0000001210031d86bd0000000bc0000000b00000000ad0044552a50000000a30027e029b00435fe837f1d4ce640000000b90034dc65700001c4ac70b1894470034800a2688e98437003158299600cc5e2d002dd6c2000279501d002ad4e19532582a1300275400f4e02d26090025524064880c0000 9 (orbitLabel c v))
def B (i : Nat) := mv (mask 145) (fld 0x506f30f31e30502f43e10403000e63f60e43105505f63106400406102e40f10e60 12 i) inputs
def I (ys : List Nat) := bsr 0xd6f67d87d01a17a5cdcb4769c75a8d58bf7ea796bedd3a3cb9d5cf37b9c19f56b8150e95a33e10cd82cdc34879c9fd3b70d90a6c6b5bd7475e4112b1589afe2c4ec3fbb136708df52b6cd9ce2a222d6b0ccd94de0b2fc92f 32 (hk ys) 5 0 22
set_option maxRecDepth 10000 in
lemma roof : bar 145 (cutB 10 inputs B) (cutN 10 22) (fun _ => I) (rowOrient 145 rho) scs 11 0 = true := by decide +kernel
def nextRecipe (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0x1720839844a0e210717118b9445c622e6317298b98448000a6007300b9c014a0ce0307284b9c214c10e60508228c854204a72152802bdd55eecaf733f30abdc09ccaa00052822bd954a04af6157b1abd81480cae7657a8abd4d5ea0a405573aab9947c86a5054f2a239955e42af145789abc415ce2ae510f2a2bcc0bca8ae530732a941cdca8ae135721ab98c5c4aae6152002a9815cc0aa7067302b9c15ca02a6017300a9425ca02e5057180b901f4c0fe6017183f90254812e404508458423c208610470857842ac20fe30
    | 1 => 0x7fb0bfd81e80cfe767f9a3fcc5fe60f4037f39bf98c7c42f5034f10a38c9fea8ff427fa0bfd01dc64ce430f1097881fc620e317a839b885fc82f4000d300798274c13e606702028c01c60fe70a5285394042022b211081884144204272113b0094005ee82f7617b98bdc85ee22f7517b80901c400025011281894145ec42f6412810bd945ec62f6117b0090185cec2f4217a28bd0c5e822f4012020b9d05cc821041282084184a0c2f2517918bc845e402e7217210bd4c5ea22f5012028b9d43ca22f3012018b90c5ce62f10
    | 2 => 0x37881541ca20e0502008155000c800750038802d40162013a509f2856882bc406e108b010f8063c0536039f01869003c8106038701c8406564321028309c9c864e81276093b8494025ee72f755f289f84e5ee04e522d20494064a052f6597a2cbd0c7c631e424f20a394a1c272f5397a8cbd42480b2e759791cbc85dc04c6136709879065e6124039739979001ca325073720cb94e48015a50af281b9028c074e030910bc4082c42f1057ba83dcc1eec0f7707a803fdcdfeecbe313f21bfdc09c645a207a813fd8dea0aff64
    | 3 => 0x58815400aa085f652f9a97cc868025503288315418bea85f522fa815014bcea5f422fa015010bce814012a01150010c049e0147011f80cec060b210080804140e420f23079303c841e4a0f200000014000a02050507bb03d181e86010402820041c0a0e0f6507b183d841ec00406071303d4c1ea20f500202838941e620f3002018388c1e200400ab882c408e2055f105a811d4088a00410030000d418620d15073281a54190a0e650630834141cdea9350737a15141cde835f5037a03941cc808c50260810541c220f5f20
    | 4 => 0x72002e815640abe055b02a18153c088e053d10b04058e28c75063b81d8859e48cf265f129f8849c0a46056281b14018a02cf7667ab0f98d8a0a9e64473ab3d859ec0cf6467b1b10199c4ccf14678233c4d9e06cf1062004e9027c8116041f01c7810220a1f730fbb07dc03ee21f740a03840002a0415000fb1854143ec81f600fb0850183cec1f340f9807cc4220615030883054183ea81f400fa107d0428081e740a0002cc034601e300d38079c256602b305f01ad80cfc087604ad902acc0a2085f722fba97dc0bee84402
    | 5 => 0x5b04ad40fc0c76065f032d81914809e304720429421ca01b409882cfdd27eed3f709fb8cfdd57ea67f1427a9b7cc66a0735019a814d4027ecb35059fb04fd8a7ec33f459fa04fd087e651f434fa123d4e7ea10f149fa9cfc0e6800c7049d384f9c29ee74f75a7b82fd44fe264f522da0514068a054500a7b2d3d147e631f424fa0a3d4a9ea10f13a7a9d3d469e073f23a20031c0c16a14a70a73856d41f6802b5077b9bbdd5680a740122029d805ca04e50077b2bbd146806e5044a0221015dea0ef5377a939015de06ef02
    | 6 => 0x18000d40a36c23f501a820fd4c7ea234051f32c5c522e251f108fb8c7dda3ee0b5043a82914106a0115038fb00fc0e3e083f018f810d00228011a701f30479c234c03e508f3021c090e0a87104fb1a2dc53ec09f6138839041d20009502438a254150e2a8712478823dd11ee28f7047b91d41c8a0e80004281a14193e608f4018828d4152a0685044f80a3c093e088f054080a100114e09e60473841c0e1eeb0f7687b82fd94fec24f656fa1c14121ec1050287b0c14021ea03f438282a7d511ecb0f03820032d8214e10e70
    | 7 => 0x2ed458606cb0318814edc436641b429da14dc8c6208910585b942d4a0e46f35061a848d01e660c37091b03cd8046c0b7233b91c8dc1e6e08b10508008401e20121000db822dc16e0d1b703b831dc0d7e06bf065f91afc15680047023f821fc18fe487f263f819fc8ce800470595b83edc156e02b70278113c1488000b2001880040216c0110060805040262011b6080803ed8056c0ab6045a042d4276801b307d980ad0156a117048b8145c4236e23f651fb00fd847ec63406
    | _ => 0
  fld v 17 (i % 96)
def C (i : Nat) :=
  let d := nextRecipe i
  mv (mask 145) (d % 4096) (B (d/4096))
def nextCodes (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0x6b997e0ee21e04d79c7d8920000000988000d702b366cd6dd12123a86e46f65960002e51613b670b102cac6ed4464f00027d602ce552550000000365197e56e0000cf00017da0001f62220f0c508000000183ab575b7bc694e42d839e0819240000ca8c5fcfe0fd42750001f0fb6f0005070f001ac18e80017b2b53bce2668260a140b48f8c79a7ed7a502a9648440388901c0008ee549b465c2e8b1
    | 1 => 0x6010001af2df54ad99e68fdf047696c9421e9bc00031d8000000c9336a4478fee1b91d54fb20004d692ded460000a7998cbc000017f800000000072f55dd2301fd0fdac2000006338d013215ea0d00000023e60005be1c2050a6d95ad3d70c462bd15e3529c961974439478001b28376a171b3cd3dc1cbbb4ead8065ed18f035ec736e20208001ee92f5c7bc94089518a80010a600017403ac00008a
    | 2 => 0x23b1e94b2e86a1f58c28bc00001cf12945d091e91ea56a496c966fc383887c7d400c2df800068758e1a742e6a9c237000152628000036382381900003ffc000feb64b3f28a509cc00030940007a600053d5a9ef4ba3407eb68c20e352247c0e28ab53ab90d3485c86f34e00ff099520d33443181cbb12800001a4bc685a9dc0004040000ab932dd954019ce4001d784fa8001b0600057afd54000d69
    | 3 => 0x8a59d0c0013032040001582d591939a3872aaef5710b48a360980b93f9d7a200013e000143461f000233cb94e0b1393864e809a91dd0649928a785be23d54b26e01a80e19aa00000961d905780002313fe04a3d5b77616fcf4673185916450aa0004e3dd0040a00049d16688aa53e44ea54cdf400082318ccfa004615f1b49b8e13800d80742da5c72a52675f5aa0a00047e13741a738e0620b26bf7
    | 4 => 0x78aa7507a612503a0000d3b18d33ca1d687e0fa2e128b8000bd95ef746e99a9fc7fe8914000c722810cf40008d30833ec1d3c591d1dce6d416c3e113b35cecee4a36d0a917b654e4f38e24f9525ae808001f140007b62ba5762a9c0bd0d2418f6e982408138ca7f993ea70296634939f0a8516217570b8cc8d729092e50002ea246259cb274000a090740001988c3e0b80001008b960b935e0ce03b8
    | 5 => 0x43db4f991a0e630eaa0800021000024b000005916816e007c62a499ff44c7658548b000090e0000003854000cc46a804780007753b53db16263f326786dc24659278af7a9ad2e490ff0003d762f41b811a122c0001588769008ad1b08952c000bcecbb8844349dc16767b19cde020c2400000006a559ba85cace000ccf92f635a21200059c13eefea2d254e418842a1348bb4dedfb7000341d1c48f5
    | 6 => 0x3dfdc8896f0a79655f4a2e3000000145a59cab3ad4400036962277c1ae2e376d799e55e40004a28424001a7f6b7fa94000bf936631815642682150000308abb39aaa6c00054f6650000001871fbe15b816a3d41f14c39bc800027c892701739c00054ec000c934f0b37cce80000e01751b26b210b52559be085c556eabf4a85fa7ab9c39bfeb4469f21b00e4b5616200000000000e413242e6136
    | 7 => 0x488018b174db000164efce0005c000002282829a521b1f0200000010417640005ce9ecdb287be000341caea0005c02ed7c020003d119304a20003fdaf1c9bc65e1a7b21800046371ab0843d6e442c08b54000000240800149c8f4322000147450cf5191f9a6972c338dc7ace62162ca04980013b649593e463ea8a5058f0400058e0004d05656b8c00002bd0507a40000c38ebc6ee2832745382100
    | 8 => 0x8100000001e704d000076eb1100010dc0000de338c2929fa441611173cba485d66b09b80010ae0762699ef5c9a4b9929082e33123db9f830a7a0602e899dcc22600005a800000000027558a1bea8cbaf44474e08d4f8ea84b0cb87e60b126b69f800000000000000b2ba5c7aee497632ffcfd334d3aa08286b69538ff80005de8320001970000aa9b3aa738cf253128680008f02e54aa9abc0f2620
    | 9 => 0xc8001b5a0ab676f679f540002c8a2c0f0c64f018b4400017f33398001bea0efe8e92bc0000000000b2e81137200c0000001c0ef7380000000b50002d814f22f35b73520f065a02fc2d44436dbb4c3c151e9b6b654bcf6090ab14000393199604b2aa912c000000770c0dd5a67017d091dc000cb20000728a38e1fa0780007bbfb60c880011c2f9000000008f86d1297055860beb219f800072eb54
    | 10 => 0x2e46354c6c0007d36eac3c24ee849f9ad02ef1b31ea2807c437d065856413a00078367d483870e15e000088653df6ca1bc00014a0b00000c2657b00016481e630661e00cce000ad12aa8bcd484ce9f5bb118fc6aed60270df7e000d0207a4000845104880dd988583aeafa5fd9322916805415348e7f41f89d960000000002e38c7500012363120f10000cfcb1a38edf00d3c001d8e64f2934000283
    | 11 => 0x28649200005dcb57fb220633040d2c8de0f130613c5d02b9f66c0000bca000156a53c13e0000000000000a2c0003fa5c6ae610000058a9c0000190001e820003ba3b5194e00072c0c5c00013200000000000004a6800397c7774cf00011405110003fc4890dc04613f2885200034e000084ec4b75e375f98e2f16c1aa81f5cdca00011b9b880cb0001fb3c4a0300003ecc82a5634cc30e45ccb45
    | 12 => 0xfda8568d2e0000004f68e14f58e9db04fe90c8d5e6ae7a2fcf684f6800136e7c800024835b8cce0002720920000000000326200037fb6e00001fe35c2d14001f1b000491732032e66600003a820765e0b9c0000003aa83d0c92ea361a4cbc001f6737a04c80006501f1aab1f20acb3876d50000e2808eb2ec000f03036318e4c64a058d80003628ea24c563d25e5f55963cf849e5790001ec0001201
    | 13 => 0xfc00010d044500000001e0cc0db56da800098b5e59ddd7b0e230003948abe51135887a4000598afd9e3d09a4370005775206d9e00028a0000a0472f470e194000d8d903808048410701244af5838149b4ddf5c565b3dec000000e00019fdc4205a3751eac1e07e10003ea5ba445d0fe824d23ef626c1ab0c0000002348888fece99307aaa042e36a3b025fc0000003ae291c4607c8025976cd0a000
    | 14 => 0x1b7971000000022500007b2409bdd8001bed90b6534000178000000000000045795eeb7e5140000000eca00060a85c06e400001301002748a25c9017ccc40a86641f19a071840001f555ae92d0002670212f0265c10c41ed3292f40001c420004a82c0bb2e3fe610e8d5f6c0000259f7569a00fd71e7b18e6000c1c824c00000024bb4d8cd699600012a051a2829731f9b27ade90d500000013f3
    | 15 => 0x7cdb7800066b2ab2efcfd258628d0001e72000696427efbc07c12229b9646e302e7800346435d65431e4b2445500003417a40002db0000e420e54a0800310000045f8e3cb16d73196b43800095d7c72d4f9ca1a40941bf0ce8a641a900029268fe54524882e03983142b582dc0d5718292805c74700028e449a3cb23d9c50bd6d15198946c97471d8c100014d49c9c10654d890ba900014e1d3e000
    | 16 => 0x3633b344fe0340001db98280ff98c1114000a8f2f030342200140003254000efde93ef742f42862cb000099481d0e10003d9400076e19943b20004f28000f1e5c3299ad64000c00157968808ce6600033bd0e44251bba6586400003b0800002e5ce73c80000005000000000620e9a41e67f40000000b68654000d0071b0001b92b4c000160211bfd423e9774000180f20052c7bc000a471054000000
    | 17 => 0x640121c000bd366fa82dba2eb200009e52dabfc00045ab9e2d4104cab058420005ecf36d079902766000004c37778ebd4dc90f670c88003ca40ae0948003108933a3826840000001450000850000000000014000000005893b059e998f59917e12c00000000000007b49ffcc2a853000470c000492715918332c00036e10b996c0004a2bb7e28a4f5ea007f79202dc3051858bb2000000259c38851e
    | 18 => 0x536000000000011984700000000006e318a67621288804000d5b0000de80007faddb38f504edc25118000001fee83ca20b46cfd31bf00002000000d73a0460106928eb0b1ca844654e8a1450e133712925f37c1eb7152838b9a6a80778003bac9b0a8f264db780000000dd02872b8235213000000061a03ac000000dfc800180c0004d5cd180005b931800002849d32432d140000003deba1000126f
    | 19 => 0x1f780005a4d456638e9814e91467433c098af2faa023055f80007da9e24d920004d25ccc27aea20d296b4000db869e00006320000002e0c257c2347594e7bc07601fc9d8448ad650f687fc0000001fd1c2400042d28ca8480c000032aa029aaa11c3c4a5e1bfe7320c095900000007ef80000003e80de34b4f3a3a50003a64dde6c121cb49dada2f7000242c5328b70a70889cb4eac1d125b0001fdd
    | 20 => 0xd7e800034800000012003ff5654030001106f703199a0d73e42e00026481ba00000000010f000000019dd706c52665bc94f1ca2e532134739a9840af0000cc2000000000095011c6a7000000033714c870db90000000000293ab874da8e3c12ae520001eb4db688470a086800000006db4fee142a467d30e0b20000213000200c0802843180b74000d670001bfc4a700000000000000003788b7253d
    | 21 => 0x159e00000025d1a0e23661d88080481960000000ce7ee2ba7dedec86005
    | _ => 0
  fld v 13 (i % 96)
def action2 (ys : List Nat) := orbitLookup nextCodes 0 678 (hk ys)
def rho2 (ys : List Nat) : List Nat :=
  let a := action2 ys/759
  if a=0 then [] else
    let c := fld 0x339415a3a42cec08eae2074aca1ac688 21 a
    vals.map (fun v => fld 0xf400000000000001ceda0000000000035c00ca0000001210044e0b200000000bc0000000b000000011f00446071e00000011d0043e031c0046e349086208e8660000000f0003bddc6300001c4d970b60ac490034800c9689199039003158319620d8642e002dd6c2c002bd5c1f002ad541c5346030140028540124e03a2e0a0045a2a088a0140400 9 (orbitLabel c v))
def J (ys : List Nat) := action2 ys % 759
def r2 (i : Nat) := bar 145 (cutB 9 (B i) C) (cutN 9 759) (fun _ => J) (rowOrient 145 rho2) [] 10 0
set_option maxRecDepth 10000 in
lemma roofPart0 : span r2 1 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart1 : span r2 1 1 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart2 : span r2 1 2 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart3 : span r2 1 3 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart4 : span r2 1 4 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart5 : span r2 1 5 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart6 : span r2 1 6 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart7 : span r2 1 7 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart8 : span r2 1 8 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart9 : span r2 1 9 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart10 : span r2 1 10 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart11 : span r2 1 11 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart12 : span r2 1 12 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart13 : span r2 1 13 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart14 : span r2 1 14 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart15 : span r2 1 15 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart16 : span r2 1 16 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart17 : span r2 1 17 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart18 : span r2 1 18 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart19 : span r2 1 19 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart20 : span r2 1 20 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart21 : span r2 1 21 = true := by decide +kernel
lemma secondRoofOK : span r2 22 0 = true := by with_reducible exact (sj (sj (sj (sj roofPart0 roofPart1) (sj roofPart2 (sj roofPart3 roofPart4))) (sj (sj roofPart5 (sj roofPart6 roofPart7)) (sj roofPart8 (sj roofPart9 roofPart10)))) (sj (sj (sj roofPart11 roofPart12) (sj roofPart13 (sj roofPart14 roofPart15))) (sj (sj roofPart16 (sj roofPart17 roofPart18)) (sj roofPart19 (sj roofPart20 roofPart21)))))
def t2 (i : Nat) := ck 9 (C i)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart0 : span t2 81 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart81 : span t2 88 81 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart169 : span t2 42 169 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart211 : span t2 44 211 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart255 : span t2 25 255 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart280 : span t2 64 280 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart344 : span t2 90 344 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart434 : span t2 41 434 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart475 : span t2 66 475 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart541 : span t2 66 541 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart607 : span t2 56 607 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart663 : span t2 32 663 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart695 : span t2 39 695 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart734 : span t2 9 734 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart743 : span t2 14 743 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart757 : span t2 2 757 = true := by decide +kernel
lemma secondTestOK : span t2 759 0 = true := by with_reducible exact (sj (sj (sj (sj leafPart0 leafPart81) (sj leafPart169 leafPart211)) (sj (sj leafPart255 leafPart280) (sj leafPart344 leafPart434))) (sj (sj (sj leafPart475 leafPart541) (sj leafPart607 leafPart663)) (sj (sj leafPart695 leafPart734) (sj leafPart743 leafPart757))))
lemma upperDead (i : Nat) (hi : i < 22) : ¬NatRun (mask 145) (goal 145) 10 (B i) :=
  symCutRoot (ori_ok rho2) (spOK secondRoofOK i (Nat.zero_le _) hi)
    (fun j hj => checkpointCheck_sound closed (spOK secondTestOK j (Nat.zero_le _) hj))
theorem finChk : ¬NatRun (mask 145) (goal 145) 11 inputs :=
  symCutRoot (ori_ok rho) roof upperDead

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 12 ≤ t := by
  refine proveAtCap 7 145 11 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row29

namespace Row30
def vals : List ℕ := [1,1,1,2,2,2,4,4,8,8,8,10,10,10,10,10,10,10,10,10,10,10,10,10,10,12,12,12,12,16,16,17,17,17,17,20,20,20,24,24,24,24,28,28,28,28,28,28,28,28,28,28,28,28,28,32,32,32,33,33,33,33,33,33,33,33,33,33,33,33,33,33,34,34,34,34,34,34,34,34,34,34,34,34,34,34,36,36,36,36,36,36,36,36,36,36,36,36,36,36,64,64,65,65,65,65,66,66,66,66,66,66,66,66,66,66,66,66,66,66,68,68,68,68,80,80,80,81,81,81,81,81,81,81,81,81,81,81,81,81,84,84,84,84,84,84,84,84,84,84,84,84,84,3,5,9,3,6,18,5,6,9,40,72,3,5,6,9,11,14,18,26,40,42,48,72,74,96,13,14,44,76,18,48,19,21,25,49,21,22,52,25,26,56,88,3,5,6,9,18,29,30,40,48,60,72,92,96,40,48,96,3,5,6,9,18,35,37,40,41,48,49,72,96,97,3,5,6,9,18,35,38,40,42,48,50,72,96,98,3,5,6,9,18,37,38,40,44,48,52,72,96,100,72,96,67,69,73,97,3,5,6,9,18,40,48,67,70,72,74,82,96,98,69,70,76,100,82,88,112,3,5,6,9,18,40,48,72,83,85,89,96,113,3,5,6,9,18,40,48,72,85,86,92,96,116]
def inputs : List ℕ := [0x21770b02045f801580572b5801589f0401b29e000fff800003c0000000fffc00000780000007,0x42a115256ca8802acaea01a802a921492f517200000000fffc00003fff000000000001fff838,0x2e0c2061e083112b3008c02305330723c0261a5fff0000f00000fffc00000007ffc381e0000c0,0x9504a848314224c413104c417747843dbb8e080000000000000000000000007fffc01fffff00,0x2ea1750e0428003080c2030825b87ffc04c0041fffffff000000000000000007fffffe0000000,0x30c18609183045bf06fc1bf079c0248927004000000000000000fffffffffff80000000000000,0x3f01f80fffc07fc007001c004e0040023800801fffffffffffff0000000000000000000000000]
def scs : List ℕ := [0x1fc2a230a32689b,0x1fc480e8ae2649e,0x1a84802ca3288b1,0x158480e89a2649d,0xe82a02ca2278ae,0x1580b1fcae26ca2,0x1580b230b128ca2,0x2302a158b1288a3,0x1fc2a02c9b2749a,0xe80b0a89e26c99,0xa80b158ae2749e,0x1203a1589e26899]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)
def recipe7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x276f2054e1804f2c358615d1704f985c2052700a3e5d2123e334084c44182052a24a22031b9bd041a8501a7b03c2a069709341a802b7403c0321a3a7916a7d3c733eb07020f5354f85b07210523d1229b07028f52166c1e286c8f5344dba3105b3f40518205273285f5b1704d115d05b06199bc051a2353224b832b4504f620905b070103c266f03c0c3f85e3f748f52f6d8f4360f9a52e40a0405210529a21a8a266a8f92d6021506101d52b17a469901a7e2c2ca80963f22a294f85b394504f271720b032104c2a5604c335084e0701a2a286e0f5051a20f394e84d030083c3a6c8f5276220f044022e2633a0e05010f52c488500319a15032104d346f8f615008669a41280346c8f5461822a3d7383f051a04f2e6c1b82c45850346f8f42b17a43715a9b5271e20e0607404075a9b61431c32075cc88220084d2e5604e263384f071c050042104f21684bb06168502456057052104f305c42d0516ad02e538504e21210281ea395864280686427e3c731b73a3f850901804f2e3104b07020d8021a20f1b0084f1a0286606212a82c5cc88031e04f012104d343f8501361a15021e8531b1a29a1a014b6271685007033eb5c5c22a011704d0564280060905b
    | 1 => 0x51a2110e3f85e0516853041685362168532a5c20d28252552b6e0f5061804c71183f42a6b0f5431822a4e1ba0e071ba042b4d20d071d8e601000f5072104f2633a1107021b72c6e83e070e866113f04a3e7403c333804b02012062b5623e3c718f507032052c730f52721210011b84c2c6e8f52855061335084c2e3f1b12c748f4032121006020f527712050319b4d3c5485506028f5066427e8a2120e5c074052b4520f882104d3942a3e0741a800401a82601685301168505d168502e3486038028a2070083e25083fe25008503f589c824538532d57c6d39311c6031e8503f74a80070089330748f5266d094395084d8707404394284d0f5f4212d55853071704d6c0e8660701a2c011820304212710501a2a0417a343456853621828d9a2128d061a20d0b5c85b151aa520521a89276c0f5963d9b50c0105b621e853062128d0518a7d2500853393285f2e7083e625c488240404c05073f4390594035731b7333105d1b24a74021e04d2753853021822a2a5084e303384f2e008502b6c1b8065a9b600000f5316e8d8071e04f271e20f7d5e2812c6c8f5071804c2b18a1a2b6c1dca818205031e20f2553124031984c0602a7f246c9db2e6a8f50702a06
    | 2 => 0x3010f50b5da152a5304e3a6e0f504010f5286b0f407188505f218503350a0e393f04f2d55a88011e04c0741ba1050bc4035403a124568502e5304f3c390665f1e8502b6c0f52a0304f0507404041685041182052a530522c7403c051685002168536219a8d2854927234604b051a23e335084f396c0f5394d04c2451050033f22a24350642c6ca0a2753052060e86607188533f58a18011984d075bba107212043c73205286e1da393104b070103f2e5304c28568532b5320d136185e0616b792821a3a071e8507319a155d2120d33348605f1ea36071aa3a056427e8e1e8537e21a881100c662b21a4d0306bd1333e04f5e1c0502854855070322a0717a34062104c275084c050083e3f74beb051e04d3d0f29b31738f53a3f8530417a7d0619a15062104d3157c080418a287e1e853051820d3652a812c1f2482b482102a6a893061704d2e3f04f03000f52e5a850286e3eb5c0ac652706bd1031a8503a31bf12d031278f5c205061822a124005e2456a8a336a8f535730f507033a10319a873c7303f051704f26730f59a1e28d031b84c0f21222071984c2e6c0f5050120a7e1a053011804f2c17292051b9241a6305b295e336145b185334284c101ea4e
    | 3 => 0x3f74a7e2b42a0e031a04f315005c2b17a4b34020533e7328034412883f74b3c041a20f313b98506023fc2e3a12b01210520401a2a3942a0e344f2150f40a1504073f4051a20d275a853032104f052128d070303e2b568532b4284f0609bd33a4105307230eb5f5e281022104c0641ba12633a0d326f03e346e0f5021a23e2a708f52a5c23e041c0500c5d85b05181b1050133c3c5723f901820d271e20d022104d6507405395304f18181bb217fa8002211be031e20d640a41e071b33627023eb210084c9a188532771a09230084c355d4880618853246ca808c0e866065bba106218502534860012104f901704f071804f7901a813b5185b0741a812b1a2863016a983342a0d3818170256c1b5923fa2c2e5604c630e86607183345b1984d2821a53045f209275604c2a4d04c125f05d8a1704f32748f5021e04f3818971330204f07000f5021804c031e04c1662a883a4dba32b3d8502e6b0f5237ba05245b3a12753124441822a8819a153a41288031b84f2e4d04c071b84c396d8f53543ba10731a06343f8532c009273953853266a8f42c2ca7e03183f43e1fb8e2b3f04f395084f07023fc0321287051822a031a053367083ca31822a041a04f02008f5
    | 4 => 0x71a04f040127301181b19a1a053052104c042104c8a2123e136105f031a20f275a850061984d6352a80031804c246bbeb1244c21304f85b05008f5031e853336b0f5052104d200084d28010500218853273e04f6b0905b155f2d56418142377103f206605b393105d02211bf2851050307083f2550a5a3c730d8396aa05660905b021e8502a0384f051e20e2b5323e240a41e1662a891644866075e2812b4820e3c57216256c0f5395a850071e20d763f2052756057a61822a260913d334e84e7e1685306028f62a512291b00924335a850071d127255084f2e00853041804c5e21a36051e2a70f5f41d051804c27549272b4804f0f19a22246e0f53940a048f5c22a360185b07018f5306d0f5061b0cc115ca150606bd12753850031b84d392121f3c3b9852e720f5070a41e246e1b6061804f293b9856b403a12b1a21d34020500702a058a1ba0d0f5b04f021e20f0321052021984c071b84f053d9b51901050333f23e05020f5050e4be2b4520d07084051a760f4061ca34326f0945d023eb031885006000f507031b4272120e0321853030103c071a0533c52a7d343305e071984d02183f4a3182052d718f52e134e5885c48807008f5061b84c3456850
    | 5 => 0x1b6405f031e04d04019dc0621853050103e2b6c0db2b6c03e0318205155f218062120e071e853051e850377103e346f8f9061d8c607073f42b038502e738f40b3f3f4061a04f3173a05815c22a2716a562b4dba3901e04f2f3f8500602a2a2c6c83e271704f357003c5c5c205032123e2a3f04c062104f06211fa031704f27718f50521a36162529b3c22b666864280070327f031e23e5d1804f021804f334084d011e04d256c1b71e0084d3a4585329550613a35061031a2118a168500316853b418205253da048a0e8662e3e04f2c4e04864011b523008520719bbc3f7483c3a430502b6aa05040e866031b92402000f5383d18507019b7051984c271bb471a01053071b84d34430502a5304c1b6305b071a235061d127011704f2d5205d156085b0219a87346e20a0c5e05b25709b82a53853021b84c244ea04061ba3e60210520521a3a913f20605018f5246c8f56b5d48805021b7393f04c0501bfc0f1e22213614042b5620d1019a232856850071f8a0210084d07023eb070083c04018f402188500602a05011b9242e5604f270084f0521ad007031b5335604c395084e871984c236385d072104d271ba3e12423ee7e0ac65021a210345105010758f5
    | 6 => 0x28350612e3105d0501beb2f3305e336c0f50519aa72b252503565cb8276a8f53f1718b3274b3c02182053024b837619a15041804f0506bd12a00850621a288051804fba18205061828d254e84d4e1e20e2e3f04c2e708f59a1e8532c403a133409bc071704f24040ae901e20f0317a34286e1dc051d8c6271ba0d5a1984c900a41e276223e060222c3934864880b8a82c0112739624de04000f50702a092a3105d286ca0905000f534350612b1a21c07403a1056427f07168535d1ba3e1024a23275304c02010f5366f0f4041b84c2b3f20d071b9242b6c0f4051ab71935c22a611a2883f749b4145b432041a20d021e04c106085daf1822a271820c10083e128350643c7322d315005d316e89327548550316850021b84f04188507918a7d065c2052b3e04f05188502e5320d9619a151c01053ac1822a051aa36913d9b5395a85307030f5061b84d39348623759068275304f394084c346f83c051a2103c3904801008f5393e04f283b98504181b12d55061061b9fa8b0e86606210522a0384c871b84c2f6c8f5245604e05212103103866040905b2b18a1b39429bd061a20e245304e04188532e748f524319e82b1ea1f0518853a01822a255604f271820d
    | 7 => 0x363b9852a7222a3e1fb902c6c83f051e20d2b4820d3c732802a6a8f5240404d0618205334284f041d1272431a066221a882e6c1b423011b0310ba232b748f433429bc2f31bf12e722050518a28041ba3e387183c07200a1070120603018f52f748f53a45850330204c04018f5731a2353d558532c48a3a326f03f2504053271823e011e04f5f16850335604e1b7b0f5011804c051e04c43182053a720f473183f4ab1822a061704f062123e07010f52b18a1d2c5c43207029b52862a39245685328718f53a510504e1e20f2a19a222c5c4880508405255304f9a1685325040508f183f48a173bc031a20d2301050621a053061a21102210520616853390a45f396a8f5051984d04008f50716850210a18c245084e061b924021a20e411822a335604f396b0f5196628e032120d333285f2a5b04f394284c010083c306d0f6315805e256b0f55d2120e031c050890b8a8303584a4c5c22a051e287031aa39075a9b5327483e060283e333f04f021a04f24708f5285b3a10664280070905ba7182053c730f50401a2e8b52a7e071823e0501a82611a053070ac65335a853915a9b639708f55203a7f3041ba1071e04d022104f25708f5275604f0717a7d3038068
    | _ => 0
  let q := fld packed 28 (i % 128)
  (prefixGates (q &&& 2047) <<< 24) ||| (thirdGate ((q >>> 11) &&& 511) <<< 12) ||| fourthGate (q >>> 20)
def finger7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x54ed84ad4aa1220f4ca25fc394e9a8e0ccc9b6cb6cf96bd407f5ec988310bcf9fecef76e8383524561e439b77427749f457199ea235a9f6cfafbd9c8eb224376b6828db50fd59c3357ce0f87875428f5a63f5e961fe982a1f2d3a54839505256095993c0f89538ac0e352111c650ce8bd9f699993bf02745c68ab35c678292c0
    | 1 => 0x47845c5502601181ecdbcd21053f4717af37693c13495d7a444a86b7edddcf557e2b2530d5b872a716ee7b1cd12784b94b6fa52e50f6f9acf7311a30ccb0bfa256a4a07fd12ccda7edfb41522a976f632f61d041bc497ff939bc55480410edf618a6e154bd1a7a129ccc61d0aad12b8ca41ec469ab47b80825adfbb9dc573243
    | 2 => 0x6ebaf0de77c593e1d01a891e1f0d44bc6822b27cfb53b304ac54bc69f5fdcddb63abdd1411faca96ee89f7f09a5847a2c4ab4494c8dc1d532556ce731d44c14c18a11fd501805cf0e426509e517e796d3fd6c45b8cc824288f468fc3a20fa521dba1f6c4a6feda51f753f9185e980bb975f74df53ca02e5a1ed73589c358a18b
    | 3 => 0x85fd9586b2bdb25b77937b0873e9d72e0a9b38a911c6ae19d6903cd3e6da20c4c94207f24ccf3d370627599031571579b3cec61ade8b0c40ba93f6c830ef5f41f9fdce23973d2df13c8715a72118de19382e444107cf19c6a2bd492f2ae6163f3322430d0bf6bf7a34bb56cec6568b669045cf1b0d1de78361e3f69c45e07dc8
    | 4 => 0x1ab102508c8565cca97b12d3e4822590f220d2c38c1c2c7aefe44666cdcb8f31c1b691705cc61298662fd369e80a140d3c9d778d8d8745893c37fe0d0bdd284b06fe9b544a9b70b0e2519d430f9a95fdc15c82b2a495563e11bb174b57da03d1e1dd3e2b4976da19ef20f415fdc828cf884af7901f3f5c6b255826ed544d755a
    | 5 => 0x60ebdc23ba5973406e5da1340ce1ded151e8f6bfeec1dbe8950501923f92f155baee22289fca329fdccc269a3815f37c01579810b43bc9fc9da92328e9f4ca38c4050fbdc940b04b1d54dd957d82beb0307e61bc26a5c83e71fe62ba5e6be812f349fd0917ad53e9e9e1031b660c34fcc5d4e86e7f37b453501dc1e7a7ad297c
    | 6 => 0xf61cd8107f48741ba80d5f58f4949b67bd31a49f542ee04efed2d529a94aa90c7685537dac6b802ac2ac2330c785e8398f32e6fb4e069db9e4abd46a4063c9485d7d76fe3abaf7bbcc60c042267b2bdf979909fba0e9ad32b5bf50046d84743adaf24a1b6dec2e4b6e1a99550b34e59a2f4a2897e89a2cc38f105358984497aa
    | 7 => 0xa15fec7bac1cba9d11db9311f68ebc35c73dbb8a255fc1bf9fd449c4b029527801cf784b1da23d1baacba66735ab6e507f672972e7f3d738c289edea2f497da0bd74166ed0de07f34de07a5aaefdece528a61d17a34783828609cecb5eb9b3702b2ed0d2efe41feab94d57ea1a1bc57c63173cfc6a297df4c0e76eea739cc680
    | _ => 0
  fld packed 8 (i % 128)
def recipe8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x3486031a065f3d23f20535861043797703e1e1bd652100dc6f5805f023fc0333433bed0bb4a6405e021c06218565850028f43285f041e45204b0404325a431aa3621a1d51c1d16a7d03b2b700f503bd0420504d20d0427d740f50405c03894358627e8f4448600133c5098502378573a7701b65c124554600184046234648620412b083e0670644022c040616b0f45604f6184f0305f7403c6445c2a8f5590482185004050481b132c005bba11aa3b3d8506c9da589c8104c2448551e850390686605b02beb033751aa3a04048010f64e84e560e1028996d0f504215731b61a2d7040a36d03c03a2c033d3429245f05c560575f84e5f04a3e84c4084c5304c4528d5586025a955d85b030415f2065ac2f04086603ed031b0378680398f040e00404e0432a3d925028982b83f31bf17303c1822a319ff3e85c16a540084d7d03c
    | 1 => 0x5e21108405038bf783eb41a7e7f2814d04c1a053041613604a03927038bb033bc5aa7d3f04f1b14c008f57da0602057720f46105f03c88030407383c798f54f2157a03f2d8f55e05b55a884533c199b14a127040686b1b5760f40cc445529064864640a73290e7d8f5038436c0f55785d2a03c7483c6e83c1214d1729556c2f40a7e16a293f22a01a5a0385c020946204c3d18538cb001ce033a0e6185f4120d61a0f460480225b034be4a9850c3db758f56a8f5032cf219ef038611ca4e58860041bc2234f732085c1855e1250897d01924038503384f4284c1804f7d05d7a3eb5d852600505127702a8117a9127b8f0212752cb81fa980817a0304851c4f333d12e0626b20666125172fd1ca342c8f46504e4804d000f55a84e780f502866578551a850039b47f3eb04127489850205203bed0434d60946608531b84c41a34
    | 2 => 0x778f50440118a8521853183f40385203a2b031b5428685c04c6b0f5040575e84874a055084e530527c83c5285f4022d1a04f390666f03e19a046f8f47d83c6b1b602a2a0396161acf03c4b028bb5509b1a3772104f5d05b360614328d48a39043744c1b1034880437e288f52b0f40414856ad00185041850630484284f040c05e85c4d1852b03c5e85d03b7803a2d031244f85b018621eb5016bfe5105002ba120373674694504c6f0f45a8503fa2c311e80104f48924031b80cc724428a03c3c5904b0328a1d127558534442f49125031dc03c051242e52a817f83f3ea296f83e104c60184e219501ca21018f5388486e0f5470481d24f01bfc719b41d251038c3038550104c0ba4e1e04c7f8f5350645205c3f23e728f5252211b9de040521eb44430521b84f31a0452a80172046005201050638606f03f321ff1e1be1aa32
    | 3 => 0x13cf40fc8f5604d023756e3eb7c0f40fcc1418615084f562870084f614053204b2127172beb1b3e31ea1d01bd37a8f50404f0305001a0a7103f460571a29902041042885e85b21a2001a2903857028480220f562cf1e8537483f7183c4084d03271073f467c4b7333c5ea393904836a40022d02e8f50185b0d435410e257402350600404c01053410617b0f5770f403b740d4273a12b79beb74a2a2e0f50599c0817b040e40284e6085b7303f038c03f04a033ee408fe252791ca1e4ebf4040de4684803a5b020537c03c538533b1867083c43050658531ca945c2050332b562a77f03c6e1b7038f54804f02125039bd3345c1a2351b84d6012558b4303af76e2081dadb55a890285e1c2231ca1b210521a21d01a281ea880323a7fa0856a7d6105d7c205021fa1a20e0a40f41053028645295d418641f8a05489a770f50083c
    | 4 => 0x3beb5784b18a7863bd367864021b8172230ac656c83e5304e01c067703f481e41249145853034055b12401a811e04d01b743506118a283f927040417b83f6f8f57103c0384a6c0f42e83c6486020c76271523c12b773eb040986c9b564c400384f03055081697d83f2b20a0c4c86d8f42d83c1ca1d1704f2123e0423e3706671a06042040294328a2a52a7e01b3f2737a1ea891e23e6705e400554d23e4592b023344684b5c853151a32922b1a2110385b0384c022394e84c368600383c3f84d040530334d01185718f5019da4f0e74b1851b92462124039be5705b033795f9854004b280f57e8f56e27308a150185201a73011b503a084820f55a8b030430084e04228533783f84a03408252507e0f50185e039e5030f56b093038600305c041fa488530305d31162040ec590ff0204d0ecbe0420e7c03e010f4031b621222
    | 5 => 0x385f040c471a0a03282028d81c2fe6b8f518a980242f033f10384d02a2d3305e27b900325b03b7557bd803c095ebd4033eb03c8a1e9cc17a460bace5f2091c23603099280f418205538506d9b43105d51215680680427c01a053d9b41f34e0404b399c955a8d033f4038415084d1ca1f588641a20b56a15710f421a8a47cc5311752017d45850333f417a43540486585d1ba0d0ba230409b709b67a0f56f03c611277c8f53385e01b3c010f55ba347cbfc032040519a6c1db020407e03c1cbe5530993f20d2983c03b360fcbf2ebeb1aa915604e074043385b678535c04f029205004a66048388de79a050283c1a23e038534e84d211bc0386863855042895f84f5a8dd031b15389a039253e04f03c640405f17a290084c290f5028f7182032a2806705f032081aada2b8f54284d01a0303228042a8022cf77a73720f50905b
    | 6 => 0x1e1e30305b560e00284c1e04f1ca1c428660304c1804c548a7738f57d0f56d03f4504b5604c0343c019386685d5d8574f229038c403234038f21b9bc51ba7642815f04b17a0103a05568531499d440f0134f30120456bed3d9b50223a644064c0dd4e9b14504d58a40298f5020f5028607803c2e83f028f57a03c674325b84c4c19203a7e018533a185760f5748f42983f768f563c6503b3c3f127124927b8f54e8e01baff35465040405005d0944f7a8f44c271040441e1dd788f54c185458480cc705f84d293a16da2a03b345285e1a20d5ea3643a347fa2a5f3d116a996c8f5040a6019fa0383f571c503057040cd6d093211bd1e89e1ea852c8f5749b52120d211de6c9b63a9c95b04f2b83c03273021245a9b61c0501a3f642a0d50177023a1109bb042cf03c691dc5703a89033744104f6185537848031083f8503385f
    | 7 => 0x450487383f4e05b1e1bc0323e5f0607d1b71984c17afc041386d8f56ca0a023796385d1c2226c1dc71a052418238866042a750a5b271ab738f4208a21e1ab2903c628500305321a3a440530203c021b1024134804c0423a4520e25a4526b67531856405f0e8660185d03125040646c83f290d9608486104b67c6a018f401a113d8537c0f54b9053606856052468f1018616185e5f05d034f1151a46427e6c1b47b03c031fa5e053043d141a805d84d26b626c03e020503884b1720b038d943853748f5788f402c654004e1d45a74bfc2a83c3f85e7803f038407f0f521a7d718f61dbdc038441704d298f401a2c0184d3f04c731b545143760fa2c0f47cbeb0304f1e20e4e9f756a291da51041246f0f5030a66204e018867003c1ca951d18141280319e81e28d2aa2d74a2b5c052031420204e0232a4404a030f636a902c0f5
    | _ => 0
  let q := fld packed 20 (i % 128)
  (prefixGates (q &&& 2047) <<< 12) ||| thirdGate (q >>> 11)
def finger8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xc7ed32ad38c4d70f7392cfc362da7e4da56f8acb525b0cb161146aa9ee83a18f3615bd483d8304b332e2d005a7478e3b3b3b0ce10bf6c62b82a060a4a8524af9b6a5af48fed580befcace787aa79280da6f78b72b01108ed6a594572394fa483821d7d174b477fda5b687d1148287d5be10e58b0b30cfc62f7b4b3a7265342d0
    | 1 => 0x2484267302df2a812bb2deef8345b74faf69bc7f1049a763e88a7846d81bf955d1be8a2323e0882435fa584c37631450f62f162e50f6d1e22ab72dc392ad7a6d74d98b7906d2af37be4dd0ce2af022d876641fcb4c40dbf90958cba7e5b12c1f9f5eb8c09e4997d53671d2d0ab3c048cbd4015a8ab47563953df2fd4bd2832a9
    | 2 => 0xf8eeb0de0a0993e1a65c783f0510af8f3988b27cb792c36e151ebcd02876961185aba3a183413e4dee46cfe6972f48eef260c09d037bc52d253905311bfb952a80e4a4a48d808d6de22659aaa2d2086dba73e05bdd4c24abb1bacf517c90a512e1a293c48ebb3b9a5af9f9ee2ce7f648c1f76250b8a0635a1e577a4d58a6a199
    | 3 => 0xb0c6927ad1868fdc123db84d4de936728cbccee6b4c64fc0ede8def50a61e4067965078bb6b92c375dda40ad6eaefc64031db4ccd3510a6912e34cc8d8158d66d8e8b62d07672b4e3b733a3b3afbb3fabbb6832d17b28ac6e93b09502a6b618c4722434cb88af5e8afb59f27c6e39566af046785a143e7c0d6d4387a4521b4c8
    | 4 => 0x1a210bc6948530cc79b3106548275a455520d2df231c276d2d0ec6899d17ada71102a4ecb4698d042d3fa0696fa6680d3c2b97de0bd80689e396fa0d6666f432cf1ea0dd139bf27a32061643d57fe321735c628aa473205ed3db8bfb981d0305e1dd3e7f0ebeee18d5a2ddd217cd47cf1f834ac63572467cbb912655754d7544
    | 5 => 0x3d529223baa413273eaebb34a2db1da272cb09bffaabce2a9505a89a3f3fe04b6226ed2888db29e3de15140802fda8c7665714c7f90535bb1ff1233c980e2a8c7b0886bdc9c427b0e29016b1632f38b3fd67ec666ca59faeacd9e6307e6be82f2693fd32b374ae179d5d89cb6f9634173f15e88df0e3971e2dd1bd4d2d348d7c
    | 6 => 0x875ad5d97f83ebe2a8ba9ab4901137938f2079d2f7ebdb4e9cd234e9a929f8afd6ac7d7d1e20dc2abc891430e9434139210fe87f4e20a29e0fcec69140dee2181d6f11979aba792936b08ce384aa4ff567f97bfb9a4e72b01e0a6b676dde4ee6aff24ac85aa02ecdaea450390ba6e59a79dfea9743aebbaf1b4de96c90497104
    | 7 => 0xb664fe173a55239de112c52942a340d5f2e6baa265b204bf682d448cb03252fa068ba1aa9b83e07baadff1c681e931b0c167a82121800ee714a569d0a9627d669fd30944d05570fd234939865e8e95b99a5fad7399cc3e671d325adb5edbb3b553d558cebaf6f5eaee9ec62b581264a2abfd0ffc4b293ff7b8d42e318490ea0e
    | _ => 0
  fld packed 8 (i % 128)
def count (s : Nat) : Nat := if s = 7 ∨ s = 8 then 1024 else 0

def board : Nat → Nat → List Nat
  | 7, i => cpBoard (mask 153) inputs 4 (recipe7 i)
  | 8, i => cpBoard (mask 153) inputs 3 (recipe8 i)
  | _, _ => []
def atFinger (table : Nat → Nat) (ws : List Nat) : Option Nat :=
  let h := hk ws
  let i := h % 1024
  if table i == h / 1024 % 254 + 1 then some i else none

def lookup : Nat → List Nat → Option Nat
  | 7, ws => atFinger finger7 ws
  | 8, ws => atFinger finger8 ws
  | _, _ => none
def ck := checkpointCheck 153 scs count board lookup
def pan (s i : Nat) := ck s (board s i)
set_option maxHeartbeats 50000000 in
lemma block7_0 : span (pan 7) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_64 : span (pan 7) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_128 : span (pan 7) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_192 : span (pan 7) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_256 : span (pan 7) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_320 : span (pan 7) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_384 : span (pan 7) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_448 : span (pan 7) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_512 : span (pan 7) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_576 : span (pan 7) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_640 : span (pan 7) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_704 : span (pan 7) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_768 : span (pan 7) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_832 : span (pan 7) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_896 : span (pan 7) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_960 : span (pan 7) 64 960 = true := by decide +kernel
lemma good7 : span (pan 7) 1024 0 = true := by with_reducible exact (sj (sj (sj (sj block7_0 block7_64) (sj block7_128 block7_192)) (sj (sj block7_256 block7_320) (sj block7_384 block7_448))) (sj (sj (sj block7_512 block7_576) (sj block7_640 block7_704)) (sj (sj block7_768 block7_832) (sj block7_896 block7_960))))
set_option maxHeartbeats 50000000 in
lemma block8_0 : span (pan 8) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_64 : span (pan 8) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_128 : span (pan 8) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_192 : span (pan 8) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_256 : span (pan 8) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_320 : span (pan 8) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_384 : span (pan 8) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_448 : span (pan 8) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_512 : span (pan 8) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_576 : span (pan 8) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_640 : span (pan 8) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_704 : span (pan 8) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_768 : span (pan 8) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_832 : span (pan 8) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_896 : span (pan 8) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_960 : span (pan 8) 64 960 = true := by decide +kernel
lemma good8 : span (pan 8) 1024 0 = true := by with_reducible exact (sj (sj (sj (sj block8_0 block8_64) (sj block8_128 block8_192)) (sj (sj block8_256 block8_320) (sj block8_384 block8_448))) (sj (sj (sj block8_512 block8_576) (sj block8_640 block8_704)) (sj (sj block8_768 block8_832) (sj block8_896 block8_960))))
theorem closed : ∀ s i, i < count s → ck s (board s i) = true := by
  intro s i hi
  by_cases h7 : s=7
  · subst s
    exact spOK good7 i (Nat.zero_le _) hi
  by_cases h8 : s=8
  · subst s
    exact spOK good8 i (Nat.zero_le _) hi
  simp [count,h7,h8] at hi
def rho (ys : List Nat) : List Nat :=
  match fld 0x601f980029169dbd 1 (bsr 0xf850a4d4f75c4219f66a85edf192b1c8f10b3d10f02621c1ea560623e90f1b50e55cc3f5e54b2f93ddd4ff26d8f36f54d4d49ed1d2f67d14d231283fd0ccea2fd0880740ccdb0224bc1e371bbbb2cc41bb977ba8b495dd75b24eca81adbe6ec1abc6d4e4aad227489fc673cb9b9d6f459b57dc8e99b8f581999c8f3592bbc11f91e295a38fd552108fd0d8ef8c393d7f873364d67a3860b979cacf55763be7b2742847757231c5d16d7e8955698f92135b61fc905a0e96be59374dbc55a040b854f78f74543a82f94f7260614b9bce66449564e73bb12cbe2e4efcb826dacc5c1f1987801e19b624116dda8f10f4dc3b0cfcfabb07417c29061259210149de88 32 (hk ys) 7 0 64) with
  | 1 => vals.map (fun r => fld 0x12e0000192bd00000000000000000000000010b0039d529d0000001210000190b9004c59c8c662f8542300000010000365649a003f16a785a15832060000001200000000b800000010e003ad569e0000000ff003615099003b9606a56920160300492447f002ed741f0045d847c60ab84c1d0038202666d8e93600002c54664510dc1000 9 r)
  | _ => []
def B (i : Nat) := mv (mask 153) (fld 0xe20f51e61505f62104e40e42e21400503e30e60f42504f30f52f31f23f20f40e41106105f21f10402e62506401000e10e31e51f41404103 12 i) inputs
def I (ys : List Nat) := bsr 0xf850a4d4f192b1c8f10b3d10f02621c1ea560623e90f1b50e55cc3f5e54b2f93ddd4ff26ccdb0224bc1e371bb495dd75b24eca81adbe6ec1abc6d4e4aad227489fc673cb9b9d6f459b57dc8e99b8f581999c8f3592bbc11f91e295a38fd552108c393d7f7a3860b979cacf55742847757231c5d16d7e89555b61fc9055a040b8543a82f94f7260612e4efcb81e19b62406125921 32 (hk ys) 6 0 37
set_option maxRecDepth 10000 in
lemma roof : bar 153 (cutB 10 inputs B) (cutN 10 37) (fun _ => I) (rowOrient 153 rho) scs 11 0 = true := by decide +kernel
def nextRecipe (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0x13d944f641140c450113d88450213d844f6313d804406139d84f5213d084f5313d502e5113d401e5313d044f4313d004404139d44e74139504e65139904104114104105114144106114184f2113c8c4f20139c84e52139084f1313c404e51139044e7113cc044031390c4e731394c45071041c4e621388c4e131398c3e51110022e50139c03a40739803e40929824e600e980fe600f9804e600e8c05e600f8c04a503f9404e5012901ce40139019a40939019e40128c19e30179004e306a8045a306b80566105b842161087841ce03938c08e10218405e30
    | 1 => 0x14418550617d085f4117d005404179d05e54178d05f2117c805e52178c85e7217c405e31179c45e511541c5107179905e4115000ba602f9818e707b9818e5066941ee50679405a708b80d8e30179c05a503f80dee30179400e520dc8435000fdd030000fc9035050fc843f450fd8c3f640b9843f600798c3f410fd0c3f400d0103e740f99031060d41831020d4083f510fd4c3f130fc403e610f9043e710fcc034030f90c3e730f98c35070c41c3e530f84c34008b9c04103104044b21104084721114004f7613dd44f7213dc44f7313dd04f701101c4000
    | 2 => 0x67d8d2e13439459f505f94c2e5307948ce43479059f402b9089e536795191055b948de41654193e2357884be4167cc07e423f94d9e43679cd9f10679058e51679448e523b90594005a901fe305b9008a4023900ee305980dfe025b80e36038f80d56035780c510116c84510215c840e2115d00573015d40576015dc0550017dd85f7517dd05f7217dc45f7317dc05407140005f6517d8c5501154085f64154105f6217d845f60150185e7617d505f3417d445f530b84c5f50078c85f3217cc45f301500c5e75179cc5e53179945e631440c5503144145505
    | 3 => 0x2841c8e16218588e14218508e643b94c8e763b9948e743b98ce10321410e50320418e10521418e5052041c850739418d10623d4cef4223d48ef4123d40ef4021014e40423854861523994ee5423914ee3423cc8b10723cc0ef201d41c71072398cee522390cee322384c861323c80ef1021008e40123908ee3123848861223988ee51210008101814020100229c08e703b9808a6023980ee50229408e503b9013a604f9808a30238c0ee2059809fe015b8088a2023880ee104d80d3e032e900be4064409562165d41976065dc1950067dd06e305394d9502
    | 4 => 0x4f94d5e517bd41e4057b9d5ee257b914be517bcc07e523f88dce537b9cdbe507b9058e61790018a6063981ee702580c9e03939c18e407580dde0393941ee4050401450020408e1012040ce10201418010621c40871721c58871521c4c871221c508f1023c5c8f1623c548f1323c488f1421400650623dd8ef6523dd0ef6321408e5012140ce50223dd4ef6421414e50423dccef6223dc8ef6123dc0ef602101ce406184188e172185c8f653bd508f453bcd08f603bd408f403bcc08f623bd448f643bd4c25070841c15070441c8f433041c8f423bcc48404
    | 5 => 0x63c918f201b9818f76539cd850061405850363dd5850563dcd8f7163dc184076389d8f654b9cd0e715f9cc2e7363d801e72339cd1e7163d00ae72638989e23639918e76639d181065b9c8de616141d3e73579c58f50610158e2563914be7163cc07e723f9cd8e436388d8f10639058400784050a217840c0e4141885e7707bdd9ef727bdd5ef737bdc5ef747bdc1e40705809ef625398de50079405e5037bd95ae527bd8def617bd81e4067b9d9ef254b94d0e215f88c2e2307808ce5347945ef402b949ee722798dde237b989ee64598496e1237945e506
    | 6 => 0x6d0021602378061e024980d2e0303805a6026b808c6033380e0e038180d76035f80d46035380d1221904051a219040e4730038c647405d84d162191d42476091dc24f7693dd64f7493dce4f718384e4f709101c6e2093d954e139140245019140e4f646b90a3e4393d864f609101a4e7693d512e23439057e130b90e4f5007908ce2347884ae02939d49e137784e4e6593989fe315b908de31879093e43579064f40910124e742f8c64f301f8c8fe437188dce238b90dbe309100026030b80d8b2160405810303985876061c858f2763c998f2563c8d8f21
    | 7 => 0x8bdd5ae738bdc62f708bdce24078b89e2f654b9d10e735f9d02e718bd801e73339c51e738bd00ae738b8989e24779d22e768b9d1fe625b9ccde62879cd3e718bd415e732f9ca2f031f9c0fe71739c624003e9c0fe708b980960427811ce708b900fa4077810fe40739408b200ecc04b306c40804016fdd9bf756fdd1bf726fdc1bf736d01c5b106fd9544036d401b5026fd91a4026fd89bf606d019be766fd5124034100574030900c14023100d140129009be752500dbe536f995be636c415640235005b5064d00d54016d010b4011d008f4036f8c9be72
    | 8 => 0x3f890fa623f988f1023d408de523d418ff513fd40ff532f948ff031f940f4004580d1e03838120604518114e04498112e0430885c101328840e3271d01262431885c75071d81c77073dd9cf7573dd1cf7173dcdcf7273dc1c4071b885cf6553851c50371401c50173d91ae4373d85cf6073d8dc406739d9cf544b8910e435f8502e4173d401e43338851e232b80dce7527851ce5273995c1055b90cde32714193e4173d015e432f8c9cf031f8c0fe41710022b21884040e6289c862f278bc9a2f258bc862f23838922f201b9862f76539d22503894022501
    | 9 => 0x2d8c0be302e9c0be7022cc19b30010087f761fdd47f741fdc07f721fdcc7407098047f651fd8c75021d4007f641d4107f601fd8874061fd507f341fd487f530900414031fcc07f321d00c7e751f9cc7e531c41475051c41875061fd007f421fc08740003809a6036b80e16033780a1e035d8117e044180d0e033c4042a2103908f7503dd00fb723dc9426213dd80f7703fdd8ff723fdd4ff713fdc0ff733fdd0f4070580cff623fd90f5033d400f5013fd94f5053fd84ff603fd8cf4063fc94ff453fc8cff240b8841e0333944ff403fd0cae533f9c89e64
    | 10 => 0x4bc4d0f5157d502f5307d48cf4347d04af4227d4d5e5454415550557c0cdf41554193f23550024b4062d41eb508c4023500569015e40569415e5022d405b4085814de048781546055381506054381516044781176055f81426050b814c60433811de0503c84bf762fdd4bf742fdc0bf722fdc4bf732d01c6f102fd94bf632d404b5022fd90b5002fd80b5042fd88bf612fd50bf342fd40bf512fd4c2f1307cc8bf302fcc8bf312bcc8be7527d0cbe532c414b5052fd00b1062d418bf422fd04b4003dc0e4b3062cc1eb302e940be5071c0e27032c8c0ba30
    | 11 => 0x37d45050637d4d750608418250604418150630418c50637cc5150628418a506379961e762441c95073794dd50634415f50535415650637c121f0537c061f0237c0a1f03350021400869c0de60879c21a60379421e6086900de30879013f764fdd53f704fdc93f714fdcd3f744d01c6f314fd953f644fd8135034d40535024fd853f634d4013f504fd493f404bc510f534fd502f5107d4ccf4147d0caf434f9d49f544f95131054d4153f0337d0935064d000fb5072d022b504e9c13e704e9413e504e9013e4057dd06f3053d4d550257d8d550057d415f40
    | 12 => 0x45400c1003140167107fcc1ff6318411410668415ff5248415010259c5021025bc416f405bdd011005141965055bd8d2505414096f1409408150030414c50544415150528414a505244189506598516e147fc096f037fc056f025840564000840025005c40175004040105004840125002ed02170585c0a170385c421b7137d94df6437d80df6237d84df6335018610585c59410235404d50285c54d50485c4e171287c421f7187dda1f7587dc21f7387dca05078501c650587c5945028540a15036941a1f1337d521f6537d421f6037cd1250637cc21f40
    | 13 => 0x429c10e708381a0606469c11e70469411e50498152e05329c0ce7025d80972127c846e6227dc4950527dd09f1527d8c9f610b9d09f60079d09f1427c109f1327c0c9f10250017a215d885df7677dc9df7577dd1df7377dc5df707501c160477d894e6177d81d5036b951df6477c952e5277c150e245f8842e2407810ce5277c111e5277c0cae50779c89e61750009a6027981de7069815ae0569811ae048c81a3a068d81a3e068d8123e045e9817e600a9802e60429810e604a9812e60469811e6032980ce6077981670359c09d100754009100254011100
    | 14 => 0x5001460653818bb3033dd8cf7533dc0cf7133dcccf721bc84cf6033d94cf623140cc50433d84cf5433c10cf2433d4ccf5033d482f4107d0ccf0331000fb4025c11d70432940ce5047dd91f7547dd11f7347dc11f7147dc86f2047d951f6047d891501454111f6347d511f0447c911f5043d051f520bd0c1f4247c0ccf23450019b4025c0dd70316cc18b407ad022b400ed004b402bdd8af752bdd0af732bdc8af702901c64022bd94af6029408a5042bd8caf542bc10af522bd40240405010af032bc08a400098102e04418110e045e9c17e700a9c02e70
    | 15 => 0x45c112f604bdc12f744bdcd2f721bc8d2f624940d25014bd912f054bc112f0349001d70586d012a704b9c08b6022d01070409c0d0f7043dcd0f7143dd0170243d810f6441405050543d8d0f0543c950f4543c110f03410019b5009c117f705fdc97f745fdcd7f7105c117f6053d8575035d4157f645fc157f254bd497f0343c917f045d0002f700bdc82f710bdcc2f7405c0c2f600bd882f640940c25050bd842f050bc942f450bc0c2f230bc102f2409001cb5092d405b5026d822b6062d803b6012d401f74040001f64054141f6307d141f0207c101f03
    | 16 => 0x78dc08b101040031001440191006adc17b705ad00bb7086dc0cb703edc11b7083c1a0f0483c0e04001bd89cb7092dc05b7076dc04b707adc0010032d8147060ad811b6053c154f7053dd14f711bd494f0453c194f0351001db6069c15a704529c14e7078401810090402210070400f1002c400bb6069c19a70269c0daf016bdc1af736bdd0050051415af056bc11a5026bc19af026bc0da4006a9c1ae7083dd06f518fc123f0653c923f036bd8e34003ed81cb608adc1510092d818b707ad81310022dc05b6012d81a6066b819270509c15070586d80c704
    | 17 => 0x2ecc8bb4290cc1ab0103d940f6003d91ab7103d880f6103d8c0406000000f5403d4c0f0403c0c050101409ab6103c140f0103c080400039800f5203d440405038140e656ad45210103d040f4303d08040403cc80f310100c0e640398c0e43038100e03039500e530041005040041405054c4093b5249c50f35070d01510249c4d372390d0053404ad894b614ad48cb523cd01172431c8c533041c9593505edc9772541c90272309c91c35090d40535024d8183608dc9947243cd81c36051c8e372390d81936014d80f37064dc2072481c8dc37090dc05370
    | 18 => 0x1012ed44bb313cc0dc3033ec0dcb0300408d102
    | _ => 0
  fld v 18 (i % 96)
def C (i : Nat) :=
  let d := nextRecipe i
  mv (mask 153) (d % 4096) (B (d/4096))
def nextCodes (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0x8c600097300000002c1cb5df6d4c6c3a37dff5a750c793f10340000000c4a6a0003a43a72cfe96b180008fe61901d9fba0f072c8bf12188064568ca43722982143cfc6a000e5b8d23c41ffa4516bd83e635dfb9e00026b41da767d3ca62a900035f000000ddf52440653ed007c0b63ebf1286804cb64943884c000a19595000464655ba3dc12edb9b00012100099e
    | 1 => 0x69cec142500024d5a51e1000e38d2d21dbeb342d750ed427000000b6e000cbc6b8e40d1aab75050003ebd5a60ed26000a4fde899a1c11c100007802a791d46a29e7578f89fc63000000f8cbc1d6bb7e0000004329a5f0cce1a6295e810fcd7ee000000206f6a46330e0007cd000e13303000230000d90000ce23346fa8461fde42000f643d50003d1000171d07256120
    | 2 => 0xd6638c50966215d692742a2000e6a889fe3fe07d62a3238bb77a500007e0960009d23ff8ce000443af600067787e9d5000000ae0000000126c9b8b7ba10008df128fc01e42ffc0dd6a0006345c631601a3a50004b20000a25315a1e6624bfac037000000000bdeb89e892b500005c0bfa53d24aacaaa0004fdd95413000b0a00066549cd7e2c10003fb323b5a000000
    | 3 => 0x9fe7cc000f383fe53b9593f3014ae39f56252a18459d6ea9cf00000006f36590007b099a5611b22f41ce9590008c1000f36a16000f95ed936ef4657300082a0e700079e98a97d15100046524d416bf3eb281c5f27ffb461988fe3b0d1ada72b282a5c985b48c82f8aa25186e99a0006200000005e3d6d000f26d6600047a0009089dd439b7d1eefdc0000006db000000
    | 4 => 0xb2de6f5bb81a4660000008406a0eb62cc5a5e3ab15fec5f325ba4238d778c820007020fe174000a3a2e005155f3978050000008d0000014ad3e864a97e81c4a21000841cf900055283d34c6ad355d9e000eec9948d1604f8219f5eb78a0005dbc1255e3f96aa0000b110b53332b0ccd7262c00000000043fea5bf0217de9f920004c318f00066700018226758271437b
    | 5 => 0x3ef000e922b84be000d6e3cabdf6bc7c75f6a7cefd000b3f000000e5b0008af2c211aae45c5973686121fa0b7f3a3be9952d881b000023b79f0000009904a05cab1946826b78773e4f7ab30004863f2000df80005f19708bb93a10f163000c150005f51cf000000000a2a083fa9f6d97f0008c2f86442120000b1df0d91227dd9202f18100000058ca2b5de2ef1afc75
    | 6 => 0xf56000000814000f534fd3659f9bd49fd41e1cd000809e75000000164000000000c5d37cfcd66c00028160d04375b42fe69000558aeef1dfd90006809d60c0bec91ff9d76200062300041bd45000c438a4f1b52f29f48197552dc925bc000000b3f00038ad4704da31602e7b000000000a1900013452ad666f870b98a73a703df000041f145b64b3190f1a9c9b
    | 7 => 0x830f400008b10009b83367ca269a7e0009a92cdb250004f4c87f63b0986500037705780d0b5c4d94b67b650a94976e5f78954e6cd9d1a370f9acea88d794380b6c8568d217000bef9110a34f4000000364e412db40bbc16dca7a3706f6c31b65f209465a0fa100000071a39d00020de63677b15611281000c2965201c0002a651e281d85b2a5e0d6c6e478f91814d199
    | 8 => 0xab700021a0b0fd47a9b31a50d852607e44b5fefc696e2ed200060db45f255412b83040263aa0ce000767954eea00003602fc8e5479a652300054a7c51dc25cd29183d5e00b4ace77000c59c3d00000061ca8d1220009dcf4bc509e829c5b718d0004960a3806e340003410000000008e51a72dbf8376987713468d8c6619000c3700042534d09c19be865ee3fb1f83b8
    | 9 => 0xea5d6232c86bc45d46f15c8e338c22afd1afd1a00000012ca82be439a60becc5840e9d577dd00054433446501f762dc1898d42bea19460e8743a6000000d4fbb760b5c1cee39500082fe652230004e70004fc46efbee080b9e08000e70c5b0000009fab45bbc0002e526a000000000c5c71797d000000b6753c00020b5896501f8c4106b0009b30e51f5dffeebcfe868
    | 10 => 0x4de000a10466000d40000dc2bc7d7b00000020540400045b57a17e4090009d0000000087c5845b000000f3ac63112942bd50009c4000000000000000382c201acb860000d90adc1f0ac9a726c000000f9e9d6599d4e00023f7ce8d0000e6200089000000e8c1c15b54df2032e1905882059afa60003e651598ccef7c80009a31db9a3926e8d2872f91b0000fae00072b
    | 11 => 0x9ad7ff67b383cd22a6bc10c20ae300006fdb39a1af96f9236cdc22e826737000023505421c85941d800795a8160573f64890d00053158e7739c600041f0000003d66028b7cb67083e050da52be8c8f000f5133514bdac9c8dc1ede00020747c0000c6caceaf44b475d4557c770624c0fe758f2a86e2071c5bb7b94ff5ea6f1000a86c0b1c10005c40001a8c2cbfa000
    | 12 => 0xaf276f000aa60000006ad2664fe07f0ae06c8175fd7a5e7c1cf5ef000000fd636300e616000076a858c0182ce2e9819e39ab9036fc4fc949367c1a3dd49285d412b2670000823dea0000006b20007ee7d2785000ff0db8d6b596f4cf4ea09ccd2f932b00030e00073767828f06f34b3ab24b1d5ad7e920005ed6568df323fd6dc3793ffc00000035ef86f1c00094f027
    | 13 => 0xc2812eb7a1c8000080f480000000005d307950a0300004ce000949ee7000000c445cf7cf000ef427f11f00080f310164063ef1b66000bc60009ee03de52b28d1f000a83a31000857ec9000503acf06aeda9e018916d2c060e9a10005077ea4e7149b6c404260aeab1fa5a06c3e0caa222c536ddc91000ba648d58408148563bab99a13941f8e6e35470aa6c243
    | 14 => 0x8dce1100076d6404027fe00054390a735dd7432762acbc936a2f6896463a00039f9bf000000000a6d000451000000853367000bb710d51251e0a84b14a760e000000000115de084b366af092f2f4f2140dc620e100016830ee6a04b000961ae8645238539a8569702f4905338b68253f53ebb16000b69cb9c0b2328f662300000000091c0a66a964a4e3ccb2383475b5
    | 15 => 0x719fd2000d29140f6e0000002b40ed53d406981a0085d2b1731837c713f8c02a0200003d110d803e344a00044f46095e351000624051730100fc38fe73c000bd955d3b3bf370c39c57682be520008c55f4000129000f5746b82c00008d6fca87000ed0d8ddf191a52e0008f0a02b90fde00066d0009850000008a600001e061124705abcf392d2b4f000000000b848c4
    | 16 => 0x903d996f32d33b697463302000000418153000000000e5425d3cfbf700000000003d63e000acf4c1a5d3780005f9bf4000000ee1e1cdbe461000e07cbc81f316e0ab639cbfb441993369b000000cc0c6378d1080006b6000d5954e6294bc790420000bf714cfb300061163f4e05822f779e005a2cb570001ed5f662c000ca449d7cf67bbef000184955e19000af16c5
    | 17 => 0xfc6000e41259000ac1b2667300091620f2e2000615c2ea5000061500095cfcadea0003e126d6a6000556c41eb106e829aab00020cc8e77a0e917c2c5a670005eb02d5a0a77a326c23e6e3899e9b5be2b816522c7af1b588b6e7e4e7a4d3beeeacdf000241bec673ad3a7c6991480d994361ef4acb40000000002c8805ca600003800000000000007ac8300062e000
    | 18 => 0x783c2000000ec20bb68a1ef15140e9da39f000ca353e00009131a42066f202000000000644bc21dde3d6e79160005ce72be3735186ffaa8a5f0242d1c50055a7aa297b346d2f000c223e28f081deb789fdc22f40008870000002c2d5cc2348c94165900086e000778000000bc3817b4ebf440beea4f71d8000b8ac12567840b892e43487a1d74aa4b730631bc413356
    | 19 => 0xaf5257000000000bea8fcce1ac4a324cbd89000df30004834b5000000018000a51000b47000c930004daa4ba440000eb8b5c6d07141963000000000040996e000a9edf3f86ec1000bc4000efa40d0001529b2000d3f0007e61a1c39e8e610379f8f5eba71d6ee2c7fd0004b3c235e0e7b65713249e00016b8da13832aa9bd0b17809c95553297af8129d9a41cadc1818
    | 20 => 0x2745dc6fcfc55cca7b1e33e8fe700003e559d36298b773dcea06f9473120297ba40005285fb0b04286c7801d427f03510000000008de70ab5b9f30a4d9c0003a430ac2174dabb2687e8d02e90000b380000004e20007da9bcf285663548ea1b165563f000ce470bab2cc2107adaaf43d92adc745242eb021000e90da3189e1f10bec521131421e31bf18db56312ba492
    | 21 => 0x462df4000a324c907d0004170005ff03a03bdd8000f4c187fd400074293c000d48af4cd75e2cbf0009c4f60cda56c7d8c82e290008451df73c48f6ee813bd2c38888087045cca16b00086a3a327a0000007734f68b8000000e3151e45473b0dcfec000a9038bbb99bb559b2f0000004560008bba18db7000607000904f1731a547bbc17eca82e4f75dae773bda01fabf
    | 22 => 0xa6f1c884a12333c827af24f77cfb1374700043d000748000646c04000f6d04b2b9fba000f5dc4527e9a326c000fcaf8470fd4b85a00094e06c00045c6986a4eef0004414cf0000000780009da0002588ee3e17aa9f497d5fa000000a6679d48bb91a569875fe0006c0d4a799a4b5b56f5c57fdc000000000e7f929000000000e7fca90001580000000007713635295b0
    | 23 => 0x56da170e1000000114b730da791e075645409362350008eb067ba7000f7a3a22710004991faeafc5d78d0004821a300097b000782565000dc70001470001f14d599c3c8a6f4e71e200076c8a5d4c7b00006ef2060009d1000c5bff0593fbc340cf4bd1287da49ea07e096b95ede0001dcb98e7a629000a673bf000b334a45a80008cabd75daee83bb21635db23253e45
    | 24 => 0x8015546870f68042d60002bda7a71fb662f9b0a32f0bfd232c1f5e0000405490002bc629d614c707376558036db295b8277c6f17c83f25f4e36ae0003460a11ae0d500075d0001d8e88cab5e1548000ce65bc00028f000aa771deff147b7f96f7060a191ab3f739993fc6063535498000ca81fe24bbc4e07ad4db70005ef0027bc5ff0000000907be000f3a0002be
    | 25 => 0x91fe82e5d9f6a31423191000a4a530681ffc00074d1c70005f5df26290004ebc505086bae08ddb000f508a900013fc4a1ac0006e321ea52000db3119bae628000ed61157e9fff4bc0004b6af85a7d502f236ccd6c18000701aef4294c13875ba94a9836a04fffb25ad509460bae471351000a553b5ee653e000000000a67f0860a00086bee75794035fa46164e4ffda9
    | 26 => 0x72efa6c62fb92fe1f0000c04000eeff73a82399000fa1fc171881d27c4ba4c400049e94200095a5e8ed10008cf8dd00064f9441863c1975caa0007857c95db00038afa5b46d2faf124000000037f7bda5eeb441a09e000483ce1000000000d4600007900000082f99ad5c0007ec3db84f2e14b1d8000098397f8cb567e21f74000de7c3e23ca3b0000007306b0000
    | 27 => 0xc07469c1f82a63ac63634232d89404dd543b28c672000000c798aaf751c9d45df23ee6203d87927a5876c451d80000009b1681d1db041f84b06b30ca645a1661e8cc5582cad0bad97f800000036c2e201b2c7252000fd400034b00084d0001c6ec8000a947369beeb42620000008c57190820009afea30000568607ec872cff000416edb9e23d891fd86f58000d6e42f
    | 28 => 0x7e4ca0c455d521259e424032610a67000a058fb00089a92b000676e474643b581600055a0008d5f3a05493b0002a659579f36aedff54000eda92876d00067c000000e863b252e3efe60000cda7b600000000000084f5216730005e2000f5b2a28deb1c8cacaf4c1aadd10422000d4659fbc381d4bcd5c5fe1c946a06d7a4abaeaf41dcecea6b886a8000535a3949f05f
    | 29 => 0x558000fa259f98c291750d563d6438a2600074ba477f5d9a8eea529232abc9a9ff8ec000ebc00086c0000005cb0f970d64615a5709cbae2b40ccc35965662fa9ad85bdb000256000000dab07f0bff4e00083d1e0000f6d00046281a3c6924ac9fc59016b8fc122200064300040092abb5b970000000008e30000000007b0ef025e0000000003f5d794a1000be4037000
    | 30 => 0x10686c961b5b4ddc58350323ba6071304000ec0657e950006f5048000762dd59b5cdd000c31822998756299768d297c15ae7ba1ec9240003c9c6aae8ad5000dbf5228081124ee000f60889000632000c02432000868be3c5f00000093a4f8409000afaa2d000379e309c06ee7051a3c72268df4747c7700012584f000862622f28000000657cd3f3207b794bb60c85f3
    | 31 => 0xce313806e8a1000000a135ec000484000f0cb43000b8b08d937a75adc0000000000000000007ad0003e33748f72fd1d800027cd2656eb56a010003e6a4400036b8385be1a61b6f84a96fb244500000000000001a0bc39e0001ed000698d63a6b000ca909492a179cf33d761ed95d6c000bd56b32ae40d00038c12c70e4f07360ad0000004b300084c5bdecdfa3480402
    | 32 => 0x8d022649d3de000465000eb38a4da184a0e50004ef510000aa4baa91f6e4641
    | _ => 0
  fld v 12 (i % 96)
def action2 (ys : List Nat) := orbitLookup nextCodes 0 1031 (hk ys)
def rho2 (ys : List Nat) : List Nat :=
  let a := action2 ys/1737
  if a=0 then [] else
    let c := fld 0x118357ac688 21 a
    vals.map (fun v => fld 0x13100002491700000000000000000000000011400442053000000012f000024516004ba5a9890455167e00000011300436032c0044a227b851dcd2650000000cc0000000c10000000f9003adbb2b0000000f7003a5b72a003d5e863731548e39003259036003017e29002f578255c4a4441e002cd641c54062500a0049e4c07928140400 9 (orbitLabel c v))
def J (ys : List Nat) := action2 ys % 1737
def r2 (i : Nat) := bar 153 (cutB 9 (B i) C) (cutN 9 1737) (fun _ => J) (rowOrient 153 rho2) [] 10 0
set_option maxRecDepth 10000 in
lemma roofPart0 : span r2 1 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart1 : span r2 1 1 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart2 : span r2 1 2 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart3 : span r2 1 3 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart4 : span r2 1 4 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart5 : span r2 1 5 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart6 : span r2 1 6 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart7 : span r2 1 7 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart8 : span r2 1 8 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart9 : span r2 1 9 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart10 : span r2 1 10 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart11 : span r2 1 11 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart12 : span r2 1 12 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart13 : span r2 1 13 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart14 : span r2 1 14 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart15 : span r2 1 15 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart16 : span r2 1 16 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart17 : span r2 1 17 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart18 : span r2 1 18 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart19 : span r2 1 19 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart20 : span r2 1 20 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart21 : span r2 1 21 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart22 : span r2 1 22 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart23 : span r2 1 23 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart24 : span r2 1 24 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart25 : span r2 1 25 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart26 : span r2 1 26 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart27 : span r2 1 27 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart28 : span r2 1 28 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart29 : span r2 1 29 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart30 : span r2 1 30 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart31 : span r2 1 31 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart32 : span r2 1 32 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart33 : span r2 1 33 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart34 : span r2 1 34 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart35 : span r2 1 35 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma roofPart36 : span r2 1 36 = true := by decide +kernel
lemma secondRoofOK : span r2 37 0 = true := by with_reducible exact (sj (sj (sj (sj (sj roofPart0 roofPart1) (sj roofPart2 roofPart3)) (sj (sj roofPart4 roofPart5) (sj roofPart6 (sj roofPart7 roofPart8)))) (sj (sj (sj roofPart9 roofPart10) (sj roofPart11 roofPart12)) (sj (sj roofPart13 roofPart14) (sj roofPart15 (sj roofPart16 roofPart17))))) (sj (sj (sj (sj roofPart18 roofPart19) (sj roofPart20 roofPart21)) (sj (sj roofPart22 roofPart23) (sj roofPart24 (sj roofPart25 roofPart26)))) (sj (sj (sj roofPart27 roofPart28) (sj roofPart29 (sj roofPart30 roofPart31))) (sj (sj roofPart32 roofPart33) (sj roofPart34 (sj roofPart35 roofPart36))))))
def t2 (i : Nat) := ck 9 (C i)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart0 : span t2 53 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart53 : span t2 100 53 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart153 : span t2 42 153 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart195 : span t2 45 195 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart240 : span t2 40 240 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart280 : span t2 33 280 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart313 : span t2 43 313 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart356 : span t2 37 356 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart393 : span t2 51 393 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart444 : span t2 73 444 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart517 : span t2 81 517 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart598 : span t2 45 598 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart643 : span t2 11 643 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart654 : span t2 48 654 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart702 : span t2 89 702 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart791 : span t2 42 791 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart833 : span t2 8 833 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart841 : span t2 21 841 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart862 : span t2 39 862 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart901 : span t2 53 901 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart954 : span t2 14 954 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart968 : span t2 68 968 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1036 : span t2 79 1036 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1115 : span t2 54 1115 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1169 : span t2 42 1169 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1211 : span t2 49 1211 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1260 : span t2 22 1260 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1282 : span t2 100 1282 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1382 : span t2 96 1382 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1478 : span t2 71 1478 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1549 : span t2 40 1549 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1589 : span t2 41 1589 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1630 : span t2 10 1630 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1640 : span t2 11 1640 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1651 : span t2 14 1651 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1665 : span t2 16 1665 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1681 : span t2 27 1681 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1708 : span t2 22 1708 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma leafPart1730 : span t2 7 1730 = true := by decide +kernel
lemma secondTestOK : span t2 1737 0 = true := by with_reducible exact (sj (sj (sj (sj (sj leafPart0 leafPart53) (sj leafPart153 leafPart195)) (sj (sj leafPart240 leafPart280) (sj leafPart313 (sj leafPart356 leafPart393)))) (sj (sj (sj leafPart444 leafPart517) (sj leafPart598 (sj leafPart643 leafPart654))) (sj (sj leafPart702 leafPart791) (sj leafPart833 (sj leafPart841 leafPart862))))) (sj (sj (sj (sj leafPart901 leafPart954) (sj leafPart968 (sj leafPart1036 leafPart1115))) (sj (sj leafPart1169 leafPart1211) (sj leafPart1260 (sj leafPart1282 leafPart1382)))) (sj (sj (sj leafPart1478 leafPart1549) (sj leafPart1589 (sj leafPart1630 leafPart1640))) (sj (sj leafPart1651 leafPart1665) (sj leafPart1681 (sj leafPart1708 leafPart1730))))))
lemma upperDead (i : Nat) (hi : i < 37) : ¬NatRun (mask 153) (goal 153) 10 (B i) :=
  symCutRoot (ori_ok rho2) (spOK secondRoofOK i (Nat.zero_le _) hi)
    (fun j hj => checkpointCheck_sound closed (spOK secondTestOK j (Nat.zero_le _) hj))
theorem finChk : ¬NatRun (mask 153) (goal 153) 11 inputs :=
  symCutRoot (ori_ok rho) roof upperDead

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 12 ≤ t := by
  refine proveAtCap 7 153 11 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row30

end PEqualNP.Outside.L_meta_982_aux

theorem PEqualNP.Outside.L_meta_982 : (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) t → 12 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) t → 12 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) t → 12 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) t → 12 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) t → 12 ≤ t) := by
  exact ⟨
    PEqualNP.Outside.L_meta_982_aux.Row0.shard,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard01,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard02,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard03,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard04,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard05,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard06,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard07,
    PEqualNP.Outside.L_meta_982_aux.Row8.shard,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard09,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard10,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard11,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard12,
    PEqualNP.Outside.L_meta_982_aux.Row13.shard,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard14,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard15,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard16,
    (PEqualNP.Outside.L_meta_982_aux.Reduction.row17_of_row0 PEqualNP.Outside.L_meta_982_aux.Row0.shard),
    PEqualNP.Outside.L_meta_982_aux.Row18.shard,
    PEqualNP.Outside.L_meta_982_aux.Row19.shard,
    PEqualNP.Outside.L_meta_982_aux.Row20.shard,
    (PEqualNP.Outside.L_meta_982_aux.Reduction.row21_of_row0 PEqualNP.Outside.L_meta_982_aux.Row0.shard),
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard22,
    PEqualNP.Outside.L_meta_982_aux.Row23.shard,
    PEqualNP.Outside.L_meta_982_aux.Row24.shard,
    PEqualNP.Outside.L_meta_982_aux.Row25.shard,
    PEqualNP.Outside.L_meta_982_aux.Row26.shard,
    PEqualNP.Outside.L_meta_982_aux.Row27.shard,
    PEqualNP.Outside.L_meta_982_aux.Row28.shard,
    PEqualNP.Outside.L_meta_982_aux.Row29.shard,
    PEqualNP.Outside.L_meta_982_aux.Row30.shard⟩
