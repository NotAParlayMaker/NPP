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
      · exact fun i hi => span_ok z_K3_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3_3 i (Nat.zero_le i) hi
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
      · exact fun i hi => span_ok z_C5_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C5_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C5_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C5_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C5_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C5_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C5_6 i (Nat.zero_le i) hi
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
theorem z_BOWTIE_5 : span (Z_BOWTIE 5) 40 0 = true := (@span_join (Z_BOWTIE 5) 24 0 16 (@span_join (Z_BOWTIE 5) 12 0 12 h_BOWTIE_5_0 h_BOWTIE_5_12) (@span_join (Z_BOWTIE 5) 12 24 4 h_BOWTIE_5_24 h_BOWTIE_5_36))
theorem h_BOWTIE_6_0 : span (Z_BOWTIE 6) 12 0 = true := by decide +kernel
theorem h_BOWTIE_6_12 : span (Z_BOWTIE 6) 12 12 = true := by decide +kernel
theorem h_BOWTIE_6_24 : span (Z_BOWTIE 6) 12 24 = true := by decide +kernel
theorem z_BOWTIE_6 : span (Z_BOWTIE 6) 36 0 = true := (@span_join (Z_BOWTIE 6) 12 0 24 h_BOWTIE_6_0 (@span_join (Z_BOWTIE 6) 12 12 12 h_BOWTIE_6_12 h_BOWTIE_6_24))
theorem h_BOWTIE_7_0 : span (Z_BOWTIE 7) 1 0 = true := by decide +kernel
theorem z_BOWTIE_7 : span (Z_BOWTIE 7) 1 0 = true := h_BOWTIE_7_0
theorem base_BOWTIE : ∀ s : ℕ, HasCircuitSize 5 f_BOWTIE s → 8 ≤ s := by
  refine prove_base 5 50 7 f_BOWTIE rows_BOWTIE xs_BOWTIE pool_BOWTIE NN_BOWTIE HT_BOWTIE PT_BOWTIE
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_BOWTIE_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_6 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_7 i (Nat.zero_le i) hi
    )

-- Base case NET (n=6, cap=7, k=72, states=26, pool=9)
def f_NET : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)
def rows_NET : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 4, 8, 10, 10, 10, 12, 12, 12, 16, 17, 17, 17, 20, 20, 20, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 33, 33, 33, 34, 34, 34, 40, 40, 42, 42, 42, 42, 42, 42, 42, 42, 42, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 56, 56, 56, 56, 56, 56, 56, 56, 56, 3, 5, 9, 3, 6, 18, 5, 6, 36, 9, 11, 14, 26, 13, 14, 44, 18, 19, 21, 25, 21, 22, 52, 25, 26, 3, 5, 6, 9, 18, 29, 30, 36, 60, 36, 35, 37, 41, 35, 38, 50, 41, 44, 3, 5, 6, 9, 18, 36, 43, 46, 58, 50, 52, 3, 5, 6, 9, 18, 36, 51, 53, 57, 3, 5, 6, 9, 18, 36, 57, 58, 60]
def xs_NET : List ℕ := [0x25f2c25a78569e264f007fc00038000e0007, 0x4a955ea9c8ab235cb900000ff9c000001c38, 0x9329a53497cc74e9d20000000003fe70e1c0, 0xe4420e4622d188fe04ff800ffe03ff80fe00, 0xe874388102e1ff1020fffff00003ffff0000, 0xf0783f07ff00408100fffffffffc00000000]
def pool_NET : List ℕ := [0x1803000491204c, 0xd8060fc5012849, 0xac000fc4d12848, 0x64030fc501344c, 0x180000c4c12049, 0xc000184c12448, 0x64000fc5012849, 0xd8030fc4d12848, 0xac060fc501344c]
def NN_NET : ℕ → ℕ
  | 5 => 6
  | 6 => 19
  | 7 => 1
  | _ => 0
def HT_NET : ℕ → ℕ
  | 5 => 0xaf88224b70c6766557b62238571865263d1fc77a23def86d
  | 6 => 0xd5d2024bd11ae5e5cb9323a0bf32673cb6491b83b504a249b064ad26b04415efab09f6778f29c79884d9c66f80263ad760b07a3441b4b838403ba3af3ce49e4c2fdc23a307fae6c603fe551b
  | 7 => 0x80263ad7
  | _ => 0
def PT_NET : ℕ → ℕ
  | 5 => 0x14c0c530248c08f32048cc0f330
  | 6 => 0x64103c840f20018c0073101d0007320041401040040407500000001020194801000040c075103c400742
  | _ => 0
def Z_NET (s : ℕ) := bar 72 (Sgen 72 7 xs_NET PT_NET) NN_NET (idxGen NN_NET HT_NET) id pool_NET s
theorem z_NET_0 : span (Z_NET 0) 0 0 = true := rfl
theorem z_NET_1 : span (Z_NET 1) 0 0 = true := rfl
theorem z_NET_2 : span (Z_NET 2) 0 0 = true := rfl
theorem z_NET_3 : span (Z_NET 3) 0 0 = true := rfl
theorem z_NET_4 : span (Z_NET 4) 0 0 = true := rfl
theorem h_NET_5_0 : span (Z_NET 5) 6 0 = true := by decide +kernel
theorem z_NET_5 : span (Z_NET 5) 6 0 = true := h_NET_5_0
theorem h_NET_6_0 : span (Z_NET 6) 12 0 = true := by decide +kernel
theorem h_NET_6_12 : span (Z_NET 6) 7 12 = true := by decide +kernel
theorem z_NET_6 : span (Z_NET 6) 19 0 = true := (@span_join (Z_NET 6) 12 0 7 h_NET_6_0 h_NET_6_12)
theorem h_NET_7_0 : span (Z_NET 7) 1 0 = true := by decide +kernel
theorem z_NET_7 : span (Z_NET 7) 1 0 = true := h_NET_7_0
theorem base_NET : ∀ s : ℕ, HasCircuitSize 6 f_NET s → 8 ≤ s := by
  refine prove_base 6 72 7 f_NET rows_NET xs_NET pool_NET NN_NET HT_NET PT_NET
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_NET_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_6 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_7 i (Nat.zero_le i) hi
    )

-- Base case C6 (n=6, cap=7, k=78, states=8, pool=5)
def f_C6 : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def rows_C6 : List ℕ := [1, 1, 2, 2, 4, 4, 6, 6, 6, 8, 8, 9, 9, 9, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 36, 36, 36, 38, 38, 38, 38, 38, 38, 38, 38, 38, 3, 5, 3, 10, 5, 20, 7, 14, 22, 10, 40, 11, 13, 41, 3, 5, 10, 13, 14, 20, 28, 40, 44, 48, 20, 48, 19, 21, 49, 3, 5, 10, 19, 20, 22, 26, 40, 48, 50, 26, 28, 56, 3, 5, 10, 20, 27, 29, 40, 48, 57, 40, 48, 3, 5, 10, 20, 35, 37, 40, 41, 48, 49, 35, 42, 50, 37, 44, 52, 3, 5, 10, 20, 39, 40, 46, 48, 54]
def xs_C6 : List ℕ := [0x99359933005f00be15c0007fe7fc001c003803, 0xaa8e0a81533690152f37fe38000007fe00001cc, 0xad701502a419257a47cbffc0000000000ffc1f0, 0x322462374e6201dcfa200000007ff8000fffe00, 0xc449845b8fbc7e6004800000007ffffff000000, 0xf87ff87c09c04b809003ffffff8000000000000]
def pool_C6 : List ℕ := [0x24020d45813851, 0x1000074531384f, 0x60040d46513c53, 0x8000385113c4e, 0xcc090746514458]
def NN_C6 : ℕ → ℕ
  | 6 => 7
  | 7 => 1
  | _ => 0
def HT_C6 : ℕ → ℕ
  | 6 => 0xf44a7c96734fb6dc691bff606195314356426bf32c44989c2aa6f5bd
  | 7 => 0xf44a7c96
  | _ => 0
def PT_C6 : ℕ → ℕ
  | 6 => 0x41401000040c0102004100101
  | _ => 0
def Z_C6 (s : ℕ) := bar 78 (Sgen 78 7 xs_C6 PT_C6) NN_C6 (idxGen NN_C6 HT_C6) id pool_C6 s
theorem z_C6_0 : span (Z_C6 0) 0 0 = true := rfl
theorem z_C6_1 : span (Z_C6 1) 0 0 = true := rfl
theorem z_C6_2 : span (Z_C6 2) 0 0 = true := rfl
theorem z_C6_3 : span (Z_C6 3) 0 0 = true := rfl
theorem z_C6_4 : span (Z_C6 4) 0 0 = true := rfl
theorem z_C6_5 : span (Z_C6 5) 0 0 = true := rfl
theorem h_C6_6_0 : span (Z_C6 6) 7 0 = true := by decide +kernel
theorem z_C6_6 : span (Z_C6 6) 7 0 = true := h_C6_6_0
theorem h_C6_7_0 : span (Z_C6 7) 1 0 = true := by decide +kernel
theorem z_C6_7 : span (Z_C6 7) 1 0 = true := h_C6_7_0
theorem base_C6 : ∀ s : ℕ, HasCircuitSize 6 f_C6 s → 8 ≤ s := by
  refine prove_base 6 78 7 f_C6 rows_C6 xs_C6 pool_C6 NN_C6 HT_C6 PT_C6
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_C6_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_6 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_7 i (Nat.zero_le i) hi
    )

-- Base case TwoK3 (n=6, cap=8, k=102, states=122, pool=5)
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
theorem z_TwoK3_6 : span (Z_TwoK3 6) 58 0 = true := (@span_join (Z_TwoK3 6) 24 0 34 (@span_join (Z_TwoK3 6) 12 0 12 h_TwoK3_6_0 h_TwoK3_6_12) (@span_join (Z_TwoK3 6) 12 24 22 h_TwoK3_6_24 (@span_join (Z_TwoK3 6) 12 36 10 h_TwoK3_6_36 h_TwoK3_6_48)))
theorem h_TwoK3_7_0 : span (Z_TwoK3 7) 12 0 = true := by decide +kernel
theorem h_TwoK3_7_12 : span (Z_TwoK3 7) 12 12 = true := by decide +kernel
theorem h_TwoK3_7_24 : span (Z_TwoK3 7) 12 24 = true := by decide +kernel
theorem h_TwoK3_7_36 : span (Z_TwoK3 7) 12 36 = true := by decide +kernel
theorem h_TwoK3_7_48 : span (Z_TwoK3 7) 1 48 = true := by decide +kernel
theorem z_TwoK3_7 : span (Z_TwoK3 7) 49 0 = true := (@span_join (Z_TwoK3 7) 24 0 25 (@span_join (Z_TwoK3 7) 12 0 12 h_TwoK3_7_0 h_TwoK3_7_12) (@span_join (Z_TwoK3 7) 12 24 13 h_TwoK3_7_24 (@span_join (Z_TwoK3 7) 12 36 1 h_TwoK3_7_36 h_TwoK3_7_48)))
theorem h_TwoK3_8_0 : span (Z_TwoK3 8) 1 0 = true := by decide +kernel
theorem z_TwoK3_8 : span (Z_TwoK3 8) 1 0 = true := h_TwoK3_8_0
theorem base_TwoK3 : ∀ s : ℕ, HasCircuitSize 6 f_TwoK3 s → 9 ≤ s := by
  refine prove_base 6 102 8 f_TwoK3 rows_TwoK3 xs_TwoK3 pool_TwoK3 NN_TwoK3 HT_TwoK3 PT_TwoK3
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_TwoK3_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_6 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_7 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_8 i (Nat.zero_le i) hi
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
theorem z_K3C5_6 : span (Z_K3C5 6) 59 0 = true := (@span_join (Z_K3C5 6) 24 0 35 (@span_join (Z_K3C5 6) 12 0 12 h_K3C5_6_0 h_K3C5_6_12) (@span_join (Z_K3C5 6) 12 24 23 h_K3C5_6_24 (@span_join (Z_K3C5 6) 12 36 11 h_K3C5_6_36 h_K3C5_6_48)))
theorem h_K3C5_7_0 : span (Z_K3C5 7) 12 0 = true := by decide +kernel
theorem h_K3C5_7_12 : span (Z_K3C5 7) 12 12 = true := by decide +kernel
theorem h_K3C5_7_24 : span (Z_K3C5 7) 12 24 = true := by decide +kernel
theorem h_K3C5_7_36 : span (Z_K3C5 7) 12 36 = true := by decide +kernel
theorem h_K3C5_7_48 : span (Z_K3C5 7) 1 48 = true := by decide +kernel
theorem z_K3C5_7 : span (Z_K3C5 7) 49 0 = true := (@span_join (Z_K3C5 7) 24 0 25 (@span_join (Z_K3C5 7) 12 0 12 h_K3C5_7_0 h_K3C5_7_12) (@span_join (Z_K3C5 7) 12 24 13 h_K3C5_7_24 (@span_join (Z_K3C5 7) 12 36 1 h_K3C5_7_36 h_K3C5_7_48)))
theorem h_K3C5_8_0 : span (Z_K3C5 8) 1 0 = true := by decide +kernel
theorem z_K3C5_8 : span (Z_K3C5 8) 1 0 = true := h_K3C5_8_0
theorem base_K3C5 : ∀ s : ℕ, HasCircuitSize 6 f_K3C5 s → 9 ≤ s := by
  refine prove_base 6 88 8 f_K3C5 rows_K3C5 xs_K3C5 pool_K3C5 NN_K3C5 HT_K3C5 PT_K3C5
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_K3C5_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_6 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_7 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_8 i (Nat.zero_le i) hi
    )




def gfn {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) : BFn n :=
  fun x => A.any (fun a => x a) || E.any (fun e => x e.1 && x e.2)

def Eb_K3 : List (Fin 3 × Fin 3) := [(0,1),(0,2),(1,2)]
def Eb_C5 : List (Fin 5 × Fin 5) := [(0,1),(0,2),(1,3),(2,4),(3,4)]
def Eb_BOWTIE : List (Fin 5 × Fin 5) := [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)]
def Eb_NET : List (Fin 6 × Fin 6) := [(0,1),(0,2),(0,3),(1,2),(1,4),(2,5)]
def Eb_C6 : List (Fin 6 × Fin 6) := [(0,1),(0,2),(1,3),(2,4),(3,5),(4,5)]
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

theorem base_NET_gfn : ∀ s, HasCircuitSize 6 (gfn [] Eb_NET) s → 8 ≤ s := by
  have : gfn [] Eb_NET = f_NET := by funext x; simp [gfn, Eb_NET, f_NET, Bool.or_assoc]
  rw [this]; exact base_NET

theorem base_C6_gfn : ∀ s, HasCircuitSize 6 (gfn [] Eb_C6) s → 8 ≤ s := by
  have : gfn [] Eb_C6 = f_C6 := by funext x; simp [gfn, Eb_C6, f_C6, Bool.or_assoc]
  rw [this]; exact base_C6

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

theorem node0 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)]) s → 8 ≤ s := by
  exact gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 5), (1, 2), (3, 5)]) (fun i : Fin 6 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 5 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 5), (1, 2), (3, 5)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (fun i : Fin 6 => match i.val with | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (3 : Fin 5) | 5 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base16)

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

theorem node17 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (4, 6), (5, 6)]) s → 8 ≤ s := by
  exact gfn_base (E := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (4, 6), (5, 6)]) (Eb := [(0, 1), (0, 2), (0, 5), (2, 4), (4, 6), (5, 6)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 7) | 2 => (2 : Fin 7) | 4 => (4 : Fin 7) | 5 => (5 : Fin 7) | 6 => (6 : Fin 7) | _ => (0 : Fin 7)) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 5), (2, 4), (4, 6), (5, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)]) (fun i : Fin 7 => match i.val with | 1 => (3 : Fin 6) | 2 => (1 : Fin 6) | 4 => (4 : Fin 6) | 5 => (2 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base36)

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

theorem node23 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (2, 6), (3, 4)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (2, 6), (3, 4)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (2, 6), (3, 4)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (2, 6), (3, 4)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (2 : Fin 6) | 2 => (1 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base40)

theorem node24 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (3, 6)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (3, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4), (3, 6)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4), (3, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (3 : Fin 6) | 2 => (4 : Fin 6) | 3 => (1 : Fin 6) | 4 => (2 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base40)

theorem node25 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (5, 6)]) s → 11 ≤ s := by
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (5, 6)]) (p := (6 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) (A1 := [5]) (E1 := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 5 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base40) node20

theorem node26 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 6), (5, 6)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 6), (5, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 5), (3, 6), (5, 6)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 5), (3, 6), (5, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 5 => (4 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base41)

theorem node27 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (3, 6), (5, 6)]) s → 9 ≤ s := by
  exact gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (3, 6), (5, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (1, 2), (3, 6)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 7) | 2 => (2 : Fin 7) | 3 => (3 : Fin 7) | 4 => (4 : Fin 7) | 6 => (6 : Fin 7) | _ => (0 : Fin 7)) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (1, 2), (3, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (5 : Fin 6) | 6 => (4 : Fin 6) | _ => (0 : Fin 6)) (by decide) base39)

theorem node28 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (4, 6), (5, 6)]) s → 9 ≤ s := by
  exact gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (4, 6), (5, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (1, 2), (4, 6)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 7) | 2 => (2 : Fin 7) | 3 => (3 : Fin 7) | 4 => (4 : Fin 7) | 6 => (6 : Fin 7) | _ => (0 : Fin 7)) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (1, 2), (4, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (5 : Fin 6) | 4 => (3 : Fin 6) | 6 => (4 : Fin 6) | _ => (0 : Fin 6)) (by decide) base39)

theorem node29 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 6), (4, 6)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 6), (4, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 6), (4, 6)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 6), (4, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base41)

theorem node30 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (4, 5)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (4, 5)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 5 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base41)

theorem node31 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (3, 6), (5, 6)]) s → 8 ≤ s := by
  exact gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (3, 6), (5, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 6), (1, 2), (3, 6)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 7) | 2 => (2 : Fin 7) | 3 => (3 : Fin 7) | 4 => (4 : Fin 7) | 6 => (6 : Fin 7) | _ => (0 : Fin 7)) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 6), (1, 2), (3, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (3 : Fin 5) | 6 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base16)

theorem node32 : ∀ s, HasCircuitSize 7 (gfn [1] [(0, 2), (0, 3), (3, 5), (3, 6), (5, 6)]) s → 8 ≤ s := by
  exact gfn_fix0 (A := [1]) (E := [(0, 2), (0, 3), (3, 5), (3, 6), (5, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(0, 2), (0, 3), (3, 5), (3, 6), (5, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 2), (0, 3), (3, 5), (3, 6), (5, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (fun i : Fin 7 => match i.val with | 0 => (3 : Fin 5) | 2 => (4 : Fin 5) | 5 => (1 : Fin 5) | 6 => (2 : Fin 5) | _ => (0 : Fin 5)) (by decide) base14)

theorem node33 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (5, 6)]) s → 10 ≤ s := by
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (5, 6)]) (p := (4 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (3, 6), (5, 6)]) (A1 := [1]) (E1 := [(0, 2), (0, 3), (3, 5), (3, 6), (5, 6)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) node31 node32

theorem node34 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5), (5, 6)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5), (5, 6)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 5 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base41)

theorem node35 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 4), (3, 5)]) s → 9 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 4), (3, 5)]) (p := (2 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 3), (0, 4), (0, 5), (1, 4), (3, 5)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 3), (0, 4), (0, 5), (1, 4), (3, 5)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 5) | 3 => (3 : Fin 5) | 4 => (2 : Fin 5) | 5 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base16)

theorem node36 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 6), (5, 6)]) s → 9 ≤ s := by
  exact gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 6), (5, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 4), (3, 5)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 7) | 2 => (2 : Fin 7) | 3 => (3 : Fin 7) | 4 => (4 : Fin 7) | 5 => (5 : Fin 7) | _ => (0 : Fin 7)) (by decide) node35

theorem node37 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5), (4, 6), (5, 6)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5), (4, 6), (5, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (4, 5), (4, 6), (5, 6)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2), (4, 5), (4, 6), (5, 6)]) (Eb := [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 4 => (3 : Fin 6) | 5 => (4 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base37)

theorem node38 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6), (4, 5), (4, 6)]) s → 9 ≤ s := by
  exact gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6), (4, 5), (4, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (2, 5), (3, 6)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 7) | 2 => (2 : Fin 7) | 3 => (3 : Fin 7) | 5 => (5 : Fin 7) | 6 => (6 : Fin 7) | _ => (0 : Fin 7)) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (2, 5), (3, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (5 : Fin 6) | 2 => (1 : Fin 6) | 3 => (3 : Fin 6) | 5 => (2 : Fin 6) | 6 => (4 : Fin 6) | _ => (0 : Fin 6)) (by decide) base39)

theorem node39 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (3, 4), (5, 6)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (3, 4), (5, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (3, 4), (5, 6)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (3, 4), (5, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)]) (fun i : Fin 7 => match i.val with | 2 => (5 : Fin 6) | 3 => (1 : Fin 6) | 4 => (2 : Fin 6) | 5 => (3 : Fin 6) | 6 => (4 : Fin 6) | _ => (0 : Fin 6)) (by decide) base39)

theorem node40 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 6), (3, 4), (5, 6)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 6), (3, 4), (5, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 4), (1, 2), (1, 5), (1, 6), (5, 6)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 4), (1, 2), (1, 5), (1, 6), (5, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) (fun i : Fin 7 => match i.val with | 0 => (1 : Fin 6) | 2 => (2 : Fin 6) | 4 => (5 : Fin 6) | 5 => (3 : Fin 6) | 6 => (4 : Fin 6) | _ => (0 : Fin 6)) (by decide) base40)

theorem node41 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (3, 6), (5, 6)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (3, 6), (5, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 3), (0, 4), (1, 5), (3, 4), (3, 6), (5, 6)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 3), (0, 4), (1, 5), (3, 4), (3, 6), (5, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) (fun i : Fin 7 => match i.val with | 1 => (3 : Fin 6) | 3 => (1 : Fin 6) | 4 => (2 : Fin 6) | 5 => (5 : Fin 6) | 6 => (4 : Fin 6) | _ => (0 : Fin 6)) (by decide) base41)

theorem node42 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 6), (4, 6), (5, 6)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 6), (4, 6), (5, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (1, 4), (2, 5), (4, 6), (5, 6)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2), (1, 4), (2, 5), (4, 6), (5, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) (fun i : Fin 7 => match i.val with | 0 => (2 : Fin 6) | 2 => (1 : Fin 6) | 4 => (3 : Fin 6) | 5 => (4 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base41)

theorem node43 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (4, 5), (5, 6)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (4, 5), (5, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 3), (1, 4), (3, 5), (3, 6), (4, 5), (5, 6)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 3), (1, 4), (3, 5), (3, 6), (4, 5), (5, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) (fun i : Fin 7 => match i.val with | 0 => (3 : Fin 6) | 1 => (5 : Fin 6) | 4 => (4 : Fin 6) | 5 => (1 : Fin 6) | 6 => (2 : Fin 6) | _ => (0 : Fin 6)) (by decide) base41)

theorem shard00 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) t → 8 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node0

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

theorem shard08 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 8 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (4, 6), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node17

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

theorem shard13 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (2, 6), (3, 4)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node23

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

theorem shard17 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (3, 6), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node27

theorem shard18 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (4, 6), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node28

theorem shard19 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 6), (4, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node29

theorem shard20 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (4, 5)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node30

theorem shard21 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node33

theorem shard22 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node34

theorem shard23 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 6), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node36

theorem shard24 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5), (4, 6), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node37

theorem shard25 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6), (4, 5), (4, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node38

theorem shard26 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (3, 4), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node39

theorem shard27 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 6), (3, 4), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node40

theorem shard28 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (3, 6), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node41

theorem shard29 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 6), (4, 6), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node42

theorem shard30 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) t → 10 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (4, 5), (5, 6)] := by
    funext x
    simp [gfn, Bool.or_assoc]
  rw [heq]
  exact node43

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

def checkD (k : Nat) (scores : List Nat) : Nat → List Nat → Bool
  | 0, ws => !(ws == [goal k])
  | s+1, ws => !(nextCovered k s ws (fun _ zs =>
      !(scr k s scores zs) && !(checkD k scores s zs)))

theorem checkD_sound {k s ws scores} (ok : checkD k scores s ws = true) :
    ¬NatRun (mask k) (goal k) s ws := by
  intro h
  induction s generalizing ws with
  | zero => simp [checkD, zero_done h rfl] at ok
  | succ s ih =>
    let F (_ : Nat) (zs : List Nat) : Bool := covers k s zs &&
      (!(scr k s scores zs) && !(checkD k scores s zs))
    have all : ∀ t ys, NatRun (mask k) (goal k) s ys → F t ys = true := by
      intro t ys hy
      have bad : checkD k scores s ys = false := by
        cases he : checkD k scores s ys
        · rfl
        · exact False.elim (ih he hy)
      simp [F, covers_ok hy, scr_no scores hy, bad]
    have hit := next_complete h s rfl _ (List.Perm.refl _) F all
    rw [checkD, nextCovered_eq] at ok
    rw [hit] at ok
    contradiction

def insertWord (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: rest => if a ≤ b then a :: b :: rest else b :: insertWord a rest

def sortWords : List Nat → List Nat
  | [] => []
  | a :: rest => insertWord a (sortWords rest)

def checkpointBoard (m : Nat) (xs : List Nat) : Nat → Nat → List Nat
  | 0, _ => sortWords xs
  | d+1, c => sortWords (mv m (c % 4096) (checkpointBoard m xs d (c / 4096)))

def checkpointHit (count : Nat → Nat) (board : Nat → Nat → List Nat)
    (lookup : Nat → List Nat → Option Nat) (s : Nat) (ws : List Nat) : Bool :=
  match lookup s ws with
  | none => false
  | some i => decide (i < count s) && ws.isPerm (board s i)

def checkpointCheck (k : Nat) (scores : List Nat) (count : Nat → Nat)
    (board : Nat → Nat → List Nat) (lookup : Nat → List Nat → Option Nat) : Nat → List Nat → Bool
  | 0, ws => !(ws == [goal k])
  | s+1, ws => !(nextCovered k s ws (fun _ zs =>
      !(scr k s scores zs) && !(checkpointHit count board lookup s zs) &&
        !(checkpointCheck k scores count board lookup s zs)))

theorem checkpointCheck_sound {k scores count board lookup}
    (closed : ∀ s i, i < count s → checkpointCheck k scores count board lookup s (board s i) = true)
    {s ws} (ok : checkpointCheck k scores count board lookup s ws = true) :
    ¬NatRun (mask k) (goal k) s ws := by
  intro h
  induction s generalizing ws with
  | zero => simp [checkpointCheck, zero_done h rfl] at ok
  | succ s ih =>
    let F (_ : Nat) (zs : List Nat) : Bool := covers k s zs && (!(scr k s scores zs) &&
      !(checkpointHit count board lookup s zs) && !(checkpointCheck k scores count board lookup s zs))
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
      have bad : checkpointCheck k scores count board lookup s ys = false := by
        cases he : checkpointCheck k scores count board lookup s ys
        · rfl
        · exact False.elim (ih he hy)
      simp [F,covers_ok hy,scr_no scores hy,nohit,bad]
    have hit := next_complete h s rfl _ (List.Perm.refl _) F all
    rw [checkpointCheck, nextCovered_eq] at ok
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


def rowOrient (k : Nat) (sel : List Nat → List Nat) (ys : List Nat) : List Nat :=
  let r := sel ys
  if pickRows r (mask k) = mask k ∧ pickRows r (goal k) = goal k then ys.map (pickRows r) else ys

theorem rowOrient_sound {k u ys} (sel : List Nat → List Nat) (h : NatRun (mask k) (goal k) u ys) :
    NatRun (mask k) (goal k) u (rowOrient k sel ys) := by
  unfold rowOrient
  dsimp only
  split
  next e =>
    have tr := transport h (sel ys)
    rw [e.1, e.2] at tr
    exact tr
  next => exact h
def cutCount (s n u : Nat) := if u = s then n else 0

def cutBoard (s : Nat) (xs : List Nat) (board : Nat → List Nat) (u i : Nat) :=
  if u = s then board i else xs

theorem cut_root {k s n : Nat} {xs pool : List Nat}
    {board : Nat → List Nat} {idx : List Nat → Nat}
    (cover : bar k (cutBoard s xs board) (cutCount s n) (fun _ => idx) id pool (s+1) 0 = true)
    (dead : ∀ i, i < n → ¬NatRun (mask k) (goal k) s (board i)) :
    ¬NatRun (mask k) (goal k) (s+1) xs := by
  intro h
  have hr : NatRun (mask k) (goal k) (s+1) (cutBoard s xs board (s+1) 0) := by
    simpa [cutBoard] using h
  obtain ⟨q, _, j, hj, hq⟩ := bar_sound cover (fun h => h) hr
  by_cases e : q = s
  · subst q
    exact dead j (by simpa [cutCount] using hj) (by simpa [cutBoard] using hq)
  · simp [cutCount, e] at hj
theorem symCutRoot {k s n : Nat} {xs pool : List Nat}
    {board : Nat → List Nat} {idx : List Nat → Nat}
    {ori : List Nat → List Nat}
    (perm : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (cover : bar k (cutBoard s xs board) (cutCount s n) (fun _ => idx) ori pool (s+1) 0 = true)
    (dead : ∀ i, i < n → ¬NatRun (mask k) (goal k) s (board i)) :
    ¬NatRun (mask k) (goal k) (s+1) xs := by
  intro h
  have hr : NatRun (mask k) (goal k) (s+1) (cutBoard s xs board (s+1) 0) := by
    simpa [cutBoard] using h
  obtain ⟨q, _, j, hj, hq⟩ := bar_sound cover perm hr
  by_cases e : q = s
  · subst q
    exact dead j (by simpa [cutCount] using hj) (by simpa [cutBoard] using hq)
  · simp [cutCount, e] at hj

namespace Row0
def vals : List ℕ := [1, 1, 1, 2, 2, 4, 4, 8, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 3, 5, 9, 3, 6, 5, 6, 9, 24, 40, 3, 5, 6, 9, 11, 14, 24, 26, 40, 42, 48, 3, 5, 6, 9, 13, 14, 24, 28, 40, 44, 48, 24, 48, 3, 5, 6, 9, 19, 21, 24, 25, 40, 48, 49, 3, 5, 6, 9, 19, 22, 24, 26, 40, 48, 50, 3, 5, 6, 9, 21, 22, 24, 28, 40, 48, 52, 40, 48, 3, 5, 6, 9, 24, 35, 37, 40, 41, 48, 49, 3, 5, 6, 9, 24, 35, 38, 40, 42, 48, 50, 3, 5, 6, 9, 24, 37, 38, 40, 44, 48, 52]
def inputs : List ℕ := [0x560aeb5806c0dcbb00d81b2bc00000ffe000001ffc00000007, 0x8b5941280965a815012ab5164007ff000000ffe000001ffc18, 0xacc1182312d81302615b0261cbff8000007ff000000ffe00060, 0x330660cc2720e41c85fc3f8e1000000000000000000ffffff80, 0xc21843085bc3786f0e604c0400000000007ffffffff00000000, 0xfc1f83f07c0380700b80700803ffffffff80000000000000000]
def scores : List ℕ := [0x1141516c6f19c68, 0xe02d088671986a, 0x1402d0286f1b87a, 0x88151147a1a06e, 0xe0220b46a19867, 0x1404516c6a19c66, 0x1140a1406f19868, 0x880a0e06e19c68, 0x1140a0887a1b86f, 0x1140a054681a866, 0x880a0b46e19868]
def target : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def rho (ys : List Nat) : List Nat :=
  match fld 0xc2442484a9320293200f4a0006d822688000 3 (bsr 0xf7831134f4fedb03ef42530ceeb6ca99dd448942d75a4f37d12435e6ceeaee09cdfdf8d5c84b49c4c0a8f783b5e46551b359a4deb279c2a1b0edf685b0147856aee40560ae8440cba181a3399de14f0f9b4f693095865b2993b4971e9375f304880f16b08715b59f73aa60ef6f5f01b26e5e2e6b6decb162639a36156375fee9527a8cb85157812a493de4eb4577ef263b056ff32e79e25f2c0f0be325862c5321a9d46920ee1b271e6cd2651774472c1683bb1211c516140dd37f0e0aa5544e073f6720 32 (hk ys) 6 0 49) with
  | 1 => vals.map (fun r => fld 0x9d00a8927a000000790084b36f00bcb050b15b45430000007700828f6e00988c2d8d3822200075740a7f156807006a660367050000 8 r)
  | 2 => vals.map (fun r => fld 0xa8009d927a0000008200778f6e00988d388c2d2220000000840079b36f00bcb15bb050454300757f15740a6807006a670566030000 8 r)
  | 3 => vals.map (fun r => fld 0x9d00a8927a0000007700828f6e00988c2d8d382220000000790084b36f00bcb050b15b45430075740a7f156807006a660367050000 8 r)
  | 4 => vals.map (fun r => fld 0xbc0098756a000000b1008d7f6700a8845b82381505000000b0008c7466009d7950772d0a030092b3458f226800007a6f436e200700 8 r)
  | 5 => vals.map (fun r => fld 0x9800bc756a0000008d00b17f6700a88238845b15050000008c00b07466009d772d79500a0300928f22b3456800007a6e206f430700 8 r)
  | 6 => vals.map (fun r => fld 0xbc0098756a000000b0008c7466009d7950772d0a03000000b1008d7f6700a8845b823815050092b3458f226800007a6f436e200700 8 r)
  | _ => []
def B (i : Nat) := mv (mask 102) (fld 0xe21e30e41105505f41503f31f30000f10400e40401f21103e10 12 i) inputs
def I (ys : List Nat) := bsr 0xf7831134ef42530cd12435e6ae8440cba181a339880f16b08715b59f639a36156375fee9527a8cb85157812a2c0f0be31683bb1211c516140dd37f0e0aa5544e073f6720 32 (hk ys) 5 0 17
def test (i : Nat) := checkD 102 scores 8 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 102 (cutBoard 8 inputs B) (cutCount 8 17) (fun _ => I) (rowOrient 102 rho) scores 9 0 = true := by decide +kernel
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
lemma regionOK : span test 17 0 = true := (@span_join test 8 0 9 (@span_join test 4 0 4 z0 z4) (@span_join test 4 8 5 z8 (@span_join test 2 12 3 z12 z14)))
theorem finiteCheck : ¬NatRun (mask 102) (goal 102) 9 inputs :=
  symCutRoot (rowOrient_sound rho) roof (fun i hi => checkD_sound (span_ok regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 6 target t → 10 ≤ t := by
  refine proveAtCap 6 102 9 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finiteCheck

end Row0

namespace Row8
def vals : List ℕ := [1, 1, 2, 2, 4, 4, 6, 6, 6, 8, 8, 9, 9, 9, 12, 12, 12, 12, 16, 16, 17, 17, 17, 18, 18, 18, 18, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 32, 32, 33, 33, 33, 33, 34, 34, 34, 36, 36, 36, 36, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 64, 64, 65, 65, 65, 65, 66, 66, 66, 66, 68, 68, 68, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 72, 72, 72, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 3, 5, 3, 10, 5, 20, 7, 14, 22, 10, 40, 11, 13, 41, 13, 14, 28, 44, 20, 80, 19, 21, 81, 19, 22, 26, 82, 26, 28, 56, 88, 3, 5, 10, 20, 27, 29, 40, 57, 80, 89, 96, 40, 96, 35, 37, 41, 97, 35, 42, 98, 37, 44, 52, 100, 3, 5, 10, 20, 39, 40, 46, 54, 80, 96, 102, 52, 56, 112, 3, 5, 10, 20, 40, 51, 53, 57, 80, 96, 113, 3, 5, 10, 20, 40, 51, 54, 58, 80, 96, 114, 80, 96, 67, 69, 81, 97, 67, 74, 82, 98, 69, 84, 100, 3, 5, 10, 20, 40, 71, 78, 80, 86, 96, 102, 74, 88, 104, 3, 5, 10, 20, 40, 75, 77, 80, 89, 96, 105, 3, 5, 10, 20, 40, 77, 78, 80, 92, 96, 108]
def inputs : List ℕ := [0x4758c02323e0239c600989f15980f07857001ffc00001e000ffe00000f3ff80703803, 0x8a094d651e24e504a26a87100a8f908bcd0000007ff1e07ff0003ff870000078001cc, 0xad412856ae0404a09466d7820151127d1f2ffe0007ffe000000003fff800000003c1f0, 0xae95d385404009412883212457a7a03fe88ffffff8000000000000000003fff803fe00, 0x310621188488de8bd1cc42001dc7ffd01200000000000007fffffc000003fffffc0000, 0xc218426109116f0de1f787ffe60200224000000000000007fffffffffffc0000000000, 0xfc1f83fe0ffff00e01380448b8044480000ffffffffffff80000000000000000000000]
def scores : List ℕ := [0x1d8682048f2348c, 0x1d84507c9f258b5, 0x1a0500dcb52449f, 0xdc1f114962308f, 0xdc1f140912308d, 0x1d8371a0b523c96, 0x1a01f1d89f23491]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def rho (ys : List Nat) : List Nat :=
  match fld 0x390316102385a747615795325321322065498800498870526050420542332101 4 (bsr 0xffb93cdefabd6fedf7423f9ff582b9f1f3eea8d9f1d7b75be9e8d5bae5792811e114fcb2df5d4d4adc65c784da702df4d622589bcfb96cf1cec4936bca9679c0c7c1e596c27abfbebd935c50b84dff99b6afeed9b5124aadb06b5123abf9511da91b880da8bfc72fa3016442a219af959d6d03769cd84ac39b5f3f3a969bfb69910afed88cf5763a8579a19a804750dd7e6767d87d7567f679c1958678a4f16178a3812770f9676d6a3fff10689e704a676cd73d647d8899587d0c395843e1385545aa6351ec39f451744c1d4a197648498a981d3dcd5e1a391e942f367f10d32e65260a29ce9e4826bdf0a919042b95183e48a70fd8f69e0644477e063cd20e 32 (hk ys) 7 0 64) with
  | 1 => vals.map (fun r => fld 0x455f8f20000000db00001ccd0002d000a2002a94c9f0000000d70000194c1002c000a1002712891002c9ac4571aa4a0425787d40145286c2e120000000000045d9ac200421f2ea7d204d0650043000bb004057cb5839d9d25d771ccc25b000018eb964a746e3300261248d498380c0400265702c5ea58602a4b82d1800478240400 9 r)
  | 2 => vals.map (fun r => fld 0x325c6bd000000107000015e97003e800ee0024d4a8f00000010c0000164990045c0101002755296004216876582603e0b8aa0554734e03836090000000000031dacb800335ccbe650dca030003e400e900249408c7e1a14c614a0182e0200001b6bb6bae48a2c00309a0b5608cc842a003a9445d50a342800791953e5b488102400 9 r)
  | 3 => vals.map (fun r => fld 0x2c1aea10000000f9000018e920042000ea00261728d0000000fc0000194940045400f2002718291003e99a6864a4c6e068ba0584654e8386604000000000002bdaca0002d1b6a25907c8a140041c00e90025d708c861d9765d4c82c580000001cca671a94a017002a9a09f5486c8412003b97c615ea3c6002809cd6a5b4b0245400 9 r)
  | 4 => vals.map (fun r => fld 0x41d5e970000000c900001c6bd003e80093003b94a8f0000000c700001acb8003e40092003a5408c003359437732f8a0307e1a12806531842e020000000000043164990042160985a1d83e0b0045c009d0040552968aa05380e551cc360900001aeb96daec8a2c003a9428d511742800003098233682d4842a7919522044f96c2400 9 r)
  | 5 => vals.map (fun r => fld 0x45e19010000000e600001b6d00033400be0030976b50000000e30000164a90032400bd00275329600329ac506bb048a42638dd70305c8cc582a0000000000045568aa003ea0eee84204ec73003f000a6003c9449f7c9a1d26175194ba5b000015ea5582703e1b0024d2e8f4c038160900251401750a442812490191802468100000 9 r)
  | 6 => vals.map (fun r => fld 0x3f22af20000000d70000160a10032800c10025138910000000db0000168a20039800d000299549f00359644557a803e147194152425285c3612000000000003e610ea003362ec27d1a102650031c00b900249308d648dd3a33498181c040000218bb83ba4ec5d002fa02b577184e65b002e1322c4ba3016005e8c12c2a478081200 9 r)
  | 7 => vals.map (fun r => fld 0x36dccd000000011500001f8f2002d000aa002894c9f000000117000019ac2004300101002ed7cb500421f4817cba8d065839d9dc7374974c25b0000000000035d94c1002c9c6a96b114a042002c0009c0028528915787d4a1b500502e1200001929d63ae46e33002657a965c0b0602a00261260e492340c044b82d1e09460000400 9 r)
  | 8 => vals.map (fun r => fld 0x3e58e920000000b000001aea1004200098003a9728d0000000af00001aca00041c0097003a5708c002d1641f6da888a14861d9320b5d9745800000000000003f19494003e99293669a06e0600454009c003c982918ba053a0e61194660400001c6a573298a017003b97a8f5f1846002002a9521b6827c8412809cd2c095a96c5400 9 r)
  | 9 => vals.map (fun r => fld 0x4322f010000000e30000192bd002c800a9002653a960000000e6000019abe0036c00d0002ed84b500359945063ae06e306b91582425c8b0662a0000000000041df4ee002d22aaa841d90273002bc00a50025d268f5807d381b4c02c1c0900001f8a67cba4d06100289e49f75174ca5b002812817492300c02508512212468000800 9 r)
  | 10 => vals.map (fun r => fld 0x2be0e970000000c700001f2920035800b800281d28c0000000c900001f4930038c00bd00295dc8f003299a377e250d006731417c305305cc202000000000002c21098002ca18995a07cec0b0035c00b900285d48d6d915762c51050ba00000022e9d8aa71020e002a602965506ce60900305843379244ca04681096a2a4f848b600 9 r)
  | _ => []
def B (i : Nat) := mv (mask 140) (fld 0xe10f41506e54000400f40f10106e41 12 i) inputs
def I (ys : List Nat) := bsr 0xf7423f9fe5792811969bfb6979c1958678a4f161647d889951ec39f44a197648391e942f0644477e 32 (hk ys) 4 0 10
def test (i : Nat) := checkD 140 scores 8 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 140 (cutBoard 8 inputs B) (cutCount 8 10) (fun _ => I) (rowOrient 140 rho) scores 9 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 2 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z2 : span test 3 2 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z5 : span test 2 5 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z7 : span test 3 7 = true := by decide +kernel
lemma regionOK : span test 10 0 = true := (@span_join test 5 0 5 (@span_join test 2 0 3 z0 z2) (@span_join test 2 5 3 z5 z7))
theorem finiteCheck : ¬NatRun (mask 140) (goal 140) 9 inputs :=
  symCutRoot (rowOrient_sound rho) roof (fun i hi => checkD_sound (span_ok regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 10 ≤ t := by
  refine proveAtCap 7 140 9 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finiteCheck

end Row8

namespace Row13
def vals : List ℕ := [1, 1, 1, 1, 2, 2, 2, 4, 4, 4, 8, 8, 10, 10, 10, 10, 12, 12, 12, 12, 16, 16, 18, 18, 18, 18, 20, 20, 20, 20, 32, 33, 33, 33, 33, 36, 36, 36, 40, 40, 40, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 48, 48, 48, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 64, 65, 65, 65, 65, 66, 66, 66, 72, 72, 72, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 80, 80, 80, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 96, 96, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 104, 104, 104, 104, 104, 104, 104, 104, 104, 104, 104, 104, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 112, 3, 5, 9, 17, 3, 6, 34, 5, 6, 68, 9, 24, 11, 14, 26, 42, 13, 14, 28, 76, 17, 24, 19, 22, 26, 50, 21, 22, 28, 84, 34, 35, 37, 41, 49, 37, 38, 100, 41, 42, 56, 3, 5, 6, 9, 17, 24, 34, 45, 46, 60, 68, 108, 49, 50, 56, 3, 5, 6, 9, 17, 24, 34, 53, 54, 60, 68, 116, 68, 67, 69, 73, 81, 67, 70, 98, 73, 76, 88, 3, 5, 6, 9, 17, 24, 34, 68, 75, 78, 90, 106, 81, 84, 88, 3, 5, 6, 9, 17, 24, 34, 68, 83, 86, 90, 114, 98, 100, 3, 5, 6, 9, 17, 24, 34, 68, 99, 101, 105, 113, 3, 5, 6, 9, 17, 24, 34, 68, 105, 106, 108, 120, 3, 5, 6, 9, 17, 24, 34, 68, 113, 114, 116, 120]
def inputs : List ℕ := [0x11b11bf1b046c88d93e09b21364f8451149f000000fff000000001e0000000078000000f, 0x2452451457d147a28e2145428a90cbc2f1710000000003ffc7ff8e000000000003c0f070, 0x4864862868a19143245f861f0c393c8f23a20000000000000000000fff1ffe383c0f0380, 0x828f2842810a27947082289751c2112ffc04000fff00000007fff000001fffc0000ffc00, 0xf308308303cc3a18410bb0e461043ff44808fff0000003fff800000fffe000003ff00000, 0xf40f40f40e100420080bc0f781ffc2008040fffffffffc000000000fffffffffc0000000, 0xf80f80f80fe03fc07ffc0018002020080200fffffffffffffffffff00000000000000000]
def scores : List ℕ := [0x210781b0932489b, 0x13c291e09925895, 0x1b0290e09b24c92, 0x1b05e13c9b24093, 0x1b0291e09924891, 0x1b04f1e09624890, 0x1b0381789325491, 0x1b04f1789b24c92, 0x1b04f0a49524490, 0x13c382109925895, 0x1b0290e09b24492, 0x1b0380a49b24893, 0x13c291b09924095, 0x1b05e0e09624c90, 0x1b04f0e09325496, 0x1b05e0e09524490, 0x1b02913c9924091, 0x1b0292109924c91, 0x13c291b09124099]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)
def rho (ys : List Nat) : List Nat :=
  match fld 0x410491615c4c61879001472004085200024 2 (bsr 0xfec2e0a6fb828f20f957e4b6f6775b50edc75f20e7e8002fe55b79a3e248fac0df9b3e41df6c305dddc57c74dd7e3b8edaf1b502da6af460da0097e5d6c6b9f9d5c5105dd4b15d83ca77149ac7fabf8bc0994494c0922f4db8ca5e19b6c3adebaaa547aca9085f8fa2f2d5f2a2ab883a9e7733ac93cc3e9d8eb19e27872f76d9864f32ce8336ba717daa46ee7d3c8db47c7b514477b25c0b6f26116f6ec645866c998ae35d1ff5f951f0f60450c3b84d4a810e8a4a0dd619457e3ffc37bc66913786270730541d362cd540902ca29bed2a16156129bdc33d28c110b624a8a85720c1af3b205f4dd61f43052f17fff0a9171e26bd140972810e591ac00e13c6420dabd1680b1f4adc08bd97d908ab4b81083f91b402a08c45 32 (hk ys) 7 0 70) with
  | 1 => vals.map (fun r => fld 0x1130000000f90034e0e840000000ea003120c780000208db82ad4d86a0000000000030800b80034000a9678e1643500304009f600a56226002d15e965808c3e1e0000000e90000000de003ddec5e002b5b05b003a1ce4f0028dae4c00369aa496b2648a4400000009e00288009b0029d4c1655069261400275380c50041240a0025520044881c0000 9 r)
  | 2 => vals.map (fun r => fld 0x1130000000c4003aa0c780000000d3003e60e84000020ab58236cd86a000000000003a400de003a000a37393dae4c003dc00ad7b179b05b00369ac996a9248a440000000c20000000b80030580290027d6226003419e38002a56435002d1602357a583e1e0000000a200278009b0027540104e031240a0029d541a530592614002552207480100000 9 r)
  | 3 => vals.map (fun r => fld 0x1130000000ea003120c780000000f90034e0e840000208db82ad4d86a0000000000030800b800304009f600a562260034000a9678e16435002d15e965808c3e1e0000000e90000000de003a1ce4f0028dae4c003ddec5e002b5b05b00369aa496b2648a4400000009e00288009b00275380c50041240a0029d4c165506926140025520044881c0000 9 r)
  | _ => []
def B (i : Nat) := mv (mask 144) (fld 0xf65e53f43000102f10e43e21e31f53100403e30f30400e10760f50504e51e61500e65106506104405f51f21401f31e50761f61651502 12 i) inputs
def I (ys : List Nat) := bsr 0xfb828f20f957e4b6edc75f20e7e8002fe248fac0ddc57c74da0097e5c7fabf8bc0922f4db6c3adeba2f2d5f293cc3e9d7daa46ee7d3c8db47c7b514477b25c0b6f26116f5d1ff5f94a810e8a457e3ffc37bc66913786270730541d362ca29bed2a16156129bdc33d24a8a8571f43052f171e26bd140972810e591ac00e13c6420dabd1680b1f4adc08bd97d902a08c45 32 (hk ys) 6 0 36
def test (i : Nat) := checkD 144 scores 9 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 144 (cutBoard 9 inputs B) (cutCount 9 36) (fun _ => I) (rowOrient 144 rho) scores 10 0 = true := by decide +kernel
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
lemma regionOK : span test 36 0 = true := (@span_join test 18 0 18 (@span_join test 9 0 9 (@span_join test 4 0 5 z0 (@span_join test 2 4 3 z4 z6)) (@span_join test 4 9 5 z9 (@span_join test 2 13 3 z13 z15))) (@span_join test 9 18 9 (@span_join test 4 18 5 z18 (@span_join test 2 22 3 z22 z24)) (@span_join test 4 27 5 z27 (@span_join test 2 31 3 z31 z33))))
theorem finiteCheck : ¬NatRun (mask 144) (goal 144) 10 inputs :=
  symCutRoot (rowOrient_sound rho) roof (fun i hi => checkD_sound (span_ok regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 144 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finiteCheck

end Row13

namespace Row18
def vals : List ℕ := [1, 1, 1, 1, 2, 2, 4, 4, 8, 8, 10, 10, 10, 12, 12, 12, 16, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 36, 36, 36, 36, 48, 48, 48, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 64, 64, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 66, 66, 66, 66, 68, 68, 68, 68, 72, 72, 72, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 3, 5, 9, 17, 3, 6, 5, 6, 9, 40, 11, 14, 42, 13, 14, 44, 17, 80, 19, 22, 82, 21, 22, 84, 25, 56, 88, 3, 5, 6, 9, 17, 27, 30, 40, 58, 80, 90, 96, 3, 5, 6, 9, 17, 29, 30, 40, 60, 80, 92, 96, 40, 96, 3, 5, 6, 9, 17, 35, 37, 40, 41, 49, 80, 96, 97, 35, 38, 42, 98, 37, 38, 44, 100, 49, 56, 112, 3, 5, 6, 9, 17, 40, 51, 54, 58, 80, 96, 114, 3, 5, 6, 9, 17, 40, 53, 54, 60, 80, 96, 116, 80, 96, 3, 5, 6, 9, 17, 40, 67, 69, 73, 80, 81, 96, 97, 67, 70, 82, 98, 69, 70, 84, 100, 73, 88, 104, 3, 5, 6, 9, 17, 40, 75, 78, 80, 90, 96, 106, 3, 5, 6, 9, 17, 40, 77, 78, 80, 92, 96, 108]
def inputs : List ℕ := [0x16c16c88d76c05b05b22337b00ec0ec9292af800000000fff8000000003ffe000000000000f, 0x216b141781140859c505e02501155942e2e588007ff80f0000001ffe03c0000007ff81c1c30, 0x2b182187902189c60861e404615981187474717ff8000f00001ffe0003c00007ff8000e0e0c0, 0x2ba2ba38004a012812848818857a17a3807f827ffffff0000000000000000007ffffff00ff00, 0xc40c41221841bd0bd0e006101dc1dc3ff80040000000000001ffffffc000007ffffffff0000, 0x3083082446082de0de0fffbe0e6026010049000000000000001ffffffffffff8000000000000, 0x3f03f03ffff03e00e00911c00b8038024900007fffffffffffe0000000000000000000000000]
def scores : List ℕ := [0x1fc4d06ca8280bd, 0x134351649c26097, 0x22c671fc9927098, 0x19c590d4bd268a8, 0x22c7f19c9825c9c, 0xd41b134a026899, 0xd41b22ca82609a, 0xd41b1fca82649a, 0xd41b134a025c99, 0x1342719cbd264a0, 0xd4271349c25c98]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def rho (ys : List Nat) : List Nat :=
  match fld 0x18822492803840868420032830708899 2 (bsr 0xf9795bfaf7ca5b71f5bf7ce0f163380ced9c28c1e94ccfbde058865fdaf380a7d840bc00d79982c3ce89ad8ece82c438c6ce523bc0fd0ac4bd0fed01bcfab1a9b69b83adb23ed016b0fb3666b0c1e62daba738b6aaca9698a9ebec5fa9dd629ca52443c2a48ba7fa9fdf667098e2a61e8d02265289ba790489afb26b8568c2c484c9e6908295090c81d5c9697a18dad2737193a4695708f968cc8bed60e0a5a660ab18a1608a3ff95f41c7865eb654ca5a25f2da5910af6d54d59f9047ca584e451e2fcb421dd2bf40e1f9033e3a2c25384bcb65321a3b972dbc0bf7272886371db835851c6fbd121be8f6051aa9a0ae18a9b674148b0d770b63a955055a7878 32 (hk ys) 7 0 64) with
  | 1 => vals.map (fun r => fld 0xef003ec00e3000000121004b401150000000dc00381b0bd0000000bc0032000b10000000ab002ba10a800476387f9422e0c7c004320874829e0ce650000000ba0031800b0003add44d7b165aa4a0000000a300299a8a000369a242691186a33002e16e1b6189d5e18002a9521256055341000289420a520353208002712e044c0180000 9 r)
  | 2 => vals.map (fun r => fld 0x12d0048401150000000fb003bc00e30000000e000371b0bd0000000c6002e800b00000000a60028da8a0003adec5975135aa4a00369a446689086a330000000c8002f000b100476508b8e1fe0c7c0000000ae002ae10a8004320a78821d0ce65002e186275b86d5e1800289480d508293208002a958155484934100027130064b8100000 9 r)
  | 3 => vals.map (fun r => fld 0x121004b401150000000ef003ec00e30000000dc00381b0bd0000000ba0031800b00000000a300299a8a0003add44d7b165aa4a00369a242691186a330000000bc0032000b100476387f9422e0c7c0000000ab002ba10a8004320874829e0ce65002e16e1b6189d5e1800289420a520353208002a95212560553410002712e044c0180000 9 r)
  | _ => []
def B (i : Nat) := mv (mask 151) (fld 0xf10f40106f21506102f50e64404f41e40502f53e65e51401e54500f51100e41e21503103405e50f54e34e10400f34000f65 12 i) inputs
def I (ys : List Nat) := bsr 0xf9795bfaf163380ce94ccfbde058865fd840bc00ce82c438bd0fed01b23ed016b0fb3666b0c1e62daba738b6a9dd629ca48ba7fa9fdf667098e2a61e89ba79048295090c7a18dad2737193a468cc8bed60e0a5a660ab18a1608a3ff95f41c7865a25f2da47ca584e451e2fcb40e1f9033e3a2c252dbc0bf7272886371c6fbd121aa9a0ae 32 (hk ys) 6 0 33
def test (i : Nat) := checkD 151 scores 9 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 151 (cutBoard 9 inputs B) (cutCount 9 33) (fun _ => I) (rowOrient 151 rho) scores 10 0 = true := by decide +kernel
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
lemma regionOK : span test 33 0 = true := (@span_join test 16 0 17 (@span_join test 8 0 8 (@span_join test 4 0 4 z0 z4) (@span_join test 4 8 4 z8 z12)) (@span_join test 8 16 9 (@span_join test 4 16 4 z16 z20) (@span_join test 4 24 5 z24 (@span_join test 2 28 3 z28 z30))))
theorem finiteCheck : ¬NatRun (mask 151) (goal 151) 10 inputs :=
  symCutRoot (rowOrient_sound rho) roof (fun i hi => checkD_sound (span_ok regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 151 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finiteCheck

end Row18

namespace Row19
def vals : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 4, 8, 8, 10, 10, 10, 10, 12, 12, 12, 12, 16, 16, 17, 17, 17, 17, 20, 20, 20, 20, 24, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 33, 33, 33, 34, 34, 34, 40, 40, 40, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 64, 64, 65, 65, 65, 65, 66, 66, 66, 66, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 96, 96, 96, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 3, 5, 9, 3, 6, 18, 5, 6, 36, 9, 72, 11, 14, 26, 74, 13, 14, 44, 76, 18, 80, 19, 21, 25, 81, 21, 22, 52, 84, 25, 26, 88, 3, 5, 6, 9, 18, 29, 30, 36, 60, 72, 80, 92, 36, 35, 37, 41, 35, 38, 50, 41, 44, 104, 3, 5, 6, 9, 18, 36, 43, 46, 58, 72, 80, 106, 50, 52, 112, 3, 5, 6, 9, 18, 36, 51, 53, 57, 72, 80, 113, 3, 5, 6, 9, 18, 36, 57, 58, 60, 72, 80, 120, 72, 80, 67, 69, 73, 81, 67, 70, 74, 82, 3, 5, 6, 9, 18, 36, 69, 70, 72, 76, 80, 84, 100, 100, 104, 112, 3, 5, 6, 9, 18, 36, 72, 80, 99, 101, 105, 113, 3, 5, 6, 9, 18, 36, 72, 80, 99, 102, 106, 114]
def inputs : List ℕ := [0x42fc2c012c7c04b9cb00964f01591f045278007ff8000078001ffe00000e00001e00007, 0x3c544540257c409505533aa3902aa214bc5cfff80000007800000003ffc7000000007838, 0x898898eb98881260a6414c92cf30f23c8e90000000fff800000000000000fff1e0781c0, 0x11211210c2111bc83081791c45b47043ff020000000000001ffe0003fff80fffe007fe00, 0x2242242304222dd0dd0ea20206b87ffc10100000000000001ffffffc00000ffffff80000, 0x3c83c83c080009e09e0f3c1ff8c0040100807ffffff000001ffffffffffff00000000000, 0x3f03f03ff03ffe00e009c0100700488a22007fffffffffffe00000000000000000000000]
def scores : List ℕ := [0x114201449724490, 0x20c451dca323c94, 0x19c51114a324499, 0x1dc6720c9723c90, 0xd8201449725093, 0x1142019c9924091, 0x19c200d899250a3, 0x1142020c9323c90, 0x20c770809124c8f, 0x19c4520c9323c90, 0x20c45144942448f, 0xd8201dc9023c93, 0x1dc5120c9923c91]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)
def rho (ys : List Nat) : List Nat :=
  match fld 0x1858e48be88228500 1 (bsr 0xfdbf7bcafd7239e7f853cf8ff3a47eecf2c4f171edab805febd25c57e58a7b05e35ef914e00aade0ddc13479d7cb6f94d53813b8c9252652c2cc5fa4be370bdcbdb2c8f6b93c43e1b7eabc0db6563989b15059b2a9b60f5da23bcf419ac580ca93dd0d12904f2e208adf4a6384253f6e800f32447d71db547cc8d5d77bf9a0a5773ee0a57043f3476cf6ceca6c82649a6b3bcedc698c41da60635b1960205ccd5950015f589d670856a171b94dee9f4b4ddc56254c70b91b4671850b464185543ff014f93a510d9537f90bb23700a0a2330c54be3019fac72b5f3ac726b4de2c2131f5dd1bec420c174d6aa716b4fe39157bf054115fec560c01d95d0342b8480316ee6001b5a6cf00d1b3c6 32 (hk ys) 7 0 67) with
  | 1 => vals.map (fun r => fld 0xeb00000000000441a0c40000000000037e3ad30043e3702871dd06740000000ba0000000ae0000000a1003c13a990000000ab0029deaa3003bde6677717cc65d0000000b7003719a510000198a065af86c330036c00aa6d1158242002f580975e0b4602c002d16a2000299381d00279360f4d2441609002955219520552813002412606478000600 9 r)
  | _ => []
def B (i : Nat) := mv (mask 143) (fld 0x406f40e30104505106e43e40e60f20506f43e10403101f30f52e65e20e50e32f53e62f62f10502750504102f65f50402400000501f32652405e63f60e53f63105e52 12 i) inputs
def I (ys : List Nat) := bsr 0xfdbf7bcafd7239e7f2c4f171edab805febd25c57e58a7b05e00aade0d53813b8c9252652c2cc5fa4b7eabc0db6563989a9b60f5da23bcf4193dd0d12904f2e208adf4a63800f32446cf6ceca6b3bcedc698c41da60635b195950015f589d670856a171b94dee9f4b4ddc56254671850b464185543ff014f937f90bb2330c54be3019fac72b5f3ac726b4de2c1bec420c16b4fe39157bf054115fec560c01d95d0342b8480316ee6001b5a6cf00d1b3c6 32 (hk ys) 6 0 44
def test (i : Nat) := checkD 143 scores 9 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 143 (cutBoard 9 inputs B) (cutCount 9 44) (fun _ => I) (rowOrient 143 rho) scores 10 0 = true := by decide +kernel
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
lemma regionOK : span test 44 0 = true := (@span_join test 22 0 22 (@span_join test 11 0 11 (@span_join test 5 0 6 (@span_join test 2 0 3 z0 z2) (@span_join test 3 5 3 z5 z8)) (@span_join test 5 11 6 (@span_join test 2 11 3 z11 z13) (@span_join test 3 16 3 z16 z19))) (@span_join test 11 22 11 (@span_join test 5 22 6 (@span_join test 2 22 3 z22 z24) (@span_join test 3 27 3 z27 z30)) (@span_join test 5 33 6 (@span_join test 2 33 3 z33 z35) (@span_join test 3 38 3 z38 z41))))
theorem finiteCheck : ¬NatRun (mask 143) (goal 143) 10 inputs :=
  symCutRoot (rowOrient_sound rho) roof (fun i hi => checkD_sound (span_ok regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 143 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finiteCheck

end Row19

namespace Row20
def vals : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 8, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 16, 16, 17, 17, 17, 17, 20, 20, 20, 24, 24, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 32, 33, 33, 33, 33, 34, 34, 34, 34, 36, 36, 36, 36, 64, 65, 65, 65, 66, 66, 66, 66, 68, 68, 68, 80, 80, 80, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 96, 96, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 3, 5, 9, 3, 6, 18, 5, 6, 9, 40, 72, 3, 5, 6, 9, 11, 14, 18, 26, 40, 42, 48, 72, 74, 13, 14, 44, 76, 18, 48, 19, 21, 25, 49, 21, 22, 52, 25, 26, 56, 88, 3, 5, 6, 9, 18, 29, 30, 40, 48, 60, 72, 92, 40, 48, 35, 37, 41, 49, 35, 38, 42, 50, 37, 38, 44, 52, 72, 67, 69, 73, 67, 70, 74, 82, 69, 70, 76, 82, 88, 112, 3, 5, 6, 9, 18, 40, 48, 72, 83, 85, 89, 113, 3, 5, 6, 9, 18, 40, 48, 72, 85, 86, 92, 116, 104, 112, 3, 5, 6, 9, 18, 40, 48, 72, 99, 101, 105, 113, 3, 5, 6, 9, 18, 40, 48, 72, 99, 102, 106, 114, 3, 5, 6, 9, 18, 40, 48, 72, 101, 102, 108, 116]
def inputs : List ℕ := [0x42c42fc2c10bf0b047847c02b13e0806ca78000007ff8001ffe007007800003c0000007, 0x857c544542151152bc8bc405524294bd45c8007ff800000000007807800000000fff838, 0x3c18818818f062061c93c88a660e478098697ff8000001ffe0003807801ffe1c0f0000c0, 0x12a12a12a14a84a85125111ee8f087eee38200000000000000000000001fffe00fffff00, 0x2142142142f50f50e202222b70fff81300100000000001ffffffc000001ffffff0000000, 0x3d83d83d838608608003fff38049121c01007ffffffffe0000000007ffe0000000000000, 0x3e03e03e03f80f80fffc000c0080046002007ffffffffffffffffff80000000000000000]
def scores : List ℕ := [0x20c771ac9023c93, 0x20c291749929098, 0x1dc5102c98250a4, 0x1ac0b1dc9923c91, 0x1442902c9323c90, 0x1ac2920c9824091, 0x1dc51174942408f, 0x1442902c9124c90, 0xa40b20ca424c94, 0x1440b0a4942448f, 0x1ac0b144a424498, 0x1dc6b20c9924c8f, 0x144291749925091, 0x1440b0a49124c8f, 0x1ac0b1749924091, 0x1dc5d1aca423c94]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)
def rho (ys : List Nat) : List Nat :=
  match fld 0x0 1 (bsr 0xfbbb207cf846ca6cf61c44aef1b63f6af06788f3f031bf29ea55c7ace5f9f36fe3a88167de74b108dd3a27eddaffd105ca576bb2c7982f8ac6d913dec5966451bcfa0acbbab7b327b8baf593b418853ab15943afb131d659afe29894ab31c543a11482539fd1d2c69f49cf7d97512cf58f527ac58e3190de8d86beca8d5482e48ca23b4f8b6d44ce89a6f67187ca36b980bc0f9a78c2eb90788cce96776f78a472a0de69722a42c06ac9398c65216b4b61e17a56612940e660131ae153f09545530585d250c39e5b470a563941568e913dd4164a3b6dbc71359a118e2aff0cd01f724bbd1d0730f518edb4be17f81bf2170a89d51628de5813a908c611d1e6300c8d7ce50bbe84ff033eea7e 32 (hk ys) 7 0 67) with
  | _ => []
def B (i : Nat) := mv (mask 143) (fld 0xf43404f53e21e40102401106e30f50105e31f24402e63406100403101104e62f60e60e61663000505e52500f54503f61f63760e51e24e50e10e41f64103400f51e20405f31f62f52e65f65f20e53e64f41e43765f40f23e23502f10f21f30e54504506501 12 i) inputs
def I (ys : List Nat) := bsr 0xfbbb207cf846ca6cf61c44aef1b63f6af06788f3f031bf29ea55c7ace5f9f36fe3a88167de74b108dd3a27eddaffd105ca576bb2c7982f8ac6d913dec5966451bcfa0acbbab7b327b8baf593b418853ab15943afb131d659afe29894ab31c543a11482539fd1d2c69f49cf7d97512cf58f527ac58e3190de8d86beca8d5482e48ca23b4f8b6d44ce89a6f67187ca36b980bc0f9a78c2eb90788cce96776f78a472a0de69722a42c06ac9398c65216b4b61e17a56612940e660131ae153f09545530585d250c39e5b470a563941568e913dd4164a3b6dbc71359a118e2aff0cd01f724bbd1d0730f518edb4be17f81bf2170a89d51628de5813a908c611d1e6300c8d7ce50bbe84ff033eea7e 32 (hk ys) 7 0 67
def test (i : Nat) := checkD 143 scores 9 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 143 (cutBoard 9 inputs B) (cutCount 9 67) (fun _ => I) (rowOrient 143 rho) scores 10 0 = true := by decide +kernel
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
lemma regionOK : span test 67 0 = true := (@span_join test 33 0 34 (@span_join test 16 0 17 (@span_join test 8 0 8 (@span_join test 4 0 4 z0 z4) (@span_join test 4 8 4 z8 z12)) (@span_join test 8 16 9 (@span_join test 4 16 4 z16 z20) (@span_join test 4 24 5 z24 (@span_join test 2 28 3 z28 z30)))) (@span_join test 17 33 17 (@span_join test 8 33 9 (@span_join test 4 33 4 z33 z37) (@span_join test 4 41 5 z41 (@span_join test 2 45 3 z45 z47))) (@span_join test 8 50 9 (@span_join test 4 50 4 z50 z54) (@span_join test 4 58 5 z58 (@span_join test 2 62 3 z62 z64)))))
theorem finiteCheck : ¬NatRun (mask 143) (goal 143) 10 inputs :=
  symCutRoot (rowOrient_sound rho) roof (fun i hi => checkD_sound (span_ok regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 143 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finiteCheck

end Row20

namespace Row23
def vals : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 8, 8, 10, 10, 10, 10, 12, 12, 12, 16, 16, 17, 17, 17, 17, 20, 20, 20, 24, 24, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 32, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 36, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 64, 64, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 66, 66, 66, 66, 68, 68, 68, 68, 72, 72, 72, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 3, 5, 9, 3, 6, 18, 5, 6, 9, 40, 11, 14, 26, 42, 13, 14, 44, 18, 80, 19, 21, 25, 81, 21, 22, 84, 25, 26, 56, 88, 3, 5, 6, 9, 18, 29, 30, 40, 60, 80, 92, 96, 40, 96, 35, 37, 41, 97, 3, 5, 6, 9, 18, 35, 38, 40, 42, 50, 80, 96, 98, 37, 38, 44, 100, 50, 56, 112, 3, 5, 6, 9, 18, 40, 51, 53, 57, 80, 96, 113, 3, 5, 6, 9, 18, 40, 53, 54, 60, 80, 96, 116, 80, 96, 3, 5, 6, 9, 18, 40, 67, 69, 73, 80, 81, 96, 97, 67, 70, 82, 98, 69, 70, 84, 100, 73, 88, 104, 3, 5, 6, 9, 18, 40, 75, 78, 80, 90, 96, 106, 3, 5, 6, 9, 18, 40, 77, 78, 80, 92, 96, 108]
def inputs : List ℕ := [0x4b04b2235cb012e72c080afc02b13e1153c000000007ffc000fff00000f00000780007, 0x95ad505e055025415494dd44055242af2e4003ffc07800000000001fff000000003c38, 0xac60861e408627182187811885660e47234bffc000780000fff0001e00003ffc381c0c0, 0xae8ae8e0012804a04a12062115e8f087fc13ffffff8000000000000000003fffc01ff00, 0x3103104886106f42f43818400770fff84080000000000000ffffffe000003fffffe0000, 0xc20c20911820b783783fef83f98040048800000000000000ffffffffffffc0000000000, 0xfc0fc0ffffc0f803802470022e0089100003ffffffffffff00000000000000000000000]
def scores : List ℕ := [0x1101e1409723c90, 0x1d81e208a024893, 0x1d844178b724097, 0x140440c0922388f, 0x1d85e2089223c8e, 0x17830078a025cb7, 0x11030078932408e, 0x1d8501788f23892, 0x1d850178a023893]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def rho (ys : List Nat) : List Nat :=
  match fld 0xc07d61251b0941ae 1 (bsr 0xfad57cb8f9047f6df75acffbed7be9d0ebdd4332e951c2f7e84a982be66bcd2cda83b6a2d9681db1d39d99dccd0b5820cd09d6d8ca5d2c92c3b0b69ec223ee35bf567c23bd81d0b9bb13f5dcb6d82285adc7586cada8c338ac8cb5c4ac7e0d38a2be6553a0b125729d83592a98f245569756d55b95268ac49377e3d79164dcb68d3232e286f93574830329a581d920eb7a1f058178c8f10a7482b68d6968e6a668f7a89367b8c7d6675a0ee560fd95995accbdfd5a3906515885c981534d0c244f485e064ebbd8de4ce777da486b43f04010b6873d5df0733d31516f3699612b2f5a17b02cee13cf22802718116347de1041c9290b589ae80b0d049403c2b6a1 32 (hk ys) 7 0 64) with
  | 1 => vals.map (fun r => fld 0x11b000021f030000000e90037400d10000000ce002f594b70000000b40036800aa00000009e002f1369700365ca506c1118e41002ed883d5d0b0602a0000000b6000021aab0045a1682853d0ec730000000a700291f6a0003cdf46f79178d65c002c5641e0028d341a00271320e4c2401408002894c175084d26110023d2406470000600 9 r)
  | _ => []
def B (i : Nat) := mv (mask 142) (fld 0xe64e51e52f34e54e40e20404f65f40f20402503e50e65506f41102f52f53106e34e41f10f32101501103f50405f54f51000e10e24400502 12 i) inputs
def I (ys : List Nat) := bsr 0xf75acffbed7be9d0ebdd4332e951c2f7e84a982be66bcd2cda83b6a2c3b0b69ebf567c23b6d82285adc7586cada8c338ac8cb5c4a2be6553a0b1257298f245569756d55b9377e3d78d3232e286f93574830329a578c8f10a68f7a89367b8c7d6675a0ee560fd95995a3906515885c9814f485e064ce777da486b43f04010b6873d5df0733d31516f2cee13cf116347de03c2b6a1 32 (hk ys) 6 0 37
def test (i : Nat) := checkD 142 scores 9 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 142 (cutBoard 9 inputs B) (cutCount 9 37) (fun _ => I) (rowOrient 142 rho) scores 10 0 = true := by decide +kernel
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
lemma regionOK : span test 37 0 = true := (@span_join test 18 0 19 (@span_join test 9 0 9 (@span_join test 4 0 5 z0 (@span_join test 2 4 3 z4 z6)) (@span_join test 4 9 5 z9 (@span_join test 2 13 3 z13 z15))) (@span_join test 9 18 10 (@span_join test 4 18 5 z18 (@span_join test 2 22 3 z22 z24)) (@span_join test 5 27 5 (@span_join test 2 27 3 z27 z29) (@span_join test 2 32 3 z32 z34))))
theorem finiteCheck : ¬NatRun (mask 142) (goal 142) 10 inputs :=
  symCutRoot (rowOrient_sound rho) roof (fun i hi => checkD_sound (span_ok regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 142 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finiteCheck

end Row23

namespace Row24
def vals : List ℕ := [1, 1, 1, 2, 2, 4, 4, 8, 8, 10, 10, 10, 12, 12, 12, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 36, 36, 36, 36, 40, 40, 40, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 64, 64, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 66, 66, 66, 66, 68, 68, 68, 68, 72, 72, 72, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 3, 5, 9, 3, 6, 5, 6, 9, 24, 11, 14, 26, 13, 14, 28, 24, 48, 80, 3, 5, 6, 9, 19, 21, 24, 25, 48, 49, 80, 81, 96, 3, 5, 6, 9, 19, 22, 24, 26, 48, 50, 80, 82, 96, 3, 5, 6, 9, 21, 22, 24, 28, 48, 52, 80, 84, 96, 48, 96, 3, 5, 6, 9, 24, 35, 37, 41, 48, 49, 80, 96, 97, 35, 38, 50, 98, 37, 38, 52, 100, 41, 56, 104, 3, 5, 6, 9, 24, 43, 46, 48, 58, 80, 96, 106, 3, 5, 6, 9, 24, 45, 46, 48, 60, 80, 96, 108, 80, 96, 3, 5, 6, 9, 24, 48, 67, 69, 73, 80, 81, 96, 97, 67, 70, 82, 98, 69, 70, 84, 100, 73, 88, 104, 3, 5, 6, 9, 24, 48, 75, 78, 80, 90, 96, 106, 3, 5, 6, 9, 24, 48, 77, 78, 80, 92, 96, 108]
def inputs : List ℕ := [0x12c12c88d72c02b02b2232eb003601b55d8255e000000003ffe000000000fff80000007ffc0007, 0x216b1417811404596505e025004aab500a85cb2001ffe03c0000007ff80f0000000fff80000e18, 0x2b182187902189660461e4046156c0260130e8e5ffe0003c00007ff8000f00001fff00000007060, 0x2b62b63800460978978e0009801900c80641ff09ffffffc000007ffffff00000000000000007f80, 0xcc0cc12218c13903904887105fe0ff07f8792000000000000000000000000001ffffffffff8000, 0x3083082446082de0de0fffbe0e601300980200000000000000007fffffffffffe00000000000000, 0x3f03f03ffff03e00e00911c00b801c00e0040001ffffffffffff800000000000000000000000000]
def scores : List ℕ := [0x2141f14cbb2b4ae, 0xb01f0489e274a1, 0x244120b0a52789f, 0x2146d2449f2849d, 0xec121b4bb2b8ad, 0x2143b07cae2b4bb, 0x14c1207ca52749f, 0xb01214c9f2849e]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def rho (ys : List Nat) : List Nat :=
  match fld 0xe465b8084d80806c001965881811001861a653052400291 3 (bsr 0xfd73216afd2ae6a0f4b4ebf0eebc10b5ee8dd76ee615bbb3e2771267dcc8cd84db1f5491d9204e97d82f7fc1d3bc4e42d26d8defcf757ea1c77a1116c3428d89bce7a9e1ba26b6e3b8ed470bb1f21bebb0f1248fa9f68c8ea820a7a09e1133ea9d7fb3f59821dd2d94b96e8c92b118818f112e658a3c63418944838f7e976dac7e6e118f7d3edc677c2f6c1276c035e76b7510e56625fa5465e342a66579cdbd600390ec5b81fc0d5b728fb5522d3c26518f9a784cc737e84a3af73d41b01e383b19fbcd39e2c65133c0b0563136606d2d6bcfc22d5bc1062870c4e623ac96e32281415921d63bcd20a119321663282a1523e67c14e5b5370c33c12b07c33d73 32 (hk ys) 7 0 64) with
  | 1 => vals.map (fun r => fld 0xfb0041c00ef0000000e8003b1c8bb00000012b004dc01200000000c70035174ae004a650859a246248200462207a889f8da6b0000000f80041000ee0000000c50034970ad003d9ea538097dbe5000399ba486f13076390000000a8002ad6ca500305661f5a0b0240f0029d4c09548313e07002853a034f0140000 9 r)
  | 2 => vals.map (fun r => fld 0x129003d800a70000001180039982a1000000128003d400a600000011000375669d003ee56857c14d5009003a18e7a629203e030000001340040400a900000011100379689e0041e6e918217d560c003b1a87e6913058050000001120037d6c9f00391746d5c0ec2400003be4082771414a07002ed5c6b568e41e00 9 r)
  | 3 => vals.map (fun r => fld 0xf6004a400a70000000e60046182a1000000101004d000a90000000de00445689e0041e085f9ba45560c003b1a44c6a1f858050000000f5004a000a60000000dd00441669d003edf05395a155009003a18a48639e83e030000000df004496c9f00391703b5d1b42400003bddc50902094a07002ed5a39571ac1e00 9 r)
  | 4 => vals.map (fun r => fld 0xfb0041c00ef0000000e8003b1c8bb0000000f80041000ee0000000c50034970ad003d9ea538097dbe5000399ba486f130763900000012b004dc01200000000c70035174ae004a650859a246248200462207a889f8da6b0000000a8002ad6ca500305661f5a0b0240f0029d4c09548313e07002853a034f0140000 9 r)
  | _ => []
def B (i : Nat) := mv (mask 157) (fld 0xe40f51000106f30e51400503f31e50e31506f21e21e30403f40504f41104401f10e10103 12 i) inputs
def I (ys : List Nat) := bsr 0xfd73216ad9204e97d3bc4e42c3428d89bce7a9e1b8ed470bb1f21beba820a7a09e1133ea9d7fb3f59821dd2d7e976dac7d3edc6776c035e76b7510e56579cdbd600390ec5b81fc0d522d3c264cc737e82d6bcfc221d63bcd20a119321663282a 32 (hk ys) 5 0 24
def test (i : Nat) := checkD 157 scores 9 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 157 (cutBoard 9 inputs B) (cutCount 9 24) (fun _ => I) (rowOrient 157 rho) scores 10 0 = true := by decide +kernel
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
lemma regionOK : span test 24 0 = true := (@span_join test 12 0 12 (@span_join test 6 0 6 (@span_join test 3 0 3 z0 z3) (@span_join test 3 6 3 z6 z9)) (@span_join test 6 12 6 (@span_join test 3 12 3 z12 z15) (@span_join test 3 18 3 z18 z21)))
theorem finiteCheck : ¬NatRun (mask 157) (goal 157) 10 inputs :=
  symCutRoot (rowOrient_sound rho) roof (fun i hi => checkD_sound (span_ok regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 157 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finiteCheck

end Row24

namespace Row25
def vals : List ℕ := [1, 1, 1, 2, 2, 4, 4, 6, 6, 6, 8, 8, 10, 10, 10, 12, 12, 12, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 20, 20, 20, 20, 24, 24, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 32, 33, 33, 33, 33, 34, 34, 34, 40, 40, 40, 40, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 64, 64, 65, 65, 65, 65, 66, 66, 66, 68, 68, 68, 68, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 96, 96, 96, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 3, 5, 9, 3, 18, 5, 36, 7, 22, 38, 9, 72, 11, 26, 74, 13, 44, 76, 3, 5, 9, 15, 18, 30, 36, 46, 48, 72, 78, 80, 18, 48, 80, 3, 5, 9, 18, 19, 21, 25, 36, 48, 49, 72, 80, 81, 21, 22, 52, 84, 25, 26, 56, 88, 3, 5, 9, 18, 29, 30, 36, 48, 60, 72, 80, 92, 36, 48, 35, 37, 41, 49, 35, 38, 50, 41, 44, 56, 104, 3, 5, 9, 18, 36, 43, 46, 48, 58, 72, 80, 106, 72, 80, 67, 69, 73, 81, 67, 74, 82, 69, 76, 84, 100, 3, 5, 9, 18, 36, 48, 71, 72, 78, 80, 86, 102, 100, 104, 112, 3, 5, 9, 18, 36, 48, 72, 80, 99, 101, 105, 113, 3, 5, 9, 18, 36, 48, 72, 80, 99, 102, 106, 114]
def inputs : List ℕ := [0x41fc1c02389f009c4f802e23277001e4a578007ff800001e00000f000003ffe00000007, 0x3c244246a487125a438805244019297239ccfff8000fff0e07ff8700000000003ffc7398, 0x848848ea978201489132e41e0a209d5c1f10000000ffff000000003ffc3c0003fff83e0, 0x11111110c21246d93c21669e04440d59fe0200000000000007fff803fffc00003ffffc00, 0x22a22a23142489621245b71ffb78f260108800000000000000000003ffffffffc0000000, 0x3cc3cc3c1840027c3ffe38088380438081207ffffff0000007fffffc0000000000000000, 0x3f03f03fe07fff802001c0111c009c0124007ffffffffffff80000000000000000000000]
def scores : List ℕ := [0x13c360489524ca9, 0x1dc4f20c9a23c91, 0x1dc36084a924095, 0x1a0210489a24cac, 0x1a0211dcac23c93, 0x1dc36084ac2449a, 0x841213c9523c90, 0x84120d8932408f, 0x13c211a0ac254a9, 0x84121a09a24091, 0x1a0360489a24cac, 0x1a02120c9524c90, 0x1dc680d8932448f]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)
def rho (ys : List Nat) : List Nat :=
  match fld 0x4ca5c03880c243322ed706239220fea4 2 (bsr 0xffc6f9c4ff41e8e2fbd0a54cf606c261f4a30a53f2969921e92c093ee7041e37e63d7411dd2668d5c6cca5b0c5f20b3dc424d732c0987827bea7d536bb5677f8bada98a2b9008580b21ff34eaa85e630a31945aa9f9ee1e99c41684c9ad428319876483e95deaa86951f47a69483de0593dbbcc29172253d8dac909b8a1809cf89cba2718924bbb385d02f51856e310484ff0c0179f3338c79431fc0766724c1743f5c48724dcc286b654a0c68d3a29c65efabe465ccde23622f2961561473d54fd401c84c7e3d33494994ac4328b7fa424e10483052afba2624c49e25a41b5a1f1ec26f180438f81538f044106645730dc8155e0ba567900812b114000423c2 32 (hk ys) 7 0 64) with
  | 1 => vals.map (fun r => fld 0x291929e000000000002a19a9f002ada0a0530486c0f00000010f0000000d4003f400ed002596a900040800f6002617e95809a180644b81c5c050000001100038c00d50000000ee0026d6c91003a400dd7313d864b00275889a4e030640a0043a22770034d7244003b1785d5a23c42008ea0e0a746c921524279185585b4980c3c00 9 r)
  | 2 => vals.map (fun r => fld 0x291929e000000000002ada0a0002a19a9f530486c0f0000001100000000ee0038c00d50026d6c91003a400dd00275889a7313d864b4e030640a00000010f003f400ed0000000d4002596a900040800f6809a18064002617e954b81c5c050043a2277003b1785d0034d72445a23c42008ea0e0a7479185585b6c92152424980c3c00 9 r)
  | 3 => vals.map (fun r => fld 0x47623050000000000040a1ef6003a620dd8720cee740000000cd0000000bf0039800c30036572a9002a0009f00261a8957193daa4b6992088420000000d00040400c00000000c4003c978ac002ac00a07e9a1da6400275dc9a76184ba5b0029992360025d6a2e002716c325a24c421e520493c0f4b01d20054d831220a4780c0000 9 r)
  | _ => []
def B (i : Nat) := mv (mask 143) (fld 0x504000e40e20e10e52f10f53104f20506400106e32101f32e62f40e43402401f12e12f42f52501 12 i) inputs
def I (ys : List Nat) := bsr 0xff41e8e2f606c261dd2668d5c6cca5b0c5f20b3dc424d732bb5677f8b9008580b21ff34eaa85e6309f9ee1e99c41684c95deaa86951f47a693dbbcc28dac909b89cba271743f5c48724dcc2865efabe4622f2961494994ac424e10482624c49e25a41b5a000423c2 32 (hk ys) 5 0 26
def test (i : Nat) := checkD 143 scores 9 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 143 (cutBoard 9 inputs B) (cutCount 9 26) (fun _ => I) (rowOrient 143 rho) scores 10 0 = true := by decide +kernel
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
lemma regionOK : span test 26 0 = true := (@span_join test 13 0 13 (@span_join test 6 0 7 (@span_join test 3 0 3 z0 z3) (@span_join test 3 6 4 z6 z9)) (@span_join test 6 13 7 (@span_join test 3 13 3 z13 z16) (@span_join test 3 19 4 z19 z22)))
theorem finiteCheck : ¬NatRun (mask 143) (goal 143) 10 inputs :=
  symCutRoot (rowOrient_sound rho) roof (fun i hi => checkD_sound (span_ok regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 143 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finiteCheck

end Row25

namespace Row26
def vals : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 8, 8, 10, 10, 10, 12, 12, 12, 16, 16, 18, 18, 18, 20, 20, 20, 32, 32, 34, 34, 34, 36, 36, 36, 40, 40, 40, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 48, 48, 48, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 64, 64, 66, 66, 66, 68, 68, 68, 72, 72, 72, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 80, 80, 80, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 3, 5, 6, 9, 17, 24, 33, 65, 96, 3, 6, 5, 6, 9, 24, 11, 14, 26, 13, 14, 28, 17, 24, 19, 22, 26, 21, 22, 28, 33, 96, 35, 38, 98, 37, 38, 100, 41, 56, 104, 3, 5, 6, 9, 17, 24, 33, 43, 46, 58, 65, 96, 106, 3, 5, 6, 9, 17, 24, 33, 45, 46, 60, 65, 96, 108, 49, 56, 112, 3, 5, 6, 9, 17, 24, 33, 51, 54, 58, 65, 96, 114, 3, 5, 6, 9, 17, 24, 33, 53, 54, 60, 65, 96, 116, 65, 96, 67, 70, 98, 69, 70, 100, 73, 88, 104, 3, 5, 6, 9, 17, 24, 33, 65, 75, 78, 90, 96, 106, 3, 5, 6, 9, 17, 24, 33, 65, 77, 78, 92, 96, 108, 81, 88, 112, 3, 5, 6, 9, 17, 24, 33, 65, 83, 86, 90, 96, 114, 3, 5, 6, 9, 17, 24, 33, 65, 85, 86, 92, 96, 116]
def inputs : List ℕ := [0x3b61db21db0ed92526d936c936c9b649494955b600000000000000000000000000000000000001ff, 0x40b7050205b8285c082ce14041670a1717172c0a000fff80007ffc0e0003ffe0001fff0383838600, 0x2e0c20617061030e89c304184e1820c3a3a3a380dfff0000fff8000707ffc0003ffe0001c1c1c1800, 0x8504285728b9470011408a14ea2751c024bfc0500000000fffffff8000000003ffffffe0001fe000, 0x2e61730e4302182009d84ec388c0460803fe48061fffffff0000000007ffffffc000000001fe00000, 0x30818409840c20492de06f03ef03781ffc000028000000000000000007fffffffffffffffe0000000, 0x3f01f80ff80fc07ffe00700270038012480000301ffffffffffffffff800000000000000000000000]
def scores : List ℕ := [0x1a8000a0a929ca8, 0x1dc00250a6294a4, 0xd428000a2284a3, 0x114000a0a6290a5, 0x11400250a9288a7, 0x1a828000a829ca9, 0x21c6a000a5290a6, 0x1dc00148a6288a4, 0x1a8001dca828ca1, 0xd40021ca528ca2, 0x25000148a9294a8, 0xa00021ca9284a7, 0xd4000a0a728ca2, 0x250000a0a9298a5, 0x1dc0021ca8298a4, 0xa000250a728ca1]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
def recipe7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xe60b30a52353102102103104000e50330101000e40351105000e10a70330000f30251106000e50720361000e42b73364000100102106000100e20331101e42353106000e31351732000f10b51241100e31101331f50f32a52354500a20a30370e20331e61372000e60676361e21a50340741000100e40351000e41352103000e31310732000e42362b62000f60275105100e20331b52f40742252b64000000e60330000e20740360e31342e65376e10340310400000e21a40350000e41352106000f30b65271000e60371104000106e60371000e20331642000e65350364000000e10370e20b50320105000e30a50320000e30341105000e50370102000f51753253000e52363104000e30320330100e64375106000f60764260000e10a30370000e40360103f50b75a75107500a40310106000101e65376000e21a40310000e20350720e30b50f60365000e42353640000e10340a31000e40a60370000e20100275000000e65351000e32343105000e62373106000e42321105000e31a51310e30341e51362100102103106000e31731371000e60350105000100e64343000f51660330000e30a60330000f50b70265000e50320a65000505731243000e40100276e61372e52363000000e50350000e10a60370000f60762260000e20360a42e60371e54365000000e60360000000000103000e30a60370000e50370106000e31310b60e52363e64375000e65b54375000e42372103000f52a75354000e20331105000e65b53375e30350102104000000000106000e31310b50000e31371106000105e31371000000e65352000f42650360000502a42332f52a75b52376000101e51362000e42a72362000f20b72270000e31b52343000000101101000e10340310500a40320106e10e51331351e20331e31342000e54103365000104e65351000e30350101102f42a74376000e42320341000000e21332000e52100352000e41710351f21a52353b64000e20350105000000e50330e31771342b43000f50753275100f42b72273000000e40320000e50100350e20a40a70350000101102104
    | 1 => 0xe30a70350000101e41352000f20b63264000e20b50320000e21a50340000e21a50370000f60761260e10350101104000e40360105e31342b43b64000000e30341000e50103360000e51a70310000e10360101102102e63374000f53a75351000e20340720000000100103000e50340750e20340e64375000e30100262e30a50a70360000e50340106000103e65350000f40743253000000e32343000f21b42241000e42320741000f60763260000e20370106100101e63374000e40720370000000e60350000000e50361e42353b54b65e10b40a73374000104e65376000e40320642000e65b50341000e31342b53000e50370750000e60330101000f40b75275000e30320b30000e50730340000f10b31241000e42353104000e40a70320e42353103b54000100e60371000f10b72275000000e63374100e42353103000500a30310000502761263000e60320104e31310330402000f32640370f10b31b51251e42353b54106000000e20331000f42650340000e30341103000500b20242000100e43354000e60320760000e42a72321000f20b43254000e30330103000506b30253000f10242762000f10b41231000105e30341000e42320b61000f20b73275000e60103360000e10a30340000102102104f30b65776271000e30330106000e42106342000e40a70330000e32343104100e31351103000e42321104000e50361104000e31351103e51a70762372000102104106000000e20350e20331e53364000e20a60370000e10750321000e40730370000e60771276000e30320101000e60360101000000101102000e30720341000e60350760f10101b21232000e30a70330000e31351106000e63374104100e42a72320000f10b72273000e31761342000101e64341000000101106000000e60371000e10105340000f10a42372000e20331104000f52b72274000000e52363000f30754252f20721230105000105e32372000e30370102f20b50341641100e42a72321e20b31a52362000e31310330000000100104500a70350102000e40370102000000e10360000f60275b54
    | 2 => 0x500b30240000e60340104000e31a51361000e60100264000e64375105100e31342104f20b50341106000f50b70364e41352f32241000102e52363000f61763271000f30251b43000e30360101000f20b50242100e20370104e31310b40b64000501765276e10721242106000e42320b54000f54a75350000e30341101000e40330106000f30251761000e20a60340000502b76275e30b50a74375100e31331103e31b62353103e51362e64375000101e54365000f10b62276000100e30341000f53b73274000500a70330000e10321105000e42372b54000e42321743000f53b73265000e40b30350000100e52363000101e21332000e60360102000000102102000104f43271f21b73665350000e30341a41f21a41761343000e60350101000e50361101000e40360740e41352e65376000f20253763000000e20340000000102106000500a40350000f30b43253f10e50350242000e50330102000e54a73331000e60b60370e42353b54a64000101e62373000000e31361000e40a70360f50b70103364000e30350106000e60720340f50e70330276000e42104342000e20360720000e20331101f54a75b51376100e30100330e20350f20253000e61372106000e65376506000100e54365100f10a30332100e31b52343000f10b40250000103105106000e31342105f32a52103354000e62373103000e40320102f10e70320242000f40652372000505632372000000000100000f10102363000000e10350f20b50710342000e42353103f32a52354106000f40741240f51a75350365000000e40351000e53a73330000501664343000102102103000f21a41310000e31371103f30e42353b73000e42353106000e20340104000103e31342e10370101750e42b63a75376f50e42353753000f60675351000e53a73353000106e10321000000e65376000f40b74264000e60360b60000f21630370000f60275106000f40742240000f20721221000e60371101e43b63a75376000e32720342000f50276b65000100e42353000f20a53363000000e30360000000e60320000e32a52321
    | 3 => 0xf41642320000500b50275000e42320b64000e40770351000000e10321000e54730365000e50b70350000e31105341000e64730374000f40252762000100e20320000102e62373f21a41310b62f50754a75376000102f51262000e61372104000500b40241000500a50330000e53a73331000e40351a42100101e62373000e31331b43000e65351106000500a20370000f10b71261000e30760370000f20b62252000f61665353000e31342103000e53a73332f10e40380340100e64343106000000000105000e50350103000e20370a42000f40105332000e21a40370500e30330330000e30770341f50e70320276000e50350750e21a50732352000e42b21352000f51a75376000e20731253000000103106e20340e43354000f30b75275000105f43261000e40653331000e20320103000000e31342000e20a40370000e65b50375000e10a70340000e42102342000e10321104000101101101e20331105106000e31361105000f52a75350000000e51362000e20340101000e60104340000e40a70340100e20331b32000e50730350000e21332103000101101106000e60371102e10b40310101100f21a41342000e50330103000f50276b61000f51b71274500a20370103000e40320103000e31a51331000e21332106000e50330750e10360a31106f10101660242000e65376106000100101103e20360720101000e50740361000f32b53252000e40320106000103f32254000000104105000f41650340000f51a75353e20350320404f20e41361b72e40b30a72373000e52a70310100101101106000100e20340101e61372102e10321e64375000f20721252f40741b64b76000103104106000000100100f20b52242105000000e20360000e10321101000e10340106000f30731230101101101102000f52b72264000e40351101000e50770361000e51362104000000e65353500e20380320f10f70b31373f52a75b53375000100e32343000e30730341000f62665354000e61372105000101e64375000e10106340100e61372104000e10370102f10b71231105000e60371a65
    | 4 => 0xf64670340000101e50361000000000000000000e42372000f30251101000f52a75376000f21a52342e31342b53106000e10370710000e20a70360000103e53331000e40330740000e20331103000f10242104e30b30a62363f32a52353105000500a40320e30360104106000e31342630e50370b50b64000f41743251000e31310b53000e31361102000e20331106000e40730351000f41642342500b40100230000f20a53331000e20720331000e30100265000102e54343000e10a50360000000e53364000f10b52253000e31101265f10b52b65273e50330e63374500a10320103000e52b10363000e20350320000f54a75352000f21b51251e50361103104000e30a50370e10a30340106000e65750375000e31310105000000101104e20350320f42000f10242b21000e10350102f50f32b54365000e20350106000000100101000000000104000e31751342000e40351102000e31361b63000e10340b10000f20b42240000e60760371000e60371103000e43354105000000e42362000e30360631000e31b10341000e52363103000f52754262000e42a72342000f20b52242e30370102102000f60105273000102e64375000e65105232f40f31262354000100102104000e42353b64f30f62b82275f20721a41343000e50370b50000e31a61350e20b20b51242000e52363106000e10360103000e50330a65000f20b73274000000e61372e42b73103364000e41352104000100e61372000000e30320000e10321631000e30341104000e10a50330000e10360106100e31371b41000f20b72262000e30750360000100e31342000e62102372000e60340105000000e54365000000e64375000000e50320000101103104000000f20253000e60330103000100e20370100e10321104000f21a52320000e20740370000500b70274000e31342b63e60371103104100501a31341000e10340710000500a30370000f40b75272000e40370740000f10242105000e21a50360000e50361102000e60330106000f32a52321000101e64342101f41b71263000e50105340e31342102b42
    | 5 => 0xf52754254000101e31310000e60100262000e40a60340000e30350105000e50370104000000e31351e10b40a53354f60f21a41373e40503253331000102102106000000e42342000000000101000f10a42352000e31361103000e20340106000000e31310000100e64340000101e31371000e20750331000105e32343000e51362102e31310330400f50e70360370000e20370720000f53a75376000e31371b53000e60720330500a30a50320000e40a60320102e54104365000e50370350000000e43354000e62373105000e65376660e52363e63374000e65b51375f32a52354105f30e42353b74000e40a60330000e30330104f10b40330103000000f30251000e42102261000500a70350000000100102000501662342000101e42353e20a40a60320000f50754254000e31a61330000e31371105000f50276b64000e40351103000e61101371000100e64341000000100106100e20340101000f30732230000e63730373000e30370105000e31a61370100e20b41332000f10b61251000e40351106000e31771342000e30642321000e20320a42000000e41352000000101103000000e60340000e50761276000e40370105000100e10321000e31310730000f61763263000e30720330000e40320740000f63665351f30251732b63500a10350a20000e42372106000e31331105000e42320b41000e31a51371000106f40262101e31342b63000500a40330000f10b62263000000f10242000e40720351000000e40360000e30741252e60371e52363000f30251104000e20370105000e31731342000100102103f20f40342b73000f30b63254000e42a62310000e30341106000e20a40350000f62670350000e50a76361e10360e60371000e51b10362000f10b52252000100103106000e41101341000e31a71331000e40751253000101e63374000e50361103000000e42320000f20101242000101e43354000e10a30350e30341e21332000f21a41343000e42b63354000e32343106000e60340103000f53b73264000e50361106100f43b73273000e30a70360f10b32b63276
    | 6 => 0x105106000e40340103000f32a52354000000e62373000e42372b52000e52a70320e31b52343105000e10b40231000e10330a31000100e62373f51a75b52375000e65350b64000000e42353000e51362103000f54a75376101f41743243f51e42320341000f60f21373000e10740321000000102103000000f60275000000e31371000e50330105000e10100275000e51362106000f30b73264000e40320105000e65352105000502a42352000e30b20241000000e30370000e40340105000e52a70340e62373e53364000e31b72363000f60762275000f43650330000000e40370000000f50276500a10a20330000f20b62260000103104105000101e32343000f10b71270000e42a62320000e31a71351000e61372102000000e31331000f51a75350000e65353105000e30320102000e10340105000104105106000000f40252000000e50340000e62373104000f30251b10000103e65354000e20b50242e10340710231000000e20370000102e43354000102e63374e40351101102101101102103000e51a70350000e10350710f40f73b64275000e61710371000f53660370f10e41253363000000e65350000e65b52343000e42762353000e60350665000e20350b20000e65b52342000100e41352000e31331b41000e30330730e42b20352b54000000e50370000e30370104e31b51a74375000e65351105000e60340101000f62665350000e31a71310000e40330105000500a10350000e30a60350000e42353b54000e10321102000104e43354000e40330b40000f60762272000f50753253000e42a72320f40743b74665000f43650360000f10242742000f20b62242e62373e54365000f10242b20000e31331104000e60720371000e40360101000e31342b43000f32a52353f20f70721373e21a40b32342000e50340103000f10b40330f61e53283364000e10a70350f10b62103276000000e30330000e20370104000e30720370000e21a40360000f30b43240000e30a50330100e30341106000e42320743500a70330106000000102104000f41650360000e65105231
    | 7 => 0xe53364106000e54a73332000f30251102000503732253101e51362105000100101101000e53730364101101e31342000f65670320000e10370106000101104106000000103104f20e52264354000101e61372000f63670320e30760341101000000e10340000502661351f42b65a75376000e40730360000e60360760000e42742353000000104106000f50f43365000e62720372000e31751371f21a41710b73000f53a75350000e41352102000101101102000f10b71231000e42362106000e50320101000f60765275000f20b63276000e20760331e50370b50102000f30251b63000f20b50341000e21332104000e30370101101e51101361000e30320103000e61372103000e54a73343000e20102360100e61372102f60f21b53375000e40320104000e10721242f21a41343b53000e40360102000e40370101000000e40330000103e64375100e31342102000e31731351000e20320720000103e54365000e30100276000e50320103000e60330105000501a31321000f40101241000e20750360000e30350730000f60761275000e50320750000e20a40320000e54365106000100e64375000f40741251000f10b32253000e10340104000e10330104000e20370101000e32a52372000f30651351e40351e65376f21a41102332000f50751251500b20710210000f32a52320000e30103360000e10321103000106e50361000101e64340e10a42b20331000500a30350000f20b43251000000000102000e50370101000f54b74265000e42a62370f10b51b75665000e10321106000502a42372f10f70371231000104e63374f50f32a52365f51a75b51376000e51a70330000000e30350000e30107310000104e53364e42742353b54000f50b75265000105e53364000105f31254000f60675354000e20740331000e50350105e10a60370105e30a60370105f32a52b20354000e42320b51000100e21332000000103105000100e31310e10a50360102000102e42353000e30370730f20b50341b53000f50b75270000e42b20352000e60360105000e30330101000505a76362
    | _ => 0
  fld packed 48 (i % 128)
def finger7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xe1674e2c7fbb1d738980af0d464d0db422f8c6072aea3f6f62638ca32ca7d80e1dc2f08b3baf2e075799204ab86ce27978afda9f45f5ab0e31d665bfa9f62f66a3f4974c3028ccb80c173a7ef2480c717f175a8db64223da7bb5604a803e315b803f2bdfe238c9433e1e92af6629d12abf7fd29e0b8d6b896dadb5d6ab332a1a
    | 1 => 0xa6c0d54f2bee3d5f0d247af9d1f2636a1f473c181c2cfea710ca52665f9bb2066dba8361f16e8cbfd86fa8c32d6851af507b9919d74cec20a71cef348367e3e204c5d64b81a7158a1adae9911bfcb565942e3734bb25251de0ac13a627dbf97ff83de87f12bb0b82d8da0e2021593efeec42dd461e47a5afbd6e12b962941128
    | 2 => 0x591d80e0964efc077e294f045d8a0adff265ba145b4ac9a9f220eb41e22718ac6f88d853737c272cadda1fbc38f594509d465866d403f89170d361f09df86a8f72a65f24358d64774351c0207f08b36801f682d870c8706ada209f96ed66946b4df6328afba996d13ff81a47236cafc38843c3af8eecd53a5b08ad6cdd7ab331
    | 3 => 0x987299a6fbd274bec0f1aedc3763b17f5f9c73cee35987860de483b59b56c7f652d84c9f3375e44bf846e5b84f2285ade1c80e1b4dd5e6e666022a57b2a0b5de14c4e982e41e64f451818bef8f716671f3c8057e707a1673ccbdda77bef8e0c84ea7bb3f5e658dbd2c44f27adc6ba0301a0b39cfb4dcca9ffaf16978397477a7
    | 4 => 0x1e147594621afa892e58dd3467f3976ce6ad1a53a0262f4b59b640f63723d00405ad73de0e4457558cb10b23e3d8fa3569f8642074a1dee412762906f83d426020c3c177694d89344dcfd69d0e21e8a125efa7f59e9614578e5ae3123501d9c104e26ff7fc9bb9d6a07d702be1dc7e2c0ba68c31461f81674a7f56951a831584
    | 5 => 0xc6de1b38ba3e401e528de71b56c54e9c1f2577b9d0655bf668b9cbcb32c2c03a65d0ad80cf7c8b8f07c7f2067dc06be68ef91aa10d33a5a3a46c2fa4bc69a23d1768425445c12182ad04a7260c5d9c93930e26cd4f08edc9f88a829117c05dfceb2bde882a4205dd3bf225150fdafbc19a9efb5e7ea3a0a14e948a8d82fcc844
    | 6 => 0x1ccc9df35ab91acd8c7d81740a842da97a3639a5c3c449c4689387012789df413c831df6a2ce0b814ea146aad9e3d7470286a89085f6355e9cabd6411f607e1465b220ef1937e8c290f3cde5fe454810f1d34a694004f57e5e773a69c0178edd62949814da411b34b296745f8d7f0da05c683cfc9c8a4fef638d74205019b296
    | 7 => 0xcd4bb7e5b485c6ab82a7fbc42bd4305fb1d6499d28aea87fee8fd66d0a86ac2ad7a2195187fe3308c0afc7f806ed4049159a6056b17f9d55147081ddbc6a2ad77a5143dc4365ec5be21edb0274d45f66b83d426ddf39a5c4e0ad3ab4251cacc35bbe4e3c0344dd5cc511bbbbf3d7e1d0266925c13238b6c7c853941c90957d1b
    | _ => 0
  fld packed 8 (i % 128)
def recipe8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xe40b40000e43a63000502b62000f54663000f65674000f10104000000f32000501a71000e60104500b10b51000503105000000400e50103a75000100404000504732100f20b53000f10107000503730e21332f20000e30107000e10b40000e63b53000f41650f40f61b81000000e40e10321504000e60330000f31107f10b72102000e32720000f54b76000e61b41000e65776000102506000101e64000e21107000e43b73000f41104000e61772000000f52e30341105000e64732000f61763000e21b10500b20b52000f42650000e21a70000f50b70000e42753000f60764000e30b60000f30105000e54731000504106000f43105000502104000f40743000f30102000505731000502764e60104105000000e32000e21a40000f32105e31742b74000f61665000104f32000502660000000e31000e65754000e20103e60105107500a10a50100e42105000103e54100501a71000f32a74000e51100400f54b76000e10b21000106e60000e62105000000103000100f61000101e50f31102b73000e50b61000e65b76000e31b31000f40652000e54107000503b64000500660000000106000102402500b40102000f52104000e65352000f20b42000e31b52100e20b71f20b62b72000f53107e30a50107000106e20000e31a61000101e52e51a70107f21b53b75100e20b51e31743b74f30f62b87000401106100e41752000504631000e21332000503106400f54b86000e32105000102e62000f31b54f60e21380000f10b71000e30642000f51a75000000e61000000f54f30b63b76
    | 1 => 0xe21a40a60100102402e30341e53000f20502e10a50102000506770000402107e42a72b73100400107000f10b31000e30341000e21b50000105406000101501000104505100500101000e63731000100103e40a70105000504731000e41752000101f21502a32a72000000504000f40653000e32343000400102000f62105000e50b30f42b65b76000e20b60100e21a41000e60350000e50361100100e62000f10b41000106400100e30a70000f43650000e40102000e63732000f42105000500664000100e42000e42b65000f61672500b10105f20f71774f40b64a75000f30103f50f42365000e63374400f43b85100f43a74000101f41000f21b53100e10a50f20b73103000e10b30e50e65376000e20331000e50720000e20104f21b43b64000f41b65000500107000e64775500b20b42f20b73106000f20a53000e54765000104f31000105f43000e20107100101502000104403000101e21000e31751000f30754000f60105000e60730000100f64000000401000501a31400e70350502b32b43000000503500e21332000106f10000e20350e41352e62e20a40104f32b54b65000f20107000e40b30000502b42500a20a50000403107100100f60503a54a74e65376f65f10f30331000501a61000f53a75000f53661f10b32b53e40b51642000503a54000000f41000e60371000000f64000503a74500b40b54000505730000e52363f50b76106e42372f64e40351f61000100f40000f54662000105403f41104b65000e10a50000e52104000f51a76000500761000000502000e10a70
    | 2 => 0xf20b43104000100e41500e32343000e62b62000f40103000f30a75000000e41000f21a52e20a70107000e30b41000f65672100e31a71f32a52b74400f43b75000e31b72000f10501000500b10100f40b75000e31b62000500a30f20b53b75000502a32000100f20000501760101103504000505b76000e54b65000e52763000e42b75000e32b43000100e10000104e53000e41b52000e10a42000104406100504752100401105000505b43e10a60105f31b74665e20400342f21b73106000e42106e31b42b64000000f60000506b30100e62104000e41101100501b71000f62104000e63774000e52a70000502a62000102106e31742b54e31a61b62f40b65105f10b51b75000f61105000e32721000f65671f10e40351000f51105f21b51652000f60762e31a61103000e61b72000e60b30000e31b74000e20750000e40653f20721b42000506b50000503a53100f40742000f42651000f53662000e64b75e31e53364000e32b62000f63675000e60750000503732000000e50000503731000000505000102f43000f42103000000100000f20b72000e10350e51362f50000000501000e60676000000404000502a76000e40351000100f42000f42107f50752f43e10321f43000f60104000e61710000503630000101e65000f50107000506b40000102e64f20101107000e51b62f20f60b42000f64672000e21a50100100e20e20731a41100f10a30f60762104000f41743000e31731000e51103000103e32f21a41b54000503743000402104000f54661000101f63000f41652100402105
    | 3 => 0x500b60000100401000f21b63e21a70104000e10321f60f42375000f50106000101f61e10321f53e30360f50000e20a60e20350f40000000e42000e32104000f51106f30731b63000501a41f30731f72000e40720500102102100102406f10b40100000503a63000000f61100e40105000e31104000f40b65e10b70661f52b72104000e32107100e21a51000100506000000f51000f10b32000e50770102103402000e31107100500b20000101f50f40741b74100f61102000f53105000000e10f51a75376000503643000103106000f10b62000104f65000105e53100f31b54000f52506000e31342000f31b64000100e54f10b31b73000000405e10321104000f60765f52e75387000f60101e42b53b65000000e64000f32a54500b20b72000e42105000100405000e32743e21a40743000f41102e50361402000102f63e50f74276e41401363000e31743100f60101e42a62b65000e40a60000e61104000103f54000e20a53000f60f21000f20b63e10a50103f31b54107000f51104000e53b64000e62b52e10a70103000e61107000f54107000f60761000102405000100402000500b20000502b32000e64730000e20b31500a20a30000e50102000e10105000101504000100e50000504a63000000f43000400103000000406101e63105000104405000505b53000101403000e53106000e51104000502a72000100e32000e10a60000e65107000e42b62000e40103000504a75f42e62373e10321f65000e32b52000104e63e10a30a70000e43b54000000f62f40e60350000e51107
    | 4 => 0x501a31a41f32b54b75000000000000e42372000f60102000101f64101e43a72000e30a50000f52a75000500105000500b40000000f53000e20106000506a20e43a63a73100500b50000e51a70000e40b70000f50a76000f30a65100e21a71000e42742000503b63e52363f50000f21a41000f31a64000e54730000101e31f50f41365e10321e43f30103754f10e60320000e53364500e51362000401104e10b21b31000403106000f20106000f20b50e30341e51000e20b70e53364f53000501b51000f63665100f20a62000401107f60f21b43000101104f10101b21000503107000e31b42000504a65000501102000100101000000104000102e65000e50b70000e43106e10721a41e20331f63e10a30104000e63106000e21732000f53104000f43b65000101404000e30b50000103f64000e32a52f40b64b74500b30100000f42b75e21a50103000e52106000e41a71100100405000101e63000e62b42000f64106e10a70104000000e53e50106107e10f40252000502103e40370f60000e20760000e31a71000f30f72000f40742f51105b76000e30320000e30106f21e61372000e21a60000f31106000f54a75000400104000f32107e54403376f20502b42f10b61a75000e54365000e64375000f43b75000e42b53000500b50e50f70286000400107000e30a60000f20b53000e32102000102503000503b53000e31a51000100e51000e62107f43104b65f50754b76e42b63b76000e54a73000101406000f51664100e32743000000f65000e42b20e32a52105000f50752f20502b62
    | 5 => 0xe31761000000403000000f20000e65b53100500a40000104e30000e20a40f10f50b75000106f30000101e43000500661000e42342000000101000e42b63e52a70107000102404000f50663f62104106000502661000e43a73f60f41375000f30104e42402364100f60664000f50b76000103e43f10b31b53000000e43000f20a43000e64b43000f43a65000000e63000e43354000000f21000e20105000e50104000e53764000e31b54000000e52100e61104000106f50000505732000f30251000e42a62000501103000e50b50000103404000e50761000e42a72000f50105000500a60000000e60100101401000000f10000f51b76500b30b72000000e30e40a70107000403105000000f31000501107500b20b31000404107000102f32000f21b51100f42107e20e72383000000e21000e41352000101103000102406e43a73105000505763000402106000e20731e21a50107f50104b76e32a52754100f20b43000f40b64000502765e30a50a60100101e61000100e60000f10b51000502b72500a30631000506a50100e20104000100f43000f21105000e43732000100f62000102e53000e41103000101e42500b10b31100102103f10b72105100e40751e42a62105e30341106000f30b63000103504000501662000f20653000e62b73000f43a75000e60105500b30662000f52754f51104b76e10f20380000e30105000504107000f50f43000f51753000e43731000e60771e10a50a60000f60674000f52b72000000e54100502a53000e21105000f20721e62373f62000f30106
    | 6 => 0x105106f10b32107f32a52354000e30a70000f32b64000e10107000f53b73000000f42000f53660000102f51e31f41361f50104b75000e42353000103e64000000f50000e42b42000f52b76000f20101000405107000102103000f60275000f52664f40741b64000500662000e64107500a20103000f31640000e61106f20b43103101e32a72000e30370000e43754f20e54365000f54105000e54b73000503632e32a52b43000f40b75000000402f20b43107000100400000101e62000500760f61104106000100502500b20103e31a71103000e31331000501b21f32b54104e21a50a70000f20103000e50a76000101e41000505a76000503b54000e10740e50761102000105e30000f42104000e20370000e65105000103406000e51b40e20b31107f30f61365000f40741000e32a62000f10b72f20102b42000f50664000e30102000f21a73000000506000501b31000f21a63f50f43b65000f62103000f10a52102e43a72500a10a40000f41b75000f40106000102f64e20731102000105e43000f42b65000501665000f30b65000100501000500665f20721b43100e32a52000f10a42000504753000402105500b10103000000f30000f31504100100f32000f20b73000f51b71000000500000f32b53000f52661500a70107000100f53000e42721000f32a52501a41102000000e20000f61102000f62671000e31101f31b64b76000100e61000f42a75000f20a73f21a41b43000e60740000f51102100e10107000e65b54000e64731e32a62105000f31b74000f40105f30e63374
    | 7 => 0x502663000000f63000101f52000f10b61e42753b65000f10b42500a70760000500b70000e51762100e41a70e10a30106000e60103100f61103000e10721101f21b53000f41106000504653000101f31e30a70102000000e65e10102107f31b64a75000104106000500663000f31102e32a52104000e63b74000e21103000e30750000f50101f30f40b84000000e51000503a64000502105000f62665f20b72b52000f30b75e41a71107000e10760000e52b63000e20770000f32106501a71105000e53107000f61675000e20a70000400106f40101b74000100504000e61105e21a60104000f20503000000f40000101401f30754b65000504b65000e41b61000e32a72000f10a72000e40106e30a60104f20b53103f30102b52e10321e32000103f43000e40b51f43b75106f41104106000f60763000501660100e10a40e30a60107f20b53107000e31b64000f52105000103f65000104e65000e10770000f21b73f20b63b76f51b71a75e61401383000f50b75000101506000e60b71f54b74a75000f65106f21b63103000e51105f51b71675000000102000104e32000e42104f30104b75f50f21363e30a50103000e32106e54365f53f30101b54000102f42000f32a64e20a60107000e30350000e31106000f40104e31b74665f40103b65000f30101f50e42764000100503e31a61b64000f32641000f51103000f62674000f61106000501763f20e40330000500101f10b32104000f50751000e20102503b64105000505663000f51107000e60b50000f32b54500b10b30000f21b43
    | _ => 0
  fld packed 36 (i % 128)
def finger8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x70361dc5216f4d0fcb64d0154e45e41953ca116ebf6981ed3a628cd352ce38d6ef3ff31d9a77aacc57130d3e12d9ae919b1fe3b0cfb7163845ba22b83692f6b8a1904f3027c19f1a40ab2c7f3fae1d9136be5a4b2cc025c2da89126eee3e486f393f9628b03a52a44459efbd389fc8a2e8d6459e4427fd0c51dfad4c502e2e36
    | 1 => 0x7eb24ca81620d0bf3c687a158eae281aed476ccbdb309edafacaf6c1fd52ad2d6dba9f8a42a88f1df720c3cef172cee814d93f19c1c6af3af15a057d83b8be52e144b3ad3e7797363ea2084575f24ca0fdf50d0ac13267a4dfac237e1c19149d044b2e53a1b1cfbb26e50c340c590d2bd946dd842e07831c9a4e35684739cbde
    | 2 => 0x46e8d22608c14015df8555494e0f4b03f129380e73577176096d0671d0d7b9ba3f391c9b4d5f445de7eb11ccc15118d5124f2437b303f36a514e0eb2308ff9c3f61e50203512fdbcd38c2ec2d4f3baacd1dc8e55f7bbf1bcda2f9f49ec476f674deea0ed182e31357babc8d5fa09057b607cb36b612ff9bb80143cec52ee68c6
    | 3 => 0xbc6e2194fbebf6c50fe79d5a3476102421eb6f27fa4da82f3b0d7465875c61de1e64b30aef54598131661db8d222fbf9c09f081bb0e6a4de66a083a46557b3da9de25ec2cf4cd06610f15bf7e812120636a9f819876e84a3f4f44192e7b7125e15fe38889e7b4f92daaf1749b05244da18b4d9dac901c24116adb5135fe4a0c0
    | 4 => 0xa584759486717fd9015a8889b67bd49ff40c47ea3fd85d3504d97e17e7d530ed05a6ef6e5f2f5dfa5b19fdefc8d3de35472f26b2b1a1de2c0f2c2d9c442333f27bbfd7f1c42a3edb256041c33a38d5c267fa9ab11ea84f638a9fe384138ae761f9156fedcf9bb985044ba5dd5648539facc2061be43c4f9c9280d790ba31d06c
    | 5 => 0x1b8050d33f8e97f5192a141b56f8fda3c419186ede5fc7f4bb70b74fb85da54665e64439123681249d71f23ad0ed535be0c154e4ac8ac069a5c9eb0ab6fc3957e7b8785245c176d734e4242826e7b5debf3072928ba9b211f894538df571054a332b699ca542fbbe3b582ff251b91b2d4412a201c7f4f68745a847b2bd3164d1
    | 6 => 0x1c2e9d486fe395d7bb7a4d010a3be2282233a6a5c372959d1f26090abf4fdf70400c44990b6b07a371275762cb9b1447c9d5cf6d8864ee76593c30421f4b95c8dda1bef88c0da5886479eb9de8c8406199ccfe550524380763337fd99c97c072d5f4217573407b5cd31563e579e6d9f251e142b9a161ac90e181630365fae884
    | 7 => 0xd48e9d9bfbca0e29359b3ca9b59a50e858b82b11c6e3a8d7cfaa52170fc53ef54ba94485aa09b647832beb2fe018f14c2396704823e813989cd624183a2cc01990484d53a048c41e102daa747c56247378ca945a925e580762673a1e1817279e7053444e5965dd058c9358d54c405f08027cf5ba775e4a22ba4acae4666cf090
    | _ => 0
  fld packed 8 (i % 128)
def count (s : Nat) : Nat := if s = 7 ∨ s = 8 then 1024 else 0

def board : Nat → Nat → List Nat
  | 7, i => checkpointBoard (mask 161) inputs 4 (recipe7 i)
  | 8, i => checkpointBoard (mask 161) inputs 3 (recipe8 i)
  | _, _ => []
def atFinger (table : Nat → Nat) (ws : List Nat) : Option Nat :=
  let h := hk ws
  let i := h % 1024
  if table i == h / 1024 % 254 + 1 then some i else none

def lookup : Nat → List Nat → Option Nat
  | 7, ws => atFinger finger7 ws
  | 8, ws => atFinger finger8 ws
  | _, _ => none
def ck := checkpointCheck 161 scores count board lookup
def panel (s i : Nat) := ck s (board s i)
set_option maxHeartbeats 50000000 in
lemma block7_0 : span (panel 7) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_64 : span (panel 7) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_128 : span (panel 7) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_192 : span (panel 7) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_256 : span (panel 7) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_320 : span (panel 7) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_384 : span (panel 7) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_448 : span (panel 7) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_512 : span (panel 7) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_576 : span (panel 7) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_640 : span (panel 7) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_704 : span (panel 7) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_768 : span (panel 7) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_832 : span (panel 7) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_896 : span (panel 7) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_960 : span (panel 7) 64 960 = true := by decide +kernel
lemma good7 : span (panel 7) 1024 0 = true := (@span_join (panel 7) 512 0 512 (@span_join (panel 7) 256 0 256 (@span_join (panel 7) 128 0 128 (@span_join (panel 7) 64 0 64 block7_0 block7_64) (@span_join (panel 7) 64 128 64 block7_128 block7_192)) (@span_join (panel 7) 128 256 128 (@span_join (panel 7) 64 256 64 block7_256 block7_320) (@span_join (panel 7) 64 384 64 block7_384 block7_448))) (@span_join (panel 7) 256 512 256 (@span_join (panel 7) 128 512 128 (@span_join (panel 7) 64 512 64 block7_512 block7_576) (@span_join (panel 7) 64 640 64 block7_640 block7_704)) (@span_join (panel 7) 128 768 128 (@span_join (panel 7) 64 768 64 block7_768 block7_832) (@span_join (panel 7) 64 896 64 block7_896 block7_960))))
set_option maxHeartbeats 50000000 in
lemma block8_0 : span (panel 8) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_64 : span (panel 8) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_128 : span (panel 8) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_192 : span (panel 8) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_256 : span (panel 8) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_320 : span (panel 8) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_384 : span (panel 8) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_448 : span (panel 8) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_512 : span (panel 8) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_576 : span (panel 8) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_640 : span (panel 8) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_704 : span (panel 8) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_768 : span (panel 8) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_832 : span (panel 8) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_896 : span (panel 8) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_960 : span (panel 8) 64 960 = true := by decide +kernel
lemma good8 : span (panel 8) 1024 0 = true := (@span_join (panel 8) 512 0 512 (@span_join (panel 8) 256 0 256 (@span_join (panel 8) 128 0 128 (@span_join (panel 8) 64 0 64 block8_0 block8_64) (@span_join (panel 8) 64 128 64 block8_128 block8_192)) (@span_join (panel 8) 128 256 128 (@span_join (panel 8) 64 256 64 block8_256 block8_320) (@span_join (panel 8) 64 384 64 block8_384 block8_448))) (@span_join (panel 8) 256 512 256 (@span_join (panel 8) 128 512 128 (@span_join (panel 8) 64 512 64 block8_512 block8_576) (@span_join (panel 8) 64 640 64 block8_640 block8_704)) (@span_join (panel 8) 128 768 128 (@span_join (panel 8) 64 768 64 block8_768 block8_832) (@span_join (panel 8) 64 896 64 block8_896 block8_960))))
theorem closed : ∀ s i, i < count s → ck s (board s i) = true := by
  intro s i hi
  by_cases h7 : s=7
  · subst s
    exact span_ok good7 i (Nat.zero_le _) hi
  by_cases h8 : s=8
  · subst s
    exact span_ok good8 i (Nat.zero_le _) hi
  simp [count,h7,h8] at hi
def rho (ys : List Nat) : List Nat :=
  match fld 0x241e8700452bd4d5b9ac0800b194030a0023292721100198a01150119c0510843008c02906010001 5 (bsr 0xfd356f1ef6e89598f389cc02eaec9a74e968fdc8e90a70ade6a94e04ddfbeb78daa3d3cbcbc8cd82c8b110a9c6f26311c33ddce8bfca6579bf2fb6e0b9aafae4b6d3eddfb24e7b36ac56727da3255ffe9836ca2f96b10df38a5599d588a3c458878fa7a584ef97717cee56ca798bb9e87940e06777fadc0165e3f9c265b85c2d641ccac75cf1d879583f712c580c731957b07efd558e792a558b6be055809c225499bbec4f0e61214d99dc424ca69a8549936523398838913613983b346e7c9331cf2ecc2c7b9ebc298b49532544fb592448e2d92085ee49187beddf17882ede12009c670f4f26fe0cdf66f30a1bc6c4092451960379507400e99527007e3081 32 (hk ys) 7 0 64) with
  | 1 => vals.map (fun r => fld 0x1220045401090000000df0034800c70000000b5002c800a60000000e20035400c8004524077899aa106700345ba35680a18c25002c566125803d480d0000000ff003c800e5004c67a949821e4a84003b9f45276915c642002e5761a5c05d4a150000000c50030800a90040e0a6481185505f0030586226007d4e1d0028d440b508240000 9 r)
  | 2 => vals.map (fun r => fld 0xdf0048800b50000000d20045400b20000000c70042400a60000000ee004c400b9003fdf4529ea51761a003c9da459821d701700395c64292a114a150000000d10045000b100389ba35901dd661200355a028899a9600f003218c258419d480d0000000c10040c00a300315862282991440b00309801f811854209002a54e1d5417c0000 9 r)
  | 3 => vals.map (fun r => fld 0x1310045001030000000ee0034400c10000000b9002c400a30000000f20035400c2004566087899aa046100349da45680a1801f002c970175803d42090000000ff0038800c50048a7a94901de0a640037df4526e8d58622002d5761a59849440b0000000e50032000a9004264a848419d505f0031dc642630954e1d002994a15520340000 9 r)
  | 4 => vals.map (fun r => fld 0xf2003fc00e50000000d50038800c80000000c20031400a9000000115004880109004c660879ea524a8400452266a901de10670040e046182991505f0000000d20037c00c7003b9da457d149c64200345a0286e8d58c2500305801f618894e1d0000000b2002d400a6002e570175d8694a15002c5600f59849480d0028d42095102c0000 9 r)
  | 5 => vals.map (fun r => fld 0xe2003fc00c50000000d5003c800c20000000c80039400a9000000114004c401030048a40779ea520a6400456266a9821e046100426106792a11505f0000000d1003b800c10037dba357d149862200349a02876915801f0031d8c25719094e1d0000000b1002e400a3002d566125d869440b002c9600f5c05d420900299480d528540000 9 r)
  | 6 => vals.map (fun r => fld 0xff003c800e50000000e20035400c80000000c50030800a90000000df0034800c7003b9f45276915c64200345ba35680a18c250030586226007d4e1d000000122004540109004c67a949821e4a84004524077899aa10670040e0a6481185505f0000000b5002c800a6002e5761a5c05d4a15002c566125803d480d0028d440b508240000 9 r)
  | 7 => vals.map (fun r => fld 0xd1003b800c1000000114004c401030000000b1002e400a30000000e2003fc00c50037dba357d14986220048a40779ea520a64002d566125d869440b0000000d5003c800c200349a02876915801f00456266a9821e0461002c9600f5c05d42090000000c80039400a90031d8c25719094e1d00426106792a11505f00299480d528540000 9 r)
  | 8 => vals.map (fun r => fld 0x1150034800b20000001220037c00b50000001090031c00a6000000131003b800b9003ca6087769157017003fe7a947d149761a003964a84719094a150000001140034400b100356266a680a1600f0038a40776e8d5661200322106763095480d0000001030030400a30030a04616007d4209003160a6461889440b002a5505f538740000 9 r)
  | 9 => vals.map (fun r => fld 0xe20035400c80000000ff003c800e50000000c50030800a90000000df0034800c700345ba35680a18c25003b9f45276915c6420030586226007d4e1d000000122004540109004524077899aa1067004c67a949821e4a840040e0a6481185505f0000000b5002c800a6002c566125803d480d002e5761a5c05d4a150028d440b508240000 9 r)
  | 10 => vals.map (fun r => fld 0x114004c401030000000d1003b800c10000000b1002e400a30000000e2003fc00c50048a40779ea520a640037dba357d1498622002d566125d869440b0000000d5003c800c200456266a9821e046100349a02876915801f002c9600f5c05d42090000000c80039400a900426106792a11505f0031d8c25719094e1d00299480d528540000 9 r)
  | 11 => vals.map (fun r => fld 0xd20037c00c70000001150048801090000000b2002d400a60000000f2003fc00e5003b9da457d149c642004c660879ea524a84002e570175d8694a150000000d50038800c800345a0286e8d58c2500452266a901de1067002c5600f59849480d0000000c20031400a900305801f618894e1d0040e046182991505f0028d42095102c0000 9 r)
  | 12 => vals.map (fun r => fld 0x1150034800b20000001220037c00b50000001090031c00a60000001140034400b100356266a680a1600f0038a40776e8d5661200322106763095480d000000131003b800b9003ca6087769157017003fe7a947d149761a003964a84719094a150000001030030400a30030a04616007d4209003160a6461889440b002a5505f538740000 9 r)
  | 13 => vals.map (fun r => fld 0xf20035400c20000000ff0038800c50000000e50032000a90000000ee0034400c100349da45680a1801f0037df4526e8d586220031dc642630954e1d000000131004500103004566087899aa04610048a7a94901de0a64004264a848419d505f0000000b9002c400a3002c970175803d4209002d5761a59849440b002994a15520340000 9 r)
  | 14 => vals.map (fun r => fld 0x1220037c00b50000001150034800b20000001090031c00a60000001140034400b10038a40776e8d5661200356266a680a1600f00322106763095480d000000131003b800b9003fe7a947d149761a003ca6087769157017003964a84719094a150000001030030400a3003160a6461889440b0030a04616007d4209002a5505f538740000 9 r)
  | 15 => vals.map (fun r => fld 0xee0034400c10000001310045001030000000b9002c400a30000000ff0038800c50037df4526e8d586220048a7a94901de0a64002d5761a59849440b0000000f20035400c200349da45680a1801f004566087899aa0461002c970175803d42090000000e50032000a90031dc642630954e1d004264a848419d505f002994a15520340000 9 r)
  | 16 => vals.map (fun r => fld 0xd50038800c80000000f2003fc00e50000000c20031400a900000011500488010900452266a901de1067004c660879ea524a840040e046182991505f0000000d20037c00c700345a0286e8d58c25003b9da457d149c64200305801f618894e1d0000000b2002d400a6002c5600f59849480d002e570175d8694a150028d42095102c0000 9 r)
  | _ => []
def B (i : Nat) := mv (mask 161) (fld 0x401506000e10f10500106e21e53f31f21400100 12 i) inputs
def I (ys : List Nat) := bsr 0xe90a70adb24e7b36ac56727d8a5599d57cee56ca580c731955809c223613983b2448e2d917882ede0a1bc6c40379507400e99527 32 (hk ys) 4 0 13
def test (i : Nat) := ck 10 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 161 (cutBoard 10 inputs B) (cutCount 10 13) (fun _ => I) (rowOrient 161 rho) scores 11 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 1 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z1 : span test 1 1 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z2 : span test 1 2 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z3 : span test 1 3 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z4 : span test 1 4 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z5 : span test 1 5 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z6 : span test 1 6 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z7 : span test 1 7 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z8 : span test 1 8 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z9 : span test 1 9 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z10 : span test 1 10 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z11 : span test 1 11 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z12 : span test 1 12 = true := by decide +kernel
lemma regionOK : span test 13 0 = true := (@span_join test 6 0 7 (@span_join test 3 0 3 (@span_join test 1 0 2 z0 (@span_join test 1 1 1 z1 z2)) (@span_join test 1 3 2 z3 (@span_join test 1 4 1 z4 z5))) (@span_join test 3 6 4 (@span_join test 1 6 2 z6 (@span_join test 1 7 1 z7 z8)) (@span_join test 2 9 2 (@span_join test 1 9 1 z9 z10) (@span_join test 1 11 1 z11 z12))))
theorem finiteCheck : ¬NatRun (mask 161) (goal 161) 11 inputs :=
  symCutRoot (rowOrient_sound rho) roof (fun i hi => checkpointCheck_sound closed (span_ok regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 12 ≤ t := by
  refine proveAtCap 7 161 11 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finiteCheck

end Row26

namespace Row27
def vals : List ℕ := [1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 16, 16, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 36, 36, 36, 40, 40, 40, 40, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 48, 48, 48, 48, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 64, 64, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 68, 68, 68, 72, 72, 72, 72, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 80, 80, 80, 80, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 3, 5, 9, 17, 3, 6, 34, 66, 5, 6, 9, 24, 3, 5, 6, 9, 11, 14, 17, 24, 26, 34, 42, 66, 74, 96, 13, 14, 28, 17, 24, 3, 5, 6, 9, 17, 19, 22, 24, 26, 34, 50, 66, 82, 96, 21, 22, 28, 34, 96, 3, 5, 6, 9, 17, 24, 34, 35, 37, 41, 49, 66, 96, 97, 37, 38, 100, 41, 42, 56, 104, 3, 5, 6, 9, 17, 24, 34, 45, 46, 60, 66, 96, 108, 49, 50, 56, 112, 3, 5, 6, 9, 17, 24, 34, 53, 54, 60, 66, 96, 116, 66, 96, 3, 5, 6, 9, 17, 24, 34, 66, 67, 69, 73, 81, 96, 97, 69, 70, 100, 73, 74, 88, 104, 3, 5, 6, 9, 17, 24, 34, 66, 77, 78, 92, 96, 108, 81, 82, 88, 112, 3, 5, 6, 9, 17, 24, 34, 66, 85, 86, 92, 96, 116]
def inputs : List ℕ := [0x8d8846c4de36026c41362679b080769016d47c000000001fff8000000000fffc00000000000f, 0x16290b149038a95148a8a488c553eca27cd4bc4000000000000000000000000001fff83fff0f0, 0xb8305c183840c4e18270c1c1063808c70098c8bffe1fff0e0001fff0fff870000e0001c000300, 0x21425ca3c085008a12751e022820311756e30100001ffff000000000ffff8000000001ffffc00, 0xb98790c1010604ec3c460804303abe1c0702023fffe000000001ffff000000000ffffe0000000, 0xc2046102260816f03f781ff7c0c4c00098001000000000000001fffffffffffff000000000000, 0xfc07fe03fff01f002380113800870000e000203ffffffffffffe0000000000000000000000000]
def scores : List ℕ := [0x1f067234a52749c, 0x19c1f0c8b3280a1, 0x1603207c9f2689b, 0x7c0c19c9d270a5, 0x19c0c1f09f26c9a, 0x2345807ca1280b3, 0xc80c11ca02709a, 0x11c0c19c9b2689f, 0x23432030a52689d, 0x19c0c1f0a12709a, 0xc81f234b327ca0, 0xc81f11ca526c9d, 0x19c0c11cb327ca1]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)
def recipe7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xe51762276000e30341105f10b51e76387e20a40350105104e53103363000e61331103f50f41a86362e43a63a73331000e61331105000e51350102500a40a50330100501a31310100101e63374f20e50320253000e65351364000f10b72275100e31351103000f63671331000e10340106000f21b51242000100e20340000e61101263f31754b75275000e31351104f32a52b63343000e61310760e10360102106000e42372105000e20a53331500a10a70340000e30106340000f32a52321000e61310106000e62342106000e51350103500a10330100000f60674343100102e64375e40b20f60362100e31351102000501a31321000500a76363000e40360104500a30310106000000e40320000e40360102000e51310106100500b40274500a20370103000e65353106000103e65354e10360103106000e40653331000505a76365000f32a52320f51e75350276000503b53272000e20320106000e30330b63f30732a52320000101e31342f10b40330105000e31361105000f40741250e10350101101e65351364405100100e63331000f60665354500a30a50340000e30360105000e40360103500a20370102f50a75b52375000f53a75350000e40720330e30a70320104000000101101000f50661330000000101103000e31771342000504a43330000103e54343000000e61351e30350103106e10340b10104000e40a70360000e53a73331500e42353364000e30350b63000e31371102000f52664343500a50a70310000f40652321000e61341102101e52102363000e21a40310000101e65376000f40252b20e30a70320103000000e31331501b21a41342000000101102f50b70102264000106e60371000f20102242000f21b51241000100f40275000f10101231000e31310106000000101104000e31310330000e51340102e20320102104000f30641371000000e42353000e30a50320000e40740370000e31371105000e10730340000501a31351f60761e42353000e21a50340f20721e71331000e10350102000f42650370000000e31342000e61341105000e10a30340
    | 1 => 0xe51310f61275500a10330103000e30320730f10b70b40670000500a40350000501664343000e10350106e20a60320106000101102103000e52a70320000e65b52375000101101101000e21a50360f30f21343b63f20721e76363000506a10360000101103104000e61351103000000000106000e42a62340000e31371b43000e51310751e31310330102f50b76506360000e53a73332000e61351105000e42a72321000f41642372000e40a70330000100e50361000e40330740501a31a51320000e53a73330f21b43b75275000e31331103000000100100000e31710341000e31342103500a30a70320000e30a60370f32a52732354000f31650350000000102103000000e65350100f40104275f10101231104100e10a30350000e31731361000100e20370000e42353103000e10a50360000e20360101000e42353105000f40252752000f53b73264000f30b53250e10340f10242f10b32253106f10f50b80340000e10330101000f43650330f50f21b51361000e20720340000500b20242101e31361104000100e40330000000e30370000000103104000e31342105000f53661331000000102102000f10242103000e31351106000000102104000000e51330000000104105000f32640360000e30341103000e31761342000f31650370e30341e42353000e61101264000500a10340000e31361102501a31310721000e31361104100f10a41331e10330f20253f20e52264341f21a52353103000e31a61330000102e64364f50f32b83275000e21a70350000000000100000502a52330000e30341102000e52340104000000103105000e51730370000f61763275000e42772353000f10b52253000e20340103000f10242105000000e20360000e10730350000f60672342000f21b51251f10e41371242000e10a30350102e65105376e30350e65376000e42b21341000100e40370500a30310b42000e32a52362100e42a72342000000e10330101102e64343000103e64343e41a71361103000e31a61310e30320330400000500a40320e40b20b41b63000e30a70350000e62102263
    | 2 => 0xe40b30252000000100103f51b71102364f30501331240000000100101000103104105f50b70760741000e31371732000102102104000e30370105e20340f41242f10242104105100e31a51370000e51370751000e31361b43000e20360102000f41a65343000e20360104e10330e31342501b51275b54000e51350106f10f31a71380000e54a73332000000e20340000000100102000e10330104100e40370103e32e76361375000e30360101f32a52720354000500b10231000e30a50360000000100104000e41a61310100e40330a64f31754b65276000e65354106f50f43a86361e51762103275000f50a75376000e20360103e10730350103000100e20350f32a52b21354000f30b54252f20e50350253f41f32252b63000e20320a42000e21a70340100e40370102000e20720370f30b54b75272100e40370104000e10330103000100e41330100e30a70330000e10330105100f10b31221100e20340101000e31a51331100e20a40370000e65b50343000000f40252000f53661371102e65376106100f20b52260000e20102360000100e60320000e31106341500a10330750500b30720220000e40a70320e51350102102000f51276b65000e10a60340000e61b10360000000e40340000f21a52372100e50100360000e40320104f50b70f10351000100e31371000000e30360000f20721230f10b70b20b31f40741504330f10b70665752000000101106000e20a60350000f41b75275e30a70330106e20b20b52242f21b43b73743000101e51362100e30a70320100e40370b40000f41b65276f10b70b20b32e10340b10106000e40a60370100e60350760f10b70b20b51000e61341761000e51100273000e61341106e21a40a60310000f61675352000e31351732f10e50320242f50f41743363000e40320105000e40730340000101e64340000f20a53343f10b60b20a75000f20253106000101101102100500a20370101e31342102000e42b21361000e61351102f10b40330743000e51340106000e65351764e20350f20253000000e30320101e31342104000e31731342
    | 3 => 0xe31310b30000e31361732000000e65352000e61351106000000e42320000f40252105100e40340101000f20103364000e10360101000000e40370000e61772276000000e20370f51e75353275000100e54365000f31650360000f10b31b72000106e50361000e30360103f20b50341641000e40340105000e21a50310e20b60a75376000101102106000e10370101e30a70320b63000e64343105000e41a61330000e50a70340000e10370106f10b70b20763000000e54343000e40330102e31310730a60501e51340351e30e76362375000e42353106f30f61732363000e30320104000100e65352000e40730370000e30320102000500a40310000e52104340000e51330102000e21a60340000e30350101000e31342106000e42102342000e30760341e20350101101000f50a75351000f51b75265100100e20331000000104106101101102103000e10750360000000102106f50a75b54375000f63671310000102e65376000e30320103000000e61361500a40350102f50b70f21352500a20330a31000505730243000e32a52372000000e10360000e10a70360000000e30330000100100102f10b31a52b72e10350105106000100100100000e30330730000e30a50330e51340f61275500a40a70350000e54a73330000f63665351f10f51a81341000000103106000000e10370100e20370103000000105106f40f32262354000e21a40370000f20b52242e10a50360102f53b73103264000e20731253000e30720341000e51340751f10f51a71340000f31b75275f30b53250104000100e20320000e20340101000100100101000000e30350000000f61275000000e42342000e42342103e31342103105000e30350730000102102103000e30370104501a41a51310000e20350102000505a76360e30a60330106000100e31342000e30341106000102103104000f40b65262000104e43354000e42a72320000f32a52353000e54a73343000e61331106500a10340101f20f40342252000100e20331000100e40360500a10a20330000e51370a65f10b51743b73000e61b61275
    | 4 => 0xe65353000e31310730000e10360103000105f30254000e30330103000f40741242100e41a70310100e64b41374000000e20320000e30350102000f61102274000502a42332000e10370103000e42342104100e60340102000000100106000103e63374000e10a60370f20721b51b61000e10360b10000e10370105100e42a72321000e51710370000e40720340100f30631371000105e63374000e20360106f32e52320354000e40104340e30720341105500a20340751000f32a52354000e31a71351500e31310330000e10370b10000e30730341f30732a52354000504631330000e21a50370000100101102e20350e51350e30370103104000e30350105000e42353504000e32a52320500a40320106100e31342102000e40760370f10b31b43b73000e61310665000f20b50341000101e64375000f60761275000f60763273e61331103106000e42104342000e31a71331000f40252b21000e42320341000000e31310e40340101101000e20340102000500a20340000e30a60320000100102103000e30750341e30360101101000100101101500b10231102100e20340106000e40320740000f10b62276000e10350710000101e31310f20b50741251f10b32b42232000f42a65343f50102a74375000e40370101f50104a75376000e42a72362f20e52372253f41642b20310e51350103106000e30b20241000e20370101e41b52642342000f40b75272000e42742372000e41a71310000e20100275000f51276b61000e64103243000e40320106000e30320b30000100102104500b10231104000e62104342f21a52320342000100e54342000500765276000f50b70274000500a20350000e42353104000000e42321000000e65376000f60671341000000e42362000e52a70350000e10a60350000e31a61350e30350f51353e10a60340102000e31b10350000e40340102000500a10320000e50a70350f10e41253353000f64672342f10b60a75376e20350b20b41e20a40a70360000e10a70330f51e71310276e10750360101000e30360102f10b62b76273000101103106
    | 5 => 0xe30370101b42000e42762353000100e51362000f54a76363000e51710350100101101103000f20a53363000e31b10360000f10b32253102e53102364f10b40b20332100e20350b32000e40a60320000e40a60340000e42a72342000102e64375000e42321104000104e65376000e65b53343000e42362104000500a20330000e42b20352000502a42352000000e31351000f42650320000e61361105e31310732b43000e32a52321000e30330631000e65351105000f42650340000101e54365000e10a70350000e65751375000f10b70b20000e20350a42000e20740360000104e65352000e10340101000e42321103000103e65376f10b60f20360000e42362103000102e51362000f41642342000e10100276f10242e65376000e40370102000f50b70265e43b63a75376000501b51275000e20370104000501a71310000101e61331000e20370102000e10100274000e30760370000f20253763000e30350631000e30370b53101101101106f21a52b20353101102103106000f50f21363000f32640370000103e65352000e10a50370000e42320103000102e43332000e61b10340000e42320105000e30a60350000e10a30370000500a40330000101e64342000e40370105000e40a70340e40a70330106e30330101102000000e65351500a20a50340000f50a75354000f60665352000f20a53373000100100106000e10740350e31342103106000f40252743000f61275105e31342102106000e30b20340000102103106000000e10340000506a40360000e50a70320000e10a50340000e61361b61e40330b40b63000e61101262000e61361102f10b70b20665000e54343105000e10360104e10a70360104100e20340721000e10360102000e20350720500a40310104f10e41381341000000f51276e10370e31342000000e61310000000e62342100100100101000f61105273000e20a70320000103104106000e10370104000e42742353000102102106000e10370102f50b70743363000102104106000e65b54375000104105106000000e51310000f60671331000f20b73274
    | 6 => 0x100e60340106000e42321743000e10105340e10330e65376000e10340104500a10350100000500a40370000000e40360000500a20370e30a60350105e10a30370105f51b71742362500a30320100000e42102276000e20a70350f10b60f20363000f51104276000e21a60370000e61310104000e65376661000e30350106000e61310102000e42342106f53104a75376000e42320743f10b60752b72000e10350101000f30732240000f51107270000f64675353f40741b74272000f60665351100e31342106f10b60a75354000e65352105000e30a70320e30320b53b65000e51310104000000000101000f50b70264000f40742252000e30a70330000e30642362000e20320104000e10340b10000e30320101000e20320102000f51105276000e30103360000e21a40360000f41642362000000e31371000e30100262000100101106000e40360105000000e61341e31a51a61370f21a52b43354000100e60350000f31b65276000e51310103000e31b10330000e65105253000501a51370000e42a62320100e20320b32000000f20253500a30a40320000000e51340000e65376506000f41642320000e20320103000e20340106000e40330101000e20320105e30330103105000e40370106000f65674343000100102106500b10231106000e20a40370000e20a60320f10b40330b62f10e50320b70000e40720370000000e10350101103e64375000e31b10341000e10730360101101e63374000f30641331100e20350106000f20b43254000e51740370000f21a52342f60761102274000500a30340000000000000000100e31331000503732253e10370b10105000f20253b32f32a52354105000e10730370e21a50370105500a20340101f10b31b62662000e40340740000e20370106e32a52a62370000e31751371000f40252106000e42720352000e65105376000103e65353000e30720360f20b50341105000000e51370000e30320b53000104e65353000e53a73353000e61341665000104e53364000f10b52252000e20740350000e40340106000e42b21352000000e40330
    | 7 => 0xe54a73331000f20253104500b40730231000101e41330000000000104000500a20310500a30340101000000000102000503b63276500a10370102e30350b53b65000501a71321e30360101b62000e40340103000e10330102000e42a62370000f61765275500a10370104000100e65376000f10102363000e20a60340f21b42b53b63000e20a60370000e30a70360e20a60320105000f10b32243000f21a52353000e51370102000e31310b43000e51370104000101e31371500a30340102000000000103000000f10242000103f32254000000000105100e31331104000e51340a65000e41a61370000e40330104f31e42b84354f40e31263354000f50f21362e10a70330106e30a50a60370000000e31361e10350e30341e40a60320104100100e63374500b70760274100100e20340000e65352106000e51370103000e42320106000e31342104000101f51263000e31751342000000e52340000000e30341000e30730360000f21b42232000e30a60330000e30330b53000e31a51371f10b40330b52000e20a40350000e40107310500e40320340000f31b63261e30350f40252000000e61331000e30360b63f50751e42342000f30731231000101e53364000e51740340000e20a70360000e40340642000e42102265000e54343106000e42107330000e31101264000e40a60330e10a60330105000000e42372502a42321104000e51b70265e30320b53a64e20a70350101000e52a70310500a40310106e40330b40732000e30350b53f10b70b20761000e31351105e10a70350103000e61b10350000e41a71331000e51370b51000000e51350000f21a52362000100e31310000100e64375000e20a40360000f21b63276000e10330710100f42a74340000f10b41231000e61361761000e20b50242000e61361106500a40330101000e20750370500a50a70340000f20b63264000000e65354000e10360106000102e64341000e30330106000e21a70310000e50a70330000e31371731000e21a70360000f10b40330000e51750370100e51362105100e20350721000100e64341
    | _ => 0
  fld packed 48 (i % 128)
def finger7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x7e56d0471084d3f59c915c05f432f73c276d6b12bf34946d9edfba90aa43c90e42f716c91b795ad14f1ea5d42ace20d08167953f95ad90fd066ddcf85346cc5cab3ac5587ee8532d3e8935af1221e992868a86f993502868a77e069f3f6a7cb6af985bc0f295ce378b0243ad3aaf1f140c01c283d41bf566bfef801e5a9709a5
    | 1 => 0x47291803b38032bd82558fab113490469c21973735290e5bfa3b91edae4580bc4ca35bf5118687eaa0f77024f4602a2a635d8b277542b8656fd7a2b0294ef470b0f5c5f34c131e34ee36550fc563036af8de03ebe1c49b2b66fc2fd6f1016863b73cb920a4327737d196bcce48867cc5ad5131077ba02324942f027b73f0a11f
    | 2 => 0x9f5532797ea6ebaccf7a7cbe7969a2ac07854d44a5c6952001102087ad8219c21b4203ea26f294913157d0c9b082b08afaca6c3ae2bc483ad494d5e489b18d8db415e8e4f4dbbd382cb3dc837ab4a517f9d61ed7573050269d64b62f442b758d4597d07b9d2d1fc67e5c4e0ad901db87b16e679f01f0eac39caa28378aae06ea
    | 3 => 0x661b19b077428c1708c63396173ca23c8cb7372f5830bfa633e85f71f922cbe369bcb9ec509d19d1c625a2f934c4c1ab543ddd4a4c84b214ad20e06749d84ca765da8279b56ae2cde30dd2594f498daf413219504a1b53a4a1a5a7e42fe7c554bbaf9035bec82e399d0bb4d1aed51dbdcd25caa24c7a3a1519f59258a089494d
    | 4 => 0x3c32148d059f508a424bd4deb0b71c92a460cbdecaf5be37e8fac0052997e8420c0c7ea0aa3a0e6bed4fe884f69d5813c78ad6731cdfae80e05f110f2136915aee6bc3192fe930134b06ceb453a75580494610408127d24d3805c5a4c7546db4ca32b025d92191e1f1e29e3cb9e1a2c2f266901e9bb1edf6f9da76f0a1365f15
    | 5 => 0xaf93bfe805ca7877ac95cb9d9960d0f8e0d1c92b1bcc54c379cae7603def8a5e470c3eb84b06cd8c7d8ed58adaa995dc2470d485a45bae4778c60822d56dae588cb22012e1fc2a82cb75cb791bd894c9960d75bc21d9b00eb2d9379a3efba376651639eeb18066a2058f4ad6ce474317ccfabb101f061f482f5f607139f39a4e
    | 6 => 0xab72919a2d03c1b791357e6af41218bd34a104165f2df2dcf48694d97c085f27e772debfb2e2f9349a8b4d2fa3c758f8282e4e67b1a82b53db86d31c8e62e5c4e4887452f98d87db4a08f3b844232d436690bdc0830760392f89b6fa58c4a134306cc3eb3181f5cdbfa9e5826090c0b703c4086189350bb2a4c6a78d4ba44a77
    | 7 => 0x4a0f9adb593d46824eab39771e7b287d2bc59f1557e84ada459b624bda246bc9071d861f7607696687ddb7a066d43b866e17c643cea113caef4ca01d98f0c58d4e931e2b1957e88f4dc10b0b35a120f5998cc73fdabc4117a7b14fa2901b78e03079917a15ecdd619d662b76a3df048bc19673f9a3df9468178a8b9245081614
    | _ => 0
  fld packed 8 (i % 128)
def recipe8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xe50104000f20a73000e60b30000e42106000506a10000f43107000e53732e10a30107000103405100e20105f20101b32000e43107000100f64e20b31b62000102f62101f21b73000000505f30b74665000e65753000e40105f20b53104503a64a74000e40103f20102b42000506a40100f10b71000f20a43000501a76000e61b10f60f53275000e31743000504732e50a70105000501b61000503b74f21b63105000f41b64f52b72102e52340405000f61670f10b31a52000500b50000000e65000e41b31000000e52000f20721000101e21000e40104f20b53103000500b20000e40106000f41107000e42772000e10102000f63670e50a70104000e40a60f10b62753000f21107000e43b54100e60107500b30b43000f65671e10721b41000f20b43000e32a52e10a70107101501b41000106f60500a40a70e31342f32000f31b65000f61106f21b73103000f32b74000502b42000f32640000f50b70000e20103e21a70106000e20105000e42a62000e61351f32e52365503b64b76f10b72102000f61672000100e32000e43731100500b70f60f21373f10b31b51000500760f10b60a75100101404000e21a60e40370f60e20a40107f43b65107000e31331000f42103000f21630f20b50741000e20104500104107000000e32000f32105000000e10000f42106000f41b65f10b72103000e51762100500102f10b72105000e42353000e43754000f51a76f21b53104000f50664f30f21b85000100f50000502b52000e64731000101e42000e32102000e31342e31342f53000100f30
    | 1 => 0x501a61e10e53364000502b62000f41642000f52107100e10a70f31103b65000f52660e32a52106000e52740000f62107000f40107000e32105000e20750000000e61000502a32000000402501b21b51000000106000e10105f30101b73f30731b73000e10103f20f60761000102f52100f10b40000000e21000f10b62e43a63107000f53107000000e41100f31640000504630f43b73b54000100f31000100100f10101b31000500a20e30a60107101102104000e10a50f42b75106000e10104000e32106000f10101000101406100100f31000505b73f21b51743000502a76000e10106000e40b30f41b65105000e30102101103404100f60103000101e43000f52661000400105000500660000e65b54000400103000f61765e20350f40000f32b64f30f62b84000e30370000103104000100f21000101e62000102102000500661000f21b43000102104000e51330000104105000f21b62e50102105100f60102000f30b74000e61676000102e52000e61101101101f61f31102b72000101504000400104000102e42e41a61105000400106e40b51b64000100e51000106e30000f50107000000100000f10b42000f60f21000506a20000502a42100e32a52000100f42f30f21b75500b70106000000f10000000406000e20a70000f20107f53105a43000f10102000f53664000000e54000102404000000e30000104405500a30a50000f40743000101e64000f60506000e10330f30b54b65000e53106e40a70107100f61673000000e63000e51b70f60101762f32a52b54000e10a60
    | 2 => 0xf50104107000100103000f60101f30731b63000100101000101403000f41652f21b43103000e21b50000101e53000f10105000104406000f41a65000f10103000102406000e40751f21b51652e20a70105000f61763000e30105000000500e20a40a70000000e60000e50b20000100102000102e43000f42105000e31a61f50103107000f42a75000f43b75f10b40b74000100104000e40107f20b53107000000f62000e31b10000e30a50000f10104000103406000f54b76000f10106000105406100f42104400e20340000103e54000100e42000e30104000f64670102f62103000e30106000104505000e10b50000f21a52000101e63100101f63000000f60000000f31000503a74000f32b63000f40a52000f30101000f52b76000f50751000000404501b31b74000e63106e40b20b62000f40742100f42a74000100404000f60673000f50661000f20b52000103505f53b76106000e20731000505a43e30400352000e52105000e42754f50e73373000105403100e42a72f10b41104f30e52364000f42107000101106000501a71000e20107000101401000f40b65500b20101e30360f53e40a60103e64343403000100f62102e32b43000e65751000501a41000501a21f60f32676e31361405502a32a42f20b43104000f10b32e60b30b53000f20b42f40f21353000500a40000e52106000f50106502b32b73000000e64000f31105000000403000504a63500a50a70000e31b51e40a60104000f32107e42a62105000f60665f43b63b76000f31b75000e30320f50e74373000504753
    | 3 => 0x101501000102e54000e54a73f40104b65000e61751f51b71a75000f30104000501660000f10b70000e62b52501a21102000e20370e30502242000506770f20b42105000e31b42500a40104000f53661501a71103500a40102000504a75e21a60107000403105000102e63e20104107000102402000e32107000f30105e65376f65e50e64375000f30102000101f63000e21b70000e10107000f40a75000f42650e43754107000101e51000e42753000100e64f10b32104000100e41000e53b64f32b53b73000f64107f51753b76101e41a70500a40105000103e64000e32a62000000503000e64106000e21b32000403106000e61105000f32b73000402105000000501000f30106000000502000f65672000e61361000e63732000e51740000e21103000e41105000e21105000f10b40000e41103000e30330100100102000e30642000400107000e63730000f42653000e52b40f60f31375000e61104100e31a51000402104000e61106000e30b41000f64673e51b62752000105106000e54b73502107770000f32b54e10103105000500b60000000f64000e60102000000e51000e41104000504653000f21a53000e41106000502a62000e53107000e20740000f61275000e42342000100e21e10a50104000500a10000e52a70100f30b54f21b43104100e40751000101f61000104f30000000401000e51770000105f63000e50107000e61731000f41b75000f10b51100501b41101102e43000100e54000e42102000503643000f41105000f10b31000505663000501b31000f51753
    | 4 => 0xe62100f41107000000f41000e41a71000503732000500664101504107400104107000e20320000000f21e31351f43000100e60e52a70105000100401000506b60000501a31000e31742000e10a70000000f61000e21732000103f64000401103e40b51641000401105000f10107000000506000f60672000e32b43000f64105f10b51104000e51106f32a52354000f54663000e30107000103e30102504652000e54107500a10a40000501b51100101102000101503f32b54b75000f60764000e20a40000e63107000e31101000401104500a10105e10a60107000f43b65500a30101f41103b75f21b42b64000501763000401106000500104000500a60000e60105000500102000e31310000e60103000e32743e31a61105102f62106000f50754000505107100f64106100101101000e43a73000e42742000f50663101e43a72e30a50105000e51b62000000e31000f62104500b30b73000f50f41000502b72f10103105e65107b60000e42b53000f50b76102102e43000f50f21000e60104000500105000e20770000e60106000501764e31342f41000e65107000f31104000e52107000e64775000f31102000f60104000000f51000f62103000000504000500b10000100406000102403e30a50106000e42321000e65376000f62105000100e43000e40653000500a30f60f43375000f31650e41506241f20b52104000f40b75000f32a52000e65b50100e42105f20b43107000f60103000f60762f21a52b53000103404000f31106000f20b50000f64672000101405000f60105
    | 5 => 0xf50f43a86f10b51407000f62674503a54a74000f51b71000101f65000104403000f51102000103f53000e31104000f40a65e43a73106000e31106e40a70102f10b51743100f60762000102e50000100405000e50100000e62b73000000f65500103105000e31761000e31351000e50b30000101f32000f20653000f51103000f21b72f10b60b76e30370f60000e50761000100f61000500b76000e64107000f51105000403107000504106000f52663100104406102e43a72000f10f73000f61673000506a30000000f50f31b75106000506a60500a30105100103504f40103b75f40f72375000e40b51000000f20000500b70000100f20000e30a70000100403f40b75105000e40b20000f32a64f21b43b63000e61772f20b50106000e61107000f30b54103e54a74f40f32353f10b51e76f10f63b87f50a75507000402107000f54106000e40a70500e20331000101e61000e21107000501b41501a41a71000501b21000e41107000e52b10000e21a40000e10760000e60b50000000f43000503105000e10a30000f60671000102502e10a50107000000e43e50a70761000501b71f10b40b20000502104000501102f41743b74000102405000f31652000101506000e30b64f50b70740000e30760f40743b63100e41103000503631000e21a50100e41105000e20a60000f51276000100e63000e52b63000100402000103403000e54731f10b41f72000503106000502103101f32b54500b70664000501103000505b53000e41b41000e42a72100503742000504b75000e51b30000e51105
    | 6 => 0x102e32000505631000e43105100502a62101e61103e30741b61f50751f72000e40360000e21a70101101506000f21b73000f64106000101f21000f50a75000e40730e30103b53000e30b20100503a74e20a60103000503b54e20a60105f32b64b76000f43106000e20b70e10a30106000503a54000f53b76e20f52253000f21b51000101f41e42a72105503a53740f10b32b42000e43106000f42651100e31742000f40101000000f42000000101000101f43000000e20000e20b40000f63665e20a60104000f21105f10b31107100e21a51000f10b72000e54743000101f42000f31b63000100501000f54660100101106000100500000e61341f21b43b73f40741b74000f61104f10105107502103105000f61102100e30104000e62104000e62773000f10b52000e62106000103f32000502664000500107000e32a72000000f32000f21104000f41106000e51730000f21106000e31731000f21b53e10350f40000e53764000e64103000f61103e40360f50000000f52000e30730000f42a65e20a40103000100f63000103506000100e40000000f40000f41650f53e75387100e30105000e40b40100e42107000e30b74000000000000000f54000e10721104505107501b51102000e43a63000000f53f20f50352000e64b43000f31107f61275406000100400000e31105000f60106000e32b52000e63b74000404107000e30750000f10a72000e21b40000e30a60500103104100404107000f42b75500b10b20000f20103100500b20e30a70102000f43a65000f20101000e40330
    | 7 => 0xf40102101103f64000f40104f50b76106000000104000504b65000100f10000000102000102f43000f32106f10b32b43000f20b63000e63b53000102f42000100f54000100f60100e10721000105f43000f51107000101404000504107500b10107000f41743000000400000502765000f40103000f51b76e30a60103000e53730000e65b51f50f32364000f63672000000103000f40106000f50662000000105000f54105000e62102000503b64500b70763500a20a30f10b32b73000e52b20000e31b54e31104105000101f62000f31b73000f53a76000e41a61000000e53e31103105000504b63e30a60104000e40102000e52763000104f65f50f41b65000e32b62000e30341f10b31b43000000e42000f60675f31b73a74000e63731f20101105000000e50000e30b50f10b31f72f32b63a63e30b41b63000e50b40000100e20000f53a75000000405500b50b75f32b63b43f30105107f60f42375000103f65000f50104f30f61364f20e50264000f50102100104405000e42372500a70105000e53a73e30330403100e64107100f20103e30a70105100e63774000f21b63e30a70103000100f40000f20102000100503000e50b50000f21a63000000f63f41b64a64e40f32263000f52b72000f64671f30b54104f20b53b75000501107000f50103000502107e30341f65000f50105000101f31000000e40000f20b53000e20102000f20104000f51660000e65b76000f20a63000f43104000e50a70000e30b30000102f32000e63774000f10b60100100500f10f70773000f54a76
    | _ => 0
  fld packed 36 (i % 128)
def finger8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x1e77bcddfaacf044443632c3a7353e6e5ebc840fb43638ddccf2c183607acc062bd2bff801a78b2247b8b57eaa6a88bb628cd33f9a675dd506bbe266db30e0d9a196c374d4a33c4138c6df2664fc2964024686b652769894939689a145300a35f88ed7c0a9194cac72f9e6d6c38bf913a213c21a1d9ea494f5e323a2bf971b10
    | 1 => 0x742f5b3cf7aada2a4b8c3835e63eb511de3597c5d66cee168949c656343c783f0d1e0bf5660ebd488dfb71ac53cf9a3fcb5c8beb40ba27f413d14ce54475773646a9c5f3f4401eba1236550fa6c5a0492a58d1cb61ebf8295f12bade3ae768d7e99c40030b25c4c44254bdf4b0ce82bf2d988e8a46a023bcc6d2ccaf0b13d8e8
    | 2 => 0xd4552ffb7e9182ab3928b12fe0da582a3e43ef1a5a71420f019a2fec823de4ae1b4cf11f2a9d5fdb4277f3be151d0ec6c52bde4b9d03bdbf9ed74a542dabb3ee045664461817a443d1c0f5e3c38f6397a7bd11960c113a26463d6f39a4c11c49217cdd0757a17dac909d97abb71d5d37f53054b4d4375b9f25351386c7aec932
    | 3 => 0x85449428d06adc5905076d968d6f98de0a0add331d61a146d6ca250b25463482ea042291444737b038a56eac49eaadcec9bb4fe10167a46acd0fcff64dd85d6edc65b5818e6ae2fe89ae63942550417968ea5b614a4ab290a140f3cfdf13d2132bfb3dc6bec8f428d12086fd0eae5f7ea8f0ad333c58deaccb1380d6fb986643
    | 4 => 0xaf2145956e0172442b7d8b00dd9a716aa980b9f8c94436dee6c7b13a64792421657dcaeae886b6b7e665161d991198614acb5d51dac3347e02f700f583fd9680288d3194287a5238a3d870e4464378d1c595c3309db0d3ef38805dfc4d4dfed8ddcb8efbf3d1a50f1e2d27d4728427420afdf446cc1cd397df89b8a3eec9c53
    | 5 => 0xdd2fd2db6910dcf2ce22a5f53a36d7ea0e55fc49ada6efc363109a75f6bff8941ac75a8fdea27eeeaa76230fbcf10fd9467abecb9099d266fb943bbd6b80efdf342fcca20cc80c27a7be99f0a3e846a23a10e491813c196665b7984f9abae325f40efcfb8631dee340c1485895472b98afe83ccf028f3b0ea83a212f2de0c8cc
    | 6 => 0xae9b87d732f0a2b7ae132c1f87c82c9ec118ab1c8491346dca33b86e4d5d1cc8b74d4332990ff97d12679a30a427b65fe29e34ef48a80a5381f1f8db442360a3e767bbef8f84a8f852c7c96adaaea37731a409cc2aa679ee07da0a472d26c1389c6cee1d7506070fc87e03937974cac2222ef3832c92e0ced0f68461f3182177
    | 7 => 0x202bf78659dbb28206ab5d5f512502069a8608391be9915e2ca353a89a15577d07bd911fa187a84c5c7642540fb44ad76f1250152daecd9ada2aa05529010e58d282caafef452c821ba855e9353046a90b29d208daee9ab1dabf53da447cd7a8ea9dc225fc200d802394395722e16f9e21c6a12b6eb9906e3bdd97942380d444
    | _ => 0
  fld packed 8 (i % 128)
def count (s : Nat) : Nat := if s = 7 ∨ s = 8 then 1024 else 0

def board : Nat → Nat → List Nat
  | 7, i => checkpointBoard (mask 154) inputs 4 (recipe7 i)
  | 8, i => checkpointBoard (mask 154) inputs 3 (recipe8 i)
  | _, _ => []
def atFinger (table : Nat → Nat) (ws : List Nat) : Option Nat :=
  let h := hk ws
  let i := h % 1024
  if table i == h / 1024 % 254 + 1 then some i else none

def lookup : Nat → List Nat → Option Nat
  | 7, ws => atFinger finger7 ws
  | 8, ws => atFinger finger8 ws
  | _, _ => none
def ck := checkpointCheck 154 scores count board lookup
def panel (s i : Nat) := ck s (board s i)
set_option maxHeartbeats 50000000 in
lemma block7_0 : span (panel 7) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_64 : span (panel 7) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_128 : span (panel 7) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_192 : span (panel 7) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_256 : span (panel 7) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_320 : span (panel 7) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_384 : span (panel 7) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_448 : span (panel 7) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_512 : span (panel 7) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_576 : span (panel 7) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_640 : span (panel 7) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_704 : span (panel 7) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_768 : span (panel 7) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_832 : span (panel 7) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_896 : span (panel 7) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_960 : span (panel 7) 64 960 = true := by decide +kernel
lemma good7 : span (panel 7) 1024 0 = true := (@span_join (panel 7) 512 0 512 (@span_join (panel 7) 256 0 256 (@span_join (panel 7) 128 0 128 (@span_join (panel 7) 64 0 64 block7_0 block7_64) (@span_join (panel 7) 64 128 64 block7_128 block7_192)) (@span_join (panel 7) 128 256 128 (@span_join (panel 7) 64 256 64 block7_256 block7_320) (@span_join (panel 7) 64 384 64 block7_384 block7_448))) (@span_join (panel 7) 256 512 256 (@span_join (panel 7) 128 512 128 (@span_join (panel 7) 64 512 64 block7_512 block7_576) (@span_join (panel 7) 64 640 64 block7_640 block7_704)) (@span_join (panel 7) 128 768 128 (@span_join (panel 7) 64 768 64 block7_768 block7_832) (@span_join (panel 7) 64 896 64 block7_896 block7_960))))
set_option maxHeartbeats 50000000 in
lemma block8_0 : span (panel 8) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_64 : span (panel 8) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_128 : span (panel 8) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_192 : span (panel 8) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_256 : span (panel 8) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_320 : span (panel 8) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_384 : span (panel 8) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_448 : span (panel 8) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_512 : span (panel 8) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_576 : span (panel 8) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_640 : span (panel 8) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_704 : span (panel 8) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_768 : span (panel 8) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_832 : span (panel 8) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_896 : span (panel 8) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_960 : span (panel 8) 64 960 = true := by decide +kernel
lemma good8 : span (panel 8) 1024 0 = true := (@span_join (panel 8) 512 0 512 (@span_join (panel 8) 256 0 256 (@span_join (panel 8) 128 0 128 (@span_join (panel 8) 64 0 64 block8_0 block8_64) (@span_join (panel 8) 64 128 64 block8_128 block8_192)) (@span_join (panel 8) 128 256 128 (@span_join (panel 8) 64 256 64 block8_256 block8_320) (@span_join (panel 8) 64 384 64 block8_384 block8_448))) (@span_join (panel 8) 256 512 256 (@span_join (panel 8) 128 512 128 (@span_join (panel 8) 64 512 64 block8_512 block8_576) (@span_join (panel 8) 64 640 64 block8_640 block8_704)) (@span_join (panel 8) 128 768 128 (@span_join (panel 8) 64 768 64 block8_768 block8_832) (@span_join (panel 8) 64 896 64 block8_896 block8_960))))
theorem closed : ∀ s i, i < count s → ck s (board s i) = true := by
  intro s i hi
  by_cases h7 : s=7
  · subst s
    exact span_ok good7 i (Nat.zero_le _) hi
  by_cases h8 : s=8
  · subst s
    exact span_ok good8 i (Nat.zero_le _) hi
  simp [count,h7,h8] at hi
def rho (ys : List Nat) : List Nat :=
  match fld 0xa1c3269301086009430000c2b222cc10001411c7140c2088 3 (bsr 0xfc4b4dc4f92dd3dff61fed3ff211aca1e747446fe5011aebe0c65e1ee0bec9a5dd5f2d6bd98f9235d6b3f50ed4374c98d2d8af1ecfd00ed3cd66fd69c8b4a9cdc5c11f1dbe262fe8bd9611c6ba26cfbeb6dee1a3ab7077f8a746b738a4ed92aba25f850ca21c1a76a06890169d0dc8ed9bfe408f9a3d9b8f93f46c539100bc9787315ce181ddfa1c7a807146735658f171e68e7f6606a67d62f503dc626c705560bc372c5e96bbfb5d5c0b5a5c2e1b595bf34bc35b35d66658b7e884572aefb653f30f574f30a7ce4e426725445164e537c9eea53440a5903382a54727ac431823b384ef1e3d14911c63350c17d8839c13487c1407fc126d07c8c95c072bcecb 32 (hk ys) 7 0 64) with
  | 1 => vals.map (fun r => fld 0xfe0000000f10000000ed0000000e00000000dc00001b2b30000000ea0000000df003e9f2580030dac54003a5d047002c1aa430036da84069a806430000000120000000114004c25e8d0031618890047e3c7c002ca167800442147584a84ce650000000b6002b800a5002fd8e2d5f07d3a1d002ad681a55031380a0027d36084d0100000 9 r)
  | 2 => vals.map (fun r => fld 0xea0000000df0000001200000001140000000b6000015ca50000000fe0000000f1003e5f458003598654004be608d004318a890031d7e2d5f2743e1d0000000ed0000000e0003a1d2470035560430047a3e7c0042d6478002d1561a55270180a0000000dc0036400b300351b640698c940300042a20758499d42650026d3e084d0000800 9 r)
  | 3 => vals.map (fun r => fld 0xed0000000e00000000fe0000000f10000000dc00001b2b30000001200000001140047e3c7c002ca1678004c25e8d00316188900442147584a84ce650000000ea0000000df003a5d047002c1aa43003e9f2580030dac540036da84069a8064300000000b6002b800a5002ad681a55031380a002fd8e2d5f07d3a1d0027d36084d0100000 9 r)
  | 4 => vals.map (fun r => fld 0x1200000001140000000ea0000000df0000000b6000015ca50000000fe0000000f1004be608d004318a89003e5f4580035986540031d7e2d5f2743e1d0000000ed0000000e00047a3e7c0042d6478003a1d247003556043002d1561a55270180a0000000dc0036400b30042a20758499d426500351b640698c940300026d3e084d0000800 9 r)
  | 5 => vals.map (fun r => fld 0x1200000001140000000ea0000000df0000000b6000015ca50000000ed0000000e00047a3e7c0042d6478003a1d247003556043002d1561a55270180a0000000fe0000000f1004be608d004318a89003e5f4580035986540031d7e2d5f2743e1d0000000dc0036400b30042a20758499d426500351b640698c940300026d3e084d0000800 9 r)
  | 6 => vals.map (fun r => fld 0xed0000000e00000000fe0000000f10000000dc00001b2b30000000ea0000000df003a5d047002c1aa43003e9f2580030dac540036da84069a8064300000001200000001140047e3c7c002ca1678004c25e8d00316188900442147584a84ce650000000b6002b800a5002ad681a55031380a002fd8e2d5f07d3a1d0027d36084d0100000 9 r)
  | _ => []
def B (i : Nat) := mv (mask 154) (fld 0x102f10000502400501e50f23402f31e23106e20e53f53f43101e43506e30403f20e10f30 12 i) inputs
def I (ys : List Nat) := bsr 0xf92dd3dfd4374c98d2d8af1ec8b4a9cdbe262fe8bd9611c6ba26cfbea746b738a25f850ca21c1a76a06890169d0dc8ed9bfe408f93f46c5360bc372c5d5c0b5a5c2e1b595bf34bc35b35d66653f30f5723b384ef1c63350c13487c14072bcecb 32 (hk ys) 5 0 24
def test (i : Nat) := ck 10 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 154 (cutBoard 10 inputs B) (cutCount 10 24) (fun _ => I) (rowOrient 154 rho) scores 11 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 1 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z1 : span test 1 1 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z2 : span test 1 2 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z3 : span test 1 3 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z4 : span test 1 4 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z5 : span test 1 5 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z6 : span test 1 6 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z7 : span test 1 7 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z8 : span test 1 8 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z9 : span test 1 9 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z10 : span test 1 10 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z11 : span test 1 11 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z12 : span test 1 12 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z13 : span test 1 13 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z14 : span test 1 14 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z15 : span test 1 15 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z16 : span test 1 16 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z17 : span test 1 17 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z18 : span test 1 18 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z19 : span test 1 19 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z20 : span test 1 20 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z21 : span test 1 21 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z22 : span test 1 22 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z23 : span test 1 23 = true := by decide +kernel
lemma regionOK : span test 24 0 = true := (@span_join test 12 0 12 (@span_join test 6 0 6 (@span_join test 3 0 3 (@span_join test 1 0 2 z0 (@span_join test 1 1 1 z1 z2)) (@span_join test 1 3 2 z3 (@span_join test 1 4 1 z4 z5))) (@span_join test 3 6 3 (@span_join test 1 6 2 z6 (@span_join test 1 7 1 z7 z8)) (@span_join test 1 9 2 z9 (@span_join test 1 10 1 z10 z11)))) (@span_join test 6 12 6 (@span_join test 3 12 3 (@span_join test 1 12 2 z12 (@span_join test 1 13 1 z13 z14)) (@span_join test 1 15 2 z15 (@span_join test 1 16 1 z16 z17))) (@span_join test 3 18 3 (@span_join test 1 18 2 z18 (@span_join test 1 19 1 z19 z20)) (@span_join test 1 21 2 z21 (@span_join test 1 22 1 z22 z23)))))
theorem finiteCheck : ¬NatRun (mask 154) (goal 154) 11 inputs :=
  symCutRoot (rowOrient_sound rho) roof (fun i hi => checkpointCheck_sound closed (span_ok regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 12 ≤ t := by
  refine proveAtCap 7 154 11 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finiteCheck

end Row27

namespace Row28
def vals : List ℕ := [1, 1, 1, 1, 2, 2, 2, 4, 4, 8, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 16, 16, 18, 18, 18, 18, 20, 20, 20, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 36, 36, 36, 40, 40, 40, 40, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 48, 48, 48, 48, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 64, 64, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 66, 66, 66, 66, 68, 68, 68, 68, 80, 80, 80, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 3, 5, 9, 17, 3, 6, 34, 5, 6, 9, 24, 72, 3, 5, 6, 9, 11, 14, 17, 24, 26, 34, 42, 72, 74, 96, 13, 14, 28, 76, 17, 24, 19, 22, 26, 50, 21, 22, 28, 34, 96, 3, 5, 6, 9, 17, 24, 34, 35, 37, 41, 49, 72, 96, 97, 37, 38, 100, 41, 42, 56, 104, 3, 5, 6, 9, 17, 24, 34, 45, 46, 60, 72, 96, 108, 49, 50, 56, 112, 3, 5, 6, 9, 17, 24, 34, 53, 54, 60, 72, 96, 116, 72, 96, 3, 5, 6, 9, 17, 24, 34, 67, 69, 72, 73, 81, 96, 97, 67, 70, 74, 98, 69, 70, 76, 100, 81, 88, 112, 3, 5, 6, 9, 17, 24, 34, 72, 83, 86, 90, 96, 114, 3, 5, 6, 9, 17, 24, 34, 72, 85, 86, 92, 96, 116]
def inputs : List ℕ := [0x23611b2236cd809b104d899e6c22880b653e000000000fffc0000000007ffe000000000f, 0x48b74505e062814520a29203155e12e6a2e2000fff80f000000000000000000f03fff070, 0x2e0c2061e4083138609c3070418e47804c345fff0000f00000fff87ffc38000703c000180, 0x9504a848831426284bd47828a0897bb71c08000000000000000007fffc0000003ffffe00, 0x2e61730e0041813b0f1182010c0ffa0380811fffffff000000ffff8000000007fc0000000, 0x30818409118205bc0fde07fdf031004c000800000000000000fffffffffffff8000000000, 0x3f01f80ffffc07c008e0044e0020047001001fffffffffffff00000000000000000000000]
def scores : List ℕ := [0x13c290f89b24c94, 0x210771789224496, 0x1dc290309c25caa, 0x1780c1dc9b25093, 0x1780c0a4aa24c9c, 0x1dc5e2109624891, 0x1783e0309624492, 0x13c0c1789c2509b, 0xa40c178aa24497, 0x1dc0c0a49424c9b, 0xf80c0a49724896, 0x1783e1dc9b24493, 0x1783e13caa26c93, 0xa40c13c9b25093, 0x1dc29210aa25897, 0x1783e13caa26c9c]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)
def recipe7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xe20106340000e30b20340000f50661370000e20a60340000e20320105000e51310751000e31710341e20350b20106000e62742342000e31751342000e21a70360000f10b40330000000e42320000e31101264000f50a75351e51a76b60354000e41371741000e51a76363e20360e62373000e31371102500b70664340000e21a50310e30320730a50000e31a71310000e30341105100100e60330000f30641371000101e31331000000e61351000505a76364100100102106e62342103105000000e52340000f20a53373000e21a60370e21a60340106e30330631106000f20b63276500b50743243000e42b21361000100100101000e40a60370e20e76360376000105e32343000000101101000e30350105000100e61351000000e21332000101e51331e30330631105100e20331104000e62320104000f50751251000e10330104e10a50360103000e20350720000e62b20310000e10370101000e40a60330000f41642372e30a50a70320000100e61341000e30370102100e62342106000e32a52321e40b60a75376000e31361b43000e62320761000000e42342000f50752276000e10340104000100103106000f10a42352000e51310a65100e21a71341000e32362103000000100102000e31351106000e30a70320f21502b53374000000000102100e31342103000e31310b43e31101331101000f10b31221100f60661331f20b70710b32000e10330106000f20b50242000e30341101000e31351105000103e65352e10330e65376000e40330106000e40b30252000e10a60340000106e50361000f31b63261000000e10370000101e64342000f20b43254f60f41642382000f43b63263101e31342106000e52a70310000e40340642000e10a50370000e30770341f32b63a75350000e62102265000000e20320e30a50330104e10a70330101000f10242762000e40760370000e10a60370101e31342104000e30330b53000100104106000100e31371000e43354104000f61675352000e54a73343000100e20350000e51370106000e51730370e10350105106000f65671351
    | 1 => 0xe51350000e31101331000e52340104000000000000000e31310102f30f62364275e10370e42372000000e40320000e31106341000501a51310100100101102e31a51a61330000e30350103000e41a61340000101101102500a20a30350e40a60370104000e30730341000103f63275100e40370104f10b40330106000e31342102000e21332104000100e64343101e61310102000e10360101000e20740360000e51710340000104f53276000f50b70265000e21a50370000e31361105500b50a74342000e65b52343000e42320105501a31a51370000e52340106000e40a70320000e40770351e10370e31342f30732b63261e51b30a52353000e52a70320000e32a72320000e54a73332000e40330740100e30370103000102e62342000101101106000e52340105000000e51310000e21332106000e30a50370000100e40320000100e43332000000102103e21332e65376000f61662352000500a30350000e32a52362000e31310330000e40340740e10330104106000e51340751e30341101103000e62320103000000e10360000e10330103000f42b65276000e21332105100e61341106500a20a50370000e32362732000e10370104101103e64343000100e31310000e31a61370000502663353000505a53373000e62104342f30f52b74271f10f31b81286e40351101102000f40742242100500a40370000000f20253000f10502374000e10360105000e40330b64000000102106000e42342105000f21b71271000502b52276100103104106000000e20370000f43650360e40b20b71364000e41371106000e40a60340000e40340b64000e31310b30000e42320743000000102104f20e52264341000101e31310000e30341104f21e52320353f21b51b31332500a20330101000e62320665000f41743253000e51100273e42353e65354000e20a40320f20e40320340000104e65354000f60665353000e40a60320e31a51a61370000e20320106000e10370105000e62742362000e42a72362000e40351103000e42353103000100e40370000e40b30350f10b40b20331
    | 2 => 0xe31a61350000e42320103000e51340105500a10a70330000e30642321e21a50370104000e41a61370000000000106000f21a63340000e51350106000000f52276000e40320106000000e65376000f60673353e20320e40370000101e53364000e20a60320000e40320642000f21b42251100e32102343000000000105000f10b72273000f43b74273101101102106e52340104105e31342102106000f30731250000e32a72362000101101101000e40320105500a20310101f10b32b53253100e64b43374000e54103243000e40100340000f61764275000e21332103f41f32343b73000e65b50342000502a72352000e40730360000e10360104f43b63b73264e31342102104000e50a70330000e40102360000f54661371000f32650370f10b52743253000e31351732100e31310103000e40740360000100e21351e31310330400000e51310106100101e63331100e20a40370000f10b32253000e21a60350100e32343106000e42762353000500a10340e30350e63374000f10b32243000102103106f30e52382353e10340b10100000e30370101500e30350330000000102102000000e31371000501a31321100e32343104100102103104000e21a40310000e10a30350100e43332104000102103104f30b64a75351100e61b51274f10a42332104100e52363106000e42320102000100e51362000102e65376000f21b63276e20350720b50000e10370103e20a40a60320000f62675353000000000101500a30320102000f10b52253000e21a70350000f20253106000e42742372e30b20a31332100e31310104e31a61370105000e20320103100e40370103000e20360105f31e42382354100e20a70350000f30b53250000e20350102000102e54365000e30a60370000000e30370f50f43363b73000e51740340000102104106000000e31331000e31a51361000f52b75265000e42320104000e20370105000103e31342000e42104342e20340e62373000500765276000105f30254f20b70b31362000e42b21352e30350631103e10a70105340e41a61a70340000e40740370
    | 3 => 0xf20721221000e42a62320000e42a72320000e31101265000e30350b53000e62321105000e31771342101101e21332103e63374106000501a31310e21332e43354000e40320b64101f63664341000000e30330000e20100271000e31731361100e64375106000f10b40231f10b40330620e30320330101500a10330100000104e43354f10b60b20351000000e20350e10340e30320000f50661350000f32650350100e21351103e20370b20101000000105106000000e42372000e31b10330000f52105276000f50b70264000000e31361f30731250106000e40360102101101101106000f61675354000e30100330000e31371104000e20360102000e30350631000102e32343000102102103000e52340752000f10242742000102e43332000e31107320500a30a70320000000e31310000e30360102000e10730350000e31731342500a10a70340100100e20331000e42b21341000e51a70330e21a40a60310000e51b70265000e42a62340000500a10330e31a51a71310000f53661371000e30a70360000000101103f10b32b63276000000e31342000e42a72342000e50a70320500a10340106000e20720360100e64341106e20320e43354000f20253104100501a41320100f10b40240000e52104340000102102106000f61275b52f30b53b63b73102103104106000e65105243000000e65351f10e30320242f50e72372275000e10100272000e40a70340e30320730102501a51330104000f52276b60000102102104000e20340720000f20103364000000101106f21b53f63271000100e31342000f30732250000000e63353000101e64375000f61275b50000000000104500a30a40320100e64b40332100e54104365500a10a20350e40a60320103000000101104000f52753275e10370103105000e40320104000000e62321000e40370102000e20107310000f52a76361f32b63661754000f50a75354e30a60320102000e51370102000e20750370000e42102342000e31331106000e30750360000100e61331e31342102102000e30370105f20b42e76361500b70664343
    | 4 => 0xf21b51242e40320642104000f52a76364e30730642362000104105106000100100100000e30320730e30320330e53000100e10321000000103105000f41650360000e42320b41100f60104272000e30a60330000e20a60350000102e53364000100e64364000e30330106000e51350752000e20340102000e31310104102e65105376f20721221105100e40330101000e21a70310f20b50100330e10b40a53354000e61101264e40320b64104000000e65350000e31a51310500a10330103000e20350106000f61662320f21b51b31b62000000e40370000000e51370000f30b53243000e31361106000e40720370e40360102106f20e50370253000e31342103e32a52a72321000101e61351000e20350105000000100101000e42372105102102103106000e20720340000f40741250000f52276b63000f32b43253000e40730340000e10350102000e20760370000f20a43363f10e50340350000104e65351000e30720341100100e63331000e10370106000e63105343000e51310752000500a10370000e42b20361000f20b50341000e31310105100f32b52262000f60764264f30f50353240000e31342106000e10a70360f20e52321252000000101102f64505276362000500a20310000f50754254000e10360b10000f10242732e51103a75352f20b43b75274000101103104000e51710370000102f51262000000e62362000e62321104000e65351106e21b40721231000e31342105000e51340104e30350101b42000e40730351e40330340102f20b50341b63000f10b62263000e40320740000f42650370000f20b63264e10b60651370000000e62352000100e64342000e63353106000e40740351f31754b74672000505a76361f20b50710340000f20105243f30b53250b64f10b31b43b63000000104106000e65b52342000e10a50340000e32a72352000e42372743000000000103000101104106000e21a40360000e30730370000f61662342000e42353104000501a31351f30b54b65261000000104105000e20a40370000f21630350e30100330100e40320104105
    | 5 => 0xe40320101000f50a75376000e30330103000f53661310000104e65350000f61662276f21b71764261f10b31b62753000e42321105100100100106000f65670100000e51370104000e20350103000103105106000e31a71361000101e31351000100101102000e41a61330000e31361103000501662362e10a50a70330000e42b20352000e31351102e41a61a70330102e52102363f20e50330350100501a71310000e30750341000e20740370100f31b54276000502a72320000e10100275000e30a50320000e65350106000e31310103000e10750360000e51107310000f10b31b62000e65b50375e30330105106f20e52264354000e40360101000f65672342000f40743253f10e41381242e51710a76362000e31371732e10a70360104000501b71274000101102103000f21b73275000e20360101000e40370105000101e32343000e20a40360000500a20370000000e42362000000e65354000e51370105000e40100261000e62362104e40330740a50104e65351106000100101103000f10101231000e30320330000106e40370000e10740370e30720341106000e65351764000e62b21361000f50a75353000e42a72321f41642b21361000e20370b20000e42321743100500a70330105e63374106000e65352b64f10b60b40353000f64675353000e31b10360000000e40360000101102106000f20b52242000e41371104000505630370000000e20360000e40351102000000e43354000000103104000e62352762000e43730353000000e54343000e62362106000e10a30370000101102104000000e30360000e31761342000102e52363000e30320b30f10b72102274000e53a73353500b50a74340000f41a65343000000f10242100e40a75352101e52102363000e31361731000e62352106000e20a60370f10b32b73274e21a40a60350100e20370101000000e42321e30b20340a40000e30330104000e10350710000e20100273000e62106342000f10a52372000e50a70350000e40370101000501a51370000000103106e30370e53364500b20b52275000f53a75350
    | 6 => 0xf10b60b20b42000f61275b54000f42650360000e51310100e50b61a75354000e30100265000000e40351000000e42353000e30a50330000e40100276000e31361732000e10a30360000f10104242000e42b21371000e65b51343000e40720351f10b60661763000e40653331000103e65350000f10b72275000e51370103000e31331b43000e20a70360000e50a70340000e32a72321100101102106000e31310732e40370104105000f40651371e10a50360101000e51a70340000100e20370000104e53364000101e53332000000e62342000e10740360500a10a20340000e30720370000f60665354000e10350104000e10a50330000e52a70350000e10a70340000f20253b32e10a30340101103e43100343000105e43354000f20253753f40f21351b74e10a60340102000101e21351000000100100000e10370102000e43103354e31361731743f20b50341102e20b60a75376000e40360104101102103106000f30b64261000000e30320000101e64341000e20360104000e30a60350000e41a61310000000e20340000e65354106100101e43354102e52363105000100e40330101e32343104000e65b54375000f53a75352000100e20320000e54a73330000f10242104102e43a72332100e20350101000f10242102000505a76365100f41b74264000100f54276f20b63103264500f30b53375000e30341102000e10a30340000e51105340000e40330b40f50101a74375000e62352103000e31a61330000000e32362000000000100000f61275106000103104106000e31a51371000e10a60330000e54343106000e43354106000e31371106000000e10350000e30360106000000e65352e43354e65376f50b70a64341000e10100276000101e51351000e30350730000105e30370000f10242106000e30350102000e43354105000103104105000e61351761500a10350100e21a50360102f20b43b65276000e10340710000e62b62275000f40743240000f21a53373e21332e65352000f10242105000f60f41374f10b32b43254000f61675353000e51a76362e20a60370105
    | 7 => 0xf21630360000f21a43363000000e30341000e20350b20000e51310102000e30750370100e20370103000e31751371100101e32321000e62342103f10b51b21242000e42353106000000e65353000f60672321000f61675350000e40351106e42353e65376000f40742250f10e40320340000e62b21341000e10360102100e31a51330e30e53331352000e31a71351000e21332102000e10a70330000e21a60340000e30330631000000e30350000e42353105000e30320104000102e52342e50a70340106000e21a50360000e21a70340000101e61310000f31650370e40720351105f60f31754374000f20102242000e20340104000e20a70320000e10330101000e40330101000100e64340e20350b20b51000103e65354f60e51380265000e20370102000e10a60350000e42320741000f60672352000f20253b31000f60763273000e10340101000100100106000e62342105000f40652321000e31a61310000100e62342100100e63374000f42650340f10b62b76273000f61107360000e30320106e10360e30341000e53a73332000000100103000000e31351000e20340106000100e53364000e51a70350000100e61310000100100103e10a50360106000f61765275000000e62320000e30320105000f60665352100e40370101000f64672320000e30105340000e20340105000000e10330000000e40330000e21b10332000e40360b64e10340710104000f20a53363000e30a70350f20e52382352000f30641361000e21a50340000e10a70350000101e31342000000e40340000000100106000e30a50360000e40351101000100f41275000e21a40370000100e64375e10a30340105000e40a70360000e10350106000e20102360e30341102104000e30730360501a31321b32000000100104000e61351102000e65b52375000e20750360e10a60330105000502a52330000e31a71331103104105106e10330710105100500a20370f20102b52276e43354105106000101e61331000e10350105000f21a73353000505a76362100e10321102000f43650370e10a50330101
    | _ => 0
  fld packed 48 (i % 128)
def finger7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xc8cc477d050aac140b79fc35671dcff1f69577510e555fc235a41b8ccdfaea6f5e39f83b3e6bee5d320b5d442630ec80655acdcdc3a5d96e65e9fd727dfbd5838c2f5782e5aef345f54d2b7089f05d1b7d9b61e305f7508a61010e39b91c1c11689a44c8fa2678ad36fe16b0d41d2a53f56a1cc4c952461394e665066a0c845a
    | 1 => 0x3d6d3609dfcbbf87c6ca0a8b32f4fc84e36f98f2f2c35ac4778fd37eec28f9113372428f1bcdc58a2b4289e1119a6f95e137253d794756576ceb994547806447d9d0e8a8d35bbac7ee1ea2a9e84b307ea293c381be744bc4cf3cc0acba201b8090cc87b34b50583010342af509c27f9aba87f3fb25e27ae71ffa371e26198542
    | 2 => 0x9443df343d359c40afa4444f3b8aee4bd464170e0c55ebb1180ca5b0162484fb0c0d9af5d3cb2bdebc2249ec8fb1b4b578c83cf3b0ee03f433aa511a192211c162d3406d55adb522d3e050f3132ecbb8aecaa62498eca21f10dae9e704e334a2484c307f1af4fa82bd37d065f169817abfd6141f4c06872164ed346313f0ac5
    | 3 => 0xcfec55118c5421ca961026f9d51c5203ab0b200e6860f75d350d3c158a9f6c0d1f8f5f890dbe3d54b365b92334878227a0bc696ab1f1c094e2ee669acbc1e80ad5883f4dc9755112bfce517a45f019bb53ed8465b59d5f1171e2d135f97d6b5aedd6219a3cdf212294fabf8726fa617903595a7587bce8711e6a42609d38cfc6
    | 4 => 0x7a21054e79caf96626bd22e9c7094878a6d768624138aa7ef7675723d29813991c89478d72c21c0dc8042767ec382545ef0f937827966303d50e3f746eefbf4eeabfc04220e86a0ac971890bd0495c3d1682618e6647532294281d339614844dc487925356c7dc7a0840e9979dc79e75c28453e246107250f4063bba5c3ef93a
    | 5 => 0xa254f7d772704bd4dd87d44c3a7a0308fb9b3a2bd0a8a835639395a7fc796ac3895544cc99f284b2c23ce42068ba34a38363a8966654ddbf611d4d5c21fdfafc3b962f573329b98cd56414eb1a54788b4cbf9548f6c860edb6abbce39aaf06dc64f2a328989e5275e0943bf4721522cf93f704bdf48d018fcc9f3419a1de117a
    | 6 => 0xda141627ea6e40487876b65387677bc025b375284da4303a67bac0405ca4eb81a436b9fbb37921424c694ec99ee54be703863b54b9c7529d2f6f22cf2302c78895eada234b082d0b3d51776cda7be4f609ba6d1ecff72949f9331e94ad99799c206c6a49ebaf5b991623d0303b51cc86976335dbb3bc169035c36d95d2099ef9
    | 7 => 0xc4cf59569aac5b06cb931e05226f66fd34116d2d5f71b482324f7b7e5623f9c0f7655799b59b72e9c40373030b8bf831909f269bdd47bf1194f98bc540b5a36dde3a998732a70c1d1f2fbaa0f2fa5d8ebd1cc3cc5cbe09947a45389f081bed406afce7e88199d031a84eaa074b86444745f7d36c544728e04560c696360349f1
    | _ => 0
  fld packed 8 (i % 128)
def recipe8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xf61106000100e32501b31b74f10b60f42000102f65000e20b60000f30106000f64105000102f52000f10502000e20a60e21a40104000e42320000f61105101102504000e30b60000e54765f30732754000e42772f10b42107000000402000101f41000101e21f30732b43100f20743e42a72105000100e53000e61104000e61351100101402400103107f20b63753000f21b63000e31743000f40101000504a43000e32a52f10b42106000101f62000103e31000f61662f10401253500e10321000f31b75000101101000500b10000501a51000e21332500a40a70f20b50b31000e42721000100e42e52a70104000f60675f43104107000103505000f41653100101f31f20104106000104403100e41752000f20b63000000f52000000e32000e51740000500764000e53b64000e52b40000f32b75e32a62105100e20a70000e10b21000f41b64501a41a71000f43b74000000f40000f30101000502104100100f60000000f63000000102000f21105000e20760000501b71100f30103e31a51105000e42720000000e51000e10a30000e51750500b20101100100f32100101403000504107000e42105100e20102000100e50f31b63107000103404e52b63b75e20a70106f21b43b65000f50662000e42a62000500b70f20f42b72000504106e53a73106f61f53376500101102000f21107000502107f61f43375000000f64000e41a71000102e53000100502000000f30000f20b70000100f61000102402f31e42353000e63753f20101103000000f61000101e53000e65b54e31a51106
    | 1 => 0xf63507000e30107000e20b70000000000000101f52f21b43106000f10b41000501a41100e32a72000e32b62000100404000505630e42372f64000100e20000500b60000e51b40f50101101100101404000f64665f60f31375000e20731100f10101101f41b75e42353f42f21b43b75000500a10100e42104e20a60106000100400000402107000f41650000400102000101e63000e10750000501762000f21b71000504730000f10b51000000403e42a72104000101e41500a20101000402106000f64675f60f32375000501763000f20b42f50e75387000000e41000500a50000f40104000f32b43f31b75106500b50102000e41a61000f60763f40101105000f50102e32a52106f30e60371e20b31101000e32102000e51105000f52b76f40101b54000e60103000f31102000f40652000f30731f20b43103f20b63107000500763000000400000000e64000f52676f10b32b63000f20b73000e21a60000106f50000f40107f43b74a74000000e52000500a20000f42b65000e30102000e32106100502104e30341e62000f63106000102106000502a76000e51107000f30105000100f40000f60764000e61b72e50761103000f50754100102104f10b32105000f60761000e20b31000e30770101502a73000f31b65000f40b65000f20631000101401000100f21000f62764000f40505100506b60e42a62107e30360f53000e51a70000f10b72000f21b43e40a60104000f60f21000e51b10f30b54b65000f30107000f64106000e52b63f10b62102000000e30100f42a74f20b70106
    | 2 => 0xf63672000f10b40f10b52106e31a61106000100e60000500662000105e63000000106000f20a73000402104000f62671000103f63000e65376000403105f30731754000f10f63000e10730000f54b76f10b60b71000e50761000000f41000102e64000000e54000f53b76000502661000505730000e63731000f43b75000e10740e41a61105500b20105e21a70103f31103b75000105e30000000406000e30b30000100f32000104e32000f10103000102e42400102107e40a70103000f10b62000504a75000e42762e20f30360402106107000400105501a31b43101e41107000502b76000f43b63000f43b65400102105000502763f20e50361000e52105500a20104000f50751e30102104000403106e30e42353000f51a76100f40103000f40103f30101102000f32754f10101b41000e40103000102102000e41106f21b73764e10a30104000506a20100100404000100403000400107000e64107000e30a60f31104b65100e20770000e65b53500b50741000e10b50000f30b74f20b73106e21a60107000f53661f10e40351000e31b54000000101f21b53f63e42a62104500b70102000400106000e30105000f64673000f60102000e52b10000e50b40e20350f40000f30103000103f64000100f42000102502f42b65105e30102105000e42b21000f10b52000e31a61000f61765f60f41774000502b72f10b32104000100e10000100500000f30641f60f41771000f52664f10b72106000102f43000101f51000100405000402105000e30b20000101402000e54a73f32b63107
    | 3 => 0xe60106000f20102000101f43f60f43375e50e32343000e10a50000e31103000502b62000e63730000104406f43b65b76000e30b50e31351f43000e30330e31a51b54000000f60101102e63e10a60103000e10103100f40b75400102103000401103000000503000e20350000f41107000f41642000e54107000e41771000503632000105106000000f62000f20b53f50101742f50b70264000f41b65f20b52103100504107000e41104f50f32754f40401b86000e10100f32504365000502a62000000f54000e32743f53105b76000f51660000105f30000e65b76000101e51000100503000e20b20000104f32e30a60105100f20b52100e21a51000105406000103e64405e75353000503b53000f32b73000400104000f50101000100501f10b62105000101103e21a60104000f52b72000f64671000e54731000e60102100e20a40000e64b75000f50753000102f51000e20103000501b31000f60671000501760000104f31f10b41754000f51102000f61a75000000e62e31a61105000100e31f50103754000503a53e30a50103500a40a50000e32b52000506a40100e20731f31103b65000101106102503b54000502b32100f31102000f30732000f43650000f21b42000000104000e31b42000000f50000f41743000e51763f30b74105000102f64e21a50752000101e43101f42b76000000e60100f31b73f20b63b76101f32b74e21500282000100e62000000f31000e42b53000e31710000e51770000f65674000102e32100100f21103f64105f20b70672000101406e10330f20
    | 4 => 0xe54b43000e43754000f42651000504a73000f41103000f62104000e30a50100500a40000e40106000103105f10b60a75000e30642000f10a42000504b65f20b50100e31103107100102504000e50b20000104506000000f32000102504000f30b53000e60100000103406000100e21000000f65000f54663000501764e21a50103000e65350f60401775000101e64000f60f41f10b62b76000f62106000e40370000500b40000f53a75000f50661f62e65376000000e43e41104107100f10104000f10101000f30b64000f31105000100101000106400000100e40000101e42000f20b50000101e50f54e75386e31342f41100503107000e53764000f10a62e40103103000e62105000f21b51000f53b73000e42b72000e32b43000f31754100e31a51000105506f20b50341000000e65000102403f10b60102f32754b74000502665000e63774f30103b74000101102000e64103100f10107000e21a70000e40102000e62773501b31107000e10721500e21332f50e32272000000f10000e50a70000e60105000e40a70f10e50320000e20770000000e53000e30760000e62107000f41652000101f65e21a60763000102f42f10b52103000e65750000e52763000e62352e21732a42000f60101000f63674000e31a71000e62106100f21a62000e21103000501102000e51b30000104106000e21732000f50107000505b73000000e40000000103000e21b70000101f61000f41104000e31101504b65b76000f31107f30f61364000e61772100501a41000f50105000102404000100e54
    | 5 => 0xe30e51362000f50106000e20107f10b40641000e43103000e42b20f30101b43500b20b31000101404000100e30000105f53000103403000501b61e60b71101000000f53000e20106000503b63f20f70721e10a70103101e42104f20b53103000f51105000f41a65000f32107000e65b51000000e21000000501000103f54f32b43b64000e42753e30741103000f31505000e30a70000000500000100e63f52754b76000f42b75000100f52000102503000f43a65e21b32a52000f42106000f54b74000103f43000000405100f41104000f50b70000000f20000f60665100f62106100101106f50101102000000e31000500760000e60b71000f43651000102405000e62752500b40105000f10105000e53105000e42742000e43106000e10a60000000e10000f52660000e40b70000000401000e63b74000500765000f61764000e40b20000e62104000502a42e21105a40000f62674000e65107100f10b32f40f21b86000f62675000e20102e65405387000f30a64e40351f40100f21b52000f31a65000500a30000e20360000000e50000e43354000103104000505631000f50103000500660000e53107000e60104100f63104000f51753e10721106500a20a50500b30105000e30b64e50a70106000103e63e21a40103000f10242000101f21000e53106f20721105000100401000f21a63f41102b74000101f64e31a71107000e42321000505a53000e62676000e64b43000f60104000101f53000f21b73000000e20000f40653000e40107000e40653000503105000e60b60000000f51
    | 6 => 0xe40a60000e41b52000501a71000404106f10b31107000e50b30000e40351000e42353000f42103000103f65000505731f61763104f60f42375000f31a75f50f42365f20102b52000502b52000502a32000e20750000104405000f21b62100402105000e21a40000504753f40f31364000101504101101f62000000e63f30103b64000f41b75000501107100e30105f10b72763000102f62000e10105000f63670000f53105000401105000000e61500a30a50000f30642000e51103000500107000501105000502660000e53731e40351403000e21106f21b51103e32743b73100e20b43000100100f32103b65000405107000505a43000500105000f52754000506770000e65776e30a60b64000e30320000e31107f31754b74000e52a70f10b42754000f51662000000505000102f63000e10107000f20106000000f43000401107f20b70101000101403000e21a50000f21b53400e53364e40102b74000f61102e30741b51000e40751000e10106000e41752000f21103000401106e10a60106f50f21363100e43a72f53b73a75000f20a63f10b52b75000e32362000000100000e62b73e62104106f21b73104000e20105000506670e40105107505b73765000e10b30000101f42000f51104000e40104500102102000e50106000e40b30100f63664000105e31000e63732000505663000e51b50000501a21000101405000000404000f10b60e30341f30000f32104000e40b75000e31771000500101000f50752000f42104000f10b31000e53103101101502100501a71000100402
    | 7 => 0xf21106f52b72a75000e30341000503b64000100f43000103f53000e51710e10102103e41a61103000f60107000501103e31b42b43000e65353000e61105000f50b76000f10b42e51103104501b51b75501104105501a71105f30732b63f31754b65000500103e10a70102000e51b62000500761000400103000102e63000e30350e42353105f20102b72f30103b54f60103665000103405500b50742000502a52000f20104000503743000f52b75000e32a72000e43b63000e31104000e30b41f20b43754000100e61000f43104000e60b30000e61107000e10104000e63106000e42a72000401104f50f21b53000f53664f20b53b65100100106000f51b71000e21b50000f51b76000e41b41000e61106000101501f20e40330e51a70103000e10a70000501b21000f40a65000100103000e31351000e21b32000e40760f60e32282000e50104000102f50e10e41341000505107000e30741000503643000e20a70000e30103000f20b43000e63b53e60b71665000101e31000000504f21e52364f41743b64e40a60102000105403f20b50a52000e53a73e42362f54000f43106000f31b63000e32a62000e10340000e50b70f21b53106000e65b50000e31b10f10f60b31100e64375000000502101501b41101501a21e62104676000000f21f52b75a75000f40742000100f30000e31a51000100e43000e41b61e40653105000101e62100101e63000f51103000f53104000404107000000e42000e52b20000101f54e40360f54000f20a43e30400352000503730e10102104500b10102
    | _ => 0
  fld packed 36 (i % 128)
def finger8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xd6d5c0dde47bc673e6227b86729bc4c019c3c015531110da586deedcd389f9038c7fef8121f73eae2ca5fb526853f809d603a510dbb9a17985d1ccccfae8a6af154e0604cc7d289e37675598aa594cc7df663f5a273cc9878ce802b7db1b18a2f13f5519cc2c56e62f4cd963295d98a728ccffe8de3b3ed8160d7e6506b9d72
    | 1 => 0x53a2cb09eac9c0d341ec072aef14f264e5e75bb7893a7f1992bd2bfee314b9137efb4a2fa0c30b89a4c630454e4573ac2e76335c744c62ced940ebb01b7c72d80ce29411f8736dac6cd7c71215b5e416a4fd21e08c4565a08b3ce655bdea9023af4764e452743d4393653efa0b1d580b2d2e2072f063d0885ea04b34a4e50f72
    | 2 => 0x69577999b8d17fc486326afcf3e3d861dc88ce3b23fc829b896de0db2a3ce3149205b76aa9ba5620d06e2eaf31abeb460e63683aa1ecc69dd7f9ad66e42b35c23667c245dc5a0920536731c02994896de6a29afe77d274bc3367ae164b3f47bd77333817afbe69e55cbb67d49ebe14aabee7938aba6c872f53efb72f59b0ed57
    | 3 => 0x45d984dd4802e3c3689154692e1c90bb59358e45eeb4e45ddede3f15eb9f48d1518f0ec39d0b8352a59cf5ddc376eb48a5d09a61bb63fa9392b27a7f27496f710988927b7649133f49aa79f0c573b8dba0b9254d987f24973d2cd0bf29706b2dd85b3eb62bdf4fc80ac352f36629426cf08d823b65205bcc03c73e5044516029
    | 4 => 0xb1afb951fc22c5e341bd644996b5f7a2bbf95064afda6494107d6f71d498c52fd511058dfd681734c6c69c85e78c25333e515002c964578a36b92702051c79fe1451c08691b236c8d354892d819c0fdc82b88bcbde0246f65e8eaad00c0dd7e0b67bfb2a56e662aa2b2837645bec9eb5874666e2e3edf98f62dbcaa61ba3d430
    | 5 => 0x1ea53940e2385a1907d2e3c1f262405512de0b29ae1e7a21e4ece3b8f89636a384127db34954690351b24f5a5e0b19638a31e04c6d4dbb63429cd8b882b6a1bd18903d3e81ea22bc2a4e1c59459631a821747a9240028bedcfabbcc6a58167470d2591cb641cd96d52940b8306f9b4fa24e804281ca8951a4b7a3b2525beb643
    | 6 => 0x8512b8f27cfe4048b4585d3c4b7b4b2501dfd038528ada253ddea8bec284a0ad8643ee301b16112fd10fcfbcec2944c7ddb40d54f21d46eb080a4cc0232c702f6ad23903d33e02f92ac05edaab7fc5aba5ef35ce17989f93e5315994ad400525543efd0a1ae51d4365a8aa019f4f5a4f938a1b3c353cd841b7f3b1bd251069af
    | 7 => 0xf69a591d83edb398d7dbbe4822e9dc43e74596914070ed3a9e57e14e56238a8e653b50744028a6d7d54a5dd6f1da87cef199ab199d927511549f9ed9ea71789393c2f98732cdf44faa0f2bf6be5cc05c9533887ff199a82c14b8bc35db55ec1af2b519cd8099caa686f71dbb16c79828860265a4201ad6d65a6f6b96377197fa
    | _ => 0
  fld packed 8 (i % 128)
def count (s : Nat) : Nat := if s = 7 ∨ s = 8 then 1024 else 0

def board : Nat → Nat → List Nat
  | 7, i => checkpointBoard (mask 145) inputs 4 (recipe7 i)
  | 8, i => checkpointBoard (mask 145) inputs 3 (recipe8 i)
  | _, _ => []
def atFinger (table : Nat → Nat) (ws : List Nat) : Option Nat :=
  let h := hk ws
  let i := h % 1024
  if table i == h / 1024 % 254 + 1 then some i else none

def lookup : Nat → List Nat → Option Nat
  | 7, ws => atFinger finger7 ws
  | 8, ws => atFinger finger8 ws
  | _, _ => none
def ck := checkpointCheck 145 scores count board lookup
def panel (s i : Nat) := ck s (board s i)
set_option maxHeartbeats 50000000 in
lemma block7_0 : span (panel 7) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_64 : span (panel 7) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_128 : span (panel 7) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_192 : span (panel 7) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_256 : span (panel 7) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_320 : span (panel 7) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_384 : span (panel 7) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_448 : span (panel 7) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_512 : span (panel 7) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_576 : span (panel 7) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_640 : span (panel 7) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_704 : span (panel 7) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_768 : span (panel 7) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_832 : span (panel 7) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_896 : span (panel 7) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_960 : span (panel 7) 64 960 = true := by decide +kernel
lemma good7 : span (panel 7) 1024 0 = true := (@span_join (panel 7) 512 0 512 (@span_join (panel 7) 256 0 256 (@span_join (panel 7) 128 0 128 (@span_join (panel 7) 64 0 64 block7_0 block7_64) (@span_join (panel 7) 64 128 64 block7_128 block7_192)) (@span_join (panel 7) 128 256 128 (@span_join (panel 7) 64 256 64 block7_256 block7_320) (@span_join (panel 7) 64 384 64 block7_384 block7_448))) (@span_join (panel 7) 256 512 256 (@span_join (panel 7) 128 512 128 (@span_join (panel 7) 64 512 64 block7_512 block7_576) (@span_join (panel 7) 64 640 64 block7_640 block7_704)) (@span_join (panel 7) 128 768 128 (@span_join (panel 7) 64 768 64 block7_768 block7_832) (@span_join (panel 7) 64 896 64 block7_896 block7_960))))
set_option maxHeartbeats 50000000 in
lemma block8_0 : span (panel 8) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_64 : span (panel 8) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_128 : span (panel 8) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_192 : span (panel 8) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_256 : span (panel 8) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_320 : span (panel 8) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_384 : span (panel 8) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_448 : span (panel 8) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_512 : span (panel 8) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_576 : span (panel 8) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_640 : span (panel 8) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_704 : span (panel 8) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_768 : span (panel 8) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_832 : span (panel 8) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_896 : span (panel 8) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_960 : span (panel 8) 64 960 = true := by decide +kernel
lemma good8 : span (panel 8) 1024 0 = true := (@span_join (panel 8) 512 0 512 (@span_join (panel 8) 256 0 256 (@span_join (panel 8) 128 0 128 (@span_join (panel 8) 64 0 64 block8_0 block8_64) (@span_join (panel 8) 64 128 64 block8_128 block8_192)) (@span_join (panel 8) 128 256 128 (@span_join (panel 8) 64 256 64 block8_256 block8_320) (@span_join (panel 8) 64 384 64 block8_384 block8_448))) (@span_join (panel 8) 256 512 256 (@span_join (panel 8) 128 512 128 (@span_join (panel 8) 64 512 64 block8_512 block8_576) (@span_join (panel 8) 64 640 64 block8_640 block8_704)) (@span_join (panel 8) 128 768 128 (@span_join (panel 8) 64 768 64 block8_768 block8_832) (@span_join (panel 8) 64 896 64 block8_896 block8_960))))
theorem closed : ∀ s i, i < count s → ck s (board s i) = true := by
  intro s i hi
  by_cases h7 : s=7
  · subst s
    exact span_ok good7 i (Nat.zero_le _) hi
  by_cases h8 : s=8
  · subst s
    exact span_ok good8 i (Nat.zero_le _) hi
  simp [count,h7,h8] at hi
def rho (ys : List Nat) : List Nat :=
  match fld 0x66751402adaa695 1 (bsr 0xfc42f9d4f983b625f65fdd8aef12a16bec0068fceb7ae66ce7927403e2dfa6bce2db16bfe26ffb0ddcca50b6dbb0c082d44e0266cc4ddd90c85b11f0c1dfed25bf892aa7be90fde1b9bc5323b8bf2ae5b840280ab5d8ee2bb3adf8d9ab918a6c97bbd4b794566034940775d48b1dbc4189fbe569857f9ccf8332a657802623957e18e57872440c2866b42c306577bede64e28e865fb708ae5f5ac764582d6f9955b81b3d559524404b5745984233e06b3e995e0c3ca6bef13b7161ac39b75ee63691856b3404dacb3142e40e3053a2802852bf39263f2b591ea98f881e2ab19a1d566ad01839463c149a43ab0b8e4e0d0b26fed30646ede901f9f82f01eef95d 32 (hk ys) 7 0 64) with
  | 1 => vals.map (fun r => fld 0xec0036c00ca0000001140000001000000000df003398eaa0000000e80035c00c900361ce4f6b0f984370000000b40029d829700335884b618e852270000001110000000fe0047e3a84002b9ee700044a2077002a5ec6c00419f4747ca70bc5c0000000b2002880096002b56a245586924070029562205083122040026d281e498240000 9 r)
  | _ => []
def B (i : Nat) := mv (mask 145) (fld 0xf54e52f21f41000401e10e20f65e50100f20f10402400506f53e54e41e42f31106e51500e53503f50f52e31e21f51f42104e65504405103 12 i) inputs
def I (ys : List Nat) := bsr 0xfc42f9d4f983b625f65fdd8aef12a16bec0068fce2dfa6bce2db16bfdbb0c082d44e0266bf892aa7b9bc5323b840280ab5d8ee2bb3adf8d997bbd4b7940775d48b1dbc4189fbe569857f9ccf8332a657802623957e18e57872440c286577bede5fb708ae582d6f994b5745983ca6bef139b75ee63404dacb3053a2802852bf391e2ab19a1839463c149a43ab0b26fed301f9f82f 32 (hk ys) 6 0 37
def test (i : Nat) := ck 10 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 145 (cutBoard 10 inputs B) (cutCount 10 37) (fun _ => I) (rowOrient 145 rho) scores 11 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 1 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z1 : span test 1 1 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z2 : span test 1 2 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z3 : span test 1 3 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z4 : span test 1 4 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z5 : span test 1 5 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z6 : span test 1 6 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z7 : span test 1 7 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z8 : span test 1 8 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z9 : span test 1 9 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z10 : span test 1 10 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z11 : span test 1 11 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z12 : span test 1 12 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z13 : span test 1 13 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z14 : span test 1 14 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z15 : span test 1 15 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z16 : span test 1 16 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z17 : span test 1 17 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z18 : span test 1 18 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z19 : span test 1 19 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z20 : span test 1 20 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z21 : span test 1 21 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z22 : span test 1 22 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z23 : span test 1 23 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z24 : span test 1 24 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z25 : span test 1 25 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z26 : span test 1 26 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z27 : span test 1 27 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z28 : span test 1 28 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z29 : span test 1 29 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z30 : span test 1 30 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z31 : span test 1 31 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z32 : span test 1 32 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z33 : span test 1 33 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z34 : span test 1 34 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z35 : span test 1 35 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z36 : span test 1 36 = true := by decide +kernel
lemma regionOK : span test 37 0 = true := (@span_join test 18 0 19 (@span_join test 9 0 9 (@span_join test 4 0 5 (@span_join test 2 0 2 (@span_join test 1 0 1 z0 z1) (@span_join test 1 2 1 z2 z3)) (@span_join test 2 4 3 (@span_join test 1 4 1 z4 z5) (@span_join test 1 6 2 z6 (@span_join test 1 7 1 z7 z8)))) (@span_join test 4 9 5 (@span_join test 2 9 2 (@span_join test 1 9 1 z9 z10) (@span_join test 1 11 1 z11 z12)) (@span_join test 2 13 3 (@span_join test 1 13 1 z13 z14) (@span_join test 1 15 2 z15 (@span_join test 1 16 1 z16 z17))))) (@span_join test 9 18 10 (@span_join test 4 18 5 (@span_join test 2 18 2 (@span_join test 1 18 1 z18 z19) (@span_join test 1 20 1 z20 z21)) (@span_join test 2 22 3 (@span_join test 1 22 1 z22 z23) (@span_join test 1 24 2 z24 (@span_join test 1 25 1 z25 z26)))) (@span_join test 5 27 5 (@span_join test 2 27 3 (@span_join test 1 27 1 z27 z28) (@span_join test 1 29 2 z29 (@span_join test 1 30 1 z30 z31))) (@span_join test 2 32 3 (@span_join test 1 32 1 z32 z33) (@span_join test 1 34 2 z34 (@span_join test 1 35 1 z35 z36))))))
theorem finiteCheck : ¬NatRun (mask 145) (goal 145) 11 inputs :=
  symCutRoot (rowOrient_sound rho) roof (fun i hi => checkpointCheck_sound closed (span_ok regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 12 ≤ t := by
  refine proveAtCap 7 145 11 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finiteCheck

end Row28

namespace Row29
def vals : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 4, 8, 8, 10, 10, 10, 10, 12, 12, 12, 12, 16, 16, 17, 17, 17, 17, 20, 20, 20, 20, 24, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 32, 33, 33, 33, 33, 34, 34, 34, 34, 40, 40, 40, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 64, 64, 64, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 3, 5, 9, 3, 6, 18, 5, 6, 36, 9, 72, 11, 14, 26, 74, 13, 14, 44, 76, 18, 80, 19, 21, 25, 81, 21, 22, 52, 84, 25, 26, 88, 3, 5, 6, 9, 18, 29, 30, 36, 60, 72, 80, 92, 96, 36, 96, 35, 37, 41, 97, 35, 38, 50, 98, 41, 44, 104, 3, 5, 6, 9, 18, 36, 43, 46, 58, 72, 80, 96, 106, 50, 52, 112, 3, 5, 6, 9, 18, 36, 51, 53, 57, 72, 80, 96, 113, 3, 5, 6, 9, 18, 36, 57, 58, 60, 72, 80, 96, 120, 72, 80, 96, 3, 5, 6, 9, 18, 36, 67, 69, 72, 73, 80, 81, 96, 97, 3, 5, 6, 9, 18, 36, 67, 70, 72, 74, 80, 82, 96, 98, 3, 5, 6, 9, 18, 36, 69, 70, 72, 76, 80, 84, 96, 100]
def inputs : List ℕ := [0x4b012eacb004b8e5802591f005647c1149e0000001fff80007ffc000007800001e00007, 0x95ab54055009502a98ea8f100aa8852f1720007ffe000000000007ffc78000000007838, 0x2ae602980a60126053205322253cc3c8f23a5fff8000000000000000000001fff1e0781c0, 0x3080c2030833c818409e470416d1c10ffc0800000000000fff80007fff801fffe007fe00, 0xc103040c1055d0ae872880401ae1fff0404000000000000fffffff8000001ffffff80000, 0x3020c08302099e0cf07cf07ffe3001004020000000000000fffffffffffffe00000000000, 0x3fc0ff03fc0fe00f004f00488bc0122288801fffffffffff0000000000000000000000000]
def scores : List ℕ := [0x1d46720c9524891, 0x1d4570e8bd258a5, 0x1282015c9924c92, 0x19c20128a524c9b, 0x20c3a1d4bd25499, 0x1d44a19ca524496, 0x20c3a1289925895, 0x19c20128bd24c9b, 0x19c4a080a5264bd, 0x1283a15c9624c91, 0x128200e89524492, 0x20c3a19c9224495, 0x15c3a20ca525496]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
def recipe7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xf30b70720360000e10321104e41352e32343000f10b72272e20b70b52364100f30b74274000e40320104000e54342105000e41310103000100100106000000e51330000000e65351e20a60370b52000f64107360000f50661330000103e54365000e54a74342000e40370101000e31370104000e20a70350000e40351106000f10a52332100100e31342000f42a72321000e31310a63f43a73332b64000e20106350000e40360101000e20a73363000000101101000f10b40240000000e65354f51b71a72275e40351e53364000105e40351000e20a70360500a10340106000e40106350000f41650370000e32343105f10b62b76272000e20340101e10321104105000501a41351000e21a40360000e20a60350000e10a30370000e40370103000501b76275e41310103104000e43a63330000e51330105000505a76361000e21360106000100e64342000f10b31230e40320340e51000e40360103100500a30310000e10740360000e65b52342000e10350102f40103b74274000e43332b43000000102102000e10730321000100e31331000e30100275000e40320101000000000101000f51b76273000e32a70310000504a65375000e41361103e41310f40b75000502a72332000103e52363e32a60a70350501a41310106000e63353104101e41352106101e54104365000e54b40332000e20a50370000e54340754000e10a40360e20a60350105000e10340b10000e40730351000f41743251000501b71272e10a40370102000f60107330000f51664340f41104b75273100504a75352000f21a72342f30f70b53374100e21a70350000f61673330f10b51b61263000000e10350f40652a62363000e32343106000000000103000102102103000100e62352000e41a61340000e41352103000f53a76361000000101104000f51664374100502a72332000e50a70340e31350731b53000000e62342000e65351106000e21a70310000e20320b52e20b40a63364000e10100310000e10360102000100e43330000e20350101000101e54342000f10b50340000101e61351000e10100276
    | 1 => 0xe53364105000000e54374100e10a30350500a20a50340000102e54365500a40370102000104e65350e20350b52106100e32a52320e41310340403000104e42353000501a31310000f30641330000503a73353f21a72362b62000101102102000e40100276e10b50f71374e20320720106e32343e65353f40f32352b63000e10370101000100101101000f41b75273f60f31b53374000e10a70340000e43332102000000100100000100e54341000103e43331000f30a73331100e30350102e31a50330103000e20320105000e41341104000e10321106000e21360102000e32a70350000000e40351000e51330751000e40320106000e31310103000e54a74341000f43651331e40351102104000e20370101000e31a74364000101e51331000e10750370e10350310e21e41b41a63364000e10370103f21a72362b42e40320e53364100f10a71331000f40b75272101102102103000e21360721000e31350106000500a10340000f51a75354000e10330104000000100102000103e64342000e63b32362000e40100262000e43332104000e10a70330000f30b63253e40370e32343000e31a50360000e10330710000e62321104000e30a70360e10330101102000e20370103000000e21360e10360f61764000e54104241000f20631360e21360e41352f21a72320b42e40320740103e32a50a60310000e40351105000f50753253e20320b32b62e10a70360103e20a50360104e10321102103000e63332b62e41310340502f21b53250106000e50340750000000e54342000e53b70353f40b75272105000e10a60340100e30a70320000102e64341500a10340104000f43a73330000e31350731000101e41352500a20310b21e40370101101000100e43363100e21b70321000100e62321f20e51310350100e10350103000e42a72321100500a30370000e32100332100e61331104000e40100340101e65376106f51e75354374f10b40240102000102e64343101102102106000e31310100e10a40a60370000e31100274e31e52321351000f53b73274000000e32343000f30a73353
    | 2 => 0xf52a76364000000e62321000e63331104f30a73331b42000e41341105000e40330106000e41371104000e62320104000e20107310100503a54342000e21a50360e20320720b32000e20a50360500b40b74271000e20a60370100e10350710000e30a70350000102e32362000e10321102000e54b41331000503a73332000e54343105f21b71a72273000e52a70320000e53a70320000e20350b52000e10330105e10b21a51361000504b75275000e50340106000e21a40370000000104106101e21332103e20a50320103000100e10350f51104a75350000e40360b40000e31730360500a20370102000e41a71310000f32b52252000e20320720000e30360104000e41741371000e53364104000e42a62320000f64275b52000e41341741000e41310b40000106e40351000e40340104000100e54365000100e43331000e20350b32000e31760370000e51a70340000e10350b10000f42a72362000000e10321000f50752252000e31750360100100e30341000e20360101000000e40320000e62b21351000100f65272f60e32370332f10b62a75353000e41341106000e31350732000000e31370000e31a50310000104105106000106e10350000f42b74272000e20320101000000e31350000103e53364000e65105254e31330f61273000000e54340000e40b20350000f32b53252000e63b30352000100e21332000e31370b53000f21b73273e54343f63275000e30a70330000102e43373000e10330106000e31350b53000f21b42232100e43331104000f40741241000e31370b31000100e40320000100e64340e10321101102000e10321105000e43332106e31b64654374e31350f61273000e65b51341000e40320105000105f41253000e62321106e20370f62107e10a40a60350100f31a71310e31730a74343000101e62352101e31331104000e20350104000e40770351000f21b53250000e31370105000100e64343000e41361b41000e62342103000000e20320000e54340105000f43a73331000e50340104000e40760351000104f64273000e40351102500a20330100
    | 3 => 0x100e61310104f10b72272103000100e53364000e50a70320000000e41331000e10770321000f51b71274000e40360104000e41731352000000102103000e54b40330000e10730340000e50340102000e10a30360000f64765275000f51664342000100e20320100100e63331000102e64340000e31a50370000e30a50370000e30a50330000e32343103000000e40330000e54a76363500a20350100100e30330106000101101101000000e63353000103e64343100103104106000e63331106000e40340103000000e63330e10340b10b20000506a50340000e62320106000101e62362100e30320103000100e20340100f21b42241000f60675353000f64275b53100e20370b42000e10a30340000e41331105000f53664342100101e32372500a10320106000000000104000e54a74343000e41341102000000e50340000e43103262000e51a70330000f41b61263e40320340403000f10b62264000000e65350e10350102102000e20a40350e20320103103000f64275106e10730321103000e10350101f10b50b20342000e20104360000000101102000102e43332000e40330105000f61273104000f42651361000e62362b62000e53364106000e63330105501a41a51330000e30360106e20320a62104000f10b50241000e41101265100e20340104000e40a70320f10b40a73353000e21a50310000e10740321e10a30340105f32b64654374000100e43373000e54340a65000e43a63370000101e51362000000e41341000f43b75275000e50340105000e53a70330000000104105000f10b51250000f61673363f30732b52b63000e10350103e20a50360102100100101101f10b31a72362f10b62264105000505a76360f20f71b52374000e62362104000f40652342000000e54343000e41331106e31310b53b64000f21b52b74000104e43363000000e10330e31310b53643100e50100360500b30a72320000f32a74364000f61273753000102103106000106e20331100e20320106000e65352b64000000e43332000e10360101e54374f65107000e54a76362f21b63b76273
    | 4 => 0xf21b71271000e20320a62000e42342b42100e30320104000f60672362101e21a70340000e40351101000000100103000e20a70320000e53100353000500a50330000f21a72362000e10a60330000104e65352000f50a75353000e20a70340e10750370101e41361102106000e41371102000000000105e21a60a70350e50b61a75353000f21a72352000e41352105e10330101103000100100101e53364506210000000e20350000e21a70360e10330f61764000000e62362000106e10321000e10a60350000e53a70350500a30350106000e54341754000e40351103e20370b20104e30360730101000501a21350000f21a72320000000e62352500a40330106000000102106e40370e53364000102f63274e20320b52643e40351101104e10321e65353000100e30330000e40740370f10b50b20341100e42a70320000100103104000000e63331000f52654341000102e42353000101e43331000000e41371000000e62320000e40740360000e31a60350000e31350a63000f64675353000e65b51343000e10730370000100e43332000f32b64276000f32a74340000e41a71341000103f50262000500a10320100e30320106000e20350105000e21360103000e20370b52104e54104364000e50a70350000f54660340000e21a70340100e64341b63000e21a70350000e10350310000000000106000102104106000000f64275000102e62362000e41352106100e62320103000101e21332100e30330104000100f65274000103e43332000e62752362000e40100265000e41a61370000000e53364e54340a65b53000e30a50320000000e30360000e62320105000501a51320000000e40340000e20370b32000e41371105000f53654341000e40a70360000f60272104e30a50370102000e40730360101e53364106000e43a73332000e43a73331000e20a73343000e42a72342000f42650370000102e62342000100103106e50a70350105000f30a73363000e52a70310000f50b70274000101e64343000e31710330000000105106000e40370104000f32b72272e10321103103
    | 5 => 0xf32b73272000100101106000e41371106000e31a70350000000e10340f10b40b20331000103e51362000e50a70330e10340e41352000f42a72332000000e41310f40e41371341000000e52363000e54341106000e41b10351100100e32320000e30106350500a30350101000f53a76362000e43a63310e32a50a60370000e31a60330000e21a40350000101e53364100e20a50340000e31310106e40b51a64342e41341f41b75f60f21b52374000103103106000e21a40310000000f60272100e10350102e31310e53364000e21a50370000e41361102e10350310e52000104e43354000e20340102000104e65353000e10730360000000100106100e10a70330000f20b70271000501a31340000e32b50332000e65352105000e20360104000e10750321000000e40370100e30341106000e41310105000f30641370100e62320104000100e42353100e53103364000e10321103000500a30350000101e64364000000e40360000500a40330000e40320103000f60272752100f42643330000f40b75275000e63753363000000000102f51b71743363000e31370103000e31310731000e41352102500a20a72332000e10340103e10760321102000e31350103000000e41361000e20350720000f60272105000000e20340e20340102104000e43a73330e30a70320102000e42a62370f20e50330103000e41761352000000e31360e10360104106000100104106e32343104a40000e51a70350000f43a73332000e32a70320000101e43373000f10b50250000e41310740000100101102e20a60340104e10321103104000e40a70330000104e54365100f63764274000e20a50340000e42a62340e20a70340102100e61341106100e20a40370000000000000000000102104000e20100275000e10340106000000e41352e41352102104000e20a40370000e10760321000100e62342000e41310106f30b64b76272000e52363106000e41a71361000e20340105000f21630350000e30a70320f21b42b52b63000f61675352e40351102102f30b63654340000101e65376000000f61273
    | 6 => 0x104505a76361000f32641360000e41331103000e31310102e10a40330106100e64341106e20370e31343000102102102000f21630340000505a76363000e10360106e10a30360103000e32a70360000e10370102f42e64340365000000e63363e41341741b51000000101103101101102103000e54341103000e20a60340000e40330103000500a40350e20a40350101000000100101000e42a62310000101e64340000e31a60370100e30341101e40320340e54e31a60310102000000e54341f43e64341365000e30a50360000e31a50330500b70271104000e31310732000e20370102000100e62362f10b31b42b64100e31a51370101e42353106000f40b60263000000e31310000f50b76272000f40a65343e32343104106000000103103000100e20350000e20740370100100e32372e40a60340106e20320e40351000000e10370000501a41331000e41a61330000103e64340000f50a75351000e63331762000e31a70330100e31a51330000f10b72273e10350101102e10100310103000000000100000100101103e10350710b20000e20a40360000100e30341e20320e62373000000e65352000f51753253000e63b32352000e65353106000e40103360000103e50361000e20360106000000e20370500a20340101500a30a70310e30a60a70330f51a75353b64000e50100273000e40a60370000e40320740000100f60272000101e32321100501a71331000104e40351000e10a70360e10b21a61330000f32640360000e10340102000103103104000106e50361000102e52363000e63b31362000e65105243000e41310102000e10370105100101e61310500a20a70330e31350732b53000e31a70360000e21a50340000000100104000f43b63254000e41b10360000e10730350100e30341104100f20b70271000e10330103101e43332104e31310102106000e54374b54504a65351a65000e62106352000e54b42373000500a20340e10350310404e50340101106000100e61351000101103106000e20370105100e42a70340000e63363106100f60272104000e62320761
    | 7 => 0xf60272102000e53a70310500b50b75271000e10a40370000101e61341000100102102e20a70320103000e10a70350000e65354106f21a72342105000e10b50310000101101106000e41a71331e20370b32b53000e10350105500b50a74340000500a10370000000103104000e20320b32000e51a70310000f52654374000e32b70332000000e63332f43a73363b64f40742250a62000e20350103000f53654340f50505a86365000100e64341000f40651371e10a60350103100e64342106f10b31230106000000e10360100f40742242000e20a50320000e20350a62000504a65352f10b50340105000e62352103000500a20370000102102106500e40320340e10321e65351000e54341a65000e31750370e10330e50320000f41b75275000101f63274000e40330740000e42a72320000000101106000503a73331e32b43a73331000103f53264e40b51643332000e41371103000e62320103000f10a32360000101e42353e10321101101100e20a70350000e30360101000e63332105100f32b52243e10a30350101000f51660340500a10350103000e62b20341000e32343104000f53654374000e20740360100e43373b43f21e41310343000e40a60340000f60272742000e20a40320e31b30a62363000e10350106000f52b72274000f60672321000000103106102102103106000103f63274f50b70100273e41352103106e20a40a50370000104e65351000106e10370101f21b71271000500a10330e10350e53364000101104106000100e51362000f51a75352000501a41321000000e65353000e30360103000100e41352000000e20360000e10321101000e31103360f10b50340106000000e42342e10a30360101000101101102000f42b62254100500a20310000e20a60320000e62362105000f30b74272e10370f60272e10a70350106101e21332102f30641b62353000e62352104000e43a63320f10f50351250e40351e31330000e40330101100e10a40370e21a50a60370000103104106000e40720351000101e62320000e41310340000e40a60320000e63332106
    | _ => 0
  fld packed 48 (i % 128)
def finger7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x694852a30c20b5eb1b0629dba4c4bb5861079cd7f4163dcd65ce7764152eca0c842d2ee0c5f23daab6a0610d66155a0dea34f342f4e2c39fb86a0d3fe8ef82393627f59948c54fcb111301b482d771eb95e69cb8d9f42e48e6276e563be672dccfddd38d228889efcd4fd9f88ea7de34d8c7774d3b335ee7238f835eaf6cbed2
    | 1 => 0xaffe45f269eae0bad2cce1e51abe2c9e2b1b61a8aaeb15610974a5a4646870f015ba7d95ebfa943404ebac4418e269cfac7c4cf13f3baee5b708f067170baccf0918b95474cf5abccf9f7be884b9193945466708af655d8616af57106364d236feb43044806bbc37f96e5be5f3de764293b5454b2fa43373fc84501ab9339136
    | 2 => 0xabe7f3085b8081931748b1703c4e7e598679e6dda9d67d8c85a117ba3ae577960cc63eb0aa5c96132031959b05567a591f70a90b1181131b01037d81816a4a42d0ecf26ca3f89079229653690ec58c82005540870ae2610c26756b593ca257108bab750086b3bdfbd531e79f1ace1b8ed66d405a4e98baba139fb61334ffb7f
    | 3 => 0xb669e46b6d5bd3b62e80bb0fb7ec21f8fe8136240f4c6f58b985a9f234d071cac9dabad164f55f713319c58de88656463519cad350fc683c05e1cdb58b78f0eb465b5f8beb73c057c0fbf3b866781ce48a5d5eef4e03a5dd330a616c6c6956342c56af4e6a7d49fce8f5128684cb754aa7f621894f5cfde0975e36a8e465e060
    | 4 => 0xb365266523ba54f657bb2f81911df96a6c155c212c1ff7e0c76a529d0f89fd531835455c5ae9c842887536cdddf9336d144b37ae35136c6b0690f30694b9d03bde1e63ee4e3fe7d5acb84adebb533dcb1543a266e69289275e4f6421986ce6dd9d7128081fe5f59c109f7caf76f51a8e0162933a9b586cfb3d4ec83f7f59f30e
    | 5 => 0xbaac352c1f1fd7f8de5b54877803156ff74e8bd8079a75f29a865f18133f459c29bba6b3aae34af41745ac51504e9af8b446086db6647c60fbe5d2a3d46ab97ebb256f314f5230413ebd564cfdb7e1635021bda70f8c9860dbeda45bbc148d5fb916c635fee1f2d1b20308883f7dc7491b5613b201d6cdfab3b8dce1c11ff3af
    | 6 => 0x879338d3a490d460cfc85b2f3931ef793d759bba61e84494e058d1f0ff994a153234e96d38a82e49cbbdb26574901dd6dfc9b6f2e2c2a3093f0e968d1cb0c33e567fe71a6960cf84143cbea4523e5973d7fa0baa08e66bbfcbf573c86f8e3f25f1dbb47b2495ecb40fec29877bf76bc5bed96c7bbc97e916cde373e1659a737
    | 7 => 0xb60f36ec33bc1d2069e7b38d50bda0cf0de51b27c50715b326631d29e961dc22fc27d90761e2843b04937f77b61468405056562632647935b9ca235b59aac42ea15ba1194aa1f9c07581117d4148e53b122cac580ceb0eed90b1fc1e3fc9152be3cc57e5f012c915aa405ebc2ed2f2c27e2dcf14df28ac18851a45319881fa73
    | _ => 0
  fld packed 8 (i % 128)
def recipe8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x100f30b74101f42b75000100f40000e62b20501b21b52405e75353000103e52100e41b52000e20b60000506a30000e51330000e65351000f21f75000f53b75000102e54000f10107000e32105000f53654500b20b32100101f62000e31b10f30b64107000f20503f32b73a73e20a60107f31105107e21732b62000e10b21000500760000000404000100502000e65354000e40b20000e41b52f21b63103100f31a71000000500000e20b63100e64775e21a40106000f31b53000101f61000e31710000500a50000e31a70000f21502000e21760000e64775000500b20e40a60105e32a60a70000f50506000f51a75100f30107000502665e40b51641e20a50105f10b62104e60b20b52000e63774f31b64104000f50b76000e52b10000100e20000f41653000e20b43f20b43b64501b21b32000500660000000101000404106000f30731000f20a73000f54660000e60b60000e40760000100e60000e40103000f41102000501760f20101b41000e10a70000f10b52000e20b50e30741103000501a76000f54106000e62b73000500761000f40742000f43104100e64107000e62b52e60771102000e32b43000101e54e21e43354000e63763000f51663000f41a65000f32b64000100404500a10a50000f64672000000103e31a50103100101e61f50105b76000100f10000505664000101f43000102e64000f41505f10b62754f30732105000e62342000f51a76000000e40000000f41000505a54000e64741000f30105000e52105000e63b74000e30741f10b50340000e30b50000100401
    | 1 => 0xf10b32b53000e61b31000f50753f31102104000101401100e63774000101405000f32b53e10721b61000502760000f30102000502a52000f61104000103404000000f43000104f65000e20107100e62773000f60101000101504000f21104f30b54b65e20340f30000401105000f43b63000e42105000500a60000100100000f52663000f10a52501a31a50000f21a72101102e32000000f10100f61102000e10102100f30101f50b70743000f30732000f30b64500b10b41000501103000e20a60000f31105f30731b53000e32107000100f50f42b62b74000f30104000502660000000f30000000e52100e21b32000f60103000103504000f43106000105e41000e60b71100f21b53501a51105000f30b63000501660000e60107000104506f60101104e31a60104000106f20000e10750000f31a74100101e63000e32a60101e31a71e20a70105000e54b43000f61675f32b52b75000100f30f40653a63e10330e54000f10106000500a40f41104b65000f54663f21b63b76f21b42b52000e63732000e31a74f21b71a72100100f30000e43a73e20a50107000f52b75000e52106000500663000500664000f52654000e30105101f41b75000e62721e40a70107000f21103000105f54000e62762000f41743000e42b53000101f62f20101b42000f40651000f62507000100e64000e20105e10104105e32a50a70000e62752e21a40743000e65b52000502b62000102403f40104b75000f43107000f32641000f60f51000f51505000f65673000500102f21104107000e21a40000e10760
    | 2 => 0x500a20a50000e62321000f42b74000f10a72000f50104000f41b65100f20104000501b51000f32b74000100e41000f32105000f42104000506a50000f40f71f21b42b54000506a20000f21503e21a50104100f32105000e51b62000000e30000103e64000403105000f30b54000e21105000f41652f54b74a75000102f65000502a32000e54742000e43b32000104106000f53104000f32b54000100f51f10b72105000e51a70e20a70106101e41752000000e20000e60103000f61106000f51103000103f50100100e31000f63507000400102000f40b75000e54107000f65106f30a73b74000100e52000100e53000f20101f42b65107e40351e53501a31732000401107000e10321000e42107000f50754000e32743000105f64000e52b20000101f63f10b50651000e30106000502b76000000e32f20721104000103405000f32a74f31102b53000e51b30f10b62102f30f21343000400104000f31107501a31b53100502a42000000e60000501a71f60f41375000e50104100e10a30e30a60a70000104406000e51730000f20104000f32b52e30103107000103f65000101501f41103107000103f63e31742b62000f20631000106400000e31104f10b72106f61102103000e40a60000102f32000103503e20103107101f63104000101404000e53b20000f41f74000e32106500103103f10b32b63000f31b64000e20a50000f10b62000100403000e61104000e40a70501b71763100e43b73000e20320000f10103000100405000f32a64000e52100000106f50000e60106000502103
    | 3 => 0x100f40102f61e65376000f53105e42a62763000500101000f10b40000e10100e50a70106000106f10000102103000000406000f40741f50104a75f10104107e21360f51000e40751000f10b32100e31107f21102b42100e21732000f21b73f21a72f75100100f62000e40330000f61102f43104b75000503b63000103403000e64b75f50101b75000104f54000501a61000f40107000f50b70000500103000401103000f40b65000504a75000f50107000f21a43000f30f75500a50103000502a42000500a70000f32107000f42107000e32a50000101f50000101e65000000104000504743000e30100000e50340000e21107e30e63374100106400000403107f10b32106000f21b53f20b43b74000f31102000f43a75f30103b73e10a40105000000f61e51a70762000e32a70000000f65000f40a65000e53764000102e51000000e54000f42b65e20e63374f51753b75000000401000f52b72f40b65105502e72383e53364f50000f10b42000f54b74000000e42502a42105000e41752000e40102000e43b63e32a50106000e20731000f31b71000504b65000e41341e20f70283000105f42000f42650000f30a64502b32b73100501a41f32103b53100102403000000f31100103f64500a20107000e50b30000f32b72000f61105e31370f63e32a70106000e30103000101e53000f52104f30102b43000e54106000505b76000101e64000e40104000f41103100f10a71000e62773f30103104000000506000401106000f10b72000e42106000e20a70f21b73106000f40104000e20103
    | 4 => 0xf20b43b53000e41a71000e64106000e50761000104505000e54741f30101721000100103000000e43e30a60106000f40102f60103763000503b43000f30101000000f54000e10105100f10b42f21b43106f21b63107000000105000f21b62000f50102000100f60000502b42000101e50000100f64102e42104000502b32000e51b40000100e43000e10721000f10104000e20760000100400000102402000500765000e21103f30103b53500b10b31000000f52000100e31000f53661e41a71106000102106000f21b52f51752107000e20b40000f52660000f21b42000102f42000000f40000e61b41000e31730100103104000e43106000e32b20500e32343000e21732000100f20000e62742000f20b73000000f50100f21b71000000f42f20b70b52f40f61365000e53105000000f32000e50b61000f60506100e43105f51104b76101e31b42000e60b20000000403000e31750000000e21000f60673000100506000e54a76000e65b76000503664000f41b61000000106000504742000f63104000e40b70101f32107000e20a40000000f53500b50103000106e40000e41761000f40653000e50a70000f61673000e53364e10a40107000102406000e21b50000e51b50f20b73105000f50105e40751103f10b32102100e40b51000500a30f20721b53000f32106000f42106000f42653104506a50f21b63104f30b70764f53104b76000505643102e63b74000e21106000e43107000501b61000403106000e31b30000503761000000e41000f54107000101403e10340f31f10b62b76
    | 5 => 0xf51b76000f52b76000f32b73000f54a76000e31b50000e53b64f32103b73000100f65000e63b31e10103107000e41310000f50505000e52363000500b40000000f63000f20b53101e43107e51b62103000402107000500b50000501107000100f31f40b65b76f50101743000f53b73000100f21000400105000102f53000e41101100e63107f30e73384000f31b74000100402000f20105000100e10000e65750000f21b63000e20104000f53b76400102103f40103b74000100106f52105b76000f51754000504b75100f30b50102103404000100f42000e20a73000e10107e61b72104500a20a30f21b43b64f10b51107100e42353000f63105f20b53106f30b53b74f50103743000e40360f10f61b82000e61105e10e64375400e52352f21102b32f30e32343000000102000e41b31000f51752000f50a75000401f75e32743a63000502104e52363f50000e40720000e41361e20a50102000f43b75000000f62000e61b51e10a40103000100e30000f10a62100100402000e42742000f50751000104405000f20b63f21b71b32000000e64000e10b70000f31640000106e10000f21105000e40b51100101102000e30a60e10330f20000f61674e40a60104000e53107500e40351000102f43000f10a32000f21b43000101f32000000000000102104000f10b31000506a40000e41352e20a50104000402105000e21a60000501104e40a70104000e60100000503765000f51753000f62105000e10a40100400102500b40b54f43b75105000e54b41000e60771000e51105000502b52
    | 6 => 0xe65107000000502e54a76b64000f20106f10b42b74f30f52b72000e51100100101e62000103406f50104b76000f10b50000f43b65f30b74104e30a50107000f64105000000405000e10a60000101103000f31b54f41b75106400103107000f51107000000f21501b31101000100101000f64765501b21b42000501b71e31b64105e10a70105e10a30103000e61106000e10103401103103000101e43000101f64000100f61f20b43107000f20103000e40730000e21100000000402000502105000000501000e61772000101e31e43332404000100e63f32b64104100103404e10a60730100f10104f10b32b43000e10370000503107000000e51000000505e10a60106f42a72b75000505740000400107000f41104000f20b70000f21106000000100000103f64000f20a53000e31a60502a42a72000103e43000e10a30000e30b70000000e10000401104f30f51353000f64a75000f10b51000e20370000f64106f53b73675000e42104f40742b74000402106000102e42000501105e21a40a50000f21a63100e30a70e32400354000104e42e21a50105101e31105e20a70102e31a50105f60f42375000e61107000f60105000105404000f31103000100e32000100f43000e63106000102f62000f54662501b31105000100104000502107000e42a62000e42a72000f60761000e21b10e10a30106e30a50105000e10106f30101b43000f51104000e30102f10b51106000103506f20721b52000405107000e43754000f52664000000e53e10a40a60000100f41000e31742000f21107
    | 7 => 0xf43a65000100500000101f41100100e20000f51102000506770000503a43e10370f60400f70283e10b50b64f43b74765000404107000103f43000100e40000100504e41b52107f43b63664000e31a50000100e62000e21a50f20102b32e31a70107000e63332000000e65000f50101f10b52b65400e50380100102e32000106f40e31a74105000101f21000101f31000102502000f51b71000e61710000e40106000e30a50000f52103000e43a63000501a21e20a60b63f20721b42000f41b75f50b76106000000f51000506670f30b74106000102e53000f40103000e52b63000f20102000101106000101f42000e20720000f50103f10b62753000e54b65e50a70102000101f51000e54b42000f20b43000f42103100f20b63e10a70107000505a76000f32103000e40100500b70760f60e42282e32343104f50f43363000f20721000000503000e62b21000e21104000e52763f32e72342e30a50106000000400000e63b53000e65776000100e42000101f54000e62b42000e51762000000e50000501a41000503b53f30731b64000102405000000f20000f32104e50a70104000e31743000f60672000f41107000000f64f51b71a75000e10740000504754000000e31000f61107000f43651000102404e10a60103000000504000101406000e61b72e20b63104e31e52363000f21102000e42b72000500104000503105f40f41b86000e31b64000e42753100f20b73000000e61000400106000e32b50000e41104100100e10000f65674000501763000e31b42e40370f60000e31b60
    | _ => 0
  fld packed 36 (i % 128)
def finger8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x9209e0c59ad32647d55929db4b1f8d3af1c95815d08eb4564f6d3d434d18740cb0d7a0b78fd5778d8b825eb393ea487444b29a141690262838493d8cc8ed821fb89394e881c531fc8a3f4adec2a8baf63409a6af33d5c6885112724a851f59c55502c5879dd5e866cd0c570a669a6f720fef924d4641534c60e3bc50ca6c34e2
    | 1 => 0x871c0974c153910e3aa63b1474bc5f34786b1acd4d3bad27824960a4bdc7214b50d869d799707f2e8599ed0dbc3e303ab250d2ab3822d578ce417c1af55ef50535299d9a4a51c72cf349d4f6327bbbf322689bf7bb127e195dc685e9c4050695d9d3ca5f52b8be9a47ce2af61be82bf8d236210fb47f7abd3f560bd2f6ab743a
    | 2 => 0xccbec68b1e55ecbf2f8a8e261a6faef8d0c7592fc6cfe192dd9ad09647ceb679062c2d3412f9331afcbfc71b07dc70692b81dde2e32354f5a9743796c48d6cac8b26e12fdead5b861e259f2d765a210f95a17a9a53aba5632b8c8f662a7791581b520479db9fc6efdfa4b49d17f768bdb52738f5a9fd5a69a1416e3a6ecdb032
    | 3 => 0xa6030ee64ffa06338f80924f31fe7e3fcb75a96c2f0f6a58c89b13dceead363f74b5557b5d4e6be296799f76db731eb6931925b9502a383130e442b563ad63f5611d1d2157677fcbf28a8f148076618a2b6338b8d501fc377a49c16caef30f4096f1639bfa1357863e7a92362f62d0f9e43cc707192af8a9f22f1b51e08d2781
    | 4 => 0x9f354e923af3ff614027b5a2590ae2b21443b214374407a1cfee1e493aade9ef7f1375f33f20abf17480ecd952aa9c2015c14b756132fe3194ed90d4a0d1d1369687a7d3147c3a2073acec7ca9cd1de36183f661422d27de6f3fb42de391a779d44f93b676326a6340ea5a2962e7faeecb65d9e57e3740be91dc29a10d61334
    | 5 => 0x9114bcdaa18cf3e874df541578f3116be9f362ea32f0fd82345cc246f97a8db3ad75a978d9de4a342d452db9dd206fd2dc7842c773767c2a84178aa315f3af15925a6f69ca20d8357c31dc4ce388c3564d7905b5471608bd763bb870bd97a55fe7543865c71e17a32b1d08884ce0c7eb1525e3c3c410fedce45a3ca3665e5328
    | 6 => 0x686b947de699518158013ea5af52e5f50ad7f012786086214e59021f7b1ba0fb814189dfa2d657923b0484d2b1f4b71aafe79376772cf4421023415811630e9fe5e5df62d49139701ad89b5618232cd0fc641dd0eb5d2cd268f11311a0b546427429c0f38d29786bd1fec91e6d2a4052073350138631b8eb555b6669bc9e69e4
    | 7 => 0x8cb17dd369aad881472fa0777421ed38daa2ed02dff0150ac976ef70d08e3bd1fb4f935bf285e888a9fab24e02defc81d867cb26b1b2cf3363d6439678d7da682343f509b9a197e6947e9074c10daf43974871144dd358b9b8d2645bdeea98b0ca35315d3ddbf75e712a5231e5feedd3a1adbe623392e2c89d607d37f225997d
    | _ => 0
  fld packed 8 (i % 128)
def count (s : Nat) : Nat := if s = 7 ∨ s = 8 then 1024 else 0

def board : Nat → Nat → List Nat
  | 7, i => checkpointBoard (mask 145) inputs 4 (recipe7 i)
  | 8, i => checkpointBoard (mask 145) inputs 3 (recipe8 i)
  | _, _ => []
def atFinger (table : Nat → Nat) (ws : List Nat) : Option Nat :=
  let h := hk ws
  let i := h % 1024
  if table i == h / 1024 % 254 + 1 then some i else none

def lookup : Nat → List Nat → Option Nat
  | 7, ws => atFinger finger7 ws
  | 8, ws => atFinger finger8 ws
  | _, _ => none
def ck := checkpointCheck 145 scores count board lookup
def panel (s i : Nat) := ck s (board s i)
set_option maxHeartbeats 50000000 in
lemma block7_0 : span (panel 7) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_64 : span (panel 7) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_128 : span (panel 7) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_192 : span (panel 7) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_256 : span (panel 7) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_320 : span (panel 7) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_384 : span (panel 7) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_448 : span (panel 7) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_512 : span (panel 7) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_576 : span (panel 7) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_640 : span (panel 7) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_704 : span (panel 7) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_768 : span (panel 7) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_832 : span (panel 7) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_896 : span (panel 7) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_960 : span (panel 7) 64 960 = true := by decide +kernel
lemma good7 : span (panel 7) 1024 0 = true := (@span_join (panel 7) 512 0 512 (@span_join (panel 7) 256 0 256 (@span_join (panel 7) 128 0 128 (@span_join (panel 7) 64 0 64 block7_0 block7_64) (@span_join (panel 7) 64 128 64 block7_128 block7_192)) (@span_join (panel 7) 128 256 128 (@span_join (panel 7) 64 256 64 block7_256 block7_320) (@span_join (panel 7) 64 384 64 block7_384 block7_448))) (@span_join (panel 7) 256 512 256 (@span_join (panel 7) 128 512 128 (@span_join (panel 7) 64 512 64 block7_512 block7_576) (@span_join (panel 7) 64 640 64 block7_640 block7_704)) (@span_join (panel 7) 128 768 128 (@span_join (panel 7) 64 768 64 block7_768 block7_832) (@span_join (panel 7) 64 896 64 block7_896 block7_960))))
set_option maxHeartbeats 50000000 in
lemma block8_0 : span (panel 8) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_64 : span (panel 8) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_128 : span (panel 8) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_192 : span (panel 8) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_256 : span (panel 8) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_320 : span (panel 8) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_384 : span (panel 8) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_448 : span (panel 8) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_512 : span (panel 8) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_576 : span (panel 8) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_640 : span (panel 8) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_704 : span (panel 8) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_768 : span (panel 8) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_832 : span (panel 8) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_896 : span (panel 8) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_960 : span (panel 8) 64 960 = true := by decide +kernel
lemma good8 : span (panel 8) 1024 0 = true := (@span_join (panel 8) 512 0 512 (@span_join (panel 8) 256 0 256 (@span_join (panel 8) 128 0 128 (@span_join (panel 8) 64 0 64 block8_0 block8_64) (@span_join (panel 8) 64 128 64 block8_128 block8_192)) (@span_join (panel 8) 128 256 128 (@span_join (panel 8) 64 256 64 block8_256 block8_320) (@span_join (panel 8) 64 384 64 block8_384 block8_448))) (@span_join (panel 8) 256 512 256 (@span_join (panel 8) 128 512 128 (@span_join (panel 8) 64 512 64 block8_512 block8_576) (@span_join (panel 8) 64 640 64 block8_640 block8_704)) (@span_join (panel 8) 128 768 128 (@span_join (panel 8) 64 768 64 block8_768 block8_832) (@span_join (panel 8) 64 896 64 block8_896 block8_960))))
theorem closed : ∀ s i, i < count s → ck s (board s i) = true := by
  intro s i hi
  by_cases h7 : s=7
  · subst s
    exact span_ok good7 i (Nat.zero_le _) hi
  by_cases h8 : s=8
  · subst s
    exact span_ok good8 i (Nat.zero_le _) hi
  simp [count,h7,h8] at hi
def rho (ys : List Nat) : List Nat :=
  match fld 0xa642008424c080416a3045606004d40410d260b00b68b011 3 (bsr 0xfb1e0242e5fbb754e4578a26dedbcf48db58da58d6f67d87d01a17a5cdcb4769cc699b04ca2bb017c75a8d58c7065f89c36964cdc06437d3bf7ea796bedd3a3cba2a6b7eb9d5cf37b9c19f56b87ddabdb8150e95b297db70afe0a9b8ad3abd9bab3198cca40fb604a33e10cda11498099ff1daf193c305ad9196233f82cdc3487bce97e879c9fd3b70d90a6c6b5bd747656919bf65250aa663039633607708f15e4112b15b37383a589afe2c5230a7b74ec3fbb14c26dc6242d98db4401a06353937667136708df531b323aa2e2779bc2b6cd9ce2a222d6b29b832402845105b238b879f1e7ebf48129b800a0eda5e770ccd94de0b2fc92f07ad7b9b06fa3e4d 32 (hk ys) 7 0 64) with
  | 1 => vals.map (fun r => fld 0xf400000000000001ceda000000000002f000b0000000111002b552a50000000d70000000ca0000000c70048586bd00000009f0028e029b00435fc757fa0cce640000000d3002e5c65700001c2c6712b09447002dc009e5b081501d002ad4c96538642a1300349a23a00289843700315803360a645e2d00275380b5003d2609002552203490180000 9 r)
  | 2 => vals.map (fun r => fld 0xf400000000000001aeca0000000000039c00da0000001210030d8ebd0000000bc0000000b00000000a3004053e9b0000000ad002a622a5003fe1a837f19cea640000000b90038da65700001a4a268b0874370038800ac709298c47003058a99600bc662d002d96e20002a13c1d002813a0f4e24c16090029d5619530552c13002492a06488000600 9 r)
  | 3 => vals.map (fun r => fld 0xf40000000000000178b00000000000035c00ca0000001010027d469b0000000e70000000da0000000a9004455aa50000000c30031e42bd003f9fe67869d506640000000e30034d7257000016ca85ba78401d0034400c2690e944370027140934e82c1e0900385c44a003195847002994e1555a58321300301822f628cd322d0024524004a80c0c00 9 r)
  | 4 => vals.map (fun r => fld 0xf400000000000001aeca000000000002f000b00000001010028d3e9b0000000e70000000da0000000c3004858ebd0000000a9002b622a5003fdfc6786a0cea640000000e3002e5a65700001a2c2692887437002d800a85b8813c1d0028138934e83c160900389c24a002b18c4700305802f62a64662d0029d4c15558652c130024922004a8180600 9 r)
  | 5 => vals.map (fun r => fld 0xf40000000000000178b00000000000039c00da000000111002a55aa50000000d70000000ca00000009f00405469b0000000c70030e42bd003fa1a757f99d06640000000d30038d7257000016e9e5b2a0401d0038400c671129584700299569653854321300345a43a003094437002713a0b5024c1e09003018a33608bd322d002452a03490000c00 9 r)
  | _ => []
def B (i : Nat) := mv (mask 145) (fld 0x506f30f31e30502f43e10403000e63f60e43105505f63106400406102e40f10e60 12 i) inputs
def I (ys : List Nat) := bsr 0xd6f67d87d01a17a5cdcb4769c75a8d58bf7ea796bedd3a3cb9d5cf37b9c19f56b8150e95a33e10cd82cdc34879c9fd3b70d90a6c6b5bd7475e4112b1589afe2c4ec3fbb136708df52b6cd9ce2a222d6b0ccd94de0b2fc92f 32 (hk ys) 5 0 22
def test (i : Nat) := ck 10 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 145 (cutBoard 10 inputs B) (cutCount 10 22) (fun _ => I) (rowOrient 145 rho) scores 11 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 1 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z1 : span test 1 1 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z2 : span test 1 2 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z3 : span test 1 3 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z4 : span test 1 4 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z5 : span test 1 5 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z6 : span test 1 6 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z7 : span test 1 7 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z8 : span test 1 8 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z9 : span test 1 9 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z10 : span test 1 10 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z11 : span test 1 11 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z12 : span test 1 12 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z13 : span test 1 13 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z14 : span test 1 14 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z15 : span test 1 15 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z16 : span test 1 16 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z17 : span test 1 17 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z18 : span test 1 18 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z19 : span test 1 19 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z20 : span test 1 20 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z21 : span test 1 21 = true := by decide +kernel
lemma regionOK : span test 22 0 = true := (@span_join test 11 0 11 (@span_join test 5 0 6 (@span_join test 2 0 3 (@span_join test 1 0 1 z0 z1) (@span_join test 1 2 2 z2 (@span_join test 1 3 1 z3 z4))) (@span_join test 3 5 3 (@span_join test 1 5 2 z5 (@span_join test 1 6 1 z6 z7)) (@span_join test 1 8 2 z8 (@span_join test 1 9 1 z9 z10)))) (@span_join test 5 11 6 (@span_join test 2 11 3 (@span_join test 1 11 1 z11 z12) (@span_join test 1 13 2 z13 (@span_join test 1 14 1 z14 z15))) (@span_join test 3 16 3 (@span_join test 1 16 2 z16 (@span_join test 1 17 1 z17 z18)) (@span_join test 1 19 2 z19 (@span_join test 1 20 1 z20 z21)))))
theorem finiteCheck : ¬NatRun (mask 145) (goal 145) 11 inputs :=
  symCutRoot (rowOrient_sound rho) roof (fun i hi => checkpointCheck_sound closed (span_ok regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 12 ≤ t := by
  refine proveAtCap 7 145 11 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finiteCheck

end Row29

namespace Row30
def vals : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 8, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 16, 16, 17, 17, 17, 17, 20, 20, 20, 24, 24, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 64, 64, 65, 65, 65, 65, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 68, 68, 68, 68, 80, 80, 80, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 3, 5, 9, 3, 6, 18, 5, 6, 9, 40, 72, 3, 5, 6, 9, 11, 14, 18, 26, 40, 42, 48, 72, 74, 96, 13, 14, 44, 76, 18, 48, 19, 21, 25, 49, 21, 22, 52, 25, 26, 56, 88, 3, 5, 6, 9, 18, 29, 30, 40, 48, 60, 72, 92, 96, 40, 48, 96, 3, 5, 6, 9, 18, 35, 37, 40, 41, 48, 49, 72, 96, 97, 3, 5, 6, 9, 18, 35, 38, 40, 42, 48, 50, 72, 96, 98, 3, 5, 6, 9, 18, 37, 38, 40, 44, 48, 52, 72, 96, 100, 72, 96, 67, 69, 73, 97, 3, 5, 6, 9, 18, 40, 48, 67, 70, 72, 74, 82, 96, 98, 69, 70, 76, 100, 82, 88, 112, 3, 5, 6, 9, 18, 40, 48, 72, 83, 85, 89, 96, 113, 3, 5, 6, 9, 18, 40, 48, 72, 85, 86, 92, 96, 116]
def inputs : List ℕ := [0x21770b02045f801580572b5801589f0401b29e000fff800003c0000000fffc00000780000007, 0x42a115256ca8802acaea01a802a921492f517200000000fffc00003fff000000000001fff838, 0x2e0c2061e083112b3008c02305330723c0261a5fff0000f00000fffc00000007ffc381e0000c0, 0x9504a848314224c413104c417747843dbb8e080000000000000000000000007fffc01fffff00, 0x2ea1750e0428003080c2030825b87ffc04c0041fffffff000000000000000007fffffe0000000, 0x30c18609183045bf06fc1bf079c0248927004000000000000000fffffffffff80000000000000, 0x3f01f80fffc07fc007001c004e0040023800801fffffffffffff0000000000000000000000000]
def scores : List ℕ := [0x1fc2a230a32689b, 0x1fc480e8ae2649e, 0x1a84802ca3288b1, 0x158480e89a2649d, 0xe82a02ca2278ae, 0x1580b1fcae26ca2, 0x1580b230b128ca2, 0x2302a158b1288a3, 0x1fc2a02c9b2749a, 0xe80b0a89e26c99, 0xa80b158ae2749e, 0x1203a1589e26899]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)
def recipe7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x100e61b51371000e31a61310000f40652342000e30320730e20a60350102000e52350106100e61751372000e10740360e30320330403e21a40350106000101e51341000e31342103000102f51263000100e61361f43a64332b54000102e64341000e62362362101e62342106000502b52276000000103106000f10a42362000f43a64331f50e75354375000000104106000f60672342000000e31331000f52276b65e30341e52370000501a41310000f31640330000e20320720000f10b32243500b10231104000101e21341000f60665354000e30a50330000e54330105000e43a63332000102e43321000e10a30360000000e65376000e60350101f50f74285376500a30740350000e40370104e20a60340105101503a54363000e54b30342f21f42a72310500a20a50340e30a50370104000e54a73331e31310730b60000f10a42332000e31351732e10350e65376000e10370102000e10a70340000e21a50360000100101101000000e41331100e61731372000e20a40370000100101102000000e31371100e30a54373f10b32b63276000e65105230000000101104000e31771342000e52370b52000e20370102100e10a70350000100f40253e41341741b64000000e31361f52e72342276000105e63374000e30341104e20a40350105000e42a72320000106e50361000100100106100e10a50340000101e61310102102103104000e65b51342e30341101101000100e43320000101e51362000e21a70350000e30642321000e31351106000e30370103f31b64b76274000e62b62372000e51a70310000e30370104000e52350b52000e54b31372000e31a61350000e62762373000e65350106500a40370100000100e43362e10a60350103000e62b21372000e54a73330000505630350101102104106000e65b51341000e30100264000502a52320000f52276b62000e62b62275000e30360102000500a20370000e31731361e41361b41102000501a41351000e54b30321000e42a72321000e31310330e30341105106000e62362764000e32a62310100e31331731000f10242105
    | 1 => 0x100e41330103000f30731240000e41310104000e41310103000e41310742101e43321106000e62320665000000e41341000e10330105f10b40330a20000000e20340000102103106f52b72364a64000e42a72342f10b32102232e52350b52b64000000000100000e20a70360000e54103273000e62102372000e32105342000f51264106000504730243000102e64375000e52350105000e52710340101e64343106000000e54373500a10330101000000e62342000e60350760000500a10340000000e42342000f40a64331000e10a50360e10340710105000e54331106000101e61361000000103105f10101b41242e20a50a70360000e43a63373000000104105e41310b64105000e52740370e20a40370102000f42650370000e20370b20100101e63330000e52720340000e20320101000e41310740000100102106000e31310730000e62320103000f20b63276000100103106000e62342104000100e20320e10b60a75376000e41a61310000e54a73343e20720340720000e31361102f21b52242105100100100106000000e65352500a10a20350000e20a50370101e42a72321000e20750370f21b43b43241000e41a65343000100e64375000e20a50340000f52b75265000f54662342500a40370103000f50662320000f40b60263000e41a71361000e52310106101e41370741103104105106000f10b31230e30341101106e62362362404000000e30330e10340710b60000e41361103000e41361742100e10a40350100100101102000100e30320000f31640370000e52340104102e52102363000100e20370000e62362b62000e65b53375e20340101104000100100103100e61675352000e20360101000e41a61330000e52320106000e21a50340000e30642352000100e20350e10370e30341f40b60730751000000000000e21a70310105000f32b65276000e20a70320f10242103104000000e31342000e10330106000e65b52375e20370e30341e30320330e43000505a76360000e50a70320000e10340102f31b53a64332100e20340106000000e10350000103e54342
    | 2 => 0x101102000e54373b54000e21a60340000000e41371000000101103000e42a62320000e31331106000e31371732000101e53364000e30730370e41310740b64000500a10350000100e61310000101e41360101e21341106000e31a71310000e30a60350000e65b54375000e31361732000000e30341000502a42332500a10330106000500a30340e30320330400000e40a60340000102e64342000102102104000505a76361500b10b51252000e53a73331000102103104000100e50361000e30a50360000000e30370000e10a30370000e31a51310100e21341102000f43651310500a10a40370000e40a60330000100e30330000e41331106000e10350104000500a20330000f62673353e30a70350103e32a52a72362100e61101371000505630370000101104106000e10a60350000e41a71331100e41340104000f30b54251000e65351105000e54331105000e31361106000104e32343f50b70f10370000f32650360000100e43372000e41361105000100e61331000e41361b41f21b43b65276000100e31331000e54b31342f20b70b31362000501a31341000e31351731000e43a63331000100102104f10101231102000e10370105000e10a50330000100103104e30341e65376000e20360104000101e64340000000e63353000e41731371501a31371102e30b20340105000e20370105100100100102e30330f40343000e41361a54e30a50a70360500b20b52275e21a50340102000e30360105000e62676365000e20320105000e30730350000000000102000e31b10350e30360102106000e54103243f10b52b65263000e31342102000e52310105000e63105343500a20a40330000e65352764000f21b63264100e30a54332000000e10360000000e62362100f41b74264e10a50340102000e62373105000e30320104000000e62321100e30a70350000e10350102000f64672342000e10340106000000e30350000e32a62320000e41341a54000500a30320000e62b20372000e60350104000f10b62263000e52320105000506b20252000e10750360000f50b76272
    | 3 => 0x100501a71310000e32a62350000e30341102000f20a43353000e31351104000e41103361f10b62b76273e40a60340102e60350e65376100e31a71351000f40a64373100e64341b63000f63670350000f61764264100100e30330e10a50360106501a41a71310e10a30370102000e62752373000103105106000e41b10330000e30370102000f64765265000104105106000e41a71341000e30750341f10b32243105000e41741371105e63374106e41361b41732000e10370101000101e51331101101103106000100100101000000e41361f60f21b52374000000e52340000100100102000e31351103000f10b40231100e20370721e60350101104e31b31a72373000e65b52343e30b20340100000e20370101f10242103103000e30a60370000103e65350f21b63b76274e20a50340106100e20350721000104e65350100501a31321f10b32b73273000e10100274000e41331b64000101e65353000e10100276100101101103000e41331105e41a71361106000101e41310000f50662340000e31371105000f32650320000500a30370000000e54332000e30330106e62506287373000f10a52372e41361742106000e52370106f60101664342000e62352103100e54104365000e65376106000100e53332000e10a70350000e20a60370e30360f42343000e20340720100100103106000500765276000e10a70330000e10a30340000f21b43250000e30320b30000000e65354000e30360101000502a72352000103e54340000000000106000e10330101000e10360102000502a72321100e30350b30000e31710341000000e20350100101e65376e31a61350105000e50a70330101f41b71363000e62b21361000e42a72362000e30350102000e10a30350000e10350106000000e40370000101e41340000101e43362000e65352b64000100e62342000e41a61370000106e10321101e64741374e20a40a50370e10e76363375000e30730341000e30a50370500a20310104e10a50370102000e20a50320000e41341102000102e52363e32a62310105000f43a64373000000100101
    | 4 => 0xe30341106500a40370101500a10330100000e41341b64000e10370104000e10370103f21b71b41363000f31b53251e30750341102000e31b10330000e20340105102103104106000e10330102000e52710350f21b43754250000e20370103000000100104000e62362762000000e20360000e20320103000e20100273000e31101331000501a41321000e20320104000f10242762100e10a70330e20340102750000100e43332000f10b72273000e62342105100500b40242000e31a51331000e42342105e20a40a50320f30b54251106e30a60370102000e52310104000e62373103000f43a64332000f52a76360e30341101103000e62373104000e20a60320000f51754254f10242104106000e62b20341e30b30a72373000000e30320000e31b10370500a30370101e30320730a40000e51a70330100102104106000501662352000e21a40360000f62765272000e52320103100e30a70330000e54331754000e30360103000e52320104000e30a50320000100e30350000e10330103e30330101b32000f50662350000e32a62370000e10330104000e53a73330000e30770341e30320b30101000000e41310e30360101101500a20370100000e32a72320000000102106000000e32352f52b72102364e30330103104000e52350103000e31a61330000e20350102101e21a51310000e62362106000000e60350e20a40320104e10350e41310000e10360106000e62321106f20e41371342e20e41341341000e31103361e30320104106000f60762262000e30b20241100101e61331000e40370102000e42a62310000e30350106e10340710104000100e43321e21a50340105000000103104500103763262100e64375106f30731240106000106f20263100e61341102000e54b30320100100e30370000e54103231000000000105e21a40a50310500a10a20330000e41371102000101101102000e41341106500a50a70340000f30641361000e20340106000101f41275000100e64343000000e54343000f62670350400e73373373000000100106000e10350105000000e62320
    | 5 => 0xf31b64264000e20360102e20370102103000e41371105000101103104104e63374106000104e30341000e31361103100e31a51330100e20a70320000e41361106000e31361104000104e53364100100102106100100101106e41310742b64000e31106341000e52340106100e10a40370000000e62352f60f42282375f52b72364a54500a10a70350000101e64341000e30360b43000e31731351f10b52b75273000104e31342000e30320330000e21a40310100100e63374100e20a40350000e21a40370000e30370105e10a30370105000e30320102000000e54330500a10370103e30330b43103e40a60330105000f42a65373000f62675354501a41a71351000e30330730000e30330101000e20a60340000500a20350e30360102102000e54332106000e41761371000e65b50375000f40651371100501a41320000e20a70350000e41310102000e65353105500a20310103000f51264b30000e30720350000502a32342100e43372104000e40100276100e61331104000102e65376000e20720370100500a20340000e65105376000e60350102000000000101000e65354106100e61372102000e10340104e31351103731000e41101263000e31a61370000e31751361000e10a60340000f10b62264f60761e52370000e20a40350000500a30310000f21a53343000f10b52253000f10104242000e52104340000f10b41231501a31a51310000e41a61340000e10350101500a30a40310000f52103276000e40370740000e54a73332000e62102260000000102104000000e31310f40b60751732e10360103104000e10730370000f65672352500a10320103000e52310752f21b53b65276000e42a62340000e31a71331f30b64b76272000e20100274000e62321105000100101106000101102106000102e43332e30320104105000e53a73332000e30a70350000e30100330500a30320104100e61351106000e10a70360000e21a50370000e10340b10000f21b63276000e20370106f30b54a64373000e62b20310000f42a65343000101e64375000e31a51361000000f10242
    | 6 => 0xe50a70340000e20a50360000f43a64330000f30641351000000e30360500a20330100e21a40a50360f51b71742362000000e10330101e65105376000e62752362000e63103253000f60665352000e31371106000e30330103000e62b21351000100e20340000f52b72364000e30330104000e32352732100e40a70340000e20a40320100100e32371000e10730350000000e52350000e41361b64000f52b72265000f50664373000e21a40350f30b54a64332000e65752375500a30a70310000e65350105100100101103000102f51262000e10340710000e52340105000e62320761e31351103105000e51a70340100e20350102000101e62342000f50b70760000000000103e10330103106000f21630340e20340e62352000000000104000f40651361e20360e30341103e65b52375000100e41360000100e61341e50a70320104f10e40380242000e10a60330000000101101000e32352106000e10350103000e62320102000e60350106000106e30341e20a40350102e30320b43b63000101e61351000e62742342000e42104342000e54332105000e10360101000f21b52242e21a40a50370000e65b50341100e61361103000f43651331f52e75351276000f21a43353101e41370104000e43a63330000e31310102000e30350101000e31331103100e43321106e30320b30105000e30720341000e31331104e31a71351103500a20a70340000f64675353000505a76365f50101b75271e10340710b50000f50752252000000105106000e20350105000f41650370000103e65376000e30a60330000e10740370000102e50361000104e65376000e20340101000000100100000e30720370000e54343106500a10330103000f40a64343e10a30350105000f51264b31000e40370105000e10106340000e10350b10000000e31351000e21a70310e41a61370105000f20a73353000e51a70350103e53103363000101e43372100101101102000e21a60310000e41331103000000e65350000101e31331000e40a60370000e31371103100e43a72321000e30a70320000100101103
    | 7 => 0xe62352106000e62321764000101e65376000e10730360e10370104105e62373e54373100103e64343000000e10340000e20107310e20a40320102000e30750360000503a74354f43b63a53330500b10231106101103e64340000100e61372000e20a60350000e54330106100100e63353000103e43354100e30330730500b70664342e51a70340102000102e54365000e42a62370f50f42362732000000102102000000e65351000e62742373000100e41310000000102103f50b70f30374000e41a65374500a50a70330000e62362103000e41107320e20a60370101000500a30350000e32a72352000e21a70360000000f51264000500a10320000e10360104000e62321104000106e60371000101e64343e50a70350101000e30320105e60350102106000000101106000e21a60350f10b50b30342100e21341721101102e43330000e41a71310000000e54331000e31a51371000100e41340100e30350b63100f41b71264000103e32343000e30a60320000e41310b64000e31107320f10b40330b42e10a50370103102102103106000e31101276000e10a60370000501662342000e40370101000000100102e42a72342104000000e10370000e20340104000000100103000e31310106103e63374106000e21a50310000e60350105000e32a72321000e32352104000e30a70360000000e20370000e65b51375e60350760103000f31640360000e30b20340000e32a72362000100100100100e21341106000f42b75275000000e20320000e42342742000e31351102e30100330106000e42342104100100e60340e10a50360104e31751342102000501a76364000104e65354000103104105000e30730360000e30341101000000e52310e10721a31351500a30340100000f10242106e40a60340101000000e62373101101101103e41310a54b31000100e53364f20b63104276000e41341741000f60665353000e41b10360e10350b10b50000000e52370e21a70340105000103e65352000e62320105000e30370101000000e52320000e30a70330500a20340104000f53662352
    | _ => 0
  fld packed 48 (i % 128)
def finger7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xf9cc84ad979d730f4c0fa9c3941a94e01a49a5cb6cc793d407f516e5ee10bcf9e34df765e32452ca61e2f6b77460f53a879f2f28235ac607fafbd96deb3c4376b625c94e0fd5ce333fce0f87db542884533f8bcaed3974d35ccda548395052d60959d664f850ad2b0be5adf6c650d98b8f9e45993bf0ed45b826b35c1e77f1c0
    | 1 => 0x1b845c550280dc81ecdbcdef7c3f147caf6beeb013495d7a440c7eb7dcddf9557e2b25c1d506729f7bee7b1cb55cf6b90534c52eeef652e0f7261a30ccb001a2fca4a0ebd11acda7ed849d306097d9622fe805bcbc5860f939a855fc3d10edf63fd9ec10523227129c1261d0aad1aa8c73fc20dbab4773082554fbb91c5c3249
    | 2 => 0x6e27f0de778a93e15b1a3e1e9627e9bc6877b27c995fc304ac548d0aacfd96ad63abdd14d3faeb96a489f6f0c479a6d1c4ab449465dc347c25bc1b73da6c024c9aa1d108d8805c95d526509e517e4e6d3f98c45b4b03240d057af106a20fa521370fc2c48ffebe2ed112f91853980bb975524daf3ca0735a1ee73589b758a1ae
    | 3 => 0xb1ec95869cbde8c57749ab6773e561c119f63f1011c69519d6903cd3e6da20f8c49107934c9a3d37062759b6c0574379b11039d5babc4840badff6b030cb8b45f9fdcea497472df143cda6a732e0deb1e32ece0707cf19c6a2bd31422ae6168e6f22435e3df6fcfd26bb56cec63e49469045cf63791de783c3e3d19c45ba49c8
    | 4 => 0x1a0602508c8595cca97b1234e4be25baf2cbd2018c1c2c0aeff14649cd220d31c1b67a94f76836a367711069c602140d3ce7778d336b45e018f9f52221dd284b4ee538544a9bdfb0d67806430f6349a1c15cb4b2a4da56971113174b571503a9e1e83e2bc7a2dafc5320f4c94c5795cf71f0f7901fd55c6bc9c526ed894d75af
    | 5 => 0x60ebdc23ba2e732b5e0ea1340c362f2c51e8d50512f95add95051c923f39c14c57ee22289fafbad91ef96e9a381cf33d4257e3108834c96f2da923281ff44538e8e727bdc9408b4bc8547f957d824d40307e61c372a50b3e71fe2eba33bae812bc49fdfc771ad13be91503b6660c41fcdad4e85fd537b453501d8896b49e297c
    | 6 => 0x6a522f107f31c81ba80d8d6df42a9beabdbea43a532e1b4efed261b9707325badcd4857d8f6480764eac2330e78546398fc0178a28a69db9e4abd476406359f0555678e73abafc22c360c242777b2bdf976509fba09d57f1e5ed50286d847403daf24a0c0eec2ec26e1a99550b34e59a2f8888300ef618c38f10bd5a5a56970d
    | 7 => 0xa17a6917cfad099d114993113c3df9e87b3d2e4121b28fbff6d549c41896524d018db84beea2bc1baacba62035dff1505b67a6725d81d738c223f58404497da0bd6c916e5ab80751e8e07a5aaefdece5ab281d17999b83824309ce445ecdb3862b78d0d2a1e41feab94d5c021ae9c5ca63b38bfc8f297df41342f0ea739ca780
    | _ => 0
  fld packed 8 (i % 128)
def recipe8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xe42753000501660f20721b43000e42105000f40652e41a71107000e21106e30a60106e41a61104e20e73384000f31a74000e54730f20b53b65e40370f60500e50361000f30b64101102405000506b60000e31b71000103106000f31640e32a52107000505a53000403107100104405000f41650100101e61f21b42a52e10102105e31a61106000000e51e10b21107000e31743000f64107e60b71102000000e64000f20107000101e43000500a40000f21107000f32754000e52106000506a50e40a70103101e21b32100500b40000e60b30f21102b32000400102000101f62000f41b65000f63107000501a76000101403f21b61101000f40107000106e20000e30a70000e30b54000f31105000102e64000f54b74000000405000502a76000000e53000e20104000f60674000f51662000000e62000e20105000102f63100e60103100f20b53f43b63664000e43754000e31361000e21b40000f10b72000e30b41e40a60105e54a73106000502107000e53103000e21a40e21a70106000100f42000000e32e20a70102500a40a70f10b32104000501760000102e32000101f53f10b32105000e60750000f20b43000e51a70000e21b50000504b43000e10721000e10740000e10a60000401104000f50101f32b63b76000f10b40000401105000e42b53000f52b75000e50761000100e64f53b73675000402106f10103103000e65776000e21107e30a60107000f54b76503f54b86000500105000100f63000102e62f50751102f20102660000f20721e42a62104000e60106000f60102
    | 1 => 0xe20a50102f40b60b74000501663000101e41000e52b50000503643000e10a30000103e54000f54a76000504653000e63106000f60105e20340f32000e63732000f50752100f40102000000100f21b73105000400104000101f32000f31b53000103e30000400105000103404000000f42500b70106000105f43000000504000f10b41000103403000501665e65376f65000e63774000f60763f30b54107000106f20e40a70107e50502270000f43b65100e10105000f62103000000f61000403106000000e30000f62104000102404000e42721000102e42102f43104f52105b76000e32720e40b30b73100102106000e62b62000f60762000f20106000502a72000e10b60000f21106e20b31101f10b72102000103e31000f31b54000100e40000e62762000000406000e65352100f10107000100e63000e62b21000000f10000000e10e30a50105000f50103000101401f10e41352000f32a75000f50104000f62671e51a70103000506b30000500101f10b42103000e54765000f20b73000e30642000e10750000f30a74000f50f21101f32b74000e40b40000e31b51000100e42100101e63000500761000100404000e65750f43504b85100100f60000f61674000502105000100e61500a20104000f20b70101102f63000e61b72000103506e41371f64000501107000e21b70000f51103000000000000e21b10000000f32000f51104000e43a73000e31342000103505f21b63b76000100e21000f60106000e40103000e65b76000500762f21102b52000e41b52000e10350000e42104
    | 2 => 0xf31000100e30000103e53000e41371000e61b31000e40106101f41b75000100f64000f50753000e10b30000000e20000100e60000f20101f10b31104000e21a50000e40a60000e64107000f31a54101e43107000e30341000e31a71000104e43f32b65776000106e50000f61102102402105000e30103e41105106e30a50b54000e32743101f62106000f40101100500104000e30370000f10b32000f41b75000f50661f21b71a72e30a70107500a10a20000e53107e30f51354000000401000405107000402104000f51753000501a31000e31742000402105000f51b71f40f61365000f20b42000f53105000e32a62000f21b42000500104100102403000100f31000f10a42000f41102000100503100f42107000e31a51000506a40e21a60104000e42a62000e10760000e32107000e31b10000f30a64f30642a52000500a30000e60771f20e60371000f40b75f32b73b54000f50664000505a76f60f43375000e63353000e41a65e50b61752000e61772e42a72104000f41b61000e50104000e53a73000f64105f60103764000e50105000f54661000501a21000f63675f54b76106000000102000502663000000e41000502764000100406f51b71675000f54662f20102b52100e42b53000e43106000100f30f42b65776000e10360000000f65000f43651000f20a53500b50103000000e61000e62321e32a72105000e40107f60761105000e40751000e30350101f42b76401e51341f30103b74000e40b51000f21503000f32b63000105e43101f31b74f30102b53000501105
    | 3 => 0xf21b61b42000f40103000e20a70f30f61364e30341e41000f42107100e41103000f40742000e30a50000101f42000f60675f30731b53000505632f20b53743f40101b54f30101b43000e31104f10b32102000000f50000e30107000e31105501b21b32000f61106000e51762f31e51341000e43a63100f32103000f10b42f51102742100503b54000e51106000e64b75100100401000100f20000101e64000e64106000102e54000e20740000e62721f52105107000f53506f20b60104f21b53b75000500a20000101f63e31a51103000000506000e52763100e20a70100e63107f41b65105000f10107000e10107000f10b50000f40741000000f51000106f30e30a70106000103f31000e53106000103f43e41371f61000000505100f30b74500b40100000101e32000e21104000000e42000e62106102e42a72000e21105e30a60105e50103104100f40742e30400352000100400502105107000502763f50f43b87000e41103000102f53000e41a61000e52750000102e52000e31751000e41b71000e32106100f10b31000e65354000101405000102f64f10101104000000106000e30770000e61103000101e62000f60101401104106000f21b52000e61b51100e21107000e52104e20a50105f50101104e10a70102000e52105f42b64a64500b40b74000e41b61f40b60730e43a63a73000e62773f54105b76100e30a54f60f42375000f21b53f21b71104000503b54000100e53000e50100000e41741000f43104000f50663000f42743f20b43b75000103f54000000f30000101402
    | 4 => 0xf50752b75000f50102000100502f10b32b63000f43b75f30f62b54e10a30106501b41b54000104e65000e21a60000f54506000105f30f40101107000100f61000103f64f10b32107000e60b20000f62765000504b75000101404000f42b74000101e42000e63731000e42a72000f42106000000e50000e31b31000504106000f42a65000102506000f32b65f51f43365500103107000f60764e30341f30000503a54f30f71374f10b52b65000e30106000e43105000f31504000f61105100100f31e31a51107000505631000102504000500b50000e30320000101e21100e20103000502a42e52b63104000101f50501a51a70000e32a72f40b75106100e40751f31b54106100e32a52000501103000f30b74000e43732400e40340000f61763e41a61103000105406000e41b31e50a70105100e63105000e63105000f10106000f50f71f21b73103000500660000501f21000f60104000e20731000e41107e10a70105000100506000000e54500101104e50a70771000100f40000e60350000e60b60f21b53743000e32b43e41a71105000503630000100504000000404000000f63000101f54f21b43b65000e40102e31342404e40751107501b21b52000e20a60000100e31000403105000000503000e65105e40a60a70000504731f51104b76e10350f63000000f62000f30102000f20104000000105100e30102000f21104000f20105000f52663000e41771000f21105000f52103000101f51f60105106000e20103000f52104f42b74a74000f61675000100106100f10b41000e62320
    | 5 => 0xe30102000f40b60500a20a30000503731000e62105000f65674000000e21f21e51331502103107f10b72103000e20106100e60105000e30a60000e50103e21a40105e40a60106100f42103000100401000e32104000e62352100500a40100f20b73000501b61e51a70104000100405100100e62e20103760000101406000e10102000e31a61f41b75105000f51107000f54660000f53b76f10b32106e10721105000e54330100e10a50000505107f52104b75000f42b75100103e64000401106000e20a50103f54b76000f61507000000e52100102f63000e42107000e54b65100f61764000f60672000f65670000e31761000f52b72000503b73000502a62000f21b71000500a50f10e40253f20721105500b70763000000f43000102e43000f32b75000000f54000e10b40000e65752000000101000f30732000101f21100f40101101e32a72e30360f53000400103000102f62f40f21352000f52660000503b63000102403e41a65106100100e10100e21a71100501a31000e21a70000e54a73000f10b31000e41b75000e30b30102402104000504a43000502b72100500102000e52100000102104000e31310000e41106000e20a40f40f21353000f53106000e43b63000500765000e20b31500b10105000e62752f21102104000500a60000f30107000100e43000f31107000f52676000f53104000000402000e42102000e43b73000501a51000f31b74f30b54104f40742b64000000500000100f62f20101107f61504375000f62107000100403000101e63000000e60000f21f64
    | 6 => 0x100102e63000104406000f10104000e10104000500763000100501000f50751000e10105000e50a70101f42104000000e63000000f60000f43650000f50105000e10a70f10101102f20b73103000f21b73000e51b40f10b32b43f20b73104e30642105000e32102000e50b20000e52350000506b10000505b43f10b42106100e32b43000e41a71000f32b73f40101b74e43e76387100f20105e30741a71f32754b65000e54b32f10b42b64500a20105000100e10000e32a52f30b74106000000403000000103000f32104000102f32000105506000000104000102f43000f52b76000e10b21100e21103502b32b74000501a41000506670000000f20000e54107000e64775000000f21f31b53b63f42e72352000e63730100e20a50000000f52000101f64000f63672000f50b70000400107000501a71f10b31102000106f50500a20a40000404107000e50b30000000f40000506a20000502761f42b75765000503107e20a40a50000e62676e41a61106000f30a54000f21a63101104405000f61670f31b53a53000101e52400e50380000000e31000f42b65e10a30102000105106e40f50380000e51105000100f32100101e32100f21b74000100f43000504a75000000502000100100500b30721100100f10f32504365000f60671000e30b20000500102100101f61000e60103000f20b60000f20a43000101503100e43a72000101f31000101e54f30e73384000103405100101501000503a64e21a60103000104405000e30741000e43b54000502661e50b61b75000f30106000f31642
    | 7 => 0x502760000105e63000f10a32000101506e21a60106000f32b43e62342404000e10340000100e32e10102107000000e40f40501341000501b51000f21b63f53b76106f41b61664e50104105e53a73105000f51663000101504e21a40a50f40f21b86000e52107000e41104000101e31000102402000e31b61000e41105502a32a42000e41753000102103500a10103000100500000e10770000103f65500a10104100f30102000e20b70000e61104000f31b64000f40743000f21102000e61105000100e62000500b70f32b75106000e60b71000505b53f30b54b75000101106000100e54000e41710000000f53f10b42b74000e53764000e40a70000e32b52000f40b65000f30b54000f21b43f30b74105f20b53b75100501a41100f21b72000e62b73e10a30105000f21b61f10b31107000e54732000e20b40e10e73384000100102000e31103000505663f50752103000100402000e41752000000e65000106f40100104506000e21732100101f32000103504000102405000f30731000501b31000400106000000f64000500b20100100100100e63774000404106000f62674000402107e20a60106000e20102000f61103000503106000e30104f42743b64000f61104000e65753000e30105000501662501a21a40000e52310f21e41354000500b40000000e43f30102105000e62373100502107000102e51e21a60107f42b62b74000f60761100f10a52000100e20100e40103000e52370000e52b63f31b54104000e21103000100e65000504753000103406e41501272000000501
    | _ => 0
  fld packed 36 (i % 128)
def finger8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x1aa3327638c4575a59b2cf0f71f1b64def6f8acb52f20cb185b6d7a9b883a187369a62483db1e76532aad00546ca8eec3bd60ce1e3d87a2b82a060a4a8d64af9371b5356c224810e9fc3e787b179053d0af7cd72b04508d00d461b72d74fa483821d7d174b47740e52687d73bd93b2cf836d1db0b3a1be628bb4099e2664d1d0
    | 1 => 0x46e778a60da92a16bbb2def881b99b2faf649e6810c3a73de8767846d85a90c1d1eb062386a1887abafa584cc363135065f7aad7eed26ce2ddb70c5992787ac44e60a0866babaf37be717fce2a7a3d9b765e98327240dba709d2cba758cb126d7eb078ea9ee547584a71a1baab3c0c8cbd4015a8ab30f62b53df3524bd28326d
    | 2 => 0xf806e0de8009f111a65c7869dc49af8fe4884f7c6192f86e157165d0283374ca75aba32843e13e4dd154cfe6e24148eeeb925b9d6504c5ca600d053169df95d156bfa4a48d6a666de2361631ddd2e96dbaaee0c8aeb141ab5fbacf51273da512e1a283a2d28a659a39e4f9ee2ce79d48750a6294b8a064300b571a4d58546652
    | 3 => 0x1f2f926ad1862edc125f8f4d4d6279a7abbccee6b41298c0ed59f7f55ad5e417751dcc8bb6b9b6f6c61d539ba5aefc3782094f4dd3400a6912e3e3786b4e8d49ed96b6c8075abfc2d3623af23afbedfabbb6d92d17b24be8a24e099a2a6b61d8f2b5714cc70bb25177147b39c1dbf279e2dd6b859dcb6f97d6d4267a88abb452
    | 4 => 0x1fe7d8c694f26d493ab32e65683a0a4155a31387b77427252d0ea8895617ada75fbca4f902698d047e3f82333ea6ef0d47cee1e95abf5eb2e3bb7cb166666832cfa3a03eae46f23cc1064962d57fe32173a1e78aa4731708d320ae98984b8505b756e1d9ebbeb755d5a2db3e17cd41cf1f694a723572b9d19691c2df3f4d92af
    | 5 => 0x895fb6426fe51327991dbbac18291dd2ee62aa050315182441a8ef9f743f6905dd26e6c29fd42968165d140843d9682d66dfc611c405ecad1ff1313cd1dd2a8c6d082653c9df7da5e51516b16304a8b3fd6a7f066cc6a6aeacd9e630d401e81226937932b33e1b173b8d2952949616cb3fd762def0158b1eb97aad23bb878d5c
    | 6 => 0xf0d53d9117debe292a29ab402113709162079371feb0d7dfe74343a8f29c1532b607d918b20dc3655041430e943413921b3e8cd8820a29e0f4fc69161de62182d50879785bf792936168ce384a253e7f0f97b928f471fb5370ada676dd44e4daf902bf35aec04a0dda45039d4a6714e83e729cd72eaf3d7ccf3e96c9085f704
    | 7 => 0xb664fe3bf455b69d7912c547a6a3c2c05ceabaca65500483072d448c703252fa318b9005dbe9e87b1cdff1bdd70b46b0c1675b21215e0ee71b3b69d0a9fea4e499d35e445755705123493f375e8e95649a44e67399373e67c10972dbefdb1cb59cf8ecd7a5c1f5bdee4dc6af5812c576ab4feb50b52b66f43f252e1c8404dd0e
    | _ => 0
  fld packed 8 (i % 128)
def count (s : Nat) : Nat := if s = 7 ∨ s = 8 then 1024 else 0

def board : Nat → Nat → List Nat
  | 7, i => checkpointBoard (mask 153) inputs 4 (recipe7 i)
  | 8, i => checkpointBoard (mask 153) inputs 3 (recipe8 i)
  | _, _ => []
def atFinger (table : Nat → Nat) (ws : List Nat) : Option Nat :=
  let h := hk ws
  let i := h % 1024
  if table i == h / 1024 % 254 + 1 then some i else none

def lookup : Nat → List Nat → Option Nat
  | 7, ws => atFinger finger7 ws
  | 8, ws => atFinger finger8 ws
  | _, _ => none
def ck := checkpointCheck 153 scores count board lookup
def panel (s i : Nat) := ck s (board s i)
set_option maxHeartbeats 50000000 in
lemma block7_0 : span (panel 7) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_64 : span (panel 7) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_128 : span (panel 7) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_192 : span (panel 7) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_256 : span (panel 7) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_320 : span (panel 7) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_384 : span (panel 7) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_448 : span (panel 7) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_512 : span (panel 7) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_576 : span (panel 7) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_640 : span (panel 7) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_704 : span (panel 7) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_768 : span (panel 7) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_832 : span (panel 7) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_896 : span (panel 7) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block7_960 : span (panel 7) 64 960 = true := by decide +kernel
lemma good7 : span (panel 7) 1024 0 = true := (@span_join (panel 7) 512 0 512 (@span_join (panel 7) 256 0 256 (@span_join (panel 7) 128 0 128 (@span_join (panel 7) 64 0 64 block7_0 block7_64) (@span_join (panel 7) 64 128 64 block7_128 block7_192)) (@span_join (panel 7) 128 256 128 (@span_join (panel 7) 64 256 64 block7_256 block7_320) (@span_join (panel 7) 64 384 64 block7_384 block7_448))) (@span_join (panel 7) 256 512 256 (@span_join (panel 7) 128 512 128 (@span_join (panel 7) 64 512 64 block7_512 block7_576) (@span_join (panel 7) 64 640 64 block7_640 block7_704)) (@span_join (panel 7) 128 768 128 (@span_join (panel 7) 64 768 64 block7_768 block7_832) (@span_join (panel 7) 64 896 64 block7_896 block7_960))))
set_option maxHeartbeats 50000000 in
lemma block8_0 : span (panel 8) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_64 : span (panel 8) 64 64 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_128 : span (panel 8) 64 128 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_192 : span (panel 8) 64 192 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_256 : span (panel 8) 64 256 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_320 : span (panel 8) 64 320 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_384 : span (panel 8) 64 384 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_448 : span (panel 8) 64 448 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_512 : span (panel 8) 64 512 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_576 : span (panel 8) 64 576 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_640 : span (panel 8) 64 640 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_704 : span (panel 8) 64 704 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_768 : span (panel 8) 64 768 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_832 : span (panel 8) 64 832 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_896 : span (panel 8) 64 896 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma block8_960 : span (panel 8) 64 960 = true := by decide +kernel
lemma good8 : span (panel 8) 1024 0 = true := (@span_join (panel 8) 512 0 512 (@span_join (panel 8) 256 0 256 (@span_join (panel 8) 128 0 128 (@span_join (panel 8) 64 0 64 block8_0 block8_64) (@span_join (panel 8) 64 128 64 block8_128 block8_192)) (@span_join (panel 8) 128 256 128 (@span_join (panel 8) 64 256 64 block8_256 block8_320) (@span_join (panel 8) 64 384 64 block8_384 block8_448))) (@span_join (panel 8) 256 512 256 (@span_join (panel 8) 128 512 128 (@span_join (panel 8) 64 512 64 block8_512 block8_576) (@span_join (panel 8) 64 640 64 block8_640 block8_704)) (@span_join (panel 8) 128 768 128 (@span_join (panel 8) 64 768 64 block8_768 block8_832) (@span_join (panel 8) 64 896 64 block8_896 block8_960))))
theorem closed : ∀ s i, i < count s → ck s (board s i) = true := by
  intro s i hi
  by_cases h7 : s=7
  · subst s
    exact span_ok good7 i (Nat.zero_le _) hi
  by_cases h8 : s=8
  · subst s
    exact span_ok good8 i (Nat.zero_le _) hi
  simp [count,h7,h8] at hi
def rho (ys : List Nat) : List Nat :=
  match fld 0x601f980029169dbd 1 (bsr 0xf850a4d4f75c4219f66a85edf192b1c8f10b3d10f02621c1ea560623e90f1b50e55cc3f5e54b2f93ddd4ff26d8f36f54d4d49ed1d2f67d14d231283fd0ccea2fd0880740ccdb0224bc1e371bbbb2cc41bb977ba8b495dd75b24eca81adbe6ec1abc6d4e4aad227489fc673cb9b9d6f459b57dc8e99b8f581999c8f3592bbc11f91e295a38fd552108fd0d8ef8c393d7f873364d67a3860b979cacf55763be7b2742847757231c5d16d7e8955698f92135b61fc905a0e96be59374dbc55a040b854f78f74543a82f94f7260614b9bce66449564e73bb12cbe2e4efcb826dacc5c1f1987801e19b624116dda8f10f4dc3b0cfcfabb07417c29061259210149de88 32 (hk ys) 7 0 64) with
  | 1 => vals.map (fun r => fld 0x12e0000192bd00000000000000000000000010b0039d529d0000001210000190b9004c59c8c662f8542300000010000365649a003f16a785a15832060000001200000000b800000010e003ad569e0000000ff003615099003b9606a56920160300492447f002ed741f0045d847c60ab84c1d0038202666d8e93600002c54664510dc1000 9 r)
  | _ => []
def B (i : Nat) := mv (mask 153) (fld 0xe20f51e61505f62104e40e42e21400503e30e60f42504f30f52f31f23f20f40e41106105f21f10402e62506401000e10e31e51f41404103 12 i) inputs
def I (ys : List Nat) := bsr 0xf850a4d4f192b1c8f10b3d10f02621c1ea560623e90f1b50e55cc3f5e54b2f93ddd4ff26ccdb0224bc1e371bb495dd75b24eca81adbe6ec1abc6d4e4aad227489fc673cb9b9d6f459b57dc8e99b8f581999c8f3592bbc11f91e295a38fd552108c393d7f7a3860b979cacf55742847757231c5d16d7e89555b61fc9055a040b8543a82f94f7260612e4efcb81e19b62406125921 32 (hk ys) 6 0 37
def test (i : Nat) := ck 10 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 153 (cutBoard 10 inputs B) (cutCount 10 37) (fun _ => I) (rowOrient 153 rho) scores 11 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 1 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z1 : span test 1 1 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z2 : span test 1 2 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z3 : span test 1 3 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z4 : span test 1 4 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z5 : span test 1 5 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z6 : span test 1 6 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z7 : span test 1 7 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z8 : span test 1 8 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z9 : span test 1 9 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z10 : span test 1 10 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z11 : span test 1 11 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z12 : span test 1 12 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z13 : span test 1 13 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z14 : span test 1 14 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z15 : span test 1 15 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z16 : span test 1 16 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z17 : span test 1 17 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z18 : span test 1 18 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z19 : span test 1 19 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z20 : span test 1 20 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z21 : span test 1 21 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z22 : span test 1 22 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z23 : span test 1 23 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z24 : span test 1 24 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z25 : span test 1 25 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z26 : span test 1 26 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z27 : span test 1 27 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z28 : span test 1 28 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z29 : span test 1 29 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z30 : span test 1 30 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z31 : span test 1 31 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z32 : span test 1 32 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z33 : span test 1 33 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z34 : span test 1 34 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z35 : span test 1 35 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z36 : span test 1 36 = true := by decide +kernel
lemma regionOK : span test 37 0 = true := (@span_join test 18 0 19 (@span_join test 9 0 9 (@span_join test 4 0 5 (@span_join test 2 0 2 (@span_join test 1 0 1 z0 z1) (@span_join test 1 2 1 z2 z3)) (@span_join test 2 4 3 (@span_join test 1 4 1 z4 z5) (@span_join test 1 6 2 z6 (@span_join test 1 7 1 z7 z8)))) (@span_join test 4 9 5 (@span_join test 2 9 2 (@span_join test 1 9 1 z9 z10) (@span_join test 1 11 1 z11 z12)) (@span_join test 2 13 3 (@span_join test 1 13 1 z13 z14) (@span_join test 1 15 2 z15 (@span_join test 1 16 1 z16 z17))))) (@span_join test 9 18 10 (@span_join test 4 18 5 (@span_join test 2 18 2 (@span_join test 1 18 1 z18 z19) (@span_join test 1 20 1 z20 z21)) (@span_join test 2 22 3 (@span_join test 1 22 1 z22 z23) (@span_join test 1 24 2 z24 (@span_join test 1 25 1 z25 z26)))) (@span_join test 5 27 5 (@span_join test 2 27 3 (@span_join test 1 27 1 z27 z28) (@span_join test 1 29 2 z29 (@span_join test 1 30 1 z30 z31))) (@span_join test 2 32 3 (@span_join test 1 32 1 z32 z33) (@span_join test 1 34 2 z34 (@span_join test 1 35 1 z35 z36))))))
theorem finiteCheck : ¬NatRun (mask 153) (goal 153) 11 inputs :=
  symCutRoot (rowOrient_sound rho) roof (fun i hi => checkpointCheck_sound closed (span_ok regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 12 ≤ t := by
  refine proveAtCap 7 153 11 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finiteCheck

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
