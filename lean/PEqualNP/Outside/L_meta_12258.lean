import PEqualNP.Defs
import Mathlib.Data.Tree.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
namespace PEqualNP.Outside.L_meta_12258_aux.Elim

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

end PEqualNP.Outside.L_meta_12258_aux.Elim
namespace PEqualNP.Outside.L_meta_12258_aux.FalseBase

abbrev Forest := Nat → Nat × Nat

def unpack (packed width index : Nat) : Nat :=
  (packed >>> (width * index)) &&& ((1 <<< width) - 1)

def decodeNode (parentWidth width packed index : Nat) : Nat × Nat :=
  let entry := unpack packed width index
  (entry &&& ((1 <<< parentWidth) - 1), entry >>> parentWidth)

def treeBlock (start count : Nat) (check : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ next i => check i && next (i + 1)) count) start

theorem treeBlock_at {start count i : Nat} {check : Nat → Bool}
    (h : treeBlock start count check = true) (lo : start ≤ i) (hi : i < start + count) :
    check i = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    change (check start && treeBlock (start + 1) count check) = true at h
    rcases Bool.and_eq_true_iff.mp h with ⟨here, rest⟩
    by_cases eq : i = start
    · simpa [eq] using here
    · exact ih rest (by omega) (by omega)

theorem treeBlock_merge {start left right : Nat} {check : Nat → Bool}
    (a : treeBlock start left check = true)
    (b : treeBlock (start + left) right check = true) :
    treeBlock start (left + right) check = true := by
  induction left generalizing start with
  | zero => simpa using b
  | succ left ih =>
    rw [Nat.succ_add]
    change (check start && treeBlock (start + 1) (left + right) check) = true
    change (check start && treeBlock (start + 1) left check) = true at a
    rcases Bool.and_eq_true_iff.mp a with ⟨here, rest⟩
    exact Bool.and_eq_true_iff.mpr ⟨here, ih rest (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b)⟩

abbrev Word := Nat
abbrev RowState := Nat × List Word × List (Word × Word × Word)
abbrev CutCheck := RowState → Bool

def rootWords (base : List Word) (token : Nat) : List Word :=
  List.rec (motive := fun _ => Nat → List Word) (fun _ => [])
    (fun word _ next bits =>
      let tail := next (bits >>> 1)
      if bits &&& 1 == 0 then tail else word :: tail) base token

def rootState (base : List Word) (fuel token : Nat) : RowState :=
  (fuel, rootWords base token, [])

def insertWord (w : Word) (ws : List Word) : List Word :=
  List.rec [w] (fun a tail next => if w ≤ a then w :: a :: tail else a :: next) ws

def childState (mask token : Nat) (state : RowState) : Option RowState :=
  let (fuel, ws, history) := state
  let keep := token % 4
  let op := (token / 4) % 3
  let a := token / (4 * 3 * 64)
  let b := (token / (4 * 3)) % 64
  if fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let w := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
    if w == 0 || w == mask || ws.contains w then none
    else
      let rest := if keep.testBit 0 then ws else ws.erase x
      let rest := if op == 2 || keep.testBit 1 then rest else rest.erase y
      some (fuel - 1, insertWord w rest, (w, x, y) :: history)

def gateToken (a b op keep : Nat) : Nat := ((a * 64 + b) * 3 + op) * 4 + keep

abbrev Bound := Nat × List Word × Nat × Word

def stockWord (mask : Nat) (stock : List Word) (needed : List Word) (word : Word) : List Word :=
  let v := word &&& mask
  if v == 0 || v == mask || stock.contains v || needed.contains v then needed
  else v :: needed

def recipeStart (mask : Nat) (stock words : List Word) : List Word :=
  (List.rec (motive := fun _ => List Word → List Word) id
    (fun word _ next seen => next (stockWord mask stock seen word)) words) []

def recipeClosure (mask : Nat) (stock : List Word) (history : List (Word × Word × Word))
    (start : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) id
    (fun (out, a, b) _ next seen =>
      next (if seen.contains (out &&& mask) then stockWord mask stock (stockWord mask stock seen a) b else seen))
    history start

def recipeNeeded (mask : Nat) (stock words : List Word) (history : List (Word × Word × Word)) :
    List Word :=
  recipeClosure mask stock history (recipeStart mask stock words)

def maskFlat (mask word : Nat) : Bool :=
  let v := word &&& mask
  v == 0 || v == mask

def flatCount (mask : Nat) (words : List Word) : Nat :=
  List.rec 0 (fun word _ count => if maskFlat mask word then count + 1 else count) words

def availableB (mask : Nat) (bank : List Word) (w : Word) : Bool :=
  w == 0 || w == mask || bank.contains w

def recipeGate (mask : Nat) (bank : List Word) (w a b : Word) : Bool :=
  availableB mask bank a &&
    ((w == mask ^^^ a) || (availableB mask bank b && (w == a &&& b || w == a ||| b)))

def replayRecipes (mask : Nat) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := w &&& mask
      if needed.contains v && !availableB mask bank v &&
          recipeGate mask bank v (a &&& mask) (b &&& mask) then
        v :: next (v :: bank)
      else next bank) recipes bank

def boundCloses (target : Word) (state : RowState) (bound : Bound) : Bool :=
  let (mask, stock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    (let remaining := fuel - flatCount mask ws
     if remaining < lower then
       let start := recipeStart mask stock ws
       if start.length + remaining < lower then
         let needed := recipeClosure mask stock history start
         if needed.length + remaining < lower then
           let replay := replayRecipes mask needed history.reverse stock
           (replay.length + remaining < lower) &&
             ws.all (fun w => availableB mask (replay ++ stock) (w &&& mask))
         else false
       else false
     else false)

def knownCloses (target : Word) (bounds : List Bound) (state : RowState) : Bool :=
  List.rec false (fun bound _ later => boundCloses target state bound || later) bounds

def AvailableWord (mask : Nat) (bank : List Word) (word : Word) : Prop :=
  word = 0 ∨ word = mask ∨ word ∈ bank

def GateWord (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  (∃ a, AvailableWord mask bank a ∧ out = mask ^^^ a) ∨
  (∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b))

def WordBuilds (mask : Nat) (roots : List Word) : List Word → Prop
  | [] => True
  | w :: ws => GateWord mask roots w ∧ WordBuilds mask (w :: roots) ws

def Lower (mask : Nat) (roots : List Word) (target : Word) (minimum : Nat) : Prop :=
  ∀ values, WordBuilds mask roots values →
    AvailableWord mask (values ++ roots) target → minimum ≤ values.length

def Known (bounds : List Bound) : Prop :=
  ∀ bound ∈ bounds, Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1

theorem restrictWord (mask : Nat) (word : Word) : word &&& mask &&& mask = word &&& mask := by
  simp

theorem projectGate {mask cut : Nat} (submask : mask &&& cut = cut)
    {roots : List Word} {out : Word} (gate : GateWord mask roots out) :
    GateWord cut (roots.map (· &&& cut)) (out &&& cut) := by
  have av {word : Word} (ha : AvailableWord mask roots word) :
      AvailableWord cut (roots.map (· &&& cut)) (word &&& cut) := by
    rcases ha with rfl | rfl | hm
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl submask)
    · exact Or.inr (Or.inr (List.mem_map_of_mem hm))
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq | eq⟩
  · refine Or.inl ⟨a &&& cut, av ha, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    have cutAt := congrArg (fun n : Nat => n.testBit i) submask
    simp only [Nat.testBit_and, Nat.testBit_xor] at cutAt ⊢
    cases h : cut.testBit i
    · simp
    · simp [h] at cutAt
      simp [cutAt]
  · subst out
    refine Or.inr ⟨a &&& cut, b &&& cut, av ha, av hb, Or.inl ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    cases cut.testBit i <;> simp
  · subst out
    refine Or.inr ⟨a &&& cut, b &&& cut, av ha, av hb, Or.inr ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases cut.testBit i <;> simp

theorem projectBuilds {mask cut : Nat} (submask : mask &&& cut = cut)
    {roots values : List Word} (builds : WordBuilds mask roots values) :
    WordBuilds cut (roots.map (· &&& cut)) (values.map (· &&& cut)) := by
  induction values generalizing roots with
  | nil => trivial
  | cons w ws ih =>
    exact ⟨projectGate submask builds.1, ih builds.2⟩

theorem availableWeaken {mask : Nat} {small big : List Word} {w : Word}
    (sub : ∀ x ∈ small, AvailableWord mask big x)
    (av : AvailableWord mask small w) : AvailableWord mask big w := by
  rcases av with rfl | rfl | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact sub w h

theorem gateWeaken {mask : Nat} {small big : List Word} {out : Word}
    (sub : ∀ x ∈ small, AvailableWord mask big x)
    (gate : GateWord mask small out) : GateWord mask big out := by
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq⟩
  · exact Or.inl ⟨a, availableWeaken sub ha, rfl⟩
  · exact Or.inr ⟨a, b, availableWeaken sub ha, availableWeaken sub hb, eq⟩

theorem extendKnown {bound : Bound} {bounds : List Bound}
    (old : Known bounds)
    (new : Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1) :
    Known (bound :: bounds) := by
  intro x h
  rcases List.mem_cons.mp h with rfl | h
  · exact new
  · exact old _ h

def AgreesAt (i j : Nat) (word : Word) : Prop :=
  word.testBit i = word.testBit j

theorem agreesAvailable {i j mask : Nat} {bank : List Word} {word : Word}
    (m : AgreesAt i j mask) (all : ∀ w ∈ bank, AgreesAt i j w)
    (av : AvailableWord mask bank word) : AgreesAt i j word := by
  rcases av with rfl | rfl | h
  · simp [AgreesAt]
  · exact m
  · exact all _ h

theorem agreesGate {i j mask : Nat} {bank : List Word} {word : Word}
    (m : AgreesAt i j mask) (all : ∀ w ∈ bank, AgreesAt i j w)
    (gate : GateWord mask bank word) : AgreesAt i j word := by
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq | eq⟩
  · simp only [AgreesAt, Nat.testBit_xor] at m ⊢
    rw [m, show a.testBit i = a.testBit j from agreesAvailable m all ha]
  · subst word
    simp only [AgreesAt, Nat.testBit_and]
    rw [show a.testBit i = a.testBit j from agreesAvailable m all ha,
      show b.testBit i = b.testBit j from agreesAvailable m all hb]
  · subst word
    simp only [AgreesAt, Nat.testBit_or]
    rw [show a.testBit i = a.testBit j from agreesAvailable m all ha,
      show b.testBit i = b.testBit j from agreesAvailable m all hb]

theorem agreesBuilds {i j mask : Nat} {roots values : List Word} {word : Word}
    (m : AgreesAt i j mask) (all : ∀ w ∈ roots, AgreesAt i j w)
    (builds : WordBuilds mask roots values)
    (av : AvailableWord mask (values ++ roots) word) : AgreesAt i j word := by
  induction values generalizing roots with
  | nil => exact agreesAvailable m all av
  | cons v vs ih =>
    have vg := agreesGate m all builds.1
    have hc : ∀ w ∈ v :: roots, AgreesAt i j w := by
      intro w h
      rcases List.mem_cons.mp h with rfl | mem
      · exact vg
      · exact all _ mem
    apply ih hc builds.2
    rcases av with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by
        simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using h))

theorem buildsMap {m n : Nat} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots : List Word} {bank : List Word}
    (supply : ∀ v ∈ roots, AvailableWord n bank (f v))
    {values : List Word} (h : WordBuilds m roots values) :
    WordBuilds n bank (values.map f) := by
  have av {bank roots : List Word} {v : Word}
      (src : ∀ v ∈ roots, AvailableWord n bank (f v))
      (h : AvailableWord m roots v) : AvailableWord n bank (f v) := by
    rcases h with rfl | rfl | hv
    · exact Or.inl zero
    · exact Or.inr (Or.inl ones)
    · exact src _ hv
  induction values generalizing roots bank with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨?_, ih ?_ h.2⟩
    · rcases h.1 with ⟨a, ha, eq⟩ | ⟨a, b, ha, hb, eq | eq⟩
      · exact Or.inl ⟨f a, av supply ha, eq ▸ invert a⟩
      · exact Or.inr ⟨f a, f b, av supply ha, av supply hb, Or.inl (eq ▸ meet a b)⟩
      · exact Or.inr ⟨f a, f b, av supply ha, av supply hb, Or.inr (eq ▸ join a b)⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inr (Or.inr List.mem_cons_self)
      · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_cons_of_mem _ hx))) (supply _ hw)

theorem lowerMap {m n : Nat} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots bank : List Word} {goal : Word} {minimum : Nat}
    (supply : ∀ v ∈ roots, AvailableWord n bank (f v))
    (bound : Lower n bank (f goal) minimum) :
    Lower m roots goal minimum := by
  intro values build hit
  suffices AvailableWord n (values.map f ++ bank) (f goal) by
    simpa using bound (values.map f) (buildsMap f zero ones invert meet join supply build) this
  rcases hit with rfl | rfl | mem
  · exact Or.inl zero
  · exact Or.inr (Or.inl ones)
  · rcases List.mem_append.mp mem with hv | hr
    · exact Or.inr (Or.inr (List.mem_append_left _ (List.mem_map_of_mem hv)))
    · exact availableWeaken (fun w hw => Or.inr (Or.inr (List.mem_append_right _ hw))) (supply _ hr)

theorem buildsWeaken {mask : Nat} {small big values : List Word}
    (supply : ∀ w ∈ small, AvailableWord mask big w) (build : WordBuilds mask small values) :
    WordBuilds mask big values := by
  induction values generalizing small big with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gateWeaken supply build.1, ih ?_ build.2⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inr (Or.inr List.mem_cons_self)
    · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_cons_of_mem _ hx))) (supply _ hw)

theorem gateBuildsIndex {mask : Nat} (bank values : List Word)
    (legal : ∀ i, i < values.length →
      GateWord mask (bank ++ values.take i) (values.getD i 0)) :
    WordBuilds mask bank values := by
  induction values generalizing bank with
  | nil => trivial
  | cons v vs ih =>
    have first := legal 0 (by simp)
    have tail : ∀ i, i < vs.length →
        GateWord mask ((bank ++ [v]) ++ vs.take i) (vs.getD i 0) := by
      intro i hi
      simpa [List.take_succ_cons, List.append_assoc] using
        legal (i + 1) (by simpa using hi)
    refine ⟨by simpa using first, buildsWeaken ?_ (ih (bank ++ [v]) tail)⟩
    intro w mem
    exact Or.inr (Or.inr (by simpa [or_comm] using mem))

theorem lowerWeaken {mask goal minimum : Nat} {old new : List Word}
    (lower : Lower mask old goal minimum) (supply : ∀ w ∈ new, AvailableWord mask old w) :
    Lower mask new goal minimum := by
  apply lowerMap id rfl rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) supply
  exact lower

def properWord (mask word : Word) : Prop := word ≠ 0 ∧ word ≠ mask

def binWord (isOr : Bool) (a b : Word) : Word :=
  if isOr then a ||| b else a &&& b

theorem binWord_comm (d : Bool) (a b : Word) : binWord d a b = binWord d b a := by
  cases d <;> simp [binWord, Nat.land_comm, Nat.lor_comm]

variable {mask : Nat} {target : Word}

def LiveWord (mask : Nat) (target : Word) : Nat → Nat → Finset (Word) → Prop
  | 0,t,S => t=0 ∧ S={target} ∧ properWord mask target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset (Word)) (a : Word), t=u+1 ∧ S=insert a U ∧ properWord mask a ∧
      (mask ^^^ a) ∉ insert a U ∧ LiveWord mask target k u (insert ((mask ^^^ a)) U)) ∨
    (∃ (U : Finset (Word)) (a b : Word) (d : Bool), S=insert a (insert b U) ∧ properWord mask a ∧ properWord mask b ∧ a ≠ b ∧
      binWord d a b ∉ insert a (insert b U) ∧ LiveWord mask target k t (insert (binWord d a b) U))
theorem LiveWord.stop {target : Word} (hp : properWord mask target) : LiveWord mask target 0 0 {target} := ⟨rfl,rfl,hp⟩
theorem LiveWord.unary {target : Word} {k t : Nat} {U : Finset (Word)} {a : Word} (ha : properWord mask a)
    (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)) :
    LiveWord mask target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem LiveWord.binary {target : Word} {k t : Nat} {U : Finset (Word)} {a b : Word} {d : Bool}
    (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
    (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)) :
    LiveWord mask target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem LiveWord.ind {target : Word} {motive : ∀ (k t : Nat) (S : Finset (Word)), LiveWord mask target k t S → Prop}
    (stop : ∀ (hp : properWord mask target), motive 0 0 {target} (LiveWord.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset (Word)} {a : Word} (ha : properWord mask a)
      (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)),
      motive k t (insert ((mask ^^^ a)) U) tail → motive (k+1) (t+1) (insert a U) (LiveWord.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset (Word)} {a b : Word} {d : Bool}
      (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
      (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)),
      motive k t (insert (binWord d a b) U) tail →
      motive (k+1) t (insert a (insert b U)) (LiveWord.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset (Word)} (h : LiveWord mask target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

theorem liveWordProper {k t S} (h : LiveWord mask target k t S) : ∀ a ∈ S, properWord mask a := by
  induction h using LiveWord.ind with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

theorem liveWordSize {k t S} (h : LiveWord mask target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using LiveWord.ind with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : (mask ^^^ a) ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : binWord d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

def wordRep (mask : Nat) (ws : List Word) (w : Word) : Prop :=
  w ∈ ws ∨ ¬properWord mask w

def wordWitness (mask : Nat) (ws : List Word) (w : Word) : Prop :=
  (∃ a ∈ ws, properWord mask a ∧ w = mask ^^^ a) ∨
  ∃ d a b, a ∈ ws ∧ b ∈ ws ∧ properWord mask a ∧ properWord mask b ∧
    a ≠ b ∧ w = binWord d a b

theorem pullWord {w : List (Word)} {z : Word} {k t S} (h : LiveWord mask target k t S)
    (hz : wordRep mask w z ∨ wordWitness mask w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ LiveWord mask target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := liveWordProper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase ((mask ^^^ a))
        have ht : LiveWord mask target k t (insert ((mask ^^^ a)) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : (mask ^^^ a) ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,LiveWord.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (binWord d a b)
        have ht : LiveWord mask target k t (insert (binWord d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : binWord d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,LiveWord.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

def Masked (mask word : Nat) : Prop := word &&& mask = word

theorem maskedAvailable {bank : List Word} {word : Word}
    (all : ∀ w ∈ bank, Masked mask w) (aw : AvailableWord mask bank word) :
    Masked mask word := by
  rcases aw with rfl | rfl | hw
  · simp [Masked]
  · simp [Masked]
  · exact all _ hw

theorem maskedGate {bank : List Word} {out : Word}
    (all : ∀ w ∈ bank, Masked mask w) (g : GateWord mask bank out) :
    Masked mask out := by
  rcases g with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, ea | ea⟩
  · have h := projectGate (mask := mask) (cut := mask) (by simp)
      (roots := bank) (out := mask ^^^ a) (Or.inl ⟨a, ha, rfl⟩)
    have ma := maskedAvailable all ha
    unfold Masked at ma ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bit := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and, Nat.testBit_xor] at bit ⊢
    cases hm : mask.testBit i <;> simp_all
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    simp only [Masked] at ma mb ⊢
    rw [Nat.land_assoc, mb]
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    unfold Masked at ma mb ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bitA := congrArg (fun n : Nat => n.testBit i) ma
    have bitB := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at bitA bitB ⊢
    cases hm : mask.testBit i <;> simp_all

def binaryWitness (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  ∃ d a b, a ∈ bank ∧ b ∈ bank ∧ properWord mask a ∧ properWord mask b ∧
    a ≠ b ∧ out = binWord d a b

theorem classifyBinary {bank : List Word}
    (all : ∀ w ∈ bank, Masked mask w) (d : Bool) {a b : Word}
    (ha : AvailableWord mask bank a) (hb : AvailableWord mask bank b) :
    wordRep mask bank (binWord d a b) ∨ binaryWitness mask bank (binWord d a b) := by
  have c0 : wordRep mask bank 0 := Or.inr fun h => h.1 rfl
  have cm : wordRep mask bank mask := Or.inr fun h => h.2 rfl
  have classify {w : Word} (hw : AvailableWord mask bank w) :
      w = 0 ∨ w = mask ∨ w ∈ bank ∧ properWord mask w := by
    by_cases zh : w = 0
    · exact Or.inl zh
    by_cases mh : w = mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh, zh, mh⟩)
  have ma : a &&& mask = a := maskedAvailable all ha
  have mb : b &&& mask = b := maskedAvailable all hb
  have absorbA : a ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  have absorbB : b ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  rcases classify ha with rfl | hma | ⟨ha', pa⟩
  · rw [binWord_comm]
    cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord, hz] using c0)
      · exact Or.inl (by simpa [binWord, hm] using cm)
      · exact Or.inl (by simpa [binWord, wordRep] using
          (Or.inl hv : wordRep mask bank b))
  · rw [hma, binWord_comm]
    cases d
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord, hz] using c0)
      · exact Or.inl (by simpa [binWord, hm] using cm)
      · exact Or.inl (by simpa [binWord, mb, wordRep] using
          (Or.inl hv : wordRep mask bank b))
    · exact Or.inl (by simpa [binWord, absorbB] using cm)
  rcases classify hb with rfl | hmb | ⟨hb', pb⟩
  · cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · exact Or.inl (by simpa [binWord, wordRep] using
        (Or.inl ha' : wordRep mask bank a))
  · rw [hmb]
    cases d
    · exact Or.inl (by simpa [binWord, ma, wordRep] using
        (Or.inl ha' : wordRep mask bank a))
    · exact Or.inl (by simpa [binWord, absorbA] using cm)
  by_cases eq : a = b
  · subst b
    cases d <;> exact Or.inl (by simpa [binWord, wordRep] using
      (Or.inl ha' : wordRep mask bank a))
  exact Or.inr ⟨d, a, b, ha', hb', pa, pb, eq, rfl⟩

theorem classifyWord {bank : List Word} {out : Word}
    (all : ∀ w ∈ bank, Masked mask w) (gate : GateWord mask bank out) :
    wordRep mask bank out ∨ wordWitness mask bank out := by
  have c0 : wordRep mask bank 0 := Or.inr fun h => h.1 rfl
  have cm : wordRep mask bank mask := Or.inr fun h => h.2 rfl
  have classify {w : Word} (hw : AvailableWord mask bank w) :
      w = 0 ∨ w = mask ∨ w ∈ bank ∧ properWord mask w := by
    by_cases zh : w = 0
    · exact Or.inl zh
    by_cases mh : w = mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh, zh, mh⟩)
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, h | h⟩
  · rcases classify ha with rfl | hma | ⟨hm, hp⟩
    · exact Or.inl (by simpa using cm)
    · exact Or.inl (by simpa [hma] using c0)
    · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
  · subst out; exact (classifyBinary all false ha hb).imp id Or.inr
  · subst out; exact (classifyBinary all true ha hb).imp id Or.inr

theorem extractWordLive {roots values : List Word}
    (all : ∀ w ∈ roots, Masked mask w) (builds : WordBuilds mask roots values)
    (hit : AvailableWord mask (values ++ roots) target) (p : properWord mask target) :
    ∃ k t S, k ≤ values.length ∧ LiveWord mask target k t S ∧ ∀ w ∈ S, w ∈ roots := by
  have hm := (hit.resolve_left p.1).resolve_left p.2
  induction values generalizing roots with
  | nil =>
    exact ⟨0, 0, {target}, Nat.zero_le _, LiveWord.stop p, by simpa using hm⟩
  | cons w ws ih =>
    have next : ∀ v ∈ w :: roots, Masked mask v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact maskedGate all builds.1
      · exact all _ hv
    have ht : AvailableWord mask (ws ++ w :: roots) target := by
      exact Or.inr (Or.inr (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hm))
    obtain ⟨k, t, S, hk, live, sub⟩ :=
      ih next builds.2 ht ((ht.resolve_left p.1).resolve_left p.2)
    have available : ∀ v ∈ S, v ∈ roots ++ [w] := by
      intro v h
      simpa [or_comm] using sub v h
    obtain ⟨k', t', S', hk', hl, hsub⟩ := pullWord live (classifyWord all builds.1) available
    exact ⟨k', t', S', by simp only [List.length_cons]; omega, hl, hsub⟩

theorem insertWordMem {x w : Word} {ws : List Word} :
    x ∈ insertWord w ws ↔ x = w ∨ x ∈ ws := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change x ∈ (if w ≤ a then w :: a :: tail else a :: insertWord w tail) ↔ _
    split <;> simp [ih, or_assoc, or_left_comm]

theorem insertWordNodup {w : Word} {ws : List Word} (nd : ws.Nodup) (fresh : w ∉ ws) :
    (insertWord w ws).Nodup := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change (if w ≤ a then w :: a :: tail else a :: insertWord w tail).Nodup
    split
    · exact List.nodup_cons.mpr ⟨fresh, nd⟩
    have hn := List.nodup_cons.mp nd
    have hnot : w ≠ a ∧ w ∉ tail := by simpa using fresh
    exact List.nodup_cons.mpr ⟨by simp [insertWordMem, hnot.1.symm, hn.1], ih hn.2 hnot.2⟩

theorem insertWordSet (w : Word) (ws : List Word) :
    (insertWord w ws).toFinset = insert w ws.toFinset := by
  ext x
  simp [insertWordMem]

theorem eraseWordSet {ws : List Word} (nd : ws.Nodup) (w : Word) :
    (ws.erase w).toFinset = ws.toFinset.erase w := by
  ext x
  simp [nd.mem_erase_iff, and_comm]

theorem gateTokenFields {a b op keep : Nat} (hb : b < 64) (ho : op < 3) (hk : keep < 4) :
    gateToken a b op keep % 4 = keep ∧
    gateToken a b op keep / 4 % 3 = op ∧
    gateToken a b op keep / (4 * 3 * 64) = a ∧
    gateToken a b op keep / (4 * 3) % 64 = b := by
  unfold gateToken
  omega

def keepWord (save : Bool) (w : Word) (ws : List Word) : List Word :=
  if save then ws else ws.erase w

theorem keepNodup {ws : List Word} (nd : ws.Nodup) (save : Bool) (w : Word) :
    (keepWord save w ws).Nodup := by
  cases save
  · exact nd.erase _
  · exact nd

theorem keepSubset (save : Bool) (w : Word) (ws : List Word) :
    ∀ v ∈ keepWord save w ws, v ∈ ws := by
  cases save
  · exact fun _ h => List.mem_of_mem_erase h
  · exact fun _ h => h

theorem keepSet {ws : List Word} (nd : ws.Nodup) {w : Word} {U : Finset Word}
    (eq : ws.toFinset = insert w U) :
    (keepWord (decide (w ∈ U)) w ws).toFinset = U := by
  by_cases hw : w ∈ U
  · simp [keepWord, hw, eq, Finset.insert_eq_of_mem hw]
  · simp [keepWord, hw, eraseWordSet nd, eq]

theorem keepPairSet {ws : List Word} (nd : ws.Nodup) {a b : Word} {U : Finset Word}
    (ab : a ≠ b) (eq : ws.toFinset = insert a (insert b U)) :
    (keepWord (decide (b ∈ U)) b (keepWord (decide (a ∈ U)) a ws)).toFinset = U := by
  have x : decide (a ∈ insert b U) = decide (a ∈ U) := by simp [ab]
  have h := keepSet nd eq
  rw [x] at h
  exact keepSet (keepNodup nd _ _) h

theorem getWord {ws : List Word} {x : Word} (h : x ∈ ws) :
    ws.getD (ws.idxOf x) 0 = x := by
  have inb := List.idxOf_lt_length_iff.mpr h
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inb] using
    List.getElem_idxOf inb

theorem unaryChild {mask fuel a : Nat} {ws : List Word}
    {history : List (Word × Word × Word)} {x : Word} {keep : Nat}
    (ha : a < ws.length) (ha64 : a < 64) (hf : fuel ≠ 0) (hk : keep < 2)
    (hx : ws.getD a 0 = x) (p : properWord mask (mask ^^^ x)) (fresh : mask ^^^ x ∉ ws) :
    childState mask (gateToken a a 2 keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (mask ^^^ x) (keepWord (keep.testBit 0) x ws),
        (mask ^^^ x, x, x) :: history) := by
  obtain ⟨ke, op, aa, bb⟩ := gateTokenFields (a := a) ha64 (by decide : 2 < 3) (by omega : keep < 4)
  simp only [childState, ke, op, aa, bb, hx]
  simp [hf, Nat.not_le_of_lt ha, Nat.not_le_of_lt hk, p.1, p.2, fresh, keepWord]

theorem binaryChild {mask fuel a b : Nat} {ws : List Word}
    {history : List (Word × Word × Word)} {x y : Word} {keep : Nat}
    (d : Bool) (hab : a < b) (hb : b < ws.length) (hb64 : b < 64)
    (hf : fuel ≠ 0) (hk : keep < 4)
    (hx : ws.getD a 0 = x) (hy : ws.getD b 0 = y)
    (p : properWord mask (binWord d x y)) (fresh : binWord d x y ∉ ws) :
    childState mask (gateToken a b (if d then 1 else 0) keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (binWord d x y)
        (keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)),
        (binWord d x y, x, y) :: history) := by
  have oh : (if d then 1 else 0) < 3 := by cases d <;> decide
  obtain ⟨ke, op, aa, bb⟩ := gateTokenFields (a := a) hb64 oh hk
  simp only [childState, ke, op, aa, bb, hx, hy]
  cases d <;>
    simp_all [Nat.not_le_of_lt hab, Nat.not_le_of_lt hb, keepWord, binWord, properWord]

def WordViable (mask : Nat) (target : Word) (state : RowState) : Prop :=
  state.2.1.Nodup ∧ ∃ k t, k ≤ state.1 ∧ LiveWord mask target k t state.2.1.toFinset

def HasChild (mask : Nat) (state child : RowState) : Prop :=
  ∃ a b op keep, a < state.2.1.length ∧
    ((a = b ∧ op = 2 ∧ keep < 2) ∨
      (a < b ∧ b < state.2.1.length ∧ op < 2 ∧ keep < 4)) ∧
    childState mask (gateToken a b op keep) state = some child

theorem unaryProgress {mask fuel k t : Nat} {x target : Word} {U : Finset Word} {ws : List Word}
    {history : List (Word × Word × Word)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x U) (fresh : mask ^^^ x ∉ insert x U)
    (tail : LiveWord mask target k t (insert (mask ^^^ x) U)) :
    ∃ child, HasChild mask (fuel, ws, history) child ∧ WordViable mask target child := by
  let a := ws.idxOf x
  have xm : x ∈ ws := by
    rw [← List.mem_toFinset, he]
    simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hx : ws.getD a 0 = x := getWord xm
  have p := liveWordProper tail (mask ^^^ x) (Finset.mem_insert_self _ _)
  let save := decide (x ∈ U)
  let keep := if save then 1 else 0
  have keepLt : keep < 2 := by dsimp [keep]; split <;> decide
  have keepBit : keep.testBit 0 = save := by
    unfold keep
    cases save <;> decide
  have fn : mask ^^^ x ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord save x ws
  let child : RowState := (fuel - 1, insertWord (mask ^^^ x) rest, (mask ^^^ x, x, x) :: history)
  refine ⟨child, ⟨a, a, 2, keep, ha, Or.inl ⟨rfl, rfl, keepLt⟩, ?_⟩, ?_⟩
  · have eq := unaryChild (fuel := fuel) (history := history) ha (by omega) (by omega) keepLt hx p fn
    rw [keepBit] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup nd save x) (fun h => fn (keepSubset save x ws _ h)),
      k, t, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveWord mask target k t (insertWord (mask ^^^ x) rest).toFinset
    rw [insertWordSet, keepSet nd he]
    exact tail

theorem binaryProgress {mask fuel k t : Nat} {x y target : Word} {d : Bool} {U : Finset Word}
    {ws : List Word} {history : List (Word × Word × Word)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x (insert y U)) (xy : x ≠ y)
    (ordered : ws.idxOf x < ws.idxOf y) (fresh : binWord d x y ∉ insert x (insert y U))
    (tail : LiveWord mask target k t (insert (binWord d x y) U)) :
    ∃ child, HasChild mask (fuel, ws, history) child ∧ WordViable mask target child := by
  let a := ws.idxOf x
  let b := ws.idxOf y
  have xm : x ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ym : y ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hb : b < ws.length := List.idxOf_lt_length_iff.mpr ym
  have hab : a < b := ordered
  have hx : ws.getD a 0 = x := getWord xm
  have hy : ws.getD b 0 = y := getWord ym
  let v := binWord d x y
  have p := liveWordProper tail v (Finset.mem_insert_self _ _)
  let saveX := decide (x ∈ U)
  let saveY := decide (y ∈ U)
  let keep := (if saveX then 1 else 0) + (if saveY then 2 else 0)
  have fields : keep < 4 ∧ keep.testBit 0 = saveX ∧ keep.testBit 1 = saveY := by
    unfold keep
    cases saveX <;> cases saveY <;> decide
  obtain ⟨keepLt, bx, by'⟩ := fields
  have fn : v ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord saveY y (keepWord saveX x ws)
  let child : RowState := (fuel - 1, insertWord v rest, (v, x, y) :: history)
  refine ⟨child, ⟨a, b, if d then 1 else 0, keep, ha, Or.inr ⟨hab, hb, ?_, keepLt⟩, ?_⟩, ?_⟩
  · cases d <;> decide
  · have eq := binaryChild (fuel := fuel) (history := history) d hab hb (by omega) (by omega) keepLt hx hy p fn
    rw [bx, by'] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup (keepNodup nd saveX x) saveY y)
      (fun h => fn (keepSubset saveX x ws _ (keepSubset saveY y _ _ h))), k, t, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveWord mask target k t (insertWord v rest).toFinset
    rw [insertWordSet, keepPairSet nd xy he]
    exact tail

theorem wordProgress {mask : Nat} {target : Word} {state : RowState}
    (width : state.2.1.length ≤ 64) (h : WordViable mask target state) :
    target ∈ state.2.1 ∨ ∃ child, HasChild mask state child ∧ WordViable mask target child := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨nd, k, t, cap, live⟩ := h
  cases k with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    left
    change ws.toFinset = {target} at eq
    rw [← List.mem_toFinset, eq]
    simp
  | succ k =>
    right
    rcases live with ⟨u,U,x,_,eq,px,fresh,tail⟩ | ⟨U,x,y,d,eq,px,py,xy,fresh,tail⟩
    · exact unaryProgress nd width cap eq fresh tail
    have xm : x ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have ym : y ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have diff : ws.idxOf x ≠ ws.idxOf y := by
      intro same
      apply xy
      rw [← getWord xm, same, getWord ym]
    by_cases h : ws.idxOf x < ws.idxOf y
    · exact binaryProgress nd width cap eq xy h fresh tail
    · have eq' : ws.toFinset = insert y (insert x U) := by rw [eq, Finset.insert_comm]
      have fresh' : binWord d y x ∉ insert y (insert x U) := by
        rw [binWord_comm d y x, Finset.insert_comm]; exact fresh
      have tail' : LiveWord mask target k t (insert (binWord d y x) U) := by
        rw [binWord_comm d y x]; exact tail
      exact binaryProgress nd width cap eq' xy.symm (by omega) fresh' tail'

theorem rootWordSublist (base : List Word) (token : Nat) : (rootWords base token).Sublist base := by
  induction base generalizing token with
  | nil => exact List.Sublist.slnil
  | cons w ws ih =>
    change (if token &&& 1 == 0 then rootWords ws (token >>> 1)
      else w :: rootWords ws (token >>> 1)).Sublist (w :: ws)
    split
    · exact (ih _).cons _
    · exact (ih _).cons₂ _

theorem rootToken (base : List Word) (S : Finset Word) :
    ∃ token < 2 ^ base.length, (rootWords base token).toFinset = base.toFinset ∩ S := by
  induction base with
  | nil => exact ⟨0, by simp, by simp [rootWords]⟩
  | cons w ws ih =>
    obtain ⟨token, htoken, ih⟩ := ih
    let bit : Nat := if w ∈ S then 1 else 0
    have hbit : bit < 2 := by dsimp [bit]; split <;> decide
    let code := 2 * token + bit
    have low : code &&& 1 = bit := by
      rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      dsimp [code]
      omega
    have high : code >>> 1 = token := by
      rw [Nat.shiftRight_eq_div_pow]
      change code / 2 = token
      dsimp [code]
      omega
    refine ⟨code, ?_, ?_⟩
    · simp only [List.length_cons, pow_succ]
      dsimp [code]
      omega
    · change (if code &&& 1 == 0 then rootWords ws (code >>> 1)
        else w :: rootWords ws (code >>> 1)).toFinset = _
      rw [low, high]
      by_cases hw : w ∈ S
      · simp [bit, hw, ih]
      · simp [bit, hw, ih]

theorem liveAgrees {i j k t : Nat} {S : Finset Word}
    (h : LiveWord mask target k t S) (m : AgreesAt i j mask)
    (all : ∀ w ∈ S, AgreesAt i j w) : AgreesAt i j target := by
  induction h using LiveWord.ind with
  | stop => exact all _ (Finset.mem_singleton_self _)
  | @unary k t U a pa fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp only [AgreesAt, Nat.testBit_xor]
      rw [show mask.testBit i = mask.testBit j from m,
        show a.testBit i = a.testBit j from all a (Finset.mem_insert_self _ _)]
    · exact all _ (Finset.mem_insert_of_mem hw)
  | @binary k t U a b d pa pb ab fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have aa : a.testBit i = a.testBit j := all a (Finset.mem_insert_self _ _)
      have bb : b.testBit i = b.testBit j := all b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      cases d <;> simp [AgreesAt, binWord, Nat.testBit_and, Nat.testBit_or, aa, bb]
    · exact all _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))

theorem positiveInMask {i : Nat} (mt : Masked mask target) (ht : target.testBit i = true) :
    mask.testBit i = true := by
  have h := congrArg (fun n : Nat => n.testBit i) mt
  simpa [Nat.testBit_and, ht] using h

variable {rows : Nat}

def fullMask (rows : Nat) : Nat := 2 ^ rows - 1

theorem toNatMasked (v : BitVec rows) : Masked (fullMask rows) v.toNat := by
  unfold Masked fullMask
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt v.isLt]

theorem notNat (v : BitVec rows) : (~~~v).toNat = fullMask rows ^^^ v.toNat := by
  rw [← BitVec.xor_allOnes, BitVec.toNat_xor, Nat.xor_comm, BitVec.toNat_allOnes]
  rfl

theorem gateOfAvailable {bank : List Word} {w : Word}
    (av : AvailableWord mask bank w) : GateWord mask bank w :=
  Or.inr ⟨w, 0, av, Or.inl rfl, Or.inr (by simp)⟩

theorem toNatAvailable (bank : List (BitVec rows)) (i : Nat) :
    AvailableWord (fullMask rows) (bank.map BitVec.toNat) (bank.getD i 0).toNat := by
  rw [List.getD_eq_getElem?_getD]
  cases h : bank[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_of_getElem? h)))

def buildable (m g : Word) : Nat → Finset (Word) → Prop
  | 0, s => g ∈ s
  | n+1, s => buildable m g n s ∨
    (∃ a ∈ s, buildable m g n (insert (m ^^^ a) s)) ∨
    (∃ a ∈ s, ∃ b ∈ s, ∃ d, buildable m g n (insert (binWord d a b) s))

theorem supplyPool {m g : Word} {n s q} (sub : s ⊆ q) (h : buildable m g n s) : buildable m g n q := by
  induction n generalizing s q with
  | zero => exact sub h
  | succ n ih =>
    rcases h with h | ⟨a,ha,h⟩ | ⟨a,ha,b,hb,d,h⟩
    · exact Or.inl (ih sub h)
    · exact Or.inr (Or.inl ⟨a,sub ha,ih (Finset.insert_subset_insert _ sub) h⟩)
    · exact Or.inr (Or.inr ⟨a,sub ha,b,sub hb,d,ih (Finset.insert_subset_insert _ sub) h⟩)

theorem supplyMore {m g : Word} {n l s} (le : n ≤ l) (h : buildable m g n s) : buildable m g l s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

abbrev maskedFlat (m a : Word) : Prop := a &&& m = 0 ∨ a &&& m = m

def flatSet (m : Word) (s : Finset (Word)) := s.filter (maskedFlat m)
def visibleWords (m : Word) (s : Finset (Word)) := s.image fun w => w &&& m

theorem flIns {m a : Word} {s : Finset (Word)} (ha : a ∉ s) :
    (flatSet m (insert a s)).card = (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases f : maskedFlat m a <;> simp [flatSet,Finset.filter_insert,f,ha]

theorem flLe (m a : Word) (s : Finset (Word)) :
    (flatSet m (insert a s)).card ≤ (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases old : a ∈ s
  · rw [Finset.insert_eq_of_mem old]
    omega
  · rw [flIns old]

theorem prIns (m a : Word) (s : Finset (Word)) :
    visibleWords m (insert a s) = insert (a &&& m) (visibleWords m s) := Finset.image_insert ..

theorem cofNot {mask m : Nat} (sub : mask &&& m = m) (a : Word) :
    (mask ^^^ a) &&& m = m ^^^ (a &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h := congrArg (fun w : Nat => w.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at h ⊢
  cases he : m.testBit i
  · simp
  · have hm : mask.testBit i = true := by simpa [he] using h
    simp [hm]

theorem cofBinary (m a b : Word) (d : Bool) :
    binWord d a b &&& m = binWord d (a &&& m) (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases d <;> simp only [binWord, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and, Nat.testBit_or] <;>
    cases m.testBit i <;> simp

theorem flNot {mask m : Nat} (sub : mask &&& m = m) (a : Word) :
    maskedFlat m (mask ^^^ a) ↔ maskedFlat m a := by
  unfold maskedFlat
  rw [cofNot sub]
  constructor <;> intro h
  · rcases h with h | h
    · right
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
    · left
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
  · rcases h with h | h <;> simp [h]

theorem flBoth {m a b : Word} {d : Bool} (ha : maskedFlat m a) (hb : maskedFlat m b) :
    maskedFlat m (binWord d a b) := by
  unfold maskedFlat at *
  rw [cofBinary]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> cases d <;>
    simp [binWord, ha, hb]

theorem simpleBin {m a b : Word} {d : Bool} (h : maskedFlat m a ∨ maskedFlat m b) :
    binWord d a b &&& m = 0 ∨ binWord d a b &&& m = m ∨
      binWord d a b &&& m = a &&& m ∨ binWord d a b &&& m = b &&& m := by
  rw [cofBinary]
  have top1 (x : Word) : m &&& (x &&& m) = x &&& m := by
    rw [Nat.land_comm x m, ← Nat.land_assoc]
    simp
  have top2 (x : Word) : m ||| (x &&& m) = m := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_or, Nat.testBit_and]
    cases x.testBit i <;> cases m.testBit i <;> rfl
  have right1 (x : Word) : (x &&& m) &&& m = x &&& m := restrictWord m x
  have right2 (x : Word) : (x &&& m) ||| m = m := by rw [Nat.lor_comm, top2]
  rcases h with (ha|ha)|(hb|hb) <;> cases d <;>
    simp [binWord, *, top1, top2, right1, right2]

def projectedStock (m : Word) (s : Finset (Word)) := insert 0 (insert m (visibleWords m s))

theorem maskedBuild {goal : Word} {k t s} (run : LiveWord mask goal k t s) (m : Word) (submask : mask &&& m = m) (properGoal : ¬ maskedFlat m goal) :
    ∃ n, n+(flatSet m s).card ≤ k ∧ buildable m (goal &&& m) n (projectedStock m s) := by
  induction run using LiveWord.ind with
  | stop =>
    refine ⟨0,?_,?_⟩
    · simp only [flatSet, Finset.filter_singleton, properGoal, ite_false, Finset.card_empty,
        Nat.add_zero, Nat.le_refl]
    · change goal &&& m ∈ projectedStock m {goal}
      simp [projectedStock,visibleWords]
  | @unary k t u a pa fresh tail ih =>
    obtain ⟨n,cap,built⟩ := ih
    have nn : (mask ^^^ a) ∉ u := fun h => fresh (Finset.mem_insert_of_mem h)
    rw [flIns nn] at cap
    have card := flLe m a u
    have old : a &&& m ∈ projectedStock m (insert a u) := by simp [projectedStock,prIns]
    have sub : projectedStock m u ⊆ projectedStock m (insert a u) := by
      exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ (Finset.image_subset_image (Finset.subset_insert ..)))
    by_cases f : maskedFlat m a
    · have ff := (flNot submask a).mpr f
      simp only [f,ff,ite_true] at cap card
      refine ⟨n,by omega,supplyPool ?_ built⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rcases hw with rfl|rfl|rfl|h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · rcases ff with e|e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inr h))
    · have nf := mt (flNot submask a).mp f
      simp only [f,nf,ite_false] at cap card
      refine ⟨n+1,by omega,Or.inr (Or.inl ⟨_,old,supplyPool ?_ built⟩)⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rw [cofNot submask] at hw
      tauto
  | @binary k t u a b d pa pb ab fresh tail ih =>
    let v := binWord d a b
    obtain ⟨n,cap,built⟩ := ih
    have nn : v ∉ u := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    change n+(flatSet m (insert v u)).card ≤ k at cap
    rw [flIns nn] at cap
    have ca := flLe m a (insert b u)
    have cb := flLe m b u
    by_cases simple : maskedFlat m a ∨ maskedFlat m b
    · have budget : n + (flatSet m (insert a (insert b u))).card ≤ k+1 := by
        by_cases fa : maskedFlat m a <;> by_cases fb : maskedFlat m b <;>
          simp only [fa,fb,ite_true,ite_false] at ca cb simple
        all_goals first | have vf : maskedFlat m v := flBoth fa fb; simp only [vf,ite_true] at cap; omega | omega | tauto
      refine ⟨n,budget,supplyPool ?_ built⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rcases hw with e|e|e|e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · subst w
        have cases := simpleBin (d := d) simple
        tauto
      · tauto
    · have fa : ¬maskedFlat m a := fun h => simple (Or.inl h)
      have fb : ¬maskedFlat m b := fun h => simple (Or.inr h)
      simp only [fa,fb,ite_false] at ca cb
      refine ⟨n+1,by omega,Or.inr (Or.inr ⟨a &&& m,?_,b &&& m,?_,d,supplyPool ?_ built⟩)⟩
      · simp [projectedStock,prIns]
      · simp [projectedStock,prIns]
      · intro w hw
        simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
        rw [cofBinary] at hw
        tauto

theorem availableB_spec {mask : Nat} {bank : List Word} {v : Word} :
    availableB mask bank v = true ↔ AvailableWord mask bank v := by
  simp [availableB, AvailableWord, or_assoc]

theorem recipeGate_spec {mask : Nat} {bank : List Word} {v a b : Word}
    (h : recipeGate mask bank v a b = true) : GateWord mask bank v := by
  simp only [recipeGate, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, availableB_spec] at h
  rcases h with ⟨ha, first | ⟨hb, second⟩⟩
  · exact Or.inl ⟨a, ha, first⟩
  · exact Or.inr ⟨a, b, ha, hb, second⟩

theorem replayRecipesBuilds (mask : Nat) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) : WordBuilds mask bank (replayRecipes mask needed recipes bank) := by
  induction recipes generalizing bank with
  | nil => trivial
  | cons recipe recipes ih =>
    obtain ⟨w, a, b⟩ := recipe
    change WordBuilds mask bank
      (if needed.contains (w &&& mask) && !availableB mask bank (w &&& mask) &&
          recipeGate mask bank (w &&& mask) (a &&& mask) (b &&& mask) then
        (w &&& mask) :: replayRecipes mask needed recipes ((w &&& mask) :: bank)
      else replayRecipes mask needed recipes bank)
    split
    · rename_i yes
      exact ⟨recipeGate_spec (Bool.and_eq_true_iff.mp yes).2, ih _⟩
    · exact ih _

theorem flatCountCard (mask : Nat) {words : List Word} (nodup : words.Nodup) :
    flatCount mask words = (flatSet mask words.toFinset).card := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    have nd := List.nodup_cons.mp nodup
    have fresh : w ∉ ws.toFinset := by simpa using nd.1
    have bool : maskFlat mask w = true ↔ maskedFlat mask w := by
      simp [maskFlat, maskedFlat]
    change (if maskFlat mask w then flatCount mask ws + 1 else flatCount mask ws) = _
    rw [List.toFinset_cons, flIns fresh, ih nd.2]
    by_cases h : maskedFlat mask w
    · simp [h, bool.mpr h]
    · have no : maskFlat mask w = false := Bool.eq_false_iff.mpr (fun ht => h (bool.mp ht))
      simp [h, no]

theorem buildsAppend {mask : Nat} {roots first second : List Word}
    (left : WordBuilds mask roots first)
    (right : WordBuilds mask (first ++ roots) second) :
    WordBuilds mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact right
  | cons w ws ih =>
    refine ⟨left.1, ih left.2 ?_⟩
    have same (bank other vals : List Word) (perm : bank.Perm other)
        (h : WordBuilds mask bank vals) : WordBuilds mask other vals := by
      induction vals generalizing bank other with
      | nil => trivial
      | cons v vs ih =>
        exact ⟨gateWeaken (fun x hx => Or.inr (Or.inr (perm.mem_iff.mp hx))) h.1,
          ih _ _ (perm.cons v) h.2⟩
    exact same _ _ _ (List.perm_middle (a := w) (l₁ := ws) (l₂ := roots)).symm right

theorem buildableWords {mask goal n : Nat} {pool : Finset Word} {bank : List Word}
    (h : buildable mask goal n pool) (supply : ∀ w ∈ pool, AvailableWord mask bank w) :
    ∃ values, values.length ≤ n ∧ WordBuilds mask bank values ∧
      AvailableWord mask (values ++ bank) goal := by
  induction n generalizing pool bank with
  | zero => exact ⟨[], Nat.le_refl _, trivial, supply _ h⟩
  | succ n ih =>
    have add {w : Word} (g : GateWord mask bank w)
        (tail : buildable mask goal n (insert w pool)) :
        ∃ values, values.length ≤ n+1 ∧ WordBuilds mask bank values ∧
          AvailableWord mask (values ++ bank) goal := by
      have growing : ∀ v ∈ insert w pool, AvailableWord mask (w :: bank) v := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Or.inr (Or.inr List.mem_cons_self)
        · exact availableWeaken (fun _ hh => Or.inr (Or.inr (List.mem_cons_of_mem _ hh))) (supply _ hv)
      obtain ⟨values, budget, build, hit⟩ := ih tail growing
      refine ⟨w :: values, by simp only [List.length_cons]; omega, ⟨g, build⟩, ?_⟩
      rcases hit with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by simp only [List.mem_append, List.mem_cons] at *; tauto))
    rcases h with h | ⟨a, ha, h⟩ | ⟨a, ha, b, hb, d, h⟩
    · obtain ⟨values, cap, build, hit⟩ := ih h supply
      exact ⟨values, by omega, build, hit⟩
    · exact add (Or.inl ⟨a, supply a ha, rfl⟩) h
    · apply add (w := binWord d a b) ?_ h
      exact Or.inr ⟨a, b, supply a ha, supply b hb, by cases d <;> simp [binWord]⟩

theorem boundClosesSound {state : RowState} {bound : Bound}
    (known : Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (submask : mask &&& bound.1 = bound.1)
    (viable : WordViable mask target state) :
    boundCloses target state bound = false := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨cut, stock, minimum, goal⟩ := bound
  obtain ⟨nd, k, t, steps, live⟩ := viable
  change k ≤ fuel at steps
  change LiveWord mask target k t ws.toFinset at live
  apply Bool.eq_false_iff.mpr
  intro hc
  let replay := replayRecipes cut (recipeNeeded cut stock ws history) history.reverse stock
  change ((target &&& cut) == goal && goal != 0 && goal != cut &&
    (if fuel - flatCount cut ws < minimum then
      if (recipeStart cut stock ws).length + (fuel - flatCount cut ws) < minimum then
        if (recipeNeeded cut stock ws history).length + (fuel - flatCount cut ws) < minimum then
          (replay.length + (fuel - flatCount cut ws) < minimum) &&
            ws.all (fun w => availableB cut (replay ++ stock) (w &&& cut))
        else false
      else false
    else false)) = true at hc
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨goalEq, nonzero⟩, nonflat⟩, scan⟩ := hc
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  rcases Bool.and_eq_true_iff.mp scan with ⟨length, sources⟩
  simp only [decide_eq_true_eq] at length
  have pn : ¬maskedFlat cut target := by simpa [maskedFlat, goalEq] using And.intro nonzero nonflat
  obtain ⟨n, hn, build⟩ := maskedBuild live cut submask pn
  rw [← flatCountCard cut nd] at hn
  change n + flatCount cut ws ≤ k at hn
  have supply : ∀ w ∈ projectedStock cut ws.toFinset, AvailableWord cut (replay ++ stock) w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image,
      List.mem_toFinset] at hw
    rcases hw with rfl | rfl | ⟨v, hv, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact availableB_spec.mp (List.all_eq_true.mp sources v hv)
  obtain ⟨ys, hy, built, avail⟩ := buildableWords build supply
  have both := buildsAppend (replayRecipesBuilds cut _ history.reverse stock) built
  have hit : AvailableWord cut ((replay ++ ys) ++ stock) goal := by
    rw [← goalEq]
    exact availableWeaken (fun v hv => Or.inr (Or.inr (by
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using hv))) avail
  have enough := known (replay ++ ys) both hit
  simp only [List.length_append] at enough
  omega

theorem knownClosesSound {bounds : List Bound} {state : RowState}
    (known : Known bounds) (submask : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (viable : WordViable mask target state) :
    knownCloses target bounds state = false := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (boundCloses target state bound || knownCloses target bounds state) = false
    rw [boundClosesSound (known _ List.mem_cons_self) (submask _ List.mem_cons_self) viable]
    exact ih (fun b hb => known b (List.mem_cons_of_mem _ hb))
      (fun b hb => submask b (List.mem_cons_of_mem _ hb))

abbrev PointWire (rows : Nat) := Fin rows → Bool

def encodePoint (f : PointWire rows) : BitVec rows :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem encodeBit (f : PointWire rows) (i : Fin rows) :
    (encodePoint f).getLsbD i.val = f i := by
  simp only [encodePoint, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

theorem encodeNot (f : PointWire rows) : encodePoint (fun j => !f j) = ~~~encodePoint f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_not, encodeBit f ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
  simp [hi]

theorem encodeAnd (a b : PointWire rows) :
    encodePoint (fun i => a i && b i) = encodePoint a &&& encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]

theorem encodeOr (a b : PointWire rows) :
    encodePoint (fun i => a i || b i) = encodePoint a ||| encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]

def pointWord (f : PointWire rows) : Word := (encodePoint f).toNat

def relabel (sourceIndex : Fin rows → Fin rows) (word : Word) : Word :=
  pointWord fun i => word.testBit (sourceIndex i).val

theorem maskBit {i : Nat} (hi : i < rows) : (fullMask rows).testBit i = true := by
  simp [fullMask, Nat.testBit_two_pow_sub_one, hi]

theorem pointZero : pointWord (fun _ : Fin rows => false) = 0 := by
  have eq : encodePoint (fun _ : Fin rows => false) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp
  simp [pointWord, eq]

theorem relabelZero (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex 0 = 0 := by
  simpa [relabel] using (pointZero (rows := rows))

theorem relabelMask (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex (fullMask rows) = fullMask rows := by
  have all : (fun i => (fullMask rows).testBit (sourceIndex i).val) = fun _ => true := by
    funext i
    exact maskBit (sourceIndex i).isLt
  have bits : encodePoint (fun _ : Fin rows => true) = BitVec.allOnes rows := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp [hi]
  simp [relabel, all, pointWord, bits, fullMask]

theorem relabelNot (sourceIndex : Fin rows → Fin rows) (a : Word) :
    relabel sourceIndex (fullMask rows ^^^ a) = fullMask rows ^^^ relabel sourceIndex a := by
  have eq : (fun i => (fullMask rows ^^^ a).testBit (sourceIndex i).val) =
      fun i => !a.testBit (sourceIndex i).val := by
    funext i
    simp [Nat.testBit_xor, maskBit (sourceIndex i).isLt]
  simp only [relabel, eq, pointWord, encodeNot, notNat]

theorem relabelAnd (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a &&& b) = relabel sourceIndex a &&& relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_and, pointWord, encodeAnd, BitVec.toNat_and]

theorem relabelOr (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ||| b) = relabel sourceIndex a ||| relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_or, pointWord, encodeOr, BitVec.toNat_or]

theorem lowerRelabel (sourceIndex : Fin rows → Fin rows) {bank roots : List Word}
    {src dst : Word} {minimum : Nat}
    (old : Lower (fullMask rows) bank src minimum)
    (goal : relabel sourceIndex dst = src)
    (supply : ∀ w ∈ roots, AvailableWord (fullMask rows) bank (relabel sourceIndex w)) :
    Lower (fullMask rows) roots dst minimum := by
  apply lowerMap (relabel sourceIndex) (relabelZero sourceIndex) (relabelMask sourceIndex)
    (relabelNot sourceIndex) (relabelAnd sourceIndex) (relabelOr sourceIndex) supply
  rw [goal]
  exact old

theorem relabelXor (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ^^^ b) = relabel sourceIndex a ^^^ relabel sourceIndex b := by
  have eq : encodePoint (fun i => (a ^^^ b).testBit (sourceIndex i).val) =
      encodePoint (fun i => a.testBit (sourceIndex i).val) ^^^
      encodePoint (fun i => b.testBit (sourceIndex i).val) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_xor, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
    exact Nat.testBit_xor ..
  simpa only [relabel, pointWord, BitVec.toNat_xor] using congrArg BitVec.toNat eq

theorem lowerRelabelMasked (sourceIndex : Fin rows → Fin rows)
    {oldMask newMask : Nat} {bank roots : List Word} {src dst : Word} {minimum : Nat}
    (old : Lower oldMask bank src minimum)
    (masks : relabel sourceIndex newMask = oldMask)
    (goal : relabel sourceIndex dst = src)
    (supply : ∀ w ∈ roots, AvailableWord oldMask bank (relabel sourceIndex w)) :
    Lower newMask roots dst minimum := by
  apply lowerMap (relabel sourceIndex) (relabelZero sourceIndex) masks
    (fun w => by rw [relabelXor, masks]) (relabelAnd sourceIndex) (relabelOr sourceIndex) supply
  rwa [goal]

theorem extendKnownRelabel (sourceIndex : Fin rows → Fin rows) {bounds : List Bound}
    {source destination : Bound} (old : Known bounds) (mem : source ∈ bounds)
    (budget : destination.2.2.1 = source.2.2.1)
    (masks : relabel sourceIndex destination.1 = source.1)
    (goal : relabel sourceIndex destination.2.2.2 = source.2.2.2)
    (supply : ∀ w ∈ destination.2.1,
      AvailableWord source.1 source.2.1 (relabel sourceIndex w)) :
    Known (destination :: bounds) := by
  apply extendKnown old
  rw [budget]
  exact lowerRelabelMasked sourceIndex (old _ mem) masks goal supply

theorem relabelToNatBound (sourceIndex : Fin rows → Fin rows) (word : Word) :
    Masked (fullMask rows) (relabel sourceIndex word) := toNatMasked _

theorem relabelBit (sourceIndex : Fin rows → Fin rows) (word : Word) (i : Fin rows) :
    (relabel sourceIndex word).testBit i.val = word.testBit (sourceIndex i).val :=
  encodeBit _ i

theorem relabelOutside (sourceIndex : Fin rows → Fin rows) (word i : Word) (h : rows ≤ i) :
    (relabel sourceIndex word).testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le (show (encodePoint _).toNat < 2 ^ rows from BitVec.isLt _)
    (Nat.pow_le_pow_right (by decide) h)

theorem relabelInj (sourceIndex : Fin rows → Fin rows) (onto : Function.Surjective sourceIndex)
    {a b : Word} (ba : Masked (fullMask rows) a) (bb : Masked (fullMask rows) b)
    (eq : relabel sourceIndex a = relabel sourceIndex b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · obtain ⟨j, h⟩ := onto ⟨i, inside⟩
    have bit := congrArg (fun w : Nat => w.testBit j.val) eq
    simpa only [relabelBit, h] using bit
  · have ea := congrArg (fun w : Nat => w.testBit i) ba
    have eb := congrArg (fun w : Nat => w.testBit i) bb
    simp only [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, inside, decide_false,
      Bool.and_false] at ea eb
    rw [← ea, ← eb]

theorem kw_step (goal : Word) (D D' : Finset Word) (u v w : ℕ) (c : ℕ → ℕ → Bool) (f : ℕ → ℕ → ℕ)
    (hu : u ∈ D) (hv : v ∈ D) (huv : u ≠ v) (huD : u ∉ D') (hvD : v ∉ D')
    (hsub : ∀ x ∈ D', x ≠ w → x ∈ D)
    (hf : ∀ e i, goal.testBit e = true → goal.testBit i = false →
      f e i ∈ D' ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false)
    (hr : ∀ e i e' i', goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)
    (hcu : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = true →
      u.testBit e = true ∧ u.testBit i = false)
    (hcv : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = false →
      v.testBit e = true ∧ v.testBit i = false)
    (hc : ∀ e i e' i', c e i = c e' i' → c e i' = c e i) :
    ∃ g : ℕ → ℕ → ℕ,
      (∀ e i, goal.testBit e = true → goal.testBit i = false →
        g e i ∈ D ∧ (g e i).testBit e = true ∧ (g e i).testBit i = false) ∧
      (∀ e i e' i', goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → g e i = g e' i' → g e i' = g e i) := by
  have hg : ∀ e i, goal.testBit e = true → goal.testBit i = false → f e i = w →
      ((if f e i = w then (cond (c e i) u v) else f e i) = u ∧ c e i = true) ∨
      ((if f e i = w then (cond (c e i) u v) else f e i) = v ∧ c e i = false) := by
    intro e i _ _ h
    rw [ite_eq_left (h)]
    cases c e i
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  refine ⟨fun e i => if f e i = w then (cond (c e i) u v) else f e i, ?_, ?_⟩
  · intro e i he hi
    obtain ⟨h1, h2, h3⟩ := hf e i he hi
    show (if f e i = w then (cond (c e i) u v) else f e i) ∈ D ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit e = true ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit i = false
    by_cases hw : f e i = w
    · rw [hw] at h2 h3
      rcases hg e i he hi hw with ⟨hx, hcc⟩ | ⟨hx, hcc⟩
      · rw [hx]; exact ⟨hu, hcu e i h2 h3 hcc⟩
      · rw [hx]; exact ⟨hv, hcv e i h2 h3 hcc⟩
    · rw [ite_eq_right (hw)]; exact ⟨hsub _ h1 hw, h2, h3⟩
  · intro e i e' i' he he' hi hi' heq
    show (if f e i' = w then (cond (c e i') u v) else f e i') =
      (if f e i = w then (cond (c e i) u v) else f e i)
    have heq' : (if f e i = w then (cond (c e i) u v) else f e i) =
      (if f e' i' = w then (cond (c e' i') u v) else f e' i') := heq
    by_cases h1 : f e i = w
    · by_cases h2 : f e' i' = w
      · have h3 : f e i' = w := (hr e i e' i' he he' hi hi' (h1.trans h2.symm)).trans h1
        have hcc : c e i = c e' i' := by
          rcases hg e i he hi h1 with ⟨hx, hx'⟩ | ⟨hx, hx'⟩ <;>
            rcases hg e' i' he' hi' h2 with ⟨hy, hy'⟩ | ⟨hy, hy'⟩
          · rw [hx', hy']
          · exact absurd (hx.symm.trans (heq'.trans hy)) huv
          · exact absurd (hy.symm.trans (heq'.symm.trans hx)) huv
          · rw [hx', hy']
        rw [ite_eq_left (h3), ite_eq_left (h1), hc e i e' i' hcc]
      · exfalso
        rw [ite_eq_right (h2)] at heq'
        have hm := (hf e' i' he' hi').1
        rcases hg e i he hi h1 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, heq']; exact hm)
        · exact hvD (by rw [← hx, heq']; exact hm)
    · by_cases h2 : f e' i' = w
      · exfalso
        rw [ite_eq_right (h1)] at heq'
        have hm := (hf e i he hi).1
        rcases hg e' i' he' hi' h2 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, ← heq']; exact hm)
        · exact hvD (by rw [← hx, ← heq']; exact hm)
      · have h1n : (if f e i = w then (cond (c e i) u v) else f e i) = f e i := ite_eq_right h1
        have h2n : (if f e' i' = w then (cond (c e' i') u v) else f e' i') = f e' i' := ite_eq_right h2
        rw [h1n, h2n] at heq'
        have h3 := hr e i e' i' he he' hi hi' heq'
        have h3n : ¬ f e i' = w := by rw [h3]; exact h1
        rw [h1n, ite_eq_right (h3n)]
        exact h3

theorem and_cu (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (_h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_and] at h1
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem and_cv (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_and] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem or_cu (u v e i : ℕ) (_h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_or] at h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem or_cv (u v e i : ℕ) (h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_or] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

def KWPartition (goal : Word) (ws : Finset Word) : Prop :=
  ∃ f : Nat → Nat → Word,
    (∀ e i, goal.testBit e = true → goal.testBit i = false →
      f e i ∈ ws ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false) ∧
    (∀ e i e' i', goal.testBit e = true → goal.testBit e' = true →
      goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)

theorem kwFromLive {mask goal : Word} {k : Nat} {S : Finset Word}
    (live : LiveWord mask goal k 0 S) (tight : S.card = k + 1) : KWPartition goal S := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    subst S
    exact ⟨fun _ _ => goal, fun _ _ hp hn => ⟨by simp, hp, hn⟩, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ k ih =>
    rcases live with ⟨u, U, a, eq, _⟩ | ⟨U, a, b, op, rfl, pa, pb, ab, fresh, tail⟩
    · omega
    let w := binWord op a b
    have wU : w ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have wA : w ≠ a := fun eq => fresh (Finset.mem_insert.mpr (Or.inl eq))
    have wB : w ≠ b := fun eq => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl eq)))
    have tailSize := (liveWordSize tail).2
    change (insert w U).card + 0 ≤ k + 1 at tailSize
    rw [Finset.card_insert_of_notMem wU] at tailSize
    have paCard := Finset.card_insert_le a (insert b U)
    have pbCard := Finset.card_insert_le b U
    have aU : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h)] at tight
      omega
    have bU : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      have := Finset.card_insert_le a U
      omega
    obtain ⟨f, hf, hr⟩ := ih tail (by
      change (insert w U).card = k + 1
      rw [Finset.card_insert_of_notMem wU]
      omega)
    have keepA : a ∉ insert w U := by simp [wA.symm, aU]
    have keepB : b ∉ insert w U := by simp [wB.symm, bU]
    have other : ∀ x ∈ insert w U, x ≠ w → x ∈ insert a (insert b U) := by
      intro x hx hn
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((Finset.mem_insert.mp hx).resolve_left hn))
    have ha : a ∈ insert a (insert b U) := Finset.mem_insert_self ..
    have hb : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    cases op
    · exact kw_step goal _ _ a b w (fun _ i => !(a.testBit i)) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3 => and_cu a b e i h1 h2 h3) (fun e i h1 h2 h3 => and_cv a b e i h1 h2 h3)
        (fun _ _ _ _ h => h.symm)
    · exact kw_step goal _ _ a b w (fun e _ => a.testBit e) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3 => or_cu a b e i h1 h2 h3) (fun e i h1 h2 h3 => or_cv a b e i h1 h2 h3)
        (fun _ _ _ _ _ => rfl)

theorem liveDirected {mask goal : Word} {k : Nat} {S : Finset Word}
    (live : LiveWord mask goal k 0 S) {p n : Nat}
    (hp : goal.testBit p = true) (hn : goal.testBit n = false) :
    ∃ w ∈ S, w.testBit p = true ∧ w.testBit n = false := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_,rfl,_⟩ := live
    exact ⟨goal, by simp, hp, hn⟩
  | succ k ih =>
    rcases live with ⟨u, U, a, ueq, _⟩ | ⟨U,a,b,op,rfl,pa,pb,ab,fresh,tail⟩
    · omega
    obtain ⟨w, hw, wp, wn⟩ := ih tail
    rcases Finset.mem_insert.mp hw with eq | hU
    · subst w
      cases op
      · by_cases ha : a.testBit n = false
        · exact ⟨a, Finset.mem_insert_self .., and_cu a b p n wp wn (by simp [ha])⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            and_cv a b p n wp wn (by cases h : a.testBit n <;> simp_all)⟩
      · by_cases ha : a.testBit p = true
        · exact ⟨a, Finset.mem_insert_self .., or_cu a b p n wp wn ha⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            or_cv a b p n wp wn (by cases h : a.testBit p <;> simp_all)⟩
    · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),wp,wn⟩

namespace PackedRect

theorem tb4095 (i : ℕ) : (4095 : ℕ).testBit i = decide (i < 12) := by
  have e : (4095 : ℕ) = 2 ^ 12 - 1 := by norm_num
  rw [e, Nat.testBit_two_pow_sub_one]

def tb (w e : ℕ) : Bool := !(Nat.beq (Nat.land (Nat.shiftRight w e) 1) 0)

theorem tb_eq (w e : ℕ) : tb w e = w.testBit e := by
  have h : Nat.land (Nat.shiftRight w e) 1 = 1 &&& (w >>> e) := Nat.and_comm _ _
  unfold tb Nat.testBit
  rw [h]
  generalize (1 &&& w >>> e) = X
  cases X <;> rfl

def rect (x J : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => Nat.lor (cond (tb x e) (Nat.shiftLeft J (Nat.mul 12 e)) 0) (rect x J e)

def rectW (x : ℕ) : ℕ := rect x (Nat.xor (Nat.shiftRight x 12) 4095) 12

theorem rect_tb (x J i : ℕ) (hJ : J.testBit i = true) : ∀ n e : ℕ, e < n → x.testBit e = true →
    (rect x J n).testBit (12 * e + i) = true := by
  intro n
  induction n with
  | zero => intro e he; omega
  | succ n ih =>
    intro e he hx
    show ((cond (tb x n) (J <<< (12 * n)) 0) ||| rect x J n).testBit (12 * e + i) = true
    rw [Nat.testBit_or]
    by_cases hen : e = n
    · subst hen
      rw [tb_eq, hx]
      simp [Nat.testBit_shiftLeft, hJ]
    · rw [ih e (by omega) hx]
      simp

theorem rectW_tb (x e i : ℕ) (he : e < 12) (hi : i < 12) (h1 : x.testBit e = true)
    (h2 : x.testBit (12 + i) = false) : (rectW x).testBit (12 * e + i) = true := by
  apply rect_tb _ _ _ _ 12 e he h1
  show ((x >>> 12) ^^^ 4095).testBit i = true
  rw [Nat.testBit_xor, Nat.testBit_shiftRight, h2, tb4095]
  simp [hi]

def full : ℕ := 22300745198530623141535718272648361505980415

theorem full_eq : full = 2 ^ 144 - 1 := by norm_num [full]

theorem tb_land (a b q : ℕ) : (Nat.land a b).testBit q = (a.testBit q && b.testBit q) :=
  Nat.testBit_and a b q

theorem tb_lor (a b q : ℕ) : (Nat.lor a b).testBit q = (a.testBit q || b.testBit q) :=
  Nat.testBit_or a b q

theorem tb_xor (a b q : ℕ) : (Nat.xor a b).testBit q = Bool.xor (a.testBit q) (b.testBit q) :=
  Nat.testBit_xor a b q

theorem full_tb (q : ℕ) : full.testBit q = decide (q < 144) := by
  rw [full_eq, Nat.testBit_two_pow_sub_one]

theorem land_sub (h a : ℕ) (H : ∀ q, h.testBit q = true → a.testBit q = true) :
    Nat.land h a = h := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land]
  cases hh : h.testBit q
  · rfl
  · rw [H q hh]; rfl

theorem land_disj (a h : ℕ) (H : ∀ q, a.testBit q = true → h.testBit q = true → False) :
    Nat.land a h = 0 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land, Nat.zero_testBit]
  cases ha : a.testBit q
  · rfl
  · cases hh : h.testBit q
    · rfl
    · exact (H q ha hh).elim

def orS (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftRight x s)

def orSL (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftLeft x s)

theorem orS_tb (x s q : ℕ) : (orS x s).testBit q = (x.testBit q || x.testBit (s + q)) := by
  show (x ||| x >>> s).testBit q = _
  rw [Nat.testBit_or, Nat.testBit_shiftRight]

theorem orSL_tb (x s q : ℕ) :
    (orSL x s).testBit q = (x.testBit q || (decide (s ≤ q) && x.testBit (q - s))) := by
  show (x ||| x <<< s).testBit q = _
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, ge_iff_le]

theorem orS_ex (k p x n s : ℕ)
    (hx : ∀ q, x.testBit q = true → ∃ j, j < n ∧ p.testBit (k * j + q) = true) (q : ℕ)
    (h : (orS x (k * s)).testBit q = true) : ∃ j, j < n + s ∧ p.testBit (k * j + q) = true := by
  rw [orS_tb, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨j, hj, hp⟩ := hx q h
    exact ⟨j, by omega, hp⟩
  · obtain ⟨j, hj, hp⟩ := hx _ h
    refine ⟨j + s, by omega, ?_⟩
    rw [Nat.mul_add, Nat.add_assoc]; exact hp

theorem orSL_ex (k p x n s : ℕ)
    (hx : ∀ q, x.testBit q = true → ∃ j, j < n ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true)
    (q : ℕ) (h : (orSL x (k * s)).testBit q = true) :
    ∃ j, j < n + s ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true := by
  rw [orSL_tb, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨hs, h⟩
  · obtain ⟨j, hj, hq, hp⟩ := hx q h
    exact ⟨j, by omega, hq, hp⟩
  · obtain ⟨j, hj, hq, hp⟩ := hx _ h
    have e : q - k * (j + s) = q - k * s - k * j := by rw [Nat.mul_add]; omega
    refine ⟨j + s, by omega, ?_, ?_⟩
    · rw [Nat.mul_add]; omega
    · rw [e]; exact hp

def rowM : ℕ := 5445847423328601499764522166702896582657

theorem rowM_tb (q : ℕ) (h : rowM.testBit q = true) : q < 144 ∧ q % 12 = 0 := by
  have hlt : q < 144 := by
    by_contra hq
    have h0 : rowM.testBit q = false := by
      apply Nat.testBit_lt_two_pow
      have h1 : rowM < 2 ^ 144 := by norm_num [rowM]
      have h2 : (2 : ℕ) ^ 144 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [h0] at h
    exact Bool.noConfusion h
  have hall : ∀ q : ℕ, q < 144 → rowM.testBit q = true → q % 12 = 0 := by decide +kernel
  exact ⟨hlt, hall q hlt h⟩

def rowsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 6) 3) 1) 1) rowM

def colsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 96) 48) 24) 12) 4095

def hullC (p : ℕ) : ℕ :=
  Nat.land (orSL (orSL (orSL (orSL (rowsOf p) 6) 3) 1) 1)
    (orSL (orSL (orSL (orSL (colsOf p) 96) 48) 24) 12)

def hull (p : ℕ) : ℕ := hullC (Nat.land p full)

theorem rowsOf_tb (p q : ℕ) (h : (rowsOf p).testBit q = true) :
    (q < 144 ∧ q % 12 = 0) ∧ ∃ j, j < 12 ∧ p.testBit (j + q) = true := by
  unfold rowsOf at h
  rw [tb_land, Bool.and_eq_true] at h
  refine ⟨rowM_tb q h.2, ?_⟩
  have h0 : ∀ q, p.testBit q = true → ∃ j, j < 1 ∧ p.testBit (1 * j + q) = true :=
    fun q hq => ⟨0, by norm_num, by simpa using hq⟩
  have h1 := orS_ex 1 p _ 1 6 h0
  have h2 := orS_ex 1 p _ _ 3 h1
  have h3 := orS_ex 1 p _ _ 1 h2
  have h4 := orS_ex 1 p _ _ 1 h3
  obtain ⟨j, hj, hp⟩ := h4 q h.1
  exact ⟨j, by omega, by simpa using hp⟩

theorem colsOf_tb (p q : ℕ) (h : (colsOf p).testBit q = true) :
    q < 12 ∧ ∃ j, j < 16 ∧ p.testBit (12 * j + q) = true := by
  unfold colsOf at h
  rw [tb_land, Bool.and_eq_true, tb4095, decide_eq_true_eq] at h
  refine ⟨h.2, ?_⟩
  have h0 : ∀ q, p.testBit q = true → ∃ j, j < 1 ∧ p.testBit (12 * j + q) = true :=
    fun q hq => ⟨0, by norm_num, by simpa using hq⟩
  have h1 := orS_ex 12 p _ 1 8 h0
  have h2 := orS_ex 12 p _ _ 4 h1
  have h3 := orS_ex 12 p _ _ 2 h2
  have h4 := orS_ex 12 p _ _ 1 h3
  obtain ⟨j, hj, hp⟩ := h4 q h.1
  exact ⟨j, by omega, hp⟩

theorem hullC_spec (p : ℕ) (hp : ∀ q, p.testBit q = true → q < 144) (q : ℕ)
    (h : (hullC p).testBit q = true) :
    q < 144 ∧ ∃ i e', i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  unfold hullC at h
  rw [tb_land, Bool.and_eq_true] at h
  obtain ⟨hR, hC⟩ := h
  have r0 : ∀ q, (rowsOf p).testBit q = true →
      ∃ j, j < 1 ∧ 1 * j ≤ q ∧ (rowsOf p).testBit (q - 1 * j) = true :=
    fun q hq => ⟨0, by norm_num, by omega, by simpa using hq⟩
  have r1 := orSL_ex 1 (rowsOf p) _ 1 6 r0
  have r2 := orSL_ex 1 (rowsOf p) _ _ 3 r1
  have r3 := orSL_ex 1 (rowsOf p) _ _ 1 r2
  have r4 := orSL_ex 1 (rowsOf p) _ _ 1 r3
  obtain ⟨j, hj, hjq, hr⟩ := r4 q hR
  obtain ⟨⟨hb, hm⟩, i, hi, hpi⟩ := rowsOf_tb p _ hr
  have c0 : ∀ q, (colsOf p).testBit q = true →
      ∃ j, j < 1 ∧ 12 * j ≤ q ∧ (colsOf p).testBit (q - 12 * j) = true :=
    fun q hq => ⟨0, by norm_num, by omega, by simpa using hq⟩
  have c1 := orSL_ex 12 (colsOf p) _ 1 8 c0
  have c2 := orSL_ex 12 (colsOf p) _ _ 4 c1
  have c3 := orSL_ex 12 (colsOf p) _ _ 2 c2
  have c4 := orSL_ex 12 (colsOf p) _ _ 1 c3
  obtain ⟨j', hj', hjq', hc⟩ := c4 q hC
  obtain ⟨hlt, e', he', hpe⟩ := colsOf_tb p _ hc
  have e1 : i + (q - 1 * j) = 12 * (q / 12) + i := by omega
  have e2 : q - 12 * j' = q % 12 := by omega
  rw [e1] at hpi
  rw [e2] at hpe
  have hb' := hp _ hpe
  exact ⟨by omega, i, e', hi, by omega, hpi, hpe⟩

theorem hull_spec (p q : ℕ) (h : (hull p).testBit q = true) :
    q < 144 ∧ ∃ i e', i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  have hp : ∀ q, (Nat.land p full).testBit q = true → q < 144 := by
    intro q hq
    rw [tb_land, full_tb, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.2
  obtain ⟨h1, i, e', hi, he, ha, hb⟩ := hullC_spec _ hp q h
  rw [tb_land, Bool.and_eq_true] at ha hb
  exact ⟨h1, i, e', hi, he, ha.1, hb.1⟩

def tw : List ℕ → ℕ → ℕ → ℕ
  | [], _, t => t
  | a :: l, o, t => tw l (Nat.lor o a) (Nat.lor t (Nat.land o a))

def priv (t a : ℕ) : ℕ := hull (Nat.land a (Nat.xor t full))

def hullsOK (t : ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | a :: l, acc => Nat.beq (Nat.land (priv t a) a) (priv t a) &&
      (Nat.beq (Nat.land acc (priv t a)) 0 && hullsOK t l (Nat.lor acc (priv t a)))

def avOK1 (as : List ℕ) : Bool := hullsOK (tw as 0 0) as 0

def orL : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.lor a (orL l)

def rectOK1 (l : List ℕ) : Bool := avOK1 (l.map rectW)

def IsRect (R : ℕ → Prop) : Prop :=
  ∀ e i e' i' : ℕ, e < 12 → i < 12 → e' < 12 → i' < 12 →
    R (12 * e + i) → R (12 * e' + i') → R (12 * e + i')

def Part (zs : List ((ℕ → Prop) × ℕ)) : Prop :=
  (∀ z ∈ zs, IsRect z.1) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → q < 144) ∧
  (zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False)) ∧
  (∀ q, q < 144 → ∃ z ∈ zs, z.1 q) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true)

theorem Part.rect {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, IsRect z.1 := h.1

theorem Part.bnd {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, ∀ q, z.1 q → q < 144 := h.2.1

theorem Part.disj {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False) := h.2.2.1

theorem Part.cov {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ q, q < 144 → ∃ z ∈ zs, z.1 q := h.2.2.2.1

theorem Part.sub {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true := h.2.2.2.2

theorem pw_forall {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ l : List α, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x l ih =>
    intro h a ha b hb hab
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with ha' | ha'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hab
      · rw [ha']; exact h.1 b hb'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · rw [hb']; exact hs _ _ (h.1 a ha')
      · exact ih h.2 a ha' b hb' hab

theorem tw_spec (q : ℕ) : ∀ (as : List ℕ) (o t : ℕ), (tw as o t).testBit q = false →
    t.testBit q = false ∧ (o.testBit q = true → ∀ a ∈ as, a.testBit q = false) ∧
    as.Pairwise (fun a b => ¬ (a.testBit q = true ∧ b.testBit q = true)) := by
  intro as
  induction as with
  | nil => intro o t h; exact ⟨h, fun _ a ha => by simp at ha, List.Pairwise.nil⟩
  | cons a l ih =>
    intro o t h
    obtain ⟨h1, h2, h3⟩ := ih (Nat.lor o a) (Nat.lor t (Nat.land o a)) h
    rw [tb_lor, Bool.or_eq_false_iff, tb_land] at h1
    refine ⟨h1.1, ?_, ?_⟩
    · intro ho b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · have h4 := h1.2
        rw [ho] at h4
        simpa using h4
      · exact h2 (by rw [tb_lor, ho]; rfl) b hb
    · refine List.pairwise_cons.mpr ⟨?_, h3⟩
      intro b hb hab
      have h4 := h2 (by rw [tb_lor, hab.1]; simp) b hb
      rw [h4] at hab
      exact Bool.noConfusion hab.2

theorem priv_in {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) : ∀ z ∈ zs, ∀ q,
    (priv (tw (zs.map Prod.snd) 0 0) z.2).testBit q = true → z.1 q := by
  intro z hz q hq
  obtain ⟨hq144, i, e', hi, he', ha, hb⟩ := hull_spec _ q hq
  have key : ∀ x, x < 144 →
      (Nat.land z.2 (Nat.xor (tw (zs.map Prod.snd) 0 0) full)).testBit x = true → z.1 x := by
    intro x hx hbit
    rw [tb_land, tb_xor, full_tb, Bool.and_eq_true] at hbit
    obtain ⟨hzx, ht⟩ := hbit
    have ht' : (tw (zs.map Prod.snd) 0 0).testBit x = false := by simpa [hx] using ht
    obtain ⟨_, _, hpw⟩ := tw_spec x _ 0 0 ht'
    rw [List.pairwise_map] at hpw
    obtain ⟨z', hz', hzq⟩ := hP.cov x hx
    by_cases hzz : z' = z
    · rw [← hzz]; exact hzq
    · exfalso
      exact pw_forall (fun a b h h' => h ⟨h'.2, h'.1⟩) zs hpw z' hz' z hz hzz
        ⟨hP.sub z' hz' x hzq, hzx⟩
  have h1 := key _ (by omega) ha
  have h2 := key _ (by omega) hb
  have h3 := hP.rect z hz (q / 12) i e' (q % 12) (by omega) hi he' (Nat.mod_lt _ (by norm_num))
    h1 h2
  rwa [Nat.div_add_mod] at h3

theorem hullsOK_sound (t : ℕ) : ∀ (zs : List ((ℕ → Prop) × ℕ)) (acc : ℕ),
    (∀ z ∈ zs, ∀ q, (priv t z.2).testBit q = true → z.1 q) →
    (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true) →
    zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False) →
    (∀ q, acc.testBit q = true → ∀ z ∈ zs, ¬ z.1 q) →
    hullsOK t (zs.map Prod.snd) acc = true := by
  intro zs
  induction zs with
  | nil => intros; rfl
  | cons z zs ih =>
    intro acc hh hs hd ha
    rw [List.pairwise_cons] at hd
    have hz := hh z List.mem_cons_self
    have e1 := land_sub _ _ (fun q hq => hs z List.mem_cons_self q (hz q hq))
    have e2 := land_disj acc (priv t z.2) (fun q h1 h2 => ha q h1 z List.mem_cons_self (hz q h2))
    have e3 := ih (Nat.lor acc (priv t z.2)) (fun z' hz' => hh z' (List.mem_cons_of_mem _ hz'))
      (fun z' hz' => hs z' (List.mem_cons_of_mem _ hz')) hd.2 (fun q hq z' hz' hz'q => by
        rw [tb_lor, Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact ha q hq z' (List.mem_cons_of_mem _ hz') hz'q
        · exact hd.1 z' hz' q (hz q hq) hz'q)
    show (Nat.beq (Nat.land (priv t z.2) z.2) (priv t z.2) &&
      (Nat.beq (Nat.land acc (priv t z.2)) 0 &&
        hullsOK t (zs.map Prod.snd) (Nat.lor acc (priv t z.2)))) = true
    rw [e1, e2, e3, Nat.beq_refl]
    rfl

theorem avOK1_sound {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) :
    avOK1 (zs.map Prod.snd) = true :=
  hullsOK_sound _ zs 0 (priv_in hP) hP.sub hP.disj (fun q hq => by simp at hq)

end PackedRect

abbrev Witness := Word × Nat × Nat

def witnessWord (w : Witness) : Word := w.1

def essentialB (mask target : Word) (stock : List Word) (entry : Witness) : Bool :=
  let (w,p,n) := entry
  mask.testBit p && mask.testBit n && target.testBit p && !target.testBit n &&
    (w.testBit p != w.testBit n) &&
    stock.all (fun x => x == w || x.testBit p == x.testBit n)

theorem essentialRequired {stock : List Word} {entry : Witness} {S : Finset Word} {k t : Nat}
    (ok : essentialB mask target stock entry = true)
    (sub : ∀ w ∈ S, w ∈ stock) (live : LiveWord mask target k t S) :
    witnessWord entry ∈ S := by
  obtain ⟨w,p,n⟩ := entry
  simp only [essentialB, Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨mp,mn⟩,tp⟩,tn⟩,unequal⟩,rest⟩ := ok
  by_contra no
  have all : ∀ x ∈ S, AgreesAt p n x := by
    intro x hx
    have h := List.all_eq_true.mp rest x (sub x hx)
    have hw : x ≠ w := fun e => no (by simpa [witnessWord, e] using hx)
    simpa [hw, AgreesAt] using h
  have agree := liveAgrees live (mp.trans mn.symm) all
  have falseBit : target.testBit n = false := by simpa using tn
  simp [AgreesAt, tp, falseBit] at agree

theorem essentialWordsIn {stock : List Word} {witnesses : List Witness} {S : Finset Word} {k t : Nat}
    (ok : witnesses.all (essentialB mask target stock) = true)
    (sub : ∀ w ∈ S, w ∈ stock) (live : LiveWord mask target k t S) :
    (witnesses.map witnessWord).toFinset ⊆ S := by
  intro w hw
  obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  exact essentialRequired (List.all_eq_true.mp ok entry mem) sub live

theorem essentialLower {stock : List Word} {witnesses : List Witness} {minimum : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (bound : minimum ≤ (witnesses.map witnessWord).toFinset.card - 1) :
    Lower mask stock target minimum := by
  intro values build hit
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive masked build hit proper
  have card := Finset.card_le_card (essentialWordsIn ok sub live)
  have size := (liveWordSize live).2
  omega

theorem essentialLift {stock cutStock : List Word} {witnesses : List Witness} {minimum cut prior : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (submask : mask &&& cut = cut)
    (cutProper : properWord cut (target &&& cut))
    (supplies : ∀ w ∈ stock, AvailableWord cut cutStock (w &&& cut))
    (known : Lower cut cutStock (target &&& cut) prior)
    (bound : minimum ≤ prior + (flatSet cut (witnesses.map witnessWord).toFinset).card) :
    Lower mask stock target minimum := by
  intro values build hit
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive masked build hit proper
  have subW := essentialWordsIn ok sub live
  have subFlat : flatSet cut (witnesses.map witnessWord).toFinset ⊆ flatSet cut S :=
    Finset.filter_subset_filter _ subW
  have card := Finset.card_le_card subFlat
  have pf : ¬maskedFlat cut target := by simpa [maskedFlat, properWord] using cutProper
  obtain ⟨n, budget, built⟩ := maskedBuild live cut submask pf
  have starts : ∀ w ∈ projectedStock cut S, AvailableWord cut cutStock w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image] at hw
    rcases hw with rfl | rfl | ⟨x,hx,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact supplies _ (sub _ hx)
  obtain ⟨ys,len,built',out⟩ := buildableWords built starts
  have lower := known ys built' out
  omega

def unpackWitnesses (stock : List Word) (codes : List Nat) : List Witness :=
  List.rec [] (fun code _ rest =>
    (stock.getD (code >>> 18) 0, (code >>> 9) &&& 511, code &&& 511) :: rest) codes

def DagAuto (mask goal : Word) (select : Fin rows → Fin rows) : Prop :=
  Function.Surjective select ∧ relabel select mask = mask ∧ relabel select goal = goal

abbrev WordMoveStep := List (Word × Nat) × List (Word × Nat)
abbrev WordMove := List WordMoveStep

def mixStep (m : WordMoveStep) (w : Word) : Word :=
  let left := List.rec 0 (fun (part,n) _ acc => ((w &&& part) <<< n) ||| acc) m.1
  let right := List.rec 0 (fun (part,n) _ acc => ((w &&& part) >>> n) ||| acc) m.2
  left ||| right

def BitLinear (f : Word → Word) : Prop :=
  ∀ w i, (f w).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (2 ^ j)).testBit i = true

theorem bitLinearZero : BitLinear (fun _ => 0) := by
  simp [BitLinear]

theorem bitLinearOr {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f w ||| g w) := by
  intro w i
  change ((f w ||| g w).testBit i = true) ↔ _
  simp only [Nat.testBit_or, Bool.or_eq_true]
  rw [hf w i, hg w i]
  constructor
  · rintro (⟨j,hw,hj⟩ | ⟨j,hw,hj⟩)
    · exact ⟨j,hw,Or.inl hj⟩
    · exact ⟨j,hw,Or.inr hj⟩
  · rintro ⟨j,hw,hj | hj⟩
    · exact Or.inl ⟨j,hw,hj⟩
    · exact Or.inr ⟨j,hw,hj⟩

theorem bitLinearLeft (mask n : Nat) : BitLinear (fun w => (w &&& mask) <<< n) := by
  intro w i
  simp only [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hw, hm⟩
    exact ⟨i-n,hw,h,rfl,hm⟩
  · rintro ⟨j,hw,h,rfl,hm⟩
    exact ⟨h,hw,hm⟩

theorem bitLinearRight (mask n : Nat) : BitLinear (fun w => (w &&& mask) >>> n) := by
  intro w i
  simp only [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hw,hm⟩
    exact ⟨n+i,hw,rfl,hm⟩
  · rintro ⟨j,hw,rfl,hm⟩
    exact ⟨hw,hm⟩

theorem mixStepLinear (move : WordMoveStep) : BitLinear (mixStep move) := by
  obtain ⟨left, right⟩ := move
  unfold mixStep
  apply bitLinearOr
  · induction left with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearLeft part count) ih
  · induction right with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearRight part count) ih

def mixMove (move : WordMove) (w : Word) : Word :=
  (List.rec (motive := fun _ => Word → Word) id
    (fun step _ next w => next (mixStep step w)) move) w

theorem bitLinearId : BitLinear id := by
  intro w i
  change w.testBit i = true ↔ ∃ j, w.testBit j = true ∧ (2 ^ j).testBit i = true
  simp [Nat.testBit_two_pow]

theorem bitLinearComp {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f (g w)) := by
  intro w i
  change (f (g w)).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (g (2 ^ j))).testBit i = true
  rw [hf]
  constructor
  · rintro ⟨j,gj,fj⟩
    obtain ⟨k,wk,gk⟩ := (hg w j).mp gj
    exact ⟨k,wk,(hf (g (2^k)) i).mpr ⟨j,gk,fj⟩⟩
  · rintro ⟨j,wj,h⟩
    obtain ⟨k,gk,fk⟩ := (hf (g (2^j)) i).mp h
    exact ⟨k,(hg w k).mpr ⟨j,wj,gk⟩,fk⟩

theorem mixMoveLinear (move : WordMove) : BitLinear (mixMove move) := by
  induction move with
  | nil => exact bitLinearId
  | cons op ops ih =>
    change BitLinear (fun w => mixMove ops (mixStep op w))
    exact bitLinearComp ih (mixStepLinear op)

def permuteAxes (axes : List Nat) (offset row : Nat) : Nat :=
  offset ^^^ (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun j _ next i => (if row.testBit i then 1 <<< j else 0) ||| next (i + 1)) axes) 0

theorem relabelLinear (select : Fin rows → Fin rows) : BitLinear (relabel select) := by
  intro w i
  by_cases inside : i < rows
  · let ii : Fin rows := ⟨i,inside⟩
    change (relabel select w).testBit ii.val = true ↔ _
    rw [relabelBit]
    constructor
    · intro h
      refine ⟨(select ii).val,h,?_⟩
      change (relabel select (2 ^ (select ii).val)).testBit ii.val = true
      rw [relabelBit, Nat.testBit_two_pow]
      simp
    · rintro ⟨j,h,bit⟩
      change (relabel select (2^j)).testBit ii.val = true at bit
      rw [relabelBit, Nat.testBit_two_pow, decide_eq_true_eq] at bit
      exact bit ▸ h
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
    simp [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]

theorem wordMoveAgreement {select : Fin rows → Fin rows} {mask : Word} {move : WordMove}
    (bounded : Masked (fullMask rows) mask)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = relabel select (2 ^ i.val))
    {w : Word} (masked : Masked mask w) : mixMove move w = relabel select w := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [mixMoveLinear, relabelLinear]
  have source {j : Nat} (bit : w.testBit j = true) :
      mixMove move (2^j) = relabel select (2^j) := by
    have m : mask.testBit j = true := by
      have eq := congrArg (fun x : Nat => x.testBit j) masked
      simpa [Nat.testBit_and, bit] using eq
    have within : j < rows := by
      have eq := congrArg (fun x : Nat => x.testBit j) bounded
      simpa [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, m] using eq
    exact basis ⟨j,within⟩ m
  constructor <;> rintro ⟨j,hj,hi⟩
  · exact ⟨j,hj,by rwa [← source hj]⟩
  · exact ⟨j,hj,by rwa [source hj]⟩

theorem relabelBasis {select inverse : Fin rows → Fin rows}
    (left : ∀ i, inverse (select i) = i) :
    ∀ j : Fin rows, select (inverse j) = j →
      relabel select (2 ^ j.val) = 2 ^ (inverse j).val := by
  intro j right
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · let pos : Fin rows := ⟨i,inside⟩
    change (relabel select (2 ^ j.val)).testBit pos.val = _
    rw [relabelBit, Nat.testBit_two_pow, Nat.testBit_two_pow]
    apply (Bool.eq_iff_iff).mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro eq
      have e : j = select pos := Fin.ext eq
      rw [e,left]
    · intro eq
      have hp : inverse j = pos := Fin.ext eq
      rw [← hp, right]
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside), Nat.testBit_two_pow]
    have ne : (inverse j).val ≠ i := by have := (inverse j).isLt; omega
    simp [ne]

theorem dagAutoFromMove {select inverse : Fin rows → Fin rows} {mask goal : Word} {move : WordMove}
    (left : ∀ i, inverse (select i) = i)
    (right : ∀ i, select (inverse i) = i)
    (bm : Masked (fullMask rows) mask)
    (gm : Masked mask goal)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val)
    (sameMask : mixMove move mask = mask) (sameGoal : mixMove move goal = goal) :
    DagAuto mask goal select ∧ ∀ w, Masked mask w → mixMove move w = relabel select w := by
  have agree {w : Word} (hw : Masked mask w) : mixMove move w = relabel select w :=
    wordMoveAgreement bm (fun i h => (basis i h).trans (relabelBasis left i (right i)).symm) hw
  exact ⟨⟨fun i => ⟨inverse i,right i⟩,(agree (by simp [Masked])).symm.trans sameMask,
    (agree gm).symm.trans sameGoal⟩,fun _ h => agree h⟩

theorem maskedBelow {mask w : Word} (bm : Masked (fullMask rows) mask)
    (bw : Masked mask w) : Masked (fullMask rows) w := by
  unfold Masked at *
  rw [← bw, Nat.land_assoc, bm, bw]

theorem maskedTransfer {mask w : Word} {select : Fin rows → Fin rows}
    (same : relabel select mask = mask) (hw : Masked mask w) :
    Masked mask (relabel select w) := by
  unfold Masked at *
  rw [← same, ← relabelAnd, hw]

theorem liveMaskedImage {mask goal : Word} {select : Fin rows → Fin rows}
    (auto : DagAuto mask goal select) (maskBounds : Masked (fullMask rows) mask)
    {k t : Nat} {S : Finset Word} (live : LiveWord mask goal k t S)
    (masked : ∀ w ∈ S, Masked mask w) :
    LiveWord mask goal k t (S.image (relabel select)) := by
  let f := relabel select
  have hmask : f mask = mask := auto.2.1
  have inj {a b : Word} (ma : Masked mask a) (mb : Masked mask b) :
      f a = f b → a = b :=
    relabelInj select auto.1 (maskedBelow maskBounds ma) (maskedBelow maskBounds mb)
  have proper {a : Word} (ma : Masked mask a) (ha : properWord mask a) :
      properWord mask (f a) := by
    exact ⟨fun eq => ha.1 (inj ma (by simp [Masked]) (eq.trans (relabelZero select).symm)),
      fun eq => ha.2 (inj ma (by simp [Masked]) (eq.trans hmask.symm))⟩
  have freshImage {S : Finset Word} {v : Word} (hv : v ∉ S) (mv : Masked mask v)
      (ms : ∀ w ∈ S, Masked mask w) : f v ∉ S.image f := by
    intro hw
    obtain ⟨w,hs,eq⟩ := Finset.mem_image.mp hw
    exact hv (inj (ms w hs) mv eq ▸ hs)
  induction live using LiveWord.ind with
  | stop hp =>
    rw [Finset.image_singleton, auto.2.2]
    exact LiveWord.stop hp
  | @unary k t U a ha fresh tail ih =>
    let v := mask ^^^ a
    have ma := masked a (Finset.mem_insert_self ..)
    have mv : Masked mask v := by
      apply maskedGate (bank := [a]) (by simpa using ma)
      exact Or.inl ⟨a, Or.inr (Or.inr (by simp)), rfl⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem hU)
    have fve : f v = mask ^^^ f a := by
      change relabel select (mask ^^^ a) = _
      rw [relabelXor, auto.2.1]
    have ht := ih hnew
    have hf := freshImage fresh mv masked
    change LiveWord mask goal (k+1) (t+1) ((insert a U).image f)
    rw [Finset.image_insert] at ht hf
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht hf
    rw [Finset.image_insert]
    exact LiveWord.unary (proper ma ha) hf ht
  | @binary k t U a b op pa pb ab fresh tail ih =>
    let v := binWord op a b
    have ma := masked a (Finset.mem_insert_self ..)
    have mb := masked b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have mv : Masked mask v := by
      apply maskedGate (bank := [a,b]) (by simpa using And.intro ma mb)
      exact Or.inr ⟨a,b,Or.inr (Or.inr (by simp)),Or.inr (Or.inr (by simp)),by
        cases op <;> simp [v, binWord]⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
    have fve : f v = binWord op (f a) (f b) := by
      cases op
      · exact relabelAnd ..
      · exact relabelOr ..
    have ht := ih hnew
    have hf := freshImage fresh mv masked
    change LiveWord mask goal (k+1) t ((insert a (insert b U)).image f)
    rw [Finset.image_insert] at ht
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht
    rw [Finset.image_insert, Finset.image_insert, fve] at hf
    rw [Finset.image_insert, Finset.image_insert]
    exact LiveWord.binary (proper ma pa) (proper mb pb) (fun h => ab (inj ma mb h)) hf ht

def dagMoveWords (m : WordMove) (ws : List Word) : List Word :=
  List.rec [] (fun w _ next => insertWord (mixMove m w) next) ws

theorem dagMoveSet {m : WordMove} {ws : List Word} {select : Fin rows → Fin rows}
    (agree : ∀ w ∈ ws, mixMove m w = relabel select w) :
    (dagMoveWords m ws).toFinset = ws.toFinset.image (relabel select) := by
  induction ws with
  | nil => simp [dagMoveWords]
  | cons w ws ih =>
    change (insertWord (mixMove m w) (dagMoveWords m ws)).toFinset = _
    rw [insertWordSet, ih (fun w hw => agree _ (List.mem_cons_of_mem _ hw)),
      agree _ List.mem_cons_self, List.toFinset_cons, Finset.image_insert]

abbrev RowChart := { rows : List Nat // rows.length = 24 }

def chartRow (chart : RowChart) (i : Nat) : Nat :=
  chart.val.getD i 0

def chartBits (w : Word) (rows : List Nat) : Word :=
  List.rec 0 (fun r _ packed => ((w >>> r) &&& 1) ||| (packed <<< 1)) rows

theorem chartBitsBit (w : Word) (rows : List Nat) (i : Nat) (hi : i < rows.length) :
    (chartBits w rows).testBit i = w.testBit (rows.getD i 0) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons row rows ih =>
    change (((w >>> row) &&& 1) ||| (chartBits w rows <<< 1)).testBit i = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have lt : i < rows.length := by simpa using hi
      simp [ih i lt, Nat.testBit_succ]

def chartWord (chart : RowChart) (w : Word) : Word := chartBits w chart.val

def ChartOK (goal : Word) (chart : RowChart) : Prop :=
  (∀ i : Fin 12, goal.testBit (chartRow chart i.val) = true) ∧
  (∀ i : Fin 12, goal.testBit (chartRow chart (12+i.val)) = false)

def chartCheck (goal : Word) (chart : Option RowChart) : Bool :=
  chart.all fun c => @decide (ChartOK goal c) (by unfold ChartOK; infer_instance)

theorem chartOfCheck {goal : Word} {chart : Option RowChart}
    (ok : chartCheck goal chart = true) (c : RowChart) (eq : chart = some c) :
    ChartOK goal c := by
  subst chart
  unfold ChartOK
  exact of_decide_eq_true ok

theorem chartWordBit (chart : RowChart) (w : Word) {i : Nat} (hi : i < 24) :
    (chartWord chart w).testBit i = w.testBit (chartRow chart i) := by
  exact chartBitsBit w chart.val i (by rw [chart.property]; exact hi)

theorem chartPos {goal : Word} {chart : RowChart} (ok : ChartOK goal chart) {i : Nat} (hi : i < 12) :
    goal.testBit (chartRow chart i) = true := ok.1 ⟨i,hi⟩

theorem chartNeg {goal : Word} {chart : RowChart} (ok : ChartOK goal chart) {i : Nat} (hi : i < 12) :
    goal.testBit (chartRow chart (12+i)) = false := ok.2 ⟨i,hi⟩

theorem chartRectangles {goal : Word} {chart : RowChart} {ws : List Word}
    (ok : ChartOK goal chart) (nd : ws.Nodup) (kw : KWPartition goal ws.toFinset) :
    PackedRect.rectOK1 (ws.map (chartWord chart)) = true := by
  obtain ⟨f, good, rectangle⟩ := kw
  let label := fun p n => f (chartRow chart p) (chartRow chart (12+n))
  let part := fun w => ((fun q : Nat => q < 144 ∧ label (q/12) (q % 12) = w),
    PackedRect.rectW (chartWord chart w))
  have partition : PackedRect.Part (ws.map part) := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro z hz
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      intro p n p' n' hp hn hp' hn' h h'
      have divmod (a b : Nat) (lt : b < 12) :
          (12*a+b)/12 = a ∧ (12*a+b)%12 = b := by omega
      have h1 := h.2
      have h2 := h'.2
      rw [(divmod p n hn).1, (divmod p n hn).2] at h1
      rw [(divmod p' n' hn').1, (divmod p' n' hn').2] at h2
      refine ⟨by omega,?_⟩
      rw [(divmod p n' hn').1, (divmod p n' hn').2]
      exact (rectangle _ _ _ _ (chartPos ok hp) (chartPos ok hp') (chartNeg ok hn)
        (chartNeg ok hn') (h1.trans h2.symm)).trans h1
    · intro z hz q hq
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      exact hq.1
    · rw [List.pairwise_map]
      exact List.Pairwise.imp (fun hne q h1 h2 => hne (h1.2.symm.trans h2.2)) nd
    · intro q hq
      have member := (good _ _ (chartPos ok (show q/12 < 12 by omega))
        (chartNeg ok (Nat.mod_lt q (by decide : 0 < 12)))).1
      exact ⟨_, List.mem_map.mpr ⟨_,List.mem_toFinset.mp member,rfl⟩,hq,rfl⟩
    · intro z hz q hq
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      obtain ⟨bound, same⟩ := hq
      have hp : q/12 < 12 := by omega
      have hn : q % 12 < 12 := Nat.mod_lt _ (by decide)
      have h := (good _ _ (chartPos ok hp) (chartNeg ok hn)).2
      change (label (q/12) (q % 12)).testBit (chartRow chart (q/12)) = true ∧
        (label (q/12) (q % 12)).testBit (chartRow chart (12+q % 12)) = false at h
      rw [same] at h
      have bit := PackedRect.rectW_tb (chartWord chart w) (q/12) (q % 12) hp hn
        ((chartWordBit chart w (by omega)).trans h.1)
        ((chartWordBit chart w (by omega)).trans h.2)
      rwa [Nat.div_add_mod] at bit
  have hw := PackedRect.avOK1_sound partition
  simpa only [PackedRect.rectOK1, List.map_map, Function.comp_def, part] using hw

theorem tightChart {goal mask : Word} {chart : RowChart} {ws : List Word} {fuel : Nat}
    (ok : ChartOK goal chart) (tight : ws.length = fuel + 1)
    (viable : WordViable mask goal (fuel,ws,[])) : PackedRect.rectOK1 (ws.map (chartWord chart)) = true := by
  obtain ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel at cap
  have card := (liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at card
  change (ws : List Word).length + t ≤ k + 1 at card
  have ht : t = 0 := by omega
  have hk : ws.toFinset.card = k + 1 := by
    have q : ws.toFinset.card = ws.length := List.toFinset_card_of_nodup nd
    omega
  subst t
  exact chartRectangles ok nd (kwFromLive live hk)

def dagForceWord {α : Type} (word : Word) (cont : Word → α) : α :=
  Nat.rec (cont 0) (fun k _ => cont (k + 1)) word

theorem dagForceWordEq {α : Type} (word : Word) (cont : Word → α) :
    dagForceWord word cont = cont word := by cases word <;> rfl

def dagForceWords (words : List Word) (cont : List Word → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Word → Bool) → Bool) (fun k => k [])
    (fun w _ next k => dagForceWord w (fun v => next (fun rest => k (v :: rest)))) words) cont

theorem dagForceWordsEq (words : List Word) (cont : List Word → Bool) :
    dagForceWords words cont = cont words := by
  induction words generalizing cont with
  | nil => rfl
  | cons w ws ih =>
    change dagForceWord w (fun v => dagForceWords ws (fun rest => cont (v :: rest))) = _
    rw [dagForceWordEq, ih]

def dagBoundCloses (target : Word) (state : RowState) (bound : Bound) : Bool :=
  let (mask, stock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    dagForceWord (fuel - flatCount mask ws) (fun remaining =>
      if Nat.blt remaining lower then
        dagForceWords (recipeStart mask stock ws) (fun start =>
          if Nat.blt (start.length + remaining) lower then
            dagForceWords (recipeClosure mask stock history start) (fun needed =>
              if Nat.blt (needed.length + remaining) lower then
                dagForceWords (replayRecipes mask needed history.reverse stock) (fun replay =>
                  decide (replay.length + remaining < lower) &&
                    ws.all (fun w => availableB mask (replay ++ stock) (w &&& mask)))
              else false)
          else false)
      else false)

theorem dagBoundClosesEq (target : Word) (state : RowState) (bound : Bound) :
    dagBoundCloses target state bound = boundCloses target state bound := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨mask, stock, lower, goal⟩ := bound
  simp [dagBoundCloses, boundCloses, dagForceWordsEq, dagForceWordEq, Nat.blt_eq]

def dagKnownCloses (target : Word) (bounds : List Bound) (state : RowState) : Bool :=
  List.rec false (fun bound _ later => dagBoundCloses target state bound || later) bounds

theorem dagKnownClosesEq (target : Word) (bounds : List Bound) (state : RowState) :
    dagKnownCloses target bounds state = knownCloses target bounds state := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (dagBoundCloses target state bound || dagKnownCloses target bounds state) =
      (boundCloses target state bound || knownCloses target bounds state)
    rw [dagBoundClosesEq, ih]

abbrev DagLink := Nat × Nat
abbrev DagLinks := Nat → Nat → Option DagLink

def dagAllowedRoot (witnesses : List Witness) (ws : List Word) : Bool :=
  witnesses.all (fun entry => ws.contains (witnessWord entry))

def dagTrace (mask : Word) (stock : List Word) (fuel : Nat) (forest : Forest)
    (i : Nat) : Option RowState :=
  (Nat.rec (motive := fun _ => Nat → Option RowState) (fun _ => none)
    (fun _ previous j =>
      let (parent, token) := forest j
      if parent == 0 then
        if token < 2 ^ stock.length then some (rootState stock fuel token) else none
      else (previous (parent - 1)).bind (childState mask token)) (fuel + 1)) i

def dagRef (count : Nat) (states : Nat → Option RowState)
    (moves : Array WordMove) (links : DagLinks) (parent token : Nat) (state : RowState) : Bool :=
  match links parent token with
  | none => false
  | some (destination, auto) =>
    Nat.blt destination count &&
      match states destination with
      | none => false
      | some saved =>
        saved.1 == state.1 &&
          if auto == 0 then saved.2.1 == state.2.1
          else match moves[auto-1]? with
               | none => false
               | some m => saved.2.1 == dagMoveWords m state.2.1

def dagPartition (directed : Bool) (ws : List Word) : Word → Word → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      Nat.beq p 0 || Nat.beq n 0 ||
      dagForceWord (p &&& w) (fun up =>
        dagForceWord (n &&& w) (fun down =>
          rest up down &&
            dagForceWord (p ^^^ up) (fun offP =>
              dagForceWord (if directed then n else n ^^^ down) (rest offP))))) ws

theorem dagOffBits {v w : Word} {i : Nat} (bit : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at bit
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at bit ⊢

theorem dagPartitionSound {directed : Bool} {ws : List Word} {positive negative : Word}
    (fail : dagPartition directed ws positive negative = false) :
    ∃ p n, positive.testBit p = true ∧ negative.testBit n = true ∧
      ∀ w ∈ ws, if directed then w.testBit p = true → w.testBit n = true
                  else w.testBit p = w.testBit n := by
  have nonempty {w : Word} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all
    apply hn
    apply Nat.eq_of_testBit_eq
    intro i
    simp [all i]
  induction ws generalizing positive negative with
  | nil =>
    change (Nat.beq positive 0 || Nat.beq negative 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p,hp⟩ := nonempty (w := positive) (fun eq => by simp [eq] at fail)
    obtain ⟨n,hn⟩ := nonempty (w := negative) (fun eq => by simp [eq] at fail)
    exact ⟨p,n,hp,hn,by simp⟩
  | cons w ws ih =>
    change (Nat.beq positive 0 || Nat.beq negative 0 ||
      dagForceWord (positive &&& w) (fun up =>
        dagForceWord (negative &&& w) (fun down =>
          dagPartition directed ws up down &&
            dagForceWord (positive ^^^ up) (fun offP =>
              dagForceWord (if directed then negative else negative ^^^ down)
                (dagPartition directed ws offP))))) = false at fail
    simp only [dagForceWordEq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p,n,hp,hn,agree⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p,n,hp.1,hn.1,?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | tail
      · simp [hp.2, hn.2]
      · exact agree _ tail
    · obtain ⟨p,n,hp,hn,agree⟩ := ih off
      have hp' := dagOffBits hp
      cases mode : directed
      · have hn' : negative.testBit n = true ∧ w.testBit n = false := by
          apply dagOffBits
          simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn'.1,?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2, hn'.2]
        · simpa [mode] using agree _ tail
      · have hn' : negative.testBit n = true := by simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn',?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2]
        · simpa [mode] using agree _ tail

theorem dagPartitionLive {mask goal : Word} {ws : List Word} {k t : Nat} {directed : Bool}
    (goalMask : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed = true → t = 0) :
    dagPartition directed ws goal (mask ^^^ goal) = true := by
  by_contra fail
  have openPair : dagPartition directed ws goal (mask ^^^ goal) = false := by
    cases h : dagPartition directed ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p,n,hp,hn,agree⟩ := dagPartitionSound openPair
  have pm := positiveInMask goalMask hp
  have nm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have implied := fun ht : goal.testBit n = true => positiveInMask goalMask ht
    cases hm : mask.testBit n <;> cases ht : goal.testBit n <;> simp_all
  cases mode : directed with
  | false =>
    have same := liveAgrees live (pm.trans nm.1.symm) (fun w hw => by
      simpa [mode,AgreesAt] using agree w (List.mem_toFinset.mp hw))
    simp [AgreesAt, hp, nm.2] at same
  | true =>
    have ht := noNot mode
    subst t
    obtain ⟨w,hw,a,b⟩ := liveDirected live hp nm.2
    have same := agree w (List.mem_toFinset.mp hw)
    simp [mode, a, b] at same

abbrev DagSample := Nat × Nat
abbrev DagSignals := Word × Word
abbrev DagCounts := Word × Word × Word

def dagForceCache (tags : List DagSignals) (use : List DagSignals → Bool) : Bool :=
  (List.rec (motive := fun _ => (List DagSignals → Bool) → Bool) (fun k => k [])
    (fun tag _ next k =>
      dagForceWord tag.1 (fun up => dagForceWord tag.2 (fun down =>
        next (fun tail => k ((up,down)::tail))))) tags) use

theorem dagForceCacheEq (tags : List DagSignals) (use : List DagSignals → Bool) :
    dagForceCache tags use = use tags := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag rest ih =>
    obtain ⟨a,b⟩ := tag
    change dagForceWord a (fun up => dagForceWord b (fun down =>
      dagForceCache rest (fun tail => use ((up,down)::tail)))) = _
    simp only [dagForceWordEq, ih]

def dagSignalContrast (directed : Bool) (full : Word) (tag : DagSignals) : Word :=
  if directed then tag.1 &&& (tag.2 ^^^ full) else tag.1 ^^^ tag.2

def dagCountStep (acc : DagCounts) (column : Word) : DagCounts :=
  (acc.1 ||| column, acc.2.1 ||| (acc.1 &&& column), acc.2.2 ||| (acc.2.1 &&& column))

def dagCountSigns (directed : Bool) (full : Word) (tags : List DagSignals)
    (use : DagCounts → Bool) : Bool :=
  (List.rec (motive := fun _ => (DagCounts → Bool) → Bool) (fun k => k (0,0,0))
    (fun tag _ more k =>
      dagForceWord (dagSignalContrast directed full tag) (fun column =>
        more (fun acc =>
          dagForceWord (acc.1 ||| column) (fun once =>
            dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
              dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => k (once,twice,thrice)))))))
    tags) use

theorem dagCountSignsEq (directed : Bool) (full : Word) (tags : List DagSignals)
    (use : DagCounts → Bool) : dagCountSigns directed full tags use =
    use (tags.foldr (fun tag acc => dagCountStep acc (dagSignalContrast directed full tag)) (0,0,0)) := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag tags ih =>
    change dagForceWord (dagSignalContrast directed full tag) (fun column =>
      dagCountSigns directed full tags (fun acc =>
        dagForceWord (acc.1 ||| column) (fun once =>
          dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
            dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => use (once,twice,thrice)))))) = _
    simp only [dagForceWordEq, ih]
    rfl

def dagHighest (value : Word) : Nat :=
  (Nat.rec (motive := fun _ => Word → Nat → Nat) (fun _ offset => offset)
    (fun i next w offset =>
      let shift := 1 <<< i
      dagForceWord (w >>> shift) (fun upper =>
        if Nat.beq upper 0 then next w offset else next upper (offset+shift))) 8) value 0

def dagSampleMiss (sample : DagSample) (full : Word) (normal tight : DagCounts)
    (x y out : DagSignals) (directed : Bool) (op keep : Nat) : List Nat :=
  let counts := if directed then tight else normal
  let dx := if keep.testBit 0 then 0 else dagSignalContrast directed full x
  let dy := if op == 2 || keep.testBit 1 then 0 else dagSignalContrast directed full y
  let rest := counts.2.2 ||| (counts.2.1 ^^^ (counts.2.1 &&& dx &&& dy)) |||
    (counts.1 ^^^ (counts.1 &&& (dx ||| dy)))
  dagForceWord ((rest ||| dagSignalContrast directed full out) ^^^ full) (fun missing =>
    if Nat.beq missing 0 then [] else [unpack sample.1 18 (dagHighest missing)])

def dagPairReject (mask goal : Word) (directed : Bool) (ws : List Word) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    let p := code &&& 511
    let n := code >>> 9
    goal.testBit p && mask.testBit n && !goal.testBit n &&
      ws.all (fun w => if directed then !(w.testBit p) || w.testBit n
                       else w.testBit p == w.testBit n)

theorem dagPairsOpen {mask goal : Word} {ws : List Word} {pairs : List Nat} {k t : Nat} {directed : Bool}
    (masked : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed = true → t = 0) : dagPairReject mask goal directed ws pairs = false := by
  apply Bool.eq_false_iff.mpr
  intro close
  obtain ⟨code,_,check⟩ := List.any_eq_true.mp close
  simp only [Bool.and_eq_true, Bool.not_eq_true, List.all_eq_true] at check
  obtain ⟨⟨⟨hp, mn⟩, hn⟩, bank⟩ := check
  have neg : goal.testBit (code >>> 9) = false := by simpa using hn
  cases mode : directed
  · have h := liveAgrees live ((positiveInMask masked hp).trans mn.symm) (fun w hw => by
      have pair := bank _ (List.mem_toFinset.mp hw)
      simpa [mode, AgreesAt] using pair)
    simp [AgreesAt, hp, neg] at h
  · have ht := noNot mode
    subst t
    obtain ⟨word,mem,on,off⟩ := liveDirected live hp neg
    have pair := bank _ (List.mem_toFinset.mp mem)
    simp [mode,on,off] at pair

def dagLocal (mask goal : Word) (chart : Option RowChart)
    (cut : CutCheck) (state : RowState) : Bool :=
  let (fuel,ws,_) := state
  ws.length > fuel + 1 ||
    (!ws.contains goal &&
      (fuel == 0 ||
        (if ws.length == fuel + 1 then
           chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c)))
         else false) ||
        cut state ||
        (if ws.length == fuel + 1 then !dagPartition true ws goal (mask ^^^ goal)
         else !dagPartition false ws goal (mask ^^^ goal))))

def dagSizeFloor (n op keep : Nat) : Nat :=
  (n - (if keep.testBit 0 then 0 else 1) -
    (if op == 2 || keep.testBit 1 then 0 else 1)) + 1

def dagTooWide (n fuel token : Nat) : Bool :=
  dagSizeFloor n (token / 4 % 3) (token % 4) > (fuel-1) + 1

def dagKept (ws : List Word) (op keep x y : Nat) : List Word :=
  keepWord (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)

def dagGateWord (mask op x y : Word) : Word :=
  if Nat.beq op 0 then x &&& y else if Nat.beq op 1 then x ||| y else mask ^^^ x

def dagDirectChild (mask : Word) (state : RowState) (a b op keep x y out : Nat) : Option RowState :=
  let (fuel, ws, history) := state
  if fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b) then none
  else if out == 0 || out == mask || ws.contains out then none
  else
    some (fuel-1, insertWord out (dagKept ws op keep x y), (out,x,y) :: history)

theorem dagDirectChildEq {mask a b op keep : Nat} {state : RowState}
    (hb : b < 64) (hop : op < 3) (hk : keep < 4) :
    let x := state.2.1.getD a 0
    let y := state.2.1.getD b 0
    dagDirectChild mask state a b op keep x y (dagGateWord mask op x y) =
      childState mask (gateToken a b op keep) state := by
  obtain ⟨fuel,ws,history⟩ := state
  obtain ⟨keepEq,opEq,aEq,bEq⟩ := gateTokenFields (a := a) hb hop hk
  simp only [childState, keepEq, opEq, aEq, bEq]
  rfl

abbrev DagTagged := Word × DagSignals

def dagTagBases (stock : List Word) (positive negative width : Nat) : List DagTagged :=
  (List.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun w _ next i => (w, unpack positive width i, unpack negative width i) :: next (i+1)) stock) 0

def dagTagRoot (bank : List DagTagged) (token : Nat) : List DagTagged :=
  (List.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun tag _ next k =>
      if Nat.beq (k &&& 1) 0 then next (k >>> 1) else tag :: next (k >>> 1)) bank) token

def dagTagKeep (keep : Bool) (w : Word) (bank : List DagTagged) : List DagTagged :=
  if keep then bank
  else List.rec [] (fun tag tail next => if Nat.beq tag.1 w then tail else tag :: next) bank

def dagTagInsert (tag : DagTagged) (bank : List DagTagged) : List DagTagged :=
  List.rec [tag] (fun old tail next => if Nat.ble tag.1 old.1 then tag :: old :: tail else old :: next) bank

def dagTagStep (mask full token : Word) (bank : List DagTagged) : List DagTagged :=
  let keep := token % 4
  let op := token / 4 % 3
  let x := bank.getD (token / (4*3*64)) (0,0,0)
  let y := bank.getD (token / (4*3) % 64) (0,0,0)
  let tag := (dagGateWord mask op x.1 y.1, dagGateWord full op x.2.1 y.2.1, dagGateWord full op x.2.2 y.2.2)
  dagTagInsert tag (dagTagKeep (op == 2 || keep.testBit 1) y.1 (dagTagKeep (keep.testBit 0) x.1 bank))

def dagTraceTags (mask width : Word) (root : List DagTagged) (fuel : Nat) (forest : Forest)
    (i : Nat) : List DagSignals :=
  let tags := (Nat.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun _ previous j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then dagTagRoot root token
      else dagTagStep mask (fullMask width) token (previous (parent-1))) (fuel+1)) i
  List.rec [] (fun tag _ rest => tag.2 :: rest) tags

def dagPackWords (ws : List Word) : Word :=
  List.rec 0 (fun w _ tail => (w &&& fullMask 512) ||| (tail <<< 512)) ws

def dagLaneMarks (n : Nat) : Word :=
  Nat.rec 0 (fun _ more => 1 ||| (more <<< 512)) n

def dagOmitted (a b : Nat) (left right : Bool) : Word :=
  (if left then 0 else 1 <<< (512*a)) ||| (if right then 0 else 1 <<< (512*b))

def dagPackedPair (mask goal packed marks erased out : Word) (directed : Bool) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    dagForceWord code (fun code =>
      dagForceWord (code &&& 511) (fun p =>
        dagForceWord (code >>> 9) (fun n =>
          let up := (packed >>> p) &&& marks
          let down := (packed >>> n) &&& marks
          let contrast := if directed then up &&& (down ^^^ marks) else up ^^^ down
          let gateOK := if directed then !out.testBit p || out.testBit n else out.testBit p == out.testBit n
          goal.testBit p && mask.testBit n && !goal.testBit n && Nat.blt p 512 && Nat.blt n 512 &&
            gateOK && Nat.beq (contrast &&& (marks ^^^ erased)) 0)))

theorem dagPackBits {ws : List Word} {i row : Nat} (inside : i < ws.length) (width : row < 512) :
    (dagPackWords ws).testBit (512*i+row) = (ws.getD i 0).testBit row := by
  induction ws generalizing i with
  | nil => simp at inside
  | cons w ws ih =>
    change ((w &&& fullMask 512) ||| (dagPackWords ws <<< 512)).testBit (512*i+row) = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp [fullMask, Nat.testBit_two_pow_sub_one, width, Nat.not_le.mpr width]
    | succ i =>
      have hi : i < ws.length := by simpa using inside
      have crossed : 512 ≤ 512*i.succ+row := by omega
      have offset : 512*i.succ+row-512 = 512*i+row := by omega
      have past : ¬ 512*i.succ+row < 512 := by omega
      simp [crossed, offset, fullMask, Nat.testBit_two_pow_sub_one, past, ih hi]

theorem dagMarkBits {length i : Nat} (inside : i < length) :
    (dagLaneMarks length).testBit (512*i) = true := by
  induction length generalizing i with
  | zero => omega
  | succ length ih =>
    change (1 ||| (dagLaneMarks length <<< 512)).testBit (512*i) = true
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have hi : i < length := by omega
      have crossed : 512 ≤ 512*i.succ := by omega
      have offset : 512*i.succ-512 = 512*i := by omega
      simp [crossed, offset, ih hi]

def dagCheckChildren (mask goal : Word) (chart : Option RowChart) (cut : CutCheck)
    (reference : Nat → RowState → Bool) (state : RowState) (sample : DagSample) (tags : List DagSignals) : Bool :=
  let n := state.2.1.length
  (n ≤ 64) && !state.2.1.contains goal &&
  dagForceWord (dagPackWords state.2.1) (fun packed =>
    dagForceWord (dagLaneMarks n) (fun marks =>
      dagForceCache tags (fun tags =>
    dagForceWord (fullMask sample.2) (fun full =>
      dagCountSigns false full tags (fun normal =>
        dagCountSigns true full tags (fun tight =>
          let visit := fun a b op retains =>
            dagForceWord (state.2.1.getD a 0) (fun x =>
              dagForceWord (state.2.1.getD b 0) (fun y =>
                dagForceWord (dagGateWord mask op x y) (fun out =>
                  let xs := tags.getD a (0,0)
                  let ys := tags.getD b (0,0)
                  dagForceWord (dagGateWord full op xs.1 ys.1) (fun up =>
                    dagForceWord (dagGateWord full op xs.2 ys.2) (fun down =>
                      treeBlock 0 retains (fun keep =>
                        let token := gateToken a b op keep
                        if dagTooWide n state.1 token then true else
                          let directed := dagSizeFloor n op keep == (state.1-1)+1
                          let pairs := dagSampleMiss sample full normal tight xs ys (up,down) directed op keep
                          let erased := dagOmitted a b (keep.testBit 0) (op == 2 || keep.testBit 1)
                          if dagPackedPair mask goal packed marks erased out directed pairs then true
                          else match dagDirectChild mask state a b op keep x y out with
                          | none => true
                          | some (fuel, ws, history) => dagForceWords ws (fun forced =>
                            let child := (fuel, forced, history)
                            reference token child || dagLocal mask goal chart cut child)))))))
          treeBlock 0 n (fun a =>
            visit a a 2 2 && treeBlock (a+1) (n-(a+1)) (fun b =>
              treeBlock 0 2 (fun op => visit a b op 4)))))))))

def dagStateOK (mask : Word) (ws : List Word) : Bool :=
  (ws.dedup.length == ws.length) && ws.all (fun w => w &&& mask == w)

theorem dagStateOKSpec {mask : Word} {ws : List Word} (ok : dagStateOK mask ws = true) :
    ws.Nodup ∧ ∀ w ∈ ws, Masked mask w := by
  simp only [dagStateOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  exact ⟨List.nodup_iff_length_dedup_eq.mpr ok.1, ok.2⟩

def dagCheckNode (mask goal : Word) (chart : Option RowChart) (cut : CutCheck)
    (count : Nat) (states : Nat → Option RowState) (moves : Array WordMove) (links : DagLinks)
    (sample : DagSample) (tags : Nat → List DagSignals) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, history) => dagForceWords ws (fun forced =>
      dagStateOK mask forced && dagCheckChildren mask goal chart cut
        (dagRef count states moves links (i+1)) (fuel, forced, history) sample (tags i))

def dagCheckRoots (mask goal : Word) (chart : Option RowChart) (cut : CutCheck)
    (witnesses : List Witness) (reference : Nat → RowState → Bool) (stock : List Word)
    (fuel : Nat) : Bool :=
  treeBlock 0 (2^stock.length) fun token =>
    let state := rootState stock fuel token
    !dagAllowedRoot witnesses state.2.1 || dagLocal mask goal chart cut state || reference token state

theorem dagLocalOpen {mask goal : Word} {chart : Option RowChart}
    {cut : CutCheck} {state : RowState}
    (masked : Masked mask goal) (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (viable : WordViable mask goal state) (noCut : cut state = false) :
    dagLocal mask goal chart cut state = false := by
  obtain ⟨fuel,ws,history⟩ := state
  have ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel at cap
  have card := (liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at card
  change ws.length + t ≤ k + 1 at card
  have fit : ¬ ws.length > fuel + 1 := by omega
  by_cases hz : fuel = 0
  · have kz : k = 0 := by omega
    subst k
    obtain ⟨_,eq,_⟩ := live
    have hm : goal ∈ ws := List.mem_toFinset.mp (by rw [eq]; simp)
    simp [dagLocal, fit, hm]
  by_cases tight : ws.length = fuel + 1
  · have ht : t = 0 := by omega
    subst t
    have dir := dagPartitionLive (directed := true) masked live (fun _ => rfl)
    have noChart : chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c))) = false := by
      cases opt : chart with
      | none => rfl
      | some c =>
        have vt : WordViable mask goal (fuel,ws,[]) := viable
        have ok := tightChart (chartOK c opt) tight vt
        simp [ok]
    simp [dagLocal, fit, hz, tight, dir, noCut, noChart]
  · have sep := dagPartitionLive (directed := false) masked live (by simp)
    simp [dagLocal, fit, hz, tight, sep, noCut]

theorem dagInsertLength (w : Word) (ws : List Word) :
    (insertWord w ws).length = ws.length + 1 := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change (if w ≤ a then w :: a :: ws else a :: insertWord w ws).length = _
    split <;> simp [ih]

theorem dagKeepLength (keep : Bool) (w : Word) (ws : List Word) :
    ws.length - (if keep then 0 else 1) ≤ (keepWord keep w ws).length := by
  cases keep
  · exact List.le_length_erase
  · simp [keepWord]

theorem dagWideChild {mask token : Nat} {state child : RowState}
    (eval : childState mask token state = some child)
    (wide : dagTooWide state.2.1.length state.1 token = true) :
    child.2.1.length > child.1 + 1 := by
  obtain ⟨fuel,ws,history⟩ := state
  let keep := token % 4
  let op := token / 4 % 3
  let i := token / (4 * 3 * 64)
  let j := token / (4 * 3) % 64
  let x := ws.getD i 0
  let y := ws.getD j 0
  let z := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
  let a := keep.testBit 0
  let b := op == 2 || keep.testBit 1
  let rest := keepWord b y (keepWord a x ws)
  let bad : Bool := fuel == 0 || j ≥ ws.length || (if op == 2 then i != j || keep ≥ 2 else i ≥ j)
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z,x,y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb,hs] at eval
  have eq : (fuel-1, insertWord z rest, (z,x,y) :: history) = child := by simpa [hb,hs] using eval
  rw [← eq]
  change (insertWord z rest).length > fuel - 1 + 1
  rw [dagInsertLength]
  have h1 := dagKeepLength a x ws
  have h2 := dagKeepLength b y (keepWord a x ws)
  have h : ws.length - (if a then 0 else 1) - (if b then 0 else 1) + 1 > fuel - 1 + 1 :=
    of_decide_eq_true wide
  dsimp only [rest]
  omega

theorem dagKeepMem {ws : List Word} {x w : Word} {keep : Bool}
    (nd : ws.Nodup) (h : w ∈ keepWord keep x ws) : w ∈ ws ∧ (keep = true ∨ w ≠ x) := by
  cases keep
  · simpa [keepWord, nd.mem_erase_iff, and_comm] using h
  · simpa [keepWord] using h

theorem dagKeepNodup {ws : List Word} (nd : ws.Nodup) (keep : Bool) (x : Word) :
    (keepWord keep x ws).Nodup := by
  cases keep
  · exact nd.erase x
  · exact nd

theorem dagPackedPairSound {mask goal out : Word} {ws : List Word} {directed : Bool}
    {pairs : List Nat} {a b : Nat} {left right : Bool}
    (nd : ws.Nodup)
    (checked : dagPackedPair mask goal (dagPackWords ws) (dagLaneMarks ws.length)
      (dagOmitted a b left right) out directed pairs = true) :
    dagPairReject mask goal directed
      (out :: keepWord right (ws.getD b 0) (keepWord left (ws.getD a 0) ws)) pairs = true := by
  obtain ⟨code,mem,verdict⟩ := List.any_eq_true.mp checked
  apply List.any_eq_true.mpr
  refine ⟨code,mem,?_⟩
  simp only [dagForceWordEq, Bool.and_eq_true, Nat.blt_eq] at verdict
  obtain ⟨⟨⟨⟨⟨⟨hp, hn⟩, neg⟩, wp⟩, wn⟩, output⟩, closure⟩ := verdict
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨
    Bool.and_eq_true_iff.mpr ⟨hp,hn⟩,neg⟩,List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | later
  · exact output
  have rightMem := dagKeepMem (dagKeepNodup nd left (ws.getD a 0)) later
  have leftMem := dagKeepMem nd rightMem.1
  obtain ⟨i,inside,eq⟩ := List.mem_iff_getElem.mp leftMem.1
  have atIndex : ws.getD i 0 = w := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside] using eq
  have omitted : (dagOmitted a b left right).testBit (512*i) = false := by
    have cleared (j : Nat) (keep : Bool) (h : keep = true ∨ w ≠ ws.getD j 0) :
        (if keep then 0 else 1 <<< (512*j)).testBit (512*i) = false := by
      rcases h with yes | diff
      · simp [yes]
      · have ne : i ≠ j := fun same => diff (same ▸ atIndex).symm
        cases keep <;> simp [Nat.shiftLeft_eq, Nat.testBit_two_pow, show 512*j ≠ 512*i by omega]
    simp [dagOmitted, Nat.testBit_or, cleared a left leftMem.2, cleared b right rightMem.2]
  let p := code &&& 511
  let n := code >>> 9
  let marks := dagLaneMarks ws.length
  let signal := dagPackWords ws
  have mark : marks.testBit (512*i) = true := dagMarkBits inside
  have test {j : Nat} (within : j < 512) :
      ((signal >>> j) &&& marks).testBit (512*i) = w.testBit j := by
    rw [Nat.testBit_and, Nat.testBit_shiftRight, mark, Bool.and_true,
      Nat.add_comm j, dagPackBits inside within, atIndex]
  have h := congrArg (fun word => Nat.testBit word (512*i)) (Nat.beq_eq.mp closure)
  simp only [Nat.zero_testBit] at h
  change (((if directed then (signal >>> p &&& marks) &&& ((signal >>> n &&& marks) ^^^ marks)
      else (signal >>> p &&& marks) ^^^ (signal >>> n &&& marks)) &&&
    (marks ^^^ dagOmitted a b left right)).testBit (512*i)) = false at h
  have pt := test (j := p) wp
  have nt := test (j := n) wn
  cases directed <;> cases px : w.testBit p <;> cases nx : w.testBit n <;>
    simp [px,nx,pt,nt,Nat.testBit_and,Nat.testBit_xor,mark,omitted,p,n] at h ⊢

theorem dagEarlyOpen {mask goal a b op keep out : Nat} {state child : RowState}
    (masked : Masked mask goal) (viable : WordViable mask goal child)
    (parent : state.2.1.Nodup) (eval : dagDirectChild mask state a b op keep
      (state.2.1.getD a 0) (state.2.1.getD b 0) out = some child) (pairs : List Nat) :
    dagPackedPair mask goal (dagPackWords state.2.1) (dagLaneMarks state.2.1.length)
      (dagOmitted a b (keep.testBit 0) (op == 2 || keep.testBit 1)) out
      (dagSizeFloor state.2.1.length op keep == (state.1-1)+1) pairs = false := by
  obtain ⟨fuel,ws,history⟩ := state
  let x := ws.getD a 0
  let y := ws.getD b 0
  apply Bool.eq_false_iff.mpr
  intro closed
  have closed := dagPackedPairSound parent closed
  let bad : Bool := fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b)
  let stale : Bool := out == 0 || out == mask || ws.contains out
  let bank := dagKept ws op keep x y
  change (if bad then none else if stale then none else
    some (fuel-1, insertWord out bank, (out,x,y)::history)) = some child at eval
  by_cases h : bad = true
  · simp [h] at eval
  by_cases h' : stale = true
  · simp [h,h'] at eval
  have eq : (fuel-1,insertWord out bank,(out,x,y)::history) = child := by simpa [h,h'] using eval
  subst child
  obtain ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel-1 at cap
  have size := (liveWordSize live).2
  change (insertWord out bank : List Word).toFinset.card + t ≤ k+1 at size
  rw [List.toFinset_card_of_nodup nd, dagInsertLength] at size
  have same : (out::bank).toFinset = (insertWord out bank).toFinset := by
    ext w
    simp only [List.mem_toFinset, List.mem_cons, insertWordMem]
  have openBank := dagPairsOpen (pairs := pairs)
    (directed := dagSizeFloor ws.length op keep == (fuel-1)+1) masked (show LiveWord mask goal k t (out::bank).toFinset by rwa [same])
  have available : (dagSizeFloor ws.length op keep == (fuel-1)+1) = true → t = 0 := by
    intro directed
    have exactBudget := beq_iff_eq.mp directed
    have first := dagKeepLength (keep.testBit 0) x ws
    have second := dagKeepLength (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
    change dagSizeFloor ws.length op keep = (fuel-1)+1 at exactBudget
    unfold dagSizeFloor at exactBudget
    dsimp only [bank, dagKept] at size
    omega
  have refuses := openBank available
  exact Bool.noConfusion (closed.symm.trans refuses)

theorem dagChildAt {mask goal : Word} {chart : Option RowChart}
    {cut : CutCheck} {ref : Nat → RowState → Bool} {state child : RowState} {sample : DagSample} {tags : List DagSignals} {a b op keep : Nat}
    (checked : dagCheckChildren mask goal chart cut ref state sample tags = true)
    (ha : a < state.2.1.length)
    (legal : (a = b ∧ op = 2 ∧ keep < 2) ∨ (a < b ∧ b < state.2.1.length ∧ op < 2 ∧ keep < 4))
    (eval : childState mask (gateToken a b op keep) state = some child)
    (masked : Masked mask goal) (viable : WordViable mask goal child) (nd : state.2.1.Nodup)
    (openChild : dagLocal mask goal chart cut child = false) :
    ref (gateToken a b op keep) child = true := by
  have narrow : dagTooWide state.2.1.length state.1 (gateToken a b op keep) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have tooMany := dagWideChild eval h
    obtain ⟨f,w,path⟩ := child
    simp [dagLocal, tooMany] at openChild
  simp only [dagCheckChildren, dagForceCacheEq, dagForceWordEq, dagCountSignsEq,
    Bool.and_eq_true, decide_eq_true_eq] at checked
  have width := checked.1.1
  have atA := treeBlock_at checked.2 (i := a) (Nat.zero_le _) (by simpa using ha)
  rcases Bool.and_eq_true_iff.mp atA with ⟨unary,binary⟩
  rcases legal with ⟨rfl,rfl,hk⟩ | ⟨ab,hb,hop,hk⟩
  · have atKeep := treeBlock_at unary (i := keep) (Nat.zero_le _) (by simpa using hk)
    have fields := dagDirectChildEq (mask := mask) (state := state) (a := a) (b := a) (op := 2)
      (keep := keep) (by omega) (by decide) (by omega)
    have direct := fields.trans eval
    have early := dagEarlyOpen masked viable nd direct
    rcases child with ⟨fuel,ws,history⟩
    simpa only [narrow,Bool.false_eq_true,ite_false,fields,eval,dagForceWordsEq,early,openChild,Bool.or_false] using atKeep
  · have atB := treeBlock_at binary (i := b) (by omega) (by omega)
    have atOp := treeBlock_at atB (i := op) (Nat.zero_le _) (by simpa using hop)
    have atKeep := treeBlock_at atOp (i := keep) (Nat.zero_le _) (by simpa using hk)
    have fields := dagDirectChildEq (mask := mask) (state := state) (a := a) (b := b) (op := op)
      (keep := keep) (by omega) (by omega) hk
    have direct := fields.trans eval
    have early := dagEarlyOpen masked viable nd direct
    rcases child with ⟨fuel,ws,history⟩
    simpa only [narrow,Bool.false_eq_true,ite_false,fields,eval,dagForceWordsEq,early,openChild,Bool.or_false] using atKeep

theorem readWordMasked {mask : Word} {ws : List Word}
    (all : ∀ w ∈ ws, Masked mask w) (i : Nat) : Masked mask (ws.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => simp [Masked]
  | some w => exact all w (List.mem_of_getElem? h)

theorem childStateData {mask token : Nat} {state child : RowState}
    (eval : childState mask token state = some child)
    (masked : ∀ w ∈ state.2.1, Masked mask w) :
    child.1 < state.1 ∧ ∀ w ∈ child.2.1, Masked mask w := by
  obtain ⟨fuel,ws,history⟩ := state
  let keep := token % 4
  let op := token / 4 % 3
  let a := token / (4 * 3 * 64)
  let b := token / (4 * 3) % 64
  let x := ws.getD a 0
  let y := ws.getD b 0
  let z := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
  let rest := keepWord (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
  let bad : Bool := fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b)
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z,x,y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb,hs] at eval
  have eq : (fuel-1, insertWord z rest, (z,x,y) :: history) = child := by simpa [hb,hs] using eval
  subst child
  have pos : 0 < fuel := by
    by_contra! h
    have he : fuel = 0 := by omega
    simp [bad, he] at hb
  refine ⟨by dsimp; omega,?_⟩
  have read (i : Nat) : AvailableWord mask ws (ws.getD i 0) := by
    simp only [List.getD_eq_getElem?_getD]
    cases h : ws[i]? with
    | none => exact Or.inl rfl
    | some a => exact Or.inr (Or.inr (List.mem_of_getElem? h))
  have hm : Masked mask z := by
    apply maskedGate masked
    unfold z
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inl rfl⟩
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inr rfl⟩
    · exact Or.inl ⟨x,read _,rfl⟩
  intro w hw
  rcases insertWordMem.mp hw with rfl | other
  · exact hm
  · apply masked w
    apply keepSubset (keep.testBit 0) x ws w
    exact keepSubset (op == 2 || keep.testBit 1) y _ w other

def DagMovesOK (mask goal : Word) (width : Nat) (moves : Array WordMove) : Prop :=
  ∀ (i : Nat) (m : WordMove), moves[i]? = some m →
    ∃ select : Fin width → Fin width, DagAuto mask goal select ∧
      ∀ w, Masked mask w → mixMove m w = relabel select w

abbrev DagMoveRecord (width : Nat) := WordMove × (Fin width → Fin width) × (Fin width → Fin width)

def dagMoves (cert : List (DagMoveRecord width)) : Array WordMove := (cert.map Prod.fst).toArray

def dagMoveRecordProps {width : Nat} (mask goal : Word) (entry : DagMoveRecord width) : Prop :=
  let (move, select, inverse) := entry
  (∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal

def dagMoveRecordOK {width : Nat} (mask goal : Word) (entry : DagMoveRecord width) : Bool :=
  let (move, select, inverse) := entry
  decide ((∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal)

theorem dagMoveRecordSpec {width : Nat} {mask goal : Word} {entry : DagMoveRecord width}
    (ok : dagMoveRecordOK mask goal entry = true) : dagMoveRecordProps mask goal entry := by
  rcases entry with ⟨move,select,inverse⟩
  unfold dagMoveRecordProps
  exact of_decide_eq_true ok

theorem dagMovesOfCheck {width : Nat} {mask goal : Word} {cert : List (DagMoveRecord width)}
    (ok : cert.all (dagMoveRecordOK mask goal) = true) :
    DagMovesOK mask goal width (dagMoves cert) := by
  intro i m get
  simp only [dagMoves, List.getElem?_toArray, List.getElem?_map] at get
  cases e : cert[i]? with
  | none => simp [e] at get
  | some entry =>
    have eq : entry.1 = m := by simpa [e] using get
    rcases entry with ⟨move,select,inverse⟩
    obtain ⟨left,right,bm,gm,basis,mm,mg⟩ :=
      dagMoveRecordSpec (List.all_eq_true.mp ok _ (List.mem_of_getElem? e))
    subst m
    exact ⟨select, dagAutoFromMove left right bm gm basis mm mg⟩

theorem dagLinked {mask goal : Word} {width count : Nat} {states : Nat → Option RowState}
    {moves : Array WordMove} {links : DagLinks} {parent token : Nat} {state : RowState}
    (bounds : Masked (fullMask width) mask)
    (valid : DagMovesOK mask goal width moves)
    (masked : ∀ w ∈ state.2.1, Masked mask w)
    (ok : dagRef count states moves links parent token state = true)
    {k t : Nat} (live : LiveWord mask goal k t state.2.1.toFinset) :
    ∃ i saved, i < count ∧ states i = some saved ∧ saved.1 = state.1 ∧
      LiveWord mask goal k t saved.2.1.toFinset := by
  unfold dagRef at ok
  split at ok
  · contradiction
  next destination auto h =>
    have hd := Nat.blt_eq.mp (Bool.and_eq_true_iff.mp ok).1
    have finish := (Bool.and_eq_true_iff.mp ok).2
    cases eq : states destination with
    | none => simp [eq] at finish
    | some saved =>
      simp only [eq, Bool.and_eq_true, beq_iff_eq] at finish
      refine ⟨destination,saved,hd,eq,finish.1,?_⟩
      have last := finish.2
      split at last
      · have same : saved.2.1 = state.2.1 := beq_iff_eq.mp last
        rwa [same]
      · split at last
        · contradiction
        next m hm =>
          obtain ⟨select,auto,agree⟩ := valid _ _ hm
          have same : saved.2.1 = dagMoveWords m state.2.1 := beq_iff_eq.mp last
          rw [same, dagMoveSet (fun w hw => agree w (masked w hw))]
          exact liveMaskedImage auto bounds live (fun w hw => masked _ (List.mem_toFinset.mp hw))

theorem dagAllNodes {mask goal : Word} {width fuel count : Nat}
    {stock : List Word} {chart : Option RowChart}
    {cut : CutCheck} {forest : Forest} {moves : Array WordMove} {links : DagLinks} {sample : DagSample}
    {tags : Nat → List DagSignals}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal)
    (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (cutSound : ∀ s, WordViable mask goal s → cut s = false)
    (autos : DagMovesOK mask goal width moves)
    (verified : treeBlock 0 count (dagCheckNode mask goal chart cut count
      (dagTrace mask stock fuel forest) moves links sample tags) = true):
    ∀ cap i saved, i < count → dagTrace mask stock fuel forest i = some saved →
      saved.1 = cap → ∀ k t, k ≤ cap → ¬LiveWord mask goal k t saved.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i s iBound stateEq sFuel k t kBound live
    rcases s with ⟨remaining, words, history⟩
    let s : RowState := (remaining, words, history)
    let states := dagTrace mask stock fuel forest
    change states i = some s at stateEq
    have checked := treeBlock_at verified (Nat.zero_le i) (by simpa using iBound)
    change dagCheckNode mask goal chart cut count states moves links sample tags i = true at checked
    simp only [dagCheckNode, stateEq, dagForceWordsEq, Bool.and_eq_true] at checked
    obtain ⟨nd,masked⟩ := dagStateOKSpec checked.1
    have ok := checked.2
    have viable : WordViable mask goal s := ⟨nd,k,t,sFuel ▸ kBound,live⟩
    have scanned := ok
    simp only [dagCheckChildren, Bool.and_eq_true, decide_eq_true_eq] at scanned
    have wide := scanned.1.1
    have absent := scanned.1.2
    rcases wordProgress wide viable with hit | ⟨child, possible, cv⟩
    · simpa [hit] using absent
    obtain ⟨a,b,op,keep,ha,legal,eval⟩ := possible
    have r := dagChildAt ok ha legal eval goalMask cv nd (dagLocalOpen goalMask chartOK cv (cutSound _ cv))
    have ⟨less,cm⟩ := childStateData eval masked
    have below : child.1 < cap := sFuel ▸ less
    obtain ⟨_,k',t',fits,clive⟩ := cv
    obtain ⟨j,dest,bound,restore,fuelEq,tail⟩ :=
      dagLinked maskBounds autos cm r clive
    exact ih child.1 below j dest bound restore fuelEq k' t' fits tail

theorem lowerDag {mask goal : Word} {width fuel count : Nat}
    {stock : List Word} {chart : Option RowChart}
    {forest : Forest} {moves : Array WordMove} {links : DagLinks} {sample : DagSample}
    {tags : Nat → List DagSignals}
    {bounds : List Bound} {witnesses : List Witness}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal) (proper : properWord mask goal)
    (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (autos : DagMovesOK mask goal width moves)
    (stockMasked : ∀ w ∈ stock, Masked mask w) (stockNd : stock.Nodup)
    (essential : witnesses.all (essentialB mask goal stock) = true)
    (known : Known bounds) (submasks : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (rootCheck : dagCheckRoots mask goal chart (dagKnownCloses goal bounds) witnesses
      (dagRef count (dagTrace mask stock fuel forest) moves links 0)
      stock fuel = true)
    (nodeCheck : treeBlock 0 count (dagCheckNode mask goal chart (dagKnownCloses goal bounds)
      count (dagTrace mask stock fuel forest) moves links sample tags) = true) :
    Lower mask stock goal (fuel+1) := by
  intro values build hit
  by_contra! small
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive stockMasked build hit proper
  have included : S ⊆ stock.toFinset := fun w hw => List.mem_toFinset.mpr (sub w hw)
  obtain ⟨token,tokenBound,eq⟩ := rootToken stock S
  rw [Finset.inter_eq_right.mpr included] at eq
  let state := rootState stock fuel token
  have eq' : state.2.1.toFinset = S := eq
  have v : WordViable mask goal state := by
    refine ⟨(rootWordSublist stock token).nodup stockNd,k,t,?_,?_⟩
    · change k ≤ fuel
      omega
    · rwa [eq']
  have cutOpen (s : RowState) (h : WordViable mask goal s) : dagKnownCloses goal bounds s = false := by
    rw [dagKnownClosesEq]
    exact knownClosesSound known submasks h
  have openRoot := dagLocalOpen goalMask chartOK v (cutOpen _ v)
  have allowed : dagAllowedRoot witnesses state.2.1 = true := by
    apply List.all_eq_true.mpr
    intro entry mem
    apply List.contains_iff_mem.mpr
    rw [← List.mem_toFinset, eq']
    exact essentialRequired (List.all_eq_true.mp essential entry mem) sub live
  have checked := treeBlock_at rootCheck (Nat.zero_le token) (by simpa using tokenBound)
  change (!dagAllowedRoot witnesses state.2.1 || dagLocal mask goal chart (dagKnownCloses goal bounds) state ||
    dagRef count (dagTrace mask stock fuel forest) moves links 0 token state) = true at checked
  simp only [allowed,openRoot,Bool.not_true,Bool.false_or] at checked
  have finish := dagAllNodes maskBounds goalMask chartOK cutOpen autos nodeCheck
  have fits : k ≤ fuel := by omega
  have still : LiveWord mask goal k t state.2.1.toFinset := by rwa [eq']
  have stateMask : ∀ w ∈ state.2.1, Masked mask w := by
    intro w hw
    exact stockMasked _ ((rootWordSublist stock token).subset hw)
  obtain ⟨i,s,hi,restore,cap,plan⟩ := dagLinked maskBounds autos stateMask checked still
  exact finish fuel i s hi restore cap k t fits plan

def dagLookupLinks (index data indexWidth sizeBits tokenBits destinationBits autoBits trials : Nat) :
    DagLinks := fun parent token =>
  let entry := unpack index indexWidth parent
  let size := entry &&& ((1 <<< sizeBits) - 1)
  let offset := entry >>> sizeBits
  let width := tokenBits + destinationBits + autoBits
  (Nat.rec (motive := fun _ => Nat → Nat → Option DagLink) (fun _ _ => none)
    (fun _ next lo hi =>
      if Nat.blt lo hi then
        let mid := (lo+hi)/2
        let code := unpack data width mid
        let key := code &&& ((1 <<< tokenBits) - 1)
        if Nat.beq token key then
          some ((code >>> tokenBits) &&& ((1 <<< destinationBits) - 1),
            code >>> (tokenBits + destinationBits))
        else if Nat.blt token key then next lo mid else next (mid+1) hi
      else none) trials) offset (offset+size)

def projectDAGStock (mask : Word) (source : List Word) (indices : List Nat) : List Word :=
  List.rec [] (fun i _ rest => (mask &&& source.getD i 0) :: rest) indices

theorem stockMaskedOfCheck {mask : Word} {stock : List Word}
    (h : stock.all (fun w => w &&& mask == w) = true) :
    ∀ w ∈ stock, Masked mask w := by
  intro w hw
  exact beq_iff_eq.mp (List.all_eq_true.mp h w hw)

theorem suppliesOfCheck {oldMask : Word} {old new : List Word} {rename : Word → Word}
    (h : new.all (fun w => availableB oldMask old (rename w)) = true) :
    ∀ w ∈ new, AvailableWord oldMask old (rename w) := by
  intro w hw
  exact availableB_spec.mp (List.all_eq_true.mp h w hw)

def dagShift (mask : Word) (move : WordMove) (word : Word) : Word :=
  mixMove move (word &&& mask)

def dagShiftUnique (mask : Word) (move : WordMove) : Nat → Word → Bool :=
  Nat.rec (fun _ => true) (fun i next occupied =>
    if mask.testBit i then
      dagForceWord (mixMove move (2^i)) (fun col =>
        Nat.beq (col &&& occupied) 0 && dagForceWord (occupied ||| col) next)
    else next occupied)

theorem dagShiftLinear (mask : Word) (move : WordMove) : BitLinear (dagShift mask move) := by
  apply bitLinearComp (mixMoveLinear move)
  simpa using bitLinearRight mask 0

theorem dagShiftBasis (mask : Word) (move : WordMove) (i : Nat) :
    dagShift mask move (2 ^ i) = if mask.testBit i then mixMove move (2^i) else 0 := by
  have select : 2 ^ i &&& mask = if mask.testBit i then 2^i else 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases same : i = j
    · subst j
      simp only [Nat.testBit_and, Nat.testBit_two_pow, decide_true, Bool.true_and]
      cases mask.testBit i <;> simp
    · cases h : mask.testBit i <;> simp [Nat.testBit_and, Nat.testBit_two_pow, same, h]
  rw [dagShift, select]
  split
  · rfl
  · apply Nat.eq_of_testBit_eq
    intro j
    apply Bool.eq_iff_iff.mpr
    rw [mixMoveLinear]
    simp

theorem dagShiftUniqueSpec {mask : Word} {move : WordMove} {n : Nat} {occupied : Word}
    (ok : dagShiftUnique mask move n occupied = true) :
    (∀ j < n, ∀ b, (dagShift mask move (2^j)).testBit b = true → occupied.testBit b = false) ∧
    (∀ j < n, ∀ k < n, ∀ b, (dagShift mask move (2^j)).testBit b = true →
      (dagShift mask move (2^k)).testBit b = true → j = k) := by
  induction n generalizing occupied with
  | zero => simp
  | succ n ih =>
    let col := mixMove move (2^n)
    change (if mask.testBit n then dagForceWord col (fun w =>
      Nat.beq (w &&& occupied) 0 && dagForceWord (occupied ||| w) (dagShiftUnique mask move n))
      else dagShiftUnique mask move n occupied) = true at ok
    cases active : mask.testBit n
    · simp [active,dagForceWordEq] at ok
      obtain ⟨existing,unique⟩ := ih ok
      have dead : dagShift mask move (2^n) = 0 := by simp [dagShiftBasis,active]
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · simp [same,dead] at h
        · exact existing j (by omega) b h
      · intro j hj k hk b a c
        by_cases e : j = n
        · simp [e,dead] at a
        by_cases e' : k = n
        · simp [e',dead] at c
        exact unique j (by omega) k (by omega) b a c
    · simp only [active,ite_true,dagForceWordEq,Bool.and_eq_true] at ok
      have disjoint := Nat.beq_eq.mp ok.1
      obtain ⟨existing,unique⟩ := ih ok.2
      have colEq : dagShift mask move (2^n) = col := by simp [dagShiftBasis,active,col]
      have old {j b : Nat} (hj : j < n) (h : (dagShift mask move (2^j)).testBit b = true) :
          occupied.testBit b = false ∧ col.testBit b = false := by
        simpa [Nat.testBit_or, Bool.or_eq_false_iff] using existing j hj b h
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · rw [same,colEq] at h
          have bit := congrArg (fun w => Nat.testBit w b) disjoint
          simpa [Nat.testBit_and,h] using bit
        · exact (old (by omega) h).1
      · intro j hj k hk b a c
        by_cases e : j = n
        · by_cases e' : k = n
          · exact e.trans e'.symm
          · rw [e,colEq,(old (by omega) c).2] at a
            contradiction
        by_cases e' : k = n
        · rw [e',colEq,(old (by omega) a).2] at c
          contradiction
        exact unique j (by omega) k (by omega) b a c

theorem dagShiftGates {mask : Word} {move : WordMove} {width : Nat}
    (bounded : Masked (fullMask width) mask) (checked : dagShiftUnique mask move width 0 = true) :
    (∀ a b, dagShift mask move (a &&& b) = dagShift mask move a &&& dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ||| b) = dagShift mask move a ||| dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ^^^ b) = dagShift mask move a ^^^ dagShift mask move b) := by
  let f := dagShift mask move
  have lin := dagShiftLinear mask move
  have uniq {j k i : Nat} (hj : (f (2^j)).testBit i = true) (hk : (f (2^k)).testBit i = true) : j = k := by
    have within {m : Nat} (a : (f (2^m)).testBit i = true) : m < width := by
      by_contra! big
      have eq := congrArg (fun w => Nat.testBit w m) bounded
      have zero : mask.testBit m = false := by
        simpa [Masked,fullMask,Nat.testBit_and,Nat.testBit_two_pow_sub_one,show ¬m < width by omega] using eq.symm
      simp [f,dagShiftBasis,zero] at a
    exact (dagShiftUniqueSpec checked).2 j (within hj) k (within hk) i hj hk
  refine ⟨?_,?_,?_⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [Nat.testBit_and, Bool.and_eq_true, lin, lin, lin]
    constructor
    · rintro ⟨j,hj,h⟩
      rw [Nat.testBit_and, Bool.and_eq_true] at hj
      exact ⟨⟨j,hj.1,h⟩,⟨j,hj.2,h⟩⟩
    · rintro ⟨⟨j,hj,q⟩,⟨k,hk,r⟩⟩
      have same := uniq q r
      subst k
      exact ⟨j,by simp [Nat.testBit_and,hj,hk],q⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [lin (a ||| b) i, Nat.testBit_or, Bool.or_eq_true, lin a i, lin b i]
    simp only [Nat.testBit_or, Bool.or_eq_true]
    constructor
    · rintro ⟨j,(left | right),same⟩
      · exact Or.inl ⟨j,left,same⟩
      · exact Or.inr ⟨j,right,same⟩
    · rintro (⟨j,left,same⟩ | ⟨j,right,same⟩)
      · exact ⟨j,Or.inl left,same⟩
      · exact ⟨j,Or.inr right,same⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    have l := lin a i
    have r := lin b i
    have v := lin (a ^^^ b) i
    cases pa : (f a).testBit i <;> cases pb : (f b).testBit i
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      have disj : a.testBit j = true ∨ b.testBit j = true := by
        rw [Nat.testBit_xor] at hj
        cases aj : a.testBit j <;> cases bj : b.testBit j <;> simp [aj,bj] at hj ⊢
      rcases disj with da | db
      · have := l.mpr ⟨j,da,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this
      · have := r.mpr ⟨j,db,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := r.mp pb
      have notA : a.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := l.mpr ⟨j,yes,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this)
      exact ⟨j,by simp [Nat.testBit_xor,notA,hj],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := l.mp pa
      have notB : b.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := r.mpr ⟨j,yes,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this)
      exact ⟨j,by simp [Nat.testBit_xor,hj,notB],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      obtain ⟨a',ha,q⟩ := l.mp pa
      obtain ⟨b',hb,r⟩ := r.mp pb
      have ea := uniq h q
      have eb := uniq h r
      rw [← ea] at ha
      rw [← eb] at hb
      simp [Nat.testBit_xor,ha,hb] at hj

def dagShiftCheck (width mask goal oldMask oldGoal : Word) (stock old : List Word) (move : WordMove) : Bool :=
  Nat.beq (mask &&& fullMask width) mask && dagShiftUnique mask move width 0 &&
    Nat.beq (dagShift mask move mask) oldMask && Nat.beq (dagShift mask move goal) oldGoal &&
    stock.all (fun w => availableB oldMask old (dagShift mask move w))

theorem dagShiftLower {width mask goal oldMask oldGoal : Word} {stock old : List Word} {min : Nat}
    (move : WordMove) (origin : Lower oldMask old oldGoal min)
    (ok : dagShiftCheck width mask goal oldMask oldGoal stock old move = true) :
    Lower mask stock goal min := by
  simp only [dagShiftCheck,Bool.and_eq_true,Nat.beq_eq] at ok
  obtain ⟨⟨⟨⟨bounded,unique⟩,masks⟩,goals⟩,supply⟩ := ok
  obtain ⟨andG,orG,xorG⟩ := dagShiftGates bounded unique
  have zero : dagShift mask move 0 = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    apply Bool.eq_iff_iff.mpr
    rw [dagShiftLinear]
    simp
  apply lowerMap (dagShift mask move) zero masks (fun w => by rw [xorG,masks]) andG orG (suppliesOfCheck supply)
  rwa [goals]

def moveSchedule (stages : Array WordMoveStep) (indices : List Nat) : WordMove :=
  List.rec [] (fun i _ rest => stages[i]?.getD ([],[]) :: rest) indices

def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0

def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]

theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]

theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]

theorem hcsGateWord {rows : Nat} (bank : List (BitVec rows))
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp))
    (hlen : g.inputs.length ≤ 2) :
    GateWord (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank g).toNat := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have zeroAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) 0 := Or.inl rfl
  have maskAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) (fullMask rows) :=
    Or.inr (Or.inl rfl)
  rcases hop with rfl | rfl | rfl
  · cases ins with
    | nil => exact gateOfAvailable (by simpa [hcsGateVal, fullMask] using maskAv)
    | cons a t =>
      cases t with
      | nil => exact gateOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact Or.inr ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inl (by simp [hcsGateVal, BitVec.toNat_and])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact gateOfAvailable (by simpa [hcsGateVal] using zeroAv)
    | cons a t =>
      cases t with
      | nil => exact gateOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact Or.inr ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inr (by simp [hcsGateVal, BitVec.toNat_or])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact Or.inl ⟨0, zeroAv, by simpa [hcsGateVal] using notNat (0 : BitVec rows)⟩
    | cons a _ => exact Or.inl ⟨_, toNatAvailable bank a, by simpa [hcsGateVal] using notNat (bank.getD a 0)⟩

theorem hcsBuilds {rows : Nat} (bank : List (BitVec rows))
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ vs, vs.length = gs.length ∧ WordBuilds (fullMask rows) (bank.map BitVec.toNat) vs ∧
      ∀ v ∈ gs.foldl hcsStep bank, v.toNat ∈ vs ++ bank.map BitVec.toNat := by
  induction gs generalizing bank with
  | nil => exact ⟨[], rfl, trivial, fun _ h => List.mem_map_of_mem h⟩
  | cons g gs ih =>
    let v := hcsGateVal bank g
    have hg := hfan g List.mem_cons_self
    obtain ⟨xs, len, build, sub⟩ := ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
    have eq : (hcsStep bank g).map BitVec.toNat = bank.map BitVec.toNat ++ [v.toNat] := by
      simp [hcsStep, v]
    rw [eq] at build
    refine ⟨v.toNat :: xs, by simp [len], ⟨hcsGateWord bank g hg.1 hg.2, buildsWeaken ?_ build⟩, ?_⟩
    · intro u hu; exact Or.inr (Or.inr (by simpa [or_comm] using hu))
    · intro u hu; have m := sub u hu; rw [eq] at m
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using m

def hcsCheckPow (p : Nat → Bool) : Nat → Nat → Bool
  | 0, s => p s
  | k + 1, s => hcsCheckPow p k s && hcsCheckPow p k (s + 2 ^ k)

theorem hcsCheckPow_spec {p : Nat → Bool} {k s i : Nat}
    (h : hcsCheckPow p k s = true) (lo : s ≤ i) (hi : i < s + 2 ^ k) : p i = true := by
  induction k generalizing s with
  | zero =>
    have e : i = s := by omega
    simpa [hcsCheckPow, e] using h
  | succ k ih =>
    simp only [hcsCheckPow, Bool.and_eq_true] at h
    by_cases hlt : i < s + 2 ^ k
    · exact ih h.1 lo hlt
    · exact ih h.2 (by omega) (by rw [Nat.pow_succ] at hi; omega)

theorem hcsLowerEq {m1 m2 g1 g2 min : Nat} {b1 b2 : List Word}
    (hm : m1 = m2) (hb : b1 = b2) (hg : g1 = g2)
    (h : Lower m1 b1 g1 min) : Lower m2 b2 g2 min := by
  subst hm; subst hb; subst hg; exact h

theorem hcsLower {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n)) (min : Nat)
    (f : (Fin n → Bool) → Bool)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (claim : Lower (fullMask (2 ^ n)) (raw.map BitVec.toNat) goal.toNat min)
    (t : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize n f t) : min ≤ t := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  obtain ⟨vs, len, built, sub⟩ := hcsBuilds raw C.gates hfan
  let eb := C.gates.foldl hcsStep raw
  have same : eb.getD C.output 0 = goal := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let y : Fin n → Bool := fun k => j.testBit k.val
    have hbank : raw.map (fun v => v.getLsbD j) = List.ofFn y :=
      beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
    have hfg : goal.getLsbD j = f y :=
      beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
    have hbits := hcsFoldBits raw ⟨j, hj⟩ C.gates hfan
    have hevj : (C.wires (List.ofFn y)).getD C.output false = f y := hev y
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
      (List.ofFn y)).getD C.output false = f y at hevj
    rw [← hbank, ← hbits] at hevj
    rw [hfg, ← hevj, ← hcsGetDBit]
  have av : AvailableWord (fullMask (2 ^ n)) (vs ++ raw.map BitVec.toNat) goal.toNat := by
    rw [← same, List.getD_eq_getElem?_getD]
    cases h : eb[C.output]? with
    | none => exact Or.inl rfl
    | some v => exact Or.inr (Or.inr (sub v (List.mem_of_getElem? h)))
  have lb := claim vs built av
  have hs : C.gates.length ≤ t := hsz
  omega

def moveStage0 : WordMoveStep := ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)])
def moveStage1 : WordMoveStep := ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)])
def moveStage2 : WordMoveStep := ([(0xff0000ff, 0), (0xff00, 8)], [(0xff0000, 8)])
def moveStages : Array WordMoveStep := #[moveStage0, moveStage1, moveStage2]
def sBase : List Word := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def sGoal : Word := 0xa8888880
def s0Mask : Word := 0xffffffff
abbrev s0Goal : Word := sGoal &&& s0Mask
abbrev s0StockWords : List Word := projectDAGStock s0Mask sBase [0, 1, 2, 3, 4]
def s0Cuts : List Bound := []
def s0Chart : Option RowChart := some ⟨[7, 11, 19, 29, 7, 7, 7, 7, 7, 7, 7, 7, 30, 13, 21, 25, 3, 30, 30, 30, 30, 30, 30, 30], rfl⟩
def s0Sample : DagSample := (0xe074321d0a8741a1d0c86c3c130184c140b0182c0c070281c0607, 12)
def s0Witnesses := unpackWitnesses s0StockWords [15902, 275993, 539161, 801301, 1063437]
def s0Links : DagLinks :=
  dagLookupLinks 0xd100a3001901 0x6631333059920cc62d870e92c331014c528062c025200c880342010001f 8 4 12 3 2 4
def s0Data : Forest := fun i => decodeNode 3 14 0x310162840c9630c06901040f8 i
def s0Tags := dagTraceTags s0Mask 12 (dagTagBases s0StockWords 0xfe0f98f070fffff 0xec0dd0b4607d7ab 12) 6 s0Data
def s0States := dagTrace s0Mask s0StockWords 6 s0Data
def s0Move0Map (i : Fin 32) : Fin 32 := Fin.ofNat 32 (permuteAxes [0, 1, 3, 2, 4] 0 i.val)
def s0Move0Inverse (i : Fin 32) : Fin 32 := Fin.ofNat 32 (permuteAxes [0, 1, 3, 2, 4] 0 i.val)
def s0Move1Map (i : Fin 32) : Fin 32 := Fin.ofNat 32 (permuteAxes [0, 1, 4, 2, 3] 0 i.val)
def s0Move1Inverse (i : Fin 32) : Fin 32 := Fin.ofNat 32 (permuteAxes [0, 1, 3, 4, 2] 0 i.val)
def s0MoveCert : List (DagMoveRecord 32) := [((moveSchedule moveStages [0]), s0Move0Map, s0Move0Inverse), ((moveSchedule moveStages [1, 2]), s0Move1Map, s0Move1Inverse)]
def s0Moves := dagMoves s0MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Autos : DagMovesOK s0Mask s0Goal 32 s0Moves := dagMovesOfCheck (by decide +kernel)
def s0Check := dagCheckNode s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) 7 s0States s0Moves s0Links s0Sample s0Tags
def s0RootAt (token : Nat) : Bool :=
  let s := rootState s0StockWords 6 token
  !dagAllowedRoot s0Witnesses s.2.1 || dagLocal s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) s ||
  dagRef 7 s0States s0Moves s0Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0RootBlock0 : treeBlock 0 32 s0RootAt = true := by decide +kernel
theorem s0Roots : dagCheckRoots s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) s0Witnesses (dagRef 7 s0States s0Moves s0Links 0) s0StockWords 6 = true := s0RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Block0 : treeBlock 0 7 s0Check = true := by decide +kernel
theorem s0Blocks : treeBlock 0 7 s0Check = true := s0Block0
theorem s0Known : Known s0Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Stock : Lower s0Mask s0StockWords s0Goal 7 := by
  apply lowerDag _ _ _ _ s0Autos _ _ _ s0Known _ s0Roots s0Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s0StockWords; decide +kernel
  · decide +kernel
  · simp only [s0Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h

theorem lower (t : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize 5
    (fun x : Fin 5 → Bool => Nat.testBit 0xa8888880
      (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) t) : 7 ≤ t := by
  let raw : List (BitVec 32) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
  let goal : BitVec 32 := 0xa8888880
  have root : Lower (fullMask 32) (raw.map BitVec.toNat) goal.toNat 7 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s0Stock
  exact hcsLower (n := 5) raw goal 7 _ (by decide +kernel) (by decide +kernel) root t h
end PEqualNP.Outside.L_meta_12258_aux.FalseBase
namespace PEqualNP.Outside.L_meta_12258_aux.TrueBase

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower : ∀ s, HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xfeeeeee0
    (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → 7 ≤ s := by
  refine S.red1 4 _ (0 : Fin 5) false (by decide +kernel) (by decide +kernel) 6 ?_
  exact fun s h => final 4 6 _ (by decide) (by decide +kernel) (fun e he => by
    have he' : e < 3 := by omega
    clear he
    interval_cases e <;> decide +kernel) s h
end PEqualNP.Outside.L_meta_12258_aux.TrueBase
namespace PEqualNP.Outside.L_meta_12258_aux.DualBase

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

open PEqualNP.MetaComplexity

lemma fold_length (gs : List Gate) (W : List Bool) :
    (gs.foldl step W).length = W.length + gs.length := by
  induction gs generalizing W with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [step, List.length_append, List.length_singleton, List.length_cons, List.length_nil]
    omega

lemma dual_size (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ x y, f x ≠ f y) (h : HasCircuitSize n f s) :
    HasCircuitSize n (fun x => !(f (fun i => !x i))) s := by
  obtain ⟨C, hc, hs, he⟩ := h
  have hlen : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).length = n + C.gates.length := by
    intro x
    change (C.gates.foldl step (List.ofFn x)).length = n + C.gates.length
    rw [fold_length]
    simp
  have hout : C.output < n + C.gates.length := by
    by_contra hn
    have hz : ∀ x : Fin n → Bool, f x = false := by
      intro x
      rw [←he x, Circuit.eval, List.getD_eq_default _ _ (by rw [hlen]; omega)]
    obtain ⟨x,y,hxy⟩ := hnc
    exact hxy (by rw [hz x,hz y])
  obtain ⟨gs,hsize,hgood,_,hdual⟩ := main n C.gates hc
  refine ⟨⟨gs,C.output⟩, hgood, ?_, ?_⟩
  · change gs.length ≤ s
    rw [hsize]
    exact hs
  · intro x
    change (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD C.output false =
      !(f (fun i => !x i))
    rw [hdual C.output x hout]
    exact congrArg Bool.not (he (fun i => !x i))

end PEqualNP.Outside.L_meta_12258_aux.DualBase
namespace PEqualNP.Outside.L_meta_12258_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4269834368 * 2 ^ 32 + 4261445632)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [6, 2]⟩, ⟨.and, [7, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [12, 13]⟩], 14⟩

lemma witness_mono : Monotone2 witness := by simp [witness, Monotone2]

lemma witness_size : witness.size = 9 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma witness_correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

end PEqualNP.Outside.L_meta_12258_aux

namespace PEqualNP.Outside.L_meta_12258_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def cofactorMap : Fin 5 → Fin 5 := ![2,3,4,0,1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma false_cofactor_eq :
    (fun x : Fin 5 → Bool => target (Fin.snoc (x ∘ cofactorMap) false)) =
    (fun x : Fin 5 → Bool => Nat.testBit 0xa8888880
      (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) := by
  have h : ∀ x : Fin 5 → Bool, target (Fin.snoc (x ∘ cofactorMap) false) =
      Nat.testBit 0xa8888880 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel
  exact funext h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma true_dual_cofactor_eq :
    (fun x : Fin 5 → Bool => Bool.not (target (Fin.snoc ((fun i => !x i) ∘ cofactorMap) true))) =
    (fun x : Fin 5 → Bool => Nat.testBit 0xfeeeeee0
      (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) := by
  have h : ∀ x : Fin 5 → Bool, Bool.not (target (Fin.snoc ((fun i => !x i) ∘ cofactorMap) true)) =
      Nat.testBit 0xfeeeeee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel
  exact funext h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma cofactor_lower (b : Bool) (s : ℕ)
    (h : HasCircuitSize 5 (fun y => target (Fin.snoc y b)) s) : 7 ≤ s := by
  have hr := Elim.relabel_size cofactorMap (fun y => target (Fin.snoc y b)) s h
  cases b
  · change HasCircuitSize 5 (fun x => target (Fin.snoc (x ∘ cofactorMap) false)) s at hr
    rw [false_cofactor_eq] at hr
    exact FalseBase.lower s hr
  · let g := fun x : Fin 5 → Bool => target (Fin.snoc (x ∘ cofactorMap) true)
    have hnc : ∃ x y : Fin 5 → Bool, g x ≠ g y :=
      ⟨fun _ => false, fun _ => true, by decide +kernel⟩
    have hd := DualBase.dual_size 5 g s hnc hr
    change HasCircuitSize 5
      (fun x => Bool.not (target (Fin.snoc ((fun i => !x i) ∘ cofactorMap) true))) s at hd
    rw [true_dual_cofactor_eq] at hd
    exact TrueBase.lower s hd

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma target_lower (s : ℕ) (h : HasCircuitSize 6 target s) : 9 ≤ s := by
  have dep : ∃ x : Fin 6 → Bool,
      target (Function.update x (Fin.last 5) (!x (Fin.last 5))) ≠ target x :=
    ⟨fun i => decide (i.val < 3), by decide +kernel⟩
  have nc : ∀ b : Bool, ∃ x y : Fin 5 → Bool,
      target (Fin.snoc x b) ≠ target (Fin.snoc y b) := by
    intro b
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    cases b <;> decide +kernel
  obtain ⟨b,t,ht,hc⟩ := Elim.gate_elim_two 5 target s dep nc h
  have hl := cofactor_lower b t hc
  omega
end PEqualNP.Outside.L_meta_12258_aux

open PEqualNP.Outside.L_meta_12258_aux in
theorem PEqualNP.Outside.L_meta_12258 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269834368 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269834368 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  refine ⟨witness, witness_mono, ?_, witness_correct⟩
  rw [witness_size]
  exact target_lower s hs
